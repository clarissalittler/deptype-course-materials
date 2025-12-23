{-# LANGUAGE LambdaCase #-}
-- | SECD Machine
--
-- The SECD machine is a historic abstract machine designed by Peter Landin in 1964.
-- SECD stands for:
--   S - Stack (for intermediate results)
--   E - Environment (variable bindings)
--   C - Control (instructions to execute)
--   D - Dump (saved contexts for function returns)
--
-- Unlike CEK, SECD compiles terms to instructions first, making it closer
-- to how real virtual machines work.

module SECD
  ( -- * Instructions
    Instr(..)
  , Code
    -- * Machine State
  , State(..)
  , Stack
  , Dump
  , DumpItem(..)
    -- * Compilation
  , compile
    -- * Evaluation
  , inject
  , step
  , eval
  , run
  ) where

import Syntax

-- | SECD instructions
data Instr
  = IAccess Int              -- ^ Access variable by de Bruijn index
  | IClosure Code            -- ^ Create closure with code
  | IApply                   -- ^ Apply function to argument
  | IReturn                  -- ^ Return from function
  | IConst Integer           -- ^ Push constant
  | IAdd                     -- ^ Add top two stack values
  | ISub                     -- ^ Subtract
  | IMul                     -- ^ Multiply
  | IIf0 Code Code           -- ^ Conditional: if0 then else
  | IFix                     -- ^ Create recursive closure
  | IDummy                   -- ^ Push dummy value (for letrec)
  | IUpdate                  -- ^ Update dummy with actual value
  deriving (Eq, Show, Read)

-- | A sequence of instructions
type Code = [Instr]

-- | Stack of values
type Stack = [Value]

-- | Dump: saved machine states for returns
type Dump = [DumpItem]

-- | Saved state when entering a function
data DumpItem = DumpItem
  { dumpStack :: Stack
  , dumpEnv   :: [Value]     -- Using list for de Bruijn indices
  , dumpCode  :: Code
  } deriving (Eq, Show)

-- | SECD machine state
data State = State
  { stStack :: Stack
  , stEnv   :: [Value]
  , stCode  :: Code
  , stDump  :: Dump
  } deriving (Eq, Show)

-- | Compile a term to SECD instructions
--
-- Uses de Bruijn indices for variables.
compile :: Term -> Code
compile = go []
  where
    go :: [Var] -> Term -> Code
    go env (TmVar x) =
      case lookup x (zip env [0..]) of
        Just i  -> [IAccess i]
        Nothing -> error $ "Unbound variable: " ++ x

    go env (TmLam x t) =
      [IClosure (go (x:env) t ++ [IReturn])]

    go env (TmApp t1 t2) =
      go env t1 ++ go env t2 ++ [IApply]

    go _ (TmInt n) =
      [IConst n]

    go env (TmAdd t1 t2) =
      go env t1 ++ go env t2 ++ [IAdd]

    go env (TmSub t1 t2) =
      go env t1 ++ go env t2 ++ [ISub]

    go env (TmMul t1 t2) =
      go env t1 ++ go env t2 ++ [IMul]

    go env (TmIf0 t1 t2 t3) =
      go env t1 ++ [IIf0 (go env t2) (go env t3)]

    go env (TmLet x t1 t2) =
      -- let x = t1 in t2  ~~>  (\x. t2) t1
      go env (TmApp (TmLam x t2) t1)

    go env (TmFix t) =
      go env t ++ [IFix]

-- | Create closure for SECD (stores environment as list)
data SECDClosure = SECDClosure Code [Value]
  deriving (Eq, Show)

-- | Inject: create initial state from term
inject :: Term -> State
inject t = State
  { stStack = []
  , stEnv   = []
  , stCode  = compile t
  , stDump  = []
  }

-- | Single step of SECD machine
step :: State -> Maybe State
step (State s e c d) = case c of
  [] -> case d of
    [] -> Nothing  -- Halted
    (DumpItem s' e' c' : d') ->
      case s of
        (v:_) -> Just $ State (v:s') e' c' d'
        []    -> Nothing  -- Error: empty stack on return

  (IAccess i : c') ->
    if i < length e
      then Just $ State (e !! i : s) e c' d
      else Nothing  -- Error: invalid index

  (IClosure code : c') ->
    let closure = VClosure "" (TmVar "compiled") (envToMap e)
        -- For SECD we store the code, but reuse Value type for simplicity
        -- In a real implementation, we'd have a separate SECD value type
    in Just $ State (VClosure "secd" (encodeCode code) (envToMap e) : s) e c' d

  (IApply : c') ->
    case s of
      (arg : VClosure _ body closEnv : s') ->
        -- Decode the closure's code
        let code' = decodeCode body
            e' = arg : mapToList closEnv
        in Just $ State [] e' code' (DumpItem s' e c' : d)
      _ -> Nothing  -- Error: invalid apply

  (IReturn : _) ->
    case d of
      [] -> Nothing  -- Already at top level
      (DumpItem s' e' c' : d') ->
        case s of
          (v:_) -> Just $ State (v:s') e' c' d'
          []    -> Nothing

  (IConst n : c') ->
    Just $ State (VInt n : s) e c' d

  (IAdd : c') ->
    case s of
      (VInt n2 : VInt n1 : s') ->
        Just $ State (VInt (n1 + n2) : s') e c' d
      _ -> Nothing

  (ISub : c') ->
    case s of
      (VInt n2 : VInt n1 : s') ->
        Just $ State (VInt (n1 - n2) : s') e c' d
      _ -> Nothing

  (IMul : c') ->
    case s of
      (VInt n2 : VInt n1 : s') ->
        Just $ State (VInt (n1 * n2) : s') e c' d
      _ -> Nothing

  (IIf0 c1 c2 : c') ->
    case s of
      (VInt n : s') ->
        let branch = if n == 0 then c1 else c2
        in Just $ State s' e (branch ++ c') d
      _ -> Nothing

  (IFix : c') ->
    case s of
      (VClosure _ body closEnv : s') ->
        -- Create recursive closure by self-reference
        let fixV = VClosure "fix" body (extendEnv "fix" fixV closEnv)
        in Just $ State (fixV : s') e c' d
      _ -> Nothing

  (IDummy : c') ->
    Just $ State s (VInt 0 : e) c' d  -- Placeholder

  (IUpdate : c') ->
    case s of
      (v : s') ->
        case e of
          (_:e') -> Just $ State s' (v:e') c' d
          []     -> Nothing
      [] -> Nothing

-- | Helper: encode code as a term (hack for reusing Value type)
encodeCode :: Code -> Term
encodeCode code = TmVar (show code)

-- | Helper: decode code from term
decodeCode :: Term -> Code
decodeCode (TmVar s) = read s
decodeCode _ = []

-- | Helper: convert environment list to map
envToMap :: [Value] -> Env
envToMap vs = foldr (\(i, v) m -> extendEnv (show i) v m) emptyEnv (zip [0..] vs)

-- | Helper: convert map back to list
mapToList :: Env -> [Value]
mapToList env = map snd $ takeWhile (not . null . fst) $
  [(show i, v) | i <- [0..], Just v <- [lookupEnv (show i) env]]

-- | Run machine to completion
eval :: State -> Maybe Value
eval state = case step state of
  Nothing ->
    case stStack state of
      (v:_) | null (stCode state) && null (stDump state) -> Just v
      _ -> Nothing
  Just state' -> eval state'

-- | Convenience: run a term
run :: Term -> Maybe Value
run = eval . inject
