{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import CEK
import SECD
import Krivine
import qualified Data.Map.Strict as Map

-- ============================================================================
-- Exercise 1: Extend the CEK Machine with Pairs
-- ============================================================================

-- We extend the syntax with pairs:
-- TmPair e1 e2    - pair construction
-- TmFst e         - first projection
-- TmSnd e         - second projection

-- Extended Term type (conceptual - in practice would modify Syntax.hs)
data ExtTerm
  = ETmVar Var
  | ETmLam Var ExtTerm
  | ETmApp ExtTerm ExtTerm
  | ETmInt Integer
  | ETmAdd ExtTerm ExtTerm
  | ETmPair ExtTerm ExtTerm     -- NEW: pair construction
  | ETmFst ExtTerm              -- NEW: first projection
  | ETmSnd ExtTerm              -- NEW: second projection
  deriving (Eq, Show)

-- Extended Value type
data ExtValue
  = EVInt Integer
  | EVClosure Var ExtTerm ExtEnv
  | EVPair ExtValue ExtValue    -- NEW: pair value
  deriving (Eq, Show)

type ExtEnv = Map.Map Var ExtValue

-- Extended Frame type for CEK machine
data ExtFrame
  = EFApp1 ExtTerm ExtEnv          -- [_ t2]
  | EFApp2 ExtValue                -- [v1 _]
  | EFAdd1 ExtTerm ExtEnv          -- [_ + t2]
  | EFAdd2 ExtValue                -- [v1 + _]
  | EFPair1 ExtTerm ExtEnv         -- NEW: [(_, e2)]
  | EFPair2 ExtValue               -- NEW: [(v1, _)]
  | EFFst                          -- NEW: [fst _]
  | EFSnd                          -- NEW: [snd _]
  deriving (Eq, Show)

type ExtKont = [ExtFrame]

data ExtState
  = EEval ExtTerm ExtEnv ExtKont
  | EApply ExtKont ExtValue
  deriving (Eq, Show)

-- CEK machine step function with pairs
stepWithPairs :: ExtState -> Maybe ExtState
stepWithPairs state = case state of
  -- Original CEK rules...
  EEval (ETmVar x) env k ->
    case Map.lookup x env of
      Just v  -> Just $ EApply k v
      Nothing -> Nothing

  EEval (ETmLam x t) env k ->
    Just $ EApply k (EVClosure x t env)

  EEval (ETmApp t1 t2) env k ->
    Just $ EEval t1 env (EFApp1 t2 env : k)

  EEval (ETmInt n) _env k ->
    Just $ EApply k (EVInt n)

  EEval (ETmAdd t1 t2) env k ->
    Just $ EEval t1 env (EFAdd1 t2 env : k)

  -- NEW: Pair construction
  -- To evaluate (e1, e2):
  -- 1. Evaluate e1 to v1
  -- 2. Evaluate e2 to v2
  -- 3. Return (v1, v2)
  EEval (ETmPair t1 t2) env k ->
    Just $ EEval t1 env (EFPair1 t2 env : k)

  -- NEW: First projection
  -- To evaluate fst e:
  -- 1. Evaluate e to a pair value
  -- 2. Extract the first component
  EEval (ETmFst t) env k ->
    Just $ EEval t env (EFFst : k)

  -- NEW: Second projection
  EEval (ETmSnd t) env k ->
    Just $ EEval t env (EFSnd : k)

  -- Apply continuation frames...
  EApply [] v ->
    Nothing  -- Done

  EApply (EFApp1 t2 env : k) v1 ->
    Just $ EEval t2 env (EFApp2 v1 : k)

  EApply (EFApp2 (EVClosure x t env) : k) v2 ->
    Just $ EEval t (Map.insert x v2 env) k

  EApply (EFApp2 _ : _) _ ->
    Nothing  -- Stuck

  EApply (EFAdd1 t2 env : k) v1 ->
    Just $ EEval t2 env (EFAdd2 v1 : k)

  EApply (EFAdd2 (EVInt n1) : k) (EVInt n2) ->
    Just $ EApply k (EVInt (n1 + n2))

  EApply (EFAdd2 _ : _) _ ->
    Nothing

  -- NEW: Pair continuation frames
  -- After evaluating first component, evaluate second
  EApply (EFPair1 t2 env : k) v1 ->
    Just $ EEval t2 env (EFPair2 v1 : k)

  -- After evaluating both components, create pair
  EApply (EFPair2 v1 : k) v2 ->
    Just $ EApply k (EVPair v1 v2)

  -- After evaluating pair, extract first component
  EApply (EFFst : k) (EVPair v1 _v2) ->
    Just $ EApply k v1

  EApply (EFFst : _) _ ->
    Nothing  -- Stuck: not a pair

  -- After evaluating pair, extract second component
  EApply (EFSnd : k) (EVPair _v1 v2) ->
    Just $ EApply k v2

  EApply (EFSnd : _) _ ->
    Nothing  -- Stuck: not a pair

-- Example: (42, 17)
examplePair :: ExtTerm
examplePair = ETmPair (ETmInt 42) (ETmInt 17)

-- Example: fst (42, 17) = 42
exampleFst :: ExtTerm
exampleFst = ETmFst (ETmPair (ETmInt 42) (ETmInt 17))

-- Example: let x = (1, 2) in fst x + snd x
examplePairComputation :: ExtTerm
examplePairComputation =
  ETmApp (ETmLam "x" (ETmAdd (ETmFst (ETmVar "x")) (ETmSnd (ETmVar "x"))))
         (ETmPair (ETmInt 1) (ETmInt 2))

-- ============================================================================
-- Exercise 2: Call-by-Name CEK Machine
-- ============================================================================

-- In call-by-name, arguments are not evaluated before being passed.
-- Instead, they are wrapped in "thunks" (delayed computations).

-- Thunk: an unevaluated term with its environment
data CBNThunk = CBNThunk Term Env
  deriving (Eq, Show)

-- Values in call-by-name
data CBNValue
  = CBNVInt Integer
  | CBNVClosure Var Term CBNEnv
  deriving (Eq, Show)

type CBNEnv = Map.Map Var CBNThunk  -- Map variables to thunks!

data CBNFrame
  = CBNFApp1 Term CBNEnv     -- [_ t2] - but t2 stays unevaluated!
  | CBNFAdd1 Term CBNEnv
  | CBNFAdd2 CBNValue
  deriving (Eq, Show)

type CBNKont = [CBNFrame]

data CBNState
  = CBNEval Term CBNEnv CBNKont
  | CBNApply CBNKont CBNValue
  deriving (Eq, Show)

-- Call-by-name CEK step
stepCallByName :: CBNState -> Maybe CBNState
stepCallByName state = case state of
  -- Variable: force the thunk
  CBNEval (TmVar x) env k ->
    case Map.lookup x env of
      Just (CBNThunk t' e') ->
        -- Evaluate the thunk in its environment
        Just $ CBNEval t' e' k
      Nothing -> Nothing

  -- Lambda: create closure
  CBNEval (TmLam x t) env k ->
    Just $ CBNApply k (CBNVClosure x t env)

  -- Application: DON'T evaluate the argument!
  -- Just create a thunk and continue
  CBNEval (TmApp t1 t2) env k ->
    Just $ CBNEval t1 env (CBNFApp1 t2 env : k)

  CBNEval (TmInt n) _env k ->
    Just $ CBNApply k (CBNVInt n)

  -- Addition: we need to evaluate both sides
  CBNEval (TmAdd t1 t2) env k ->
    Just $ CBNEval t1 env (CBNFAdd1 t2 env : k)

  -- Other cases...
  CBNEval _ _ _ -> Nothing

  -- Apply continuation
  CBNApply [] v ->
    Nothing  -- Done

  -- Function evaluated: bind argument as thunk
  CBNApply (CBNFApp1 t2 env : k) (CBNVClosure x t fenv) ->
    -- KEY DIFFERENCE: don't evaluate t2, just bind it as a thunk
    let thunk = CBNThunk t2 env
    in Just $ CBNEval t (Map.insert x thunk fenv) k

  CBNApply (CBNFApp1 _ _ : _) (CBNVInt _) ->
    Nothing  -- Stuck

  -- Addition
  CBNApply (CBNFAdd1 t2 env : k) v1 ->
    Just $ CBNEval t2 env (CBNFAdd2 v1 : k)

  CBNApply (CBNFAdd2 (CBNVInt n1) : k) (CBNVInt n2) ->
    Just $ CBNApply k (CBNVInt (n1 + n2))

  CBNApply _ _ ->
    Nothing

-- Example comparing call-by-value and call-by-name:
-- In CBV: (\x. 42) (loop) gets stuck evaluating the argument
-- In CBN: (\x. 42) (loop) returns 42 without evaluating the argument

-- The omega combinator: (\y. y y) (\y. y y)
-- This loops forever in both CBV and CBN
omega :: Term
omega = TmApp (TmLam "y" (TmApp (TmVar "y") (TmVar "y")))
              (TmLam "y" (TmApp (TmVar "y") (TmVar "y")))

-- Ignoring argument: (\x. 42) omega
-- CBV: loops forever trying to evaluate omega
-- CBN: returns 42 immediately!
ignoreOmega :: Term
ignoreOmega = TmApp (TmLam "x" (TmInt 42)) omega

-- Duplicating work: (\x. x + x) (1 + 2)
-- CBV: evaluates 1+2 once, then adds 3+3
-- CBN: evaluates 1+2 twice! Once for each use of x
duplicateWork :: Term
duplicateWork = TmApp (TmLam "x" (TmAdd (TmVar "x") (TmVar "x")))
                      (TmAdd (TmInt 1) (TmInt 2))

-- ============================================================================
-- Exercise 3: Environment Machine with de Bruijn Indices
-- ============================================================================

-- In a pure de Bruijn implementation:
-- - Variables are just numbers (indices)
-- - No need for alpha-renaming
-- - Environment is a simple list

data DBTerm
  = DBVar Int              -- de Bruijn index
  | DBLam DBTerm           -- No variable name needed!
  | DBApp DBTerm DBTerm
  | DBInt Integer
  | DBAdd DBTerm DBTerm
  deriving (Eq, Show)

data DBValue
  = DBVInt Integer
  | DBVClosure DBTerm DBEnv
  deriving (Eq, Show)

type DBEnv = [DBValue]     -- List indexed by de Bruijn index

data DBFrame
  = DBFApp1 DBTerm DBEnv
  | DBFApp2 DBValue
  | DBFAdd1 DBTerm DBEnv
  | DBFAdd2 DBValue
  deriving (Eq, Show)

data DBState
  = DBEval DBTerm DBEnv [DBFrame]
  | DBApply [DBFrame] DBValue
  deriving (Eq, Show)

-- de Bruijn CEK step
stepDeBruijn :: DBState -> Maybe DBState
stepDeBruijn state = case state of
  DBEval (DBVar i) env k ->
    -- Look up by index
    if i < length env
      then Just $ DBApply k (env !! i)
      else Nothing

  DBEval (DBLam t) env k ->
    Just $ DBApply k (DBVClosure t env)

  DBEval (DBApp t1 t2) env k ->
    Just $ DBEval t1 env (DBFApp1 t2 env : k)

  DBEval (DBInt n) _env k ->
    Just $ DBApply k (DBVInt n)

  DBEval (DBAdd t1 t2) env k ->
    Just $ DBEval t1 env (DBFAdd1 t2 env : k)

  DBApply [] v ->
    Nothing

  DBApply (DBFApp1 t2 env : k) v1 ->
    Just $ DBEval t2 env (DBFApp2 v1 : k)

  DBApply (DBFApp2 (DBVClosure t env) : k) v2 ->
    -- Extend environment by prepending (index 0 = most recent)
    Just $ DBEval t (v2 : env) k

  DBApply (DBFApp2 _ : _) _ ->
    Nothing

  DBApply (DBFAdd1 t2 env : k) v1 ->
    Just $ DBEval t2 env (DBFAdd2 v1 : k)

  DBApply (DBFAdd2 (DBVInt n1) : k) (DBVInt n2) ->
    Just $ DBApply k (DBVInt (n1 + n2))

  DBApply _ _ ->
    Nothing

-- Example: \x. x  in de Bruijn is:  λ. 0
dbIdentity :: DBTerm
dbIdentity = DBLam (DBVar 0)

-- Example: \x. \y. x  in de Bruijn is:  λ. λ. 1
dbConst :: DBTerm
dbConst = DBLam (DBLam (DBVar 1))

-- Example: \f. \x. f (f x)  in de Bruijn is:  λ. λ. 1 (1 0)
dbTwice :: DBTerm
dbTwice = DBLam (DBLam (DBApp (DBVar 1) (DBApp (DBVar 1) (DBVar 0))))

-- ============================================================================
-- Exercise 4: Tail Call Optimization
-- ============================================================================

-- A call is in tail position if there's nothing to do after it returns.
-- For tail calls, we can reuse the current continuation.

-- Determine if we're in a tail position
-- We're in tail position if the continuation is empty or only contains
-- non-computational frames

isTailPosition :: Kont -> Bool
isTailPosition [] = True
isTailPosition (FLet _ _ _ : k) = isTailPosition k  -- let is tail-transparent
isTailPosition _ = False

-- Modified CEK step with tail call optimization
stepTailOpt :: State -> Maybe State
stepTailOpt state = case state of
  -- Application in tail position: reuse continuation
  Eval (TmApp t1 t2) env k | isTailPosition k ->
    -- Mark this as a tail call for optimization
    Just $ Eval t1 env (FApp1 t2 env : k)

  -- When applying in tail position, we don't push new frames
  Apply (FApp2 (VClosure x t env) : k) v2 | isTailPosition k ->
    -- Tail call: directly continue with the function body
    -- The key insight: we don't push a return frame!
    Just $ Eval t (extendEnv x v2 env) k

  -- Regular (non-tail) application
  Apply (FApp2 (VClosure x t env) : k) v2 ->
    Just $ Eval t (extendEnv x v2 env) k

  -- For all other cases, use regular CEK semantics
  _ -> step state

-- Example: Tail-recursive factorial
-- fact = fix (\f. \n. \acc. if0 n then acc else f (n-1) (n*acc))
-- The recursive call is in tail position!

factTailRec :: Term
factTailRec =
  TmFix (TmLam "f"
    (TmLam "n"
      (TmLam "acc"
        (TmIf0 (TmVar "n")
          (TmVar "acc")
          (TmApp (TmApp (TmVar "f")
                        (TmSub (TmVar "n") (TmInt 1)))
                 (TmMul (TmVar "n") (TmVar "acc")))))))

-- Non-tail recursive factorial (for comparison)
factNonTail :: Term
factNonTail =
  TmFix (TmLam "f"
    (TmLam "n"
      (TmIf0 (TmVar "n")
        (TmInt 1)
        (TmMul (TmVar "n")
               (TmApp (TmVar "f") (TmSub (TmVar "n") (TmInt 1)))))))

-- ============================================================================
-- Test Examples and Machine State Traces
-- ============================================================================

-- Example 1: Simple function application
-- Term: (\x. x + 1) 41
-- Expected: 42
example1 :: Term
example1 = TmApp (TmLam "x" (TmAdd (TmVar "x") (TmInt 1)))
                 (TmInt 41)

-- Trace of example1:
-- State 0: Eval ((\x. x+1) 41) {} []
-- State 1: Eval (\x. x+1) {} [FApp1 41 {}]
-- State 2: Apply [FApp1 41 {}] (VClosure "x" (x+1) {})
-- State 3: Eval 41 {} [FApp2 (VClosure "x" (x+1) {})]
-- State 4: Apply [FApp2 (VClosure "x" (x+1) {})] (VInt 41)
-- State 5: Eval (x+1) {x -> 41} []
-- State 6: Eval x {x -> 41} [FAdd1 1 {x -> 41}]
-- State 7: Apply [FAdd1 1 {x -> 41}] (VInt 41)
-- State 8: Eval 1 {x -> 41} [FAdd2 (VInt 41)]
-- State 9: Apply [FAdd2 (VInt 41)] (VInt 1)
-- State 10: Apply [] (VInt 42)
-- Result: 42

-- Example 2: Higher-order function
-- Term: (\f. f 5) (\x. x * 2)
-- Expected: 10
example2 :: Term
example2 = TmApp (TmLam "f" (TmApp (TmVar "f") (TmInt 5)))
                 (TmLam "x" (TmMul (TmVar "x") (TmInt 2)))

-- Example 3: Nested let bindings
-- Term: let x = 10 in let y = 20 in x + y
-- Expected: 30
example3 :: Term
example3 = TmLet "x" (TmInt 10)
                 (TmLet "y" (TmInt 20)
                        (TmAdd (TmVar "x") (TmVar "y")))

-- Example 4: Conditional
-- Term: if0 (2-2) then 100 else 200
-- Expected: 100
example4 :: Term
example4 = TmIf0 (TmSub (TmInt 2) (TmInt 2))
                 (TmInt 100)
                 (TmInt 200)

-- Example 5: Recursive function (factorial)
-- Term: (fix \f. \n. if0 n then 1 else n * f(n-1)) 5
-- Expected: 120
example5 :: Term
example5 = TmApp factNonTail (TmInt 5)

-- ============================================================================
-- Comparing Machines
-- ============================================================================

-- The CEK, SECD, and Krivine machines all evaluate lambda calculus,
-- but with different characteristics:

-- CEK (Call-by-value):
-- - Explicit continuation as a stack of frames
-- - Evaluates arguments before passing
-- - Good for eager languages (Scheme, ML)

-- SECD (Call-by-value):
-- - Uses bytecode compilation
-- - Closer to real virtual machines
-- - Historical importance (first abstract machine)

-- Krivine (Call-by-name):
-- - Delays argument evaluation
-- - Arguments are thunks
-- - Good for lazy languages (Haskell)

-- Key insights:
-- 1. All machines make the evaluation context explicit
-- 2. This turns recursive substitution into iteration
-- 3. The continuation/stack reifies "what to do next"
-- 4. Environment captures lexical scope

-- ============================================================================
-- Test Suite
-- ============================================================================

runTests :: IO ()
runTests = do
  putStrLn "Testing Chapter 17 Solutions"
  putStrLn "============================\n"

  putStrLn "Example 1: (\\x. x + 1) 41"
  print $ run example1
  putStrLn ""

  putStrLn "Example 2: (\\f. f 5) (\\x. x * 2)"
  print $ run example2
  putStrLn ""

  putStrLn "Example 3: let x = 10 in let y = 20 in x + y"
  print $ run example3
  putStrLn ""

  putStrLn "Example 4: if0 (2-2) then 100 else 200"
  print $ run example4
  putStrLn ""

  putStrLn "Krivine machine (call-by-name):"
  putStrLn "Testing: (\\x. 42) will ignore its argument"
  print $ Krivine.run ignoreOmega
  putStrLn ""

  putStrLn "All solutions implemented!"
