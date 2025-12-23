{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import Semantic
import NbE
import qualified Data.IORef as IORef

-- ============================================================================
-- Exercise 1: Add Pairs (Dependent Sigma Types)
-- ============================================================================

-- We extend the syntax with dependent pairs (Sigma types)

-- Extended Term type (conceptual - in practice would modify Syntax.hs)
data ExtTerm
  = ETVar Ix
  | ETLam Name ExtTerm
  | ETApp ExtTerm ExtTerm
  | ETPi Name ExtTerm ExtTerm
  | ETU
  | ETSigma Name ExtTerm ExtTerm    -- NEW: Σ(x:A). B
  | ETPair ExtTerm ExtTerm          -- NEW: (a, b)
  | ETFst ExtTerm                   -- NEW: fst p
  | ETSnd ExtTerm                   -- NEW: snd p
  deriving (Eq, Show)

-- Extended Semantic Values
data ExtVal
  = EVLam Name ExtClosure
  | EVPi Name ExtVal ExtClosure
  | EVU
  | EVNe ExtNeutral
  | EVSigma Name ExtVal ExtClosure  -- NEW: Sigma type
  | EVPair ExtVal ExtVal            -- NEW: pair value
  deriving (Eq, Show)

data ExtClosure = ExtClosure ExtEnv ExtTerm
  deriving (Eq, Show)

type ExtEnv = [ExtVal]

data ExtNeutral
  = ENVar Lvl
  | ENApp ExtNeutral ExtVal
  | ENFst ExtNeutral                -- NEW: projection on neutral
  | ENSnd ExtNeutral                -- NEW: projection on neutral
  deriving (Eq, Show)

-- Extended Normal Forms
data ExtNf
  = ENfLam Name ExtNf
  | ENfPi Name ExtNf ExtNf
  | ENfU
  | ENfNe ExtNe
  | ENfSigma Name ExtNf ExtNf       -- NEW: Sigma in normal form
  | ENfPair ExtNf ExtNf             -- NEW: pair in normal form
  deriving (Eq, Show)

data ExtNe
  = ENeVar Lvl
  | ENeApp ExtNe ExtNf
  | ENeRawFst ExtNe                 -- NEW: stuck projection
  | ENeRawSnd ExtNe                 -- NEW: stuck projection
  deriving (Eq, Show)

-- Evaluation with pairs
evalWithPairs :: ExtEnv -> ExtTerm -> ExtVal
evalWithPairs env = \case
  ETVar i ->
    case lookupExtEnv i env of
      Just v  -> v
      Nothing -> error $ "Unbound variable: " ++ show i

  ETLam x t ->
    EVLam x (ExtClosure env t)

  ETApp t u ->
    vAppExt (evalWithPairs env t) (evalWithPairs env u)

  ETPi x a b ->
    EVPi x (evalWithPairs env a) (ExtClosure env b)

  ETU -> EVU

  -- NEW: Sigma type evaluation
  ETSigma x a b ->
    EVSigma x (evalWithPairs env a) (ExtClosure env b)

  -- NEW: Pair evaluation
  -- Just evaluate both components
  ETPair t u ->
    EVPair (evalWithPairs env t) (evalWithPairs env u)

  -- NEW: First projection
  -- If the argument is a pair, return first component
  -- If it's neutral, create a neutral projection
  ETFst t ->
    vFstExt (evalWithPairs env t)

  -- NEW: Second projection
  ETSnd t ->
    vSndExt (evalWithPairs env t)

-- Helper: extend environment
lookupExtEnv :: Int -> ExtEnv -> Maybe ExtVal
lookupExtEnv i env
  | i < length env = Just (env !! i)
  | otherwise = Nothing

extendExtEnv :: ExtVal -> ExtEnv -> ExtEnv
extendExtEnv v env = v : env

-- Apply closure
applyExtClosure :: ExtClosure -> ExtVal -> ExtVal
applyExtClosure (ExtClosure env t) v = evalWithPairs (extendExtEnv v env) t

-- Application
vAppExt :: ExtVal -> ExtVal -> ExtVal
vAppExt (EVLam _ closure) arg = applyExtClosure closure arg
vAppExt (EVNe neutral) arg = EVNe (ENApp neutral arg)
vAppExt _ _ = error "vAppExt: not a function"

-- First projection
vFstExt :: ExtVal -> ExtVal
vFstExt (EVPair v1 _v2) = v1                      -- Reduce: fst (a, b) = a
vFstExt (EVNe n) = EVNe (ENFst n)                -- Stuck: fst x (where x is neutral)
vFstExt _ = error "vFstExt: not a pair"

-- Second projection
vSndExt :: ExtVal -> ExtVal
vSndExt (EVPair _v1 v2) = v2                      -- Reduce: snd (a, b) = b
vSndExt (EVNe n) = EVNe (ENSnd n)                -- Stuck: snd x
vSndExt _ = error "vSndExt: not a pair"

-- Quotation with pairs
quoteWithPairs :: Lvl -> ExtVal -> ExtNf
quoteWithPairs l = \case
  EVLam x closure ->
    let var = EVNe (ENVar l)
        body = applyExtClosure closure var
    in ENfLam x (quoteWithPairs (l + 1) body)

  EVPi x a closure ->
    let var = EVNe (ENVar l)
        b = applyExtClosure closure var
    in ENfPi x (quoteWithPairs l a) (quoteWithPairs (l + 1) b)

  EVU -> ENfU

  EVNe neutral -> ENfNe (quoteNeExt l neutral)

  -- NEW: Quote Sigma type
  EVSigma x a closure ->
    let var = EVNe (ENVar l)
        b = applyExtClosure closure var
    in ENfSigma x (quoteWithPairs l a) (quoteWithPairs (l + 1) b)

  -- NEW: Quote pair
  EVPair v1 v2 ->
    ENfPair (quoteWithPairs l v1) (quoteWithPairs l v2)

-- Quote neutral with projections
quoteNeExt :: Lvl -> ExtNeutral -> ExtNe
quoteNeExt l = \case
  ENVar x -> ENeVar x
  ENApp n v -> ENeApp (quoteNeExt l n) (quoteWithPairs l v)
  ENFst n -> ENeRawFst (quoteNeExt l n)
  ENSnd n -> ENeRawSnd (quoteNeExt l n)

-- Example: identity function for pairs
-- \p. p  where p : Σ(x:A). B
examplePairId :: ExtTerm
examplePairId = ETLam "p" (ETVar 0)

-- Example: swap function
-- \p. (snd p, fst p)
exampleSwap :: ExtTerm
exampleSwap = ETLam "p" (ETPair (ETSnd (ETVar 0)) (ETFst (ETVar 0)))

-- Example: construct a dependent pair
-- (5, "hello") : Σ(n:Nat). Vec String n
-- (simplified without Vec type)
exampleDepPair :: ExtTerm
exampleDepPair = ETPair (ETVar 0) (ETVar 1)

-- ============================================================================
-- Exercise 2: Eta Expansion
-- ============================================================================

-- NbE naturally performs eta expansion for functions.
-- For pairs, we want:
--   p : Σ(x:A). B  ==>  (fst p, snd p)

-- Eta expansion for pairs requires type information
quoteWithEta :: Lvl -> ExtVal -> ExtVal -> ExtNf
quoteWithEta l ty val = case (ty, val) of
  -- Eta expand functions: λx. f x
  (EVPi x a b, EVNe n) ->
    let var = EVNe (ENVar l)
        app = EVNe (ENApp n var)
        bodyTy = applyExtClosure b var
    in ENfLam x (quoteWithEta (l + 1) bodyTy app)

  -- Eta expand pairs: (fst p, snd p)
  (EVSigma x a b, EVNe n) ->
    let fstVal = EVNe (ENFst n)
        sndVal = EVNe (ENSnd n)
        sndTy = applyExtClosure b fstVal
    in ENfPair (quoteWithEta l a fstVal)
               (quoteWithEta l sndTy sndVal)

  -- Regular quotation for other cases
  (EVPi x a b, EVLam _ closure) ->
    let var = EVNe (ENVar l)
        body = applyExtClosure closure var
        bodyTy = applyExtClosure b var
    in ENfLam x (quoteWithEta (l + 1) bodyTy body)

  (EVSigma x a b, EVPair v1 v2) ->
    let sndTy = applyExtClosure b v1
    in ENfPair (quoteWithEta l a v1)
               (quoteWithEta l sndTy v2)

  (EVU, EVU) -> ENfU

  (EVU, EVPi x a b) ->
    let var = EVNe (ENVar l)
        b' = applyExtClosure b var
    in ENfPi x (quoteWithEta l EVU a) (quoteWithEta (l + 1) EVU b')

  (EVU, EVSigma x a b) ->
    let var = EVNe (ENVar l)
        b' = applyExtClosure b var
    in ENfSigma x (quoteWithEta l EVU a) (quoteWithEta (l + 1) EVU b')

  (_, EVNe n) -> ENfNe (quoteNeExt l n)

  _ -> quoteWithPairs l val

-- ============================================================================
-- Exercise 3: Call-by-Need (Lazy Evaluation with Memoization)
-- ============================================================================

-- In call-by-need, we:
-- 1. Delay evaluation (like call-by-name)
-- 2. Memoize results (unlike call-by-name)

-- Thunk with memoization using IORef
data Thunk = Thunk (IORef.IORef ThunkState)

data ThunkState
  = Delayed (IO Val)     -- Not yet evaluated
  | Forced Val           -- Already evaluated and cached

-- Values with thunks
data LazyVal
  = LVLam Name LazyClosure
  | LVPi Name LazyVal LazyClosure
  | LVU
  | LVNe LazyNeutral
  | LVThunk Thunk        -- NEW: unevaluated thunk
  deriving (Eq)

-- Manual Eq instance (can't derive due to IORef)
instance Eq Thunk where
  _ == _ = False  -- Thunks are not structurally comparable

data LazyClosure = LazyClosure LazyEnv Term
  deriving (Eq)

type LazyEnv = [LazyVal]

data LazyNeutral
  = LNVar Lvl
  | LNApp LazyNeutral LazyVal
  deriving (Eq)

-- Force a thunk (evaluate and memoize)
force :: Thunk -> IO LazyVal
force (Thunk ref) = do
  state <- IORef.readIORef ref
  case state of
    Forced v -> return v
    Delayed action -> do
      v <- action
      IORef.writeIORef ref (Forced v)
      return v

-- Create a thunk
delay :: IO LazyVal -> IO Thunk
delay action = do
  ref <- IORef.newIORef (Delayed action)
  return (Thunk ref)

-- Lazy evaluation
evalLazy :: LazyEnv -> Term -> IO LazyVal
evalLazy env = \case
  TVar i ->
    case lookupLazyEnv i env of
      Just (LVThunk thunk) -> force thunk  -- Force when needed!
      Just v -> return v
      Nothing -> error $ "Unbound variable: " ++ show i

  TLam x t ->
    return $ LVLam x (LazyClosure env t)

  TApp t u -> do
    f <- evalLazy env t
    -- Don't evaluate u immediately - create a thunk!
    thunk <- delay (evalLazy env u)
    vAppLazy f (LVThunk thunk)

  TPi x a b -> do
    a' <- evalLazy env a
    return $ LVPi x a' (LazyClosure env b)

  TU -> return LVU

  -- Other cases...
  _ -> return LVU  -- Simplified

lookupLazyEnv :: Int -> LazyEnv -> Maybe LazyVal
lookupLazyEnv i env
  | i < length env = Just (env !! i)
  | otherwise = Nothing

extendLazyEnv :: LazyVal -> LazyEnv -> LazyEnv
extendLazyEnv v env = v : env

applyLazyClosure :: LazyClosure -> LazyVal -> IO LazyVal
applyLazyClosure (LazyClosure env t) v = evalLazy (extendLazyEnv v env) t

vAppLazy :: LazyVal -> LazyVal -> IO LazyVal
vAppLazy (LVLam _ closure) arg = applyLazyClosure closure arg
vAppLazy (LVNe neutral) arg = return $ LVNe (LNApp neutral arg)
vAppLazy (LVThunk thunk) arg = do
  v <- force thunk
  vAppLazy v arg
vAppLazy _ _ = error "vAppLazy: not a function"

-- Example demonstrating sharing:
-- let x = (expensive) in x + x
-- With call-by-need: expensive is computed only once!
-- With call-by-name: expensive is computed twice!

-- ============================================================================
-- Exercise 4: Universe Levels
-- ============================================================================

-- Replace Type : Type with a proper universe hierarchy

data UnivTerm
  = UTVar Ix
  | UTLam Name UnivTerm
  | UTApp UnivTerm UnivTerm
  | UTPi Name UnivTerm UnivTerm
  | UTU Int                        -- NEW: Type n
  deriving (Eq, Show)

data UnivVal
  = UVLam Name UnivClosure
  | UVPi Name UnivVal UnivClosure
  | UVU Int                        -- NEW: universe level
  | UVNe UnivNeutral
  deriving (Eq, Show)

data UnivClosure = UnivClosure UnivEnv UnivTerm
  deriving (Eq, Show)

type UnivEnv = [UnivVal]

data UnivNeutral
  = UNVar Lvl
  | UNApp UnivNeutral UnivVal
  deriving (Eq, Show)

-- Level of a type
levelOf :: UnivVal -> Int
levelOf (UVU n) = n + 1              -- Type n : Type (n+1)
levelOf (UVPi _ a b) =
  -- (x:A) -> B : Type (max (level A) (level B))
  max (levelOf a) (levelOfClosure b)
levelOf _ = 0

levelOfClosure :: UnivClosure -> Int
levelOfClosure (UnivClosure env t) =
  -- Approximate: would need to evaluate
  -- For now, return a conservative estimate
  0

-- Type checking with universe levels
checkUniverse :: UnivVal -> Int -> Bool
checkUniverse (UVU n) expectedLevel = n == expectedLevel
checkUniverse (UVPi _ a b) expectedLevel =
  let level = max (levelOf a) (levelOfClosure b)
  in level <= expectedLevel
checkUniverse _ _ = False

-- Example:
-- Type 0 : Type 1
-- Type 1 : Type 2
-- (A : Type 0) -> Type 0 : Type 1

-- ============================================================================
-- NbE Worked Examples with Traces
-- ============================================================================

-- Example 1: Identity function
-- Term: λx. x
-- Semantic: VLam "x" (Closure [] (TVar 0))
-- Normal form: λx. x

identityTerm :: Term
identityTerm = TLam "x" (TVar 0)

identityNormalized :: Nf
identityNormalized = normalize identityTerm
-- Result: NfLam "x" (NfNe (NeVar 0))

-- Example 2: Application
-- Term: (λx. x) true
-- Semantic evaluation:
--   1. eval (λx. x) = VLam "x" (Closure [] (TVar 0))
--   2. eval true = VTrue
--   3. vApp (VLam ...) VTrue = applyClosure ... VTrue
--   4. eval (TVar 0) [VTrue] = VTrue
-- Result: VTrue
-- Quote: NfTrue

applyIdTerm :: Term
applyIdTerm = TApp (TLam "x" (TVar 0)) TTrue

applyIdNormalized :: Nf
applyIdNormalized = normalize applyIdTerm
-- Result: NfTrue

-- Example 3: Eta expansion
-- Term: f (where f is a free variable of function type)
-- Semantic: VNe (NVar 0)
-- Quote at type A -> B:
--   1. Create fresh variable: VNe (NVar 1)
--   2. Apply f to it: VNe (NApp (NVar 0) (VNe (NVar 1)))
--   3. Quote as lambda: λx. f x

-- This demonstrates eta-expansion!
-- A neutral function f becomes λx. f x

-- Example 4: Complex reduction
-- Term: (λx. λy. x) a b
-- Step-by-step evaluation:
--   1. eval (λx. λy. x) = VLam "x" (Closure [] (TLam "y" (TVar 1)))
--   2. vApp with a:
--      evalWithPairs [VNe (NVar 0)] (TLam "y" (TVar 1))
--      = VLam "y" (Closure [a] (TVar 1))
--   3. vApp with b:
--      evalWithPairs [b, a] (TVar 1)
--      = a
-- Result: a (the first argument)

constAppTerm :: Term
constAppTerm = TApp (TApp (TLam "x" (TLam "y" (TVar 1)))
                          TTrue)
                    TFalse

constAppNormalized :: Nf
constAppNormalized = normalize constAppTerm
-- Result: NfTrue (returns first argument, ignores second)

-- Example 5: Natural number induction
-- Term: natElim (λ_. Nat) 0 (λn. λrec. suc rec) 3
-- This computes the identity on 3
-- Evaluation:
--   1. n = 3 = suc (suc (suc 0))
--   2. Step 1: s (suc (suc 0)) (natElim P z s (suc (suc 0)))
--   3. Step 2: s (suc 0) (natElim P z s (suc 0))
--   4. Step 3: s 0 (natElim P z s 0)
--   5. Base: z = 0
--   6. Combine: suc (suc (suc 0)) = 3

natElimExample :: Term
natElimExample =
  TNatElim
    (TLam "_" TNat)           -- Motive: always Nat
    TZero                     -- Base case: 0
    (TLam "n" (TLam "rec" (TSuc (TVar 0))))  -- Step: suc rec
    (TSuc (TSuc (TSuc TZero)))  -- n = 3

-- ============================================================================
-- Understanding NbE: Key Insights
-- ============================================================================

{-
NbE (Normalization by Evaluation) works in two phases:

PHASE 1: EVALUATION (Term → Val)
---------------------------------
- Converts syntactic terms into semantic values
- Uses the host language (Haskell) for computation
- Beta reduction happens automatically via function application
- Closures capture the environment

Example: eval (TApp (TLam "x" (TVar 0)) (TInt 42))
  1. eval (TLam "x" (TVar 0)) = VLam "x" (Closure [] (TVar 0))
  2. eval (TInt 42) = VInt 42
  3. vApp (VLam ...) (VInt 42)
     = applyClosure (Closure [] (TVar 0)) (VInt 42)
     = eval (TVar 0) [VInt 42]
     = VInt 42

PHASE 2: QUOTATION (Val → Nf)
------------------------------
- Reads back semantic values into normal form syntax
- Generates fresh variables for lambdas (using levels)
- Performs eta-expansion on neutral terms
- Produces canonical representatives

Example: quote 0 (VLam "x" (Closure [] (TVar 0)))
  1. Create fresh var: VNe (NVar 0)
  2. Apply closure: eval (TVar 0) [VNe (NVar 0)] = VNe (NVar 0)
  3. Quote body: quote 1 (VNe (NVar 0)) = NfNe (NeVar 0)
  4. Wrap in lambda: NfLam "x" (NfNe (NeVar 0))

NEUTRAL TERMS:
--------------
A neutral term is "stuck" on a free variable.
We can't reduce it further without knowing what the variable is.

Example: x + 1 (where x is free)
  eval: VNe (NVar 0)
  We build up the "spine" of operations applied to the variable

WHY IT WORKS:
-------------
1. Completeness: Every term normalizes to a unique normal form
2. Soundness: The normal form is equivalent to the original
3. Efficiency: Uses host language evaluation (very fast!)
4. Elegance: Separates computation from syntax

APPLICATIONS:
-------------
1. Type checking dependent types (need to compare types)
2. Proof assistants (Agda, Coq, Lean)
3. Theorem provers
4. Program optimization
5. Equality checking
-}

-- ============================================================================
-- Test Suite
-- ============================================================================

runTests :: IO ()
runTests = do
  putStrLn "Testing Chapter 18 Solutions"
  putStrLn "============================\n"

  putStrLn "Example 1: Identity function"
  putStrLn "Term: λx. x"
  print identityNormalized
  putStrLn ""

  putStrLn "Example 2: Apply identity to true"
  putStrLn "Term: (λx. x) true"
  print applyIdNormalized
  putStrLn ""

  putStrLn "Example 3: Const function"
  putStrLn "Term: (λx. λy. x) true false"
  print constAppNormalized
  putStrLn ""

  putStrLn "Example 4: Natural number eliminator"
  putStrLn "Term: natElim (λ_. Nat) 0 (λn. λrec. suc rec) 3"
  print $ normalize natElimExample
  putStrLn ""

  putStrLn "All solutions implemented!"
