{-# LANGUAGE LambdaCase #-}
-- | Denotational Semantics
--
-- The denotation function [[·]] maps syntax to semantic domains.
--
-- Key equations:
--   [[x]]ρ = ρ(x)                              (lookup in environment)
--   [[λx:A. e]]ρ = λd ∈ [[A]]. [[e]]ρ[x↦d]    (function abstraction)
--   [[e1 e2]]ρ = [[e1]]ρ ([[e2]]ρ)            (function application)
--   [[fix e]]ρ = ⊔ₙ ([[e]]ρ)ⁿ(⊥)              (least fixed point)
--
-- The environment ρ maps variables to domain elements.

module Denotation
  ( -- * Semantic Interpretation
    denote
  , denoteClosed
    -- * Environment
  , Env
  , emptyEnv
  , extendEnv
  , lookupEnv
    -- * Examples
  , factorialDen
  , fibonacciDen
  ) where

import qualified Data.Map.Strict as Map
import Syntax
import Domain

-- | Environment: maps variables to domain values
type Env = Map.Map Name Dom

-- | Empty environment
emptyEnv :: Env
emptyEnv = Map.empty

-- | Extend environment with a binding
extendEnv :: Name -> Dom -> Env -> Env
extendEnv = Map.insert

-- | Look up a variable
lookupEnv :: Name -> Env -> Dom
lookupEnv x env = case Map.lookup x env of
  Just d  -> d
  Nothing -> error $ "Unbound variable: " ++ x

-- | Denotational semantics
--
-- [[e]]ρ : the meaning of term e in environment ρ
denote :: Env -> Term -> Dom
denote env = \case
  -- Variables: lookup in environment
  -- [[x]]ρ = ρ(x)
  Var x -> lookupEnv x env

  -- Lambda abstraction: create a function in the semantic domain
  -- [[λx:A. e]]ρ = λd. [[e]]ρ[x↦d]
  Lam x _ body ->
    DFun $ \d -> denote (extendEnv x d env) body

  -- Application: apply semantic function to semantic argument
  -- [[e1 e2]]ρ = [[e1]]ρ ([[e2]]ρ)
  App e1 e2 ->
    let d1 = denote env e1
        d2 = denote env e2
    in domApp d1 d2

  -- Let binding: evaluate bound term, extend environment
  -- [[let x = e1 in e2]]ρ = [[e2]]ρ[x↦[[e1]]ρ]
  Let x e1 e2 ->
    let d1 = denote env e1
    in denote (extendEnv x d1 env) e2

  -- Fixed point: THE key semantic construct for recursion!
  -- [[fix f]]ρ = ⊔ₙ ([[f]]ρ)ⁿ(⊥)
  --
  -- By Kleene's theorem, this is the least fixed point of [[f]]ρ.
  -- Haskell's laziness gives us this for free.
  Fix f ->
    case denote env f of
      DFun g -> fix g
      d -> error $ "fix: expected function, got " ++ show d

  -- Booleans
  TmTrue -> DBool True
  TmFalse -> DBool False

  -- Conditional: strict in condition
  -- [[if c then t else e]] = [[t]] if [[c]] = true
  --                        = [[e]] if [[c]] = false
  --                        = ⊥    if [[c]] = ⊥
  If cond thn els ->
    case denote env cond of
      DBool True  -> denote env thn
      DBool False -> denote env els
      DBottom     -> DBottom
      d -> error $ "if: expected bool, got " ++ show d

  -- Natural numbers (flat domain)
  Zero -> DNat 0

  Suc n ->
    case denote env n of
      DNat m   -> DNat (m + 1)
      DBottom  -> DBottom
      d -> error $ "suc: expected nat, got " ++ show d

  Pred n ->
    case denote env n of
      DNat 0   -> DNat 0
      DNat m   -> DNat (m - 1)
      DBottom  -> DBottom
      d -> error $ "pred: expected nat, got " ++ show d

  IsZero n ->
    case denote env n of
      DNat 0   -> DBool True
      DNat _   -> DBool False
      DBottom  -> DBottom
      d -> error $ "iszero: expected nat, got " ++ show d

  -- Primitive recursion on naturals
  -- natrec z s n = s^n(z)
  NatRec z s n ->
    case denote env n of
      DNat 0 -> denote env z
      DNat m ->
        let prev = NatRec z s (natLit (m - 1))
            ds = denote env s
        in domApp (domApp ds (DNat (m - 1))) (denote env prev)
      DBottom -> DBottom
      d -> error $ "natrec: expected nat, got " ++ show d
    where
      natLit 0 = Zero
      natLit k = Suc (natLit (k - 1))

  -- Unit
  TmUnit -> DUnit

  -- Explicit bottom
  Bottom _ -> DBottom

-- | Denote a closed term
denoteClosed :: Term -> Dom
denoteClosed = denote emptyEnv

-- ============================================================
-- Examples: Classic recursively-defined functions
-- ============================================================

-- | Factorial using fix
--
-- fact = fix (λf. λn. if iszero n then 1 else n * f(n-1))
--
-- The denotation is the least function satisfying:
--   f(0) = 1
--   f(n+1) = (n+1) * f(n)
factorialDen :: Integer -> Dom
factorialDen n = denote emptyEnv factTerm
  where
    factTerm = App (Fix factF) (natLit n)

    -- λf. λn. if iszero n then 1 else n * f(pred n)
    factF = Lam "f" (TyArr TyNat TyNat) $
            Lam "n" TyNat $
            If (IsZero (Var "n"))
               (Suc Zero)  -- 1
               (mul (Var "n") (App (Var "f") (Pred (Var "n"))))

    -- Multiplication using natrec
    mul a b = NatRec Zero (Lam "_" TyNat (Lam "acc" TyNat (add a (Var "acc")))) b

    -- Addition using natrec
    add a b = NatRec a (Lam "_" TyNat (Lam "acc" TyNat (Suc (Var "acc")))) b

    natLit 0 = Zero
    natLit k = Suc (natLit (k - 1))

-- | Fibonacci using fix
--
-- fib = fix (λf. λn. if iszero n then 0
--                    else if iszero (pred n) then 1
--                    else f(n-1) + f(n-2))
fibonacciDen :: Integer -> Dom
fibonacciDen n = denote emptyEnv fibTerm
  where
    fibTerm = App (Fix fibF) (natLit n)

    fibF = Lam "f" (TyArr TyNat TyNat) $
           Lam "n" TyNat $
           If (IsZero (Var "n"))
              Zero
              (If (IsZero (Pred (Var "n")))
                  (Suc Zero)
                  (add (App (Var "f") (Pred (Var "n")))
                       (App (Var "f") (Pred (Pred (Var "n"))))))

    add a b = NatRec a (Lam "_" TyNat (Lam "acc" TyNat (Suc (Var "acc")))) b

    natLit 0 = Zero
    natLit k = Suc (natLit (k - 1))
