{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables
    Var
    -- * Types
  , Type(..)
  , tyBool
  , tyNat
    -- * Terms
  , Term(..)
    -- * Free variables
  , freeVars
    -- * Substitution
  , substVar
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

-- | Variables are represented as strings
type Var = String

-- | Types in the simply typed lambda calculus
data Type
  = TyVar Var          -- ^ Type variable (for extensibility)
  | TyArr Type Type    -- ^ Function type: τ₁ → τ₂
  | TyBool             -- ^ Boolean type
  | TyNat              -- ^ Natural number type
  deriving (Eq, Show, Ord)

-- | Convenience constructor for Bool type
tyBool :: Type
tyBool = TyBool

-- | Convenience constructor for Nat type
tyNat :: Type
tyNat = TyNat

-- | Simply typed lambda calculus terms
data Term
  = Var Var                    -- ^ Variable
  | Lam Var Type Term          -- ^ Lambda abstraction: λ(x:τ). t
  | App Term Term              -- ^ Application: t1 t2
  -- Booleans
  | TmTrue                     -- ^ Boolean literal: true
  | TmFalse                    -- ^ Boolean literal: false
  | TmIf Term Term Term        -- ^ Conditional: if t1 then t2 else t3
  -- Natural numbers
  | TmZero                     -- ^ Natural number: 0
  | TmSucc Term                -- ^ Successor: succ t
  | TmPred Term                -- ^ Predecessor: pred t
  | TmIsZero Term              -- ^ Zero test: iszero t
  deriving (Eq, Show)

-- | Compute the set of free variables in a term
freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x _ t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
  TmZero -> Set.empty
  TmSucc t -> freeVars t
  TmPred t -> freeVars t
  TmIsZero t -> freeVars t

-- | Capture-avoiding substitution: substVar x s t replaces x with s in t
-- [x ↦ s]t
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y
    | y == x -> s
    | otherwise -> Var y
  Lam y ty t
    | y == x -> Lam y ty t  -- x is shadowed
    | y `Set.member` fvs ->
        -- y is free in s, rename to avoid capture
        let y' = freshVar y (fvs `Set.union` freeVars t)
            t' = substVar y (Var y') t
        in Lam y' ty (substVar x s t')
    | otherwise -> Lam y ty (substVar x s t)
    where
      fvs = freeVars s
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 ->
    TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)

-- | Generate a fresh variable name
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
