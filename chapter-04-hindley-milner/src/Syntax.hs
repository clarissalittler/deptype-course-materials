{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables
    Var
  , TyVar
    -- * Types
  , Type(..)
  , TypeScheme(..)
    -- * Terms
  , Term(..)
    -- * Free variables
  , freeVars
  , freeTyVars
    -- * Substitution
  , substVar
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

-- | Term variables
type Var = String

-- | Type variables
type TyVar = String

-- | Monotypes (types without ∀)
data Type
  = TyVar TyVar              -- ^ Type variable α
  | TyArr Type Type          -- ^ Function type τ₁ → τ₂
  | TyBool                   -- ^ Boolean type
  | TyNat                    -- ^ Natural number type
  | TyProd Type Type         -- ^ Product type τ₁ × τ₂
  | TyList Type              -- ^ List type
  deriving (Eq, Show, Ord)

-- | Type schemes (polytypes with ∀)
-- ∀α₁...αₙ. τ
data TypeScheme = TypeScheme [TyVar] Type
  deriving (Eq, Show)

-- | Terms (no type annotations needed!)
data Term
  = Var Var                  -- ^ Variable
  | Lam Var Term             -- ^ Lambda (no type annotation!)
  | App Term Term            -- ^ Application
  | Let Var Term Term        -- ^ Let binding: let x = t1 in t2
  -- Booleans
  | TmTrue
  | TmFalse
  | TmIf Term Term Term
  -- Natural numbers
  | TmZero
  | TmSucc Term
  | TmPred Term
  | TmIsZero Term
  -- Pairs
  | TmPair Term Term
  | TmFst Term
  | TmSnd Term
  -- Lists
  | TmNil
  | TmCons Term Term
  | TmIsNil Term
  | TmHead Term
  | TmTail Term
  deriving (Eq, Show)

-- | Free term variables
freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Let x t1 t2 -> freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
  TmZero -> Set.empty
  TmSucc t -> freeVars t
  TmPred t -> freeVars t
  TmIsZero t -> freeVars t
  TmPair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmFst t -> freeVars t
  TmSnd t -> freeVars t
  TmNil -> Set.empty
  TmCons t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmIsNil t -> freeVars t
  TmHead t -> freeVars t
  TmTail t -> freeVars t

-- | Free type variables in a type
freeTyVars :: Type -> Set TyVar
freeTyVars = \case
  TyVar a -> Set.singleton a
  TyArr t1 t2 -> freeTyVars t1 `Set.union` freeTyVars t2
  TyBool -> Set.empty
  TyNat -> Set.empty
  TyProd t1 t2 -> freeTyVars t1 `Set.union` freeTyVars t2
  TyList t -> freeTyVars t

-- | Substitution for term variables
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y | y == x -> s
        | otherwise -> Var y
  Lam y t | y == x -> Lam y t
          | y `Set.member` fvs ->
              let y' = freshVar y (fvs `Set.union` freeVars t)
                  t' = substVar y (Var y') t
              in Lam y' (substVar x s t')
          | otherwise -> Lam y (substVar x s t)
    where fvs = freeVars s
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)
  Let y t1 t2
    | y == x -> Let y (substVar x s t1) t2
    | otherwise -> Let y (substVar x s t1) (substVar x s t2)
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 -> TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)
  TmPair t1 t2 -> TmPair (substVar x s t1) (substVar x s t2)
  TmFst t -> TmFst (substVar x s t)
  TmSnd t -> TmSnd (substVar x s t)
  TmNil -> TmNil
  TmCons t1 t2 -> TmCons (substVar x s t1) (substVar x s t2)
  TmIsNil t -> TmIsNil (substVar x s t)
  TmHead t -> TmHead (substVar x s t)
  TmTail t -> TmTail (substVar x s t)

-- | Generate fresh variable
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
