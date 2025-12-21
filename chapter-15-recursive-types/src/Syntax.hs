{-# LANGUAGE LambdaCase #-}

module Syntax
  ( Var, TyVar
  , Type(..)
  , Term(..)
  , freeVars, freeTyVars
  , substVar, substTyVar, freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

type Var = String
type TyVar = String

-- | Types with recursive types (μ)
data Type
  = TyVar TyVar               -- ^ Type variable: α
  | TyBool | TyNat | TyUnit   -- ^ Base types
  | TyFun Type Type           -- ^ Function: T₁ -> T₂
  | TyProd Type Type          -- ^ Product: T₁ × T₂
  | TySum Type Type           -- ^ Sum: T₁ + T₂
  | TyMu TyVar Type           -- ^ Recursive type: μα. T
  deriving (Eq, Show, Ord)

-- | Terms with fold/unfold for iso-recursive types
data Term
  = Var Var
  | Lam Var Type Term | App Term Term
  | TmTrue | TmFalse | TmIf Term Term Term
  | TmZero | TmSucc Term | TmPred Term | TmIsZero Term
  | TmUnit
  | TmPair Term Term | TmFst Term | TmSnd Term
  | TmInl Term Type | TmInr Term Type
  | TmCase Term Var Term Var Term
  | TmLet Var Term Term
  | TmFold Type Term           -- ^ Fold: fold [μα.T] t
  | TmUnfold Type Term         -- ^ Unfold: unfold [μα.T] t
  deriving (Eq, Show)

freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x _ t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> Set.unions [freeVars t1, freeVars t2, freeVars t3]
  TmZero -> Set.empty
  TmSucc t -> freeVars t
  TmPred t -> freeVars t
  TmIsZero t -> freeVars t
  TmUnit -> Set.empty
  TmPair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmFst t -> freeVars t
  TmSnd t -> freeVars t
  TmInl t _ -> freeVars t
  TmInr t _ -> freeVars t
  TmCase t x1 t1 x2 t2 ->
    freeVars t `Set.union` Set.delete x1 (freeVars t1) `Set.union` Set.delete x2 (freeVars t2)
  TmLet x t1 t2 -> freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmFold _ t -> freeVars t
  TmUnfold _ t -> freeVars t

freeTyVars :: Type -> Set TyVar
freeTyVars = \case
  TyVar v -> Set.singleton v
  TyBool -> Set.empty
  TyNat -> Set.empty
  TyUnit -> Set.empty
  TyFun t1 t2 -> freeTyVars t1 `Set.union` freeTyVars t2
  TyProd t1 t2 -> freeTyVars t1 `Set.union` freeTyVars t2
  TySum t1 t2 -> freeTyVars t1 `Set.union` freeTyVars t2
  TyMu v t -> Set.delete v (freeTyVars t)

substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y | y == x -> s | otherwise -> Var y
  Lam y ty t | y == x -> Lam y ty t
             | y `Set.member` freeVars s -> let y' = freshVar y (freeVars s `Set.union` freeVars t)
                                            in Lam y' ty (substVar x s (substVar y (Var y') t))
             | otherwise -> Lam y ty (substVar x s t)
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 -> TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)
  TmUnit -> TmUnit
  TmPair t1 t2 -> TmPair (substVar x s t1) (substVar x s t2)
  TmFst t -> TmFst (substVar x s t)
  TmSnd t -> TmSnd (substVar x s t)
  TmInl t ty -> TmInl (substVar x s t) ty
  TmInr t ty -> TmInr (substVar x s t) ty
  TmCase t y1 t1 y2 t2 ->
    TmCase (substVar x s t)
           y1 (if y1 == x then t1 else substVar x s t1)
           y2 (if y2 == x then t2 else substVar x s t2)
  TmLet y t1 t2 | y == x -> TmLet y (substVar x s t1) t2
                | otherwise -> TmLet y (substVar x s t1) (substVar x s t2)
  TmFold ty t -> TmFold ty (substVar x s t)
  TmUnfold ty t -> TmUnfold ty (substVar x s t)

substTyVar :: TyVar -> Type -> Type -> Type
substTyVar v s = \case
  TyVar w | w == v -> s | otherwise -> TyVar w
  TyBool -> TyBool
  TyNat -> TyNat
  TyUnit -> TyUnit
  TyFun t1 t2 -> TyFun (substTyVar v s t1) (substTyVar v s t2)
  TyProd t1 t2 -> TyProd (substTyVar v s t1) (substTyVar v s t2)
  TySum t1 t2 -> TySum (substTyVar v s t1) (substTyVar v s t2)
  TyMu w t | w == v -> TyMu w t | otherwise -> TyMu w (substTyVar v s t)

freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) (base : [base ++ show n | n <- [(1::Int)..]])
