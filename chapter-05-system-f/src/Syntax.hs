{-# LANGUAGE LambdaCase #-}

module Syntax
  ( Var, TyVar
  , Type(..), Term(..)
  , freeVars, freeTyVars
  , substVar, substTyVar, substTyVarType
  , freshVar, freshTyVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

type Var = String
type TyVar = String

-- | System F types
data Type
  = TyVar TyVar              -- ^ Type variable α
  | TyArr Type Type          -- ^ Function type τ₁ → τ₂
  | TyForall TyVar Type      -- ^ Universal type ∀α. τ
  | TyBool                   -- ^ Boolean
  | TyNat                    -- ^ Natural numbers
  deriving (Eq, Show, Ord)

-- | System F terms
data Term
  = Var Var                  -- ^ Variable x
  | Lam Var Type Term        -- ^ Lambda λ(x:τ). t
  | App Term Term            -- ^ Application t₁ t₂
  | TyAbs TyVar Term         -- ^ Type abstraction Λα. t
  | TyApp Term Type          -- ^ Type application t [τ]
  -- Booleans
  | TmTrue
  | TmFalse
  | TmIf Term Term Term
  -- Natural numbers
  | TmZero
  | TmSucc Term
  | TmPred Term
  | TmIsZero Term
  deriving (Eq, Show)

-- | Free term variables
freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x _ t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TyAbs _ t -> freeVars t
  TyApp t _ -> freeVars t
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
  TmZero -> Set.empty
  TmSucc t -> freeVars t
  TmPred t -> freeVars t
  TmIsZero t -> freeVars t

-- | Free type variables in a type
freeTyVars :: Type -> Set TyVar
freeTyVars = \case
  TyVar a -> Set.singleton a
  TyArr t1 t2 -> freeTyVars t1 `Set.union` freeTyVars t2
  TyForall a t -> Set.delete a (freeTyVars t)
  TyBool -> Set.empty
  TyNat -> Set.empty

-- | Free type variables in a term
freeTyVarsTerm :: Term -> Set TyVar
freeTyVarsTerm = \case
  Var _ -> Set.empty
  Lam _ ty t -> freeTyVars ty `Set.union` freeTyVarsTerm t
  App t1 t2 -> freeTyVarsTerm t1 `Set.union` freeTyVarsTerm t2
  TyAbs a t -> Set.delete a (freeTyVarsTerm t)
  TyApp t ty -> freeTyVarsTerm t `Set.union` freeTyVars ty
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> freeTyVarsTerm t1 `Set.union` freeTyVarsTerm t2 `Set.union` freeTyVarsTerm t3
  TmZero -> Set.empty
  TmSucc t -> freeTyVarsTerm t
  TmPred t -> freeTyVarsTerm t
  TmIsZero t -> freeTyVarsTerm t

-- | Substitute term variable
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y | y == x -> s
        | otherwise -> Var y
  Lam y ty t
    | y == x -> Lam y ty t
    | y `Set.member` fvs ->
        let y' = freshVar y (fvs `Set.union` freeVars t)
            t' = substVar y (Var y') t
        in Lam y' ty (substVar x s t')
    | otherwise -> Lam y ty (substVar x s t)
    where fvs = freeVars s
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)
  TyAbs a t -> TyAbs a (substVar x s t)
  TyApp t ty -> TyApp (substVar x s t) ty
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 -> TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)

-- | Substitute type variable in type
substTyVarType :: TyVar -> Type -> Type -> Type
substTyVarType a s = \case
  TyVar b | b == a -> s
          | otherwise -> TyVar b
  TyArr t1 t2 -> TyArr (substTyVarType a s t1) (substTyVarType a s t2)
  TyForall b t
    | b == a -> TyForall b t
    | b `Set.member` freeTyVars s ->
        let b' = freshTyVar b (freeTyVars s `Set.union` freeTyVars t)
            t' = substTyVarType b (TyVar b') t
        in TyForall b' (substTyVarType a s t')
    | otherwise -> TyForall b (substTyVarType a s t)
  TyBool -> TyBool
  TyNat -> TyNat

-- | Substitute type variable in term
substTyVar :: TyVar -> Type -> Term -> Term
substTyVar a s = \case
  Var x -> Var x
  Lam x ty t -> Lam x (substTyVarType a s ty) (substTyVar a s t)
  App t1 t2 -> App (substTyVar a s t1) (substTyVar a s t2)
  TyAbs b t
    | b == a -> TyAbs b t
    | b `Set.member` freeTyVars s ->
        let b' = freshTyVar b (freeTyVars s `Set.union` freeTyVarsTerm t)
            t' = substTyVar b (TyVar b') t
        in TyAbs b' (substTyVar a s t')
    | otherwise -> TyAbs b (substTyVar a s t)
  TyApp t ty -> TyApp (substTyVar a s t) (substTyVarType a s ty)
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 -> TmIf (substTyVar a s t1) (substTyVar a s t2) (substTyVar a s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substTyVar a s t)
  TmPred t -> TmPred (substTyVar a s t)
  TmIsZero t -> TmIsZero (substTyVar a s t)

-- | Generate fresh term variable
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]

-- | Generate fresh type variable
freshTyVar :: TyVar -> Set TyVar -> TyVar
freshTyVar base used = head $ filter (`Set.notMember` used) candidates
  where candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
