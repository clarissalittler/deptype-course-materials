{-# LANGUAGE LambdaCase #-}

module Syntax
  ( Var
  , Type(..)
  , Term(..)
  , freeVars
  , substVar, substType
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

type Var = String

-- | Types in a simplified HoTT
-- We use a simplified version with identity types but without full dependent types
data Type
  = TyVar Var                   -- ^ Type variable
  | TyBool                      -- ^ Booleans
  | TyNat                       -- ^ Natural numbers
  | TyUnit                      -- ^ Unit type
  | TyVoid                      -- ^ Empty type (⊥)
  | TyFun Type Type             -- ^ Function type: A → B
  | TyProd Type Type            -- ^ Product type: A × B
  | TySum Type Type             -- ^ Sum type: A + B
  | TyId Type Term Term         -- ^ Identity type: Id A a b (a =_A b)
  | TyUniverse                  -- ^ Universe of small types (Type)
  deriving (Show)

-- Custom Eq instance that ignores terms in identity types for structural comparison
-- (This is a simplification; real HoTT would need propositional equality)
instance Eq Type where
  TyVar x == TyVar y = x == y
  TyBool == TyBool = True
  TyNat == TyNat = True
  TyUnit == TyUnit = True
  TyVoid == TyVoid = True
  TyFun a1 b1 == TyFun a2 b2 = a1 == a2 && b1 == b2
  TyProd a1 b1 == TyProd a2 b2 = a1 == a2 && b1 == b2
  TySum a1 b1 == TySum a2 b2 = a1 == a2 && b1 == b2
  TyId t1 a1 b1 == TyId t2 a2 b2 = t1 == t2 && a1 == a2 && b1 == b2
  TyUniverse == TyUniverse = True
  _ == _ = False

-- | Terms with identity type operations
data Term
  = Var Var
  | Lam Var Type Term
  | App Term Term
  -- Booleans
  | TmTrue
  | TmFalse
  | TmIf Term Term Term
  -- Natural numbers
  | TmZero
  | TmSucc Term
  | TmPred Term
  | TmIsZero Term
  -- Unit
  | TmUnit
  -- Void elimination
  | TmAbsurd Type Term          -- ^ absurd : ⊥ → A
  -- Products
  | TmPair Term Term
  | TmFst Term
  | TmSnd Term
  -- Sums
  | TmInl Term Type
  | TmInr Term Type
  | TmCase Term Var Term Var Term
  -- Let binding
  | TmLet Var Term Term
  -- Identity type introduction
  | TmRefl Type Term            -- ^ refl : a =_A a
  -- Identity type elimination (J eliminator / path induction)
  -- J : (C : (x y : A) → (x = y) → Type) →
  --     ((x : A) → C x x refl) →
  --     (a b : A) → (p : a = b) → C a b p
  | TmJ Type                    -- ^ The motive type
        Term                    -- ^ The base case: (x : A) → C x x refl
        Term                    -- ^ First endpoint
        Term                    -- ^ Second endpoint
        Term                    -- ^ The path
  -- Derived operations (could be defined via J, but provided for convenience)
  | TmSym Term                  -- ^ sym : (a = b) → (b = a)
  | TmTrans Term Term           -- ^ trans : (a = b) → (b = c) → (a = c)
  | TmAp Term Term              -- ^ ap f : (a = b) → (f a = f b)
  | TmTransport Type Term Term  -- ^ transport : (P : A → Type) → (a = b) → P a → P b
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
  TmAbsurd _ t -> freeVars t
  TmPair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmFst t -> freeVars t
  TmSnd t -> freeVars t
  TmInl t _ -> freeVars t
  TmInr t _ -> freeVars t
  TmCase t x1 t1 x2 t2 ->
    freeVars t `Set.union` Set.delete x1 (freeVars t1) `Set.union` Set.delete x2 (freeVars t2)
  TmLet x t1 t2 -> freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmRefl _ t -> freeVars t
  TmJ _ base a b p ->
    Set.unions [freeVars base, freeVars a, freeVars b, freeVars p]
  TmSym t -> freeVars t
  TmTrans t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmAp f p -> freeVars f `Set.union` freeVars p
  TmTransport _ p t -> freeVars p `Set.union` freeVars t

substVar :: Var -> Term -> Term -> Term
substVar x s = go
  where
    go = \case
      Var y | y == x -> s | otherwise -> Var y
      Lam y ty t | y == x -> Lam y ty t
                 | y `Set.member` freeVars s ->
                     let y' = freshVar y (freeVars s `Set.union` freeVars t)
                     in Lam y' ty (go (substVar y (Var y') t))
                 | otherwise -> Lam y ty (go t)
      App t1 t2 -> App (go t1) (go t2)
      TmTrue -> TmTrue
      TmFalse -> TmFalse
      TmIf t1 t2 t3 -> TmIf (go t1) (go t2) (go t3)
      TmZero -> TmZero
      TmSucc t -> TmSucc (go t)
      TmPred t -> TmPred (go t)
      TmIsZero t -> TmIsZero (go t)
      TmUnit -> TmUnit
      TmAbsurd ty t -> TmAbsurd ty (go t)
      TmPair t1 t2 -> TmPair (go t1) (go t2)
      TmFst t -> TmFst (go t)
      TmSnd t -> TmSnd (go t)
      TmInl t ty -> TmInl (go t) ty
      TmInr t ty -> TmInr (go t) ty
      TmCase t y1 t1 y2 t2 ->
        TmCase (go t)
               y1 (if y1 == x then t1 else go t1)
               y2 (if y2 == x then t2 else go t2)
      TmLet y t1 t2 | y == x -> TmLet y (go t1) t2
                    | otherwise -> TmLet y (go t1) (go t2)
      TmRefl ty t -> TmRefl ty (go t)
      TmJ ty base a b p -> TmJ ty (go base) (go a) (go b) (go p)
      TmSym t -> TmSym (go t)
      TmTrans t1 t2 -> TmTrans (go t1) (go t2)
      TmAp f p -> TmAp (go f) (go p)
      TmTransport ty p t -> TmTransport ty (go p) (go t)

-- | Substitute a term into a type (for identity types)
substType :: Var -> Term -> Type -> Type
substType x s = \case
  TyVar v -> TyVar v
  TyBool -> TyBool
  TyNat -> TyNat
  TyUnit -> TyUnit
  TyVoid -> TyVoid
  TyFun t1 t2 -> TyFun (substType x s t1) (substType x s t2)
  TyProd t1 t2 -> TyProd (substType x s t1) (substType x s t2)
  TySum t1 t2 -> TySum (substType x s t1) (substType x s t2)
  TyId ty a b -> TyId (substType x s ty) (substVar x s a) (substVar x s b)
  TyUniverse -> TyUniverse

freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) (base : [base ++ show n | n <- [(1::Int)..]])
