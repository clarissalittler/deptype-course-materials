{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables
    Var
  , Label
  , RowVar
    -- * Types
  , Type(..)
  , Row(..)
    -- * Terms
  , Term(..)
    -- * Free variables
  , freeVars
  , freeRowVars
    -- * Substitution
  , substVar
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

-- | Variables are represented as strings
type Var = String

-- | Record labels
type Label = String

-- | Row type variables
type RowVar = String

-- =============================================================================
-- Types
-- =============================================================================

-- | Types with row polymorphism
data Type
  = TyBool                        -- ^ Boolean type
  | TyNat                         -- ^ Natural number type
  | TyUnit                        -- ^ Unit type
  | TyFun Type Type               -- ^ Function type
  | TyRecord Row                  -- ^ Record type: {l₁: T₁, l₂: T₂, ...}
  | TyVariant Row                 -- ^ Variant type: <l₁: T₁ | l₂: T₂ | ...>
  | TyForallRow RowVar Type       -- ^ Row polymorphism: ∀ρ. T
  deriving (Eq, Show, Ord)

-- | Row types for extensible records and variants
data Row
  = RowEmpty                      -- ^ Empty row: ()
  | RowExtend Label Type Row      -- ^ Extension: (l: T | ρ)
  | RowVar RowVar                 -- ^ Row variable: ρ
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Terms
-- =============================================================================

-- | Terms with extensible records
data Term
  = Var Var                       -- ^ Variable
  | Lam Var Type Term             -- ^ Lambda
  | App Term Term                 -- ^ Application
  -- Booleans
  | TmTrue                        -- ^ true
  | TmFalse                       -- ^ false
  | TmIf Term Term Term           -- ^ if-then-else
  -- Natural numbers
  | TmZero                        -- ^ 0
  | TmSucc Term                   -- ^ succ
  | TmPred Term                   -- ^ pred
  | TmIsZero Term                 -- ^ iszero
  -- Unit
  | TmUnit                        -- ^ ()
  -- Records
  | TmRecord (Map Label Term)     -- ^ Record: {l₁ = t₁, l₂ = t₂, ...}
  | TmProj Term Label             -- ^ Projection: t.l
  | TmExtend Term Label Term      -- ^ Extension: {l = t | r}
  | TmRestrict Term Label         -- ^ Restriction: r \ l
  -- Variants
  | TmVariant Label Term Type     -- ^ Variant injection: <l = t> : T
  | TmCase Term [(Label, Var, Term)]  -- ^ Case: case t of <l₁ = x₁> -> t₁ | ...
  -- Let binding
  | TmLet Var Term Term           -- ^ let x = t₁ in t₂
  -- Row abstraction/application
  | TmRowAbs RowVar Term          -- ^ Λρ. t
  | TmRowApp Term Row             -- ^ t [ρ]
  deriving (Eq, Show)

-- =============================================================================
-- Free Variables
-- =============================================================================

-- | Free variables in a term
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
  TmUnit -> Set.empty
  TmRecord fields -> Set.unions (map freeVars (Map.elems fields))
  TmProj t _ -> freeVars t
  TmExtend t1 _ t2 -> freeVars t1 `Set.union` freeVars t2
  TmRestrict t _ -> freeVars t
  TmVariant _ t _ -> freeVars t
  TmCase t cases ->
    freeVars t `Set.union`
    Set.unions [Set.delete x (freeVars body) | (_, x, body) <- cases]
  TmLet x t1 t2 -> freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmRowAbs _ t -> freeVars t
  TmRowApp t _ -> freeVars t

-- | Free row variables in a type
freeRowVars :: Type -> Set RowVar
freeRowVars = \case
  TyBool -> Set.empty
  TyNat -> Set.empty
  TyUnit -> Set.empty
  TyFun t1 t2 -> freeRowVars t1 `Set.union` freeRowVars t2
  TyRecord r -> rowFreeVars r
  TyVariant r -> rowFreeVars r
  TyForallRow v t -> Set.delete v (freeRowVars t)

-- | Free row variables in a row
rowFreeVars :: Row -> Set RowVar
rowFreeVars = \case
  RowEmpty -> Set.empty
  RowExtend _ ty r -> freeRowVars ty `Set.union` rowFreeVars r
  RowVar v -> Set.singleton v

-- =============================================================================
-- Substitution
-- =============================================================================

-- | Substitute a term for a variable
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y
    | y == x -> s
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
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 -> TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)
  TmUnit -> TmUnit
  TmRecord fields -> TmRecord (Map.map (substVar x s) fields)
  TmProj t l -> TmProj (substVar x s t) l
  TmExtend t1 l t2 -> TmExtend (substVar x s t1) l (substVar x s t2)
  TmRestrict t l -> TmRestrict (substVar x s t) l
  TmVariant l t ty -> TmVariant l (substVar x s t) ty
  TmCase t cases ->
    TmCase (substVar x s t)
           [(l, y, if y == x then body else substVar x s body)
           | (l, y, body) <- cases]
  TmLet y t1 t2
    | y == x -> TmLet y (substVar x s t1) t2
    | otherwise -> TmLet y (substVar x s t1) (substVar x s t2)
  TmRowAbs v t -> TmRowAbs v (substVar x s t)
  TmRowApp t r -> TmRowApp (substVar x s t) r

-- | Generate a fresh variable
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
