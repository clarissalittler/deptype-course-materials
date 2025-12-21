{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables
    Var
  , Label
    -- * Types
  , Type(..)
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
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- | Variables are represented as strings
type Var = String

-- | Record field labels
type Label = String

-- | Types in STLC with subtyping
--
-- Key additions for subtyping:
-- - TyTop: The "top" type (supertype of everything)
-- - TyBot: The "bottom" type (subtype of everything)
-- - TyRecord: Record types with width and depth subtyping
--
-- Subtyping relations:
-- - TyBot <: τ <: TyTop  (for all τ)
-- - {l₁:τ₁, ..., lₙ:τₙ, ...} <: {l₁:τ₁, ..., lₙ:τₙ}  (width subtyping)
-- - If τᵢ <: σᵢ then {lᵢ:τᵢ} <: {lᵢ:σᵢ}  (depth subtyping)
-- - If τ₁ <: σ₁ and σ₂ <: τ₂ then σ₁ → σ₂ <: τ₁ → τ₂  (function subtyping)
data Type
  = TyVar Var           -- ^ Type variable (for bounded quantification)
  | TyArr Type Type     -- ^ Function type: τ₁ → τ₂
  | TyBool              -- ^ Boolean type
  | TyNat               -- ^ Natural number type
  | TyTop               -- ^ Top type (supertype of all types)
  | TyBot               -- ^ Bottom type (subtype of all types)
  | TyRecord (Map Label Type)  -- ^ Record type: {l₁: τ₁, l₂: τ₂, ...}
  deriving (Eq, Show, Ord)

-- | Terms in STLC with subtyping
--
-- The term language is similar to Chapter 3 (STLC with ADTs),
-- but type checking uses subtyping instead of equality.
data Term
  = Var Var                     -- ^ Variable
  | Lam Var Type Term           -- ^ Lambda abstraction: λ(x:τ). t
  | App Term Term               -- ^ Application: t₁ t₂
  -- Booleans
  | TmTrue                      -- ^ Boolean literal: true
  | TmFalse                     -- ^ Boolean literal: false
  | TmIf Term Term Term         -- ^ Conditional: if t₁ then t₂ else t₃
  -- Natural numbers
  | TmZero                      -- ^ Natural number: 0
  | TmSucc Term                 -- ^ Successor: succ t
  | TmPred Term                 -- ^ Predecessor: pred t
  | TmIsZero Term               -- ^ Zero test: iszero t
  -- Records
  | TmRecord (Map Label Term)   -- ^ Record: {l₁ = t₁, l₂ = t₂, ...}
  | TmProj Term Label           -- ^ Projection: t.l
  -- Ascription (explicit type annotation for upcasting)
  | TmAscribe Term Type         -- ^ Ascription: t as τ
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
  TmRecord fields -> Set.unions (map freeVars (Map.elems fields))
  TmProj t _ -> freeVars t
  TmAscribe t _ -> freeVars t

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
  TmRecord fields -> TmRecord (Map.map (substVar x s) fields)
  TmProj t l -> TmProj (substVar x s t) l
  TmAscribe t ty -> TmAscribe (substVar x s t) ty

-- | Generate a fresh variable name
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
