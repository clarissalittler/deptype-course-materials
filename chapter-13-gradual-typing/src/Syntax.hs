{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables and Labels
    Var
  , BlameLabel
    -- * Types
  , Type(..)
  , isGround
  , isBaseType
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

-- | Blame labels track the source of type errors
type BlameLabel = String

-- =============================================================================
-- Types
-- =============================================================================

-- | Types in the gradual type system
--
-- Key addition: TyDyn (?) is consistent with any type
data Type
  = TyBool                        -- ^ Boolean type
  | TyNat                         -- ^ Natural number type
  | TyUnit                        -- ^ Unit type
  | TyFun Type Type               -- ^ Function type: T₁ -> T₂
  | TyDyn                         -- ^ Dynamic type: ?
  deriving (Eq, Show, Ord)

-- | Check if a type is a ground type
--
-- Ground types are base types or ? -> ?
-- Used in cast semantics
isGround :: Type -> Bool
isGround TyBool = True
isGround TyNat = True
isGround TyUnit = True
isGround (TyFun TyDyn TyDyn) = True
isGround _ = False

-- | Check if a type is a base type (not function or dynamic)
isBaseType :: Type -> Bool
isBaseType TyBool = True
isBaseType TyNat = True
isBaseType TyUnit = True
isBaseType _ = False

-- =============================================================================
-- Terms
-- =============================================================================

-- | Terms in the gradual type system
data Term
  = Var Var                       -- ^ Variable
  | Lam Var Type Term             -- ^ Lambda: λ(x: T). t
  | App Term Term                 -- ^ Application: t₁ t₂
  -- Booleans
  | TmTrue                        -- ^ true
  | TmFalse                       -- ^ false
  | TmIf Term Term Term           -- ^ if t₁ then t₂ else t₃
  -- Natural numbers
  | TmZero                        -- ^ 0
  | TmSucc Term                   -- ^ succ t
  | TmPred Term                   -- ^ pred t
  | TmIsZero Term                 -- ^ iszero t
  -- Unit
  | TmUnit                        -- ^ ()
  -- Let binding
  | TmLet Var Term Term           -- ^ let x = t₁ in t₂
  -- Casts (explicit type coercions)
  | TmCast Term Type Type BlameLabel
                                  -- ^ Cast: <T₁ => T₂>^l t
                                  -- Cast term from T₁ to T₂, blame l if fails
  -- Ascription
  | TmAscribe Term Type           -- ^ t : T (type annotation)
  -- Blame (runtime error)
  | TmBlame Type BlameLabel       -- ^ blame^l : T (error with blame)
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
  TmLet x t1 t2 -> freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmCast t _ _ _ -> freeVars t
  TmAscribe t _ -> freeVars t
  TmBlame _ _ -> Set.empty

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
  TmLet y t1 t2
    | y == x -> TmLet y (substVar x s t1) t2
    | y `Set.member` freeVars s ->
        let y' = freshVar y (freeVars s `Set.union` freeVars t2)
            t2' = substVar y (Var y') t2
        in TmLet y' (substVar x s t1) (substVar x s t2')
    | otherwise -> TmLet y (substVar x s t1) (substVar x s t2)
  TmCast t ty1 ty2 l -> TmCast (substVar x s t) ty1 ty2 l
  TmAscribe t ty -> TmAscribe (substVar x s t) ty
  TmBlame ty l -> TmBlame ty l

-- | Generate a fresh variable
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
