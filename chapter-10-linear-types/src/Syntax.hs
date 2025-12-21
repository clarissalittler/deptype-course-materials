{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables
    Var
    -- * Multiplicities
  , Mult(..)
  , mulMult
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

-- =============================================================================
-- Multiplicities
-- =============================================================================

-- | Multiplicities describe how many times a variable can be used
--
-- In a linear type system:
-- - 'One' (linear): Must be used exactly once
-- - 'Many' (unrestricted): Can be used any number of times (including zero)
--
-- This follows the Linear Haskell design (Bernardy et al. 2017)
data Mult
  = One   -- ^ Linear: must use exactly once
  | Many  -- ^ Unrestricted: can use any number of times
  deriving (Eq, Show, Ord)

-- | Multiply multiplicities
--
-- This is used when composing functions or in nested scopes:
-- - Many * m = Many  (unrestricted propagates)
-- - One * m = m      (linear preserves)
mulMult :: Mult -> Mult -> Mult
mulMult Many _ = Many
mulMult One m = m

-- =============================================================================
-- Types
-- =============================================================================

-- | Types in the linear lambda calculus
--
-- Key additions:
-- - Function types carry a multiplicity annotation
-- - TyLArr: A -o B (linear function, uses argument exactly once)
-- - TyArr: A -> B  (unrestricted function, may use argument many times)
--
-- Following Linear Haskell notation:
-- - A %1 -> B  (linear, uses A exactly once)
-- - A %Many -> B (unrestricted)
-- - A -> B (sugar for A %Many -> B)
-- - A -o B (sugar for A %1 -> B)
data Type
  = TyVar Var                     -- ^ Type variable
  | TyFun Mult Type Type          -- ^ Function with multiplicity: τ₁ -(m)-> τ₂
  | TyBool                        -- ^ Boolean type
  | TyNat                         -- ^ Natural number type
  | TyUnit                        -- ^ Unit type
  | TyPair Type Type              -- ^ Pair type (both components used linearly if pair is)
  | TyBang Type                   -- ^ ! type (makes content unrestricted)
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Terms
-- =============================================================================

-- | Terms in the linear lambda calculus
--
-- Key difference from STLC:
-- - Lambda abstractions are annotated with multiplicity
-- - Let bindings track multiplicity
-- - Pattern matching must respect linear usage
data Term
  = Var Var                       -- ^ Variable
  | Lam Var Mult Type Term        -- ^ λ(x :m τ). t  (m is multiplicity)
  | App Term Term                 -- ^ Application: t₁ t₂
  -- Booleans
  | TmTrue                        -- ^ Boolean: true
  | TmFalse                       -- ^ Boolean: false
  | TmIf Term Term Term           -- ^ Conditional (uses condition linearly if linear)
  -- Natural numbers
  | TmZero                        -- ^ Natural: 0
  | TmSucc Term                   -- ^ Successor: succ t
  | TmPred Term                   -- ^ Predecessor: pred t
  | TmIsZero Term                 -- ^ Zero test: iszero t
  -- Unit
  | TmUnit                        -- ^ Unit value: ()
  -- Pairs (multiplicative conjunction)
  | TmPair Term Term              -- ^ Pair: (t₁, t₂)
  | TmLetPair Var Var Term Term   -- ^ let (x, y) = t₁ in t₂
  -- Bang (makes unrestricted)
  | TmBang Term                   -- ^ !t (promotes to unrestricted)
  | TmLetBang Var Term Term       -- ^ let !x = t₁ in t₂
  -- Let binding with multiplicity
  | TmLet Var Mult Term Term      -- ^ let x :m = t₁ in t₂
  deriving (Eq, Show)

-- =============================================================================
-- Free Variables
-- =============================================================================

-- | Compute the set of free variables in a term
freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x _ _ t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
  TmZero -> Set.empty
  TmSucc t -> freeVars t
  TmPred t -> freeVars t
  TmIsZero t -> freeVars t
  TmUnit -> Set.empty
  TmPair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmLetPair x y t1 t2 ->
    freeVars t1 `Set.union` Set.delete x (Set.delete y (freeVars t2))
  TmBang t -> freeVars t
  TmLetBang x t1 t2 ->
    freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmLet x _ t1 t2 ->
    freeVars t1 `Set.union` Set.delete x (freeVars t2)

-- =============================================================================
-- Substitution
-- =============================================================================

-- | Capture-avoiding substitution: substVar x s t replaces x with s in t
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y
    | y == x -> s
    | otherwise -> Var y
  Lam y m ty t
    | y == x -> Lam y m ty t  -- x is shadowed
    | y `Set.member` fvs ->
        let y' = freshVar y (fvs `Set.union` freeVars t)
            t' = substVar y (Var y') t
        in Lam y' m ty (substVar x s t')
    | otherwise -> Lam y m ty (substVar x s t)
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
  TmUnit -> TmUnit
  TmPair t1 t2 -> TmPair (substVar x s t1) (substVar x s t2)
  TmLetPair y z t1 t2
    | x == y || x == z -> TmLetPair y z (substVar x s t1) t2
    | otherwise ->
        let fvs = freeVars s
            (y', t2') = freshenIfNeeded y fvs t2
            (z', t2'') = freshenIfNeeded z fvs t2'
        in TmLetPair y' z' (substVar x s t1) (substVar x s t2'')
  TmBang t -> TmBang (substVar x s t)
  TmLetBang y t1 t2
    | x == y -> TmLetBang y (substVar x s t1) t2
    | y `Set.member` freeVars s ->
        let y' = freshVar y (freeVars s `Set.union` freeVars t2)
            t2' = substVar y (Var y') t2
        in TmLetBang y' (substVar x s t1) (substVar x s t2')
    | otherwise -> TmLetBang y (substVar x s t1) (substVar x s t2)
  TmLet y m t1 t2
    | x == y -> TmLet y m (substVar x s t1) t2
    | y `Set.member` freeVars s ->
        let y' = freshVar y (freeVars s `Set.union` freeVars t2)
            t2' = substVar y (Var y') t2
        in TmLet y' m (substVar x s t1) (substVar x s t2')
    | otherwise -> TmLet y m (substVar x s t1) (substVar x s t2)

-- | Helper to freshen a variable if needed
freshenIfNeeded :: Var -> Set Var -> Term -> (Var, Term)
freshenIfNeeded y fvs t
  | y `Set.member` fvs =
      let y' = freshVar y (fvs `Set.union` freeVars t)
      in (y', substVar y (Var y') t)
  | otherwise = (y, t)

-- | Generate a fresh variable name
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
