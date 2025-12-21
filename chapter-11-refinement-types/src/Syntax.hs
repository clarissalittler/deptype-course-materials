{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables
    Var
    -- * Types
  , Type(..)
  , BaseType(..)
    -- * Predicates (refinements)
  , Pred(..)
  , PArith(..)
  , ArithOp(..)
  , CompOp(..)
    -- * Terms
  , Term(..)
    -- * Free variables
  , freeVars
  , predFreeVars
    -- * Substitution
  , substVar
  , substPred
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

-- | Variables are represented as strings
type Var = String

-- =============================================================================
-- Base Types
-- =============================================================================

-- | Base types (unrefined)
data BaseType
  = TyBool                    -- ^ Boolean type
  | TyNat                     -- ^ Natural number type
  | TyUnit                    -- ^ Unit type
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Types with Refinements
-- =============================================================================

-- | Types in the refinement type system
--
-- Key addition: TyRefine for refined types
--
-- {x: T | φ(x)} means "values of type T satisfying predicate φ"
--
-- Examples:
-- - {x: Nat | x > 0}         -- Positive naturals
-- - {x: Nat | x < 10}        -- Naturals less than 10
-- - {x: Bool | x = true}     -- The singleton true
data Type
  = TyBase BaseType           -- ^ Base type
  | TyRefine Var Type Pred    -- ^ Refinement: {x: T | φ(x)}
  | TyFun Var Type Type       -- ^ Dependent function: (x: T₁) -> T₂
                              -- ^ (T₂ may mention x)
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Predicates
-- =============================================================================

-- | Predicates for refinement types
--
-- These are logical formulas that can mention term variables.
-- We keep this decidable by restricting to linear arithmetic.
data Pred
  = PTrue                     -- ^ Always true
  | PFalse                    -- ^ Always false
  | PVar Var                  -- ^ Boolean variable
  | PNot Pred                 -- ^ Negation
  | PAnd Pred Pred            -- ^ Conjunction
  | POr Pred Pred             -- ^ Disjunction
  | PImpl Pred Pred           -- ^ Implication
  | PComp CompOp PArith PArith -- ^ Comparison: e₁ op e₂
  deriving (Eq, Show, Ord)

-- | Arithmetic expressions in predicates
data PArith
  = PAVar Var                 -- ^ Variable
  | PALit Int                 -- ^ Literal
  | PAAdd PArith PArith       -- ^ Addition
  | PASub PArith PArith       -- ^ Subtraction
  | PAMul Int PArith          -- ^ Multiplication by constant
  deriving (Eq, Show, Ord)

-- | Comparison operators
data CompOp
  = OpEq                      -- ^ Equality: =
  | OpNeq                     -- ^ Inequality: ≠
  | OpLt                      -- ^ Less than: <
  | OpLe                      -- ^ Less or equal: ≤
  | OpGt                      -- ^ Greater than: >
  | OpGe                      -- ^ Greater or equal: ≥
  deriving (Eq, Show, Ord)

-- | Arithmetic operators (for terms)
data ArithOp
  = Add
  | Sub
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Terms
-- =============================================================================

-- | Terms in the refinement type system
data Term
  = Var Var                   -- ^ Variable
  | Lam Var Type Term         -- ^ Lambda: λ(x: T). t
  | App Term Term             -- ^ Application: t₁ t₂
  -- Booleans
  | TmTrue                    -- ^ Boolean: true
  | TmFalse                   -- ^ Boolean: false
  | TmIf Term Term Term       -- ^ Conditional
  -- Natural numbers
  | TmZero                    -- ^ Zero
  | TmSucc Term               -- ^ Successor
  | TmPred Term               -- ^ Predecessor
  | TmIsZero Term             -- ^ Zero test
  -- Arithmetic
  | TmArith ArithOp Term Term -- ^ Arithmetic: t₁ op t₂
  -- Unit
  | TmUnit                    -- ^ Unit value
  -- Let binding
  | TmLet Var Term Term       -- ^ let x = t₁ in t₂
  -- Ascription (to introduce refinements)
  | TmAscribe Term Type       -- ^ t : T
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
  TmArith _ t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmUnit -> Set.empty
  TmLet x t1 t2 -> freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmAscribe t _ -> freeVars t

-- | Free variables in a predicate
predFreeVars :: Pred -> Set Var
predFreeVars = \case
  PTrue -> Set.empty
  PFalse -> Set.empty
  PVar x -> Set.singleton x
  PNot p -> predFreeVars p
  PAnd p1 p2 -> predFreeVars p1 `Set.union` predFreeVars p2
  POr p1 p2 -> predFreeVars p1 `Set.union` predFreeVars p2
  PImpl p1 p2 -> predFreeVars p1 `Set.union` predFreeVars p2
  PComp _ a1 a2 -> arithFreeVars a1 `Set.union` arithFreeVars a2

-- | Free variables in arithmetic expression
arithFreeVars :: PArith -> Set Var
arithFreeVars = \case
  PAVar x -> Set.singleton x
  PALit _ -> Set.empty
  PAAdd a1 a2 -> arithFreeVars a1 `Set.union` arithFreeVars a2
  PASub a1 a2 -> arithFreeVars a1 `Set.union` arithFreeVars a2
  PAMul _ a -> arithFreeVars a

-- =============================================================================
-- Substitution
-- =============================================================================

-- | Substitute in a term
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
  TmArith op t1 t2 -> TmArith op (substVar x s t1) (substVar x s t2)
  TmUnit -> TmUnit
  TmLet y t1 t2
    | y == x -> TmLet y (substVar x s t1) t2
    | y `Set.member` freeVars s ->
        let y' = freshVar y (freeVars s `Set.union` freeVars t2)
            t2' = substVar y (Var y') t2
        in TmLet y' (substVar x s t1) (substVar x s t2')
    | otherwise -> TmLet y (substVar x s t1) (substVar x s t2)
  TmAscribe t ty -> TmAscribe (substVar x s t) ty

-- | Substitute a variable with an arithmetic expression in a predicate
substPred :: Var -> PArith -> Pred -> Pred
substPred x a = \case
  PTrue -> PTrue
  PFalse -> PFalse
  PVar y
    | y == x -> case a of
        PAVar v -> PVar v
        PALit 0 -> PFalse  -- 0 is false
        PALit _ -> PTrue   -- non-zero is true
        _ -> PVar y        -- Can't substitute complex expr into bool
    | otherwise -> PVar y
  PNot p -> PNot (substPred x a p)
  PAnd p1 p2 -> PAnd (substPred x a p1) (substPred x a p2)
  POr p1 p2 -> POr (substPred x a p1) (substPred x a p2)
  PImpl p1 p2 -> PImpl (substPred x a p1) (substPred x a p2)
  PComp op a1 a2 -> PComp op (substArith x a a1) (substArith x a a2)

-- | Substitute in arithmetic expression
substArith :: Var -> PArith -> PArith -> PArith
substArith x s = \case
  PAVar y
    | y == x -> s
    | otherwise -> PAVar y
  PALit n -> PALit n
  PAAdd a1 a2 -> PAAdd (substArith x s a1) (substArith x s a2)
  PASub a1 a2 -> PASub (substArith x s a1) (substArith x s a2)
  PAMul n a -> PAMul n (substArith x s a)

-- | Generate a fresh variable
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
