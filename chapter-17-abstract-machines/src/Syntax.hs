{-# LANGUAGE DeriveFunctor #-}
-- | Syntax for Abstract Machines
--
-- This module defines the shared syntax used across different abstract machines.
-- We use a simple call-by-value lambda calculus with basic arithmetic.

module Syntax
  ( -- * Terms
    Term(..)
  , Var
    -- * Values
  , Value(..)
    -- * Environments
  , Env
  , emptyEnv
  , lookupEnv
  , extendEnv
    -- * Utilities
  , freeVars
  , subst
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- | Variable names
type Var = String

-- | Lambda calculus terms with arithmetic
data Term
  = TmVar Var                    -- ^ Variable reference
  | TmLam Var Term               -- ^ Lambda abstraction
  | TmApp Term Term              -- ^ Application
  | TmInt Integer                -- ^ Integer literal
  | TmAdd Term Term              -- ^ Addition
  | TmSub Term Term              -- ^ Subtraction
  | TmMul Term Term              -- ^ Multiplication
  | TmIf0 Term Term Term         -- ^ If-zero conditional
  | TmLet Var Term Term          -- ^ Let binding (for convenience)
  | TmFix Term                   -- ^ Fixed point (for recursion)
  deriving (Eq, Show)

-- | Runtime values
--
-- Note: Closures capture the environment at definition time.
-- This is the key insight that abstract machines make explicit.
data Value
  = VInt Integer                 -- ^ Integer value
  | VClosure Var Term Env        -- ^ Closure = lambda + environment
  deriving (Eq, Show)

-- | Environment mapping variables to values
type Env = Map Var Value

-- | Empty environment
emptyEnv :: Env
emptyEnv = Map.empty

-- | Look up a variable in the environment
lookupEnv :: Var -> Env -> Maybe Value
lookupEnv = Map.lookup

-- | Extend environment with a new binding
extendEnv :: Var -> Value -> Env -> Env
extendEnv = Map.insert

-- | Compute free variables of a term
freeVars :: Term -> Set Var
freeVars (TmVar x) = Set.singleton x
freeVars (TmLam x t) = Set.delete x (freeVars t)
freeVars (TmApp t1 t2) = freeVars t1 `Set.union` freeVars t2
freeVars (TmInt _) = Set.empty
freeVars (TmAdd t1 t2) = freeVars t1 `Set.union` freeVars t2
freeVars (TmSub t1 t2) = freeVars t1 `Set.union` freeVars t2
freeVars (TmMul t1 t2) = freeVars t1 `Set.union` freeVars t2
freeVars (TmIf0 t1 t2 t3) = freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
freeVars (TmLet x t1 t2) = freeVars t1 `Set.union` Set.delete x (freeVars t2)
freeVars (TmFix t) = freeVars t

-- | Substitution (for reference semantics comparison)
subst :: Var -> Term -> Term -> Term
subst x s (TmVar y)
  | x == y    = s
  | otherwise = TmVar y
subst x s (TmLam y t)
  | x == y    = TmLam y t  -- x is shadowed
  | otherwise = TmLam y (subst x s t)
subst x s (TmApp t1 t2) = TmApp (subst x s t1) (subst x s t2)
subst _ _ (TmInt n) = TmInt n
subst x s (TmAdd t1 t2) = TmAdd (subst x s t1) (subst x s t2)
subst x s (TmSub t1 t2) = TmSub (subst x s t1) (subst x s t2)
subst x s (TmMul t1 t2) = TmMul (subst x s t1) (subst x s t2)
subst x s (TmIf0 t1 t2 t3) = TmIf0 (subst x s t1) (subst x s t2) (subst x s t3)
subst x s (TmLet y t1 t2)
  | x == y    = TmLet y (subst x s t1) t2
  | otherwise = TmLet y (subst x s t1) (subst x s t2)
subst x s (TmFix t) = TmFix (subst x s t)
