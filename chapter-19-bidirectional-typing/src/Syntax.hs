{-# LANGUAGE DeriveFunctor #-}
-- | Syntax for Bidirectional Type Checking
--
-- Key insight: We distinguish between terms that can be *checked* against
-- a known type, and terms whose type can be *inferred*.
--
-- This distinction allows minimal type annotations while maintaining
-- complete type information.

module Syntax
  ( -- * Names
    Name
    -- * Types
  , Type(..)
    -- * Terms
  , Term(..)
    -- * Values (for NbE-based equality)
  , Val(..)
  , Closure(..)
  , Neutral(..)
  , Env
  , emptyEnv
  , extendEnv
  ) where

import qualified Data.Map.Strict as Map

-- | Variable names
type Name = String

-- | Types
--
-- In a simple system, types are separate from terms.
-- In dependent types, they would be unified.
data Type
  = TyVar Name               -- ^ Type variable
  | TyBool                   -- ^ Boolean type
  | TyNat                    -- ^ Natural number type
  | TyArr Type Type          -- ^ Function type A → B
  | TyForall Name Type       -- ^ Universal type ∀α. A
  | TyUnit                   -- ^ Unit type
  | TyProd Type Type         -- ^ Product type A × B
  | TySum Type Type          -- ^ Sum type A + B
  deriving (Eq, Show)

-- | Terms
--
-- We use a single term type but annotate forms as:
--   - Introduction forms: can be checked (↓)
--   - Elimination forms: can be inferred (↑)
--
-- Some terms can go both ways depending on context.
data Term
  -- Variables (↑ inferrable)
  = Var Name

  -- Lambda (↓ checkable only - needs type annotation to infer)
  | Lam Name Term

  -- Annotated lambda (↑ inferrable)
  | LamAnn Name Type Term

  -- Application (↑ inferrable if function is)
  | App Term Term

  -- Type annotation (↑ inferrable - provides the type)
  | Ann Term Type

  -- Let binding (depends on components)
  | Let Name Term Term

  -- Booleans
  | TmTrue                   -- ↓ checkable, ↑ inferrable
  | TmFalse                  -- ↓ checkable, ↑ inferrable
  | If Term Term Term        -- ↑ inferrable (if scrutinee is)

  -- Natural numbers
  | Zero                     -- ↓/↑
  | Suc Term                 -- ↓/↑
  | NatRec Term Term Term    -- natRec z s n

  -- Unit
  | TmUnit                   -- ↓/↑

  -- Pairs
  | Pair Term Term           -- ↓ checkable (need type for components)
  | Fst Term                 -- ↑ inferrable
  | Snd Term                 -- ↑ inferrable

  -- Sums
  | Inl Term                 -- ↓ checkable (need full sum type)
  | Inr Term                 -- ↓ checkable
  | Case Term Name Term Name Term  -- case e of inl x → t1 | inr y → t2

  -- Type abstraction/application (System F)
  | TyLam Name Term          -- Λα. e
  | TyApp Term Type          -- e [τ]
  deriving (Eq, Show)

-- | Values (for normalization)
data Val
  = VBool Bool
  | VNat Integer
  | VUnit
  | VPair Val Val
  | VInl Val
  | VInr Val
  | VLam Name Closure
  | VTyLam Name Closure
  | VNeutral Neutral
  deriving (Eq, Show)

-- | Closure: term + environment
data Closure = Closure Env Term
  deriving (Eq, Show)

-- | Neutral terms (stuck on variable)
data Neutral
  = NVar Name
  | NApp Neutral Val
  | NTyApp Neutral Type
  | NFst Neutral
  | NSnd Neutral
  | NIf Neutral Val Val
  | NCase Neutral Name Val Name Val
  | NNatRec Val Val Neutral
  deriving (Eq, Show)

-- | Environment
type Env = Map.Map Name Val

emptyEnv :: Env
emptyEnv = Map.empty

extendEnv :: Name -> Val -> Env -> Env
extendEnv = Map.insert
