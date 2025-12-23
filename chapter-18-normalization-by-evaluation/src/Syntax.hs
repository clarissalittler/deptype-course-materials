{-# LANGUAGE DeriveFunctor #-}
-- | Syntax for Normalization by Evaluation
--
-- We use a simple dependently-typed lambda calculus.
-- The key insight of NbE is separating:
--   - Syntactic terms (what we write)
--   - Semantic values (what we compute with)
--   - Normal forms (canonical representations)

module Syntax
  ( -- * Names and Levels
    Name
  , Lvl
  , Ix
    -- * Syntactic Terms
  , Term(..)
    -- * Normal Forms
  , Nf(..)
  , Ne(..)
    -- * Utilities
  , lvl2Ix
  ) where

-- | Variable names (for surface syntax)
type Name = String

-- | De Bruijn levels (count from the outside)
-- Used in semantic domain for fresh variable generation
type Lvl = Int

-- | De Bruijn indices (count from the inside)
-- Used in syntactic terms
type Ix = Int

-- | Syntactic terms
--
-- These are what the programmer writes.
-- We use de Bruijn indices for variables.
data Term
  = TVar Ix                  -- ^ Variable (de Bruijn index)
  | TLam Name Term           -- ^ Lambda abstraction
  | TApp Term Term           -- ^ Application
  | TPi Name Term Term       -- ^ Pi type: (x : A) -> B
  | TU                       -- ^ Universe (Type)
  | TLet Name Term Term Term -- ^ Let: let x : A = t in u
  -- Booleans for examples
  | TBool                    -- ^ Bool type
  | TTrue                    -- ^ true
  | TFalse                   -- ^ false
  | TIf Term Term Term       -- ^ if b then t else f
  -- Natural numbers
  | TNat                     -- ^ Nat type
  | TZero                    -- ^ zero
  | TSuc Term                -- ^ successor
  | TNatElim Term Term Term Term -- ^ natElim P z s n
  deriving (Eq, Show)

-- | Normal forms
--
-- Normal forms are terms in a canonical representation.
-- They're either:
--   - A lambda (introduction form)
--   - A neutral term (can't reduce further because of a variable)
--
-- The distinction is important: we can always compare normal forms
-- syntactically for equality.
data Nf
  = NfLam Name Nf            -- ^ Lambda in normal form
  | NfPi Name Nf Nf          -- ^ Pi type in normal form
  | NfU                      -- ^ Universe
  | NfNe Ne                  -- ^ Neutral term
  | NfBool                   -- ^ Bool type
  | NfTrue                   -- ^ true
  | NfFalse                  -- ^ false
  | NfNat                    -- ^ Nat type
  | NfZero                   -- ^ zero
  | NfSuc Nf                 -- ^ successor
  deriving (Eq, Show)

-- | Neutral terms
--
-- A neutral term is "stuck" on a variable.
-- We can't reduce it further without knowing what the variable is.
data Ne
  = NeVar Lvl                -- ^ Variable (as de Bruijn level)
  | NeApp Ne Nf              -- ^ Application to neutral
  | NeIf Ne Nf Nf            -- ^ If on neutral condition
  | NeNatElim Nf Nf Nf Ne    -- ^ NatElim on neutral number
  deriving (Eq, Show)

-- | Convert de Bruijn level to index
--
-- If we're at depth `l` and have level `x`:
--   index = l - x - 1
lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix l x = l - x - 1
