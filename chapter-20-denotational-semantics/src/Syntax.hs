-- | Syntax for Denotational Semantics
--
-- A simple PCF-like language with:
--   - Booleans and natural numbers
--   - Functions
--   - Recursion (fix)
--   - Conditional
--
-- The key feature is 'fix' which allows us to demonstrate
-- least fixed point semantics.

module Syntax
  ( -- * Names
    Name
    -- * Types
  , Type(..)
    -- * Terms
  , Term(..)
  ) where

-- | Variable names
type Name = String

-- | Types
--
-- Simple types with base types and functions.
-- In domain theory, each type denotes a domain (CPO).
data Type
  = TyBool                   -- ^ Domain: {⊥, true, false}
  | TyNat                    -- ^ Domain: {⊥, 0, 1, 2, ...} (flat)
  | TyArr Type Type          -- ^ Domain: [A → B] continuous functions
  | TyUnit                   -- ^ Domain: {⊥, ()}
  deriving (Eq, Show)

-- | Terms
--
-- The denotation [[t]] maps each term to an element of its type's domain.
data Term
  -- Variables
  = Var Name

  -- Lambda abstraction: [[λx. e]] = λd. [[e]][x ↦ d]
  | Lam Name Type Term

  -- Application: [[e1 e2]] = [[e1]]([[e2]])
  | App Term Term

  -- Let binding: [[let x = e1 in e2]] = [[e2]][x ↦ [[e1]]]
  | Let Name Term Term

  -- Fixed point: [[fix f]] = ⊔ {f^n(⊥) | n ∈ ℕ}
  -- This is the key to modeling recursion!
  | Fix Term

  -- Booleans
  | TmTrue                   -- [[true]] = true
  | TmFalse                  -- [[false]] = false
  | If Term Term Term        -- [[if c then t else e]] = cond([[c]], [[t]], [[e]])

  -- Natural numbers (using flat domain)
  | Zero                     -- [[0]] = 0
  | Suc Term                 -- [[suc n]] = [[n]] + 1
  | Pred Term                -- [[pred n]] = max(0, [[n]] - 1)
  | IsZero Term              -- [[iszero n]] = ([[n]] == 0)

  -- NatRec for primitive recursion
  -- natrec z s n = if n=0 then z else s (n-1) (natrec z s (n-1))
  | NatRec Term Term Term

  -- Unit
  | TmUnit                   -- [[unit]] = ()

  -- Explicit bottom (for demonstration)
  | Bottom Type              -- [[⊥]] = ⊥_A

  deriving (Eq, Show)
