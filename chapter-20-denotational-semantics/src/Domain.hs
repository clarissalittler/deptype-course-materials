{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Domain Theory for Denotational Semantics
--
-- Domains are complete partial orders (CPOs) with a least element ⊥.
-- They provide the mathematical foundation for giving meaning to programs.
--
-- Key concepts:
--   - Partial order (⊑): approximation relation
--   - Least element (⊥): undefined/non-terminating computation
--   - Directed sets and their suprema (⊔)
--   - Continuous functions: preserve suprema of directed sets
--   - Least fixed points: solution to recursive equations
--
-- In Haskell, we use laziness to represent domains. The key insight is that
-- Haskell's undefined/bottom corresponds to ⊥ in domain theory.

module Domain
  ( -- * Semantic Domains
    Dom(..)
  , DomFun
    -- * Domain Operations
  , isBottom
  , approx
    -- * Fixed Point
  , fix
  , fixN
    -- * Utilities
  , domBool
  , domNat
  , domApp
  ) where

import Control.Exception (evaluate, catch, SomeException)
import System.IO.Unsafe (unsafePerformIO)

-- | Semantic domains
--
-- We represent domains using Haskell types, leveraging Haskell's
-- laziness to model ⊥ (non-termination).
--
-- Each constructor corresponds to a point in the domain.
-- The implicit ⊥ is represented by Haskell's undefined/non-termination.
data Dom
  = DBottom                    -- ^ Explicit bottom (for demonstration)
  | DBool Bool                 -- ^ Boolean values
  | DNat Integer               -- ^ Natural number values
  | DUnit                      -- ^ Unit value
  | DFun DomFun                -- ^ Function values

instance Show Dom where
  show DBottom = "⊥"
  show (DBool b) = show b
  show (DNat n) = show n
  show DUnit = "()"
  show (DFun _) = "<function>"

-- | Function domain: continuous functions A → B
--
-- In domain theory, function spaces [A → B] consist of all
-- Scott-continuous functions from A to B.
type DomFun = Dom -> Dom

-- We can't derive Eq for functions, but we can check basic values
instance Eq Dom where
  DBottom == DBottom = True
  DBool a == DBool b = a == b
  DNat a == DNat b = a == b
  DUnit == DUnit = True
  _ == _ = False  -- Functions can't be compared

-- | Check if a value is bottom (undefined/non-terminating)
--
-- Uses unsafePerformIO to catch evaluation errors.
-- This is for demonstration purposes only!
isBottom :: Dom -> Bool
isBottom d = unsafePerformIO $ do
  result <- catch (evaluate d >> return False)
                  (\(_ :: SomeException) -> return True)
  return result

-- | Approximation ordering: d1 ⊑ d2
--
-- In a flat domain (like Nat):
--   ⊥ ⊑ n for all n
--   n ⊑ n for all n
--   n ⊑ m only if n = m (for defined values)
approx :: Dom -> Dom -> Bool
approx DBottom _ = True
approx _ DBottom = False
approx (DBool a) (DBool b) = a == b
approx (DNat a) (DNat b) = a == b
approx DUnit DUnit = True
approx _ _ = False  -- Functions need extensional equality

-- | Fixed point combinator
--
-- The fixed point of f is: fix f = ⊔ₙ f^n(⊥)
--
-- By the Kleene fixed point theorem, if D is a CPO and f : D → D
-- is continuous, then fix f = ⊔ₙ f^n(⊥) is the least fixed point of f.
--
-- In Haskell, this is just the standard fix, taking advantage of laziness.
fix :: (Dom -> Dom) -> Dom
fix f = let x = f x in x

-- | Compute n iterations of the fixed point approximation
--
-- This shows how the fixed point is approached:
--   f^0(⊥) = ⊥
--   f^1(⊥) = f(⊥)
--   f^2(⊥) = f(f(⊥))
--   ...
--
-- The chain ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ ... has supremum = fix f
fixN :: Int -> (Dom -> Dom) -> Dom
fixN 0 _ = DBottom
fixN n f = f (fixN (n-1) f)

-- | Smart constructor for booleans
domBool :: Bool -> Dom
domBool = DBool

-- | Smart constructor for naturals
domNat :: Integer -> Dom
domNat = DNat

-- | Apply a function domain value
domApp :: Dom -> Dom -> Dom
domApp (DFun f) d = f d
domApp DBottom _ = DBottom  -- Strict in function position
domApp d _ = error $ "domApp: expected function, got " ++ show d
