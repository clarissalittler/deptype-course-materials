------------------------------------------------------------------------
-- Syntax for Untyped Lambda Calculus
--
-- This module defines the abstract syntax of the untyped lambda calculus
-- using de Bruijn indices to avoid issues with variable capture.
------------------------------------------------------------------------

module Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _≤?_; _<?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n; suc-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Bool using (Bool; true; false; if_then_else_)

------------------------------------------------------------------------
-- Terms with de Bruijn indices

-- | Terms in untyped lambda calculus
-- Variables are represented as de Bruijn indices (natural numbers)
data Term : Set where
  var : ℕ → Term            -- Variable (de Bruijn index)
  lam : Term → Term         -- Lambda abstraction: λ. t
  app : Term → Term → Term  -- Application: t₁ t₂

------------------------------------------------------------------------
-- Shifting (renaming) for de Bruijn indices

-- | Shift all free variables in a term by d, with cutoff c
-- Variables below the cutoff are bound, so we don't shift them
shift : (d : ℕ) → (c : ℕ) → Term → Term
shift d c (var x) with x <? c
... | yes _ = var x        -- Bound variable, don't shift
... | no  _ = var (x + d)  -- Free variable, shift by d
shift d c (lam t) = lam (shift d (suc c) t)
shift d c (app t₁ t₂) = app (shift d c t₁) (shift d c t₂)

-- | Shift for substitution: increase all free variables by 1
↑ : Term → Term
↑ = shift 1 0

------------------------------------------------------------------------
-- Substitution

-- | Substitute term s for variable j in term t
-- [j ↦ s]t
subst : (j : ℕ) → Term → Term → Term
subst j s (var x) with x <? j | j <? x
... | yes _ | _     = var x           -- x < j: variable before j, keep it
... | no  _ | yes _ = var (x ∸ 1)     -- x > j: variable after j, decrement
  where
  _∸_ : ℕ → ℕ → ℕ
  zero ∸ _ = zero
  suc n ∸ zero = suc n
  suc n ∸ suc m = n ∸ m
... | no  _ | no  _ = s               -- x = j: substitute
subst j s (lam t) = lam (subst (suc j) (↑ s) t)
subst j s (app t₁ t₂) = app (subst j s t₁) (subst j s t₂)

-- | Beta reduction substitution: substitute s for the outermost bound variable
-- This is [0 ↦ s]t with appropriate shifting
substTop : Term → Term → Term
substTop s t = shift-down 0 (subst 0 (↑ s) t)
  where
  -- Shift free variables down by 1 (for after substitution)
  shift-down : ℕ → Term → Term
  shift-down c (var x) with x <? c
  ... | yes _ = var x
  ... | no  _ with x
  ...   | zero = var zero  -- This case shouldn't happen for well-formed terms
  ...   | suc n = var n
  shift-down c (lam t) = lam (shift-down (suc c) t)
  shift-down c (app t₁ t₂) = app (shift-down c t₁) (shift-down c t₂)

------------------------------------------------------------------------
-- Example terms

-- | Identity function: λx. x
-- In de Bruijn: λ. 0
idTerm : Term
idTerm = lam (var 0)

-- | Constant function: λx. λy. x
-- In de Bruijn: λ. λ. 1
constTerm : Term
constTerm = lam (lam (var 1))

-- | Omega combinator: (λx. x x)(λx. x x)
-- In de Bruijn: (λ. 0 0)(λ. 0 0)
omega : Term
omega = app (lam (app (var 0) (var 0)))
            (lam (app (var 0) (var 0)))

-- | Church numeral zero: λf. λx. x
-- In de Bruijn: λ. λ. 0
churchZero : Term
churchZero = lam (lam (var 0))

-- | Church numeral successor: λn. λf. λx. f (n f x)
-- In de Bruijn: λ. λ. λ. 1 (2 1 0)
churchSucc : Term
churchSucc = lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

------------------------------------------------------------------------
-- Decidable equality for terms

_≟_ : (t₁ t₂ : Term) → Dec (t₁ ≡ t₂)
var x ≟ var y with x Data.Nat.≟ y
  where open import Data.Nat using (_≟_)
... | yes refl = yes refl
... | no ¬p = no (λ { refl → ¬p refl })
var x ≟ lam t = no (λ ())
var x ≟ app t₁ t₂ = no (λ ())
lam t ≟ var x = no (λ ())
lam t₁ ≟ lam t₂ with t₁ ≟ t₂
... | yes refl = yes refl
... | no ¬p = no (λ { refl → ¬p refl })
lam t ≟ app t₁ t₂ = no (λ ())
app t₁ t₂ ≟ var x = no (λ ())
app t₁ t₂ ≟ lam t = no (λ ())
app t₁ t₂ ≟ app t₁' t₂' with t₁ ≟ t₁' | t₂ ≟ t₂'
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no (λ { refl → ¬p refl })
... | no ¬p | _ = no (λ { refl → ¬p refl })
