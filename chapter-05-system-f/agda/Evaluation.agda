------------------------------------------------------------------------
-- Chapter 5: System F - Evaluation
--
-- This module defines the small-step operational semantics for System F.
-- Values and the basic reduction rules are included; full term-level
-- substitution under type abstraction is complex and omitted for clarity.
------------------------------------------------------------------------

module Evaluation where

open import Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Values (closed terms in normal form)

-- We define values for closed terms (Δ = 0, Γ = ∅)
data Value : ∀ {τ} → _⊢_ {0} ∅ τ → Set where
  -- Lambda abstractions are values
  V-ƛ     : ∀ {τ σ} {t : ∅ ▸ τ ⊢ σ}
          → Value (ƛ t)

  -- Type abstractions are values
  V-Λ     : ∀ {τ} {t : weaken-ctx ∅ ⊢ τ}
          → Value (Λ t)

  -- Booleans
  V-true  : Value `true
  V-false : Value `false

  -- Natural numbers
  V-zero  : Value `zero
  V-suc   : ∀ {t : ∅ ⊢ `ℕ}
          → Value t → Value (`suc t)

------------------------------------------------------------------------
-- Small-step reduction (simplified)

-- Note: Full evaluation for System F requires term substitution that
-- properly handles type abstractions. Here we define the key rules
-- for closed terms where type context Δ = 0.

infix 4 _⟶_

data _⟶_ : ∀ {τ} → _⊢_ {0} ∅ τ → _⊢_ {0} ∅ τ → Set where
  -- If-then-else
  β-if-true  : ∀ {τ} {t₂ t₃ : ∅ ⊢ τ}
             → if `true then t₂ else t₃ ⟶ t₂

  β-if-false : ∀ {τ} {t₂ t₃ : ∅ ⊢ τ}
             → if `false then t₃ else t₃ ⟶ t₃

  ξ-if : ∀ {τ} {t₁ t₁' : ∅ ⊢ `Bool} {t₂ t₃ : ∅ ⊢ τ}
       → t₁ ⟶ t₁'
       → if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃

  -- Successor congruence
  ξ-suc : ∀ {t t' : ∅ ⊢ `ℕ}
        → t ⟶ t'
        → `suc t ⟶ `suc t'

  -- Predecessor
  β-pred-zero : `pred `zero ⟶ `zero

  β-pred-suc  : ∀ {t : ∅ ⊢ `ℕ}
              → Value t
              → `pred (`suc t) ⟶ t

  ξ-pred : ∀ {t t' : ∅ ⊢ `ℕ}
         → t ⟶ t'
         → `pred t ⟶ `pred t'

  -- IsZero
  β-iszero-zero : `iszero `zero ⟶ `true

  β-iszero-suc  : ∀ {t : ∅ ⊢ `ℕ}
                → Value t
                → `iszero (`suc t) ⟶ `false

  ξ-iszero : ∀ {t t' : ∅ ⊢ `ℕ}
           → t ⟶ t'
           → `iszero t ⟶ `iszero t'

  -- Note: Beta reduction for λ and Λ requires term substitution which is
  -- complex with intrinsically-typed terms. The key typing rules are:
  --   β-ƛ : (ƛ t) · v ⟶ t [ v ]           (requires term substitution)
  --   β-Λ : (Λ t) [ σ ] ⟶ t [σ/α]         (requires type subst in term)

------------------------------------------------------------------------
-- Multi-step reduction (reflexive-transitive closure)

infix  2 _⟶*_
infixr 2 _⟶⟨_⟩_
infix  3 _∎

data _⟶*_ {τ} : _⊢_ {0} ∅ τ → _⊢_ {0} ∅ τ → Set where
  _∎ : (t : ∅ ⊢ τ) → t ⟶* t

  _⟶⟨_⟩_ : (t : ∅ ⊢ τ) {t' t'' : ∅ ⊢ τ}
         → t ⟶ t'
         → t' ⟶* t''
         → t ⟶* t''

------------------------------------------------------------------------
-- Example reductions

-- pred (suc 0) ⟶* 0
example-pred : `pred (`suc `zero) ⟶* `zero
example-pred = `pred (`suc `zero)
             ⟶⟨ β-pred-suc V-zero ⟩
             (_∎ `zero)

-- iszero 0 ⟶* true
example-iszero : `iszero `zero ⟶* `true
example-iszero = `iszero `zero
               ⟶⟨ β-iszero-zero ⟩
               (_∎ `true)
