------------------------------------------------------------------------
-- Evaluation for Simply Typed Lambda Calculus
--
-- This module defines:
-- - Values (canonical forms)
-- - Small-step operational semantics
-- - Multi-step reduction
------------------------------------------------------------------------

module Evaluation where

open import Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)

------------------------------------------------------------------------
-- Values

-- | A term is a value (canonical form)
data Value : ∀ {Γ τ} → Γ ⊢ τ → Set where
  V-ƛ     : ∀ {Γ τ₁ τ₂} {t : (Γ ▸ τ₁) ⊢ τ₂}
          → Value (ƛ t)

  V-true  : ∀ {Γ}
          → Value {Γ} `true

  V-false : ∀ {Γ}
          → Value {Γ} `false

  V-zero  : ∀ {Γ}
          → Value {Γ} `zero

  V-suc   : ∀ {Γ} {t : Γ ⊢ TyNat}
          → Value t
          → Value (`suc t)

------------------------------------------------------------------------
-- Numeric Values

-- | A value representing a natural number
data NumericValue : ∀ {Γ} → Γ ⊢ TyNat → Set where
  NV-zero : ∀ {Γ}
          → NumericValue {Γ} `zero

  NV-suc  : ∀ {Γ} {t : Γ ⊢ TyNat}
          → NumericValue t
          → NumericValue (`suc t)

-- | Numeric values are values
numeric-is-value : ∀ {Γ} {t : Γ ⊢ TyNat} → NumericValue t → Value t
numeric-is-value NV-zero = V-zero
numeric-is-value (NV-suc nv) = V-suc (numeric-is-value nv)

------------------------------------------------------------------------
-- Small-step Operational Semantics (Call-by-Value)

infix 4 _⟶_

-- | Single-step reduction: t ⟶ t'
data _⟶_ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set where

  -- Beta reduction: (λx. t) v ⟶ t[x := v]
  β-ƛ : ∀ {Γ τ₁ τ₂} {t : (Γ ▸ τ₁) ⊢ τ₂} {v : Γ ⊢ τ₁}
    → Value v
    → (ƛ t) · v ⟶ t [ v ]

  -- Reduce function position
  ξ-·₁ : ∀ {Γ τ₁ τ₂} {t₁ t₁' : Γ ⊢ (τ₁ ⇒ τ₂)} {t₂ : Γ ⊢ τ₁}
    → t₁ ⟶ t₁'
    → t₁ · t₂ ⟶ t₁' · t₂

  -- Reduce argument position (function is value)
  ξ-·₂ : ∀ {Γ τ₁ τ₂} {v : Γ ⊢ (τ₁ ⇒ τ₂)} {t₂ t₂' : Γ ⊢ τ₁}
    → Value v
    → t₂ ⟶ t₂'
    → v · t₂ ⟶ v · t₂'

  -- If-true
  β-if-true : ∀ {Γ τ} {t₂ t₃ : Γ ⊢ τ}
    → if `true then t₂ else t₃ ⟶ t₂

  -- If-false
  β-if-false : ∀ {Γ τ} {t₂ t₃ : Γ ⊢ τ}
    → if `false then t₂ else t₃ ⟶ t₃

  -- Reduce condition
  ξ-if : ∀ {Γ τ} {t₁ t₁' : Γ ⊢ TyBool} {t₂ t₃ : Γ ⊢ τ}
    → t₁ ⟶ t₁'
    → if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃

  -- Successor reduction
  ξ-suc : ∀ {Γ} {t t' : Γ ⊢ TyNat}
    → t ⟶ t'
    → `suc t ⟶ `suc t'

  -- Predecessor of zero
  β-pred-zero : ∀ {Γ}
    → `pred {Γ} `zero ⟶ `zero

  -- Predecessor of successor
  β-pred-suc : ∀ {Γ} {v : Γ ⊢ TyNat}
    → Value v
    → `pred (`suc v) ⟶ v

  -- Reduce inside pred
  ξ-pred : ∀ {Γ} {t t' : Γ ⊢ TyNat}
    → t ⟶ t'
    → `pred t ⟶ `pred t'

  -- iszero of zero is true
  β-iszero-zero : ∀ {Γ}
    → `iszero {Γ} `zero ⟶ `true

  -- iszero of suc is false
  β-iszero-suc : ∀ {Γ} {v : Γ ⊢ TyNat}
    → Value v
    → `iszero (`suc v) ⟶ `false

  -- Reduce inside iszero
  ξ-iszero : ∀ {Γ} {t t' : Γ ⊢ TyNat}
    → t ⟶ t'
    → `iszero t ⟶ `iszero t'

------------------------------------------------------------------------
-- Multi-step Reduction

-- | Reflexive-transitive closure of reduction
data _⟶*_ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set where
  _∎ : ∀ {Γ τ} (t : Γ ⊢ τ)
    → t ⟶* t

  _⟶⟨_⟩_ : ∀ {Γ τ} (t₁ : Γ ⊢ τ) {t₂ t₃ : Γ ⊢ τ}
    → t₁ ⟶ t₂
    → t₂ ⟶* t₃
    → t₁ ⟶* t₃

infix  2 _⟶*_
infixr 2 _⟶⟨_⟩_
infix  3 _∎

-- | Transitivity of multi-step
trans* : ∀ {Γ τ} {t₁ t₂ t₃ : Γ ⊢ τ}
  → t₁ ⟶* t₂
  → t₂ ⟶* t₃
  → t₁ ⟶* t₃
trans* (_ ∎) r₂ = r₂
trans* (t₁ ⟶⟨ step ⟩ r₁) r₂ = t₁ ⟶⟨ step ⟩ trans* r₁ r₂

------------------------------------------------------------------------
-- Example Reductions

-- | (λx:Bool. x) true ⟶* true
example1 : (ƛ (` Z)) · `true ⟶* `true
example1 = (ƛ (` Z)) · `true ⟶⟨ β-ƛ V-true ⟩ (_∎ {∅} `true)

-- | if true then zero else (suc zero) ⟶* zero
example2 : if `true then `zero else (`suc `zero) ⟶* `zero
example2 = if `true then `zero else (`suc `zero) ⟶⟨ β-if-true ⟩ (_∎ {∅} `zero)

-- | pred (suc zero) ⟶* zero
example3 : `pred (`suc `zero) ⟶* `zero
example3 = `pred (`suc `zero) ⟶⟨ β-pred-suc V-zero ⟩ (_∎ {∅} `zero)

-- | iszero zero ⟶* true
example4 : `iszero `zero ⟶* `true
example4 = `iszero `zero ⟶⟨ β-iszero-zero ⟩ (_∎ {∅} `true)
