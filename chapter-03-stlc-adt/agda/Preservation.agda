------------------------------------------------------------------------
-- Chapter 3: STLC with ADTs - Preservation
--
-- Preservation is trivial with intrinsically-typed terms: the type
-- is part of the term itself, so it cannot change during reduction.
--
-- This module proves determinism of evaluation instead.
------------------------------------------------------------------------

module Preservation where

open import Syntax
open import Evaluation
open import Progress using (value-no-step)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Preservation (trivial with intrinsic typing)

-- The preservation theorem states that if Γ ⊢ t : τ and t ⟶ t',
-- then Γ ⊢ t' : τ. With intrinsically-typed terms, this is trivial
-- because the type τ is baked into the term definition.
--
-- The step relation _⟶_ has type:
--   _⟶_ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set
--
-- So if t ⟶ t', then t and t' must have the same type τ by definition.

-- With intrinsic typing, preservation is a consequence of the type indices.
-- The step relation _⟶_ has type: ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set
-- So if t ⟶ t', both t and t' have the same type τ by construction.

------------------------------------------------------------------------
-- Determinism of evaluation

determinism : ∀ {Γ τ} {t t₁ t₂ : Γ ⊢ τ}
  → t ⟶ t₁
  → t ⟶ t₂
  → t₁ ≡ t₂

-- Application
determinism (β-ƛ v₁) (β-ƛ v₂) = refl
determinism (β-ƛ v) (ξ-·₁ s) = ⊥-elim (value-no-step V-ƛ s)
determinism (β-ƛ v) (ξ-·₂ V-ƛ s) = ⊥-elim (value-no-step v s)
determinism (ξ-·₁ s) (β-ƛ v) = ⊥-elim (value-no-step V-ƛ s)
determinism (ξ-·₁ s₁) (ξ-·₁ s₂) rewrite determinism s₁ s₂ = refl
determinism (ξ-·₁ s₁) (ξ-·₂ v s₂) = ⊥-elim (value-no-step v s₁)
determinism (ξ-·₂ v s) (β-ƛ v') = ⊥-elim (value-no-step v' s)
determinism (ξ-·₂ v s₁) (ξ-·₁ s₂) = ⊥-elim (value-no-step v s₂)
determinism (ξ-·₂ v₁ s₁) (ξ-·₂ v₂ s₂) rewrite determinism s₁ s₂ = refl

-- If-then-else
determinism β-if-true β-if-true = refl
determinism β-if-true (ξ-if s) = ⊥-elim (value-no-step V-true s)
determinism β-if-false β-if-false = refl
determinism β-if-false (ξ-if s) = ⊥-elim (value-no-step V-false s)
determinism (ξ-if s) β-if-true = ⊥-elim (value-no-step V-true s)
determinism (ξ-if s) β-if-false = ⊥-elim (value-no-step V-false s)
determinism (ξ-if s₁) (ξ-if s₂) rewrite determinism s₁ s₂ = refl

-- Successor
determinism (ξ-suc s₁) (ξ-suc s₂) rewrite determinism s₁ s₂ = refl

-- Predecessor
determinism β-pred-zero β-pred-zero = refl
determinism β-pred-zero (ξ-pred s) = ⊥-elim (value-no-step V-zero s)
determinism (β-pred-suc v) (β-pred-suc v') = refl
determinism (β-pred-suc v) (ξ-pred (ξ-suc s)) = ⊥-elim (value-no-step v s)
determinism (ξ-pred s) β-pred-zero = ⊥-elim (value-no-step V-zero s)
determinism (ξ-pred (ξ-suc s)) (β-pred-suc v) = ⊥-elim (value-no-step v s)
determinism (ξ-pred s₁) (ξ-pred s₂) rewrite determinism s₁ s₂ = refl

-- IsZero
determinism β-iszero-zero β-iszero-zero = refl
determinism β-iszero-zero (ξ-iszero s) = ⊥-elim (value-no-step V-zero s)
determinism (β-iszero-suc v) (β-iszero-suc v') = refl
determinism (β-iszero-suc v) (ξ-iszero (ξ-suc s)) = ⊥-elim (value-no-step v s)
determinism (ξ-iszero s) β-iszero-zero = ⊥-elim (value-no-step V-zero s)
determinism (ξ-iszero (ξ-suc s)) (β-iszero-suc v) = ⊥-elim (value-no-step v s)
determinism (ξ-iszero s₁) (ξ-iszero s₂) rewrite determinism s₁ s₂ = refl

-- Pairs
determinism (ξ-pair₁ s₁) (ξ-pair₁ s₂) rewrite determinism s₁ s₂ = refl
determinism (ξ-pair₁ s₁) (ξ-pair₂ v _) = ⊥-elim (value-no-step v s₁)
determinism (ξ-pair₂ v _) (ξ-pair₁ s₂) = ⊥-elim (value-no-step v s₂)
determinism (ξ-pair₂ _ s₁) (ξ-pair₂ _ s₂) rewrite determinism s₁ s₂ = refl

-- Fst projection
determinism (β-fst v₁ v₂) (β-fst v₁' v₂') = refl
determinism (β-fst v₁ v₂) (ξ-fst (ξ-pair₁ s)) = ⊥-elim (value-no-step v₁ s)
determinism (β-fst v₁ v₂) (ξ-fst (ξ-pair₂ _ s)) = ⊥-elim (value-no-step v₂ s)
determinism (ξ-fst (ξ-pair₁ s)) (β-fst v₁ v₂) = ⊥-elim (value-no-step v₁ s)
determinism (ξ-fst (ξ-pair₂ _ s)) (β-fst v₁ v₂) = ⊥-elim (value-no-step v₂ s)
determinism (ξ-fst s₁) (ξ-fst s₂) rewrite determinism s₁ s₂ = refl

-- Snd projection
determinism (β-snd v₁ v₂) (β-snd v₁' v₂') = refl
determinism (β-snd v₁ v₂) (ξ-snd (ξ-pair₁ s)) = ⊥-elim (value-no-step v₁ s)
determinism (β-snd v₁ v₂) (ξ-snd (ξ-pair₂ _ s)) = ⊥-elim (value-no-step v₂ s)
determinism (ξ-snd (ξ-pair₁ s)) (β-snd v₁ v₂) = ⊥-elim (value-no-step v₁ s)
determinism (ξ-snd (ξ-pair₂ _ s)) (β-snd v₁ v₂) = ⊥-elim (value-no-step v₂ s)
determinism (ξ-snd s₁) (ξ-snd s₂) rewrite determinism s₁ s₂ = refl

-- Inl
determinism (ξ-inl s₁) (ξ-inl s₂) rewrite determinism s₁ s₂ = refl

-- Inr
determinism (ξ-inr s₁) (ξ-inr s₂) rewrite determinism s₁ s₂ = refl

-- Case
determinism (β-case-inl v₁) (β-case-inl v₂) = refl
determinism (β-case-inl v) (ξ-case (ξ-inl s)) = ⊥-elim (value-no-step v s)
determinism (β-case-inr v₁) (β-case-inr v₂) = refl
determinism (β-case-inr v) (ξ-case (ξ-inr s)) = ⊥-elim (value-no-step v s)
determinism (ξ-case (ξ-inl s)) (β-case-inl v) = ⊥-elim (value-no-step v s)
determinism (ξ-case (ξ-inr s)) (β-case-inr v) = ⊥-elim (value-no-step v s)
determinism (ξ-case s₁) (ξ-case s₂) rewrite determinism s₁ s₂ = refl
