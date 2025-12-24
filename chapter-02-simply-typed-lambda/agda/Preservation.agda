------------------------------------------------------------------------
-- Preservation Theorem for Simply Typed Lambda Calculus
--
-- Preservation: If Γ ⊢ t : τ and t ⟶ t', then Γ ⊢ t' : τ
--
-- This is the other half of type safety. With intrinsically-typed terms,
-- preservation is "free" - types are indices of terms, so the reduction
-- relation inherently preserves types.
------------------------------------------------------------------------

module Preservation where

open import Syntax
open import Evaluation
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Progress using (Progress; step; done; progress; value-no-step)

------------------------------------------------------------------------
-- Preservation is Free with Intrinsic Typing

-- | With intrinsically-typed terms, preservation is trivial:
-- The reduction relation _⟶_ is typed as:
--   _⟶_ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set
--
-- So if t ⟶ t', then both t and t' have the same type τ in context Γ
-- by the definition of the relation itself!

preservation : ∀ {Γ τ} {t t' : Γ ⊢ τ}
  → t ⟶ t'
  → Γ ⊢ τ  -- t' has the same type as t (which is τ)
preservation {Γ} {τ} {t} {t'} _ = t'

-- | More explicitly: the type of t' equals the type of t
preservation' : ∀ {Γ τ} {t t' : Γ ⊢ τ}
  → t ⟶ t'
  → τ ≡ τ  -- Trivially true!
preservation' _ = refl

------------------------------------------------------------------------
-- Multi-step Preservation

-- | Types are preserved over multiple steps
preservation* : ∀ {Γ τ} {t t' : Γ ⊢ τ}
  → t ⟶* t'
  → Γ ⊢ τ
preservation* {Γ} {τ} {t} {t'} _ = t'

------------------------------------------------------------------------
-- Substitution Preserves Types (Key Lemma)

-- | The single substitution operation is typed as:
--   _[_] : (Γ ▸ σ) ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
--
-- This already encodes that substitution preserves types:
-- If M has type τ in (Γ ▸ σ) and N has type σ in Γ,
-- then M[N] has type τ in Γ.

subst-preserves : ∀ {Γ τ σ}
  → (M : (Γ ▸ σ) ⊢ τ)
  → (N : Γ ⊢ σ)
  → Γ ⊢ τ
subst-preserves M N = M [ N ]

------------------------------------------------------------------------
-- Determinism of Evaluation

-- | Determinism: If t ⟶ t₁ and t ⟶ t₂, then t₁ ≡ t₂
determinism : ∀ {Γ τ} {t t₁ t₂ : Γ ⊢ τ}
  → t ⟶ t₁
  → t ⟶ t₂
  → t₁ ≡ t₂

-- Beta reduction cases
determinism (β-ƛ v₁) (β-ƛ v₂) = refl
determinism (β-ƛ v₁) (ξ-·₁ ())
determinism (β-ƛ v₁) (ξ-·₂ V-ƛ s₂) = ⊥-elim (value-no-step v₁ s₂)

determinism (ξ-·₁ ()) (β-ƛ v₂)
determinism (ξ-·₁ s₁) (ξ-·₁ s₂) = cong (_· _) (determinism s₁ s₂)
determinism (ξ-·₁ s₁) (ξ-·₂ v s₂) = ⊥-elim (value-no-step v s₁)

determinism (ξ-·₂ V-ƛ s₁) (β-ƛ v₂) = ⊥-elim (value-no-step v₂ s₁)
determinism (ξ-·₂ v s₁) (ξ-·₁ s₂) = ⊥-elim (value-no-step v s₂)
determinism (ξ-·₂ v s₁) (ξ-·₂ v' s₂) = cong (_ ·_) (determinism s₁ s₂)

-- If cases
determinism β-if-true β-if-true = refl
determinism β-if-true (ξ-if ())
determinism β-if-false β-if-false = refl
determinism β-if-false (ξ-if ())
determinism (ξ-if ()) β-if-true
determinism (ξ-if ()) β-if-false
determinism (ξ-if s₁) (ξ-if s₂) = cong (λ c → if c then _ else _) (determinism s₁ s₂)

-- Suc case
determinism (ξ-suc s₁) (ξ-suc s₂) = cong `suc (determinism s₁ s₂)

-- Pred cases
determinism β-pred-zero β-pred-zero = refl
determinism β-pred-zero (ξ-pred ())
determinism (β-pred-suc v) (β-pred-suc v') = refl
determinism (β-pred-suc v) (ξ-pred (ξ-suc s)) = ⊥-elim (value-no-step v s)
determinism (ξ-pred ()) β-pred-zero
determinism (ξ-pred (ξ-suc s)) (β-pred-suc v) = ⊥-elim (value-no-step v s)
determinism (ξ-pred s₁) (ξ-pred s₂) = cong `pred (determinism s₁ s₂)

-- Iszero cases
determinism β-iszero-zero β-iszero-zero = refl
determinism β-iszero-zero (ξ-iszero ())
determinism (β-iszero-suc v) (β-iszero-suc v') = refl
determinism (β-iszero-suc v) (ξ-iszero (ξ-suc s)) = ⊥-elim (value-no-step v s)
determinism (ξ-iszero ()) β-iszero-zero
determinism (ξ-iszero (ξ-suc s)) (β-iszero-suc v) = ⊥-elim (value-no-step v s)
determinism (ξ-iszero s₁) (ξ-iszero s₂) = cong `iszero (determinism s₁ s₂)
