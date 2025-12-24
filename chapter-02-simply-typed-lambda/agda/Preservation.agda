------------------------------------------------------------------------
-- Preservation Theorem for Simply Typed Lambda Calculus
--
-- Preservation: If Γ ⊢ t : τ and t ⟶ t', then Γ ⊢ t' : τ
--
-- This is the other half of type safety. With intrinsically-typed terms,
-- preservation is "free" - types are indices of terms, so the reduction
-- relation inherently preserves types.
--
-- This module demonstrates why intrinsic typing gives us preservation
-- for free and shows how to state it explicitly.
------------------------------------------------------------------------

module Preservation where

open import Syntax
open import Evaluation
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

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
-- Why This Works: The Key Insight

-- In extrinsic typing (like the Haskell implementation), we have:
--   data Term = Var Var | Lam Var Type Term | App Term Term | ...
--   typeOf : Context → Term → Either TypeError Type
--
-- Preservation must be proven:
--   If typeOf ctx t = Right ty and t ⟶ t'
--   then typeOf ctx t' = Right ty
--
-- In intrinsic typing (this Agda formalization), we have:
--   data _⊢_ : Context → Type → Set  -- Type is an index!
--
-- The reduction relation is:
--   data _⟶_ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set
--
-- Both terms in t ⟶ t' share the same type index τ.
-- Preservation is guaranteed by construction!

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
--   _[_] : (Γ , σ) ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
--
-- This already encodes that substitution preserves types:
-- If M has type τ in (Γ , σ) and N has type σ in Γ,
-- then M[N] has type τ in Γ.

subst-preserves : ∀ {Γ τ σ}
  → (M : (Γ , σ) ⊢ τ)
  → (N : Γ ⊢ σ)
  → Γ ⊢ τ
subst-preserves M N = M [ N ]

------------------------------------------------------------------------
-- Type Safety

-- | Type Safety = Progress + Preservation
--
-- A well-typed closed term either:
-- 1. Is a value (done), or
-- 2. Can step to another well-typed term (progress + preservation)
--
-- And this continues until we reach a value.

-- Combining progress and preservation
open import Progress using (Progress; step; done; progress)

-- | Evaluation preserves types
eval-step : ∀ {τ} → (t : ∅ ⊢ τ) → Progress t
eval-step = progress

-- | Type safety: evaluation of well-typed terms is safe
-- Either we reach a value, or we can keep stepping forever
-- (but we never get stuck on an ill-typed term)

data EvalResult {τ} (t : ∅ ⊢ τ) : Set where
  value : (v : ∅ ⊢ τ) → Value v → t ⟶* v → EvalResult t
  diverges : (∀ n → ∃[ t' ] (steps n t ⟶* t' × Progress t')) → EvalResult t
    where
    steps : ∀ {τ} → ℕ → ∅ ⊢ τ → ∅ ⊢ τ
    steps zero t = t
    steps (suc n) t with progress t
    ... | done _ = t
    ... | step {t'} _ = steps n t'
    open import Data.Nat using (ℕ; zero; suc)

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
determinism (β-ƛ v₁) (ξ-·₂ V-ƛ step₂) = ⊥-elim (value-no-step v₁ step₂)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)

determinism (ξ-·₁ ()) (β-ƛ v₂)
determinism (ξ-·₁ step₁) (ξ-·₁ step₂) = cong (_· _) (determinism step₁ step₂)
determinism (ξ-·₁ step₁) (ξ-·₂ v step₂) = ⊥-elim (value-no-step v step₁)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)

determinism (ξ-·₂ V-ƛ step₁) (β-ƛ v₂) = ⊥-elim (value-no-step v₂ step₁)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)
determinism (ξ-·₂ v step₁) (ξ-·₁ step₂) = ⊥-elim (value-no-step v step₂)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)
determinism (ξ-·₂ v step₁) (ξ-·₂ v' step₂) = cong (_ ·_) (determinism step₁ step₂)

-- If cases
determinism β-if-true β-if-true = refl
determinism β-if-true (ξ-if ())
determinism β-if-false β-if-false = refl
determinism β-if-false (ξ-if ())
determinism (ξ-if ()) β-if-true
determinism (ξ-if ()) β-if-false
determinism (ξ-if step₁) (ξ-if step₂) = cong (λ c → if c then _ else _) (determinism step₁ step₂)

-- Suc case
determinism (ξ-suc step₁) (ξ-suc step₂) = cong `suc (determinism step₁ step₂)

-- Pred cases
determinism β-pred-zero β-pred-zero = refl
determinism β-pred-zero (ξ-pred ())
determinism (β-pred-suc v) (β-pred-suc v') = refl
determinism (β-pred-suc v) (ξ-pred (ξ-suc step)) = ⊥-elim (value-no-step v step)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)
determinism (ξ-pred ()) β-pred-zero
determinism (ξ-pred (ξ-suc step)) (β-pred-suc v) = ⊥-elim (value-no-step v step)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)
determinism (ξ-pred step₁) (ξ-pred step₂) = cong `pred (determinism step₁ step₂)

-- Iszero cases
determinism β-iszero-zero β-iszero-zero = refl
determinism β-iszero-zero (ξ-iszero ())
determinism (β-iszero-suc v) (β-iszero-suc v') = refl
determinism (β-iszero-suc v) (ξ-iszero (ξ-suc step)) = ⊥-elim (value-no-step v step)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)
determinism (ξ-iszero ()) β-iszero-zero
determinism (ξ-iszero (ξ-suc step)) (β-iszero-suc v) = ⊥-elim (value-no-step v step)
  where
  open import Data.Empty using (⊥-elim)
  open import Progress using (value-no-step)
determinism (ξ-iszero step₁) (ξ-iszero step₂) = cong `iszero (determinism step₁ step₂)
