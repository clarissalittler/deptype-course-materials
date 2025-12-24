------------------------------------------------------------------------
-- Chapter 3: STLC with ADTs - Progress
--
-- This module proves the progress theorem: every well-typed closed term
-- is either a value or can take a step.
------------------------------------------------------------------------

module Progress where

open import Syntax
open import Evaluation
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Progress: well-typed closed terms are either values or can step

data Progress {τ} (t : ∅ ⊢ τ) : Set where
  step : ∀ {t'} → t ⟶ t' → Progress t
  done : Value t → Progress t

------------------------------------------------------------------------
-- Canonical forms lemmas

-- Canonical forms for functions
canonical-Fun : ∀ {τ σ} {t : ∅ ⊢ τ ⇒ σ}
  → Value t
  → ∃[ body ] (t ≡ ƛ body)
canonical-Fun V-ƛ = _ , refl

-- Canonical forms for booleans
canonical-Bool : ∀ {t : ∅ ⊢ `Bool}
  → Value t
  → (t ≡ `true) ⊎ (t ≡ `false)
canonical-Bool V-true  = inj₁ refl
canonical-Bool V-false = inj₂ refl

-- Canonical forms for naturals
canonical-Nat : ∀ {t : ∅ ⊢ `ℕ}
  → Value t
  → (t ≡ `zero) ⊎ (∃[ t' ] (t ≡ `suc t') × Value t')
canonical-Nat V-zero    = inj₁ refl
canonical-Nat (V-suc v) = inj₂ (_ , refl , v)

-- Canonical forms for unit
canonical-Unit : ∀ {t : ∅ ⊢ `⊤}
  → Value t
  → t ≡ `tt
canonical-Unit V-tt = refl

-- Canonical forms for products
canonical-Prod : ∀ {τ σ} {t : ∅ ⊢ τ `× σ}
  → Value t
  → ∃[ t₁ ] ∃[ t₂ ] (t ≡ `⟨ t₁ , t₂ ⟩) × Value t₁ × Value t₂
canonical-Prod (V-pair v₁ v₂) = _ , _ , refl , v₁ , v₂

-- Canonical forms for sums
canonical-Sum : ∀ {τ σ} {t : ∅ ⊢ τ `+ σ}
  → Value t
  → (∃[ v ] (t ≡ `inl v) × Value v) ⊎ (∃[ v ] (t ≡ `inr v) × Value v)
canonical-Sum (V-inl v) = inj₁ (_ , refl , v)
canonical-Sum (V-inr v) = inj₂ (_ , refl , v)

------------------------------------------------------------------------
-- Progress theorem

progress : ∀ {τ} (t : ∅ ⊢ τ) → Progress t
-- Variables: impossible in empty context
progress (` ())

-- Lambda abstraction: always a value
progress (ƛ t) = done V-ƛ

-- Application
progress (t₁ · t₂) with progress t₁
... | step s₁ = step (ξ-·₁ s₁)
... | done v₁ with progress t₂
...   | step s₂ = step (ξ-·₂ v₁ s₂)
...   | done v₂ with canonical-Fun v₁
...     | _ , refl = step (β-ƛ v₂)

-- Booleans
progress `true  = done V-true
progress `false = done V-false

-- If-then-else
progress (if t₁ then t₂ else t₃) with progress t₁
... | step s = step (ξ-if s)
... | done v with canonical-Bool v
...   | inj₁ refl = step β-if-true
...   | inj₂ refl = step β-if-false

-- Natural numbers
progress `zero    = done V-zero
progress (`suc t) with progress t
... | step s = step (ξ-suc s)
... | done v = done (V-suc v)

progress (`pred t) with progress t
... | step s = step (ξ-pred s)
... | done v with canonical-Nat v
...   | inj₁ refl = step β-pred-zero
...   | inj₂ (_ , refl , v') = step (β-pred-suc v')

progress (`iszero t) with progress t
... | step s = step (ξ-iszero s)
... | done v with canonical-Nat v
...   | inj₁ refl = step β-iszero-zero
...   | inj₂ (_ , refl , v') = step (β-iszero-suc v')

-- Unit
progress `tt = done V-tt

-- Pairs
progress `⟨ t₁ , t₂ ⟩ with progress t₁
... | step s₁ = step (ξ-pair₁ s₁)
... | done v₁ with progress t₂
...   | step s₂ = step (ξ-pair₂ v₁ s₂)
...   | done v₂ = done (V-pair v₁ v₂)

-- Projections
progress (`fst t) with progress t
... | step s = step (ξ-fst s)
... | done v with canonical-Prod v
...   | _ , _ , refl , v₁ , v₂ = step (β-fst v₁ v₂)

progress (`snd t) with progress t
... | step s = step (ξ-snd s)
... | done v with canonical-Prod v
...   | _ , _ , refl , v₁ , v₂ = step (β-snd v₁ v₂)

-- Sums
progress (`inl t) with progress t
... | step s = step (ξ-inl s)
... | done v = done (V-inl v)

progress (`inr t) with progress t
... | step s = step (ξ-inr s)
... | done v = done (V-inr v)

-- Case
progress (case t of l ∣ r) with progress t
... | step s = step (ξ-case s)
... | done v with canonical-Sum v
...   | inj₁ (_ , refl , v') = step (β-case-inl v')
...   | inj₂ (_ , refl , v') = step (β-case-inr v')

------------------------------------------------------------------------
-- Values cannot step

value-no-step : ∀ {Γ τ} {t t' : Γ ⊢ τ}
  → Value t
  → ¬ (t ⟶ t')
value-no-step V-ƛ ()
value-no-step V-true ()
value-no-step V-false ()
value-no-step V-zero ()
value-no-step (V-suc v) (ξ-suc s) = value-no-step v s
value-no-step V-tt ()
value-no-step (V-pair v₁ v₂) (ξ-pair₁ s) = value-no-step v₁ s
value-no-step (V-pair v₁ v₂) (ξ-pair₂ _ s) = value-no-step v₂ s
value-no-step (V-inl v) (ξ-inl s) = value-no-step v s
value-no-step (V-inr v) (ξ-inr s) = value-no-step v s
