------------------------------------------------------------------------
-- Progress Theorem for Simply Typed Lambda Calculus
--
-- Progress: If ∅ ⊢ t : τ then either t is a value or t ⟶ t' for some t'
--
-- This is half of type safety. It guarantees that well-typed closed
-- terms never get "stuck" - they either have finished evaluating (value)
-- or can take another step.
------------------------------------------------------------------------

module Progress where

open import Syntax
open import Evaluation
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Progress Definition

-- | The progress property: a term either is a value or can step
data Progress {τ} (t : ∅ ⊢ τ) : Set where
  step : ∀ {t'}
    → t ⟶ t'
    → Progress t

  done :
      Value t
    → Progress t

------------------------------------------------------------------------
-- Canonical Forms Lemmas

-- | If ∅ ⊢ v : Bool and v is a value, then v is true or false
canonical-Bool : ∀ {v : ∅ ⊢ TyBool}
  → Value v
  → (v ≡ `true) ⊎ (v ≡ `false)
canonical-Bool V-true = inj₁ refl
canonical-Bool V-false = inj₂ refl

-- | If ∅ ⊢ v : τ₁ ⇒ τ₂ and v is a value, then v is a lambda
canonical-Fun : ∀ {τ₁ τ₂} {v : ∅ ⊢ (τ₁ ⇒ τ₂)}
  → Value v
  → ∃[ t ] (v ≡ ƛ t)
canonical-Fun V-ƛ = (_ , refl)

-- | If ∅ ⊢ v : Nat and v is a value, then v is zero or suc
canonical-Nat : ∀ {v : ∅ ⊢ TyNat}
  → Value v
  → (v ≡ `zero) ⊎ (∃[ v' ] (v ≡ `suc v' × Value v'))
canonical-Nat V-zero = inj₁ refl
canonical-Nat (V-suc val) = inj₂ (_ , (refl , val))

------------------------------------------------------------------------
-- Progress Theorem

-- | Progress: well-typed closed terms are either values or can step
progress : ∀ {τ} → (t : ∅ ⊢ τ) → Progress t

-- Variables: impossible in empty context
progress (` ())

-- Lambda: always a value
progress (ƛ t) = done V-ƛ

-- Application
progress (t₁ · t₂) with progress t₁
... | step t₁⟶t₁' = step (ξ-·₁ t₁⟶t₁')
... | done v₁ with progress t₂
...   | step t₂⟶t₂' = step (ξ-·₂ v₁ t₂⟶t₂')
...   | done v₂ with canonical-Fun v₁
...     | t , refl = step (β-ƛ v₂)

-- Boolean values
progress `true = done V-true
progress `false = done V-false

-- Conditional
progress (if t₁ then t₂ else t₃) with progress t₁
... | step t₁⟶t₁' = step (ξ-if t₁⟶t₁')
... | done v₁ with canonical-Bool v₁
...   | inj₁ refl = step β-if-true
...   | inj₂ refl = step β-if-false

-- Natural number values
progress `zero = done V-zero

-- Successor
progress (`suc t) with progress t
... | step t⟶t' = step (ξ-suc t⟶t')
... | done v = done (V-suc v)

-- Predecessor
progress (`pred t) with progress t
... | step t⟶t' = step (ξ-pred t⟶t')
... | done v with canonical-Nat v
...   | inj₁ refl = step β-pred-zero
...   | inj₂ (v' , refl , val) = step (β-pred-suc val)

-- Is-zero
progress (`iszero t) with progress t
... | step t⟶t' = step (ξ-iszero t⟶t')
... | done v with canonical-Nat v
...   | inj₁ refl = step β-iszero-zero
...   | inj₂ (v' , refl , val) = step (β-iszero-suc val)

------------------------------------------------------------------------
-- Corollaries

-- | Values cannot step (for any context)
value-no-step : ∀ {Γ τ} {t t' : Γ ⊢ τ}
  → Value t
  → ¬ (t ⟶ t')
value-no-step V-ƛ ()
value-no-step V-true ()
value-no-step V-false ()
value-no-step V-zero ()
value-no-step (V-suc v) (ξ-suc s) = value-no-step v s

-- | Values and steps are mutually exclusive (for closed terms)
value-or-step : ∀ {τ} {t : ∅ ⊢ τ}
  → Value t
  → (∀ {t'} → ¬ (t ⟶ t'))
value-or-step v {t'} s = value-no-step v s
