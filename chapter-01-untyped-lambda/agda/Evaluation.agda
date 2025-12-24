------------------------------------------------------------------------
-- Evaluation Semantics for Untyped Lambda Calculus
--
-- This module defines:
-- - Values (canonical forms)
-- - Small-step operational semantics
-- - Multi-step reduction
-- - Normal forms
------------------------------------------------------------------------

module Evaluation where

open import Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

------------------------------------------------------------------------
-- Values

-- | A term is a value if it's a lambda abstraction
-- Values are the "final results" of evaluation
data Value : Term → Set where
  V-Lam : ∀ {t} → Value (lam t)

-- | Values are terms
value-term : ∀ {t} → Value t → Term
value-term {t} _ = t

-- | Decision procedure for values
value? : (t : Term) → Dec (Value t)
value? (var x) = no (λ ())
value? (lam t) = yes V-Lam
value? (app t₁ t₂) = no (λ ())

------------------------------------------------------------------------
-- Small-step operational semantics (call-by-value)

-- | Single-step reduction relation: t ⟶ t'
-- Call-by-value semantics: arguments must be values before beta reduction
data _⟶_ : Term → Term → Set where
  -- Beta reduction: (λ. t) v ⟶ [0 ↦ v]t
  E-AppAbs : ∀ {t v}
    → Value v
    → app (lam t) v ⟶ substTop v t

  -- Reduce the function position
  E-App1 : ∀ {t₁ t₁' t₂}
    → t₁ ⟶ t₁'
    → app t₁ t₂ ⟶ app t₁' t₂

  -- Reduce the argument position (function must be a value)
  E-App2 : ∀ {v t₂ t₂'}
    → Value v
    → t₂ ⟶ t₂'
    → app v t₂ ⟶ app v t₂'

------------------------------------------------------------------------
-- Multi-step reduction (reflexive-transitive closure)

-- | Multi-step reduction: t ⟶* t'
data _⟶*_ : Term → Term → Set where
  -- Reflexivity: t ⟶* t
  refl* : ∀ {t} → t ⟶* t

  -- Transitivity: if t₁ ⟶ t₂ and t₂ ⟶* t₃ then t₁ ⟶* t₃
  step* : ∀ {t₁ t₂ t₃}
    → t₁ ⟶ t₂
    → t₂ ⟶* t₃
    → t₁ ⟶* t₃

-- | Single step is multi-step
single-step : ∀ {t t'} → t ⟶ t' → t ⟶* t'
single-step step = step* step refl*

-- | Transitivity of multi-step reduction
trans* : ∀ {t₁ t₂ t₃} → t₁ ⟶* t₂ → t₂ ⟶* t₃ → t₁ ⟶* t₃
trans* refl* r₂ = r₂
trans* (step* s r₁) r₂ = step* s (trans* r₁ r₂)

-- | Multi-step reduction is preserved under application (left)
app1-multi : ∀ {t₁ t₁' t₂} → t₁ ⟶* t₁' → app t₁ t₂ ⟶* app t₁' t₂
app1-multi refl* = refl*
app1-multi (step* s r) = step* (E-App1 s) (app1-multi r)

-- | Multi-step reduction is preserved under application (right) when left is value
app2-multi : ∀ {v t₂ t₂'} → Value v → t₂ ⟶* t₂' → app v t₂ ⟶* app v t₂'
app2-multi v refl* = refl*
app2-multi v (step* s r) = step* (E-App2 v s) (app2-multi v r)

------------------------------------------------------------------------
-- Normal forms

-- | A term is in normal form if it cannot step
NormalForm : Term → Set
NormalForm t = ∀ {t'} → ¬ (t ⟶ t')

-- | Values are in normal form
value-normal : ∀ {t} → Value t → NormalForm t
value-normal V-Lam ()

-- | Stuck terms: normal forms that are not values
Stuck : Term → Set
Stuck t = NormalForm t × ¬ Value t

-- | Example: a free variable is stuck
var-stuck : ∀ {x} → Stuck (var x)
var-stuck = (λ ()) , (λ ())

------------------------------------------------------------------------
-- Evaluation function (fuel-based)

-- | Evaluate a term with a fuel limit
-- Returns nothing if out of fuel, otherwise the resulting term
eval : ℕ → Term → Term
eval zero t = t
eval (suc fuel) t with value? t
... | yes _ = t
... | no  _ with step t
  where
    step : Term → Term ⊎ Term  -- Left = stepped, Right = stuck
    step (var x) = inj₂ (var x)
    step (lam t) = inj₂ (lam t)
    step (app t₁ t₂) with value? t₁ | value? t₂
    step (app (lam t) t₂) | yes V-Lam | yes v = inj₁ (substTop t₂ t)
    step (app (lam t) t₂) | yes V-Lam | no  _ with step t₂
    ... | inj₁ t₂' = inj₁ (app (lam t) t₂')
    ... | inj₂ _ = inj₂ (app (lam t) t₂)
    step (app t₁ t₂) | yes v | _ = inj₂ (app t₁ t₂)  -- Value but not lambda
    step (app t₁ t₂) | no  _ | _ with step t₁
    ... | inj₁ t₁' = inj₁ (app t₁' t₂)
    ... | inj₂ _ = inj₂ (app t₁ t₂)
... | inj₁ t' = eval fuel t'
... | inj₂ t' = t'

------------------------------------------------------------------------
-- Example evaluations

-- | (λ. 0) (λ. 0) ⟶* λ. 0
example-id-id : app idTerm idTerm ⟶* idTerm
example-id-id = step* (E-AppAbs V-Lam) refl*

-- | Church numeral 1: λf. λx. f x
churchOne : Term
churchOne = lam (lam (app (var 1) (var 0)))

-- | Church numeral 2: λf. λx. f (f x)
churchTwo : Term
churchTwo = lam (lam (app (var 1) (app (var 1) (var 0))))
