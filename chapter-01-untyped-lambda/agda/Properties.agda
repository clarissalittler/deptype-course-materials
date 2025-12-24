------------------------------------------------------------------------
-- Properties of Untyped Lambda Calculus
--
-- This module proves key properties:
-- - Determinism of small-step semantics
-- - Values don't reduce
-- - Progress is NOT provable (untyped calculus can get stuck)
------------------------------------------------------------------------

module Properties where

open import Syntax
open import Evaluation
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

------------------------------------------------------------------------
-- Determinism

-- | Helper: values don't step
value-doesnt-step : ∀ {t t'} → Value t → ¬ (t ⟶ t')
value-doesnt-step V-Lam ()

-- | Determinism: if t ⟶ t₁ and t ⟶ t₂, then t₁ ≡ t₂
-- Call-by-value semantics is deterministic
determinism : ∀ {t t₁ t₂}
  → t ⟶ t₁
  → t ⟶ t₂
  → t₁ ≡ t₂
determinism (E-AppAbs v₁) (E-AppAbs v₂) = refl
determinism (E-AppAbs v₁) (E-App1 step) = ⊥-elim (value-doesnt-step V-Lam step)
determinism (E-AppAbs v₁) (E-App2 v₂ step) = ⊥-elim (value-doesnt-step v₁ step)
determinism (E-App1 step) (E-AppAbs v) = ⊥-elim (value-doesnt-step V-Lam step)
determinism (E-App1 step₁) (E-App1 step₂) = cong (λ t → app t _) (determinism step₁ step₂)
determinism (E-App1 step₁) (E-App2 v step₂) = ⊥-elim (value-doesnt-step v step₁)
determinism (E-App2 v step₁) (E-AppAbs v') = ⊥-elim (value-doesnt-step v' step₁)
determinism (E-App2 v₁ step₁) (E-App1 step₂) = ⊥-elim (value-doesnt-step v₁ step₂)
determinism (E-App2 v₁ step₁) (E-App2 v₂ step₂) = cong (app _) (determinism step₁ step₂)

------------------------------------------------------------------------
-- No Progress (Untyped Lambda Calculus can get stuck)

-- | A counterexample: (var 0) is stuck
-- This demonstrates that untyped lambda calculus lacks progress
stuck-example : ∀ {t} → ¬ (var 0 ⟶ t)
stuck-example ()

-- | Another counterexample: (var 0) (λ. 0) is stuck
-- A free variable applied to anything cannot reduce
stuck-app-example : ∀ {t} → ¬ (app (var 0) (lam (var 0)) ⟶ t)
stuck-app-example (E-App1 ())
stuck-app-example (E-App2 () _)

------------------------------------------------------------------------
-- Properties of substitution

-- | Substitution preserves value-hood in the body
-- If v is a value, then v remains unchanged by substitution
-- (since values are closed lambda terms in our system)

------------------------------------------------------------------------
-- Confluence (Church-Rosser) - Statement

-- | Diamond property (stated but not proven - complex proof)
-- If t ⟶* t₁ and t ⟶* t₂, then there exists t₃ such that
-- t₁ ⟶* t₃ and t₂ ⟶* t₃
--
-- This is the Church-Rosser theorem, which holds for untyped lambda calculus
-- but requires parallel reduction techniques to prove

diamond-statement : Set
diamond-statement = ∀ {t t₁ t₂}
  → t ⟶* t₁
  → t ⟶* t₂
  → ∃[ t₃ ] (t₁ ⟶* t₃ × t₂ ⟶* t₃)

-- Note: The full proof of Church-Rosser is non-trivial and typically
-- requires the parallel reduction technique introduced by Tait and Martin-Löf.

------------------------------------------------------------------------
-- Properties of multi-step reduction

-- | If t₁ ⟶* t₂ and t₂ is a value, then t₂ is the unique value reachable from t₁
unique-value : ∀ {t v₁ v₂}
  → t ⟶* v₁
  → Value v₁
  → t ⟶* v₂
  → Value v₂
  → v₁ ≡ v₂
unique-value refl* V-Lam refl* V-Lam = refl
unique-value refl* V-Lam (step* step _) val₂ = ⊥-elim (value-doesnt-step V-Lam step)
unique-value (step* step _) val₁ refl* V-Lam = ⊥-elim (value-doesnt-step V-Lam step)
unique-value (step* step₁ red₁) val₁ (step* step₂ red₂) val₂
  with determinism step₁ step₂
... | refl = unique-value red₁ val₁ red₂ val₂

------------------------------------------------------------------------
-- Normalization does NOT hold for untyped lambda calculus

-- | Omega diverges: Ω = (λx. x x)(λx. x x)
-- omega ⟶ omega, so evaluation loops forever

omega-reduces-to-omega : omega ⟶ omega
omega-reduces-to-omega = E-AppAbs V-Lam

-- | Thus omega never reaches a value (non-terminating)
omega-diverges : ∀ {v} → Value v → ¬ (omega ⟶* v)
omega-diverges val refl* = value-doesnt-step val omega-reduces-to-omega
omega-diverges val (step* step red) with determinism step omega-reduces-to-omega
... | refl = omega-diverges val red
