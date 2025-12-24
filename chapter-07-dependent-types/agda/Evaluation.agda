------------------------------------------------------------------------
-- Chapter 7: Dependent Types - Evaluation
--
-- This module defines the small-step operational semantics and
-- normalization for the dependent type theory.
------------------------------------------------------------------------

module Evaluation where

open import Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Values

data Value {n : ℕ} : Term n → Set where
  V-Type  : Value `Type
  V-ƛ     : ∀ {A t} → Value (ƛ A t)
  V-Π     : ∀ {A B} → Value (`Π A B)
  V-Σ     : ∀ {A B} → Value (`Σ A B)
  V-pair  : ∀ {t₁ t₂} → Value t₁ → Value t₂ → Value `⟨ t₁ , t₂ ⟩
  V-ℕ     : Value `ℕ
  V-zero  : Value `zero
  V-suc   : ∀ {t} → Value t → Value (`suc t)
  V-Bool  : Value `Bool
  V-true  : Value `true
  V-false : Value `false

------------------------------------------------------------------------
-- Small-step reduction

infix 4 _⟶_

data _⟶_ {n : ℕ} : Term n → Term n → Set where
  -- Beta reduction for functions
  β-ƛ : ∀ {A t v}
      → Value v
      → (ƛ A t) · v ⟶ t [ v ]

  -- Application congruence
  ξ-·₁ : ∀ {t₁ t₁' t₂}
       → t₁ ⟶ t₁'
       → t₁ · t₂ ⟶ t₁' · t₂

  ξ-·₂ : ∀ {t₁ t₂ t₂'}
       → Value t₁
       → t₂ ⟶ t₂'
       → t₁ · t₂ ⟶ t₁ · t₂'

  -- Projections
  β-fst : ∀ {t₁ t₂}
        → Value t₁ → Value t₂
        → `fst `⟨ t₁ , t₂ ⟩ ⟶ t₁

  β-snd : ∀ {t₁ t₂}
        → Value t₁ → Value t₂
        → `snd `⟨ t₁ , t₂ ⟩ ⟶ t₂

  ξ-fst : ∀ {t t'}
        → t ⟶ t'
        → `fst t ⟶ `fst t'

  ξ-snd : ∀ {t t'}
        → t ⟶ t'
        → `snd t ⟶ `snd t'

  -- Pair congruence
  ξ-pair₁ : ∀ {t₁ t₁' t₂}
          → t₁ ⟶ t₁'
          → `⟨ t₁ , t₂ ⟩ ⟶ `⟨ t₁' , t₂ ⟩

  ξ-pair₂ : ∀ {t₁ t₂ t₂'}
          → Value t₁
          → t₂ ⟶ t₂'
          → `⟨ t₁ , t₂ ⟩ ⟶ `⟨ t₁ , t₂' ⟩

  -- Successor congruence
  ξ-suc : ∀ {t t'}
        → t ⟶ t'
        → `suc t ⟶ `suc t'

  -- If-then-else
  β-if-true : ∀ {t₂ t₃}
            → `if `true t₂ t₃ ⟶ t₂

  β-if-false : ∀ {t₂ t₃}
             → `if `false t₂ t₃ ⟶ t₃

  ξ-if : ∀ {t₁ t₁' t₂ t₃}
       → t₁ ⟶ t₁'
       → `if t₁ t₂ t₃ ⟶ `if t₁' t₂ t₃

------------------------------------------------------------------------
-- Multi-step reduction

infix  2 _⟶*_
infixr 2 _⟶⟨_⟩_
infix  3 _∎

data _⟶*_ {n : ℕ} : Term n → Term n → Set where
  _∎ : (t : Term n) → t ⟶* t

  _⟶⟨_⟩_ : (t : Term n) {t' t'' : Term n}
         → t ⟶ t'
         → t' ⟶* t''
         → t ⟶* t''

------------------------------------------------------------------------
-- Example reductions

-- fst (0, 1) ⟶* 0
example-fst : `fst `⟨ `zero , `suc `zero ⟩ ⟶* `zero
example-fst = `fst `⟨ `zero , `suc `zero ⟩
            ⟶⟨ β-fst V-zero (V-suc V-zero) ⟩
            (_∎ {0} `zero)

-- snd (true, false) ⟶* false
example-snd : `snd `⟨ `true , `false ⟩ ⟶* `false
example-snd = `snd `⟨ `true , `false ⟩
            ⟶⟨ β-snd V-true V-false ⟩
            (_∎ {0} `false)

-- (λ(x:ℕ). x) 0 ⟶* 0
example-app : (ƛ `ℕ (` zero)) · `zero ⟶* `zero
example-app = (ƛ `ℕ (` zero)) · `zero
            ⟶⟨ β-ƛ V-zero ⟩
            (_∎ {0} `zero)

-- if true then 1 else 0 ⟶* 1
example-if : `if `true (`suc `zero) `zero ⟶* `suc `zero
example-if = `if `true (`suc `zero) `zero
           ⟶⟨ β-if-true ⟩
           (_∎ {0} (`suc `zero))

------------------------------------------------------------------------
-- Normalization

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

-- A term is in normal form if no reduction applies
data Normal {n : ℕ} : Term n → Set where
  normal : ∀ {t} → (∀ {t'} → ¬ (t ⟶ t')) → Normal t

-- Values cannot step
value-no-step : ∀ {n} {t t' : Term n} → Value t → t ⟶ t' → ⊥
value-no-step V-Type ()
value-no-step V-ƛ ()
value-no-step V-Π ()
value-no-step V-Σ ()
value-no-step (V-pair v₁ v₂) (ξ-pair₁ s) = value-no-step v₁ s
value-no-step (V-pair v₁ v₂) (ξ-pair₂ _ s) = value-no-step v₂ s
value-no-step V-ℕ ()
value-no-step V-zero ()
value-no-step (V-suc v) (ξ-suc s) = value-no-step v s
value-no-step V-Bool ()
value-no-step V-true ()
value-no-step V-false ()

-- Values are in normal form
value-normal : ∀ {n} {t : Term n} → Value t → Normal t
value-normal v = normal (value-no-step v)
