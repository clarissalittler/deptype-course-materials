------------------------------------------------------------------------
-- Chapter 3: STLC with ADTs - Evaluation
--
-- This module defines the small-step operational semantics for the
-- simply-typed lambda calculus with products and sums.
------------------------------------------------------------------------

module Evaluation where

open import Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Values

data Value : ∀ {Γ τ} → Γ ⊢ τ → Set where
  -- Lambda abstractions are values
  V-ƛ     : ∀ {Γ τ σ} {t : Γ ▸ τ ⊢ σ}
          → Value (ƛ t)

  -- Booleans
  V-true  : ∀ {Γ} → Value (`true {Γ})
  V-false : ∀ {Γ} → Value (`false {Γ})

  -- Natural numbers
  V-zero  : ∀ {Γ} → Value (`zero {Γ})
  V-suc   : ∀ {Γ} {t : Γ ⊢ `ℕ}
          → Value t → Value (`suc t)

  -- Unit
  V-tt    : ∀ {Γ} → Value (`tt {Γ})

  -- Pairs (values when both components are values)
  V-pair  : ∀ {Γ τ σ} {t₁ : Γ ⊢ τ} {t₂ : Γ ⊢ σ}
          → Value t₁ → Value t₂ → Value `⟨ t₁ , t₂ ⟩

  -- Injections (values when argument is a value)
  V-inl   : ∀ {Γ τ σ} {t : Γ ⊢ τ}
          → Value t → Value (`inl {σ = σ} t)
  V-inr   : ∀ {Γ τ σ} {t : Γ ⊢ σ}
          → Value t → Value (`inr {τ = τ} t)

------------------------------------------------------------------------
-- Small-step reduction

infix 4 _⟶_

data _⟶_ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set where
  -- Beta reduction
  β-ƛ : ∀ {Γ τ σ} {t : Γ ▸ τ ⊢ σ} {v : Γ ⊢ τ}
      → Value v
      → (ƛ t) · v ⟶ t [ v ]

  -- Application congruence
  ξ-·₁ : ∀ {Γ τ σ} {t₁ t₁' : Γ ⊢ τ ⇒ σ} {t₂ : Γ ⊢ τ}
       → t₁ ⟶ t₁'
       → t₁ · t₂ ⟶ t₁' · t₂

  ξ-·₂ : ∀ {Γ τ σ} {t₁ : Γ ⊢ τ ⇒ σ} {t₂ t₂' : Γ ⊢ τ}
       → Value t₁
       → t₂ ⟶ t₂'
       → t₁ · t₂ ⟶ t₁ · t₂'

  -- If-then-else
  β-if-true  : ∀ {Γ τ} {t₂ t₃ : Γ ⊢ τ}
             → if `true then t₂ else t₃ ⟶ t₂

  β-if-false : ∀ {Γ τ} {t₂ t₃ : Γ ⊢ τ}
             → if `false then t₂ else t₃ ⟶ t₃

  ξ-if : ∀ {Γ τ} {t₁ t₁' : Γ ⊢ `Bool} {t₂ t₃ : Γ ⊢ τ}
       → t₁ ⟶ t₁'
       → if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃

  -- Successor congruence
  ξ-suc : ∀ {Γ} {t t' : Γ ⊢ `ℕ}
        → t ⟶ t'
        → `suc t ⟶ `suc t'

  -- Predecessor
  β-pred-zero : ∀ {Γ}
              → `pred (`zero {Γ}) ⟶ `zero

  β-pred-suc  : ∀ {Γ} {t : Γ ⊢ `ℕ}
              → Value t
              → `pred (`suc t) ⟶ t

  ξ-pred : ∀ {Γ} {t t' : Γ ⊢ `ℕ}
         → t ⟶ t'
         → `pred t ⟶ `pred t'

  -- IsZero
  β-iszero-zero : ∀ {Γ}
                → `iszero (`zero {Γ}) ⟶ `true

  β-iszero-suc  : ∀ {Γ} {t : Γ ⊢ `ℕ}
                → Value t
                → `iszero (`suc t) ⟶ `false

  ξ-iszero : ∀ {Γ} {t t' : Γ ⊢ `ℕ}
           → t ⟶ t'
           → `iszero t ⟶ `iszero t'

  -- Pair congruence (left-to-right evaluation)
  ξ-pair₁ : ∀ {Γ τ σ} {t₁ t₁' : Γ ⊢ τ} {t₂ : Γ ⊢ σ}
          → t₁ ⟶ t₁'
          → `⟨ t₁ , t₂ ⟩ ⟶ `⟨ t₁' , t₂ ⟩

  ξ-pair₂ : ∀ {Γ τ σ} {t₁ : Γ ⊢ τ} {t₂ t₂' : Γ ⊢ σ}
          → Value t₁
          → t₂ ⟶ t₂'
          → `⟨ t₁ , t₂ ⟩ ⟶ `⟨ t₁ , t₂' ⟩

  -- Projections
  β-fst : ∀ {Γ τ σ} {t₁ : Γ ⊢ τ} {t₂ : Γ ⊢ σ}
        → Value t₁ → Value t₂
        → `fst `⟨ t₁ , t₂ ⟩ ⟶ t₁

  β-snd : ∀ {Γ τ σ} {t₁ : Γ ⊢ τ} {t₂ : Γ ⊢ σ}
        → Value t₁ → Value t₂
        → `snd `⟨ t₁ , t₂ ⟩ ⟶ t₂

  ξ-fst : ∀ {Γ τ σ} {t t' : Γ ⊢ τ `× σ}
        → t ⟶ t'
        → `fst t ⟶ `fst t'

  ξ-snd : ∀ {Γ τ σ} {t t' : Γ ⊢ τ `× σ}
        → t ⟶ t'
        → `snd t ⟶ `snd t'

  -- Sum injection congruence
  ξ-inl : ∀ {Γ τ σ} {t t' : Γ ⊢ τ}
        → t ⟶ t'
        → `inl {σ = σ} t ⟶ `inl t'

  ξ-inr : ∀ {Γ τ σ} {t t' : Γ ⊢ σ}
        → t ⟶ t'
        → `inr {τ = τ} t ⟶ `inr t'

  -- Case reduction
  β-case-inl : ∀ {Γ τ σ ρ} {v : Γ ⊢ τ} {l : Γ ▸ τ ⊢ ρ} {r : Γ ▸ σ ⊢ ρ}
             → Value v
             → case (`inl v) of l ∣ r ⟶ l [ v ]

  β-case-inr : ∀ {Γ τ σ ρ} {v : Γ ⊢ σ} {l : Γ ▸ τ ⊢ ρ} {r : Γ ▸ σ ⊢ ρ}
             → Value v
             → case (`inr v) of l ∣ r ⟶ r [ v ]

  ξ-case : ∀ {Γ τ σ ρ} {t t' : Γ ⊢ τ `+ σ} {l : Γ ▸ τ ⊢ ρ} {r : Γ ▸ σ ⊢ ρ}
         → t ⟶ t'
         → case t of l ∣ r ⟶ case t' of l ∣ r

------------------------------------------------------------------------
-- Multi-step reduction (reflexive-transitive closure)

infix  2 _⟶*_
infixr 2 _⟶⟨_⟩_
infix  3 _∎

data _⟶*_ {Γ τ} : Γ ⊢ τ → Γ ⊢ τ → Set where
  _∎ : (t : Γ ⊢ τ) → t ⟶* t

  _⟶⟨_⟩_ : (t : Γ ⊢ τ) {t' t'' : Γ ⊢ τ}
         → t ⟶ t'
         → t' ⟶* t''
         → t ⟶* t''

------------------------------------------------------------------------
-- Example reductions

-- fst (1, 2) ⟶* 1
example-fst : `fst `⟨ `suc `zero , `suc (`suc `zero) ⟩ ⟶* `suc `zero
example-fst = `fst `⟨ `suc `zero , `suc (`suc `zero) ⟩
            ⟶⟨ β-fst (V-suc V-zero) (V-suc (V-suc V-zero)) ⟩
            (_∎ {∅} (`suc `zero))

-- snd (true, false) ⟶* false
example-snd : `snd `⟨ `true , `false ⟩ ⟶* `false
example-snd = `snd `⟨ `true , `false ⟩
            ⟶⟨ β-snd V-true V-false ⟩
            (_∎ {∅} `false)

-- case (inl 0) of x => succ x | y => y ⟶* 1
example-case-inl : case (`inl `zero) of (`suc (` Z)) ∣ (` Z) ⟶* `suc `zero
example-case-inl = case (`inl `zero) of (`suc (` Z)) ∣ (` Z)
                 ⟶⟨ β-case-inl V-zero ⟩
                 (_∎ {∅} (`suc `zero))

-- case (inr true) of x => 0 | y => if y then 1 else 2 ⟶* 1
example-case-inr : case (`inr {τ = `ℕ} `true) of `zero ∣ (if (` Z) then `suc `zero else `suc (`suc `zero))
                 ⟶* `suc `zero
example-case-inr = case (`inr {τ = `ℕ} `true) of `zero ∣ (if (` Z) then `suc `zero else `suc (`suc `zero))
                 ⟶⟨ β-case-inr V-true ⟩
                 (if `true then `suc `zero else `suc (`suc `zero))
                 ⟶⟨ β-if-true ⟩
                 (_∎ {∅} (`suc `zero))
