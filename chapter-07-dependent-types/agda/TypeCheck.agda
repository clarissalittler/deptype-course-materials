------------------------------------------------------------------------
-- Chapter 7: Dependent Types - Type Checking
--
-- This module defines the typing judgment for dependent type theory.
-- We use Type : Type for simplicity (ignoring universe levels).
------------------------------------------------------------------------

module TypeCheck where

open import Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Contexts are lists of types

Context : ℕ → Set
Context n = Vec (Term n) n

-- Note: This is a simplification. In a full implementation, we would
-- need contexts where each type can depend on earlier variables.
-- Here we use a simpler representation for clarity.

------------------------------------------------------------------------
-- Typing judgment: Γ ⊢ t : A
--
-- Read as: "In context Γ, term t has type A"

data _⊢_∶_ {n : ℕ} (Γ : Context n) : Term n → Term n → Set where

  -- Variables
  T-Var : ∀ {i : Fin n}
        → Γ ⊢ ` i ∶ lookup Γ i

  -- Universe (Type : Type - inconsistent but simple)
  T-Type : Γ ⊢ `Type ∶ `Type

  -- Pi formation: if A : Type and B : Type (under x:A), then Π(x:A).B : Type
  T-Pi : ∀ {A B}
       → Γ ⊢ A ∶ `Type
       → (Γ' : Context (suc n))  -- Γ extended with A
       → Γ' ⊢ B ∶ `Type
       → Γ ⊢ `Π A B ∶ `Type

  -- Lambda: if t : B under x:A, then λ(x:A).t : Π(x:A).B
  T-Lam : ∀ {A B t}
        → Γ ⊢ A ∶ `Type
        → (Γ' : Context (suc n))
        → Γ' ⊢ t ∶ B
        → Γ ⊢ ƛ A t ∶ `Π A B

  -- Application: if f : Π(x:A).B and a : A, then f a : B[a/x]
  T-App : ∀ {A B f a}
        → Γ ⊢ f ∶ `Π A B
        → Γ ⊢ a ∶ A
        → Γ ⊢ f · a ∶ (B [ a ])

  -- Sigma formation
  T-Sigma : ∀ {A B}
          → Γ ⊢ A ∶ `Type
          → (Γ' : Context (suc n))
          → Γ' ⊢ B ∶ `Type
          → Γ ⊢ `Σ A B ∶ `Type

  -- Pair: if a : A and b : B[a/x], then (a,b) : Σ(x:A).B
  T-Pair : ∀ {A B a b}
         → Γ ⊢ a ∶ A
         → Γ ⊢ b ∶ (B [ a ])
         → Γ ⊢ `⟨ a , b ⟩ ∶ `Σ A B

  -- First projection
  T-Fst : ∀ {A B p}
        → Γ ⊢ p ∶ `Σ A B
        → Γ ⊢ `fst p ∶ A

  -- Second projection (type depends on first component)
  T-Snd : ∀ {A B p}
        → Γ ⊢ p ∶ `Σ A B
        → Γ ⊢ `snd p ∶ (B [ `fst p ])

  -- Natural numbers
  T-Nat : Γ ⊢ `ℕ ∶ `Type

  T-Zero : Γ ⊢ `zero ∶ `ℕ

  T-Suc : ∀ {n}
        → Γ ⊢ n ∶ `ℕ
        → Γ ⊢ `suc n ∶ `ℕ

  -- Booleans
  T-Bool : Γ ⊢ `Bool ∶ `Type

  T-True : Γ ⊢ `true ∶ `Bool

  T-False : Γ ⊢ `false ∶ `Bool

  T-If : ∀ {A c t f}
       → Γ ⊢ c ∶ `Bool
       → Γ ⊢ t ∶ A
       → Γ ⊢ f ∶ A
       → Γ ⊢ `if c t f ∶ A

infix 4 _⊢_∶_

------------------------------------------------------------------------
-- Example typing derivations

-- The identity function ℕ → ℕ is well-typed
-- λ(x:ℕ). x : Π(x:ℕ). ℕ
-- Note: This requires proper context handling which is simplified here.
