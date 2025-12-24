------------------------------------------------------------------------
-- Chapter 7: Dependent Types - Syntax
--
-- This module defines well-scoped terms for a dependent type theory
-- with Pi types, Sigma types, and Type : Type.
--
-- Unlike previous chapters, we use extrinsic typing because full
-- intrinsic typing for dependent types is extremely complex (it
-- essentially requires implementing a type checker in the types).
------------------------------------------------------------------------

module Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

------------------------------------------------------------------------
-- Terms (well-scoped with de Bruijn indices)
--
-- In dependent type theory, there is no distinction between terms
-- and types - everything is a Term.

data Term (n : ℕ) : Set where
  -- Universe (Type : Type for simplicity)
  `Type   : Term n

  -- Variables (de Bruijn indices)
  `_      : Fin n → Term n

  -- Lambda abstraction: λ(x:A). t
  ƛ       : Term n → Term (suc n) → Term n

  -- Application: t₁ t₂
  _·_     : Term n → Term n → Term n

  -- Pi type (dependent function): Π(x:A). B
  `Π      : Term n → Term (suc n) → Term n

  -- Sigma type (dependent pair): Σ(x:A). B
  `Σ      : Term n → Term (suc n) → Term n

  -- Pair introduction: (t₁, t₂)
  `⟨_,_⟩  : Term n → Term n → Term n

  -- Projections
  `fst    : Term n → Term n
  `snd    : Term n → Term n

  -- Natural numbers
  `ℕ      : Term n
  `zero   : Term n
  `suc    : Term n → Term n

  -- Booleans
  `Bool   : Term n
  `true   : Term n
  `false  : Term n
  `if     : Term n → Term n → Term n → Term n

infixl 7 _·_
infix 6 `_

------------------------------------------------------------------------
-- Renaming

Rename : ℕ → ℕ → Set
Rename m n = Fin m → Fin n

-- Extend a renaming under a binder
ext : ∀ {m n} → Rename m n → Rename (suc m) (suc n)
ext ρ zero    = zero
ext ρ (suc i) = suc (ρ i)

-- Apply renaming to a term
rename : ∀ {m n} → Rename m n → Term m → Term n
rename ρ `Type        = `Type
rename ρ (` i)        = ` ρ i
rename ρ (ƛ A t)      = ƛ (rename ρ A) (rename (ext ρ) t)
rename ρ (t₁ · t₂)    = rename ρ t₁ · rename ρ t₂
rename ρ (`Π A B)     = `Π (rename ρ A) (rename (ext ρ) B)
rename ρ (`Σ A B)     = `Σ (rename ρ A) (rename (ext ρ) B)
rename ρ `⟨ t₁ , t₂ ⟩ = `⟨ rename ρ t₁ , rename ρ t₂ ⟩
rename ρ (`fst t)     = `fst (rename ρ t)
rename ρ (`snd t)     = `snd (rename ρ t)
rename ρ `ℕ           = `ℕ
rename ρ `zero        = `zero
rename ρ (`suc t)     = `suc (rename ρ t)
rename ρ `Bool        = `Bool
rename ρ `true        = `true
rename ρ `false       = `false
rename ρ (`if t₁ t₂ t₃) = `if (rename ρ t₁) (rename ρ t₂) (rename ρ t₃)

-- Weakening (add a free variable)
weaken : ∀ {n} → Term n → Term (suc n)
weaken = rename suc

------------------------------------------------------------------------
-- Substitution

Subst : ℕ → ℕ → Set
Subst m n = Fin m → Term n

-- Extend a substitution under a binder
exts : ∀ {m n} → Subst m n → Subst (suc m) (suc n)
exts σ zero    = ` zero
exts σ (suc i) = weaken (σ i)

-- Apply substitution to a term
subst : ∀ {m n} → Subst m n → Term m → Term n
subst σ `Type        = `Type
subst σ (` i)        = σ i
subst σ (ƛ A t)      = ƛ (subst σ A) (subst (exts σ) t)
subst σ (t₁ · t₂)    = subst σ t₁ · subst σ t₂
subst σ (`Π A B)     = `Π (subst σ A) (subst (exts σ) B)
subst σ (`Σ A B)     = `Σ (subst σ A) (subst (exts σ) B)
subst σ `⟨ t₁ , t₂ ⟩ = `⟨ subst σ t₁ , subst σ t₂ ⟩
subst σ (`fst t)     = `fst (subst σ t)
subst σ (`snd t)     = `snd (subst σ t)
subst σ `ℕ           = `ℕ
subst σ `zero        = `zero
subst σ (`suc t)     = `suc (subst σ t)
subst σ `Bool        = `Bool
subst σ `true        = `true
subst σ `false       = `false
subst σ (`if t₁ t₂ t₃) = `if (subst σ t₁) (subst σ t₂) (subst σ t₃)

-- Single substitution: t [ s ] substitutes s for variable 0
_[_] : ∀ {n} → Term (suc n) → Term n → Term n
t [ s ] = subst σ t
  where
    σ : Subst (suc _) _
    σ zero    = s
    σ (suc i) = ` i

------------------------------------------------------------------------
-- Examples

-- The identity function on natural numbers: λ(x:ℕ). x
id-nat : Term 0
id-nat = ƛ `ℕ (` zero)

-- The identity function type: Π(x:ℕ). ℕ  (which is just ℕ → ℕ)
id-nat-type : Term 0
id-nat-type = `Π `ℕ `ℕ

-- Polymorphic identity: λ(A:Type). λ(x:A). x
poly-id : Term 0
poly-id = ƛ `Type (ƛ (` zero) (` zero))

-- Polymorphic identity type: Π(A:Type). Π(x:A). A
poly-id-type : Term 0
poly-id-type = `Π `Type (`Π (` zero) (` (suc zero)))

-- A dependent pair type: Σ(x:ℕ). if x == 0 then Bool else ℕ
-- (simplified: just Σ(x:ℕ). ℕ)
dep-pair-type : Term 0
dep-pair-type = `Σ `ℕ `ℕ

-- A dependent pair: (0, 0)
dep-pair : Term 0
dep-pair = `⟨ `zero , `zero ⟩
