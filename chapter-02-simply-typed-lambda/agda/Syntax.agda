------------------------------------------------------------------------
-- Syntax for Simply Typed Lambda Calculus (STLC)
--
-- This module defines:
-- - Types (Bool, Nat, function types)
-- - Intrinsically-typed terms (well-typed by construction)
-- - Typing contexts
------------------------------------------------------------------------

module Syntax where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Types

-- | Types in STLC
data Type : Set where
  TyBool : Type              -- Boolean type
  TyNat  : Type              -- Natural number type
  _⇒_    : Type → Type → Type  -- Function type: τ₁ → τ₂

infixr 7 _⇒_

-- | Decidable equality for types
_≟Ty_ : (τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
TyBool ≟Ty TyBool = yes refl
TyBool ≟Ty TyNat = no (λ ())
TyBool ≟Ty (_ ⇒ _) = no (λ ())
TyNat ≟Ty TyBool = no (λ ())
TyNat ≟Ty TyNat = yes refl
TyNat ≟Ty (_ ⇒ _) = no (λ ())
(τ₁ ⇒ τ₂) ≟Ty TyBool = no (λ ())
(τ₁ ⇒ τ₂) ≟Ty TyNat = no (λ ())
(τ₁ ⇒ τ₂) ≟Ty (τ₃ ⇒ τ₄) with τ₁ ≟Ty τ₃ | τ₂ ≟Ty τ₄
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p = no (λ { refl → ¬p refl })
... | no ¬p | _ = no (λ { refl → ¬p refl })

------------------------------------------------------------------------
-- Typing Contexts (as snoc-lists)

-- | Typing context: a list of types (using de Bruijn indices)
data Context : Set where
  ∅   : Context                    -- Empty context
  _▸_ : Context → Type → Context   -- Extend context with a type

infixl 5 _▸_

------------------------------------------------------------------------
-- Context Membership (de Bruijn indices as proofs)

-- | Proof that a type is in a context at a given position
-- This is essentially a de Bruijn index with a type annotation
data _∋_ : Context → Type → Set where
  Z : ∀ {Γ τ}
    → (Γ ▸ τ) ∋ τ                  -- Most recent binding

  S : ∀ {Γ τ σ}
    → Γ ∋ τ
    → (Γ ▸ σ) ∋ τ                  -- Skip past a binding

infix 4 _∋_

------------------------------------------------------------------------
-- Intrinsically-Typed Terms

-- | Well-typed terms: Γ ⊢ t : τ
-- Terms are indexed by their context and type
data _⊢_ : Context → Type → Set where

  -- Variables (T-Var)
  `_ : ∀ {Γ τ}
    → Γ ∋ τ
    → Γ ⊢ τ

  -- Lambda abstraction (T-Abs)
  ƛ_ : ∀ {Γ τ₁ τ₂}
    → (Γ ▸ τ₁) ⊢ τ₂
    → Γ ⊢ (τ₁ ⇒ τ₂)

  -- Application (T-App)
  _·_ : ∀ {Γ τ₁ τ₂}
    → Γ ⊢ (τ₁ ⇒ τ₂)
    → Γ ⊢ τ₁
    → Γ ⊢ τ₂

  -- Booleans
  `true : ∀ {Γ} → Γ ⊢ TyBool
  `false : ∀ {Γ} → Γ ⊢ TyBool

  -- Conditional (T-If)
  if_then_else_ : ∀ {Γ τ}
    → Γ ⊢ TyBool
    → Γ ⊢ τ
    → Γ ⊢ τ
    → Γ ⊢ τ

  -- Natural numbers
  `zero : ∀ {Γ} → Γ ⊢ TyNat

  `suc : ∀ {Γ}
    → Γ ⊢ TyNat
    → Γ ⊢ TyNat

  `pred : ∀ {Γ}
    → Γ ⊢ TyNat
    → Γ ⊢ TyNat

  `iszero : ∀ {Γ}
    → Γ ⊢ TyNat
    → Γ ⊢ TyBool

infix 5 ƛ_
infixl 7 _·_
infix 9 `_

------------------------------------------------------------------------
-- Closed Terms

-- | A closed term of type τ
ClosedTerm : Type → Set
ClosedTerm τ = ∅ ⊢ τ

------------------------------------------------------------------------
-- Example Terms

-- | Identity function: λx:Bool. x
idBool : ClosedTerm (TyBool ⇒ TyBool)
idBool = ƛ (` Z)

-- | Constant function: λx:Bool. λy:Nat. x
constBoolNat : ClosedTerm (TyBool ⇒ TyNat ⇒ TyBool)
constBoolNat = ƛ ƛ (` S Z)

-- | Successor applied to zero
one : ClosedTerm TyNat
one = `suc `zero

-- | Double function: λn:Nat. (n + n) would need recursion,
-- but we can show: λb:Bool. if b then 1 else 0
toNat : ClosedTerm (TyBool ⇒ TyNat)
toNat = ƛ if (` Z) then (`suc `zero) else `zero

------------------------------------------------------------------------
-- Renaming and Substitution

-- | Extension of a renaming past a bound variable
ext : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ∋ τ)
  → (∀ {τ σ} → (Γ ▸ σ) ∋ τ → (Δ ▸ σ) ∋ τ)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

-- | Renaming (change of context)
rename : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ∋ τ)
  → (∀ {τ} → Γ ⊢ τ → Δ ⊢ τ)
rename ρ (` x) = ` ρ x
rename ρ (ƛ t) = ƛ rename (ext ρ) t
rename ρ (t₁ · t₂) = rename ρ t₁ · rename ρ t₂
rename ρ `true = `true
rename ρ `false = `false
rename ρ (if t₁ then t₂ else t₃) = if rename ρ t₁ then rename ρ t₂ else rename ρ t₃
rename ρ `zero = `zero
rename ρ (`suc t) = `suc (rename ρ t)
rename ρ (`pred t) = `pred (rename ρ t)
rename ρ (`iszero t) = `iszero (rename ρ t)

-- | Extension of a substitution past a bound variable
exts : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ⊢ τ)
  → (∀ {τ σ} → (Γ ▸ σ) ∋ τ → (Δ ▸ σ) ⊢ τ)
exts σ Z = ` Z
exts σ (S x) = rename S (σ x)

-- | Substitution
subst : ∀ {Γ Δ}
  → (∀ {τ} → Γ ∋ τ → Δ ⊢ τ)
  → (∀ {τ} → Γ ⊢ τ → Δ ⊢ τ)
subst σ (` x) = σ x
subst σ (ƛ t) = ƛ subst (exts σ) t
subst σ (t₁ · t₂) = subst σ t₁ · subst σ t₂
subst σ `true = `true
subst σ `false = `false
subst σ (if t₁ then t₂ else t₃) = if subst σ t₁ then subst σ t₂ else subst σ t₃
subst σ `zero = `zero
subst σ (`suc t) = `suc (subst σ t)
subst σ (`pred t) = `pred (subst σ t)
subst σ (`iszero t) = `iszero (subst σ t)

-- | Single substitution: [N/x]M
_[_] : ∀ {Γ τ σ}
  → (Γ ▸ σ) ⊢ τ
  → Γ ⊢ σ
  → Γ ⊢ τ
_[_] {Γ} {τ} {σ} M N = subst σ-sub M
  where
  σ-sub : ∀ {τ'} → (Γ ▸ σ) ∋ τ' → Γ ⊢ τ'
  σ-sub Z = N
  σ-sub (S x) = ` x
