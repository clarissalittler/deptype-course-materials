------------------------------------------------------------------------
-- Chapter 5: System F - Syntax
--
-- This module defines intrinsically-typed terms for System F
-- (polymorphic lambda calculus) using de Bruijn indices.
------------------------------------------------------------------------

module Syntax where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Kinds (for type variables)
-- In System F, all types have kind *, so we don't need explicit kinds.
-- We just track the number of type variables in scope.

TyContext : Set
TyContext = ℕ  -- Number of type variables in scope

------------------------------------------------------------------------
-- Types (indexed by the number of type variables in scope)

open import Data.Nat using (_<_; s≤s; z≤n)

-- 0 < suc n for any n
z<s : ∀ {n} → zero < suc n
z<s = s≤s z≤n

data Type (Δ : TyContext) : Set where
  `ℕ      : Type Δ                           -- Natural numbers
  `Bool   : Type Δ                           -- Booleans
  _⇒_     : Type Δ → Type Δ → Type Δ         -- Function type
  TyVar   : ∀ {n} → n < Δ → Type Δ           -- Type variable (de Bruijn)
  `∀      : Type (suc Δ) → Type Δ            -- Universal type ∀α.τ

infixr 7 _⇒_

------------------------------------------------------------------------
-- Type variable weakening (adding a type variable to the context)

mutual
  weaken-ty : ∀ {Δ} → Type Δ → Type (suc Δ)
  weaken-ty `ℕ = `ℕ
  weaken-ty `Bool = `Bool
  weaken-ty (τ₁ ⇒ τ₂) = weaken-ty τ₁ ⇒ weaken-ty τ₂
  weaken-ty (TyVar {n} p) = TyVar (s≤s p)
  weaken-ty (`∀ τ) = `∀ (weaken-ty-under τ)

  -- Weaken under a binder
  weaken-ty-under : ∀ {Δ} → Type (suc Δ) → Type (suc (suc Δ))
  weaken-ty-under `ℕ = `ℕ
  weaken-ty-under `Bool = `Bool
  weaken-ty-under (τ₁ ⇒ τ₂) = weaken-ty-under τ₁ ⇒ weaken-ty-under τ₂
  weaken-ty-under (TyVar {n} p) = TyVar (s≤s p)
  weaken-ty-under (`∀ τ) = `∀ (weaken-ty-under τ)

------------------------------------------------------------------------
-- Type substitution

-- Helper: extract proof from s≤s
pred-< : ∀ {m n} → suc m < suc n → m < n
pred-< (s≤s p) = p

mutual
  -- Substitute the outermost type variable (index 0)
  subst-ty : ∀ {Δ} → Type (suc Δ) → Type Δ → Type Δ
  subst-ty `ℕ s = `ℕ
  subst-ty `Bool s = `Bool
  subst-ty (τ₁ ⇒ τ₂) s = subst-ty τ₁ s ⇒ subst-ty τ₂ s
  subst-ty (TyVar {zero} _) s = s
  subst-ty (TyVar {suc n} (s≤s p)) s = TyVar p
  subst-ty (`∀ τ) s = `∀ (subst-ty-lift τ (weaken-ty s))

  -- Substitution under a binder (for ∀)
  -- Variable 0 stays (bound by the ∀ we're under)
  -- Variable 1 → s (the variable being substituted)
  -- Variable (2+n) → Variable (1+n)
  subst-ty-lift : ∀ {Δ} → Type (suc (suc Δ)) → Type (suc Δ) → Type (suc Δ)
  subst-ty-lift `ℕ _ = `ℕ
  subst-ty-lift `Bool _ = `Bool
  subst-ty-lift (τ₁ ⇒ τ₂) s = subst-ty-lift τ₁ s ⇒ subst-ty-lift τ₂ s
  subst-ty-lift (TyVar {zero} _) _ = TyVar z<s   -- Variable 0 stays
  subst-ty-lift (TyVar {suc zero} _) s = s        -- Variable 1 → s
  subst-ty-lift (TyVar {suc (suc n)} (s≤s (s≤s p))) _ = TyVar (s≤s p)  -- Variable 2+n → 1+n
  subst-ty-lift (`∀ τ) s = `∀ (subst-ty-lift τ (weaken-ty s))

------------------------------------------------------------------------
-- Term contexts (list of types, indexed by type context)

data Context (Δ : TyContext) : Set where
  ∅   : Context Δ
  _▸_ : Context Δ → Type Δ → Context Δ

infixl 5 _▸_

-- Weaken all types in a term context (when adding a type variable)
weaken-ctx : ∀ {Δ} → Context Δ → Context (suc Δ)
weaken-ctx ∅ = ∅
weaken-ctx (Γ ▸ τ) = weaken-ctx Γ ▸ weaken-ty τ

------------------------------------------------------------------------
-- Term variables (de Bruijn indices into the term context)

data _∋_ {Δ : TyContext} : Context Δ → Type Δ → Set where
  Z : ∀ {Γ τ}     → Γ ▸ τ ∋ τ
  S : ∀ {Γ τ σ}   → Γ ∋ τ → Γ ▸ σ ∋ τ

infix 4 _∋_

-- Weaken a variable lookup when adding a type variable
weaken-var : ∀ {Δ Γ τ} → _∋_ {Δ} Γ τ → _∋_ {suc Δ} (weaken-ctx Γ) (weaken-ty τ)
weaken-var Z = Z
weaken-var (S x) = S (weaken-var x)

------------------------------------------------------------------------
-- Terms (intrinsically typed)

data _⊢_ {Δ : TyContext} : Context Δ → Type Δ → Set where
  -- Variables
  `_    : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ

  -- Lambda abstraction and application
  ƛ_    : ∀ {Γ τ σ} → Γ ▸ τ ⊢ σ → Γ ⊢ τ ⇒ σ
  _·_   : ∀ {Γ τ σ} → Γ ⊢ τ ⇒ σ → Γ ⊢ τ → Γ ⊢ σ

  -- Type abstraction and application
  Λ_    : ∀ {Γ τ} → weaken-ctx Γ ⊢ τ → Γ ⊢ `∀ τ
  _[_]  : ∀ {Γ τ} → Γ ⊢ `∀ τ → (σ : Type Δ) → Γ ⊢ subst-ty τ σ

  -- Booleans
  `true  : ∀ {Γ} → Γ ⊢ `Bool
  `false : ∀ {Γ} → Γ ⊢ `Bool
  if_then_else_ : ∀ {Γ τ} → Γ ⊢ `Bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ

  -- Natural numbers
  `zero  : ∀ {Γ} → Γ ⊢ `ℕ
  `suc   : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  `pred  : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  `iszero : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `Bool

infix 4 _⊢_
infixl 7 _·_
infix 6 _[_]
infix 5 ƛ_
infix 5 Λ_
infix 6 `_

------------------------------------------------------------------------
-- Example: polymorphic identity function  Λα. λ(x:α). x

-- First, we need the type ∀α. α → α
id-type : Type 0
id-type = `∀ (TyVar z<s ⇒ TyVar z<s)

-- The polymorphic identity
poly-id : ∅ ⊢ id-type
poly-id = Λ (ƛ (` Z))

------------------------------------------------------------------------
-- Example: applying identity to Bool

-- id [Bool] : Bool → Bool
id-bool : ∅ ⊢ `Bool ⇒ `Bool
id-bool = poly-id [ `Bool ]
