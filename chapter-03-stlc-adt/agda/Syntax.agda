------------------------------------------------------------------------
-- Chapter 3: STLC with Algebraic Data Types - Syntax
--
-- This module defines the intrinsically-typed terms for the simply-typed
-- lambda calculus extended with products (pairs) and sums.
------------------------------------------------------------------------

module Syntax where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Types

data Type : Set where
  `ℕ    : Type                    -- Natural numbers
  `Bool : Type                    -- Booleans
  `⊤    : Type                    -- Unit type
  _⇒_   : Type → Type → Type      -- Function type
  _`×_  : Type → Type → Type      -- Product type
  _`+_  : Type → Type → Type      -- Sum type

infixr 7 _⇒_
infixr 8 _`×_
infixr 7 _`+_

------------------------------------------------------------------------
-- Contexts (using snoc-lists)

data Context : Set where
  ∅   : Context
  _▸_ : Context → Type → Context

infixl 5 _▸_

------------------------------------------------------------------------
-- Variables (de Bruijn indices with typing)

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ τ}     → Γ ▸ τ ∋ τ
  S : ∀ {Γ τ σ}   → Γ ∋ τ → Γ ▸ σ ∋ τ

infix 4 _∋_

------------------------------------------------------------------------
-- Terms (intrinsically typed)

data _⊢_ : Context → Type → Set where
  -- Variables
  `_    : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ

  -- Lambda abstraction and application
  ƛ_    : ∀ {Γ τ σ} → Γ ▸ τ ⊢ σ → Γ ⊢ τ ⇒ σ
  _·_   : ∀ {Γ τ σ} → Γ ⊢ τ ⇒ σ → Γ ⊢ τ → Γ ⊢ σ

  -- Booleans
  `true  : ∀ {Γ} → Γ ⊢ `Bool
  `false : ∀ {Γ} → Γ ⊢ `Bool
  if_then_else_ : ∀ {Γ τ} → Γ ⊢ `Bool → Γ ⊢ τ → Γ ⊢ τ → Γ ⊢ τ

  -- Natural numbers
  `zero  : ∀ {Γ} → Γ ⊢ `ℕ
  `suc   : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  `pred  : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `ℕ
  `iszero : ∀ {Γ} → Γ ⊢ `ℕ → Γ ⊢ `Bool

  -- Unit
  `tt   : ∀ {Γ} → Γ ⊢ `⊤

  -- Products (pairs)
  `⟨_,_⟩ : ∀ {Γ τ σ} → Γ ⊢ τ → Γ ⊢ σ → Γ ⊢ τ `× σ
  `fst   : ∀ {Γ τ σ} → Γ ⊢ τ `× σ → Γ ⊢ τ
  `snd   : ∀ {Γ τ σ} → Γ ⊢ τ `× σ → Γ ⊢ σ

  -- Sums
  `inl   : ∀ {Γ τ σ} → Γ ⊢ τ → Γ ⊢ τ `+ σ
  `inr   : ∀ {Γ τ σ} → Γ ⊢ σ → Γ ⊢ τ `+ σ
  case_of_∣_ : ∀ {Γ τ σ ρ}
    → Γ ⊢ τ `+ σ
    → Γ ▸ τ ⊢ ρ
    → Γ ▸ σ ⊢ ρ
    → Γ ⊢ ρ

infix 4 _⊢_
infixl 7 _·_
infix 5 ƛ_
infix 6 `_

------------------------------------------------------------------------
-- Renaming

Rename : Context → Context → Set
Rename Γ Δ = ∀ {τ} → Γ ∋ τ → Δ ∋ τ

ext : ∀ {Γ Δ τ} → Rename Γ Δ → Rename (Γ ▸ τ) (Δ ▸ τ)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

rename : ∀ {Γ Δ τ} → Rename Γ Δ → Γ ⊢ τ → Δ ⊢ τ
rename ρ (` x)                = ` ρ x
rename ρ (ƛ t)                = ƛ rename (ext ρ) t
rename ρ (t₁ · t₂)            = rename ρ t₁ · rename ρ t₂
rename ρ `true                = `true
rename ρ `false               = `false
rename ρ (if t₁ then t₂ else t₃) = if rename ρ t₁ then rename ρ t₂ else rename ρ t₃
rename ρ `zero                = `zero
rename ρ (`suc t)             = `suc (rename ρ t)
rename ρ (`pred t)            = `pred (rename ρ t)
rename ρ (`iszero t)          = `iszero (rename ρ t)
rename ρ `tt                  = `tt
rename ρ `⟨ t₁ , t₂ ⟩         = `⟨ rename ρ t₁ , rename ρ t₂ ⟩
rename ρ (`fst t)             = `fst (rename ρ t)
rename ρ (`snd t)             = `snd (rename ρ t)
rename ρ (`inl t)             = `inl (rename ρ t)
rename ρ (`inr t)             = `inr (rename ρ t)
rename ρ (case t of l ∣ r)    = case rename ρ t of rename (ext ρ) l ∣ rename (ext ρ) r

------------------------------------------------------------------------
-- Substitution

Subst : Context → Context → Set
Subst Γ Δ = ∀ {τ} → Γ ∋ τ → Δ ⊢ τ

exts : ∀ {Γ Δ τ} → Subst Γ Δ → Subst (Γ ▸ τ) (Δ ▸ τ)
exts σ Z     = ` Z
exts σ (S x) = rename S (σ x)

subst : ∀ {Γ Δ τ} → Subst Γ Δ → Γ ⊢ τ → Δ ⊢ τ
subst σ (` x)                = σ x
subst σ (ƛ t)                = ƛ subst (exts σ) t
subst σ (t₁ · t₂)            = subst σ t₁ · subst σ t₂
subst σ `true                = `true
subst σ `false               = `false
subst σ (if t₁ then t₂ else t₃) = if subst σ t₁ then subst σ t₂ else subst σ t₃
subst σ `zero                = `zero
subst σ (`suc t)             = `suc (subst σ t)
subst σ (`pred t)            = `pred (subst σ t)
subst σ (`iszero t)          = `iszero (subst σ t)
subst σ `tt                  = `tt
subst σ `⟨ t₁ , t₂ ⟩         = `⟨ subst σ t₁ , subst σ t₂ ⟩
subst σ (`fst t)             = `fst (subst σ t)
subst σ (`snd t)             = `snd (subst σ t)
subst σ (`inl t)             = `inl (subst σ t)
subst σ (`inr t)             = `inr (subst σ t)
subst σ (case t of l ∣ r)    = case subst σ t of subst (exts σ) l ∣ subst (exts σ) r

------------------------------------------------------------------------
-- Single substitution

_[_] : ∀ {Γ τ σ} → Γ ▸ σ ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
t [ s ] = subst σ t
  where
    σ : Subst (_ ▸ _) _
    σ Z     = s
    σ (S x) = ` x

infix 8 _[_]
