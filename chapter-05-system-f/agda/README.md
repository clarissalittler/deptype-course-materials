# Chapter 5: System F - Agda Formalization

This directory contains the Agda formalization of System F (the polymorphic lambda calculus).

## Modules

| Module | Description |
|--------|-------------|
| `Syntax.agda` | Types with type variables, contexts, intrinsically-typed terms, type substitution |
| `Evaluation.agda` | Values, small-step semantics (partial) |
| `All.agda` | Re-exports all modules |

## Type System

System F extends the simply-typed lambda calculus with parametric polymorphism:

```
Type Variables:
  Δ ::= 0 | suc Δ            (number of type variables in scope)

Types:
  τ ::= ℕ | Bool | τ₁ ⇒ τ₂ | α | ∀α.τ

Terms:
  t ::= x | λ(x:τ).t | t₁ t₂       (term-level)
      | Λα.t | t [τ]                (type-level)
      | true | false | if ...       (booleans)
      | 0 | suc | pred | iszero     (naturals)
```

## Key Features

### Intrinsically-Typed Terms

Terms are indexed by both a type context (Δ) and a term context (Γ):

```agda
data _⊢_ {Δ : TyContext} : Context Δ → Type Δ → Set where
  Λ_  : ∀ {Γ τ} → weaken-ctx Γ ⊢ τ → Γ ⊢ `∀ τ
  _[_] : ∀ {Γ τ} → Γ ⊢ `∀ τ → (σ : Type Δ) → Γ ⊢ subst-ty τ σ
  ...
```

### Type Variable Representation

Type variables use de Bruijn indices with proofs of well-scopedness:

```agda
data Type (Δ : TyContext) : Set where
  TyVar : ∀ {n} → n < Δ → Type Δ    -- Variable in scope
  `∀    : Type (suc Δ) → Type Δ     -- Quantifier extends scope
```

### Example: Polymorphic Identity

```agda
-- The type ∀α. α → α
id-type : Type 0
id-type = `∀ (TyVar z<s ⇒ TyVar z<s)

-- The term Λα. λ(x:α). x
poly-id : ∅ ⊢ id-type
poly-id = Λ (ƛ (` Z))

-- Instantiation: id [Bool] : Bool → Bool
id-bool : ∅ ⊢ `Bool ⇒ `Bool
id-bool = poly-id [ `Bool ]
```

## Formalization Notes

### Type Substitution

Type substitution for type application is fully defined:

```agda
subst-ty : ∀ {Δ} → Type (suc Δ) → Type Δ → Type Δ
```

### Limitations

The evaluation rules are partial due to the complexity of term substitution with intrinsically-typed System F terms. Full beta reduction for:
- `(λx.t) v ⟶ t[v/x]`
- `(Λα.t) [τ] ⟶ t[τ/α]`

requires sophisticated term renaming and substitution that properly maintains type indices.

## Building

```bash
agda All.agda
```

## References

- Girard, J.-Y. (1972). *Interprétation fonctionnelle et élimination des coupures*
- Reynolds, J. C. (1974). *Towards a theory of type structure*
- Pierce, B. C. (2002). *Types and Programming Languages*, Chapter 23
- Wadler, P. (2015). *Propositions as Types*
