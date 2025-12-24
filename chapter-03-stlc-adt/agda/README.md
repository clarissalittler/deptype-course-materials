# Chapter 3: STLC with Algebraic Data Types - Agda Formalization

This directory contains the Agda formalization of the simply-typed lambda calculus extended with algebraic data types (products and sums).

## Modules

| Module | Description |
|--------|-------------|
| `Syntax.agda` | Types, contexts, intrinsically-typed terms, renaming, substitution |
| `Evaluation.agda` | Values, small-step semantics, multi-step reduction, examples |
| `Progress.agda` | Progress theorem, canonical forms lemmas |
| `Preservation.agda` | Preservation (trivial), determinism of evaluation |
| `All.agda` | Re-exports all modules |

## Type System

This formalization extends Chapter 2 with:

```
Types:
  τ ::= ℕ | Bool | ⊤ | τ₁ ⇒ τ₂ | τ₁ × τ₂ | τ₁ + τ₂

New Terms:
  Unit:     tt
  Products: ⟨t₁, t₂⟩ | fst t | snd t
  Sums:     inl t | inr t | case t of x₁ => t₁ | x₂ => t₂
```

## Key Theorems

### Progress
Every well-typed closed term is either a value or can take a step.

```agda
progress : ∀ {τ} (t : ∅ ⊢ τ) → Progress t
```

### Preservation (Trivial)
With intrinsically-typed terms, preservation is guaranteed by construction:
the step relation `_⟶_` only relates terms of the same type.

### Determinism
Evaluation is deterministic: if `t ⟶ t₁` and `t ⟶ t₂`, then `t₁ ≡ t₂`.

```agda
determinism : ∀ {Γ τ} {t t₁ t₂ : Γ ⊢ τ}
  → t ⟶ t₁ → t ⟶ t₂ → t₁ ≡ t₂
```

## Evaluation Strategy

Products and sums use **call-by-value** evaluation:
- Pairs `⟨t₁, t₂⟩` evaluate left-to-right until both are values
- Injections `inl t` and `inr t` evaluate their argument to a value
- Projections `fst`/`snd` and `case` only reduce when the scrutinee is a value

## Building

```bash
# Type-check all modules
agda All.agda

# Type-check individual modules
agda Syntax.agda
```

## Differences from Haskell Implementation

1. **Intrinsic vs Extrinsic Typing**: The Agda formalization uses intrinsically-typed terms where types are part of the term structure.

2. **De Bruijn Indices**: Variables use de Bruijn indices instead of named variables.

3. **Core Subset**: This formalization focuses on products and sums. The full Haskell implementation also includes:
   - Records (labeled products)
   - Variants (labeled sums)
   - Lists
   - Pattern matching

## References

- Pierce, B. C. (2002). *Types and Programming Languages*, Chapters 11 (Products and Sums)
- Wadler, P. (2019). *Programming Language Foundations in Agda*
