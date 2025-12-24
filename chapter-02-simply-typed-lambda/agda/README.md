# Agda Formalization: Simply Typed Lambda Calculus

This directory contains the Agda formalization of the Simply Typed Lambda Calculus (STLC) from Chapter 2.

## Modules

| Module | Description |
|--------|-------------|
| `Syntax.agda` | Types, contexts, and intrinsically-typed terms |
| `Evaluation.agda` | Small-step operational semantics and values |
| `Progress.agda` | Progress theorem with proof |
| `Preservation.agda` | Preservation theorem (free with intrinsic typing!) |
| `All.agda` | Convenience module that re-exports everything |

## Building

```bash
# Type-check all modules
agda All.agda

# Type-check individual module
agda Progress.agda
```

## Type Safety Theorems

### Progress

> If `∅ ⊢ t : τ` then either `t` is a value or there exists `t'` such that `t ⟶ t'`.

This is proven in `Progress.agda` using the canonical forms lemmas.

### Preservation

> If `Γ ⊢ t : τ` and `t ⟶ t'` then `Γ ⊢ t' : τ`.

With intrinsically-typed terms, this is **free**! The reduction relation is:
```agda
data _⟶_ : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢ τ → Set
```
Both terms share the same type index `τ`, so preservation holds by construction.

## Intrinsic vs Extrinsic Typing

### Haskell (Extrinsic)
```haskell
data Term = Var Var | Lam Var Type Term | App Term Term | ...
typeOf :: Context -> Term -> Either TypeError Type
```
Terms and types are separate. We must prove preservation.

### Agda (Intrinsic)
```agda
data _⊢_ : Context → Type → Set where
  ƛ_ : (Γ , τ₁) ⊢ τ₂ → Γ ⊢ (τ₁ ⇒ τ₂)
  ...
```
Terms are indexed by their types. Ill-typed terms cannot be constructed!

## What's Proven

- **Progress**: Well-typed closed terms don't get stuck
- **Preservation**: Reduction preserves types (by construction)
- **Determinism**: Call-by-value evaluation is deterministic
- **Canonical Forms**: Values have expected structure for each type

## Key Techniques

1. **De Bruijn Indices**: Variables are natural numbers representing binding depth
2. **Contexts as Snoc-Lists**: `∅` is empty, `Γ , τ` extends with type `τ`
3. **Membership Proofs**: `Γ ∋ τ` proves that `τ` is in `Γ` at some position
4. **Substitution Lemma**: Type-preserving substitution `_[_]`

## Exercises

1. **Add let-bindings**: Extend with `let x = e₁ in e₂` and prove it preserves type safety.

2. **Add pairs**: Extend with product types `τ₁ × τ₂` and projections.

3. **Strong normalization**: Prove that all well-typed terms terminate.

4. **Compare approaches**: Try the extrinsic approach (separate `Term` and typing judgment) and prove preservation explicitly.

## References

- *Types and Programming Languages* by Benjamin Pierce, Chapters 9-11
- *Programming Language Foundations in Agda* (PLFA) by Wadler et al.
- *Software Foundations* Volume 2: Programming Language Foundations
