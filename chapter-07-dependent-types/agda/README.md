# Chapter 7: Dependent Types - Agda Formalization

This directory contains the Agda formalization of a simple dependent type theory with Pi types (dependent functions), Sigma types (dependent pairs), and `Type : Type`.

## Modules

| Module | Description |
|--------|-------------|
| `Syntax.agda` | Well-scoped terms with de Bruijn indices, renaming, substitution |
| `TypeCheck.agda` | Typing judgment as an inductive relation |
| `Evaluation.agda` | Values, small-step semantics, multi-step reduction, normalization |
| `All.agda` | Re-exports all modules |

## Type System

The formalization includes a simple dependent type theory:

```
Terms (also used as Types):
  t, A, B ::= Type                  -- Universe
            | x                     -- Variable
            | λ(x:A). t             -- Lambda abstraction
            | t₁ t₂                 -- Application
            | Π(x:A). B             -- Dependent function type
            | Σ(x:A). B             -- Dependent pair type
            | (t₁, t₂)              -- Pair
            | fst t | snd t         -- Projections
            | ℕ | 0 | suc t         -- Natural numbers
            | Bool | true | false   -- Booleans
            | if t then t else t
```

## Key Features

### Unified Terms and Types

In dependent type theory, there is no syntactic distinction between terms and types:

```agda
data Term (n : ℕ) : Set where
  `Type : Term n              -- Type is a term
  `Π    : Term n → Term (suc n) → Term n  -- Pi is a term
  ƛ     : Term n → Term (suc n) → Term n  -- Lambda is a term
  ...
```

### Well-Scoped Terms

Terms are indexed by the number of variables in scope:

```agda
data Term (n : ℕ) : Set where
  `_ : Fin n → Term n   -- Variable index must be < n
```

### Type : Type

For simplicity, we use the rule `Type : Type`. This makes the system inconsistent (Girard's paradox) but simplifies the formalization. Real systems use a universe hierarchy.

### Typing Judgment

The typing relation is defined as an inductive type:

```agda
data _⊢_∶_ {n} (Γ : Context n) : Term n → Term n → Set where
  T-App : ∀ {A B f a}
        → Γ ⊢ f ∶ `Π A B
        → Γ ⊢ a ∶ A
        → Γ ⊢ f · a ∶ (B [ a ])  -- Dependent application!
  ...
```

Note how application has a **dependent** result type: `B [ a ]` substitutes `a` for the bound variable in `B`.

## Examples

### Polymorphic Identity

```agda
-- Type: Π(A:Type). Π(x:A). A
poly-id-type : Term 0
poly-id-type = `Π `Type (`Π (` zero) (` (suc zero)))

-- Term: λ(A:Type). λ(x:A). x
poly-id : Term 0
poly-id = ƛ `Type (ƛ (` zero) (` zero))
```

### Dependent Pair

```agda
-- Type: Σ(x:ℕ). ℕ
dep-pair-type : Term 0
dep-pair-type = `Σ `ℕ `ℕ

-- Term: (0, 0)
dep-pair : Term 0
dep-pair = `⟨ `zero , `zero ⟩
```

## Building

```bash
agda All.agda
```

## Comparison with Intrinsic Typing

Unlike Chapters 2-3, this formalization uses **extrinsic typing** (well-scoped but not well-typed by construction) because:

1. Full intrinsic typing for dependent types requires implementing type checking in the types themselves
2. This matches how real type checkers work
3. It allows stating and proving properties about type checking

## References

- Martin-Löf, P. (1984). *Intuitionistic Type Theory*
- Coquand, T. & Huet, G. (1988). *The Calculus of Constructions*
- Pierce, B. C. (2002). *Types and Programming Languages*, Chapter 30
- The Agda documentation: <https://agda.readthedocs.io/>
