# Chapter 13: Gradual Typing

## Overview

This chapter introduces **gradual typing**, which allows mixing statically-typed and dynamically-typed code in the same program. The key insight is the **dynamic type** `?`, which is *consistent* with any other type.

## Core Concepts

### The Dynamic Type

The type `?` (pronounced "dynamic" or "unknown") represents values whose type is not known statically. Unlike other types:
- `?` is consistent with every type
- Runtime checks ensure safety
- Blame tracking identifies error sources

### Key Ideas

1. **Consistency (~)**: Replaces equality in type checking
2. **Casts**: Explicit runtime type coercions
3. **Blame**: Track where type errors originate
4. **Ground Types**: Base types for runtime representation

## Syntax

### Types

```
T ::= Bool | Nat | Unit         -- Base types
    | T₁ -> T₂                   -- Function type
    | ?                          -- Dynamic type
```

### Terms

```
t ::= x | λx : T. t | t₁ t₂      -- Core lambda calculus
    | <T₁ => T₂>^l t             -- Cast with blame label
    | t : T                      -- Type ascription
    | blame^l : T                -- Runtime type error
```

## Consistency Relation

The consistency relation `~` replaces type equality:

```
  ───────                ───────
  ? ~ T                  T ~ ?

  ───────────────────────────────
  T ~ T   (for base types)

  T₁ ~ S₁    T₂ ~ S₂
  ─────────────────────
  T₁ -> T₂ ~ S₁ -> S₂
```

Consistency is **reflexive** and **symmetric** but NOT **transitive**!

Example: `Nat ~ ?` and `? ~ Bool`, but `Nat ≁ Bool`.

## Type Checking

### Key Rule Changes

Replace equality with consistency:

```
   Γ ⊢ t₁ : T₁ -> T₂    Γ ⊢ t₂ : S    T₁ ~ S
  ──────────────────────────────────────────── (App)
                  Γ ⊢ t₁ t₂ : T₂
```

### Examples

```
-- Dynamic identity: accepts anything
λx : ?. x                        -- Type: ? -> ?

-- Apply dynamic function to Nat
(λf : ?. f 0) (λx : Nat. x)      -- Type: ?

-- Mixed typing
λf : ? -> Nat. λx : ?. f x       -- Type: (? -> Nat) -> ? -> Nat
```

## Cast Calculus

### Cast Insertion

The surface language implicitly inserts casts:

```
-- Source:
(λx : ?. succ x) true

-- After cast insertion:
(λx : ?. succ <? => Nat>^l x) <Bool => ?>^l' true
```

### Cast Semantics

Casts are reduced at runtime:

```
<T => T> v = v                           -- Identity
<G => ?> v = <G => ?> v                  -- Injection (value form)
<? => G> (<G => ?> v) = v                -- Round-trip
<? => G'> (<G => ?> v) = blame^l         -- Ground mismatch
<T₁->T₂ => S₁->S₂> v = λx. <T₂=>S₂> (v (<S₁=>T₁> x))
```

### Ground Types

Ground types are the "runtime tags":
- `Bool`, `Nat`, `Unit` - base types
- `? -> ?` - function ground type

## Blame Tracking

### What is Blame?

When a cast fails at runtime, blame identifies the source:

```
(<Bool => Nat>^l true)  →  blame^l : Nat
```

The label `l` points to the source location of the problematic code.

### Blame Theorem

**Well-typed programs can't be blamed** (Wadler & Findler):
- Positive blame: Caller provided wrong type
- Negative blame: Function returned wrong type

A fully statically-typed function can never be blamed.

## Examples

### Gradual Migration

Start with dynamic code:
```
-- Phase 1: All dynamic
let add = λx : ?. λy : ?. x + y
```

Gradually add types:
```
-- Phase 2: Partially typed
let add = λx : Nat. λy : ?. x + y

-- Phase 3: Fully typed
let add = λx : Nat. λy : Nat. x + y
```

### Interop with Dynamic Language

```
-- Call Python-like function from typed code
let pyFunc : ? -> ? = ...  -- From FFI
let result = pyFunc 42     -- ? type
let typed : Nat = result   -- Runtime check
```

## Implementation Highlights

### TypeCheck.hs

```haskell
-- Consistency check
consistent :: Type -> Type -> Bool
consistent TyDyn _ = True
consistent _ TyDyn = True
consistent (TyFun t1 t2) (TyFun s1 s2) =
  consistent t1 s1 && consistent t2 s2
consistent t1 t2 = t1 == t2

-- Meet: most precise common type
meet :: Type -> Type -> Maybe Type
meet TyDyn t = Just t
meet t TyDyn = Just t
-- ...
```

### Eval.hs

```haskell
-- Cast application
applyCast :: Term -> Type -> Type -> BlameLabel -> Maybe Term
applyCast v ty1 ty2 l
  | ty1 == ty2 = Just v  -- Identity
  | ty2 == TyDyn = ...   -- Injection
  | ty1 == TyDyn = ...   -- Projection (may fail)
```

## Running the REPL

```bash
stack build
stack exec gradual-repl
```

Example session:
```
gradual> :type λx : ?. x
? -> ?

gradual> :type (λx : ?. succ x) 0
Nat

gradual> :casts (λx : ?. x) 0
(λx : ?. x) <Nat => ?>^arg 0
```

## Connections to Real Languages

- **TypeScript**: Gradual typing with `any`
- **Python**: Type hints with `Any`
- **Typed Racket**: Full gradual typing with contracts
- **Flow**: Gradual typing for JavaScript
- **Hack**: PHP with gradual types

## Gradual Guarantee

A well-designed gradual type system satisfies:

1. **Static Gradual Guarantee**: Making types more/less precise preserves typeability
2. **Dynamic Gradual Guarantee**: Making types more precise doesn't change behavior (up to blame)

## Exercises

See `exercises/EXERCISES.md` for:
- Consistency relation practice
- Cast insertion exercises
- Blame tracking
- Space-efficient casts

## References

### Foundational Papers

- **Siek & Taha, "Gradual Typing for Functional Languages" (2006)**
  The original paper introducing gradual typing with consistency relation.
  [PDF](http://scheme2006.cs.uchicago.edu/13-siek.pdf) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=1764662457634757980)

- **Wadler & Findler, "Well-Typed Programs Can't Be Blamed" (2009)**
  Introduces blame tracking and proves the blame theorem.
  [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-642-00590-9_1) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=6448771910508765384)

### Refined Criteria

- **Siek et al., "Refined Criteria for Gradual Typing" (2015)**
  Establishes the formal criteria a gradual type system should satisfy.
  [DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SNAPL.2015.274) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=1627573328299789917)

- **Garcia et al., "Abstracting Gradual Typing" (2016)**
  Shows how to systematically derive gradual type systems from static ones.
  [ACM DL](https://dl.acm.org/doi/10.1145/2837614.2837670) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=12569055159639880165)

## Project Structure

```
chapter-13-gradual-typing/
├── src/
│   ├── Syntax.hs      -- Types with ?, terms with casts
│   ├── TypeCheck.hs   -- Consistency-based type checking
│   ├── Eval.hs        -- Cast semantics, blame
│   ├── Parser.hs      -- Parser
│   └── Pretty.hs      -- Pretty printer
├── app/
│   └── Main.hs        -- REPL
├── test/
│   └── Spec.hs        -- Test suite (52 tests)
├── exercises/
│   └── EXERCISES.md   -- Practice exercises
├── package.yaml
├── stack.yaml
└── README.md
```
