# Chapter 7: Dependent Types - REPL User Guide

## Overview

The Dependent Types REPL introduces the revolutionary concept where **types can depend on values**! This unifies terms and types into a single language, enabling programs to carry precise specifications in their types. This is the foundation for proof assistants and verified programming.

**Key Features**: Pi types (Π(x:A). B), Sigma types (Σ(x:A). B), unified term/type syntax

**Power**: Types that express precise properties, programs that are provably correct!

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-07-dependent-types
stack build

# Run the REPL
stack exec dependent-types-repl
```

### Your First Dependent Type

```
λΠ> \(A:Type). \(x:A). x
  : Π(A:Type). Π(x:A). A
  λ(A:Type). λ(x:A). x

λΠ> Vec Nat 3
  : Type
  (vector of 3 natural numbers)

λΠ> :help
  [Shows available commands]
```

**Note**: Terms and types use the SAME syntax!

## Features

### 1. Unified Syntax - Terms ARE Types

Everything is a term in the same language:

```
λΠ> Type
  : Type
  Type
  (Type-in-Type, simplified but inconsistent)

λΠ> Nat
  : Type

λΠ> Bool
  : Type

λΠ> Nat -> Bool
  : Type
  (function types are terms!)

λΠ> \(A:Type). A -> A
  : Type -> Type
  (type-level functions!)
```

### 2. Pi Types (Π(x:A). B) - Dependent Functions

Functions where the result type depends on the argument value:

```
λΠ> Π(n:Nat). Vec Nat n
  : Type
  (function that takes n and returns Vec Nat n)
  (result type DEPENDS on argument n!)

λΠ> Π(A:Type). A -> A
  : Type
  (polymorphic identity type)

λΠ> Π(A:Type). Π(B:Type). A -> B -> A
  : Type
  (polymorphic const type)
```

**Syntax**: `Π(x:A). B` or `(x:A) -> B` or just `A -> B` if x not in B

### 3. Non-Dependent vs Dependent Functions

**Non-dependent** (result type doesn't use x):
```
λΠ> Nat -> Bool
  = Π(n:Nat). Bool
  (result type Bool doesn't mention n)
```

**Dependent** (result type uses x):
```
λΠ> Π(n:Nat). Vec Nat n
  (result type Vec Nat n USES n)

λΠ> Π(b:Bool). if b then Nat else Bool
  (result type depends on b!)
```

### 4. Sigma Types (Σ(x:A). B) - Dependent Pairs

Pairs where the second component's type depends on the first's value:

```
λΠ> Σ(n:Nat). Vec Nat n
  : Type
  (pair of number n and vector of length n)

λΠ> Σ(A:Type). A
  : Type
  (pair of a type A and value of that type)
  (existential type!)

λΠ> Σ(b:Bool). if b then Nat else Bool
  : Type
  (pair where second type depends on first value)
```

**Syntax**: `Σ(x:A). B`

### 5. Type-Level Computation

Types can compute because they're terms:

```
λΠ> \(n:Nat). if (iszero n) then Bool else Nat
  : Nat -> Type
  (function returning different types!)

λΠ> (\(n:Nat). if (iszero n) then Bool else Nat) 0
  =β Bool

λΠ> (\(n:Nat). if (iszero n) then Bool else Nat) 1
  =β Nat
```

### 6. Polymorphism as Dependent Types

Universal quantification is a special case of Pi:

```
λΠ> Π(A:Type). A -> A
  = ∀A. A → A (from System F)
  (polymorphic identity)

λΠ> \(A:Type). \(x:A). x
  : Π(A:Type). A -> A
  (identity function, dependent style)
```

### 7. Natural Numbers with Dependent Types

```
λΠ> zero
  : Nat
  0

λΠ> succ zero
  : Nat
  1

λΠ> \(n:Nat). Π(m:Nat). Nat
  : Nat -> Type
  (type-level function on naturals)
```

### 8. Booleans with Dependent Types

```
λΠ> true
  : Bool
  true

λΠ> false
  : Bool
  false

λΠ> \(b:Bool). if b then Nat else Bool
  : Bool -> Type
  (type-level conditional!)
```

### 9. Vectors - Length-Indexed Lists

```
λΠ> Vec Nat 0
  : Type
  (empty vector of Nats)

λΠ> Vec Nat 3
  : Type
  (vector of exactly 3 Nats)

λΠ> Vec Bool 5
  : Type
  (vector of exactly 5 Bools)

λΠ> Π(n:Nat). Vec Nat n -> Vec Nat (succ n)
  : Type
  (function that adds element to vector - type tracks length!)
```

### 10. Normalization-Based Equality

Types are equal if they normalize to the same form:

```
λΠ> :equal (succ zero) 1
  true
  (both normalize to 1)

λΠ> :equal (\(x:Nat). x) (\(y:Nat). y)
  true
  (alpha-equivalent)

λΠ> :equal ((\(x:Nat). x) 0) 0
  true
  (both normalize to 0)
```

### 11. Type Checking with Conversion

The type checker uses normalization to check equality:

```
λΠ> \(f:Nat->Nat). f : Π(x:Nat). Nat
  ✗ Type error: Nat->Nat ≠ Π(x:Nat). Nat
  Actually... wait, these ARE equal!
  Let me reconsider the example:

λΠ> \(f:Π(n:Nat). Vec Nat n). f 3
  : Vec Nat 3
  (type checker normalizes to verify types match)
```

### 12. Step-by-Step Evaluation

```
λΠ> :step
Step mode enabled

λΠ> (\(A:Type). \(x:A). x) Nat zero
  : Nat
  (λ(A:Type). λ(x:A). x) Nat 0
    [Press Enter]
→ (λ(x:Nat). x) 0
    [Press Enter]
→ 0
```

## Command Reference

### Essential Commands
- `:help` - Show help
- `:quit` - Exit
- `:type <term>` - Show type of term
- `:let <name> = <term>` - Bind term
- `:normalize <term>` - Normalize to normal form

### Type Commands
- `:tlet <name> = <term>` - Bind type (same as let!)
- `:equal <term1> <term2>` - Check if equal after normalization

### Evaluation Commands
- `:step` - Step-by-step evaluation
- `:trace` - Show evaluation trace
- `:normalize <term>` - Fully normalize

### Environment Commands
- `:bindings` - Show all bindings
- `:reset` - Clear bindings

## Guided Exploration

### Exercise 1: Understanding Pi Types (15 minutes)

Explore dependent functions:

```
λΠ> Π(n:Nat). Nat
  (what's the difference from Nat -> Nat?)

λΠ> Π(n:Nat). Vec Nat n
  (result type depends on n!)

λΠ> Π(A:Type). A -> A
  (polymorphism!)

λΠ> Π(A:Type). Π(B:Type). A -> B -> A
  (polymorphic const)
```

**Question**: When is Pi different from arrow?

### Exercise 2: Type-Level Functions (20 minutes)

Types that compute:

```
λΠ> \(n:Nat). Vec Nat n
  : Nat -> Type

λΠ> (\(n:Nat). Vec Nat n) 3
  =β Vec Nat 3

λΠ> \(b:Bool). if b then Nat else Bool
  : Bool -> Type

λΠ> (\(b:Bool). if b then Nat else Bool) true
  =β Nat
```

**Challenge**: Write a type-level function that returns Nat for even n, Bool for odd n.

### Exercise 3: Sigma Types (20 minutes)

Dependent pairs:

```
λΠ> Σ(n:Nat). Vec Nat n
  : Type
  (pair of length and vector of that length)

λΠ> Σ(A:Type). A
  : Type
  (existential type - pair of type and value)

λΠ> Σ(A:Type). Σ(B:Type). A -> B
  : Type
  (triple: two types and a function between them)
```

**Challenge**: What's the difference between `Σ(x:A). B` and `A * B`?

### Exercise 4: Polymorphic Functions (25 minutes)

Dependent-style polymorphism:

```
λΠ> :let id = \(A:Type). \(x:A). x
  id : Π(A:Type). A -> A

λΠ> id Nat zero
λΠ> id Bool true
λΠ> id (Nat -> Nat) (\(x:Nat). x)

λΠ> :let const = \(A:Type). \(B:Type). \(x:A). \(y:B). x
  const : Π(A:Type). Π(B:Type). A -> B -> A

λΠ> const Nat Bool zero true

λΠ> :let compose = \(A:Type). \(B:Type). \(C:Type).
                     \(f:B->C). \(g:A->B). \(x:A). f (g x)
  compose : Π(A:Type). Π(B:Type). Π(C:Type).
            (B->C) -> (A->B) -> A -> C
```

**Challenge**: Implement `apply : Π(A:Type). Π(B:Type). (A->B) -> A -> B`.

### Exercise 5: Vectors (30 minutes)

Length-indexed vectors:

```
λΠ> :type Vec
  Vec : Type -> Nat -> Type

λΠ> Vec Nat 0
λΠ> Vec Nat 3
λΠ> Vec Bool 5

λΠ> :let vnil = \(A:Type). nil [A]
  vnil : Π(A:Type). Vec A 0

λΠ> :let vcons = \(A:Type). \(n:Nat). \(x:A). \(xs:Vec A n).
                   cons [A] [n] x xs
  vcons : Π(A:Type). Π(n:Nat). A -> Vec A n -> Vec A (succ n)
  (type tracks length changes!)
```

**Challenge**: What's the type of `vappend`?

### Exercise 6: Type Equality (15 minutes)

Understanding definitional equality:

```
λΠ> :equal Nat Nat
  true

λΠ> :equal (succ zero) 1
  true (both normalize to 1)

λΠ> :equal (\(x:Nat). x) (\(y:Nat). y)
  true (alpha-equivalent)

λΠ> :equal (Nat -> Nat) (Π(x:Nat). Nat)
  true (syntactically different, but equal!)

λΠ> :equal (\(n:Nat). Vec Nat n) (\(m:Nat). Vec Nat m)
  true (alpha-equivalent)
```

**Challenge**: Find two terms that look different but are equal.

### Exercise 7: Curry-Howard Correspondence (20 minutes)

Types as propositions:

```
λΠ> Nat -> Nat
  (Proposition: Nat implies Nat - always true!)

λΠ> Π(A:Type). A -> A
  (Proposition: for all A, A implies A)

λΠ> Π(A:Type). Π(B:Type). A -> B -> A
  (Proposition: for all A,B, A and B implies A)

λΠ> \(A:Type). \(x:A). x
  : Π(A:Type). A -> A
  (Proof of "for all A, A implies A")
```

**Insight**: Programs are proofs, types are propositions!

## Tips and Tricks

### Tip 1: Terms and Types Unified
```
λΠ> Nat : Type           (Nat is a term of type Type)
λΠ> zero : Nat           (zero is a term of type Nat)
λΠ> Type : Type          (Type-in-Type, inconsistent!)
```

### Tip 2: Use Pi When Result Depends on Arg
```
Π(n:Nat). Vec Nat n      ✓ Result uses n
Π(n:Nat). Nat            = Nat -> Nat (n not used)
```

### Tip 3: Normalize to Check Equality
```
λΠ> :normalize (\(x:Nat). succ x) zero
  = 1
λΠ> :normalize succ zero
  = 1
λΠ> :equal them  ✓
```

### Tip 4: Type-Level Functions Are Powerful
```
\(n:Nat). Vec Nat n           Types that depend on values!
\(b:Bool). if b then Nat else Bool  Conditional types!
```

## Troubleshooting

### Problem: "Type mismatch after normalization"
**Cause**: Types don't match even after normalization
**Solution**: Check with `:normalize` on both types

### Problem: "Inconsistency from Type-in-Type"
**Cause**: Type-in-Type allows paradoxes (Girard's paradox)
**Solution**: Accept limitation or move to Chapter 8 (universe hierarchy)

### Problem: "Cannot check equality of infinite terms"
**Cause**: Non-terminating computation in types
**Solution**: Ensure type-level computation terminates

## Syntax Reference

### Terms (which include types!)
```
x, y, z, ...           -- Variables
Type                   -- Type of types
Π(x:A). B             -- Pi type (dependent function)
\(x:A). t             -- Lambda abstraction
t1 t2                 -- Application
Σ(x:A). B             -- Sigma type (dependent pair)
pair t1 t2            -- Pair construction
fst t, snd t          -- Pair projection
Nat, Bool             -- Base types
zero, succ, pred      -- Naturals
true, false, if       -- Booleans
Vec A n               -- Vectors
```

### Syntactic Sugar
```
A -> B        ≡ Π(x:A). B   (when x not in B)
(x:A) -> B    ≡ Π(x:A). B
forall (x:A). B ≡ Π(x:A). B
A * B         ≡ Σ(x:A). B   (when x not in B)
```

## Comparison with Previous Chapters

| Feature | Chapter 5 (System F) | Chapter 7 (Dep Types) |
|---------|---------------------|----------------------|
| Terms and types | Separate | Unified |
| Type dependency | No | Yes! Types depend on values |
| Polymorphism | Explicit ∀ | Pi types Π |
| Consistency | Yes | No (Type-in-Type) |
| Expressiveness | High | Very high |
| Proofs | Limited | Full (Curry-Howard) |

## Connection to Real Languages

Dependent types power:
- **Agda**: Full dependent types with universe hierarchy
- **Coq**: Calculus of Constructions
- **Idris**: Dependent types in a practical language
- **Lean**: Theorem prover with dependent types

## Key Theoretical Properties

1. **Unified Syntax**: Terms and types use same language
2. **Type-in-Type**: Inconsistent (allows paradoxes)
3. **Normalization-Based Equality**: Types equal if they normalize the same
4. **Curry-Howard**: Full correspondence between programs and proofs

## Next Steps

After mastering this REPL:
1. Complete exercises in `exercises/EXERCISES.md`
2. Work through `TUTORIAL.md`
3. Take `QUIZ.md`
4. Review `COMMON_MISTAKES.md`
5. Move to Chapter 8 for universe hierarchy and consistency!

## Quick Reference Card

```
# Building
stack build && stack exec dependent-types-repl

# Pi Types (Dependent Functions)
Π(x:A). B              Dependent function type
\(x:A). t              Lambda abstraction
A -> B                 Non-dependent function (sugar)

# Sigma Types (Dependent Pairs)
Σ(x:A). B              Dependent pair type
pair t1 t2             Pair construction
fst t, snd t           Projections

# Key Commands
:type <term>           Show type
:normalize <term>      Normalize
:equal <t1> <t2>       Check equality

# Key Insight
Terms = Types = Programs = Proofs!
```

Happy dependent typing! 🎓
