# Chapter 6: System F-omega - REPL User Guide

## Overview

The System F-omega REPL extends System F with **higher-kinded types** and **type operators**. Now types themselves can be parameterized by other types! This enables type-level programming and is the foundation for Haskell's type system, Scala's higher-kinded types, and advanced TypeScript features.

**Key Addition**: Kinds (*, * → *, (* → *) → *), type-level lambda, type-level application

**Power**: Program at the type level, not just the term level!

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-06-system-f-omega
stack build

# Run the REPL
stack exec system-f-omega-repl
```

### Your First Higher-Kinded Type

```
λω> /\A::*. \x:A. x
  : ∀(A::*). A → A
  Λα::*. λx:α. x

λω> :tlet List = /\A::*. forall B::*. (A -> B -> B) -> B -> B
  List :: * → *
  List = Λα::*. ∀(B::*). (α → B → B) → B → B

λω> :kind List
  List :: * → *

λω> :kind List Nat
  List Nat :: *

λω> :help
  [Shows available commands]
```

**Note**: `::*` means "has kind star" (proper type)

## Features

### 1. Kinds - Types of Types

Every type has a kind:

```
λω> :kind Nat
  Nat :: *
  (* means "proper type" - types of values)

λω> :kind Bool
  Bool :: *

λω> :kind Nat -> Bool
  Nat → Bool :: *

λω> :tlet List = /\A::*. forall B::*. (A -> B -> B) -> B -> B
λω> :kind List
  List :: * → *
  (* → * means "type constructor" - takes type, returns type)

λω> :kind List Nat
  List Nat :: *
  (after application, we get a proper type)
```

**Kind Hierarchy**:
- `*` - Kind of value types (Nat, Bool, Nat → Bool)
- `* → *` - Kind of type constructors (List, Maybe)
- `(* → *) → *` - Kind of higher-kinded types (Functor, Monad)

### 2. Type-Level Lambda Abstraction

Abstract over types at the type level:

```
λω> :tlet List = /\A::*. forall B::*. (A -> B -> B) -> B -> B
  List :: * → *
  (type-level lambda: takes A, returns a type)

λω> :tlet Maybe = /\A::*. forall B::*. B -> (A -> B) -> B
  Maybe :: * → *

λω> :tlet Either = /\A::*. /\B::*. forall C::*.
                     (A -> C) -> (B -> C) -> C
  Either :: * → * → *
  (takes two types, returns a type)
```

### 3. Type-Level Application

Apply types to type constructors:

```
λω> :tlet List = /\A::*. forall B::*. (A -> B -> B) -> B -> B
  List :: * → *

λω> List Nat
  : *
  (List applied to Nat gives a proper type)

λω> List Bool
  : *

λω> List (Nat -> Nat)
  : *
  (can apply to function types!)

λω> :tlet Either = /\A::*. /\B::*. forall C::*.
                     (A -> C) -> (B -> C) -> C
λω> Either Nat Bool
  : * → * → *... wait, needs more! Let me recalculate:
  Actually: Either Nat Bool :: *
```

### 4. Type Operators

Define reusable type constructors:

```
λω> :tlet Maybe = /\A::*. forall B::*. B -> (A -> B) -> B
  Maybe :: * → *

λω> :tlet List = /\A::*. forall B::*. (A -> B -> B) -> B -> B
  List :: * → *

λω> :tlet Either = /\A::*. /\B::*. forall C::*.
                     (A -> C) -> (B -> C) -> C
  Either :: * → * → *

λω> :tlet Pair = /\A::*. /\B::*. forall C::*.
                   (A -> B -> C) -> C
  Pair :: * → * → *
```

### 5. Higher-Kinded Type Operators

Types that take type constructors as arguments:

```
λω> :tlet Functor = /\F::*->*.
                      forall A::*. forall B::*.
                      (A -> B) -> F A -> F B
  Functor :: (* → *) → *
  (takes a type constructor F, returns a type)

λω> :tlet Monad = /\M::*->*.
                    forall A::*. forall B::*.
                    M A -> (A -> M B) -> M B
  Monad :: (* → *) → *
```

**Key**: `F::*->*` means F is itself a type constructor!

### 6. Kind Checking

The REPL checks kinds just like it checks types:

```
λω> :kind Nat
  Nat :: *

λω> :kind List
  List :: * → *

λω> :kind List Nat
  List Nat :: *

λω> :kind List (Nat -> Bool)
  List (Nat → Bool) :: *

λω> :kind Functor
  Functor :: (* → *) → *

λω> :kind Functor List
  Functor List :: *
  (Functor applied to List - both higher-kinded!)
```

### 7. Church Encodings at the Type Level

```
λω> :tlet List = /\A::*. forall B::*. (A -> B -> B) -> B -> B
λω> :tlet nil = /\A::*. /\B::*. \c:A->B->B. \n:B. n
  nil : ∀(A::*). List A

λω> :tlet cons = /\A::*. \x:A. \xs:List A.
                   /\B::*. \c:A->B->B. \n:B. c x (xs [B] c n)
  cons : ∀(A::*). A → List A → List A

λω> :let emptyNats = nil [Nat]
λω> :let oneNat = cons [Nat] zero (nil [Nat])
```

### 8. Functor and Monad Examples

```
λω> :tlet Functor = /\F::*->*.
                      forall A::*. forall B::*.
                      (A -> B) -> F A -> F B

λω> :let mapMaybe = /\A::*. /\B::*. \f:A->B. \m:Maybe A.
                      m [Maybe B]
                        (/\C::*. \n:C. \j:B->C. n)  -- Nothing case
                        (\a:A. /\C::*. \n:C. \j:B->C. j (f a))  -- Just case
  mapMaybe : ∀(A::*). ∀(B::*). (A → B) → Maybe A → Maybe B

λω> :let mapList = /\A::*. /\B::*. \f:A->B. \xs:List A.
                     /\C::*. \cons:B->C->C. \nil:C.
                     xs [C] (\a:A. \acc:C. cons (f a) acc) nil
  mapList : ∀(A::*). ∀(B::*). (A → B) → List A → List B
```

### 9. Type-Level Computation

Types can compute via beta-reduction:

```
λω> :tlet Apply = /\F::*->*. /\A::*. F A
  Apply :: (* → *) → * → *

λω> Apply List Nat
  =β List Nat
  : *

λω> :tlet Compose = /\F::*->*. /\G::*->*. /\A::*. F (G A)
  Compose :: (* → *) → (* → *) → * → *

λω> Compose Maybe List Nat
  =β Maybe (List Nat)
  : *
```

### 10. Step-by-Step Type Reduction

```
λω> :tstep
Type-level step mode enabled

λω> :normalize (/\A::*. /\B::*. Pair A B) Nat Bool
  (Λα::*. Λβ::*. Pair α β) Nat Bool
    [Press Enter]
→ (Λβ::*. Pair Nat β) Bool
    [Press Enter]
→ Pair Nat Bool
    [Press Enter]
→ ∀(C::*). (Nat → Bool → C) → C
  (normal form)
```

## Command Reference

### Essential Commands
- `:help` - Show help
- `:quit` - Exit
- `:type <term>` - Show term type
- `:kind <type>` - Show type kind
- `:let <name> = <term>` - Bind term
- `:tlet <name> = <type>` - Bind type

### Kind Commands
- `:kind <type>` - Show kind of type
- `:klet <name> = <kind>` - Bind kind (if supported)

### Type-Level Commands
- `:normalize <type>` - Normalize type to normal form
- `:tstep` - Enable type-level step mode
- `:tnostep` - Disable type-level step mode

### Environment Commands
- `:bindings` - Show term bindings
- `:tbindings` - Show type bindings
- `:kbindings` - Show kind bindings (if supported)
- `:reset` - Clear all bindings

### Evaluation Commands
- `:step` - Step through term evaluation
- `:trace` - Show evaluation trace

## Guided Exploration

### Exercise 1: Understanding Kinds (15 minutes)

Explore the kind system:

```
λω> :kind Nat
λω> :kind Bool
λω> :kind Nat -> Bool

λω> :tlet Maybe = /\A::*. forall B::*. B -> (A -> B) -> B
λω> :kind Maybe
λω> :kind Maybe Nat
λω> :kind Maybe Bool

λω> :tlet Either = /\A::*. /\B::*. forall C::*. (A->C)->(B->C)->C
λω> :kind Either
λω> :kind Either Nat
λω> :kind Either Nat Bool
```

**Question**: What pattern do you see in how kinds work?

### Exercise 2: Type Constructors (20 minutes)

Build type constructors:

```
λω> :tlet List = /\A::*. forall B::*. (A->B->B)->B->B
λω> :tlet Maybe = /\A::*. forall B::*. B->(A->B)->B
λω> :tlet Either = /\A::*. /\B::*. forall C::*. (A->C)->(B->C)->C

λω> :kind List
λω> :kind Maybe
λω> :kind Either

λω> List Nat
λω> Maybe Bool
λω> Either Nat Bool
```

**Challenge**: Define a `Triple A B C` type operator.

### Exercise 3: Higher-Kinded Types (25 minutes)

Implement Functor:

```
λω> :tlet Functor = /\F::*->*.
                      forall A::*. forall B::*.
                      (A -> B) -> F A -> F B
λω> :kind Functor

λω> :let mapMaybe = /\A::*. /\B::*. \f:A->B. \m:Maybe A. ...
  (implement map for Maybe)

λω> :let mapList = /\A::*. /\B::*. \f:A->B. \xs:List A. ...
  (implement map for List)
```

**Challenge**: Implement `mapEither`.

### Exercise 4: Type-Level Functions (20 minutes)

Type-level programming:

```
λω> :tlet Apply = /\F::*->*. /\A::*. F A
λω> :kind Apply
λω> Apply List Nat

λω> :tlet Compose = /\F::*->*. /\G::*->*. /\A::*. F (G A)
λω> :kind Compose
λω> Compose Maybe List Nat

λω> :tlet Const = /\A::*. /\B::*. A
λω> :kind Const
λω> Const Nat Bool
```

**Challenge**: Implement `Flip :: (* → * → *) → * → * → *`.

### Exercise 5: Monad Type Class (30 minutes)

Define Monad:

```
λω> :tlet Monad = /\M::*->*.
                    (forall A::*. A -> M A) ->
                    (forall A::*. forall B::*. M A -> (A -> M B) -> M B) ->
                    M
  (Needs return and bind)

λω> :let returnMaybe = /\A::*. \x:A.
                         /\B::*. \n:B. \j:A->B. j x
λω> :let bindMaybe = /\A::*. /\B::*. \m:Maybe A. \f:A->Maybe B.
                       m [Maybe B]
                         (/\C::*. \n:C. \j:B->C. n)  -- Nothing
                         (\a:A. f a)                  -- Just
```

**Challenge**: Implement `return` and `bind` for List.

### Exercise 6: Church-Encoded Data Structures (25 minutes)

Full List implementation:

```
λω> :tlet List = /\A::*. forall B::*. (A->B->B)->B->B

λω> :let nil = /\A::*. /\B::*. \c:A->B->B. \n:B. n
λω> :let cons = /\A::*. \x:A. \xs:List A.
                  /\B::*. \c:A->B->B. \n:B. c x (xs [B] c n)

λω> :let map = /\A::*. /\B::*. \f:A->B. \xs:List A.
                 /\C::*. \c:B->C->C. \n:C.
                 xs [C] (\a:A. \acc:C. c (f a) acc) n

λω> :let filter = /\A::*. \pred:A->Bool. \xs:List A.
                    /\B::*. \c:A->B->B. \n:B.
                    xs [B]
                      (\a:A. \acc:B.
                        pred a [B] (c a acc) acc)
                      n

λω> :let fold = /\A::*. /\B::*. \f:B->A->B. \z:B. \xs:List A.
                  xs [B] (\a:A. \acc:B. f acc a) z
```

**Challenge**: Implement `length` for lists.

## Tips and Tricks

### Tip 1: Kinds are Types of Types
```
Value : Type : Kind
42 : Nat : *
List : (* → *) : (* → *) → ... (infinite regress!)
```

### Tip 2: Kind Annotation Prevents Ambiguity
```
λω> /\F::*->*. ...     ✓ Clear that F is type constructor
λω> /\F. ...           ✗ Ambiguous kind
```

### Tip 3: Type-Level Beta Reduction
```
λω> (/\A::*. List A) Nat
  =β List Nat
```

### Tip 4: Higher-Kinded = More Abstract
```
* = concrete types
* → * = type constructors (List, Maybe)
(* → *) → * = operates on type constructors (Functor, Monad)
```

## Troubleshooting

### Problem: "Kind mismatch"
**Cause**: Type constructor applied incorrectly
**Solution**: Check kinds with `:kind`

### Problem: "Expected kind * → * but got *"
**Cause**: Using proper type where type constructor expected
**Solution**: Use type constructor like List, not List Nat

### Problem: "Cannot apply type of kind *"
**Cause**: Trying to apply a proper type
**Solution**: Only type constructors can be applied

## Syntax Reference

### Kinds
```
*                   -- Kind of proper types
* → *              -- Kind of type constructors
(* → *) → *        -- Kind of higher-kinded operators
κ₁ → κ₂            -- Kind arrow
```

### Type-Level Terms
```
/\A::κ. τ          -- Type-level lambda
τ₁ τ₂              -- Type-level application
forall A::κ. τ     -- Universal quantification with kind
```

### Term-Level (same as System F)
```
/\A::κ. t          -- Term-level type abstraction (with kind)
t [τ]              -- Term-level type application
\x:τ. t            -- Lambda abstraction
t₁ t₂              -- Application
```

## Connection to Real Languages

System F-omega powers:
- **Haskell**: Full support for higher-kinded types
- **Scala**: Higher-kinded types with `F[_]`
- **TypeScript**: Partial support (mapped types)
- **Rust**: Limited (associated types)

## Next Steps

After mastering this REPL:
1. Complete exercises in `exercises/EXERCISES.md`
2. Work through `TUTORIAL.md`
3. Take `QUIZ.md`
4. Review `COMMON_MISTAKES.md`
5. Move to Chapter 7 for dependent types!

## Quick Reference Card

```
# Building
stack build && stack exec system-f-omega-repl

# Kinds
:kind <type>           -- Show kind of type
* = proper type
* → * = type constructor
(* → *) → * = higher-kinded

# Type-Level Lambda
:tlet List = /\A::*. ...    -- Type operator
List Nat                     -- Type application

# Higher-Kinded
:tlet Functor = /\F::*->*. ...   -- Takes type constructor
Functor List                      -- Apply to List
```

Happy kind checking! 🎯
