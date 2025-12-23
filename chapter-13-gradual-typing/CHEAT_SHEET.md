# Chapter 13: Gradual Typing - Cheat Sheet

## Core Concept

**Gradual typing** bridges static and dynamic typing, allowing `?` (dynamic type) to coexist with concrete types through runtime checks.

## Type Syntax

```
T ::= Bool | Nat | Unit      Base types
    | T₁ -> T₂               Function type
    | ?                      Dynamic type (unknown)
```

## Term Syntax

```
t ::= x | λx : T. t | t₁ t₂   Core lambda calculus
    | <T₁ => T₂>^l t          Cast with blame label l
    | t : T                   Type ascription
    | blame^l : T             Runtime type error
```

## Consistency Relation (~)

The **consistency relation** replaces type equality:

```
────────              ────────
? ~ T                 T ~ ?

────────────────
T ~ T   (reflexive for base types)

T₁ ~ S₁    T₂ ~ S₂
─────────────────────
T₁ -> T₂ ~ S₁ -> S₂
```

### Key Properties

- **Reflexive**: `T ~ T`
- **Symmetric**: `T ~ S` implies `S ~ T`
- **NOT Transitive**: `Nat ~ ?` and `? ~ Bool` but `Nat ≁ Bool`

### Examples

```
Nat ~ ?                    ✓
? ~ Bool                   ✓
Nat -> Bool ~ ? -> ?       ✓
(Nat -> ?) ~ (? -> Bool)   ✓
Nat ~ Bool                 ✗
```

## Cast Semantics

### Identity Cast
```
<T => T> v = v
```

### Injection (into dynamic)
```
<Bool => ?> true         Tagged with Bool
<Nat => ?> 42            Tagged with Nat
<Nat->Bool => ?> f       Tagged with ? -> ? (ground)
```

### Projection (from dynamic)
```
<? => Bool> (<Bool => ?> true)    →  true        (success)
<? => Nat> (<Bool => ?> true)     →  blame^l     (tag mismatch)
```

### Function Casts (distribute)
```
<T₁->T₂ => S₁->S₂>^l f = λx. <T₂ => S₂>^l (f (<S₁ => T₁>^l̄ x))
```

Note: Argument cast uses **opposite blame** (negative label).

## Ground Types

Ground types are runtime tags for dynamic values:

- **Base types**: `Bool`, `Nat`, `Unit` (self-ground)
- **Functions**: `? -> ?` (the function ground type)

### Why Ground Types?

Projecting from `?` to specific type goes through ground:

```
<? => Nat -> Bool> v
```
Actually means:
```
<? => ? -> ?> v               Check it's a function
<? -> ? => Nat -> Bool> v     Then cast function type
```

## Blame Tracking

### What is Blame?

When a cast fails, **blame** identifies the responsible code:

```
(<Bool => Nat>^myLabel true)  →  blame^myLabel : Nat
```

### Positive vs Negative Blame

**Positive blame** (l): Value provided was wrong
**Negative blame** (l̄): Function misused its input

```
f : (Nat -> Bool) -> Nat
g : ?
f g  -- If g returns Nat instead of Bool, g gets blamed
```

### Blame Theorem (Wadler & Findler)

> **Well-typed programs can't be blamed.**

If code is fully statically typed (no `?`), it will never be the source of blame.

## Type Checking Rules

### Application (with consistency)
```
   Γ ⊢ t₁ : T₁ -> T₂    Γ ⊢ t₂ : S    T₁ ~ S
  ─────────────────────────────────────────────
                Γ ⊢ t₁ t₂ : T₂
```

Note: Uses **consistency** (~), not equality!

### Cast Typing
```
   Γ ⊢ t : T₁    T₁ ~ T₂
  ────────────────────────
   Γ ⊢ <T₁ => T₂>^l t : T₂
```

### Blame Typing
```
  ────────────────────
   Γ ⊢ blame^l : T
```

Blame can have any type (computation doesn't continue).

## Gradual Guarantee

### Type Precision

The precision order `⊑`:

```
? ⊑ T                  (dynamic is least precise)
T₁ ⊑ S₁    T₂ ⊑ S₂
──────────────────
T₁ -> T₂ ⊑ S₁ -> S₂
```

### Static Gradual Guarantee

Making types **more precise** preserves typeability:
```
If Γ ⊢ t : T, and T ⊑ T', then Γ' ⊢ t : T' (where Γ ⊑ Γ')
```

### Dynamic Gradual Guarantee

Making types **more precise** doesn't change behavior (up to blame):
```
If t ⇓ v with types T, then t ⇓ v or t ⇓ blame with types T' ⊒ T
```

## Common Patterns

### Gradual Migration

```
-- Phase 1: All dynamic
λx : ?. λy : ?. x + y         Type: ? -> ? -> ?

-- Phase 2: Partial types
λx : Nat. λy : ?. x + y       Type: Nat -> ? -> Nat

-- Phase 3: Fully typed
λx : Nat. λy : Nat. x + y     Type: Nat -> Nat -> Nat
```

### Dynamic Identity

```
λx : ?. x                     Type: ? -> ?
```

Works with ANY argument type.

### Mixed Typing

```
λf : ? -> Nat. λx : ?. f x    Type: (? -> Nat) -> ? -> Nat
```

Takes dynamic function that returns `Nat`, applies to dynamic argument.

### FFI Boundary

```
-- Call external dynamic library
let externalFunc : ? -> ? = ...
let result = externalFunc 42     -- Type: ?
let typed : Nat = result         -- Runtime check here
```

## Cast Insertion Examples

### Example 1: Simple Cast

Source:
```
(λx : ?. succ x) true
```

After cast insertion:
```
(λx : ?. succ (<? => Nat>^body x)) (<Bool => ?>^arg true)
```

### Example 2: Function Cast

Source:
```
(λf : ?. f 0) (λx : Nat. x)
```

After cast insertion:
```
(λf : ?. (<? => Nat -> ?>^app f) 0)
  (<Nat -> Nat => ?>^arg (λx : Nat. x))
```

### Example 3: Nested Casts

Source:
```
let f : Nat -> Nat = λx. x in
let g : ? -> ? = f in
g true
```

After elaboration:
```
let g = <Nat->Nat => ?>^bind f in
(<? => ? -> ?>^use g) (<Bool => ?>^arg true)
```

This fails at the inner cast `<? => Nat>` when applying original `f` to `true`.

## Debugging Tips

### 1. Check Consistency

Are the types consistent?
```
Nat ~ ?        ✓
? ~ Bool       ✓
Nat ~ Bool     ✗
```

### 2. Trace Cast Insertion

Where are casts inserted?
- At application sites when argument type differs
- When assigning to typed variable
- At boundaries between typed/dynamic code

### 3. Follow Blame Labels

When you see `blame^l`:
1. Find label `l` in source
2. Check what cast was there
3. Determine which side provided wrong type

### 4. Understand Ground Types

Remember:
- Base types are their own ground types
- All function types share ground type `? -> ?`

## Connection to Real Languages

| Language | Dynamic Type | Notes |
|----------|-------------|-------|
| **TypeScript** | `any` | Opt-out of type checking |
| **Python** | `Any` | Type hint for dynamic values |
| **Typed Racket** | Full contracts | Explicit typed/untyped boundaries |
| **Flow** | `any` | JavaScript gradual typing |
| **Hack** | `mixed` | PHP with gradual types |
| **Dart** | `dynamic` | Gradually typed Dart |

## Common Mistakes

### Mistake 1: Assuming Transitivity

```
Nat ~ ?     ✓
? ~ Bool    ✓
Nat ~ Bool  ✗  -- Wrong! Consistency is NOT transitive
```

### Mistake 2: Forgetting Blame Direction

```
f : (Nat -> Bool) -> Nat
g : ?
f g  -- If g is wrong, g gets blamed, NOT f
```

### Mistake 3: Confusing Cast Direction

```
<Bool => ?>     -- Inject Bool into ?
<? => Bool>     -- Project ? to Bool (may fail!)
```

### Mistake 4: Ignoring Ground Types

```
<? => Nat -> Bool> v
```
Isn't atomic! Goes through `? -> ?` ground type.

## Quick Reference

### Type Checking
```typescript
// TypeScript example
let x: any = 42;           // any ~ number
let y: number = x;         // Implicit cast
console.log(y + 1);        // 43
```

### Runtime Errors
```typescript
let x: any = "hello";
let y: number = x;         // Runtime cast succeeds (no check!)
console.log(y + 1);        // "hello1" (bug!)
```

Note: TypeScript's `any` is **unsound** (doesn't insert real casts).

### Proper Gradual Typing
```
-- In proper gradual typing:
let x : ? = "hello"
let y : Nat = x            -- Cast fails with blame!
```

## Further Reading

### Foundational Papers

- **Siek & Taha (2006)**: "Gradual Typing for Functional Languages"
  - Introduces consistency relation and gradual typing

- **Wadler & Findler (2009)**: "Well-Typed Programs Can't Be Blamed"
  - Blame tracking and blame theorem

- **Siek et al. (2015)**: "Refined Criteria for Gradual Typing"
  - Formal gradual guarantee properties

- **Garcia et al. (2016)**: "Abstracting Gradual Typing"
  - Systematic derivation of gradual type systems

## Next Steps

After mastering gradual typing:
- **Gradual polymorphism**: Extend to parametric types
- **Gradual dependent types**: Combine with dependent typing
- **Space-efficient casts**: Optimize cast representation
- **Blame tracking**: Advanced blame calculus
