# Chapter 13: Gradual Typing - REPL User Guide

## Overview

The Gradual Typing REPL provides an interactive environment for experimenting with the dynamic type `?`, consistency checking, cast insertion, and blame tracking.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-13-gradual-typing
stack build

# Run the REPL
stack exec gradual-repl
```

### Quick Start

```
gradual> λx : ?. x
  λx : ?. x

gradual> :type λx : ?. x
  ? -> ?

gradual> :casts (λx : ?. x + 1) 42
  (λx : ?. <? => Nat>^body x + 1) <Nat => ?>^arg 42
```

## Features

### 1. Type Checking with Consistency

The REPL uses **consistency** instead of type equality:

```
gradual> :type λx : ?. x
  ? -> ?

gradual> :type λf : ? -> Nat. λx : ?. f x
  (? -> Nat) -> ? -> Nat

gradual> :type (λx : Nat. x) (42 : ?)
  ERROR: Need cast from ? to Nat
```

### 2. Consistency Checking

Check if two types are consistent:

```
gradual> :consistent Nat ?
  true

gradual> :consistent ? (Nat -> Bool)
  true

gradual> :consistent (Nat -> ?) (? -> Bool)
  true

gradual> :consistent Nat Bool
  false
```

### 3. Cast Insertion (Elaboration)

See the casts inserted by the type checker:

```
gradual> :casts (λx : ?. x + 1) 42
  (λx : ?. <? => Nat>^body x + 1) <Nat => ?>^arg 42

gradual> :casts let f : ? -> ? = (λx : Nat. x) in f true
  let f : ? -> ? = <Nat -> Nat => ? -> ?>^bind (λx : Nat. x) in
    (<? -> ? => ? -> ?>^app f) <Bool => ?>^arg true
```

Casts show:
- Injection: `<Nat => ?>`
- Projection: `<? => Nat>`
- Function casts: `<Nat -> Bool => ? -> ?>`
- Blame labels: `^body`, `^arg`, etc.

### 4. Step-by-Step Evaluation

Trace reduction including cast semantics:

```
gradual> :step
Step mode enabled

gradual> (λx : ?. x) (<Nat => ?> 42)
  (λx : ?. x) (<Nat => ?> 42)
    [Press Enter to step]
→ <? => ?> (<Nat => ?> 42)
    [Press Enter to step]
→ <Nat => ?> 42
  (value)
```

### 5. Blame Tracking

See where casts fail and blame is assigned:

```
gradual> :reduce (<? => Nat> (<Bool => ?> true))
  Reduction:
  (<? => Nat> (<Bool => ?> true))
  → blame^l : Nat

  Blame: Tag mismatch - expected Nat ground, got Bool ground

gradual> :blame
  Last blame: label l, expected Nat, got Bool
```

### 6. Ground Types

Inspect ground types for dynamic values:

```
gradual> :ground Bool
  Bool

gradual> :ground (Nat -> Bool)
  ? -> ?

gradual> :ground ((Nat -> Bool) -> Unit)
  ? -> ?
```

All base types are their own ground type. All functions share ground type `? -> ?`.

## Practical Examples

### Example 1: Dynamic Identity

```
gradual> :let id = λx : ?. x
  id : ? -> ?

gradual> id 42
  42

gradual> id true
  true

gradual> id (λy : Nat. y)
  λy : Nat. y
```

### Example 2: Partial Typing

```
gradual> :let add = λx : Nat. λy : ?. x + y
  add : Nat -> ? -> Nat

gradual> :casts add 5 10
  (λx : Nat. λy : ?. x + (<? => Nat>^body y))
    <Nat => ?>^arg1 5
    <Nat => ?>^arg2 10

gradual> add 5 10
  15
```

The second argument is cast from `?` to `Nat` inside the function.

### Example 3: Runtime Failure

```
gradual> :let addNat = λx : Nat. λy : Nat. x + y
  addNat : Nat -> Nat -> Nat

gradual> :let addDyn : ? -> ? -> ? = addNat
  addDyn : ? -> ? -> ?

gradual> addDyn true 5
  Reduction:
  (<? -> ? -> ?> <Nat -> Nat -> Nat>^bind addNat)
    <Bool => ?>^arg1 true
    <Nat => ?>^arg2 5
  → ... (function cast)
  → blame^l : ?

  Blame: Cast <? => Nat> failed on value tagged with Bool
```

### Example 4: Gradual Migration

```
-- Phase 1: All dynamic
gradual> :let process1 = λconfig : ?. λdata : ?. data
  process1 : ? -> ? -> ?

-- Phase 2: Partially typed
gradual> :let process2 = λconfig : Config. λdata : ?. data
  process2 : Config -> ? -> ?

-- Phase 3: Fully typed
gradual> :let process3 = λconfig : Config. λdata : Data. data
  process3 : Config -> Data -> Data
```

### Example 5: Higher-Order Functions

```
gradual> :let applyDyn = λf : ?. λx : ?. f x
  applyDyn : ? -> ? -> ?

gradual> :casts applyDyn (λy : Nat. succ y) 42
  (λf : ?. λx : ?. (<? => ? -> ?>^app f) (<? => ?>^arg x))
    <Nat -> Nat => ?>^f (λy : Nat. succ y)
    <Nat => ?>^x 42

gradual> applyDyn (λy : Nat. succ y) 42
  43
```

## Command Reference

### Type Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:type <term>` | `:t` | Show type of term |
| `:consistent T S` | `:cons` | Check if T ~ S |
| `:ground T` | `:g` | Show ground type of T |
| `:meet T S` | | Show most precise common type |

### Elaboration Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:casts <term>` | `:c` | Show term with casts inserted |
| `:labels <term>` | `:l` | Show all blame labels |
| `:elaborate <term>` | `:e` | Full elaboration with all details |

### Evaluation Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:reduce <term>` | `:r` | Evaluate term completely |
| `:step` | | Enable step-by-step mode |
| `:nostep` | | Disable step-by-step mode |
| `:trace` | | Show all reduction steps |
| `:notrace` | | Hide reduction steps |
| `:blame` | | Show last blame information |

### Binding Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:let name = term` | | Define a binding |
| `:bindings` | `:b` | Show all bindings |
| `:clear` | | Clear all bindings |

### Information Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:help` | `:h`, `:?` | Show help message |
| `:examples` | `:ex` | Show example terms |
| `:quit` | `:q`, `:exit` | Exit the REPL |

## Advanced Features

### Cast Chains

Observe how casts compose:

```
gradual> :reduce <? => Nat> (<Nat => ?> 42)
  <? => Nat> (<Nat => ?> 42)
  → 42

gradual> :reduce <? => Bool> (<Nat => ?> 42)
  <? => Bool> (<Nat => ?> 42)
  → blame^l : Bool
```

### Function Casts

Function casts are distributed:

```
gradual> :casts <Nat -> Bool => ? -> ?> (λx : Nat. true)
  λx : ?. <Bool => ?>^pos ((λx : Nat. true) (<? => Nat>^neg x))
```

Note:
- Argument cast has **negative** polarity
- Result cast has **positive** polarity

### Blame Polarity

```
gradual> :let f : Nat -> Bool = λx. true
gradual> :let g : ? -> ? = f
gradual> :reduce g "hello"
  ...
  → blame^neg : Nat

  Explanation: The cast <? => Nat> on argument fails.
  This is NEGATIVE blame because we (caller) provided wrong type.
```

### Precision Ordering

```
gradual> :precision ? (Nat -> Bool)
  ? ⊑ Nat -> Bool

gradual> :precision (? -> ?) (Nat -> Bool)
  ? -> ? ⊑ Nat -> Bool

gradual> :precision Nat Bool
  Incomparable (neither is more precise)
```

## Example Library

Build a standard library of gradual functions:

```
# gradual-lib.txt

-- Identity
id : ? -> ?
id = λx : ?. x

-- Const
const : ? -> ? -> ?
const = λx : ?. λy : ?. x

-- Apply
apply : (? -> ?) -> ? -> ?
apply = λf. λx. f x

-- Compose
compose : (? -> ?) -> (? -> ?) -> ? -> ?
compose = λf. λg. λx. f (g x)

-- Safe division (returns Maybe)
safeDivDyn : ? -> ? -> ?
safeDivDyn = λx : ?. λy : ?.
  if (<? => Bool> (isZero y))
  then none
  else some (div (<? => Nat> x) (<? => Nat> y))
```

Load in REPL:
```
gradual> :load gradual-lib.txt
Loaded 5 definitions
```

## Tips and Tricks

### 1. Understanding Cast Insertion

Use `:casts` liberally to see where casts appear:

```
gradual> :casts (λf : ?. f 0) (λx : Nat. x)
```

This reveals the elaboration strategy.

### 2. Debugging Type Errors

If type checking fails, check consistency:

```
gradual> :consistent Nat Bool
  false
```

### 3. Tracing Blame

When you get `blame`, use `:blame` to see details:

```
gradual> :reduce (<? => Nat> (<Bool => ?> true))
  blame^l : Nat

gradual> :blame
  Label: l
  Expected: Nat ground
  Got: Bool ground
  Location: projection from dynamic
```

### 4. Comparing Precision

See how adding types changes behavior:

```
gradual> :let f1 = λx : ?. λy : ?. x
gradual> :let f2 = λx : Nat. λy : ?. x
gradual> :let f3 = λx : Nat. λy : Nat. x

gradual> :precision (? -> ? -> ?) (Nat -> ? -> Nat)
  ? -> ? -> ? ⊑ Nat -> ? -> Nat
```

### 5. Exploring Ground Types

Understand runtime tags:

```
gradual> :ground Nat
  Nat

gradual> :ground (Nat -> Nat)
  ? -> ?

gradual> :ground ((Nat -> Nat) -> Bool)
  ? -> ?
```

All functions collapse to `? -> ?` at runtime!

## Common Patterns

### Pattern 1: Safe Unwrapping

```
gradual> :let unwrap = λx : ?. λdefault : Nat.
           if (<? => Bool> (isDyn x))
           then default
           else (<? => Nat> x)
```

### Pattern 2: Dynamic Dispatch

```
gradual> :let dispatch = λx : ?. λf : ? -> ?. λg : ? -> ?. f (g x)
```

### Pattern 3: Gradual Wrapper

```
gradual> :let wrapStatic = λf : Nat -> Bool. (f : ? -> ?)
  wrapStatic : (Nat -> Bool) -> ? -> ?
```

### Pattern 4: Type Refinement

```
gradual> :let refine = λx : ?.
           if (<? => Bool> (isNat x))
           then (<? => Nat> x)
           else 0
```

## Exercises in the REPL

### Exercise 1: Consistency Practice

Check these in the REPL:
```
gradual> :consistent ? ?
gradual> :consistent (? -> Nat) (Bool -> ?)
gradual> :consistent ((? -> ?) -> ?) ((Nat -> Bool) -> Nat)
```

### Exercise 2: Cast Insertion

Compare these:
```
gradual> :casts (λx : Nat. x) 42
gradual> :casts (λx : ?. x) 42
gradual> :casts (λx : Nat. x) (42 : ?)
```

### Exercise 3: Blame Detection

Predict which will blame:
```
gradual> (<? => Nat> (<Nat => ?> 42))
gradual> (<? => Bool> (<Nat => ?> 42))
gradual> (<? => Nat -> Nat> (<Nat => ?> 42))
```

### Exercise 4: Function Casts

Expand this function cast:
```
gradual> :casts <Nat -> Bool => ? -> ?> (λx : Nat. true)
```

### Exercise 5: Migration Path

Define these three versions and compare types:
```
gradual> :let v1 = λx : ?. λy : ?. x + y
gradual> :let v2 = λx : Nat. λy : ?. x + y
gradual> :let v3 = λx : Nat. λy : Nat. x + y
```

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected '?'`

**Solution**: Ensure `?` is used in type position, not term position.

### Consistency Failures

**Problem**: Types not consistent when you expect them to be.

**Solution**: Remember consistency is NOT transitive. Check each step.

### Blame Confusion

**Problem**: Don't understand which code is blamed.

**Solutions**:
1. Use `:blame` to see details
2. Use `:casts` to see where casts are
3. Trace reduction with `:step`

### Cast Overhead

**Problem**: Too many casts make terms hard to read.

**Solution**: Use `:type` to see final type without casts, `:casts` when debugging.

## Connection to Real Languages

### TypeScript Simulation

```
gradual> -- TypeScript: let x: any = 42;
gradual> :let x : ? = 42

gradual> -- TypeScript: let y: number = x;
gradual> :let y : Nat = x
```

### Python Type Hints Simulation

```
gradual> -- Python: def f(x: Any) -> int: return x + 1
gradual> :let f = λx : ?. (<? => Nat> x) + 1
  f : ? -> Nat
```

### Typed Racket Boundary

```
gradual> -- Typed module importing untyped
gradual> :let untypedFunc : ? -> ? = ...
gradual> :let typedWrapper : Nat -> Bool =
           λx : Nat. <? => Bool> (untypedFunc (<Nat => ?> x))
```

## Performance Considerations

### Cast Overhead

Casts have runtime cost:
```
-- Many casts
(λx : ?. (<? => Nat> x) + (<? => Nat> x))

-- Fewer casts (cache the cast)
(λx : ?. let n = <? => Nat> x in n + n)
```

### Cast Chains

Avoid cast chains:
```
-- Bad: chain of casts
<? => Nat> (<Nat => ?> (<? => Nat> x))

-- Good: optimize to identity
x
```

The REPL automatically optimizes some cast chains.

## Further Reading

- [Chapter 13 README](README.md) - Complete theory
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step guide
- Siek & Taha (2006) - Gradual typing paper
- Wadler & Findler (2009) - Blame tracking

## Next Steps

After mastering the gradual typing REPL:
- Chapter 14: Row Types (structural polymorphism)
- Advanced: Gradual polymorphism, gradual dependent types
- Practice: Migrate real code from dynamic to static

Enjoy exploring gradual typing! 🎉
