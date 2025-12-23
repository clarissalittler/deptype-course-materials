# Chapter 16: Homotopy Type Theory - REPL User Guide

## Overview

The HoTT REPL provides an interactive environment for experimenting with identity types as paths, the J eliminator, and the fundamental path operations of Homotopy Type Theory.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-16-hott
stack build

# Run the REPL
stack exec hott-repl
```

### Quick Start

```
hott> refl [Nat] 0
  refl [Nat] 0

hott> sym (refl [Nat] 0)
  refl [Nat] 0

hott> :help
  [Shows available commands]
```

## Features

### 1. Identity Types

Create and inspect identity types (path types):

```
hott> :t Id Nat 5 5
Type

hott> :t Id Bool true false
Type

hott> :t refl [Nat] 0
Id Nat 0 0

hott> :t refl [Bool] true
Id Bool true true
```

### 2. Reflexivity

Create trivial paths with refl:

```
hott> refl [Nat] 5
refl [Nat] 5

hott> :def p = refl [Nat] 7
Defined: p

hott> :t p
Id Nat 7 7

hott> refl [Bool] false
refl [Bool] false
```

### 3. Symmetry (Path Inverse)

Reverse path direction:

```
hott> :def p = refl [Nat] 3
hott> sym p
refl [Nat] 3

hott> :t sym p
Id Nat 3 3

# For any path p : Id A a b
# sym p : Id A b a
```

### 4. Transitivity (Path Composition)

Compose paths end-to-end:

```
hott> :def p = refl [Nat] 5
hott> :def q = refl [Nat] 5

hott> trans p q
refl [Nat] 5

hott> :t trans p q
Id Nat 5 5

# trans requires middle points to match
# trans : Id A a b → Id A b c → Id A a c
```

### 5. Action on Paths (ap)

Apply functions to paths:

```
hott> :def f = \x:Nat. succ x
hott> :def p = refl [Nat] 0

hott> ap f p
refl [Nat] (succ 0)

hott> :t ap f p
Id Nat (succ 0) (succ 0)

# ap preserves paths
hott> :def g = \x:Nat. succ (succ x)
hott> ap g (refl [Nat] 3)
refl [Nat] (succ (succ 3))
```

### 6. Transport

Move data along paths:

```
hott> :def P = \x:Bool. Nat
hott> :def p = refl [Bool] true

hott> transport P p (succ 0)
succ 0

hott> :t transport P p (succ 0)
Nat

# transport : (P : A → Type) → Id A a b → P a → P b
```

### 7. The J Eliminator

Path induction - the fundamental principle:

```
hott> :help J
J : (C : (x y : A) → Id A x y → Type) →
    ((x : A) → C x x refl) →
    (a b : A) → (p : Id A a b) →
    C a b p

# To prove C for all paths, prove it for refl

hott> :def motive = \x y p. Id Nat y x
hott> :def base = \x. refl [Nat] x
hott> J motive base 5 5 (refl [Nat] 5)
refl [Nat] 5
```

### 8. Step-by-Step Evaluation

Enable step mode to see path reductions:

```
hott> :step
Step mode enabled

hott> sym (refl [Nat] 5)
  sym (refl [Nat] 5)
    [Press Enter to step]
→ refl [Nat] 5
  (normal form)
```

### 9. Tracing

Show all evaluation steps:

```
hott> :trace
Evaluation trace enabled

hott> trans (refl [Nat] 0) (refl [Nat] 0)
  trans (refl [Nat] 0) (refl [Nat] 0)
  refl [Nat] 0
```

## Path Operations Examples

### Basic Path Construction

```
hott> :def zero-path = refl [Nat] 0
hott> :def true-path = refl [Bool] true
hott> :def unit-path = refl [Unit] unit

hott> :t zero-path
Id Nat 0 0

hott> :t true-path
Id Bool true true
```

### Symmetry Examples

```
hott> :def p = refl [Nat] 42
hott> :def p' = sym p

hott> :t p'
Id Nat 42 42

# sym reverses endpoints
# If p : Id A a b
# Then sym p : Id A b a

# But for refl, source = target, so:
hott> sym (refl [Nat] 5)
refl [Nat] 5
```

### Transitivity Examples

```
hott> :def p = refl [Nat] 7
hott> :def q = refl [Nat] 7
hott> :def r = refl [Nat] 7

# Binary composition
hott> trans p q
refl [Nat] 7

# Associative (propositionally)
hott> trans (trans p q) r
refl [Nat] 7

hott> trans p (trans q r)
refl [Nat] 7
```

### ap Examples

```
hott> :def succ = \x:Nat. succ x
hott> :def double = \x:Nat. add x x
hott> :def not = \x:Bool. if x then false else true

hott> ap succ (refl [Nat] 0)
refl [Nat] (succ 0)

hott> ap double (refl [Nat] 3)
refl [Nat] (add 3 3)

hott> ap not (refl [Bool] true)
refl [Bool] false

# ap composition
hott> :def f = \x:Nat. succ x
hott> :def g = \x:Nat. succ (succ x)
hott> ap f (ap g (refl [Nat] 0))
refl [Nat] (succ (succ (succ 0)))
```

### Transport Examples

```
# Constant family
hott> :def P = \x:Bool. Nat
hott> transport P (refl [Bool] true) 5
5

# Non-constant family (requires dependent types)
hott> :def Q = \x:Nat. if iszero x then Bool else Nat
hott> transport Q (refl [Nat] 0) true
true
```

## Advanced Examples

### Proving Path Properties

#### Left Identity

Prove `trans refl p = p`:

```
hott> :def left-id = \A:\Type. \a b:A. \p:Id A a b.
        J (\x y q. Id (Id A a y) (trans (refl [A] a) q) q)
          (\x. refl [Id A a x] (refl [A] a))
          a b p

# This constructs a path:
# left-id : (A:Type) → (a b:A) → (p:Id A a b) →
#           Id (Id A a b) (trans refl p) p
```

#### Right Identity

Prove `trans p refl = p`:

```
hott> :def right-id = \A:\Type. \a b:A. \p:Id A a b.
        J (\x y q. Id (Id A x y) (trans q (refl [A] y)) q)
          (\x. refl [Id A x x] (refl [A] x))
          a b p
```

#### Symmetry is Involution

Prove `sym (sym p) = p`:

```
hott> :def sym-sym = \A:\Type. \a b:A. \p:Id A a b.
        J (\x y q. Id (Id A x y) (sym (sym q)) q)
          (\x. refl [Id A x x] (refl [A] x))
          a b p
```

### Function Extensionality

Assuming funext axiom:

```
hott> :axiom funext : (A:Type) → (B:Type) →
        (f g:A→B) → ((x:A) → Id B (f x) (g x)) →
        Id (A→B) f g

# Use to prove functions equal
hott> :def f = \x:Nat. add x 0
hott> :def g = \x:Nat. x

# Assume: forall x, add x 0 = x
hott> :axiom add-zero : (x:Nat) → Id Nat (add x 0) x

hott> funext Nat Nat f g add-zero
-- Proves f = g
```

### Groupoid Laws

All groupoid laws as 2-paths:

```
# Left identity
hott> :def left-id-type =
  (A:Type) → (a b:A) → (p:Id A a b) →
  Id (Id A a b) (trans (refl [A] a) p) p

# Right identity
hott> :def right-id-type =
  (A:Type) → (a b:A) → (p:Id A a b) →
  Id (Id A a b) (trans p (refl [A] b)) p

# Inverse law
hott> :def inv-law-type =
  (A:Type) → (a b:A) → (p:Id A a b) →
  Id (Id A a a) (trans p (sym p)) (refl [A] a)

# Associativity
hott> :def assoc-type =
  (A:Type) → (a b c d:A) →
  (p:Id A a b) → (q:Id A b c) → (r:Id A c d) →
  Id (Id A a d) (trans (trans p q) r) (trans p (trans q r))
```

### Higher Paths

Paths between paths (2-paths):

```
# The left identity law is a 2-path
hott> :def p = refl [Nat] 5
hott> :def lhs = trans (refl [Nat] 5) p
hott> :def rhs = p

# left-id proves: lhs = rhs
# This is a path in Id Nat 5 5
# A 2-path!

hott> :t left-id Nat 5 5 p
Id (Id Nat 5 5) (trans (refl [Nat] 5) p) p
```

## Command Reference

### Type Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:t expr` | `:type` | Show type of expression |
| `:def name = expr` | `:d` | Define named term |
| `:axiom name : T` | | Assume term exists |

### Evaluation Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:eval expr` | `:e` | Evaluate expression |
| `:step` | | Enable step-by-step evaluation |
| `:nostep` | | Disable step-by-step |
| `:trace` | | Show all evaluation steps |
| `:notrace` | | Hide evaluation steps |

### Path Commands

| Command | Description |
|---------|-------------|
| `refl [T] a` | Reflexivity path |
| `sym p` | Symmetry (inverse) |
| `trans p q` | Transitivity (composition) |
| `ap f p` | Action on paths |
| `transport P p x` | Transport along path |
| `J C base a b p` | Path induction |

### Information Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:help` | `:h`, `:?` | Show help message |
| `:examples` | `:ex` | Show example terms |
| `:quit` | `:q`, `:exit` | Exit the REPL |

## Path Type Syntax

### Identity Types
```
Id A a b            Type of paths from a to b
```

### Reflexivity
```
refl [A] a          Trivial path at a
```

### Operations
```
sym p               Reverse path
trans p q           Compose paths
ap f p              Apply function to path
transport P p x     Transport data along path
```

### J Eliminator
```
J C base a b p      Path induction
  where:
    C : (x y : A) → Id A x y → Type
    base : (x : A) → C x x refl
```

## Tips and Tricks

### 1. Understanding J

J is the universal path eliminator:

```
To prove: C a b p for all paths p
Strategy: Prove C a a refl
J extends it to all paths!
```

Example - defining sym:
```
Want: Id A b a
Given: p : Id A a b

Motive C = \x y q. Id A y x
Base case: \x. refl [A] x : C x x refl
Result: J C base a b p : C a b p = Id A b a
```

### 2. Path Composition Direction

Careful with endpoint matching:

```
trans : Id A a b → Id A b c → Id A a c
                   ^^^   ^^^
                   must match!

# Visualize
a --p--> b --q--> c
= a --trans p q--> c
```

### 3. Computation Rules

Only refl computes:

```
sym (refl a) ≡ refl a           ✓ Computes
trans (refl a) (refl a) ≡ refl a ✓ Computes

sym p = ???                     ✗ Stuck (if p unknown)
trans p q = ???                 ✗ Stuck (if not both refl)
```

### 4. Higher Paths

Paths between paths:

```
# 1-path
p : Id Nat 5 5

# 2-path
alpha : Id (Id Nat 5 5) p (refl [Nat] 5)

# 3-path
beta : Id (Id (Id Nat 5 5) p (refl [Nat] 5)) alpha refl
```

### 5. Debugging Type Errors

Common issues:

```
# Wrong sym direction
sym p : Id A a b    ✗ Should reverse!
sym p : Id A b a    ✓ Correct

# Trans endpoints don't match
trans (Id A a b) (Id A c d)    ✗ b ≠ c
trans (Id A a b) (Id A b c)    ✓ Correct

# Missing type annotation
refl 5              ✗ What type?
refl [Nat] 5        ✓ Correct
```

## Common Patterns

### Pattern 1: Defining Path Operations

Use J with appropriate motive:

```
operation = \p. J motive base a b p
  where motive and base chosen to give desired type
```

### Pattern 2: Proving Path Equalities

All equalities are paths:

```
# To prove: f p = g p for paths p
# Use J to reduce to: f refl = g refl
# Then compute
```

### Pattern 3: Transport Pattern

```
transport P p x
  where:
    P : A → Type    (family over A)
    p : Id A a b    (path in base)
    x : P a         (element in fiber at a)
  gives: P b        (element in fiber at b)
```

## Practice Exercises

### Exercise 1: Basic Paths

Create paths and check types:

```
hott> :def p1 = refl [Bool] true
hott> :def p2 = refl [Nat] 42
hott> :def p3 = refl [Unit] unit

hott> :t p1
hott> :t p2
hott> :t p3
```

### Exercise 2: Symmetry Practice

```
hott> :def p = refl [Nat] 7
hott> :def p' = sym p
hott> :def p'' = sym p'

# What is p''?
hott> p''
```

### Exercise 3: Composition

```
hott> :def p = refl [Nat] 3
hott> :def q = refl [Nat] 3
hott> :def r = refl [Nat] 3

hott> trans p (trans q r)
hott> trans (trans p q) r

# Are they equal?
```

### Exercise 4: ap Practice

```
hott> :def f = \x:Nat. add x x
hott> :def g = \x:Nat. mult (succ (succ 0)) x

hott> ap f (refl [Nat] 5)
hott> ap g (refl [Nat] 5)

# Are the results equal?
```

### Exercise 5: Prove Left Identity

```
# Prove: trans refl p = p
hott> :def left-id-proof = \A:\Type. \a b:A. \p:Id A a b.
        J (\x y q. Id (Id A a y) (trans (refl [A] a) q) q)
          (\x. refl [Id A a x] (trans (refl [A] a) (refl [A] a)))
          a b p

hott> :t left-id-proof
```

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected 'Id'`

**Solution**: Ensure proper syntax:
```
Id A a b          ✓ Correct
Id(A,a,b)         ✗ Wrong
```

### Type Errors

**Error**: `Cannot unify Id A a b with Id A b a`

**Solution**: Use sym to reverse path direction:
```
p : Id A a b
sym p : Id A b a
```

### J Doesn't Compute

**Problem**: J stays stuck.

**Solution**: J only computes on refl. If path is unknown, it won't reduce.

### Endpoint Mismatch

**Error**: `Cannot compose paths: endpoints don't match`

**Solution**: Check middle points:
```
trans : Id A a b → Id A b c → Id A a c
                   ^^^ must match ^^^
```

## Further Reading

- [Chapter 16 README](README.md) - Complete theory
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step guide
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- The HoTT Book - Comprehensive reference

## Next Steps

After mastering the HoTT REPL:
- Study the HoTT Book for full theory
- Explore cubical type theory
- Learn Agda with --cubical flag
- Investigate higher inductive types

Have fun exploring the geometric view of types!
