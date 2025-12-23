# Chapter 20: Denotational Semantics - REPL Guide

## Overview

The Denotational Semantics REPL provides an interactive environment for exploring denotational semantics, computing denotations, visualizing fixed point iteration, and understanding domain theory.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-20-denotational-semantics
stack build

# Run the REPL
stack exec denotational-repl
```

### Quick Start

```
den> 5
Term: 5
[[·]] = 5 ∈ Nat

den> (\(x : Nat). x + 1) 5
Term: (λ(x : Nat). x + 1) 5
[[·]] = 6 ∈ Nat

den> :help
[Shows available commands]
```

## Features

### 1. Computing Denotations

Type a term to compute its denotation:

```
den> true
Term: true
[[·]] = true ∈ Bool

den> (\(x : Nat). x + 1) 5
Term: (λ(x : Nat). x + 1) 5
[[·]] = 6 ∈ Nat

den> (\(x : Bool). \(y : Bool). x) true false
Term: (λ(x : Bool). λ(y : Bool). x) true false
[[·]] = true ∈ Bool
```

The REPL shows:
- The parsed term
- The denotation `[[·]]`
- The domain it inhabits

### 2. Fixed Point Iteration

Visualize how fixed points are computed via iteration:

```
den> :iterate factorial 5

F = λf. λn. if n=0 then 1 else n * f(n-1)

Iteration 0: F⁰(⊥) = ⊥
  Domain: ⊥ everywhere
  f(0) = ⊥, f(1) = ⊥, f(2) = ⊥, ...

Iteration 1: F¹(⊥) = F(⊥)
  Domain: {0}
  f(0) = 1, f(1) = ⊥, f(2) = ⊥, ...

Iteration 2: F²(⊥) = F(F(⊥))
  Domain: {0, 1}
  f(0) = 1, f(1) = 1, f(2) = ⊥, ...

Iteration 3: F³(⊥) = F(F(F(⊥)))
  Domain: {0, 1, 2}
  f(0) = 1, f(1) = 1, f(2) = 2, f(3) = ⊥, ...

Iteration 4: F⁴(⊥)
  Domain: {0, 1, 2, 3}
  f(0) = 1, f(1) = 1, f(2) = 2, f(3) = 6, f(4) = ⊥, ...

Iteration 5: F⁵(⊥)
  Domain: {0, 1, 2, 3, 4}
  f(0) = 1, f(1) = 1, f(2) = 2, f(3) = 6, f(4) = 24, f(5) = ⊥, ...

Pattern: Fⁿ(⊥) is defined on inputs {0, 1, ..., n-1}
Supremum: fix F = factorial (defined on all naturals)
```

### 3. Built-in Recursive Functions

Explore classic recursive functions:

```
den> :fact 5
Computing factorial(5)...
  [[fact]](5) = 120

den> :fact 0
  [[fact]](0) = 1

den> :fib 10
Computing fibonacci(10)...
  [[fib]](10) = 55

den> :fib 1
  [[fib]](1) = 1
```

### 4. Domain Theory Explanation

Learn about domains interactively:

```
den> :theory

=== Domain Theory ===

A domain (CPO - Complete Partial Order) is:
1. A set D with a partial order ⊑ (approximation)
2. A least element ⊥ (bottom, "undefined")
3. Suprema exist for all directed sets

The approximation ordering ⊑:
  d₁ ⊑ d₂  means "d₁ approximates d₂"
  ⊥ ⊑ d    for all d (⊥ is least)

Flat domains (for base types):
     0   1   2   3   ...
      \  |  /   /
       \ | /   /
        \|/   /
         ⊥

All defined values are incomparable.

Function domains [A → B]:
  f ⊑ g  iff  ∀x. f(x) ⊑ g(x)  (pointwise)
  Least: λx. ⊥ (undefined everywhere)

Continuity:
  A function is continuous if:
  1. Monotone: x ⊑ y ⟹ f(x) ⊑ f(y)
  2. Preserves limits: f(⊔ chain) = ⊔ f(chain)

Fixed points:
  fix f = ⊔ₙ fⁿ(⊥)
  The supremum of the Kleene chain:
    ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ f³(⊥) ⊑ ...
```

### 5. Step-by-Step Denotation

See the full denotation computation:

```
den> :trace (\(x : Nat). x + 1) 5

Step 1: Parse term
  (λ(x : Nat). x + 1) 5

Step 2: Compute [[(λ(x : Nat). x + 1) 5]]{}
  By application rule:
    [[λ(x : Nat). x + 1]]{}([[5]]{})

Step 3: Compute [[λ(x : Nat). x + 1]]{}
  By lambda rule:
    λd. [[x + 1]]{x ↦ d}

Step 4: Compute [[5]]{}
  By constant rule:
    5 ∈ Nat

Step 5: Apply function to argument
  (λd. [[x + 1]]{x ↦ d})(5)
  = [[x + 1]]{x ↦ 5}

Step 6: Compute [[x + 1]]{x ↦ 5}
  By addition rule:
    [[x]]{x ↦ 5} + [[1]]{x ↦ 5}

Step 7: Compute [[x]]{x ↦ 5}
  By variable rule:
    5

Step 8: Compute [[1]]{x ↦ 5}
  By constant rule:
    1

Step 9: Final result
  5 + 1 = 6

Result: [[·]] = 6 ∈ Nat
```

### 6. Bindings

Define and reuse terms:

```
den> :let const5 = \(x : Nat). 5
const5 = λ(x : Nat). 5
[[const5]] = λx. 5

den> const5 100
Term: const5 100
[[·]] = 5 ∈ Nat

den> :bindings
Current bindings:
  const5 : Nat → Nat = λ(x : Nat). 5
```

## Core Examples

### Basic Denotations

#### Constants
```
den> 0
[[·]] = 0 ∈ Nat

den> true
[[·]] = true ∈ Bool

den> false
[[·]] = false ∈ Bool

den> unit
[[·]] = unit ∈ Unit
```

#### Lambda Abstraction
```
den> \(x : Nat). x
Term: λ(x : Nat). x
[[·]] = λx. x ∈ [Nat → Nat]

den> \(x : Bool). \(y : Bool). x
Term: λ(x : Bool). λ(y : Bool). x
[[·]] = λx. λy. x ∈ [Bool → Bool → Bool]
```

#### Application
```
den> (\(x : Nat). x) 5
[[·]] = 5 ∈ Nat

den> (\(x : Nat). x + 1) 5
[[·]] = 6 ∈ Nat

den> (\(f : Nat -> Nat). \(x : Nat). f x) (\(y : Nat). y + 1) 5
[[·]] = 6 ∈ Nat
```

### Fixed Point Examples

#### Factorial

```
den> :iterate factorial 3

Iteration 0: ⊥
Iteration 1: λn. if n=0 then 1 else ⊥
Iteration 2: λn. if n≤1 then ... else ⊥
Iteration 3: λn. if n≤2 then ... else ⊥

den> :fact 5
[[fact]](5) = 120
```

#### Fibonacci

```
den> :iterate fibonacci 4

Iteration 0: ⊥
Iteration 1: λn. if n≤1 then 1 else ⊥
Iteration 2: λn. if n≤1 then 1 else if n=2 then 2 else ⊥
Iteration 3: ...

den> :fib 8
[[fib]](8) = 21
```

#### Sum (Triangular Numbers)

```
den> :iterate sum 4

F = λf. λn. if n=0 then 0 else n + f(n-1)

Iteration 0: ⊥
Iteration 1: λn. if n=0 then 0 else ⊥
Iteration 2: λn. if n≤1 then n else ⊥
Iteration 3: λn. if n≤2 then n*(n+1)/2 else ⊥
```

### Understanding Bottom (⊥)

#### Non-Terminating Terms

```
den> omega
Term: (λx. x x)(λx. x x)
[[·]] = ⊥  (diverges)

den> :let loop = fix (\(x : Unit). x)
loop = fix (λ(x : Unit). x)
[[loop]] = ⊥
```

#### Strict Operations

```
den> omega + 5
Term: ((λx. x x)(λx. x x)) + 5
[[·]] = ⊥  (⊥ + 5 = ⊥, strict)

den> 5 + omega
Term: 5 + ((λx. x x)(λx. x x))
[[·]] = ⊥  (5 + ⊥ = ⊥, strict)
```

#### Non-Strict Functions

```
den> (\(x : Nat). 5) omega
Term: (λ(x : Nat). 5) ((λy. y y)(λy. y y))
[[·]] = 5  (ignores argument!)
```

### Conditionals

```
den> if true then 5 else 10
[[·]] = 5 ∈ Nat

den> if false then omega else 7
[[·]] = 7 ∈ Nat

den> if omega then 5 else 7
[[·]] = ⊥  (condition undefined)
```

## Command Reference

### Computation Commands

| Command | Description | Example |
|---------|-------------|---------|
| `term` | Compute denotation | `5` |
| `:trace term` | Step-by-step computation | `:trace (\x. x) 5` |
| `:iterate F n` | Show n fixed point iterations | `:iterate factorial 5` |

### Built-in Functions

| Command | Description | Example |
|---------|-------------|---------|
| `:fact n` | Compute factorial(n) | `:fact 5` |
| `:fib n` | Compute fibonacci(n) | `:fib 10` |
| `:sum n` | Compute sum(0..n) | `:sum 10` |

### Binding Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:let name = term` | Define binding | `:let id = \x. x` |
| `:bindings` | Show all bindings | `:bindings` |
| `:clear` | Clear bindings | `:clear` |

### Information Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help |
| `:theory` | Explain domain theory |
| `:examples` | Show example terms |
| `:quit` | Exit REPL |

## Syntax Reference

### Types

```
A, B ::=
  | Bool          -- Boolean type
  | Nat           -- Natural number type
  | Unit          -- Unit type
  | A → B         -- Function type (also: A -> B)
```

### Terms

```
e ::=
  | x                      -- Variable
  | true | false           -- Booleans
  | 0 | 1 | 2 | ...        -- Naturals
  | unit                   -- Unit value
  | \(x : A). e            -- Lambda (also: λ(x:A). e)
  | e₁ e₂                  -- Application
  | if e then e₁ else e₂   -- Conditional
  | e₁ + e₂                -- Addition
  | e₁ * e₂                -- Multiplication
  | fix e                  -- Fixed point
```

### Special Terms

```
omega = (λx. x x)(λx. x x)   -- Divergent term
```

## Advanced Examples

### Custom Fixed Points

Define your own recursive functions:

```
den> :let myFact = fix (\(f : Nat -> Nat). \(n : Nat). if n == 0 then 1 else n * f (n - 1))

den> myFact 5
[[myFact 5]] = 120
```

### Mutual Recursion (Encoded)

Even and odd via mutual recursion:

```
den> :let evenOdd = fix (\(p : (Nat -> Bool) × (Nat -> Bool)).
                         ((\n. if n == 0 then true else (snd p) (n - 1)),
                          (\n. if n == 0 then false else (fst p) (n - 1))))

den> (fst evenOdd) 4
[[·]] = true

den> (snd evenOdd) 4
[[·]] = false
```

### Church Numerals

```
den> :let church0 = \(f : Nat -> Nat). \(x : Nat). x
den> :let church1 = \(f : Nat -> Nat). \(x : Nat). f x
den> :let church2 = \(f : Nat -> Nat). \(x : Nat). f (f x)

den> church2 (\(n : Nat). n + 1) 0
[[·]] = 2 ∈ Nat
```

## Tips and Tricks

### 1. Understanding Fixed Point Iteration

Use `:iterate` to see how recursion works:

```
den> :iterate factorial 5

Watch how each iteration adds one more defined input!
Iteration n defines inputs 0, 1, ..., n-1
```

### 2. Exploring Strictness

Test if operations are strict:

```
den> omega + 5
[[·]] = ⊥  (strict in left argument)

den> 5 + omega
[[·]] = ⊥  (strict in right argument)

den> (\(x : Nat). 5) omega
[[·]] = 5  (non-strict - ignores argument)
```

### 3. Comparing with Operational Semantics

See that denotational agrees with operational:

```
Operational: (\x. x + 1) 5  →  5 + 1  →  6
Denotational: [[(\x. x + 1) 5]] = 6

They agree! (Adequacy theorem)
```

### 4. Building Intuition

Start simple and build up:

```
den> 5                              -- constant
den> \(x : Nat). x                  -- identity
den> (\(x : Nat). x) 5              -- application
den> \(x : Nat). x + 1              -- non-trivial function
den> (\(x : Nat). x + 1) 5          -- non-trivial application
den> fix (\(f : ...). ...)          -- recursion
```

### 5. Domain Visualization

Use `:theory` to review domain concepts when confused.

## Common Patterns

### Pattern 1: Simple Application
```
den> (\(x : A). e) v
[[·]] = [[e]]{x ↦ [[v]]}
```

### Pattern 2: Nested Lambdas
```
den> (\(x : A). \(y : B). e) v w
[[·]] = [[e]]{x ↦ [[v]], y ↦ [[w]]}
```

### Pattern 3: Fixed Point
```
den> fix (\(f : A -> B). \(x : A). ...)
[[·]] = ⊔ₙ Fⁿ(⊥)
```

### Pattern 4: Constant Function
```
den> \(x : A). c
[[·]] = λx. [[c]]  (non-strict)
```

## Exercises

Try these in the REPL to learn denotational semantics:

### Exercise 1: Basic Denotations
```
den> 5
den> true
den> \(x : Nat). x
den> (\(x : Nat). x) 5
```

Understand the pattern: constant, lambda, application.

### Exercise 2: Fixed Point Iterations
```
den> :iterate factorial 0
den> :iterate factorial 1
den> :iterate factorial 2
den> :iterate factorial 3
```

See how each iteration adds one more value.

### Exercise 3: Bottom
```
den> omega
den> omega + 5
den> (\(x : Nat). 5) omega
```

Understand strict vs non-strict.

### Exercise 4: Trace
```
den> :trace (\(x : Nat). x + 1) 5
```

See the full denotation computation.

### Exercise 5: Custom Recursive Function
```
den> :let double = fix (\(f : Nat -> Nat). \(n : Nat).
                        if n == 0 then 0 else 2 + f (n - 1))
den> double 5
```

## Troubleshooting

### Parse Error

**Problem**: Syntax error in term.

**Example**:
```
den> \x. x
✗ Parse error: type annotation required
```

**Solution**: Add type annotations:
```
den> \(x : Nat). x
✓ [[·]] = λx. x
```

### Bottom Result

**Problem**: Denotation is ⊥.

**Causes**:
1. Non-terminating term
2. Undefined operation (e.g., division by zero)
3. ⊥ propagated through strict operation

**Example**:
```
den> omega
[[·]] = ⊥  (non-terminating)

den> 5 + omega
[[·]] = ⊥  (strict propagation)
```

### Type Error

**Problem**: Type mismatch.

**Example**:
```
den> if 5 then true else false
✗ Type error: condition must be Bool, got Nat
```

**Solution**: Fix the type:
```
den> if true then 5 else 0
✓ [[·]] = 5
```

## Connecting to Theory

### Adequacy

If a term evaluates to a value, they have the same denotation:
```
e →* v  ⟹  [[e]] = [[v]]
```

Try it:
```
den> (\(x : Nat). x + 1) 5
Operational: (λx. x + 1) 5 → 5 + 1 → 6
Denotational: [[·]] = 6
They agree! ✓
```

### Compositionality

The denotation of a compound term depends only on the denotations of its parts:
```
[[(λx. e) v]] = [[λx. e]]([[v]])
```

### Fixed Point Uniqueness

The least fixed point is unique:
```
fix f = ⊔ₙ fⁿ(⊥)
```

Verify with `:iterate`.

## Further Reading

- [README.md](README.md) - Complete theory
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step walkthrough
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- [COMMON_MISTAKES.md](COMMON_MISTAKES.md) - What to avoid
- Winskel - "The Formal Semantics of Programming Languages"
- Gunter - "Semantics of Programming Languages"

## Next Steps

After mastering the REPL:
- Complete exercises in `exercises/EXERCISES.md`
- Study the implementation in `src/Denotation.hs`
- Explore continuity proofs
- Learn about logical relations
- Study game semantics for full abstraction

Have fun exploring denotational semantics!
