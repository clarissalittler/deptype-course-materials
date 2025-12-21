# Chapter 10: Linear Types

This chapter introduces **linear types**, a type system that tracks resource usage. Linear types ensure that certain values are used exactly once, enabling safe resource management, memory safety without garbage collection, and protocol verification.

## Overview

Linear types add **multiplicities** to the type system:

- **Linear** (1): Must be used exactly once
- **Unrestricted** (ω): Can be used any number of times (including zero)

This allows compile-time tracking of resources like file handles, network connections, and memory allocations.

## Types

```
τ ::= Bool                    -- Boolean type
    | Nat                     -- Natural number type
    | ()                      -- Unit type
    | τ₁ -(m)-> τ₂            -- Function with multiplicity m
    | τ₁ * τ₂                 -- Pair type (tensor product)
    | !τ                      -- Bang type (makes content unrestricted)
```

### Function Types

- `A -o B` (linear): Function that uses its argument exactly once
- `A -> B` (unrestricted): Function that may use its argument any number of times

### The Bang Type

`!A` represents an unrestricted value of type A. It allows:
- Storing values that will be used multiple times
- Breaking linearity when needed

## Terms

```
t ::= x                       -- Variable
    | λ(x :m τ). t            -- Lambda with multiplicity annotation
    | t₁ t₂                   -- Application
    | (t₁, t₂)                -- Pair
    | let (x, y) = t₁ in t₂   -- Pair elimination
    | !t                      -- Bang introduction
    | let !x = t₁ in t₂       -- Bang elimination
    | true | false            -- Booleans
    | if t₁ then t₂ else t₃   -- Conditional
    | 0 | succ t | pred t     -- Natural numbers
    | ()                      -- Unit
```

## Typing Rules

### Linear Lambda

```
  Γ, x :1 τ₁ ⊢ t : τ₂    (x used exactly once in t)
─────────────────────────────────────────────────────
         Γ ⊢ λ(x :1 τ₁). t : τ₁ -o τ₂
```

### Unrestricted Lambda

```
  Γ, x :ω τ₁ ⊢ t : τ₂    (x used any number of times)
──────────────────────────────────────────────────────
          Γ ⊢ λ(x :ω τ₁). t : τ₁ -> τ₂
```

### Application

```
  Γ ⊢ t₁ : τ₁ -(m)-> τ₂    Δ ⊢ t₂ : τ₁
────────────────────────────────────────
         Γ, Δ ⊢ t₁ t₂ : τ₂
```

Note: Contexts are combined, ensuring each linear variable is used exactly once across both subterms.

### Pairs (Tensor Product)

```
  Γ ⊢ t₁ : τ₁    Δ ⊢ t₂ : τ₂
──────────────────────────────
   Γ, Δ ⊢ (t₁, t₂) : τ₁ * τ₂
```

### Pair Elimination

```
  Γ ⊢ t₁ : τ₁ * τ₂    Δ, x :1 τ₁, y :1 τ₂ ⊢ t₂ : τ
─────────────────────────────────────────────────────
         Γ, Δ ⊢ let (x, y) = t₁ in t₂ : τ
```

### Bang Introduction

```
  Γ ⊢ t : τ    (Γ contains no linear variables)
─────────────────────────────────────────────────
               Γ ⊢ !t : !τ
```

### Bang Elimination

```
  Γ ⊢ t₁ : !τ₁    Δ, x :ω τ₁ ⊢ t₂ : τ₂
────────────────────────────────────────
    Γ, Δ ⊢ let !x = t₁ in t₂ : τ₂
```

## Usage Tracking

The type checker maintains a **usage environment** that tracks how many times each variable is used:

```haskell
data Usage = Unused | UsedOnce | UsedMany

-- For pairs/application: add usages
addUsage :: UsageEnv -> UsageEnv -> UsageEnv

-- For if-then-else: take max (only one branch executes)
combineUsage :: UsageEnv -> UsageEnv -> UsageEnv
```

## Examples

### Linear Identity

```haskell
-- Uses argument exactly once
λx :1 Nat. x  : Nat -o Nat
```

### Duplication Requires Unrestricted

```haskell
-- OK: unrestricted can be used multiple times
λx :ω Nat. (x, x)  : Nat -> Nat * Nat

-- ERROR: cannot use linear variable twice
λx :1 Nat. (x, x)  -- Type error!
```

### Discarding Requires Unrestricted

```haskell
-- OK: unrestricted can be ignored
λx :ω Nat. 0  : Nat -> Nat

-- ERROR: cannot ignore linear variable
λx :1 Nat. 0  -- Type error!
```

### Using Bang for Duplication

```haskell
-- Wrap in bang to make unrestricted
let !x = !0 in (x, x)  : Nat * Nat
```

### Pairs and Linear Elimination

```haskell
-- Both components must be used exactly once
let (x, y) = (0, true) in (y, x)  : Bool * Nat

-- ERROR: y not used
let (x, y) = (0, true) in x  -- Type error!
```

## Real-World Applications

### Rust's Ownership System

Linear types are closely related to Rust's ownership:
- Each value has exactly one owner (linear)
- Borrowing creates references with restrictions
- `Clone` trait is like the bang type

### Session Types

Linear types can encode communication protocols:
```
Send Int (Recv Bool End)
-- Must send an Int, then receive a Bool, then close
```

### File Handle Safety

```haskell
open : FilePath -o Handle
read : Handle -o (String * Handle)
close : Handle -o ()

-- File must be closed exactly once!
let h = open "file.txt" in
let (s, h') = read h in
close h'
```

### Memory Management

```haskell
malloc : Size -o Ptr
free : Ptr -o ()

-- Memory must be freed exactly once
let p = malloc 100 in
... use p ...
free p
```

## Metatheory

### Type Safety

**Theorem (Progress)**: Well-typed closed terms are either values or can step.

**Theorem (Preservation)**: Reduction preserves types and linearity constraints.

### Linearity Properties

**Theorem (Linear Usage)**: In a well-typed term, each linear variable is used exactly once.

**Theorem (Unrestricted Contraction)**: Unrestricted variables can be used any number of times.

## File Structure

```
chapter-10-linear-types/
├── src/
│   ├── Syntax.hs      -- Types with multiplicities
│   ├── TypeCheck.hs   -- Linear type checking with usage tracking
│   ├── Eval.hs        -- Call-by-value evaluation
│   ├── Parser.hs      -- Megaparsec parser
│   └── Pretty.hs      -- Pretty printer
├── app/
│   └── Main.hs        -- REPL
├── test/
│   └── Spec.hs        -- 45 tests
├── exercises/
│   └── EXERCISES.md   -- Exercises
├── package.yaml
├── stack.yaml
└── README.md          -- This file
```

## Building and Testing

```bash
cd chapter-10-linear-types
stack build
stack test   # 45 tests
stack exec linear-repl  # Interactive REPL
```

## REPL Commands

```
linear> :help              -- Show help
linear> :type <expr>       -- Show type of expression
linear> :quit              -- Exit
```

## References

### Primary Sources

1. **Girard, J.-Y.** (1987). "Linear Logic". *Theoretical Computer Science*, 50(1), 1-102.
   - The foundational work on linear logic

2. **Wadler, P.** (1990). "Linear Types Can Change the World!". *IFIP TC 2*.
   - Connecting linear logic to programming

3. **Bernardy, J.-P., Boespflug, M., Newton, R., Peyton Jones, S., & Spiwack, A.** (2017). "Linear Haskell: Practical Linearity in a Higher-Order Polymorphic Language". *POPL*.
   - Linear types in GHC

4. **Walker, D.** (2005). "Substructural Type Systems". In *Advanced Topics in Types and Programming Languages*.
   - Comprehensive overview

### Related Systems

5. **Rust Programming Language** - Ownership and borrowing
6. **Clean** - Uniqueness types
7. **Idris 2** - Quantitative Type Theory

---

**Tests**: 45/45 passing | **Exercises**: 8 problems + challenges
