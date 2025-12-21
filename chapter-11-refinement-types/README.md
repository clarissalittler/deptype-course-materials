# Chapter 11: Refinement Types

## Overview

This chapter introduces **refinement types**, which extend simple types with logical predicates that constrain values. Refinement types bridge the gap between simple type systems and full dependent types, offering a practical way to encode rich invariants.

## Core Concepts

### What Are Refinement Types?

A refinement type `{x: T | φ(x)}` describes values of type `T` that satisfy predicate `φ`. For example:
- `{x: Nat | x > 0}` - positive natural numbers
- `{x: Nat | x < 10}` - naturals less than 10
- `{x: Bool | x == true}` - the singleton type containing only `true`

### Key Ideas

1. **Types as Sets of Values**: A refinement type carves out a subset of the base type
2. **Predicate Logic**: Refinements are logical formulas over program values
3. **Subtyping via Implication**: `{x: T | φ}` is a subtype of `{x: T | ψ}` when `φ(x) ⟹ ψ(x)`
4. **Path Sensitivity**: Type checking can track conditions from branches

## Syntax

### Types

```
T ::= Bool                    -- Boolean type
    | Nat                     -- Natural number type
    | Unit                    -- Unit type
    | {x: T | φ}              -- Refinement type
    | (x: T₁) -> T₂           -- Dependent function type
```

### Predicates

```
φ ::= true | false            -- Constants
    | x                       -- Boolean variable
    | !φ                      -- Negation
    | φ₁ && φ₂                -- Conjunction
    | φ₁ || φ₂                -- Disjunction
    | φ₁ => φ₂                -- Implication
    | a₁ op a₂                -- Comparison

a ::= x                       -- Variable
    | n                       -- Literal
    | a₁ + a₂                 -- Addition
    | a₁ - a₂                 -- Subtraction
    | n * a                   -- Scalar multiplication

op ::= == | != | < | <= | > | >=
```

### Terms

```
t ::= x                       -- Variable
    | λx : T. t               -- Lambda abstraction
    | t₁ t₂                   -- Application
    | true | false            -- Booleans
    | if t₁ then t₂ else t₃   -- Conditional
    | 0 | succ t | pred t     -- Natural numbers
    | iszero t                -- Zero test
    | t₁ + t₂ | t₁ - t₂       -- Arithmetic
    | ()                      -- Unit
    | let x = t₁ in t₂        -- Let binding
    | t : T                   -- Type ascription
```

## Type System

### Subtyping Rules

The key rule for refinement subtyping:

```
   Γ ⊢ T₁ <: T₂    ∀x. φ(x) ⟹ ψ(x)
  ──────────────────────────────────── (S-Refine)
      Γ ⊢ {x: T₁ | φ} <: {x: T₂ | ψ}
```

This says: a stronger refinement (more specific) is a subtype of a weaker one.

### Path Sensitivity

When type checking branches, we track conditions:

```
   Γ, φ ⊢ t₂ : T₂    Γ, ¬φ ⊢ t₃ : T₃
  ────────────────────────────────────
    Γ ⊢ if t₁ then t₂ else t₃ : T₂ ⊔ T₃
```

This allows type checking code like:
```
λx : Nat. if iszero x then 0 else pred x
```
where in the else branch, we know `x > 0`.

### Dependent Function Types

Function types can mention the argument in the result type:

```
div : (n: Nat, {d: Nat | d > 0}) -> Nat
```

The result type can depend on the argument value.

## Examples

### Positive Numbers

```
-- Type for positive naturals
type Pos = {x: Nat | x > 0}

-- Safe predecessor (only for positive numbers)
safePred : Pos -> Nat
safePred = λn : Pos. pred n
```

### Bounded Arrays

```
-- Array with length information
type Array n a = {arr: [a] | length arr == n}

-- Safe indexing (statically prevents out-of-bounds)
get : (a: Array n a, {i: Nat | i < n}) -> a
```

### Non-Null References

```
-- Refined nullable type
type NonNull a = {x: Maybe a | x != Nothing}

-- Safe extraction
fromJust : NonNull a -> a
```

## Predicate Validity

Checking refinement subtyping requires proving predicate implications. Our implementation uses:

1. **Ground Evaluation**: For predicates without variables, evaluate directly
2. **Syntactic Rules**: Handle simple cases like `p ⟹ p`
3. **Conservative Approximation**: When unsure, be conservative

A production system would integrate an SMT solver (like Z3) for complete reasoning.

## Implementation Highlights

### TypeCheck.hs

Key functions:
- `isSubtype`: Check subtyping, including predicate implication
- `infer`: Type inference with path sensitivity
- `checkType`: Check a term against a type
- `isValid`, `implies`: Predicate validity checking

### Path Conditions

```haskell
data Context = Context
  { ctxTypes :: Map Var Type    -- Variable types
  , ctxPath  :: [Pred]          -- Accumulated path conditions
  }
```

When entering a branch, we add the condition to `ctxPath`.

## Running the REPL

```bash
stack build
stack exec refinement-repl
```

Example session:
```
refinement> :type λx : {n : Nat | n > 0}. x
{n : Nat | n > 0} -> {n : Nat | n > 0}

refinement> :check 5 > 0
Valid (always true)

refinement> :eval let x = 3 in x + x
6
```

## Exercises

See `exercises/EXERCISES.md` for:
- Basic refinement type understanding
- Subtyping relationships
- Path sensitivity exercises
- Implementation challenges (SMT integration, liquid types)

## Key Theorems

1. **Soundness**: If `Γ ⊢ t : T` and `t ⟶* v`, then `v` satisfies the refinement of `T`
2. **Decidability**: With restricted predicate language (linear arithmetic), subtyping is decidable
3. **Subsumption**: If `Γ ⊢ t : T₁` and `T₁ <: T₂`, then `Γ ⊢ t : T₂`

## Connections

### To Prior Chapters
- **Simple Types (Ch 1-2)**: Refinements extend simple types with predicates
- **Subtyping (Ch 9)**: Refinement subtyping via predicate implication

### To Later Topics
- **Full Dependent Types**: Refinement types are a restricted form
- **Liquid Types**: Automated refinement type inference
- **Verification**: Connection to Floyd-Hoare logic

## Limitations

1. **Incompleteness**: Our simple validity checker can't prove all valid implications
2. **Undecidability**: Full arithmetic makes validity undecidable
3. **Annotation Burden**: Users must provide refinement annotations

## References

- Rondon, Kawaguchi, Jhala, "Liquid Types" (PLDI 2008)
- Vazou et al., "Refinement Types for Haskell" (ICFP 2014)
- Xi, Pfenning, "Dependent Types in Practical Programming" (POPL 1999)
- Knowles, Flanagan, "Hybrid Type Checking" (POPL 2006)
- Freeman, Pfenning, "Refinement Types for ML" (PLDI 1991)

## Project Structure

```
chapter-11-refinement-types/
├── src/
│   ├── Syntax.hs      -- Types, predicates, terms
│   ├── TypeCheck.hs   -- Type checker with refinements
│   ├── Eval.hs        -- Evaluator
│   ├── Parser.hs      -- Parser for syntax
│   └── Pretty.hs      -- Pretty printer
├── app/
│   └── Main.hs        -- REPL
├── test/
│   └── Spec.hs        -- Test suite (82 tests)
├── exercises/
│   └── EXERCISES.md   -- Practice exercises
├── package.yaml       -- Package configuration
├── stack.yaml         -- Stack configuration
└── README.md          -- This file
```
