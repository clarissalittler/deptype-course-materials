# Chapter 19: Bidirectional Type Checking - REPL Guide

## Overview

The Bidirectional Type Checker REPL provides an interactive environment for experimenting with bidirectional typing, understanding the two modes (inference and checking), and seeing how minimal annotations work.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-19-bidirectional-typing
stack build

# Run the REPL
stack exec bidir-repl
```

### Quick Start

```
bidir> true
true ⇒ Bool
Value: true

bidir> \x. x
Cannot infer type for this term
Hint: Use annotation or :check command

bidir> :check \x. x : Bool -> Bool
✓ λx. x ⇐ Bool → Bool
Value: <λx. ...>

bidir> :help
[Shows available commands]
```

## Features

### 1. Type Inference (⇒)

Type a term to infer its type:

```
bidir> true
true ⇒ Bool
Value: true

bidir> \(x : Bool). x
λ(x : Bool). x ⇒ Bool → Bool
Value: <λx. ...>

bidir> (\x. x : Bool -> Bool)
(λx. x : Bool → Bool) ⇒ Bool → Bool
Value: <λx. ...>
```

The REPL shows:
- The inferred type (after `⇒`)
- The resulting value

### 2. Type Checking (⇐)

Use `:check` to verify a term against an expected type:

```
bidir> :check \x. x : Bool -> Bool
✓ λx. x ⇐ Bool → Bool
Value: <λx. ...>

bidir> :check true : Bool
✓ true ⇐ Bool
Value: true

bidir> :check true : Nat
✗ Type mismatch: expected Nat, got Bool
```

### 3. Derivation Trees

See the full typing derivation with `:derivation`:

```
bidir> :derivation (\(x : Bool). x) true

Application:
  ├─ Infer function:
  │  │  Variable x ⇒ Bool in {x:Bool}
  │  └─ λ(x : Bool). x ⇒ Bool → Bool
  ├─ Check argument:
  │  └─ true ⇐ Bool (subsumption)
  └─ Result: Bool
```

This shows:
- Which rules were applied
- Mode switches (⇒ vs ⇐)
- Type propagation

### 4. Understanding Mode Errors

The REPL explains why terms fail:

```
bidir> \x. x
Cannot infer type for this term
Hint: Use annotation (term : Type) or :check command
Reason: Unannotated lambda has no inference rule

bidir> inl true
Cannot infer type for this term
Hint: Injections need expected sum type
Suggestion: Use :check or add annotation
```

### 5. Bindings

Define and reuse named terms:

```
bidir> :let id = \(x : Bool). x
id : Bool → Bool

bidir> :let const = \(x : Bool). \(y : Nat). x
const : Bool → Nat → Bool

bidir> id true
true ⇒ Bool
Value: true

bidir> :bindings
Current bindings:
  id : Bool → Bool
  const : Bool → Nat → Bool
```

### 6. Polymorphism

Experiment with polymorphic types:

```
bidir> :let polyId = (\\x. x : forall a. a -> a)
polyId : ∀α. α → α

bidir> polyId [Bool]
polyId [Bool] ⇒ Bool → Bool

bidir> polyId [Bool] true
(polyId [Bool]) true ⇒ Bool
Value: true

bidir> polyId [Nat] 5
(polyId [Nat]) 5 ⇒ Nat
Value: 5
```

## Core Examples

### Introduction vs Elimination

#### Introduction Forms (Check)

**Unannotated Lambda**:
```
bidir> :check \x. x : Bool -> Bool
✓ λx. x ⇐ Bool → Bool

bidir> :check \x. \y. x : Bool -> Nat -> Bool
✓ λx. λy. x ⇐ Bool → Nat → Bool
```

**Pairs**:
```
bidir> :check (true, false) : Bool × Bool
✓ (true, false) ⇐ Bool × Bool

bidir> :check (true, 5) : Bool × Nat
✓ (true, 5) ⇐ Bool × Nat
```

**Injections**:
```
bidir> :check inl true : Bool + Nat
✓ inl true ⇐ Bool + Nat

bidir> :check inr 5 : Bool + Nat
✓ inr 5 ⇐ Bool + Nat
```

**Type Abstraction**:
```
bidir> :check (\\x. x) : forall a. a -> a
✓ (Λα. λx. x) ⇐ ∀α. α → α
```

#### Elimination Forms (Infer)

**Application**:
```
bidir> (\(f : Bool -> Bool). f) (\(x : Bool). x)
... ⇒ Bool → Bool

bidir> (\(f : Bool -> Bool). f) (\(x : Bool). x) true
... ⇒ Bool
```

**Projections**:
```
bidir> fst ((true, 5) : Bool × Nat)
fst ((true, 5) : Bool × Nat) ⇒ Bool
Value: true

bidir> snd ((true, 5) : Bool × Nat)
snd ((true, 5) : Bool × Nat) ⇒ Nat
Value: 5
```

**Type Application**:
```
bidir> :let polyId = (\\x. x : forall a. a -> a)
bidir> polyId [Bool]
polyId [Bool] ⇒ Bool → Bool
```

### Type Propagation Examples

#### Example 1: Nested Lambdas
```
bidir> :check \f. \x. f x : (Bool -> Nat) -> Bool -> Nat

Trace:
  Outer lambda: f : Bool → Nat
  Inner lambda: x : Bool
  Application: f ⇒ Bool → Nat, x ⇐ Bool
  Result type: Nat

✓ Success!
```

#### Example 2: Pairs with Lambdas
```
bidir> :check (\x. x, \y. y) : (Bool -> Bool) × (Nat -> Nat)

Trace:
  Pair expects: (Bool → Bool) × (Nat → Nat)
  First component: λx. x ⇐ Bool → Bool
    - x : Bool, body needs Bool ✓
  Second component: λy. y ⇐ Nat → Nat
    - y : Nat, body needs Nat ✓

✓ Success!
```

#### Example 3: Nested Pairs
```
bidir> :check (true, (false, 5)) : Bool × (Bool × Nat)

Trace:
  Outer pair: first needs Bool, second needs Bool × Nat
  First: true ⇐ Bool ✓
  Second: (false, 5) ⇐ Bool × Nat
    - false ⇐ Bool ✓
    - 5 ⇐ Nat ✓

✓ Success!
```

### The Annotation Trick

When inference fails, add strategic annotations:

#### Strategy 1: Parameter Annotation
```
bidir> \x. x
Cannot infer ✗

bidir> \(x : Bool). x
λ(x : Bool). x ⇒ Bool → Bool ✓
```

#### Strategy 2: Term Annotation
```
bidir> \x. x
Cannot infer ✗

bidir> (\x. x : Bool -> Bool)
(λx. x : Bool → Bool) ⇒ Bool → Bool ✓
```

#### Strategy 3: Outer Annotation
```
bidir> (\f. \x. f x)
Cannot infer ✗

bidir> ((\f. \x. f x) : (Bool -> Nat) -> Bool -> Nat)
... ⇒ (Bool → Nat) → Bool → Nat ✓
```

#### Strategy 4: Minimal Annotation
```
bidir> \f. \x. f x
Cannot infer ✗

bidir> \(f : Bool -> Nat). \x. f x
λ(f : Bool → Nat). λx. f x ⇒ (Bool → Nat) → Bool → Nat ✓
```

Only annotate `f`, not `x`! The application `f x` lets us infer `x : Bool`.

## Command Reference

### Type Commands

| Command | Description | Example |
|---------|-------------|---------|
| `term` | Infer type of term | `true` |
| `:infer term` | Explicitly infer type | `:infer \(x:Bool). x` |
| `:check term : type` | Check term against type | `:check \x. x : Bool->Bool` |
| `:derivation term` | Show derivation tree | `:derivation true` |

### Binding Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:let name = term` | Define binding | `:let id = \(x:Bool). x` |
| `:bindings` | Show all bindings | `:bindings` |
| `:clear` | Clear all bindings | `:clear` |

### Information Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help message |
| `:examples` | Show example terms |
| `:theory` | Explain bidirectional typing |
| `:quit` | Exit REPL |

## Syntax Reference

### Types

```
A, B ::=
  | Bool                    -- Boolean type
  | Nat                     -- Natural number type
  | Unit                    -- Unit type
  | A → B                   -- Function type (also: A -> B)
  | A × B                   -- Product type (also: A * B)
  | A + B                   -- Sum type
  | ∀α. A                   -- Universal type (also: forall a. A)
  | α                       -- Type variable
```

### Terms

```
e ::=
  | x                       -- Variable
  | true | false            -- Booleans
  | 0 | 1 | 2 | ...         -- Naturals
  | unit                    -- Unit value
  | \x. e                   -- Unannotated lambda
  | \(x : A). e             -- Annotated lambda (also: λ(x:A). e)
  | e₁ e₂                   -- Application
  | (e : A)                 -- Type annotation
  | (e₁, e₂)                -- Pair
  | fst e | snd e           -- Projections
  | inl e | inr e           -- Sum injections
  | case e of inl x -> e₁ | inr y -> e₂  -- Case analysis
  | \\x. e                  -- Type abstraction (also: Λα. e)
  | e [A]                   -- Type application
```

## Advanced Examples

### Polymorphic Identity

```
bidir> :let polyId = (\\x. x : forall a. a -> a)
polyId : ∀α. α → α

bidir> polyId [Bool]
polyId [Bool] ⇒ Bool → Bool

bidir> polyId [Nat]
polyId [Nat] ⇒ Nat → Nat

bidir> polyId [Bool -> Bool]
polyId [Bool → Bool] ⇒ (Bool → Bool) → (Bool → Bool)
```

### Polymorphic Constant

```
bidir> :let polyConst = (\\x. \\y. x : forall a. forall b. a -> b -> a)
polyConst : ∀α. ∀β. α → β → α

bidir> polyConst [Bool] [Nat]
polyConst [Bool] [Nat] ⇒ Bool → Nat → Bool

bidir> polyConst [Bool] [Nat] true 5
... ⇒ Bool
Value: true
```

### Function Composition

```
bidir> :let compose = \(f : Nat -> Bool). \(g : Bool -> Nat). \(x : Bool). f (g x)
compose : (Nat → Bool) → (Bool → Nat) → Bool → Bool

bidir> :derivation compose not id true
[Shows full derivation]
```

### Church Booleans (Polymorphic)

```
bidir> :let churchTrue = (\\t. \\f. t : forall a. a -> a -> a)
churchTrue : ∀α. α → α → α

bidir> :let churchFalse = (\\t. \\f. f : forall a. a -> a -> a)
churchFalse : ∀α. α → α → α

bidir> churchTrue [Bool] true false
... ⇒ Bool
Value: true

bidir> churchFalse [Bool] true false
... ⇒ Bool
Value: false
```

### Case Analysis

```
bidir> case (inl true : Bool + Nat) of inl x -> x | inr y -> false
... ⇒ Bool
Value: true

bidir> case (inr 5 : Bool + Nat) of inl x -> x | inr y -> false
... ⇒ Bool
Value: false
```

## Tips and Tricks

### 1. Understanding Error Messages

When inference fails:
```
bidir> \x. x
Cannot infer type for this term
Hint: Use annotation (term : Type) or :check command
Reason: Unannotated lambda has no inference rule
```

The REPL tells you:
- What went wrong
- How to fix it (annotation or :check)
- Why it failed (no rule applies)

### 2. Using Derivation Mode

To understand what the type checker is doing:
```
bidir> :derivation (\(f : Bool -> Bool). \(x : Bool). f x) not true
```

This shows:
- Which rule was applied at each step
- Mode switches (⇒ vs ⇐)
- Context changes
- Type propagation

### 3. Minimal Annotations

Find the minimal annotation needed:
```
bidir> \f. \g. \x. f (g x)
Cannot infer ✗

Try annotating just the outermost lambda:
bidir> \(f : Nat -> Bool). \g. \x. f (g x)
Cannot infer ✗ (g's type unknown)

Annotate both f and g:
bidir> \(f : Nat -> Bool). \(g : Bool -> Nat). \x. f (g x)
... ⇒ (Nat → Bool) → (Bool → Nat) → Bool → Bool ✓

Or use a term annotation:
bidir> (\f. \g. \x. f (g x) : (Nat->Bool) -> (Bool->Nat) -> Bool -> Bool)
... ⇒ (Nat → Bool) → (Bool → Nat) → Bool → Bool ✓
```

### 4. Exploring Subsumption

Any inferred term can be checked:
```
bidir> true
true ⇒ Bool

bidir> :check true : Bool
✓ true ⇐ Bool (via subsumption)
```

### 5. Type Propagation Experiments

See how types flow inward:
```
bidir> :check (\x. (\y. (x, y))) : Bool -> Nat -> (Bool × Nat)

Types flow:
  - Outer lambda: x : Bool
  - Inner lambda: y : Nat
  - Pair: (Bool × Nat)
```

## Common Patterns

### Pattern 1: Annotate Parameters
```
\(x : A). \(y : B). e
```

### Pattern 2: Annotate Whole Term
```
(term : Type)
```

### Pattern 3: Check Instead of Infer
```
:check term : Type
```

### Pattern 4: Use Let for Readability
```
:let f = \(x : A). e
:let g = \(y : B). f
```

## Exercises

Try these in the REPL to learn bidirectional typing:

### Exercise 1: Identity Variations
```
bidir> :check \x. x : Bool -> Bool
bidir> \(x : Bool). x
bidir> (\x. x : Bool -> Bool)
```

What are the differences? Which can be inferred?

### Exercise 2: Const Function
```
bidir> :check \x. \y. x : Bool -> Nat -> Bool
```

What's the minimal annotation needed?

### Exercise 3: Application
```
bidir> (\(f : Bool -> Bool). f) (\(x : Bool). not x)
```

Can you remove any annotations?

### Exercise 4: Pairs
```
bidir> :check (true, false) : Bool × Bool
bidir> (true, false)
```

Why does one succeed and one fail?

### Exercise 5: Polymorphism
```
bidir> :let id = (\\x. x : forall a. a -> a)
bidir> id [Bool]
bidir> id [Nat]
bidir> id [Bool -> Bool]
```

Experiment with different type arguments.

## Troubleshooting

### Cannot Infer Error

**Problem**: Term has no inference rule.

**Solutions**:
1. Add parameter annotations: `\(x:A). e`
2. Add term annotation: `(term : Type)`
3. Use `:check` instead: `:check term : Type`

### Type Mismatch

**Problem**: Inferred type doesn't match expected type.

**Example**:
```
bidir> :check true : Nat
✗ Type mismatch: expected Nat, got Bool
```

**Solution**: Check your types match what you expect.

### Context Error

**Problem**: Variable not in context.

**Example**:
```
bidir> x
✗ Unbound variable: x
```

**Solution**: Define it with `:let` or ensure it's in scope.

## Further Reading

- [README.md](README.md) - Complete theory
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step walkthrough
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- [COMMON_MISTAKES.md](COMMON_MISTAKES.md) - What to avoid
- Pierce & Turner - "Local Type Inference" (2000)

## Next Steps

After mastering the REPL:
- Complete exercises in `exercises/EXERCISES.md`
- Study the implementation in `src/TypeCheck.hs`
- Add extensions (subtyping, records, etc.)
- Move to dependent types (uses bidirectional typing!)

Have fun exploring bidirectional type checking!
