# Chapter 10: Linear Types - Cheat Sheet

## Core Concept

**Linear Types**: Track resource usage at compile time. Linear values must be used **exactly once** - no duplication, no discarding.

```
Linear (1):       Used exactly once
Unrestricted (ω): Used any number of times (0, 1, 2, ...)
```

## Types

```
τ ::= Bool                    -- Boolean type
    | Nat                     -- Natural numbers
    | ()                      -- Unit type
    | τ₁ -(m)-> τ₂            -- Function with multiplicity m
    | τ₁ * τ₂                 -- Pair (tensor product)
    | !τ                      -- Bang type (unrestricted)

m ::= 1 | ω                   -- Multiplicities
```

### Function Types

```
A -o B    Linear function (uses argument exactly once)
A -> B    Unrestricted function (uses argument any number of times)

Notation: A -(1)-> B = A -o B
          A -(ω)-> B = A -> B
```

### The Bang Type

```
!A        Unrestricted value of type A
```

## Typing Rules Quick Reference

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

### Application (Context Splitting)

```
  Γ ⊢ t₁ : τ₁ -(m)-> τ₂    Δ ⊢ t₂ : τ₁
────────────────────────────────────────
         Γ, Δ ⊢ t₁ t₂ : τ₂
```

**Key**: Contexts are split - each linear variable used in exactly one subterm.

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
  Γ ⊢ t : τ    (Γ contains only unrestricted variables)
─────────────────────────────────────────────────────
               Γ ⊢ !t : !τ
```

### Bang Elimination

```
  Γ ⊢ t₁ : !τ₁    Δ, x :ω τ₁ ⊢ t₂ : τ₂
────────────────────────────────────────
    Γ, Δ ⊢ let !x = t₁ in t₂ : τ₂
```

## Usage Tracking

```haskell
data Usage = Unused | UsedOnce | UsedMany

-- For pairs/application:
addUsage :: Usage -> Usage -> Usage
addUsage Unused     u         = u
addUsage u          Unused    = u
addUsage UsedOnce   UsedOnce  = UsedMany
addUsage _          _         = UsedMany

-- For conditionals (only one branch executes):
combineUsage :: Usage -> Usage -> Usage
combineUsage = max  -- Take the maximum usage
```

## Key Rules

### Linear Variables

```
✓ λ(x :1 Nat). x              x used once
✗ λ(x :1 Nat). (x, x)         x used twice
✗ λ(x :1 Nat). 0              x not used
```

### Unrestricted Variables

```
✓ λ(x :ω Nat). x              x used once
✓ λ(x :ω Nat). (x, x)         x used twice
✓ λ(x :ω Nat). 0              x not used
✓ λ(x :ω Nat). (x, (x, x))    x used three times
```

### Context Splitting Examples

```
λ(x :1 Nat). λ(y :1 Nat). (x, y)    ✓ x left, y right
λ(x :1 Nat). λ(y :1 Nat). (x, x)    ✗ x used twice, y unused
λ(x :1 Nat). (x, x)                 ✗ x can't go to both sides
```

### Bang Type Usage

```
✓ !5                          Constant, no linear vars
✓ λ(x :ω Nat). !x             x is unrestricted
✗ λ(x :1 Nat). !x             Can't bang linear variable

✓ let !x = !5 in (x, x)       Unwrap to unrestricted
✗ let !x = 5 in (x, x)        5 has type Nat, not !Nat
```

## Common Patterns

### Linear Identity

```haskell
id : A -o A
id = λ(x :1 A). x
```

### Linear Composition

```haskell
compose : (B -o C) -o (A -o B) -o A -o C
compose = λ(g :1 B -o C). λ(f :1 A -o B). λ(x :1 A). g (f x)
```

### Pair Swap

```haskell
swap : (A * B) -o (B * A)
swap = λ(p :1 (A * B)). let (x, y) = p in (y, x)
```

### Duplication with Bang

```haskell
dup : !A -o (A * A)
dup = λ(b :1 !A). let !x = b in (x, x)
```

### Discard with Unrestricted

```haskell
const : A -> B -o A
const = λ(x :ω A). λ(y :1 B). x
```

## Linear vs Unrestricted Decision Tree

**When to use Linear (1)**:
- Resources (files, memory, connections)
- Protocols (must follow steps)
- Capabilities (use once tokens)
- Values that must be consumed

**When to use Unrestricted (ω)**:
- Pure data (numbers, booleans)
- Shared references
- Functions used multiple times
- Values that can be copied

## Resource Management Patterns

### File Handling

```haskell
open  : Path -o Handle
read  : Handle -o (String * Handle)
write : (Handle * String) -o Handle
close : Handle -o ()

-- Usage:
let h = open "file.txt" in
let (data, h') = read h in
let h'' = write (h', "new data") in
close h''
```

Handle is threaded through - can't forget to close!

### Memory Management

```haskell
malloc : Size -o Ptr
use    : (Ptr * (A -o B)) -o (Ptr * B)
free   : Ptr -o ()

let p = malloc 100 in
let (p', result) = use (p, computation) in
free p'
```

### Transaction Pattern

```haskell
begin   : () -o Transaction
execute : (Transaction * Command) -o Transaction
commit  : Transaction -o ()
rollback: Transaction -o ()

let tx = begin () in
let tx' = execute (tx, cmd1) in
let tx'' = execute (tx', cmd2) in
commit tx''
```

## Bang Type Patterns

### Making Linear Values Unrestricted

```haskell
-- Can't use linear value multiple times:
λ(x :1 Nat). (x, x)    ✗

-- Solution 1: Make parameter unrestricted
λ(x :ω Nat). (x, x)    ✓

-- Solution 2: Use bang
λ(b :1 !Nat). let !x = b in (x, x)    ✓
```

### Storing Linear Values

```haskell
-- Can't store linear value directly in pair:
λ(x :1 Nat). (x, x)    ✗

-- But can store banged values:
λ(x :ω Nat). (!x, !x)  ✓
```

## Multiplicity Comparison

| Feature | Linear (1) | Unrestricted (ω) |
|---------|-----------|------------------|
| Uses | Exactly once | Any (0, 1, 2, ...) |
| Discard | No | Yes |
| Duplicate | No | Yes |
| Example | File handle | Number |
| Type | `A -o B` | `A -> B` |

## Context Combination Rules

### Addition (for pairs, application)

```
Γ, Δ: Each linear variable appears in exactly one context
Unrestricted variables can appear in both
```

### Maximum (for conditionals)

```
Only one branch executes, so take max usage
If branch: x used once
Else branch: x not used
Result: x used at most once
```

## Quick Decision Tree

**To type check `λ(x :m τ). t`:**

1. Type check `t` with `x :m τ` in context
2. Track usage of `x` in `t`
3. If `m = 1` (linear):
   - Check usage is exactly `UsedOnce`
4. If `m = ω` (unrestricted):
   - Any usage is fine

**To type check `(t₁, t₂)`:**

1. Type check `t₁` with context `Γ`
2. Type check `t₂` with context `Δ`
3. Check `Γ` and `Δ` are disjoint (for linear vars)
4. Combine contexts: `Γ, Δ`

**To type check `let (x, y) = t₁ in t₂`:**

1. Type check `t₁ : A * B`
2. Type check `t₂` with `x :1 A, y :1 B`
3. Check `x` and `y` each used exactly once in `t₂`

## Remember

### ✓ Do
- Use linear for resources (files, memory)
- Thread linear values through computations
- Use bang to make values unrestricted when needed
- Split contexts for pairs and applications
- Use unrestricted for pure data

### ✗ Avoid
- Trying to duplicate linear variables
- Trying to discard linear variables
- Banging linear variables directly
- Using linear variables in multiple subterms
- Forgetting to use all pair components

## Examples

### Example 1: Valid Linear Usage

```haskell
λ(x :1 Nat). λ(y :1 Nat). (y, x)    ✓
-- x used once (in pair, right)
-- y used once (in pair, left)
```

### Example 2: Invalid Duplication

```haskell
λ(x :1 Nat). (x, x)    ✗
-- x used twice
```

### Example 3: Context Splitting

```haskell
λ(x :1 Nat). λ(y :1 Nat). λ(z :1 Nat). ((x, y), z)    ✓
-- Inner pair: x left, y right
-- Outer pair: result of inner left, z right
```

### Example 4: Bang Introduction

```haskell
λ(x :ω Nat). λ(y :ω Bool). !(x, y)    ✓
-- Both x and y are unrestricted
-- Can bang the pair
```

### Example 5: Bang Elimination

```haskell
let !x = !5 in (x, x)    ✓
-- !5 : !Nat
-- After unwrap, x :ω Nat
-- Can use x multiple times
```

## REPL Commands

```bash
:help               # Show help
:type <expr>        # Show type of expression
:quit               # Exit
```

## Real-World Applications

### Rust Ownership

```rust
let file = File::open("data.txt")?;  // Linear ownership
// file moved here, can't use again
let contents = read_file(file);
// file is consumed, no longer accessible
```

Linear types model Rust's ownership system!

### Session Types

```haskell
Send Int (Recv Bool End)
-- Must send an Int, then receive a Bool, then close
```

Protocol encoded in types!

### Capabilities

```haskell
AdminToken -o AdminAction -o ()
-- Admin token consumed when performing action
-- Can't reuse token
```

## Variants and Extensions

| System | Usage | Discard | Duplicate |
|--------|-------|---------|-----------|
| **Linear** (1) | Exactly once | No | No |
| **Affine** (≤1) | At most once | Yes | No |
| **Relevant** (≥1) | At least once | No | Yes |
| **Unrestricted** (ω) | Any | Yes | Yes |

This chapter implements **Linear** types.

## Connection to Linear Logic

```
Linear Logic    Programming
────────────    ───────────
A ⊸ B           A -o B (linear function)
A ⊗ B           A * B (tensor product)
!A              !A (of course/bang)
A & B           A × B (with/product)
A ⊕ B           A + B (plus/sum)
```

## Next Steps

After mastering linear types:
- **Affine types**: Rust-style (can discard)
- **Session types**: Communication protocols
- **Quantitative types**: Generalized multiplicities (0, 1, ω)
- **Idris 2**: Practical implementation

## Further Reading

- **Girard (1987)**: "Linear Logic" - foundational work
- **Wadler (1990)**: "Linear Types Can Change the World!"
- **Bernardy et al. (2017)**: "Linear Haskell" - GHC implementation
- **Walker (2005)**: "Substructural Type Systems" - comprehensive overview
