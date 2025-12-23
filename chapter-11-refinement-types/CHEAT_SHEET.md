# Chapter 11: Refinement Types - Cheat Sheet

## Syntax at a Glance

### Refinement Types
```
{x: T | φ(x)}    -- Values of type T satisfying predicate φ
```

### Predicates
```
φ ::= true | false           -- Boolean constants
    | x                      -- Boolean variable
    | !φ                     -- Negation
    | φ₁ && φ₂               -- Conjunction
    | φ₁ || φ₂               -- Disjunction
    | φ₁ => φ₂               -- Implication
    | a₁ op a₂               -- Comparison

a ::= x | n                  -- Variable or literal
    | a₁ + a₂ | a₁ - a₂      -- Arithmetic

op ::= == | != | < | <= | > | >=
```

### Types
```
T ::= Bool | Nat | Unit      -- Base types
    | {x: T | φ}             -- Refinement type
    | (x: T₁) -> T₂          -- Dependent function type
```

## Key Concepts

### Refinement Types as Sets
Think of refinements as carving out subsets:
- `Nat` = {0, 1, 2, 3, ...}
- `{x: Nat | x > 0}` = {1, 2, 3, ...}
- `{x: Nat | x == 5}` = {5}

### Subtyping via Implication
```
   φ(x) ⟹ ψ(x)
  ─────────────────────
  {x: T | φ} <: {x: T | ψ}
```

**Key insight**: Stronger predicate (more specific) is subtype of weaker one.

### Examples
```
{x: Nat | x > 10} <: {x: Nat | x > 5}     ✓ (10 > implies > 5)
{x: Nat | x == 7} <: {x: Nat | x > 0}     ✓ (7 is positive)
{x: Nat | x > 5} <: {x: Nat | x > 10}     ✗ (6 > 5 but not > 10)
```

## Core Typing Rules

### Subsumption
```
   Γ ⊢ t : T₁    T₁ <: T₂
  ───────────────────────── (T-Sub)
       Γ ⊢ t : T₂
```

### Refinement Subtyping
```
   Γ ⊢ T₁ <: T₂    ∀x. φ(x) ⟹ ψ(x)
  ──────────────────────────────────── (S-Refine)
      Γ ⊢ {x: T₁ | φ} <: {x: T₂ | ψ}
```

### Path-Sensitive Conditionals
```
   Γ, φ ⊢ t₂ : T₂    Γ, ¬φ ⊢ t₃ : T₃
  ────────────────────────────────────
    Γ ⊢ if t₁ then t₂ else t₃ : T
```

Conditions refine types in branches!

## Common Patterns

### Positive Numbers
```
type Pos = {x: Nat | x > 0}

safePred : Pos -> Nat
safePred = λn : Pos. pred n
```

### Non-Zero Division
```
div : Nat -> {d: Nat | d > 0} -> Nat
div = λn. λd. n `quot` d
```

### Bounded Values
```
type Digit = {x: Nat | x >= 0 && x <= 9}
type Index n = {i: Nat | i < n}
```

### Non-Empty Lists
```
head : {xs: List a | length xs > 0} -> a
tail : {xs: List a | length xs > 0} -> List a
```

### Singleton Types
```
{x: Bool | x == true}     -- Only true
{x: Nat | x == 42}        -- Only 42
```

## Path Sensitivity Examples

### Safe Predecessor
```
safePred : Nat -> Nat
safePred = λx. if iszero x
               then 0           -- x == 0 here
               else pred x      -- x > 0 here!
```

### Nested Conditions
```
classify : Nat -> Nat
classify = λx.
  if x > 10 then
    if x < 20 then
      1    -- x : {n: Nat | n > 10 && n < 20}
    else
      2    -- x : {n: Nat | n > 10 && n >= 20}
  else
    0      -- x : {n: Nat | n <= 10}
```

## Predicate Validity

### Simple Rules
```
p ⟹ p             -- Reflexivity
p ⟹ true          -- Anything implies true
false ⟹ p         -- False implies anything
p && q ⟹ p        -- Conjunction elimination
p ⟹ p || q        -- Disjunction introduction
```

### Ground Evaluation
```
5 > 0 ⟹ true     -- Evaluate: true ⟹ true = true ✓
3 < 10 ⟹ 3 < 5   -- Evaluate: true ⟹ false = false ✗
```

### SMT Solvers (Production)
For complex implications like `x > 10 ⟹ x > 5`, use SMT solvers:
- Z3 (Microsoft)
- CVC5
- Yices

## Dependent Function Types

### Basic Form
```
(x: T₁) -> T₂    -- x is in scope in T₂
```

### Examples
```
-- Result depends on argument
replicate : (n: Nat) -> a -> {arr: Vec a | length arr == n}

-- Precondition on argument
div : (n: Nat, d: {d: Nat | d > 0}) -> Nat

-- Postcondition on result
abs : Int -> {n: Nat | n >= 0}
```

## Subtyping Relationships

### Weakening (Always Valid)
```
{x: T | φ} <: {x: T | true}    -- To trivial refinement
{x: T | φ} <: T                 -- Drop refinement
```

### Strengthening (Not Always Valid)
```
T <: {x: T | φ}                 -- Only if all T values satisfy φ
```

### Lattice Structure
```
{x: Nat | x == 5}               (most specific)
        |
{x: Nat | x > 0 && x < 10}
        |
{x: Nat | x > 0}
        |
{x: Nat | true}                 (least specific)
```

## Common Idioms

| Pattern | Refinement Type | Use Case |
|---------|----------------|----------|
| Positive | `{n: Nat \| n > 0}` | Prevent division by zero |
| Non-empty | `{xs: List a \| length xs > 0}` | Safe head/tail |
| Bounded | `{n: Nat \| n < max}` | Array indices |
| Sorted | `{xs: List a \| isSorted xs}` | Maintain invariants |
| Non-null | `{x: Maybe a \| x != Nothing}` | Safe unwrapping |

## Practical Tips

### ✓ Do
- Use refinements for preconditions (function inputs)
- Add postconditions when they help (function outputs)
- Let path sensitivity do the work in branches
- Keep predicates in decidable fragments (linear arithmetic)
- Think of refinements as contracts

### ✗ Avoid
- Complex predicates (undecidable)
- Over-annotating (let inference work)
- Refinements where simple types suffice
- Recursive predicates (often undecidable)

## Debugging Tips

### Type Error: "Cannot prove implication"
```
-- Problem: φ ⟹ ψ not provable
-- Solutions:
1. Simplify predicate
2. Add intermediate assertions
3. Check if implication is actually false
4. Use SMT solver for complex cases
```

### Name Capture in Predicates
```
-- Be careful with variable names
(x: {n: Nat | n > 0}) -> {m: Nat | m > x}  -- x is bound!
```

### Path Conditions Not Propagating
```
-- Ensure conditionals are visible to type checker
if x > 0 then ... else ...  -- Good: direct comparison
if isPositive x then ...     -- Harder: may need annotation
```

## REPL Commands

```bash
refinement> :type λx : {n : Nat | n > 0}. x
{n : Nat | n > 0} -> {n : Nat | n > 0}

refinement> :check 5 > 0
Valid (always true)

refinement> :subtype {x: Nat | x > 10} <: {x: Nat | x > 5}
true

refinement> :eval let x = 3 in x + x
6
```

## Comparison to Other Systems

| Feature | Refinement Types | Dependent Types | Simple Types |
|---------|-----------------|-----------------|--------------|
| Expressiveness | Medium | High | Low |
| Automation | High (with SMT) | Low (proof required) | N/A |
| Decidability | Often | Rarely | Always |
| Runtime cost | None | None | None |

## Further Reading

### Primary Sources
- **Freeman & Pfenning (1991)**: "Refinement Types for ML" - Original paper
- **Rondon et al. (2008)**: "Liquid Types" - Automated inference
- **Vazou et al. (2014)**: "Refinement Types for Haskell" - LiquidHaskell

### Tools
- **LiquidHaskell**: Refinement types for Haskell
- **F***: Refinements + full dependent types
- **Dafny**: Verification with refinements

## Quick Reference Card

```
Syntax:       {x: T | φ}
Meaning:      Values of T satisfying φ
Subtyping:    φ ⟹ ψ  means  {x:T|φ} <: {x:T|ψ}
Path sense:   if c then t else e refines t, e with c, ¬c
Dependent:    (x: T₁) -> T₂  means T₂ can mention x
SMT solver:   For proving φ ⟹ ψ automatically
Use case:     Statically prevent runtime errors

Remember: Stronger predicate = fewer values = subtype!
```

## Next Steps

After mastering refinement types:
- Chapter 12: Effect Systems - Track computational effects
- Full Dependent Types - Arbitrary terms in types
- LiquidHaskell - Apply refinements to real code
