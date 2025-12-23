# Chapter 11: Refinement Types - Tutorial

This tutorial walks through refinement types with step-by-step examples.

## Part 1: Why Refinement Types?

### The Precision Problem

Consider a safe division function:

```haskell
div :: Int -> Int -> Int
div x y = x `quot` y  -- What if y == 0?
```

**Problem**: The type `Int -> Int -> Int` doesn't prevent division by zero.

Solutions:
1. Runtime check: Return `Maybe Int` -- loses precision
2. Documentation: "Don't pass 0" -- not enforced
3. Refinement types: Encode the constraint in the type!

### The Refinement Solution

```
div : Nat -> {d: Nat | d > 0} -> Nat
```

Now the type system ensures the divisor is never zero!

**Key insight**: `{d: Nat | d > 0}` means "natural numbers greater than zero."

## Part 2: Refinement Type Syntax

### Basic Refinements

A refinement type has the form:
```
{x: T | φ(x)}
```

Where:
- `x` is a bound variable
- `T` is the base type
- `φ(x)` is a predicate about x

### Examples

```
{x: Nat | x > 0}           -- Positive naturals
{x: Nat | x < 100}         -- Naturals less than 100
{x: Nat | x >= 5 && x <= 10}  -- Naturals from 5 to 10
{x: Nat | x == 42}         -- Exactly 42 (singleton type)
{x: Bool | x == true}      -- Only true
```

### Predicate Language

Predicates can include:
```
true, false               -- Boolean constants
x                         -- Boolean variables
!φ, φ && ψ, φ || ψ       -- Boolean operations
φ => ψ                    -- Implication
a == b, a != b            -- Equality
a < b, a <= b             -- Comparisons
a > b, a >= b             -- Comparisons
a + b, a - b              -- Arithmetic
```

### Trivial Refinements

Some refinements are trivially true or false:
```
{x: Nat | true}           -- Same as Nat
{x: Nat | false}          -- Empty type (uninhabited)
{x: Nat | x >= 0}         -- Same as Nat (always true)
```

## Part 3: Subtyping

### The Key Insight

Refinement types form a subtyping hierarchy based on predicate implication:

```
φ(x) ⟹ ψ(x)
─────────────────────────
{x: T | φ} <: {x: T | ψ}
```

**Meaning**: If φ implies ψ, then `{x: T | φ}` is a subtype of `{x: T | ψ}`.

### Examples

```
{x: Nat | x > 10} <: {x: Nat | x > 5}     -- ✓ (10 > implies > 5)
{x: Nat | x > 10} <: {x: Nat | x > 0}     -- ✓ (10 > implies > 0)
{x: Nat | x == 7} <: {x: Nat | x > 0}     -- ✓ (7 is positive)
{x: Nat | x > 5} <: {x: Nat | x > 10}     -- ✗ (6 > 5 but not > 10)
```

### Intuition: Sets

Think of types as sets:
- `{x: Nat | x > 10}` = {11, 12, 13, ...}
- `{x: Nat | x > 5}` = {6, 7, 8, ...}
- The first is a subset of the second!

Subtype = subset (more specific = fewer values).

### Worked Example

Is `{x: Nat | x > 0 && x < 10}` a subtype of `{x: Nat | x < 100}`?

1. Need to check: `(x > 0 && x < 10) ⟹ (x < 100)`
2. If x is between 1 and 9, is x < 100? Yes!
3. Therefore, it IS a subtype.

## Part 4: Path Sensitivity

### The Problem

Consider:
```
λx : Nat. if iszero x then 0 else pred x
```

In the else branch, we call `pred x`. But `pred` on 0 is problematic!

### The Solution

The type checker tracks **path conditions**:
- In then branch: We know `iszero x` is true, so `x == 0`
- In else branch: We know `iszero x` is false, so `x != 0`, meaning `x > 0`

### Typing Rule

```
   Γ, φ ⊢ t₂ : T₂    Γ, ¬φ ⊢ t₃ : T₃
  ────────────────────────────────────
    Γ ⊢ if t₁ then t₂ else t₃ : T
```

The condition φ is added to context in the then branch, ¬φ in else branch.

### Example

```
λx : Nat. if x > 5
          then x      -- Here: x : {n: Nat | n > 5}
          else x + 10 -- Here: x : {n: Nat | n <= 5}
```

### Nested Conditions

Path conditions accumulate:
```
λx : Nat. if x > 0 then
            if x < 10 then
              x       -- Here: x : {n: Nat | n > 0 && n < 10}
            else
              x       -- Here: x : {n: Nat | n > 0 && n >= 10}
          else
            0         -- Here: x : {n: Nat | n <= 0}, i.e., x == 0
```

## Part 5: Dependent Function Types

### Basic Idea

In a dependent function type `(x: T₁) -> T₂`, the result type T₂ can mention x.

### Examples

**Division**:
```
div : (n: Nat) -> (d: {d: Nat | d > 0}) -> Nat
```
The divisor must be positive.

**Vector indexing**:
```
index : (n: Nat) -> Vec a n -> {i: Nat | i < n} -> a
```
Index must be less than vector length.

**Replicate**:
```
replicate : (n: Nat) -> a -> Vec a n
```
Result length equals input n.

### Why Dependent?

The return type can depend on the argument value:
```
head : (xs: {xs: List a | length xs > 0}) -> a

-- For specific list [1,2,3], return type is Nat
-- The constraint ensures list is non-empty
```

### Worked Example

Type check `λn. λd. div n d` where:
- n : Nat
- d : {d: Nat | d > 0}
- div : Nat -> {d: Nat | d > 0} -> Nat

1. n has type Nat ✓
2. d has type `{d: Nat | d > 0}` ✓
3. `div n d` expects Nat and positive Nat
4. We have exactly that! ✓

## Part 6: Predicate Validity

### The Challenge

To check `{x: T | φ} <: {x: T | ψ}`, we need to verify `φ(x) ⟹ ψ(x)`.

How do we check predicate implications?

### Approaches

1. **Ground evaluation**: No variables? Just compute.
   ```
   5 > 0 ⟹ true
   -- Evaluate: True ⟹ True = True ✓
   ```

2. **Syntactic rules**: Simple patterns.
   ```
   p ⟹ p           -- Always true (reflexivity)
   p ⟹ true        -- Always true
   false ⟹ p       -- Always true (ex falso)
   p && q ⟹ p      -- Conjunction elimination
   ```

3. **SMT solvers**: Full logical reasoning.
   ```
   x > 10 ⟹ x > 5   -- Needs arithmetic reasoning
   -- SMT solver can prove this
   ```

### Our Implementation

```haskell
implies :: Pred -> Pred -> Bool
implies p q
  | p == q = True                    -- Reflexivity
  | q == PBool True = True           -- Anything implies true
  | p == PBool False = True          -- False implies anything
  | isGround p && isGround q = ...   -- Evaluate
  | otherwise = False                -- Conservative
```

### SMT Solvers

For production use, integrate an SMT solver:
- Z3, CVC5, Yices
- Decidable for linear integer arithmetic
- LiquidHaskell uses Z3

## Part 7: Practical Patterns

### Safe Array Access

```
type Array n a = {arr: [a] | length arr == n}

get : (arr: Array n a) -> (i: {i: Nat | i < n}) -> a
get arr i = arr !! i  -- Always safe!

-- Usage:
let arr = [1, 2, 3] : Array 3 Nat in
get arr 0   -- OK: 0 < 3
get arr 5   -- TYPE ERROR: 5 < 3 is false
```

### Non-Null Values

```
type NonNull a = {x: Maybe a | x != Nothing}

fromJust : NonNull a -> a
fromJust (Just x) = x
-- No Nothing case needed - type rules it out!

-- Usage:
let x = Just 5 : NonNull Nat in
fromJust x   -- OK: x is definitely Just something
```

### Ordered Lists

```
type Sorted a = {xs: List a | isSorted xs}

merge : Sorted a -> Sorted a -> Sorted a
-- Implementation maintains sortedness
```

### Positive Numbers

```
type Pos = {n: Nat | n > 0}

safePred : Pos -> Nat
safePred n = pred n  -- Always safe!

safeDiv : Nat -> Pos -> Nat
safeDiv n d = n `div` d  -- Always safe!
```

## Practice Problems

### Problem 1: Subtyping

Determine if `{x: Nat | x > 7}` is a subtype of `{x: Nat | x > 3}`.

<details>
<summary>Solution</summary>

Yes! We need `x > 7 ⟹ x > 3`.

If x > 7, then certainly x > 3 (since 7 > 3).

Therefore `{x: Nat | x > 7} <: {x: Nat | x > 3}`.
</details>

### Problem 2: Path Sensitivity

What refinement does x have in each branch?

```
if x >= 10 then
  -- x has type ???
else
  -- x has type ???
```

<details>
<summary>Solution</summary>

- Then branch: x : {n: Nat | n >= 10}
- Else branch: x : {n: Nat | n < 10}

The condition adds to the path context in each branch.
</details>

### Problem 3: Function Types

Write a type for `tail` that ensures the list is non-empty:

<details>
<summary>Solution</summary>

```
tail : {xs: List a | length xs > 0} -> List a
```

Or with dependent types:
```
tail : (xs: {xs: List a | length xs > 0}) -> List a
```

The refinement ensures we never call tail on an empty list.
</details>

### Problem 4: Combined Refinements

Is this subtyping valid?
```
{x: Nat | x > 5 && x < 10} <: {x: Nat | x > 0}
```

<details>
<summary>Solution</summary>

Yes!

We need: `(x > 5 && x < 10) ⟹ (x > 0)`

If x is between 6 and 9 (the valid range), then x is definitely > 0.

The conjunction gives us more information, making it a subtype.
</details>

### Problem 5: Why Wrong?

Why is this type signature wrong?

```
weaken : {x: Nat | x > 0} -> {x: Nat | x > 10}
weaken x = x
```

<details>
<summary>Solution</summary>

The implementation doesn't work because:
- Input: any positive number (1, 2, 3, ...)
- Output requires: numbers > 10

If we get x = 5, it satisfies the input type (5 > 0) but NOT the output type (5 > 10 is false).

This is NOT a valid subtyping! `{x: Nat | x > 0} </: {x: Nat | x > 10}`.

We'd need to add 10 or check and error, not just return x.
</details>
