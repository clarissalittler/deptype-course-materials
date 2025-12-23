# Chapter 10: Linear Types - Tutorial

This tutorial walks through linear types with step-by-step examples.

## Part 1: Why Linear Types?

### The Resource Problem

Consider file handling:

```python
f = open("data.txt")
data = f.read()
f.close()
# What if we forget close()? → Resource leak
# What if we close() twice? → Error or undefined behavior
```

**Problem**: The type system doesn't track resource lifecycle.

### The Linear Solution

With linear types:
```
open  : Path -o Handle    -- Returns linear handle
read  : Handle -o (Data * Handle)  -- Uses handle, returns new one
close : Handle -o ()      -- Consumes handle
```

The `-o` arrow means "linear function"—argument used exactly once.

**Key insight**: A linear handle MUST be closed. The type system enforces it!

## Part 2: Multiplicities

### Two Multiplicities

**Linear (1)**: Used exactly once
```
λ(x :1 Nat). x      -- x used once ✓
λ(x :1 Nat). (x, x)  -- x used twice ✗
λ(x :1 Nat). 0       -- x not used ✗
```

**Unrestricted (ω)**: Used any number of times
```
λ(x :ω Nat). x          -- x used once ✓
λ(x :ω Nat). (x, x)     -- x used twice ✓
λ(x :ω Nat). 0          -- x not used ✓
λ(x :ω Nat). (x, (x, x)) -- x used three times ✓
```

### Function Types

- `A -o B` (linear): Function uses argument exactly once
- `A -> B` (unrestricted): Function uses argument any number of times

### Subtyping Intuition

Unrestricted is "more permissive":
- An unrestricted function can be used where linear is expected
- But not vice versa!

## Part 3: Usage Tracking

### How the Type Checker Works

The type checker tracks how many times each variable is used:

```
data Usage = Unused | UsedOnce | UsedMany
```

For `λ(x :1 Nat). x`:
1. Start: `x` is `Unused`
2. See `x` in body: `x` becomes `UsedOnce`
3. Check: Linear variable used once ✓

For `λ(x :1 Nat). (x, x)`:
1. Start: `x` is `Unused`
2. First `x`: becomes `UsedOnce`
3. Second `x`: becomes `UsedMany`
4. Check: Linear variable used more than once ✗

### Context Splitting

When typing `(t₁, t₂)`, linear variables must be split:

```
Example: λ(x :1 Nat). λ(y :1 Bool). (x, y)

In (x, y):
- x goes to left: Γ₁ = {x :1 Nat}
- y goes to right: Γ₂ = {y :1 Bool}
- Result: Γ₁ ⊢ x : Nat, Γ₂ ⊢ y : Bool
```

Each linear variable appears in exactly one subterm.

### Worked Example

Type check `λ(x :1 Nat). λ(y :1 Nat). (y, x)`:

```
1. Outer lambda binds x :1 Nat
2. Inner lambda binds y :1 Nat
3. Body is (y, x):
   - Need to type (y, x) with {x :1, y :1}
   - Split: y uses y, x uses x
   - Each linear variable used once ✓
4. Result type: Nat -o Nat -o (Nat * Nat)
```

## Part 4: The Bang Type

### The Problem

Sometimes we need to use a value multiple times:
```
λ(x :1 Nat). (x, x)  -- Can't do this with linear x
```

### The Solution: Bang

The bang type `!A` makes a value unrestricted:

```
!5 : !Nat    -- 5 wrapped in bang
```

### Bang Introduction

```
Γ ⊢ t : A    (Γ has only unrestricted variables)
────────────────────────────────────────────────
Γ ⊢ !t : !A
```

**Key**: Can only bang values built from unrestricted ingredients.

```
!5              -- OK: 5 is a constant
!true           -- OK: true is a constant
λ(x :ω Nat). !x  -- OK: x is unrestricted

λ(x :1 Nat). !x  -- ERROR: can't bang linear variable
```

### Bang Elimination

```
Γ ⊢ t₁ : !A    Δ, x :ω A ⊢ t₂ : B
──────────────────────────────────
Γ, Δ ⊢ let !x = t₁ in t₂ : B
```

Unwrap the bang, get unrestricted access:

```
let !x = !5 in (x, x)     -- OK! x is now unrestricted
let !x = !5 in (x, (x, x)) -- OK! Use x as many times as you want
```

### Worked Example

Type check `let !x = !5 in (x, x)`:

```
1. Type !5:
   - 5 : Nat (constant, no linear vars)
   - !5 : !Nat ✓

2. Type body (x, x) with x :ω Nat:
   - x can be used multiple times
   - (x, x) : Nat * Nat ✓

3. Result: Nat * Nat
```

## Part 5: Linear Pairs

### Tensor Product

The pair type `A * B` (tensor product) requires both components be used:

```
(t₁, t₂) : A * B
```

### Pair Elimination

```
Γ ⊢ t₁ : A * B    Δ, x :1 A, y :1 B ⊢ t₂ : C
──────────────────────────────────────────────
Γ, Δ ⊢ let (x, y) = t₁ in t₂ : C
```

Both x and y are bound linearly—must use each once!

### Valid Examples

```
let (x, y) = (1, 2) in x + y     -- Both used ✓
let (x, y) = (1, true) in (y, x) -- Both used ✓
```

### Invalid Examples

```
let (x, y) = (1, 2) in x         -- y not used ✗
let (x, y) = (1, 2) in (x, x)    -- x used twice, y unused ✗
let (x, y) = (1, 2) in 0         -- Neither used ✗
```

### Swapping Pair Components

```
swap : (A * B) -o (B * A)
swap = λ(p :1 (A * B)). let (x, y) = p in (y, x)
```

This is valid:
- p is used once (in let)
- x and y are each used once
- Returns (y, x) using both

## Part 6: Patterns

### Resource Management Pattern

```haskell
-- Linear file API
open  : Path -o Handle
read  : Handle -o (String * Handle)
write : (Handle * String) -o Handle
close : Handle -o ()

-- Usage
let h = open "file.txt" in
let (data, h') = read h in
let h'' = write (h', "new data") in
close h''
```

Notice how the handle is "threaded through":
- `open` creates a fresh handle
- `read` consumes handle, returns new one
- `write` consumes handle and data, returns new handle
- `close` consumes final handle

No way to forget to close or close twice!

### Memory Management Pattern

```haskell
malloc : Size -o Ptr
use    : (Ptr * (A -o B)) -o (Ptr * B)
free   : Ptr -o ()

let p = malloc 100 in
let (p', result) = use (p, computation) in
free p'
```

### Accumulator Pattern

```haskell
-- Linear fold
foldL : (B -o A -o B) -o B -o List A -o B
```

The accumulator is linear, threaded through the fold.

## Practice Problems

### Problem 1: Linear Identity

Write a linear identity function:

```
id : A -o A
id = ?
```

<details>
<summary>Solution</summary>

```
id = λ(x :1 A). x
```

Uses x exactly once.
</details>

### Problem 2: Linear Composition

Write linear function composition:

```
compose : (B -o C) -o (A -o B) -o A -o C
compose = ?
```

<details>
<summary>Solution</summary>

```
compose = λ(g :1 B -o C). λ(f :1 A -o B). λ(x :1 A). g (f x)
```

Each of g, f, x used exactly once.
</details>

### Problem 3: Using Bang

Make this work using bang:

```
double : Nat -> Nat * Nat
double = λ(x :ω Nat). ?
```

<details>
<summary>Solution</summary>

```
double = λ(x :ω Nat). (x, x)
```

Since x is unrestricted, we can use it twice.

Or with explicit bang:
```
double' : !Nat -o Nat * Nat
double' = λ(b :1 !Nat). let !x = b in (x, x)
```
</details>

### Problem 4: Pair Swap with Bang

Write swap that works with banged pairs:

```
bangSwap : !(A * B) -o (B * A)
bangSwap = ?
```

<details>
<summary>Solution</summary>

```
bangSwap = λ(bp :1 !(A * B)).
  let !p = bp in
  let (x, y) = p in
  (y, x)
```

Wait, there's a subtlety! After `let !p = bp`, we have `p :ω (A * B)`. Then `let (x, y) = p` gives us `x :1 A, y :1 B`. We must use each once.

Actually the above works because we do use x and y each once in `(y, x)`.
</details>

### Problem 5: Why Invalid?

Why is this invalid?

```
bad : (A -o B) -o A -o (B * B)
bad = λ(f :1 A -o B). λ(x :1 A). (f x, f x)
```

<details>
<summary>Solution</summary>

`f` is linear but used twice (applied to `x` twice). Linear functions can only be called once!

To fix:
```
good : (A -> B) -o A -o (B * B)
good = λ(f :1 A -> B). λ(x :1 A).
  let !g = ... -- need to get unrestricted version of f
```

Actually, you'd need `!(A -> B)` or similar to make this work.
</details>
