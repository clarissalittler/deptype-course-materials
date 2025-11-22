# Chapter 1: Untyped Lambda Calculus - Tutorial

## Introduction

Welcome to the tutorial for Chapter 1! This document walks you through lambda calculus concepts with detailed, step-by-step examples. Unlike the formal treatment in README.md, this tutorial explains concepts in plain language and shows exactly how to work through problems.

Think of this as sitting down with a tutor who shows you not just what to do, but why each step works.

---

## Part 1: Basic Syntax and Your First Lambda Terms

### What is a Lambda Term?

Let's start with something familiar. In JavaScript, you might write:
```javascript
const identity = x => x;
```

This is a function that takes `x` and returns `x`. In lambda calculus, we write the same thing as:
```
λx. x
```

That's it! The `λ` (lambda) means "this is a function", `x` is the parameter, the `.` separates the parameter from the body, and the second `x` is the body.

### The Three Building Blocks

Lambda calculus has exactly three types of expressions:

**1. Variables** - Just names like `x`, `y`, `z`
```
x
y
foo
```

**2. Abstractions** - Functions using λ
```
λx. x          (function taking x, returning x)
λy. y          (same thing, different variable name)
λf. λx. f x    (curried function - more on this below)
```

**3. Applications** - Calling functions
```
f x            (call f with argument x)
(λx. x) y      (call the identity function on y)
```

### Let's Build Some Functions

**Identity Function**: Returns its argument unchanged
```
λx. x
```
Think: "Give me an x, I'll give you back x"

**Constant Function**: Returns its first argument, ignores the second
```
λx. λy. x
```
Think: "Give me an x, then give me a y, I'll give you back x (ignoring y)"

Wait, why two λs? Because in lambda calculus, functions take only ONE argument. To take multiple arguments, we use **currying**.

**Apply Function**: Takes a function and an argument, applies the function
```
λf. λx. f x
```
Think: "Give me a function f, then give me an argument x, I'll apply f to x"

**Compose Function**: Combines two functions
```
λf. λg. λx. f (g x)
```
Think: "Give me two functions f and g, and an x, I'll apply g to x then apply f to the result"

### Parentheses and Precedence

This trips up beginners! Here are the rules:

**Rule 1: Application associates to the LEFT**
```
a b c  means  (a b) c  NOT  a (b c)
```

Example:
```
f x y  means  (f x) y
```
First we apply `f` to `x`, getting some result, then we apply that result to `y`.

**Rule 2: Abstraction extends to the RIGHT as far as possible**
```
λx. λy. t  means  λx. (λy. t)
λx. x y    means  λx. (x y)  NOT  (λx. x) y
```

**Rule 3: Use parentheses when in doubt!**
```
(λx. x) y      (apply identity to y)
λx. (x y)      (function that applies x to y)
```

### Practice Together

Let's parse this: `λf. λx. f x`

Step by step:
1. It starts with `λf.` so the outer function takes parameter `f`
2. The body is `λx. f x`
3. That body is another function taking parameter `x`
4. Its body is `f x` (application of f to x)

So: "A function taking f, returning a function taking x, which applies f to x"

Let's parse: `f g h`

Step by step:
1. Application associates left
2. So: `(f g) h`
3. First apply `f` to `g`, then apply the result to `h`

---

## Part 2: Free and Bound Variables

### What Does "Bound" Mean?

A variable is **bound** if it's caught by a lambda. Think of λx as declaring a variable x.

Let's look at: `λx. x`
- The first `x` (after λ) declares the variable
- The second `x` (in the body) uses it
- This x is **bound** because it's declared by the λ

Now: `λx. x y`
- `x` is bound (declared by λx)
- `y` is **free** (not declared anywhere - it comes from outside)

### Visual Aid

Think of lambdas as boxes. Variables inside the box that are declared by the box are bound. Variables that come from outside the box are free.

```
┌─ λx. ─────┐
│  x is     │  ← x is bound (declared by this λx)
│  bound    │
└───────────┘

┌─ λx. ─────┐
│  x y      │  ← x is bound, y is free (not declared here)
└───────────┘
```

### Computing Free Variables (FV)

Let's compute FV step-by-step for: `λx. λy. x y z`

Start from the inside:
1. In the innermost part `x y z`:
   - `x` is bound by outer `λx`
   - `y` is bound by `λy`
   - `z` is not bound by anything → FREE

2. Working outward with `λy`:
   - The `λy` binds `y`, so we remove `y` from the free set
   - FV(λy. x y z) = FV(x y z) \ {y} = {x, z} \ {y} = {x, z}

3. Finally with `λx`:
   - The `λx` binds `x`, so we remove `x`
   - FV(λx. λy. x y z) = {x, z} \ {x} = {z}

**Answer**: The only free variable is `z`.

### Practice Together

**Example 1**: `(λx. x) y`

Left part: `λx. x`
- FV(λx. x) = {x} \ {x} = {} (empty - no free variables)

Right part: `y`
- FV(y) = {y}

Application: union of both
- FV((λx. x) y) = {} ∪ {y} = {y}

**Answer**: Free variables are {y}

**Example 2**: `λf. λx. f x y`

Innermost: `f x y`
- FV(f x y) = {f, x, y}

After λx:
- FV(λx. f x y) = {f, x, y} \ {x} = {f, y}

After λf:
- FV(λf. λx. f x y) = {f, y} \ {f} = {y}

**Answer**: Free variables are {y}

---

## Part 3: Substitution and Alpha-Conversion

### The Basic Idea

Substitution is how we "pass arguments" to functions. When we write `[x ↦ 5]t`, we mean "replace every free occurrence of x in t with 5".

### Simple Cases

**Example 1**: `[x ↦ a]x`
- Replace x with a
- Result: `a`

**Example 2**: `[x ↦ a]y`
- We're replacing x, but this is y
- Result: `y` (unchanged)

**Example 3**: `[x ↦ a](x y)`
- In the application `x y`, replace x
- Result: `a y`

### The Shadowing Case

This is where it gets interesting!

**Example 4**: `[x ↦ a](λx. x)`

Question: Do we replace x in the body?

Answer: NO! Because the inner λx "shadows" (re-declares) x.

Think of it like:
```javascript
let x = "outer";
function foo(x) {  // This x shadows the outer x
  return x;        // This refers to the parameter, not the outer x
}
```

Result: `λx. x` (unchanged)

The inner x is a completely different variable than the outer x, even though they have the same name.

### The Dangerous Case: Variable Capture

This is THE most important thing to understand about substitution.

**Example 5 (WRONG WAY)**: `[y ↦ x](λx. y)`

If we naively substitute:
- Replace y with x
- Get: `λx. x`

**This is WRONG!** Why?

Before substitution: `λx. y` is a function that ignores its argument and returns y (which comes from outside)

After wrong substitution: `λx. x` is a function that returns its argument

We changed the meaning! The free variable y got "captured" by the λx.

**Example 5 (RIGHT WAY)**: `[y ↦ x](λx. y)`

Step 1: Recognize danger - we're substituting y with x, but there's a λx in the term
Step 2: **α-convert** - rename the bound variable to something fresh, like z
```
λx. y  →  λz. y    (α-conversion: rename x to z)
```
Step 3: Now substitute safely
```
[y ↦ x](λz. y) = λz. x
```

**Result**: `λz. x` - a function that ignores its argument and returns x

This has the right meaning!

### Step-by-Step Walkthrough

Let's do: `[y ↦ x](λx. λy. y x)`

**Step 1**: Check for capture
- We're substituting `y ↦ x`
- We have both `λx` and `λy` in the term
- Danger! Both need renaming

**Step 2**: α-convert to fresh variables
```
λx. λy. y x  →  λa. λb. b a
```

**Step 3**: Now substitute
```
[y ↦ x](λa. λb. b a) = λa. λb. b a
```

Wait, nothing changed! Why? Because in `λa. λb. b a`, the variable `y` doesn't even appear - we renamed it to `b`. So there's nothing to substitute.

**Result**: `λa. λb. b a`

### The Substitution Rules (Reference)

For quick reference:

```
[x ↦ s]x = s                           (replace the variable)
[x ↦ s]y = y  (if x ≠ y)              (different variable, don't touch)
[x ↦ s](λx. t) = λx. t                (shadowing - don't substitute in body)
[x ↦ s](λy. t) = λy. [x ↦ s]t         (if y ≠ x, y ∉ FV(s), and x ∉ FV(t) or y not bound)
[x ↦ s](λy. t) = λz. [x ↦ s][y ↦ z]t  (if y ∈ FV(s), rename y to fresh z)
[x ↦ s](t₁ t₂) = ([x ↦ s]t₁) ([x ↦ s]t₂)  (substitute in both parts)
```

---

## Part 4: Beta-Reduction and Evaluation

### The Core Rule

Beta-reduction (β-reduction) is the fundamental computation step:

```
(λx. t) s  →  [x ↦ s]t
```

In words: "When you apply a function `λx. t` to an argument `s`, substitute `s` for `x` in the body `t`"

This is exactly like function calls in regular programming!

### Example 1: Identity Function

Let's evaluate: `(λx. x) y`

Step 1: Identify the redex (reducible expression)
- We have `(λx. t)` where `t = x`
- Applied to `s = y`

Step 2: Apply β-reduction
```
(λx. x) y  →  [x ↦ y]x
```

Step 3: Perform substitution
```
[x ↦ y]x = y
```

**Final result**: `y`

### Example 2: Constant Function

Let's evaluate: `(λx. λy. x) a b`

Step 1: This is actually `((λx. λy. x) a) b` (application associates left)

Step 2: First reduction
```
(λx. λy. x) a  →  [x ↦ a](λy. x)
                =  λy. a
```

Step 3: Now we have `(λy. a) b`

Step 4: Second reduction
```
(λy. a) b  →  [y ↦ b]a
            =  a
```

**Final result**: `a`

The constant function returns its first argument and discards the second!

### Example 3: Function Application

Let's evaluate: `(λf. λx. f x) (λy. y) z`

This is more complex. Let's take it step by step.

Step 1: Parse it: `((λf. λx. f x) (λy. y)) z`

Step 2: First reduction (apply to `λy. y`)
```
(λf. λx. f x) (λy. y)  →  [f ↦ (λy. y)](λx. f x)
                        =  λx. (λy. y) x
```

Step 3: Now we have `(λx. (λy. y) x) z`

Step 4: Second reduction
```
(λx. (λy. y) x) z  →  [x ↦ z]((λy. y) x)
                    =  (λy. y) z
```

Step 5: Third reduction
```
(λy. y) z  →  [y ↦ z]y
            =  z
```

**Final result**: `z`

### Example 4: Self-Application

Let's evaluate: `(λx. x x) (λy. y)`

Step 1: Apply β-reduction
```
(λx. x x) (λy. y)  →  [x ↦ (λy. y)](x x)
                    =  (λy. y) (λy. y)
```

Step 2: Continue
```
(λy. y) (λy. y)  →  [y ↦ (λy. y)]y
                  =  λy. y
```

**Final result**: `λy. y` (the identity function)

### Normal Form

A term is in **normal form** if no more β-reductions are possible.

Examples of normal forms:
- `x` (variable)
- `λx. x` (function with no redex)
- `λx. x y` (no redex to reduce)

Examples NOT in normal form:
- `(λx. x) y` (can reduce to `y`)
- `(λx. x x) (λx. x x)` (infinite reduction!)

---

## Part 5: Evaluation Strategies

### Why Strategies Matter

Consider this term: `(λx. λy. y) ((λz. z z) (λz. z z)) v`

Depending on how we evaluate it, we might get different outcomes!

### Call-by-Value (CBV)

**Strategy**: Evaluate arguments before applying functions

**Rule**: In `(λx. t) s`, first reduce `s` to a value, then substitute

Let's trace: `(λx. λy. y) ((λz. z z) (λz. z z)) v`

Step 1: Try to reduce the first argument `(λz. z z) (λz. z z)`
```
(λz. z z) (λz. z z)  →  (λz. z z) (λz. z z)  →  ...
```

Oh no! This loops forever! The argument never becomes a value, so we never get to apply the outer function.

**Result with CBV**: LOOPS FOREVER ∞

### Call-by-Name (CBN) / Normal Order

**Strategy**: Substitute arguments without evaluating them first

**Rule**: Always reduce the leftmost-outermost redex

Let's trace the same term: `(λx. λy. y) ((λz. z z) (λz. z z)) v`

Step 1: The leftmost redex is the whole application
```
(λx. λy. y) ((λz. z z) (λz. z z)) v  →  [x ↦ ((λz. z z) (λz. z z))](λy. y) v
```

But wait! The `x` doesn't appear in `λy. y`, so it gets discarded:
```
= (λy. y) v
```

Step 2: Continue
```
(λy. y) v  →  v
```

**Result with Normal Order**: `v` ✓

### The Moral of the Story

**Normal order is "more complete"**: If a term has a normal form, normal order will find it.

**Call-by-value is "more efficient"**: It doesn't duplicate work (no re-evaluating arguments).

Most real languages use call-by-value (with some optimizations). Haskell uses lazy evaluation (similar to call-by-name but with sharing).

### Example: Where CBV is Better

Consider: `(λx. x + x) (heavy_computation)`

**Call-by-value**:
1. Evaluate `heavy_computation` once → get result `r`
2. Substitute: `r + r`
3. Done!

**Call-by-name**:
1. Substitute first: `heavy_computation + heavy_computation`
2. Evaluate `heavy_computation` → `r`
3. Evaluate `heavy_computation` again → `r`
4. Compute `r + r`

Call-by-value is faster here!

**Lazy evaluation** (Haskell) solves this by sharing: evaluate once, share the result.

---

## Part 6: Church Encodings - Booleans

### The Big Idea

Since lambda calculus has no built-in booleans, numbers, or data structures, we encode them as **functions**.

The key insight: Data is behavior!

### Church Booleans

**TRUE**: A function that takes two arguments and returns the FIRST
```
true = λt. λf. t
```

**FALSE**: A function that takes two arguments and returns the SECOND
```
false = λt. λf. f
```

### Why Does This Work?

Think about how we use booleans - for conditionals!

```
if condition then branch1 else branch2
```

With Church booleans:
```
condition branch1 branch2
```

If `condition` is `true`:
```
(λt. λf. t) branch1 branch2  →  (λf. branch1) branch2  →  branch1
```

If `condition` is `false`:
```
(λt. λf. f) branch1 branch2  →  (λf. f) branch2  →  branch2
```

It works!

### Implementing NOT

```
not = λp. p false true
```

Let's trace `not true`:
```
(λp. p false true) true
→  true false true
→  (λt. λf. t) false true
→  (λf. false) true
→  false
```

Let's trace `not false`:
```
(λp. p false true) false
→  false false true
→  (λt. λf. f) false true
→  (λf. f) true
→  true
```

### Implementing AND

```
and = λp. λq. p q false
```

Why does this work? Think through the cases:

**Case 1**: `and true true`
```
(λp. λq. p q false) true true
→  (λq. true q false) true
→  true true false
→  (λt. λf. t) true false
→  true
```

**Case 2**: `and true false`
```
(λp. λq. p q false) true false
→  true false false
→  (λt. λf. t) false false
→  false
```

**Case 3**: `and false true`
```
(λp. λq. p q false) false true
→  (λq. false q false) true
→  false true false
→  (λt. λf. f) true false
→  false
```

**Case 4**: `and false false`
```
→  false
```

### Implementing OR

```
or = λp. λq. p true q
```

**Intuition**: If `p` is true, return true. Otherwise, return `q`.

Try tracing through the cases yourself!

---

## Part 7: Church Numerals

### The Encoding

A Church numeral represents number `n` as a function that applies another function `n` times:

```
0 = λf. λx. x           (apply f zero times)
1 = λf. λx. f x         (apply f once)
2 = λf. λx. f (f x)     (apply f twice)
3 = λf. λx. f (f (f x)) (apply f three times)
```

### Visualizing It

Think of `2` as: "Give me a function f and a starting value x, I'll apply f twice"

```javascript
// In JavaScript
const two = f => x => f(f(x));

// Use it:
const increment = n => n + 1;
two(increment)(0);  // → increment(increment(0)) → increment(1) → 2
```

### Successor (Adding 1)

```
succ = λn. λf. λx. f (n f x)
```

Let's trace `succ 0`:
```
(λn. λf. λx. f (n f x)) (λf. λx. x)
→  λf. λx. f ((λf. λx. x) f x)
→  λf. λx. f ((λx. x) x)
→  λf. λx. f x
= 1
```

It works!

Let's trace `succ 1`:
```
(λn. λf. λx. f (n f x)) (λf. λx. f x)
→  λf. λx. f ((λf. λx. f x) f x)
→  λf. λx. f ((λx. f x) x)
→  λf. λx. f (f x)
= 2
```

### Addition

```
plus = λm. λn. λf. λx. m f (n f x)
```

**Intuition**: Apply f `n` times to x, then apply f `m` more times.

Let's trace `plus 1 2`:
```
(λm. λn. λf. λx. m f (n f x)) (λf. λx. f x) (λf. λx. f (f x))
→  (λn. λf. λx. (λf. λx. f x) f (n f x)) (λf. λx. f (f x))
→  λf. λx. (λf. λx. f x) f ((λf. λx. f (f x)) f x)
→  λf. λx. (λx. f x) ((λf. λx. f (f x)) f x)
→  λf. λx. (λx. f x) ((λx. f (f x)) x)
→  λf. λx. (λx. f x) (f (f x))
→  λf. λx. f (f (f x))
= 3
```

### Multiplication

```
mult = λm. λn. λf. m (n f)
```

**Intuition**: Compose the function f with itself `n` times, then do that `m` times.

For `mult 2 3`:
- 3 means "apply f three times"
- 2 means "do that twice"
- Result: apply f six times

### Is-Zero

```
isZero = λn. n (λx. false) true
```

**Intuition**:
- If n = 0, we apply the function 0 times, so we return `true`
- If n > 0, we apply `(λx. false)` at least once, which ignores its argument and returns `false`

Let's trace `isZero 0`:
```
(λn. n (λx. false) true) (λf. λx. x)
→  (λf. λx. x) (λx. false) true
→  (λx. x) true
→  true
```

Let's trace `isZero 1`:
```
(λn. n (λx. false) true) (λf. λx. f x)
→  (λf. λx. f x) (λx. false) true
→  (λx. (λx. false) x) true
→  (λx. false) true
→  false
```

---

## Part 8: Pairs and Lists

### Church Pairs

```
pair = λx. λy. λf. f x y
fst  = λp. p (λx. λy. x)
snd  = λp. p (λx. λy. y)
```

**Intuition**: A pair is a function that takes a function and applies it to both elements.

Let's trace `fst (pair a b)`:
```
(λp. p (λx. λy. x)) ((λx. λy. λf. f x y) a b)
→  (λp. p (λx. λy. x)) (λf. f a b)
→  (λf. f a b) (λx. λy. x)
→  (λx. λy. x) a b
→  (λy. a) b
→  a
```

### Church Lists

```
nil  = λc. λn. n
cons = λh. λt. λc. λn. c h (t c n)
```

**Intuition**: A list is its own fold function!

- `nil` takes a combining function `c` and a nil value `n`, returns `n`
- `cons h t` takes `c` and `n`, returns `c h (t c n)` (combine head with folded tail)

Example: `cons 1 (cons 2 (cons 3 nil))`

This represents `[1, 2, 3]`

When we fold with `+` and `0`:
```
fold (+) 0 [1,2,3]  =  1 + (2 + (3 + 0))  =  6
```

In lambda calculus:
```
list (+) 0  =  1 + (2 + (3 + 0))  =  6
```

The list IS the fold!

### List Length

```
length = λl. l (λh. λt. succ t) 0
```

**Intuition**: Fold over the list, incrementing for each element, starting with 0.

---

## Part 9: The Y Combinator and Recursion

### The Problem

How do we write recursive functions if we can't refer to names?

In normal programming:
```javascript
function factorial(n) {
  if (n === 0) return 1;
  else return n * factorial(n - 1);  // Refers to itself!
}
```

But in pure lambda calculus, we have no names!

### The Fixed-Point Approach

A fixed point of function `f` is a value `x` such that `f x = x`.

For example, fixed point of `λx. x * x` is 0 and 1:
- 0 * 0 = 0
- 1 * 1 = 1

For recursive functions, we want to find `F` such that:
```
F = (λf. λn. if (isZero n) 1 (mult n (f (pred n)))) F
```

The Y combinator finds this fixed point!

### The Y Combinator

```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

**Key property**: `Y f = f (Y f)`

Let's verify:
```
Y f
= (λf. (λx. f (x x)) (λx. f (x x))) f
→ (λx. f (x x)) (λx. f (x x))
→ f ((λx. f (x x)) (λx. f (x x)))
= f (Y f)
```

### Using Y for Recursion

To write factorial:

Step 1: Write the "one step" function:
```
factStep = λf. λn. if (isZero n) 1 (mult n (f (pred n)))
```

Note: `f` is the "recursive call" - we assume we have factorial for smaller numbers

Step 2: Apply Y:
```
factorial = Y factStep
```

Step 3: It works!
```
factorial 3
= Y factStep 3
= factStep (Y factStep) 3
= factStep factorial 3
= if (isZero 3) 1 (mult 3 (factorial 2))
→ mult 3 (factorial 2)
→ mult 3 (mult 2 (factorial 1))
→ mult 3 (mult 2 (mult 1 (factorial 0)))
→ mult 3 (mult 2 (mult 1 1))
→ mult 3 (mult 2 1)
→ mult 3 2
→ 6
```

### The Z Combinator (for Call-by-Value)

The Y combinator doesn't work with call-by-value because it immediately expands infinitely.

For call-by-value, use the Z combinator:
```
Z = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
```

The extra `λy` creates a value (a function), preventing infinite expansion.

---

## Part 10: Theoretical Properties

### Confluence (Church-Rosser Theorem)

**Theorem**: If a term can reduce to multiple different terms, those terms can always "join back up" to a common term.

Diagram:
```
      t
     / \
    /   \
   t₁   t₂
    \   /
     \ /
      t'
```

**Consequence**: If a term has a normal form, that normal form is unique (up to renaming of variables).

### Why This Matters

Without confluence, we'd have:
```
term  →  result1
term  →  result2
```

And `result1` and `result2` would be different! The language would be non-deterministic.

Confluence guarantees that regardless of reduction order (if it terminates), we get the same answer.

### Standardization Theorem

**Theorem**: If a term has a normal form, normal-order (leftmost-outermost) reduction will find it.

**Consequence**: Normal-order evaluation is "complete" for terminating programs.

### Non-Termination

Not all terms normalize!

**Omega (Ω)**: The infinite loop
```
Ω = (λx. x x) (λx. x x)
→ (λx. x x) (λx. x x)
→ (λx. x x) (λx. x x)
→ ...
```

This keeps reducing to itself forever!

**More subtle**:
```
Y f  →  f (Y f)  →  f (f (Y f))  →  ...
```

Y combinator also doesn't terminate (which is the point - it enables general recursion).

---

## Part 11: Putting It All Together

### Complete Example: Factorial

Let's implement factorial completely in lambda calculus:

```
# Booleans
true  = λt. λf. t
false = λt. λf. f
if    = λp. λt. λf. p t f

# Numbers
0 = λf. λx. x
1 = λf. λx. f x
succ = λn. λf. λx. f (n f x)
mult = λm. λn. λf. m (n f)

# Predecessor (simplified - actual implementation is complex)
pred = ... (see exercises)

# Is-zero test
isZero = λn. n (λx. false) true

# Fixed-point combinator
Z = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))

# Factorial
factStep = λf. λn. if (isZero n) 1 (mult n (f (pred n)))
factorial = Z factStep

# Compute factorial 3
factorial 3  →*  6
```

### How to Approach Problems

1. **Understand the data encoding**
   - Booleans select between branches
   - Numbers are "apply f n times"
   - Lists are their own fold

2. **Think about behavior, not structure**
   - Don't think "a boolean is true or false"
   - Think "a boolean chooses between two options"

3. **Work through examples**
   - Trace reductions step by step
   - Verify your encoding works

4. **Use the REPL**
   - Test small pieces
   - Build up to complex terms

5. **Don't be afraid of complexity**
   - Some encodings (like `pred`) are genuinely hard
   - It's okay to look at solutions!

---

## Next Steps

You should now understand:
- ✓ How to write and parse lambda terms
- ✓ How to compute free variables
- ✓ How to perform substitution (avoiding capture)
- ✓ How to apply β-reduction
- ✓ The difference between evaluation strategies
- ✓ How to encode data using Church encodings
- ✓ How to achieve recursion with Y combinator
- ✓ The theoretical properties of lambda calculus

**Ready for exercises?** Go to `exercises/EXERCISES.md` and test your understanding!

**Need more practice?** Use the REPL (`stack run`) to experiment with these concepts interactively.

**Ready for Chapter 2?** Learn how types prevent infinite loops and guarantee termination!
