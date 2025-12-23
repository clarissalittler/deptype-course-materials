# Chapter 20: Denotational Semantics - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce denotational semantics concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Domain Basics ⭐
For the flat domain of naturals, determine if these are true:

a) `⊥ ⊑ 5`
b) `3 ⊑ 5`
c) `5 ⊑ 5`
d) `5 ⊑ ⊥`

### Problem 1.2: Simple Denotations ⭐
Compute these denotations (assume empty environment):

a) `[[5]]{}`
b) `[[true]]{}`
c) `[[unit]]{}`

### Problem 1.3: Variable Lookup ⭐
Compute `[[x]]ρ` where `ρ = {x ↦ 5, y ↦ true}`.

### Problem 1.4: Lambda Denotation ⭐
What is `[[λx. x]]{}` in the domain `[Nat → Nat]`?

### Problem 1.5: Application ⭐
Compute `[[(λx. x) 5]]{}`.

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Complete Denotation Computation ⭐⭐
Compute the full denotation:

```
[[(λx. λy. x) true false]]{}
```

Show all intermediate steps.

### Problem 2.2: Fixed Point Iterations (Factorial) ⭐⭐
For `F = λf. λn. if n=0 then 1 else n * f(n-1)`, compute:

a) `F⁰(⊥)`
b) `F¹(⊥)`
c) `F²(⊥)`
d) `F³(⊥)`

For each, determine the domain of definition (which inputs are defined).

### Problem 2.3: Fixed Point Iterations (Fibonacci) ⭐⭐
For `F = λf. λn. if n≤1 then 1 else f(n-1) + f(n-2)`, compute:

a) `F⁰(⊥)`
b) `F¹(⊥)`
c) `F²(⊥)`
d) `F³(⊥)`

How does this differ from factorial?

### Problem 2.4: Domain Drawing ⭐⭐
Draw the domain diagram for:

a) `Bool` (flat domain)
b) `Bool + Bool`
c) `Bool × Nat` (just show structure, not all naturals)

### Problem 2.5: Continuity Check ⭐⭐
Determine if these functions are continuous:

a) `f(x) = x + 1` on naturals
b) `g(x) = if x = ⊥ then 0 else x` on naturals
c) `h(x) = x` (identity)
d) `k(x) = ⊥` (constant ⊥)

### Problem 2.6: Conditional Strictness ⭐⭐
Compute:

a) `[[if true then 5 else ⊥]]`
b) `[[if false then ⊥ else 7]]`
c) `[[if ⊥ then 5 else 7]]`

### Problem 2.7: Arithmetic with ⊥ ⭐⭐
Compute (assuming strict arithmetic):

a) `5 + 3`
b) `⊥ + 3`
c) `5 + ⊥`
d) `⊥ + ⊥`

### Problem 2.8: Function Ordering ⭐⭐
In the domain `[Nat → Nat]`, determine if `f ⊑ g`:

a) `f = λn. ⊥` and `g = λn. n`
b) `f = λn. n` and `g = λn. n + 1`
c) `f = λn. if n=0 then 0 else ⊥` and `g = λn. n`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Sum Function Fixed Point ⭐⭐⭐
Define `sum = fix F` where `F = λf. λn. if n=0 then 0 else n + f(n-1)`.

a) Compute the first 4 iterations
b) Prove that `fⁿ(⊥)(k) = k(k+1)/2` if `k < n`, else `⊥`
c) What is `fix F`?

### Problem 3.2: Even/Odd Mutual Recursion ⭐⭐⭐
Consider mutually recursive functions:
```
even = λn. if n=0 then true else odd(n-1)
odd = λn. if n=0 then false else even(n-1)
```

Model this as a fixed point `fix F` where `F : (Nat → Bool) × (Nat → Bool) → (Nat → Bool) × (Nat → Bool)`.

a) Define F
b) Compute F⁰(⊥, ⊥), F¹(⊥, ⊥), F²(⊥, ⊥)
c) What is the fixed point?

### Problem 3.3: List Length ⭐⭐⭐
For Church-encoded lists, define:
```
length = fix (λf. λxs. xs (λh. λt. 1 + f(t)) 0)
```

a) What domain do lists inhabit?
b) Compute the first 3 fixed point iterations
c) Show that `length [1,2,3] = 3`

### Problem 3.4: Parallel-Or ⭐⭐⭐
Consider a "parallel-or" function:
```
por(true, x) = true
por(x, true) = true
por(false, false) = false
por(⊥, ⊥) = ⊥
```

a) Is this function continuous? Why or why not?
b) Can it be computed sequentially?
c) What does this say about full abstraction?

### Problem 3.5: Denotational Equivalence ⭐⭐⭐
Show that these programs have the same denotation:

a) `(λx. (λy. x)) v w` and `v`
b) `(λf. (λx. f x)) g y` and `g y`
c) `let x = e in x` and `e`

### Problem 3.6: Y Combinator ⭐⭐⭐
The Y combinator is `Y = λf. (λx. f(x x))(λx. f(x x))`.

a) Why doesn't `[[Y]]` exist in standard domain semantics?
b) What about the strict Y (Z combinator)?
c) How does Haskell's `fix` relate to Y?

---

## Implementation Exercises (60-90 minutes)

### Problem 4.1: Add Products ⭐⭐
Extend the denotational semantics with products:

a) Define the domain `D₁ × D₂`
b) Give denotation equations for `⟨e₁, e₂⟩`, `fst e`, `snd e`
c) Compute `[[fst ⟨5, true⟩]]`

### Problem 4.2: Add Sums ⭐⭐
Extend with sum types:

a) Define the domain `D₁ + D₂`
b) Give denotation equations for `inl e`, `inr e`, `case e of ...`
c) Compute `[[case inl 5 of inl x → x | inr y → 0]]`

### Problem 4.3: Add Let Bindings ⭐⭐
Give denotational semantics for:
```
let x = e₁ in e₂
```

a) Write the denotation equation
b) Show it's equivalent to `(λx. e₂) e₁`
c) Compute `[[let x = 5 in x + x]]`

### Problem 4.4: Add Lazy Lists ⭐⭐⭐
Define denotational semantics for lazy lists:

a) Define the domain `List(D) = fix X. 1 + (D × X)`
b) Give equations for `nil`, `cons`, `head`, `tail`
c) Define `take : Nat → List(D) → List(D)` denotationally
d) Show `[[take 3 (repeat 5)]] = [5, 5, 5]`

### Problem 4.5: Add State ⭐⭐⭐
Give denotational semantics for a language with mutable state:

a) Define the domain `Store → (Dom × Store)`
b) Give equations for `!e` (dereference), `e₁ := e₂` (assignment)
c) Compute `[[x := 5; !x]]` assuming initial store `{x ↦ 0}`

---

## Theoretical Exercises (45-60 minutes)

### Theory 1: Adequacy Proof Sketch ⭐⭐
Sketch a proof of adequacy:
```
e →* v  ⟹  [[e]] = [[v]]
```

Hint: Use induction on the number of reduction steps.

### Theory 2: Compositionality ⭐⭐
Prove that the denotation function is compositional for application:
```
[[e₁ e₂]]ρ = [[e₁]]ρ ([[e₂]]ρ)
```

Show this doesn't depend on the internal structure of e₁ or e₂.

### Theory 3: Fixed Point Uniqueness ⭐⭐⭐
Prove that the least fixed point is unique:

If `f(d) = d` and `∀d'. f(d') = d' ⟹ d ⊑ d'`, then `d = fix f`.

### Theory 4: Continuity Preservation ⭐⭐⭐
Prove that function composition preserves continuity:

If `f : B → C` and `g : A → B` are continuous, then `f ∘ g : A → C` is continuous.

---

## Comparison Exercises (30 minutes)

### Compare 1: Operational vs Denotational ⭐⭐
For the term `(λx. x + 1) 5`:

a) Give the operational semantics (reduction steps)
b) Give the denotational semantics
c) Show they agree (adequacy)

### Compare 2: Different Evaluation Strategies ⭐⭐
Consider `(λx. 5) ((λy. y y)(λy. y y))`:

a) What's the denotational semantics?
b) Does call-by-value evaluation terminate?
c) Does call-by-name evaluation terminate?
d) Why does denotational semantics ignore evaluation order?

### Compare 3: Non-Termination ⭐⭐
For `omega = (λx. x x)(λx. x x)`:

a) What's `[[omega]]`?
b) What's the operational semantics?
c) How does denotational semantics handle divergence?

---

## Debugging Exercises (30 minutes)

### Debug 1: Environment Error ⭐
What's wrong?
```
[[λx. x + y]]ρ = λd. [[x + y]]ρ
```

### Debug 2: Fixed Point Count ⭐⭐
Student claims: "F³(⊥) for factorial is defined on 0, 1, 2, 3."

What's the error?

### Debug 3: Comparison Error ⭐
Student writes: "In the flat domain of naturals, 1 ⊑ 2 because 1 < 2."

What's wrong?

### Debug 4: Continuity Mistake ⭐⭐
Student claims: "f(x) = if x = ⊥ then 0 else x is continuous because it's defined everywhere."

What's the error?

### Debug 5: Application Order ⭐
What's wrong?
```
[[e₁ e₂]]ρ = [[e₂]]ρ ([[e₁]]ρ)
```

---

## Solutions

### Warm-Up Solutions

**1.1**: a) True, b) False (incomparable in flat domain), c) True (reflexive), d) False

**1.2**: a) `5 ∈ Nat`, b) `true ∈ Bool`, c) `unit ∈ Unit`

**1.3**: `5 ∈ Nat`

**1.4**: `λn. n` (the identity function on naturals)

**1.5**:
```
[[(λx. x) 5]]{}
= [[λx. x]]{}([[5]]{})
= (λn. n)(5)
= 5
```

### Standard Solutions

**2.1**:
```
[[(λx. λy. x) true false]]{}
= [[λx. λy. x]]{}([[true]]{})([[false]]{})
= (λd₁. λd₂. d₁)(true)(false)
= (λd₂. true)(false)
= true
```

**2.2**:
- a) `⊥` (undefined everywhere)
- b) `λn. if n=0 then 1 else ⊥` (defined on 0)
- c) `λn. if n≤1 then ... else ⊥` (defined on 0,1)
- d) `λn. if n≤2 then ... else ⊥` (defined on 0,1,2)

Pattern: Fⁿ(⊥) defined on 0, ..., n-1

**2.3**:
- a) `⊥`
- b) `λn. if n≤1 then 1 else ⊥`
- c) `λn. if n≤1 then 1 else if n=2 then 2 else ⊥`
- d) `λn. if n≤1 then 1 else if n≤3 then ... else ⊥`

Fibonacci grows slower because it needs two previous values.

**2.5**:
- a) Continuous (monotone and preserves limits)
- b) NOT continuous (distinguishes ⊥ from defined values)
- c) Continuous (identity is always continuous)
- d) Continuous (constant functions are continuous)

**2.6**:
- a) `5` (condition is true)
- b) `7` (condition is false)
- c) `⊥` (condition is undefined)

**2.7**:
- a) `8`
- b) `⊥` (strict)
- c) `⊥` (strict)
- d) `⊥` (strict)

**2.8**:
- a) True (⊥ function is least)
- b) False (incomparable: n ⊑ n+1 is false)
- c) True (f approximates g pointwise)

### Challenge Solutions

**3.1**:
Pattern: fⁿ(⊥)(k) = sum from 0 to k if k < n, else ⊥

**3.2**:
```
F⁰(⊥,⊥) = (⊥, ⊥)
F¹(⊥,⊥) = (λn. if n=0 then true else ⊥, λn. if n=0 then false else ⊥)
F²(⊥,⊥) = functions defined on 0,1
...
fix F = (even, odd)
```

**3.5**:
All pairs are denotationally equivalent (can be proven by the denotation equations).

**3.6**:
a) Y involves self-application, which isn't continuous
b) Z uses a thunk to delay evaluation, making it work in strict settings
c) Haskell's fix uses laziness instead of domain theory

### Debug Solutions

**Debug 1**: Should extend environment: `[[x + y]]ρ[x↦d]`

**Debug 2**: Should be 0, 1, 2 (n iterations → n-1 values)

**Debug 3**: In flat domains, defined values are incomparable. Only ⊥ ⊑ everything.

**Debug 4**: The function is not continuous because it doesn't preserve limits (distinguishes ⊥).

**Debug 5**: Wrong order. Should be `[[e₁]]ρ ([[e₂]]ρ)` (function first).

---

**Estimated Time**: 5-7 hours for all problems
**Difficulty Distribution**: 5 easy, 11 medium, 8 hard, 5 debug, 4 theory, 3 comparison

**Note**: These problems focus on understanding domains, fixed points, and the mathematical foundations of denotational semantics!
