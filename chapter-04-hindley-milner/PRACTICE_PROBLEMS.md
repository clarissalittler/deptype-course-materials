# Chapter 4: Hindley-Milner Type Inference - Practice Problems

## Purpose
Practice type inference, unification, and understanding let-polymorphism.

---

## Warm-Up Problems (15 minutes)

### Problem 1.1: Infer Types ⭐
What are the most general types?

a) `\x. x`
b) `\x. \y. x`
c) `\f. \x. f x`
d) `\x. (x, x)`
e) `\f. \g. \x. f (g x)`

### Problem 1.2: Let Polymorphism ⭐
Will these type check?

a) `let id = \x. x in (id 1, id true)`
b) `(\id. (id 1, id true)) (\x. x)`
c) `let pair = \x. \y. (x, y) in pair 1 true`
d) `let f = \x. x in let g = f in g`

### Problem 1.3: Type Variables ⭐
Instantiate these types:

a) `∀a. a → a` applied to `Int`
b) `∀a b. a → b → a` applied to `Bool` and `Nat`
c) `∀a. (a → a) → a → a` applied to `String`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Algorithm W Trace ⭐⭐
Show complete Algorithm W inference for:

```
\f. \x. f (f x)
```

Include:
- Fresh type variables generated
- Constraints collected
- Unification steps
- Final type

### Problem 2.2: Unification Practice ⭐⭐
Unify these type pairs (or explain why they fail):

a) `α` and `Int`
b) `α → β` and `Int → Bool`
c) `α → α` and `Int → Bool`
d) `α` and `α → β` (occurs check!)
e) `(α → β) → γ` and `(Int → α) → Bool`

### Problem 2.3: Principal Types ⭐⭐
Find principal types:

a) `\x. \y. \z. x z (y z)`  (S combinator)
b) `\x. \y. \z. x (y z)`    (B combinator)
c) `\x. \y. y`              (K I)
d) `\f. \g. \x. f x (g x)`

### Problem 2.4: Type Schemes ⭐⭐
Generalize these monotypes:

a) `α → α` in empty context
b) `α → β` in context `{α: bound}`
c) `α → α → β` in context `{β: bound}`

### Problem 2.5: Let vs Lambda ⭐⭐
Explain why these behave differently:

a) `let f = \x. x in let g = f in (g 1, g true)`
b) `(\f. (\g. (g 1, g true)) f) (\x. x)`

Show the types assigned to f and g in each case.

### Problem 2.6: Polymorphic Lists ⭐⭐
Implement and infer types:

a) `length = \xs. if (null xs) then 0 else 1 + length (tail xs)`
b) `map = \f. \xs. if (null xs) then [] else cons (f (head xs)) (map f (tail xs))`
c) `filter = \p. \xs. if (null xs) then [] else if (p (head xs)) then cons (head xs) (filter p (tail xs)) else filter p (tail xs)`

### Problem 2.7: Type Errors ⭐⭐
Each of these should fail. Identify the unification failure:

a) `\f. f f`
b) `\x. x x`
c) `\x. (x 1, x true)`
d) `let f = \x. (x 1, x true) in f (\y. y)`

### Problem 2.8: Substitution Composition ⭐⭐
Compose these substitutions:

a) `[α ↦ Int]` ∘ `[β ↦ α]`
b) `[α ↦ β]` ∘ `[β ↦ γ]`
c) `[α ↦ β → γ]` ∘ `[γ ↦ Int]`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Value Restriction ⭐⭐⭐
Why can't we generalize non-values?

Consider:
```
let f = if random_bool () then (\x. x + 1) else (\x. x - 1) in
(f 5, f true)
```

a) If we generalize f, what goes wrong?
b) Explain the value restriction
c) Give another example where it matters

### Problem 3.2: Rank-1 Restriction ⭐⭐⭐
HM can't type:
```
\f. (f 1, f true)
```

But it can type:
```
let g = \x. x in \f. (f g, f g)
```

Explain:
a) Why the first fails (unification fails)
b) Why the second works (let-polymorphism)
c) What "rank-1" means

### Problem 3.3: Algorithm W Correctness ⭐⭐⭐
Prove (sketch) that Algorithm W is:

a) **Sound**: If W infers τ, then term has type τ
b) **Complete**: If term has type τ, W finds it (or more general)
c) **Principal**: W finds most general type

### Problem 3.4: Mutual Recursion ⭐⭐⭐
How to type mutually recursive functions in HM?

```
even = \n. if (n == 0) then true else odd (n - 1)
odd = \n. if (n == 0) then false else even (n - 1)
```

a) Show the typing challenge
b) Explain how letrec helps
c) Give the types

---

## Debugging Exercises (30 minutes)

### Debug 1: Occurs Check ⭐⭐
Student confused why this fails:
```
\x. x x
```

Explain:
- What types are generated?
- Where does unification fail?
- What's the occurs check?

### Debug 2: Monomorphism ⭐⭐
Why does this fail?
```
(\f. (f 1, f true)) (\x. x)
```

But this works?
```
let f = \x. x in (f 1, f true)
```

Explain the difference carefully.

### Debug 3: Generalization ⭐⭐
Student claims this should work:
```
\f. let g = f in (g 1, g true)
```

Why doesn't it?

### Debug 4: Instantiation ⭐⭐
What's wrong with this reasoning?

"The type `∀a. a → a` means it works for any type, so I can use it as both `Int → Int` and `Bool → Bool` in the same context."

### Debug 5: Type Inference ⭐⭐
Given:
```
let f = \x. \y. x in
let g = f 1 in
g true
```

Student thinks g : Bool → Bool. Are they right?

---

## Code Review Exercises (30 minutes)

### Review 1: List Functions ⭐⭐
Compare inferred types:

**Version A**:
```
map f xs = if null xs then [] else cons (f (head xs)) (map f (tail xs))
```

**Version B**:
```
map = \f. \xs. foldr (\x. \acc. cons (f x) acc) [] xs
```

Are the types the same? Which is better?

### Review 2: Fold Direction ⭐⭐
```
sum_left = foldl (+) 0
sum_right = foldr (+) 0
```

Do these have the same type? Same behavior? Discuss.

### Review 3: Polymorphic Comparison ⭐⭐⭐
Is this well-typed?
```
elem = \x. \xs. foldr (\y. \acc. (x == y) || acc) false xs
```

What constraint is needed on type variable?

---

## Solutions

### Warm-Up

**1.1**:
- a) `∀a. a → a`
- b) `∀a b. a → b → a`
- c) `∀a b. (a → b) → a → b`
- d) `∀a. a → a * a`
- e) `∀a b c. (b → c) → (a → b) → a → c`

**1.2**: a) ✓, b) ✗, c) ✓, d) ✓

**1.3**: a) `Int → Int`, b) `Bool → Nat → Bool`, c) `(String → String) → String → String`

### Standard

**2.1**: Generate α, β, unify to get `(α → α) → α → α`

**2.2**: a) `[α ↦ Int]`, b) `[α ↦ Int, β ↦ Bool]`, c) Fails!, d) Fails (occurs!), e) `[α ↦ Int, β ↦ Int, γ ↦ Bool]`

**2.3**: a) `∀a b c. (a → b → c) → (a → b) → a → c`, b) `∀a b c. (b → c) → (a → b) → a → c`, etc.

**2.4**: a) `∀a. a → a`, b) `α → β` (α not free), c) `α → α → β` (β not free)

**2.5**: Let generalizes to polymorphic type, lambda doesn't

**2.7**: All fail occurs check or unification

**2.8**: a) `[α ↦ Int, β ↦ Int]`, b) `[α ↦ γ, β ↦ γ]`, c) `[α ↦ β → Int, γ ↦ Int]`

### Challenge

**3.1**: Evaluation might specialize to different types at runtime

**3.2**: HM has rank-1 polymorphism only (no polymorphic arguments)

**3.3**: By induction on typing derivation

**3.4**: Use letrec for mutually recursive defs

### Debug

**Debug 1**: α = α → β fails occurs check

**Debug 2**: Lambda-bound = monomorphic, let-bound = polymorphic

**Debug 3**: f is monomorphic (lambda-bound)

**Debug 4**: Correct! That's what polymorphism means

**Debug 5**: Yes! g : Bool → Int (partially applied)

### Review

**Review 1**: Same type; B is pointfree style

**Review 2**: Same type, same result (+ is associative)

**Review 3**: Needs Eq constraint on type variable

---

**Time**: 4-6 hours
**Focus**: Understanding unification is critical
