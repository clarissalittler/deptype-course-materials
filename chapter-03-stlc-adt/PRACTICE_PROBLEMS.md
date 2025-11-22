# Chapter 3: STLC with ADTs - Practice Problems

## Purpose
Practice with products, sums, pattern matching, and structured data.

---

## Warm-Up Problems (15 minutes)

### Problem 1.1: Product Types ⭐
Type and evaluate:

a) `pair zero true`
b) `fst (pair (succ zero) false)`
c) `snd (pair true (pair zero zero))`
d) `\p:Nat*Bool. if (snd p) then (fst p) else zero`

### Problem 1.2: Sum Types ⭐
Type these (provide annotations):

a) `inl zero`
b) `inr true`
c) `case (inl zero : Nat + Bool) of inl x => succ x | inr y => zero`

### Problem 1.3: Pattern Matching ⭐
What's wrong with:
```
case (pair true zero) of
  (x, y) => if x then y else false
```

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Optional Values ⭐⭐
Implement Option/Maybe using sums:

a) Define: `Option T = T + Unit`
b) `map_option : (A -> B) -> Option A -> Option B`
c) `bind_option : Option A -> (A -> Option B) -> Option B`
d) `get_or_default : Option A -> A -> A`

### Problem 2.2: Result Type ⭐⭐
Implement error handling:

a) Define: `Result T E = T + E`
b) `map_result : (A -> B) -> Result A E -> Result B E`
c) `bind_result : Result A E -> (A -> Result B E) -> Result B E`
d) `safe_divide : Nat -> Nat -> Result Nat String`

### Problem 2.3: Nested ADTs ⭐⭐
Implement:

a) Triple: `Triple A B C = A * (B * C)`
b) `first, second, third` accessors
c) `map_triple : (A->A') -> (B->B') -> (C->C') -> Triple A B C -> Triple A' B' C'`

### Problem 2.4: Recursive Structures ⭐⭐
Using fix, implement:

a) **Lists**: `List A = Unit + (A * List A)`
b) `length : List A -> Nat`
c) `append : List A -> List A -> List A`
d) `map : (A -> B) -> List A -> List B`

### Problem 2.5: Binary Trees ⭐⭐
Implement:

a) **Tree**: `Tree A = A + (Tree A * Tree A)` (leaf or node)
b) `height : Tree A -> Nat`
c) `map_tree : (A -> B) -> Tree A -> Tree B`
d) `fold_tree : (A -> B) -> (B -> B -> B) -> Tree A -> B`

### Problem 2.6: Either Combinators ⭐⭐
Implement:

a) `either : (A -> C) -> (B -> C) -> Either A B -> C`
b) `map_left : (A -> A') -> Either A B -> Either A' B`
c) `map_right : (B -> B') -> Either A B -> Either A B'`
d) `bimap : (A -> A') -> (B -> B') -> Either A B -> Either A' B'`

### Problem 2.7: Validation ⭐⭐
Using ADTs, implement form validation:

a) `Validation E A = A + List E` (success or errors)
b) `validate_positive : Nat -> Validation String Nat`
c) `validate_non_empty : List A -> Validation String (List A)`
d) Combine validations (accumulate errors, not short-circuit)

### Problem 2.8: State Machine ⭐⭐
Model a simple state machine:

a) States: `State = Ready + Running + Done`
b) Events: `Event = Start + Stop + Reset`
c) `transition : State -> Event -> Option State`
d) `is_final : State -> Bool`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Exhaustiveness Checking ⭐⭐⭐
Design an algorithm to check if pattern matches are exhaustive:

a) For sum types: Check all constructors covered
b) For nested patterns: Recurse
c) Give counterexample if non-exhaustive

Example:
```
case x : Bool + Nat of
  inl true => ...
  inl false => ...
  inr n => ...
```
✓ Exhaustive

```
case x : Bool + Nat of
  inl true => ...
```
✗ Non-exhaustive (missing inl false and inr cases)

### Problem 3.2: Generic Data Structures ⭐⭐⭐
Implement without built-in lists:

a) **Stack**: Using products/sums
b) **Queue**: Using two stacks
c) **Set**: Using balanced trees (sketch)

Prove time complexities.

### Problem 3.3: Expression Evaluator ⭐⭐⭐
Define expression language:

```
Expr = Lit Nat
     | Add Expr Expr
     | Mul Expr Expr
     | Ite Expr Expr Expr  -- if-then-else
```

Implement:
a) `eval : Expr -> Option Nat` (None if type error)
b) `optimize : Expr -> Expr` (constant folding)
c) `contains_zero : Expr -> Bool`

### Problem 3.4: Dependent Pairs Preview ⭐⭐⭐
Simulate dependent pairs using non-dependent ADTs:

```
DPair = ∃A. A * (A -> Type)
```

Can we encode: "Pair of Nat n and Vec of length n"?

Sketch approach (full solution needs dependent types).

---

## Debugging Exercises (30 minutes)

### Debug 1: Type Annotation ⭐
Fix:
```
\x. case x of
  inl a => a
| inr b => not b
```

### Debug 2: Non-Exhaustive ⭐⭐
What's wrong?
```
\x:Bool + Nat. case x of
  inl true => zero
```

### Debug 3: Type Mismatch ⭐⭐
Why doesn't this type?
```
\x:Nat * Bool. case x of
  (n, b) => if b then n else b
```

### Debug 4: Nested Matching ⭐⭐
Student wrote:
```
\x:(Nat + Bool) * Unit. case x of
  (inl n, unit) => n
| (inr b, unit) => zero
```

Error! Fix it (need nested case).

### Debug 5: Option Chaining ⭐⭐
This doesn't compile:
```
bind (bind mx f) g
```
What types are needed?

---

## Code Review Exercises (30 minutes)

### Review 1: Safe Head ⭐⭐
Compare:

**Version A** (returns Option):
```
safe_head : List A -> Option A
safe_head = case xs of
  nil => none
| cons x xs' => some x
```

**Version B** (total with default):
```
head_or : List A -> A -> A
head_or = \xs. \default. case xs of
  nil => default
| cons x xs' => x
```

Which is better?

### Review 2: Either vs Option ⭐⭐
When should you use `Either E A` vs `Option A`?

Give 3 examples where Either is better.

### Review 3: Pattern Match Order ⭐⭐⭐
Does order matter?

```
-- Version A
case x of
  inl _ => foo
| inr (inl _) => bar
| inr (inr n) => baz n

-- Version B  
case x of
  inr (inr n) => baz n
| inr (inl _) => bar
| inl _ => foo
```

Discuss efficiency and readability.

---

## Solutions

### Warm-Up

**1.1**: a) `Nat*Bool`, b) `Nat` (value: 1), c) `Nat*Nat` (value: (0,0)), d) `Nat*Bool -> Nat`

**1.2**: Need `: Nat + Bool` annotations

**1.3**: Branch returns Nat or Bool (mismatch)

### Standard

**2.1**:
```
a) Option T = T + Unit
b) map_option = \f. \opt. case opt of
     inl x => inl (f x)
   | inr u => inr u
c) bind_option = \opt. \f. case opt of
     inl x => f x
   | inr u => inr u
```

**2.2**: Similar to Option but keep error type

**2.4**: Use fix for recursion, pattern match on `nil` vs `cons`

**2.5**:
```
height = fix (\f. \t. case t of
  inl leaf => 1
| inr (l, r) => 1 + max (f l) (f r))
```

### Challenge

**3.1**: Check all paths through sum type constructors covered

**3.2**: Stack is `List`, Queue is `List * List` (inbox/outbox)

**3.3**: Pattern match on Expr constructors

**3.4**: Can't fully encode without dependent types, but can approximate with casts

### Debug

**Debug 1**: Add type annotation: `\x:A+B.`

**Debug 2**: Missing cases for `inl false` and all `inr`

**Debug 3**: `else` branch returns Bool, should return Nat

**Debug 4**: Need `case fst x of ...`

**Debug 5**: Need type annotations and correct chaining

### Review

**Review 1**: A is safer (explicit failure), B is more convenient

**Review 2**: Either when you need error information

**Review 3**: Logically equivalent, readability preference varies

---

**Time**: 3-5 hours
**Key**: Pattern matching is the essential new skill
