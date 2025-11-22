# Chapter 1: Untyped Lambda Calculus - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce lambda calculus concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Basic Reduction ⭐
Reduce these terms to normal form:

a) `(\x. x) (\y. y y)`
b) `(\f. \x. f x) (\z. z) (\a. a)`
c) `(\x. \y. x) (\a. a a) (\b. b)`

### Problem 1.2: Alpha Conversion ⭐
Are these pairs alpha-equivalent? Why or why not?

a) `\x. x` and `\y. y`
b) `\x. \y. x y` and `\y. \x. y x`
c) `\x. \x. x` and `\y. \y. y`

### Problem 1.3: Free Variables ⭐
Identify free variables in each term:

a) `x y z`
b) `\x. x y`
c) `\x. \y. x z (\z. z y)`

### Problem 1.4: Substitution Practice ⭐
Perform these substitutions:

a) `(\x. x y)[y := \z. z]`
b) `(\x. x x)[x := \y. y]`
c) `(\x. \y. x y)[x := y]` (watch out for capture!)

### Problem 1.5: Church Booleans ⭐
Evaluate these using Church boolean definitions:

a) `and true true`
b) `or false true`
c) `not false`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Church Numeral Arithmetic ⭐⭐
Implement these operations on Church numerals:

a) **isZero**: Returns `true` if numeral is zero, `false` otherwise
b) **leq** (less than or equal): `leq m n` returns `true` if m ≤ n
c) **sub**: Subtraction (result is 0 if m < n)

Test your implementations:
- `isZero zero` → `true`
- `leq two three` → `true`
- `sub five two` → `three`

### Problem 2.2: Church Pairs and Lists ⭐⭐
Implement these list operations:

a) **length**: Count elements in a Church-encoded list
b) **append**: Concatenate two lists
c) **reverse**: Reverse a list

Test cases:
- `length [1,2,3]` → `three`
- `append [1,2] [3,4]` → `[1,2,3,4]`
- `reverse [1,2,3]` → `[3,2,1]`

### Problem 2.3: Evaluation Strategies ⭐⭐
For the term `(\x. \y. y) ((\z. z z) (\z. z z))`:

a) Show reduction under **normal order**
b) Show reduction under **call-by-value**
c) Explain why one terminates and the other doesn't

### Problem 2.4: Combinators ⭐⭐
Implement these famous combinators:

a) **B combinator** (composition): `B f g x = f (g x)`
b) **C combinator** (flip): `C f x y = f y x`
c) **W combinator** (duplication): `W f x = f x x`

Then express `\f. \g. \x. f (g x) (g x)` using S, K, and these combinators.

### Problem 2.5: Y Combinator Variants ⭐⭐
a) Implement the **Z combinator** (call-by-value Y)
b) Use it to define **fibonacci**
c) Trace the first 3 steps of `fibonacci 3`

### Problem 2.6: Church Numerals to Peano ⭐⭐
Write a function that converts a Church numeral to Peano representation:
- Peano: `zero` or `succ n`
- Church: `\f x. f^n x`

Hint: Use a pair to track `(count, result)`.

### Problem 2.7: Option Type Encoding ⭐⭐
Encode an Option/Maybe type in pure lambda calculus:

a) Define `none` and `some`
b) Implement `map_option`
c) Implement `bind_option`

Example: `map_option (\x. succ x) (some two)` → `some three`

### Problem 2.8: Tree Encoding ⭐⭐
Encode binary trees:

a) Define `leaf` and `node`
b) Implement `tree_map`
c) Implement `tree_fold`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Church Rosser ⭐⭐⭐
Prove (informally) that these terms have the same normal form:

```
t1 = (\x. (\y. y) x) ((\z. z) (\a. a))
t2 = (\y. y) ((\z. z) (\a. a))
```

Show two different reduction paths that reach the same result.

### Problem 3.2: Scott Encoding ⭐⭐⭐
Scott numerals differ from Church numerals. Implement:

a) Scott numerals (data structure encoding)
b) `pred` operation (should be O(1)!)
c) Compare efficiency with Church numerals

### Problem 3.3: Curry's Paradox ⭐⭐⭐
The untyped lambda calculus can express logical paradoxes:

a) Encode: `Y = \f. (\x. f (x x)) (\x. f (x x))`
b) Define: `Curry = Y (\x. A → B)` for any propositions A, B
c) Explain how this proves any proposition (the paradox)
d) Why doesn't this work in typed lambda calculus?

### Problem 3.4: Lazy Evaluation Simulation ⭐⭐⭐
Create a "thunk" encoding for lazy evaluation:

a) Define `delay` and `force`
b) Implement lazy lists using thunks
c) Show how `take 3 (repeat 5)` works with lazy lists

---

## Debugging Exercises (30 minutes)

### Debug 1: Name Capture ⭐
What's wrong with this substitution?
```
(\x. \y. x) y  [substitute \z. z for x]
= \y. \z. z    ❌ Wrong!
```
Fix it properly.

### Debug 2: Incorrect Reduction ⭐⭐
Student wrote:
```
(\f. f f) (\x. \y. x)
→ (\x. \y. x) (\x. \y. x)
→ \y. \x. \y. x    ❌ Wrong!
```
What's the error? Show correct reduction.

### Debug 3: Church Numeral Bug ⭐⭐
This `mult` implementation is buggy:
```
mult = \m. \n. \f. m (n f)
```
Test it: `mult two three` doesn't give `six`. Find and fix the bug.

### Debug 4: Y Combinator Mishap ⭐⭐
Student's factorial:
```
fact = Y (\f. \n. if (iszero n) 1 (mult n (f (pred n))))
```
This doesn't work in call-by-value. Why? How to fix?

### Debug 5: Evaluation Order ⭐⭐
Explain why this behaves differently under different strategies:
```
(\x. \y. y) (omega)    where omega = (\z. z z) (\z. z z)
```

---

## Code Review Exercises (30 minutes)

### Review 1: Church Booleans ⭐⭐
A student implemented `xor`:
```
xor = \p. \q. p (q false true) (q true false)
```

Review:
- Is this correct?
- Is it optimal?
- Suggest improvements or alternatives

### Review 2: List Fold ⭐⭐
Two implementations of `sum`:

**Version A**:
```
sum = \xs. xs (\x. \acc. add x acc) zero
```

**Version B**:
```
sum = \xs. xs add zero
```

Which is better and why?

### Review 3: Predecessor ⭐⭐⭐
Student's `pred` for Church numerals:
```
pred = \n. \f. \x. n (\g. \h. h (g f)) (\u. x) (\u. u)
```

Explain:
- How does this work?
- Why is it so complex?
- Could it be simpler?

---

## Solutions

### Warm-Up Solutions

**1.1**: a) `\y. y y`, b) `\a. a`, c) `\b. b`

**1.2**: a) Yes, b) No (different meaning!), c) Yes (inner binding shadows)

**1.3**: a) `{x, y, z}`, b) `{y}`, c) `{z}`

**1.4**: 
- a) `\x. x (\z. z)`
- b) `\x. x x` (x is bound, no substitution)
- c) `\y'. y y'` (rename y to y' to avoid capture)

**1.5**: a) `true`, b) `true`, c) `true`

### Standard Solutions

**2.1**:
```
a) isZero = \n. n (\x. false) true
b) leq = \m. \n. isZero (sub m n)
c) sub = \m. \n. n pred m
```

**2.2**:
```
a) length = \xs. xs (\h. \t. succ (length t)) zero
b) append = \xs. \ys. xs cons ys
c) reverse = \xs. xs (\h. \t. append (reverse t) (cons h nil)) nil
```

**2.3**: Normal order terminates (doesn't eval argument), CBV diverges

**2.4**:
```
B = \f. \g. \x. f (g x)
C = \f. \x. \y. f y x  
W = \f. \x. f x x
Expression = S (B S (B B W)) (B B C)
```

**2.5**: Z = `\f. (\x. f (\y. x x y)) (\x. f (\y. x x y))`

**2.6**: Use `n (\x. succ x) zero`

**2.7**:
```
none = \n. \s. n
some = \x. \n. \s. s x
map_option = \f. \opt. opt none (\x. some (f x))
```

**2.8**:
```
leaf = \x. \l. \n. l x
node = \left. \right. \l. \n. n left right
tree_map = \f. \tree. tree (leaf . f) (\l. \r. node (tree_map f l) (tree_map f r))
```

### Challenge Solutions

**3.1**: Both reduce to `\a. a` via different paths (show steps)

**3.2**: Scott: `\s. \z. s` (succ) or `\s. \z. z` (zero), pred is `\n. n (\x. x) zero`

**3.3**: Untyped LC is inconsistent as logic (can prove false), types prevent this

**3.4**: `delay = \x. \dummy. x`, `force = \thunk. thunk unit`

### Debug Solutions

**Debug 1**: Need alpha-conversion first: `\y'. \z. z`

**Debug 2**: Forgot to reduce inside lambda: correct is `\y. \y'. y`

**Debug 3**: Should be `\m. \n. \f. m (n f)` → `\m. \n. m . n` (composition!)

**Debug 4**: Y diverges in CBV, use Z combinator

**Debug 5**: Normal order reduces to `\y. y`, CBV diverges trying to evaluate omega

### Code Review Solutions

**Review 1**: Correct but verbose; simpler: `\p. \q. p (not q) q`

**Review 2**: Version B is better (eta-reduced, pointfree style)

**Review 3**: Works by tracking "one step behind"; complexity inherent to Church numerals (Scott numerals are simpler)

---

**Estimated Time**: 3-5 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 4 hard, 5 debug, 3 review

**Note**: These problems complement the main exercises. Focus on understanding over speed!
