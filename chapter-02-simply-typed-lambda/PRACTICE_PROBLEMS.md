# Chapter 2: Simply Typed Lambda Calculus - Practice Problems

## Purpose
Practice type checking, type safety proofs, and STLC programming beyond main exercises.

---

## Warm-Up Problems (15 minutes)

### Problem 1.1: Type Checking ⭐
Type check or explain why these fail:

a) `\x:Nat. if (iszero x) then zero else x`
b) `\f:Nat->Bool. \x:Nat. if (f x) then x else zero`
c) `\x:Bool. \y:Nat. if x then y else succ y`
d) `\x:Bool. if x then (\y:Nat. y) else (\z:Bool. z)`

### Problem 1.2: Type Derivations ⭐
Write complete type derivation trees for:

a) `\x:Nat. succ x`
b) `(\f:Nat->Nat. f zero) (\x:Nat. succ x)`

### Problem 1.3: Type Inhabitants ⭐
Give a term of each type (or explain why impossible):

a) `Nat -> Nat`
b) `Bool -> Nat -> Nat`
c) `(Nat -> Bool) -> Nat`
d) `Nat -> (Nat -> Nat)`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Arithmetic Operations ⭐⭐
Implement in STLC:

a) **min**: `min : Nat -> Nat -> Nat`
b) **abs_diff**: `abs_diff : Nat -> Nat -> Nat`
c) **div2**: Integer division by 2 (hint: repeated subtraction)

### Problem 2.2: Boolean Logic ⭐⭐
Implement:

a) **implies**: `implies : Bool -> Bool -> Bool`
b) **nand**: `nand : Bool -> Bool -> Bool`
c) **majority3**: Takes 3 bools, returns true if ≥2 are true

### Problem 2.3: Higher-Order Functions ⭐⭐
Implement:

a) **apply_twice**: `(Nat -> Nat) -> Nat -> Nat`
b) **apply_n_times**: Takes n:Nat and function, applies n times
c) **iterate_until**: Applies function until predicate holds

### Problem 2.4: Type Safety Exploration ⭐⭐
For each, determine if it's a value, can step, or is stuck:

a) `if true then zero else false`
b) `(\x:Nat. x) (if true then zero else succ zero)`
c) `succ false`
d) `(\x:Bool. x) true`

### Problem 2.5: Progress Proof ⭐⭐
Prove Progress for:
```
If ⊢ t : T, then either:
  1) t is a value, or
  2) ∃ t' such that t → t'
```

Show for the case where `t = if t1 then t2 else t3`.

### Problem 2.6: Preservation Proof ⭐⭐
Prove Preservation for:
```
If ⊢ t : T and t → t', then ⊢ t' : T
```

Show for the case where `t = pred (succ n)`.

### Problem 2.7: Type Uniqueness ⭐⭐
Prove: In STLC, every well-typed term has a unique type.

Hint: Induction on typing derivation.

### Problem 2.8: Normalization ⭐⭐
Prove that this term terminates:
```
(\f:Nat->Nat. \x:Nat. f (f x)) (\y:Nat. pred y) (succ (succ zero))
```

Show the complete reduction sequence.

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Strong Normalization ⭐⭐⭐
Prove (sketch) that all well-typed STLC terms terminate.

Use logical relations:
- Define `⟦T⟧` for each type T
- Show closed terms of type T are in `⟦T⟧`
- Show `⟦T⟧` terms normalize

### Problem 3.2: Adding Fix ⭐⭐⭐
If we add `fix : (T -> T) -> T`, STLC loses normalization:

a) Show: `fix (\x:Nat. x)` diverges
b) Implement: `factorial` using fix
c) Prove: Progress still holds
d) Explain: Why does Preservation break?

### Problem 3.3: Canonical Forms ⭐⭐⭐
Prove the Canonical Forms Lemma:

a) If `v : Nat` is a value, then v is either `zero` or `succ v'`
b) If `v : Bool` is a value, then v is either `true` or `false`
c) If `v : T1 -> T2` is a value, then v = `\x:T1. t`

Use this to prove Progress.

### Problem 3.4: Type Erasure ⭐⭐⭐
Define erasure `erase(t)` that removes types:
- `erase(\x:T. t) = \x. erase(t)`
- `erase(t1 t2) = erase(t1) erase(t2)`
- etc.

Prove: If `⊢ t : T` and `t → t'`, then `erase(t) →* erase(t')`

---

## Debugging Exercises (30 minutes)

### Debug 1: Type Error ⭐
Student wrote:
```
let double = \x:Nat. x + x in
double (if true then 1 else false)
```
What's wrong? Fix it.

### Debug 2: Infinite Loop? ⭐⭐
Student claims this loops forever:
```
(\f:Nat->Nat. f (f zero)) (\x:Nat. succ x)
```
Are they right? Explain.

### Debug 3: Type Annotation ⭐⭐
Which type annotation is wrong?
```
\f:(Nat->Nat)->Nat. \g:Nat->Nat. f (\x:Bool. g x)
```

### Debug 4: Reduction Stuck ⭐⭐
Why is this stuck?
```
(\x:Bool. succ x) true
```
Could type checking have prevented it?

### Debug 5: Progress Violation ⭐⭐
Student says this violates Progress:
```
(\x:Nat. x) false
```
Are they right? Explain.

---

## Code Review Exercises (30 minutes)

### Review 1: Max Function ⭐⭐
Student A:
```
max = \x:Nat. \y:Nat.
  if (iszero (x - y))
  then y
  else x
```

Student B:
```
max = \x:Nat. \y:Nat.
  if (x >= y) then x else y
```

Which is better? (Assume we have >= and -).

### Review 2: Higher-Order ⭐⭐
Compare these "apply twice" implementations:

**Version A**:
```
\f:Nat->Nat. \x:Nat. f (f x)
```

**Version B**:
```
\f:Nat->Nat. (\x:Nat. f x) . (\x:Nat. f x)
```

Assuming composition, which is better?

### Review 3: Type Annotations ⭐⭐
Student wrote minimal annotations:
```
let id = \x. x in id zero
```

But STLC requires:
```
let id = \x:Nat. x in id zero
```

Is there a middle ground? Discuss tradeoffs.

---

## Solutions

### Warm-Up Solutions

**1.1**:
- a) ✓ `Nat -> Nat`
- b) ✓ `(Nat -> Bool) -> Nat -> Nat`
- c) ✓ `Bool -> Nat -> Nat`
- d) ✗ Branches have different types

**1.3**:
- a) `\x:Nat. x`
- b) `\b:Bool. \n:Nat. if b then n else zero`
- c) Impossible (can't make Nat from function without applying it)
- d) `\x:Nat. \y:Nat. x` (const)

### Standard Solutions

**2.1**:
```
a) min = \x:Nat. \y:Nat. if (x <= y) then x else y
b) abs_diff = \x:Nat. \y:Nat. if (x >= y) then (x - y) else (y - x)
c) div2 = fix (\f:Nat->Nat. \n:Nat.
           if (n < 2) then 0 else succ (f (pred (pred n))))
```

**2.5**: Progress for if: Check t1 is value (true/false), then step, else step t1

**2.7**: By induction on typing derivation; typing rules deterministic

### Challenge Solutions

**3.1**: Logical relations: ⟦Nat⟧ = normalizing terms, ⟦T1→T2⟧ = functions preserving normalization

**3.2**: 
- a) `fix (\x:Nat. x) → (\x:Nat. x) (fix (\x:Nat. x)) → ...`
- d) Type may change during reduction with fix

**3.3**: By inversion on typing rules

**3.4**: Simulation: typed reductions correspond to untyped

### Debug Solutions

**Debug 1**: `false` should be `succ zero` or similar Nat

**Debug 2**: No! Terminates in 2 steps to `succ (succ zero)`

**Debug 3**: `\x:Bool. g x` should be `\x:Nat. g x`

**Debug 4**: Type error! Should be caught by type checker

**Debug 5**: No - this IS a type error, never gets to evaluation

### Code Review Solutions

**Review 1**: B is cleaner if we have >= primitive

**Review 2**: A is better (simpler, more direct)

**Review 3**: Type inference (Chapter 4) is the middle ground!

---

**Time**: 3-5 hours total
**Focus**: Type safety proofs are key differentiator from Ch1
