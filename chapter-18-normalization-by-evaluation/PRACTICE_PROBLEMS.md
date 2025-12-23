# Chapter 18: Normalization by Evaluation - Practice Problems

## Purpose

Additional practice beyond the main exercises to reinforce NbE concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Phase Identification ⭐

Identify which phase (eval or quote) each operation belongs to:

a) Converting `TLam "x" (TVar 0)` to `VLam "x" (Closure [] (TVar 0))`
b) Applying a closure to a fresh neutral variable
c) Converting `VNe (NVar 0)` to `NfNe (NeVar 0)`
d) Looking up a variable in the environment

### Problem 1.2: Data Type Matching ⭐

Match each value to its type:

a) `VLam "x" (Closure [] (TVar 0))`
b) `NfLam "x" (NfNe (NeVar 0))`
c) `TLam "x" (TVar 0)`
d) `VNe (NVar 0)`

Types: `Term`, `Val`, `Nf`, `Neutral`

### Problem 1.3: Index/Level Conversion ⭐

Convert at depth 3:

a) Level 0 → Index ?
b) Level 2 → Index ?
c) Index 0 → Level ?
d) Index 2 → Level ?

Formula: `index = depth - level - 1`

### Problem 1.4: Closure Components ⭐

What environment should each closure capture?

a) `eval [] (TLam "x" (TVar 0))`
b) `eval [VInt 5] (TLam "y" (TVar 1))`
c) `eval [VTrue, VInt 3] (TLam "z" (TVar 0))`

### Problem 1.5: Neutral or Normal? ⭐

Classify as neutral (stuck) or normal:

a) `λx. x`
b) `x 5` (where `x` is free)
c) `42`
d) `(λx. x) y` (where `y` is free)

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Eval Trace ⭐⭐

Trace `eval [] (TApp (TLam "x" (TVar 0)) (TLit 5))` step-by-step.

Show intermediate values and closure applications.

### Problem 2.2: Quote Trace ⭐⭐

Trace `quote 0 (VLam "x" (Closure [] (TVar 0)))`.

Show:
- Fresh variable creation
- Closure application
- Recursive quote call
- Index conversion

### Problem 2.3: Normalize Church Numerals ⭐⭐

Normalize these Church numerals:

a) `λf. λx. f x` (one)
b) `(λn. λf. λx. f (n f x)) (λf. λx. f x)` (succ one)
c) `(λm. λn. λf. m (n f)) (λf. λx. f x) (λf. λx. f x)` (mult one one)

### Problem 2.4: Environment Extension ⭐⭐

Trace the environment changes when evaluating:

```
(λx. (λy. x + y) 3) 5
```

Show the environment at each lambda application.

### Problem 2.5: Neutral Propagation ⭐⭐

Trace `eval [VNe (NVar 0)] (TApp (TVar 0) (TLit 5))`.

Show how neutrals propagate through application.

### Problem 2.6: Fresh Variable Generation ⭐⭐

Quote `VLam "f" (Closure [] (TLam "x" (TApp (TVar 1) (TVar 0))))` at level 0.

Show:
- Level for `f`'s fresh variable
- Level for `x`'s fresh variable
- Final de Bruijn indices

### Problem 2.7: De Bruijn Index Calculation ⭐⭐

For `λx. λy. λz. x z (y z)`, show:

a) Indices in the term
b) Levels when evaluated
c) Indices after quoting from level 0

### Problem 2.8: Closure Application Chain ⭐⭐

Trace `applyClosure (Closure [VInt 5] (TVar 0)) (VInt 3)`.

What happens to the environment?

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: NbE for Simply-Typed Lambda Calculus ⭐⭐⭐

Implement type-directed NbE:

a) Define `quoteTyped :: Type -> Lvl -> Val -> Nf`
b) Add eta-expansion for function types
c) Normalize `f` where `f : A → B` and `f` is neutral
d) Show that `f` and `λx. f x` are now equal

### Problem 3.2: NbE with Pairs ⭐⭐⭐

Extend NbE with product types:

a) Add `TPair`, `TFst`, `TSnd` to terms
b) Add `VPair` to values
c) Add `NfPair` to normal forms
d) Implement eval and quote for pairs
e) Normalize `fst (pair true false)`

### Problem 3.3: Normalization Proof (Informal) ⭐⭐⭐

Argue informally that NbE always produces normal forms:

a) Define what "normal form" means
b) Show `eval` always terminates for terminating terms
c) Show `quote` always terminates
d) Show result of `quote` has no redexes

### Problem 3.4: NbE with Natural Numbers ⭐⭐⭐

Add natural numbers to NbE:

a) Represent naturals in semantic domain
b) Add `zero`, `suc`, and `rec` (recursion)
c) Implement eval for `rec n z (λm. λr. s)`
d) What happens when `n` is neutral?

### Problem 3.5: Call-by-Name NbE ⭐⭐⭐

Adapt NbE for call-by-name:

a) Change closure representation to delay evaluation
b) Modify `vApp` to use thunks
c) Show `(λx. 42) diverge` normalizes to `42`
d) What's the difference in the semantic domain?

### Problem 3.6: Conversion Checking ⭐⭐⭐

Implement definitional equality:

a) `conv :: Ctx -> Val -> Val -> Bool`
b) Handle η-equality for functions
c) Show `λx. f x ≡ f` when `x ∉ FV(f)`
d) Test on `(λx. (λy. x) y)` and `λx. x`

---

## Debugging Exercises (30 minutes)

### Debug 1: Missing Environment ⭐

What's wrong?

```haskell
eval env (TLam x t) = VLam x (Closure [] t)
```

### Debug 2: Wrong Level Increment ⭐⭐

What's the bug?

```haskell
quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)
      body = applyClosure closure freshVar
  in NfLam x (quote lvl body)  -- BUG HERE
```

### Debug 3: Index/Level Confusion ⭐⭐

Student wrote:

```haskell
quoteNe lvl (NVar l) = NeVar l  -- Direct use of level
```

Why is this wrong? What's the fix?

### Debug 4: Neutral Evaluation ⭐⭐

What's wrong?

```haskell
vApp (VNe neutral) arg =
  case neutral of
    NVar l -> eval ... -- Try to evaluate variable
```

### Debug 5: Environment Lookup ⭐⭐

Student's eval:

```haskell
eval env (TVar i) = env !! (length env - i - 1)
```

Is this correct? Test on `λx. λy. x`.

---

## Proof Exercises (45 minutes)

### Proof 1: Eval Deterministic ⭐⭐

Prove (informally) that `eval env t` always gives the same result.

Hint: By induction on term structure.

### Proof 2: Quote Deterministic ⭐⭐

Prove that `quote lvl v` always gives the same normal form.

### Proof 3: Normalization Commutes ⭐⭐⭐

Prove that for closed terms:

```
normalize t ≡ normalize (normalize t)
```

Hint: Show `quote lvl (eval env (quote lvl v))` ≡ `quote lvl v`.

### Proof 4: Soundness ⭐⭐⭐

Prove that normalization preserves meaning:

If `t →* u` by beta reduction, then `normalize t = normalize u`.

### Proof 5: Completeness ⭐⭐⭐

Prove that normalization finds the normal form:

If `t` has a normal form `u`, then `normalize t = u`.

---

## Code Review Exercises (30 minutes)

### Review 1: Closure Application ⭐⭐

Two implementations:

**Version A**:
```haskell
applyClosure (Closure env body) arg = eval (arg : env) body
```

**Version B**:
```haskell
applyClosure (Closure env body) arg = eval (env ++ [arg]) body
```

Which is correct? Why?

### Review 2: Quote Implementation ⭐⭐

Student's code:

```haskell
quote lvl (VLam x closure) =
  let body = applyClosure closure (VNe (NVar (lvl + 1)))
  in NfLam x (quote (lvl + 1) body)
```

Is this correct? What about the fresh variable level?

### Review 3: Optimization ⭐⭐⭐

Student optimized:

```haskell
eval env (TApp (TLam x body) arg) =
  eval (eval env arg : env) body  -- Inline beta reduction
```

Is this safe? Does it preserve semantics?

---

## Conversion Exercises (30 minutes)

### Convert 1: Substitution to NbE ⭐⭐

Convert this substitution-based reduction to NbE:

```
(λx. x + x) 3
→ 3 + 3
→ 6
```

Show eval and quote steps.

### Convert 2: Reduction Rules to Eval ⭐⭐

Given these reduction rules:

```
(λx. t) u → t[x := u]
fst (pair t u) → t
snd (pair t u) → u
```

How does eval implement each without explicit substitution?

### Convert 3: Normal Form to Value ⭐⭐⭐

Given a normal form, how do you convert it back to a value?

Why might this be useful?

---

## Solutions

### Warm-Up Solutions

**1.1**: a) eval, b) quote, c) quote, d) eval

**1.2**: a) Val, b) Nf, c) Term, d) Val (VNe contains Neutral)

**1.3**:
- a) 2, b) 0, c) 2, d) 0

**1.4**:
- a) `[]`, b) `[VInt 5]`, c) `[VTrue, VInt 3]`

**1.5**: a) normal, b) neutral, c) normal, d) neutral

### Standard Solutions

**2.1**:
```
eval [] (TApp (TLam "x" (TVar 0)) (TLit 5))
= vApp (eval [] (TLam "x" (TVar 0))) (eval [] (TLit 5))
= vApp (VLam "x" (Closure [] (TVar 0))) (VInt 5)
= applyClosure (Closure [] (TVar 0)) (VInt 5)
= eval [VInt 5] (TVar 0)
= VInt 5
```

**2.2**:
```
quote 0 (VLam "x" (Closure [] (TVar 0)))

freshVar = VNe (NVar 0)
body = applyClosure (Closure [] (TVar 0)) (VNe (NVar 0))
     = eval [VNe (NVar 0)] (TVar 0)
     = VNe (NVar 0)

quote 1 (VNe (NVar 0))
= quoteNe 1 (NVar 0)
= NeVar (1 - 0 - 1) = NeVar 0

Result: NfLam "x" (NfNe (NeVar 0))
```

**2.3**:
- a) `λf. λx. f x`
- b) `λf. λx. f (f x)` (two)
- c) `λf. λx. f x` (one)

**2.5**: `VNe (NApp (NVar 0) (VInt 5))` - neutral propagates

**2.7**:
```
Term indices: λ. λ. λ. 2 0 (1 0)
Eval levels at depth 3: x=0, y=1, z=2
Quote indices: Same as original: 2 0 (1 0)
```

### Challenge Solutions

**3.1**: Add type argument to quote:
```haskell
quoteTyped (TyArr a b) lvl (VNe neu) =
  NfLam "x" (quoteTyped b (lvl+1) (vApp (VNe neu) (VNe (NVar lvl))))
```

**3.2**:
```haskell
eval env (TPair t1 t2) = VPair (eval env t1) (eval env t2)
eval env (TFst t) = case eval env t of
  VPair v1 v2 -> v1
  VNe neu -> VNe (NFst neu)

quote lvl (VPair v1 v2) = NfPair (quote lvl v1) (quote lvl v2)
```

**3.5**: Use thunks in closures, delay argument evaluation until needed

### Debug Solutions

**Debug 1**: Should capture `env`, not `[]`

**Debug 2**: Should be `quote (lvl + 1) body`

**Debug 3**: Should be `NeVar (lvl - l - 1)` to convert level to index

**Debug 4**: Can't eval neutral - just build `VNe (NApp neutral arg)`

**Debug 5**: Incorrect - de Bruijn indices are 0-based from the front. Should be just `env !! i`

### Proof Solutions

**Proof 1**: By induction. Each case is deterministic: lookup is deterministic, vApp is deterministic, etc.

**Proof 3**: Quoting a value gives its normal form. Evaling a normal form gives back (morally) the same value.

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 6 hard, 5 debug, 5 proof

**Note**: Focus on understanding eval/quote phases and the role of fresh variables!
