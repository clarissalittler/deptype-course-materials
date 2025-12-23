# Chapter 17: Abstract Machines - Practice Problems

## Purpose

Additional practice beyond the main exercises to reinforce abstract machine concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: CEK State Identification ⭐

Identify which CEK state each represents:

a) `Eval (Var "x") {x ↦ 5} []`
b) `Apply [FApp2 ⟨λy.y, {}⟩] 3`
c) `Eval (Lam "z" (Var "z")) {} [FApp1 (Lit 7) {}]`

### Problem 1.2: Frame Purpose ⭐

What does each frame represent?

a) `FApp1 (Lit 5) {x ↦ 3}`
b) `FApp2 ⟨λx. x + 1, {}⟩`
c) `FAdd1 (Var "y") {y ↦ 10}`

### Problem 1.3: De Bruijn Indices ⭐

Convert to de Bruijn indices:

a) `λx. x`
b) `λx. λy. x`
c) `λx. λy. λz. x z (y z)`

### Problem 1.4: Closure Identification ⭐

What environment should each closure capture?

a) `let x = 5 in λy. x + y`
b) `λx. λy. x`
c) `(λx. λy. x + y) 10`

### Problem 1.5: Machine Selection ⭐

Which machine (CEK, SECD, Krivine) is best for:

a) Implementing Haskell's lazy evaluation
b) Building a bytecode VM for JavaScript
c) Adding call/cc to a language
d) Teaching evaluation strategies

---

## Standard Problems (45-60 minutes)

### Problem 2.1: CEK Trace ⭐⭐

Trace `(λx. x + x) 3` through the CEK machine step-by-step.

Show each state as `Eval term env kont` or `Apply kont value`.

### Problem 2.2: SECD Compilation ⭐⭐

Compile these terms to SECD instructions:

a) `λx. x + 1`
b) `(λx. x) 5`
c) `λf. λx. f (f x)`

### Problem 2.3: SECD Execution ⭐⭐

Execute the SECD instructions for `(λx. x + 1) 5`:

```
[IClosure [IAccess 0, IConst 1, IAdd, IReturn], IConst 5, IApply]
```

Show each (Stack, Env, Control, Dump) state.

### Problem 2.4: Krivine Trace ⭐⭐

Trace `(λx. λy. x) 5 10` through the Krivine machine.

Show how thunks are created and when they're evaluated.

### Problem 2.5: Evaluation Order Comparison ⭐⭐

Compare how CEK and Krivine evaluate:

```
(λx. 42) ((\y. y y) (\y. y y))
```

Why do they behave differently?

### Problem 2.6: Closure Environment ⭐⭐

Trace this program in CEK:

```
let y = 5 in
  let f = λx. x + y in
    let y = 10 in
      f 3
```

What does it return? Why?

### Problem 2.7: Continuation Frames ⭐⭐

What continuation frames are created for `(1 + 2) * 3`?

Show the frame stack at each step.

### Problem 2.8: Thunk Evaluation ⭐⭐

In Krivine, how many times is the expression `expensive` evaluated in:

```
(λx. x + x) expensive
```

How would call-by-need differ?

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: CEK with Pairs ⭐⭐⭐

Extend the CEK machine with pairs:

a) Add `Pair t1 t2`, `Fst t`, `Snd t` to terms
b) Define necessary frames
c) Write transition rules
d) Trace `fst (pair 1 2)`

### Problem 3.2: SECD with Conditionals ⭐⭐⭐

Add `If t1 t2 t3` to the SECD machine:

a) Define the `IIf0` instruction
b) Write compilation rule
c) Write execution rules
d) Compile and execute `if (zero? 0) 1 2`

### Problem 3.3: Krivine with Memoization ⭐⭐⭐

Extend Krivine to call-by-need:

a) Add a mutable cache to thunks
b) Modify variable lookup to cache results
c) Show that `(λx. x + x) expensive` now evaluates `expensive` once

### Problem 3.4: CEK with Exceptions ⭐⭐⭐

Add exception handling to CEK:

a) Add `Throw t` and `Catch t handler` constructs
b) Define a new frame `FCatch handler env`
c) Write transition rules
d) Trace `catch (throw 5) (λx. x + 1)`

### Problem 3.5: Tail Call Optimization ⭐⭐⭐

Identify tail calls in CEK and optimize them:

a) Define what makes a call a tail call
b) Modify CEK to recognize tail calls
c) Show continuation doesn't grow for tail recursive factorial
d) Compare stack depth with and without TCO

### Problem 3.6: SECD Stack Inspection ⭐⭐⭐

Add a `GetStack` operation to SECD:

a) Define `IGetStack` instruction
b) How to represent stack as a value?
c) Compile and execute `(λx. getstack) 5`

---

## Debugging Exercises (30 minutes)

### Debug 1: Wrong Environment ⭐

What's wrong with this CEK step?

```haskell
step (Apply (FApp2 (Closure x body cenv) : k) arg) =
  Eval body (extend x arg currentEnv) k
```

### Debug 2: Missing IReturn ⭐⭐

A student compiled `λx. x + 1` to:

```
[IClosure [IAccess 0, IConst 1, IAdd]]
```

What goes wrong when executed?

### Debug 3: Krivine Evaluation ⭐⭐

Student's Krivine machine evaluates arguments before pushing:

```haskell
step (State (App f t) env stack) =
  let tval = eval t env
  in State f env (Thunk tval env : stack)
```

Why is this wrong?

### Debug 4: De Bruijn Confusion ⭐⭐

Student compiled `λx. λy. x + y` to:

```
[IClosure [IClosure [IAccess 0, IAccess 1, IAdd, IReturn], IReturn]]
```

Test it on `(λx. λy. x + y) 3 5`. What's the bug?

### Debug 5: Frame Order ⭐⭐

Student's CEK evaluates arguments before functions:

```haskell
step (Eval (App f t) env k) =
  Eval t env (FApp1 f env : k)
```

Find a term where this gives wrong results.

---

## Code Review Exercises (30 minutes)

### Review 1: CEK Implementation ⭐⭐

Review this CEK implementation:

```haskell
step (Eval (Lam x t) env k) =
  Apply k (Closure x t env)

step (Apply (FApp2 (Closure x body cenv) : k) arg) =
  Eval body (insert x arg cenv) k
```

Is it correct? Any improvements?

### Review 2: SECD Compilation ⭐⭐

Two ways to compile `let x = t in body`:

**Version A**:
```haskell
compile (Let x t body) =
  compile t ++ [IClosure (compile body ++ [IReturn]), IApply]
```

**Version B**:
```haskell
compile (Let x t body) =
  [IClosure (compile body ++ [IReturn])] ++ compile t ++ [IApply]
```

Which is correct? Why?

### Review 3: Krivine Optimization ⭐⭐⭐

Student optimized Krivine by eagerly evaluating literals:

```haskell
step (State (App f (Lit n)) env stack) =
  State f env (Value n : stack)  -- Pre-evaluate literals
```

Is this safe? What evaluation strategy does it implement?

---

## Conversion Exercises (30 minutes)

### Convert 1: CEK to SECD ⭐⭐

Given a CEK trace, show the equivalent SECD execution:

```
CEK: Eval (λx. x) 5 [] → ... → Apply [] 5
```

### Convert 2: Substitution to CEK ⭐⭐

Convert this substitution-based trace to CEK:

```
(λx. (λy. x) 3) 5
→ (λy. 5) 3
→ 5
```

### Convert 3: Krivine to CEK ⭐⭐

Show how this Krivine trace would work in CEK:

```
Krivine: State (λx. 42) {} [Thunk expensive {}]
       → State 42 {x ↦ Thunk expensive {}} []
       → 42
```

---

## Solutions

### Warm-Up Solutions

**1.1**: a) Eval state, b) Apply state, c) Eval state

**1.2**:
- a) "After evaluating function, evaluate Lit 5 next"
- b) "Apply this closure to the argument"
- c) "After evaluating left side, evaluate Var y next"

**1.3**: a) `λ. 0`, b) `λ. λ. 1`, c) `λ. λ. λ. 2 0 (1 0)`

**1.4**:
- a) `{x ↦ 5}`
- b) `{}`
- c) After applying to 10: `{x ↦ 10}`

**1.5**: a) Krivine, b) SECD, c) CEK, d) CEK

### Standard Solutions

**2.1**:
```
Eval (App (Lam "x" (Add (Var "x") (Var "x"))) (Lit 3)) {} []
→ Eval (Lam "x" ...) {} [FApp1 (Lit 3) {}]
→ Apply [FApp1 (Lit 3) {}] (Closure "x" (Add ...) {})
→ Eval (Lit 3) {} [FApp2 (Closure ...)]
→ Apply [FApp2 (Closure ...)] 3
→ Eval (Add (Var "x") (Var "x")) {x ↦ 3} []
→ Eval (Var "x") {x ↦ 3} [FAdd1 (Var "x") {x ↦ 3}]
→ Apply [FAdd1 (Var "x") {x ↦ 3}] 3
→ Eval (Var "x") {x ↦ 3} [FAdd2 3]
→ Apply [FAdd2 3] 3
→ Apply [] 6
```

**2.2**:
```
a) [IClosure [IAccess 0, IConst 1, IAdd, IReturn]]
b) [IClosure [IAccess 0, IReturn], IConst 5, IApply]
c) [IClosure [IClosure [IAccess 1, IAccess 1, IAccess 0, IApply, IApply, IReturn], IReturn]]
```

**2.5**: CEK diverges (must evaluate argument), Krivine returns 42 (argument never used)

**2.6**: Returns 8. The closure captures `{y ↦ 5}`, not the later binding.

**2.8**: Twice in call-by-name. Once in call-by-need (memoized).

### Challenge Solutions

**3.1**:
```haskell
data Frame = ... | FFst | FSnd | FPair1 Term Env | FPair2 Value

step (Eval (Pair t1 t2) env k) = Eval t1 env (FPair1 t2 env : k)
step (Apply (FPair1 t2 env : k) v1) = Eval t2 env (FPair2 v1 : k)
step (Apply (FPair2 v1 : k) v2) = Apply k (VPair v1 v2)
step (Eval (Fst t) env k) = Eval t env (FFst : k)
step (Apply (FFst : k) (VPair v1 v2)) = Apply k v1
```

**3.2**:
```haskell
compile (If t1 t2 t3) = compile t1 ++ [IIf0 (compile t2) (compile t3)]

exec (IIf0 c1 c2 : c, 0 : s, e, d) = (s, e, c1 ++ c, d)
exec (IIf0 c1 c2 : c, n : s, e, d) = (s, e, c2 ++ c, d)  -- n ≠ 0
```

**3.5**: Tail call when continuation has no pending work. Replace continuation instead of extending it.

### Debug Solutions

**Debug 1**: Should extend `cenv` (closure's environment), not `currentEnv`

**Debug 2**: Missing `IReturn` - execution falls off end of closure code

**Debug 3**: Defeats laziness - should push term without evaluating

**Debug 4**: Indices should be `IAccess 1, IAccess 0` (y is 0, x is 1)

**Debug 5**: `(λx. x) (error)` - CEK evaluates error, but shouldn't in some evaluation orders

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 6 hard, 5 debug, 3 review

**Note**: These problems complement the main exercises. Focus on understanding the evaluation flow!
