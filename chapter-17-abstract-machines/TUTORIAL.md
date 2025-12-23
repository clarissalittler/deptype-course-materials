# Chapter 17: Abstract Machines - Tutorial

This tutorial walks through abstract machines with step-by-step examples.

## Part 1: Why Abstract Machines?

### The Problem with Substitution

Consider evaluating `(λx. x + x + x) (100 + 200)`:

**Substitution approach:**
```
(λx. x + x + x) (100 + 200)
→ (λx. x + x + x) 300           -- evaluate argument
→ 300 + 300 + 300               -- substitute (copy 300 three times!)
→ 600 + 300
→ 900
```

**Problem 1**: We copied the value `300` three times.

**Problem 2**: What if instead of `300`, we had a huge term? We'd copy it multiple times!

### The Solution: Environments

Instead of substituting, we keep a *lookup table* (environment):

```
(λx. x + x + x) 300
→ evaluate body with env = {x ↦ 300}
→ (x + x + x)[env = {x ↦ 300}]
→ lookup(x) + lookup(x) + lookup(x)
→ 300 + 300 + 300
→ 900
```

No copying of terms! Just three lookups.

### Closures: Capturing the Environment

What about nested functions?

```
let y = 10 in (λx. x + y)
```

The lambda `λx. x + y` has a free variable `y`. When we create this function value, we must remember that `y = 10`.

A **closure** is a function paired with its environment:

```
⟨λx. x + y, {y ↦ 10}⟩
```

When we call this closure with argument 5:
```
⟨λx. x + y, {y ↦ 10}⟩ applied to 5
→ evaluate (x + y) with env = {x ↦ 5, y ↦ 10}
→ 5 + 10
→ 15
```

## Part 2: The CEK Machine

The CEK machine has three components:

- **C**ontrol: The term we're currently evaluating
- **E**nvironment: Current variable bindings
- **K**ontinuation: What to do after we finish

### Machine States

```haskell
data State
  = Eval Term Env Kont    -- Evaluating a term
  | Apply Kont Value      -- Applying result to continuation
```

Two modes:
1. `Eval`: We have a term to evaluate
2. `Apply`: We have a value and need to use it

### Continuation Frames

The continuation is a list of "frames" - each frame is a piece of work waiting to be done:

```haskell
data Frame
  = FApp1 Term Env   -- We're evaluating (□ t), waiting for function
  | FApp2 Value      -- We're evaluating (v □), waiting for argument
  | FAdd1 Term Env   -- We're evaluating (□ + t)
  | FAdd2 Value      -- We're evaluating (v + □)
  ...
```

### Example Trace: Identity Function

Let's trace `(λx. x) 5`:

**Initial state:**
```
Eval (App (Lam "x" (Var "x")) (Lit 5)), {}, []
```

**Step 1:** We have an application `t1 t2`. Evaluate the function first.
```
Eval (Lam "x" (Var "x")), {}, [FApp1 (Lit 5) {}]
                               ^^^^^^^^^^^^^^^^
                               pushed: "evaluate 5 next"
```

**Step 2:** Lambda is a value! Create a closure.
```
Apply [FApp1 (Lit 5) {}], VClosure "x" (Var "x") {}
                          ^^^^^^^^^^^^^^^^^^^^^^^^^^
                          closure: lambda + empty env
```

**Step 3:** Pop frame FApp1, now evaluate argument.
```
Eval (Lit 5), {}, [FApp2 (VClosure "x" (Var "x") {})]
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                  pushed: "apply function next"
```

**Step 4:** Literal is a value!
```
Apply [FApp2 (VClosure "x" (Var "x") {})], VInt 5
```

**Step 5:** Pop FApp2, apply closure to argument.
- Extend closure's environment: `{x ↦ 5}`
- Evaluate body with new environment
```
Eval (Var "x"), {x ↦ 5}, []
```

**Step 6:** Variable lookup.
```
Apply [], VInt 5
```

**Done!** Result is 5.

### Example Trace: Addition

Let's trace `(λx. x + 1) 3`:

```
Eval (App (Lam "x" (Add (Var "x") (Lit 1))) (Lit 3)), {}, []

→ Eval (Lam "x" (Add (Var "x") (Lit 1))), {}, [FApp1 (Lit 3) {}]

→ Apply [FApp1 (Lit 3) {}], VClosure "x" (Add (Var "x") (Lit 1)) {}

→ Eval (Lit 3), {}, [FApp2 <closure>]

→ Apply [FApp2 <closure>], VInt 3

→ Eval (Add (Var "x") (Lit 1)), {x ↦ 3}, []

→ Eval (Var "x"), {x ↦ 3}, [FAdd1 (Lit 1) {x ↦ 3}]

→ Apply [FAdd1 (Lit 1) {x ↦ 3}], VInt 3

→ Eval (Lit 1), {x ↦ 3}, [FAdd2 (VInt 3)]

→ Apply [FAdd2 (VInt 3)], VInt 1

→ Apply [], VInt 4
```

**Result:** 4

## Part 3: The SECD Machine

SECD compiles terms to instructions first, then executes.

### The Instruction Set

```haskell
IAccess i     -- Push env[i] onto stack
IClosure code -- Push closure (code, env) onto stack
IApply        -- Pop function and argument, apply
IReturn       -- Return from function call
IConst n      -- Push constant n
IAdd          -- Pop two, push sum
...
```

### Compilation

Terms are compiled to instruction sequences:

```haskell
compile (Var x)    = [IAccess (index of x)]
compile (Lam x t)  = [IClosure (compile t ++ [IReturn])]
compile (App t1 t2) = compile t1 ++ compile t2 ++ [IApply]
compile (Lit n)    = [IConst n]
compile (Add t1 t2) = compile t1 ++ compile t2 ++ [IAdd]
```

### Example: Compiling `(λx. x + 1) 5`

**Step 1:** Compile `λx. x + 1`
```
compile (Lam "x" (Add (Var "x") (Lit 1)))
= [IClosure (compile (Add (Var "x") (Lit 1)) ++ [IReturn])]
= [IClosure ([IAccess 0] ++ [IConst 1] ++ [IAdd] ++ [IReturn])]
= [IClosure [IAccess 0, IConst 1, IAdd, IReturn]]
```

**Step 2:** Compile `5`
```
compile (Lit 5) = [IConst 5]
```

**Step 3:** Compile application
```
compile (App ...)
= [IClosure [...], IConst 5, IApply]
```

### Executing SECD

State: (Stack, Environment, Control, Dump)

**Initial:**
```
([], [], [IClosure [IAccess 0, IConst 1, IAdd, IReturn], IConst 5, IApply], [])
```

**Execute IClosure:**
```
([Closure([IAccess 0, IConst 1, IAdd, IReturn], [])], [], [IConst 5, IApply], [])
```

**Execute IConst 5:**
```
([5, Closure(...)], [], [IApply], [])
```

**Execute IApply:**
- Pop closure and argument (5)
- Save current state to dump
- Start executing closure body with env = [5]
```
([], [5], [IAccess 0, IConst 1, IAdd, IReturn], [([], [], [])])
```

**Execute IAccess 0:**
- Push env[0] = 5
```
([5], [5], [IConst 1, IAdd, IReturn], [([], [], [])])
```

**Execute IConst 1:**
```
([1, 5], [5], [IAdd, IReturn], [...])
```

**Execute IAdd:**
```
([6], [5], [IReturn], [...])
```

**Execute IReturn:**
- Restore from dump
- Push result onto restored stack
```
([6], [], [], [])
```

**Done!** Result is 6.

## Part 4: The Krivine Machine

Krivine implements **call-by-name** (lazy) evaluation.

### Key Difference

In CEK (call-by-value):
```
(λx. 42) (expensive computation)
→ First evaluate (expensive computation)
→ Then return 42
```

In Krivine (call-by-name):
```
(λx. 42) (expensive computation)
→ Return 42 immediately (argument never used!)
```

### Thunks

Instead of evaluating arguments, Krivine wraps them in **thunks**:

```haskell
data Thunk = Thunk Term Env
```

A thunk is an unevaluated term paired with its environment.

### Machine State

```haskell
data State = State Term Env Stack
type Stack = [Thunk]
```

### Rules

**Variable lookup:**
```
⟨x, ρ, π⟩  →  ⟨t, ρ', π⟩
  where ρ(x) = Thunk(t, ρ')
```
Look up variable, continue with thunk's term and environment.

**Lambda with argument on stack:**
```
⟨λx.t, ρ, (t', ρ')::π⟩  →  ⟨t, ρ[x ↦ (t', ρ')], π⟩
```
Bind the thunk (not value!) to x.

**Application:**
```
⟨t₁ t₂, ρ, π⟩  →  ⟨t₁, ρ, (t₂, ρ)::π⟩
```
Push argument as thunk, don't evaluate!

### Example: `(λx. λy. x) 5 10`

**Initial:**
```
State (App (App (Lam "x" (Lam "y" (Var "x"))) (Lit 5)) (Lit 10)), {}, []
```

**Step 1:** Application, push thunk for 10
```
State (App (Lam "x" (Lam "y" (Var "x"))) (Lit 5)), {}, [Thunk(10, {})]
```

**Step 2:** Application, push thunk for 5
```
State (Lam "x" (Lam "y" (Var "x"))), {}, [Thunk(5, {}), Thunk(10, {})]
```

**Step 3:** Lambda, pop thunk and bind to x
```
State (Lam "y" (Var "x")), {x ↦ Thunk(5, {})}, [Thunk(10, {})]
```

**Step 4:** Lambda, pop thunk and bind to y
```
State (Var "x"), {x ↦ Thunk(5, {}), y ↦ Thunk(10, {})}, []
```

**Step 5:** Variable lookup, get thunk for x
```
State (Lit 5), {}, []
```

**Done!** Result is 5. Note: The thunk for 10 was never evaluated!

### Call-by-Name Gotcha

```
(λx. x + x) (expensive)
```

In Krivine:
- `x` is looked up twice
- Each lookup evaluates the thunk
- `expensive` computed twice!

This is why Haskell uses **call-by-need**: memoize thunks after evaluation.

## Part 5: Comparison

### When to Use Each Machine

**CEK:**
- Simple to understand
- Good for teaching and prototyping
- Base for control operators (call/cc)

**SECD:**
- Efficient execution (compiled)
- Closer to real VMs
- Good for bytecode interpreters

**Krivine:**
- Lazy evaluation
- Good for languages like Haskell
- Simpler than STG but same idea

### Summary Table

| Feature | CEK | SECD | Krivine |
|---------|-----|------|---------|
| Evaluation | Eager | Eager | Lazy |
| Compilation | No | Yes | No |
| Arguments | Values | Values | Thunks |
| Continuation | Explicit frames | Implicit (dump) | Implicit (stack) |

## Practice Problems

### Problem 1: CEK Trace

Trace `(λf. λx. f (f x)) (λy. y + 1) 0` through CEK.

<details>
<summary>Solution</summary>

This applies "twice" to "successor" to 0, giving 2.

Key steps:
1. Evaluate outer application, push frames
2. Create closure for twice
3. Apply to successor, extend env
4. Create closure for `λx. f (f x)` with `{f ↦ <succ>}`
5. Apply to 0
6. Evaluate `f (f x)` with `{f ↦ <succ>, x ↦ 0}`
7. Inner `f x` → 1
8. Outer `f 1` → 2

Result: 2
</details>

### Problem 2: SECD Compilation

Compile `λx. λy. x + y` to SECD instructions.

<details>
<summary>Solution</summary>

```
compile (Lam "x" (Lam "y" (Add (Var "x") (Var "y"))))
= [IClosure (compile (Lam "y" (Add (Var "x") (Var "y"))) ++ [IReturn])]
= [IClosure ([IClosure (compile (Add (Var "x") (Var "y")) ++ [IReturn])] ++ [IReturn])]

Inner body:
compile (Add (Var "x") (Var "y"))
= [IAccess 1, IAccess 0, IAdd]
-- x is at index 1 (outer), y is at index 0 (inner)

Full result:
[IClosure [IClosure [IAccess 1, IAccess 0, IAdd, IReturn], IReturn]]
```
</details>

### Problem 3: Krivine vs CEK

Show a term that terminates in Krivine but diverges in CEK.

<details>
<summary>Solution</summary>

```
(λx. 42) (fix (λf. f))
```

- **CEK**: Must evaluate argument first. `fix (λf. f)` loops forever.
- **Krivine**: Returns 42 immediately. Argument never evaluated.

</details>
