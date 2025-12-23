# Chapter 17: Abstract Machines - Common Mistakes

This guide covers the most frequent errors when learning abstract machines, how to recognize them, and how to fix them.

---

## Mistake 1: Confusing Values and Terms

### The Problem
Thinking that terms and values are the same thing.

### Wrong Thinking
> "A lambda `λx. x` is a value, so I can use it directly."

### Correct Understanding
- **Terms**: Syntax (what you write)
- **Values**: Results of evaluation (what you get)

A lambda *term* `λx. x` evaluates to a *closure value* `⟨λx. x, ρ⟩` that includes the environment.

### Why This Matters
When you look up a variable, you get a value (potentially a closure), not a term. The closure carries its environment.

### How to Remember
> "Terms are input to the machine. Values are output."

---

## Mistake 2: Forgetting to Capture the Environment

### The Problem
Not including the environment when creating a closure.

### Wrong Code
```haskell
step (Eval (Lam x t), env, kont) = Apply kont (VLam x t)  -- WRONG!
```

### Correct Code
```haskell
step (Eval (Lam x t), env, kont) = Apply kont (VClosure x t env)  -- RIGHT!
```

### Why This Matters
Consider:
```
let y = 10 in λx. x + y
```

The lambda has free variable `y`. If we don't capture `{y ↦ 10}` in the closure, when we later call the function, we won't know what `y` is!

### How to Remember
> "A closure closes over its free variables."

---

## Mistake 3: Wrong Order in Application

### The Problem
Evaluating the argument before the function in call-by-value.

### Wrong Order
```
(f t) → evaluate t first, then f
```

### Correct Order (for CEK)
```
(f t) → evaluate f first, then t
```

### Why This Matters
Most languages evaluate left-to-right. Also, you need to know what the function *is* before applying it.

### The Frame Order
```haskell
-- Evaluating (f t):
step (Eval (App f t), env, kont) =
  Eval f env (FApp1 t env : kont)  -- Evaluate f first
                                   -- FApp1 says "t comes next"
```

### How to Remember
> "In CEK, function first, then argument. Frames tell you what's next."

---

## Mistake 4: Not Extending the Closure's Environment

### The Problem
Extending the current environment instead of the closure's environment.

### Wrong Code
```haskell
step (Apply (FApp2 (VClosure x t closureEnv) : k), arg) =
  Eval t (extendEnv x arg currentEnv) k  -- WRONG! Using wrong env
```

### Correct Code
```haskell
step (Apply (FApp2 (VClosure x t closureEnv) : k), arg) =
  Eval t (extendEnv x arg closureEnv) k  -- RIGHT! Using closure's env
```

### Why This Matters
The closure's body should see the bindings from when the lambda was *defined*, not when it was *called*. This is lexical scoping.

### Example
```
let x = 1 in
  let f = λy. x + y in   -- f captures {x ↦ 1}
    let x = 100 in
      f 5                 -- Should return 6, not 105!
```

### How to Remember
> "The closure carries its own environment. Extend THAT, not the current one."

---

## Mistake 5: SECD De Bruijn Index Confusion

### The Problem
Getting the de Bruijn index wrong for nested lambdas.

### Tricky Example
In `λx. λy. x + y`:
- What's the index of `x`?
- What's the index of `y`?

### Wrong Thinking
> "x comes first, so it's 0. y comes second, so it's 1."

### Correct Understanding
De Bruijn indices count *binders outward*:
- `y` is bound by the inner lambda: index 0
- `x` is bound by the outer lambda: index 1

```
λx. λy. x + y
       ^   ^
       |   |
       1   0
```

### How to Remember
> "De Bruijn indices: count binders UP and OUTWARD."

---

## Mistake 6: Forgetting IReturn in Closures

### The Problem
Not adding `IReturn` at the end of closure code in SECD.

### Wrong Compilation
```haskell
compile (Lam x t) = [IClosure (compile t)]  -- WRONG!
```

### Correct Compilation
```haskell
compile (Lam x t) = [IClosure (compile t ++ [IReturn])]  -- RIGHT!
```

### Why This Matters
When the function body finishes, we need to return to the caller. Without `IReturn`, execution falls off the end of the code!

### How to Remember
> "Every closure must return. Always end with IReturn."

---

## Mistake 7: Krivine Evaluates Arguments Too Early

### The Problem
Evaluating arguments in Krivine (which should be call-by-name).

### Wrong Transition
```
⟨t₁ t₂, ρ, π⟩ → ⟨t₁, ρ, (value of t₂)::π⟩  -- WRONG!
```

### Correct Transition
```
⟨t₁ t₂, ρ, π⟩ → ⟨t₁, ρ, (t₂, ρ)::π⟩  -- RIGHT! Push thunk
```

### Why This Matters
The whole point of Krivine is call-by-name: arguments are evaluated only when needed. Evaluating them upfront defeats the purpose.

### How to Remember
> "Krivine pushes thunks, not values."

---

## Mistake 8: Confusing Call-by-Name and Call-by-Need

### The Problem
Thinking Krivine (call-by-name) caches results like Haskell.

### Wrong Thinking
> "In `(λx. x + x) expensive`, expensive is evaluated once."

### Correct Understanding
**Call-by-name (Krivine)**: Expensive is evaluated TWICE (once for each use of x).

**Call-by-need (Haskell)**: Expensive is evaluated once, result cached.

### The Difference
```
Call-by-name:  (λx. x + x) expensive
              → expensive + expensive
              → v + v' where v and v' are computed separately

Call-by-need: (λx. x + x) expensive
              → v + v where v is computed once, shared
```

### How to Fix
To get call-by-need, you need to add memoization to Krivine.

### How to Remember
> "Name = recompute. Need = remember."

---

## Mistake 9: Misunderstanding the Continuation Stack

### The Problem
Thinking the continuation is processed left-to-right or in the wrong order.

### Wrong Thinking
> "Frames are executed in the order they were pushed."

### Correct Understanding
The continuation is a *stack* - LIFO order:
- The most recently pushed frame is processed first
- This matches the structure of nested expressions

### Example
```
(1 + 2) + 3
```
Frames pushed: `[FAdd1 3 env, ...]` then `[FAdd1 2 env, FAdd1 3 env, ...]`

Popped in reverse: first the inner `+`, then the outer.

### How to Remember
> "Continuation = stack. Last in, first out."

---

## Mistake 10: Not Handling Empty Continuation

### The Problem
Forgetting to handle the case when continuation is empty.

### Wrong Code
```haskell
step (Apply (f:k), v) = ... -- What if k is empty?
step (Apply [], v) = ???    -- Oops, no case!
```

### Correct Code
```haskell
step (Apply [], v) = Done v  -- Terminal state!
step (Apply (f:k), v) = ...
```

### Why This Matters
When the continuation is empty and we have a value, evaluation is complete. This is how the machine knows to stop.

### How to Remember
> "Empty continuation + value = we're done!"

---

## Debugging Checklist

When your abstract machine isn't working:

1. **Check environment capture**: Are closures capturing the right environment?
2. **Check evaluation order**: Function before argument (for CBV)?
3. **Check frame order**: Are frames pushed/popped correctly?
4. **Check environment extension**: Using closure's env, not current?
5. **Check de Bruijn indices**: Counting outward from binding site?
6. **Check terminal case**: Empty continuation handled?
7. **Check thunks (Krivine)**: Not evaluating arguments too early?

---

## Practice Problems

### Problem 1: Find the Bug

What's wrong with this CEK step?

```haskell
step (Eval (App f t), env, k) = Eval t env (FApp1 f env : k)
```

<details>
<summary>Answer</summary>

Wrong order! Should evaluate `f` first:
```haskell
step (Eval (App f t), env, k) = Eval f env (FApp1 t env : k)
```

The frame should remember `t` (the argument), not `f` (the function).
</details>

### Problem 2: Find the Bug

What's wrong with this SECD rule?

```haskell
exec (IClosure code : c, s, e, d) = (Closure code : s, c, e, d)
```

<details>
<summary>Answer</summary>

The closure should capture the current environment:
```haskell
exec (IClosure code : c, s, e, d) = (Closure code e : s, c, e, d)
                                              ^^^
```
</details>

### Problem 3: Predict the Result

In Krivine, what happens with:
```
(λx. x x) (λy. y)
```

<details>
<summary>Answer</summary>

1. Push thunk `(λy. y, {})` for argument
2. Lambda, bind `x ↦ Thunk(λy.y, {})`
3. Evaluate `x x`:
   - Push thunk `(x, {x↦...})` for second `x`
   - Look up first `x`, get `λy. y`
4. Lambda with stack, bind `y ↦ Thunk(x, {x↦...})`
5. Evaluate `y`:
   - Look up, get thunk for `x`
   - Evaluate `x` → `λy. y`

Result: the identity function `λy. y`

This is similar to how `ω ω` would work if it terminated.
</details>
