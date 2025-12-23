# Chapter 18: Normalization by Evaluation - Common Mistakes

This guide covers frequent errors when learning NbE and how to fix them.

---

## Mistake 1: Confusing Terms, Values, and Normal Forms

### The Problem
Using the wrong type at the wrong stage.

### Wrong Thinking
> "eval returns a Term, then quote converts it."

### Correct Understanding
Three distinct types:
- **Term**: Input syntax (what you parse)
- **Val**: Semantic domain (result of eval)
- **Nf**: Normal form (result of quote)

```
Term ──eval──► Val ──quote──► Nf
```

### How to Remember
> "Terms go in, Values in between, Normal forms come out."

---

## Mistake 2: Forgetting to Capture the Environment in Closures

### The Problem
Creating closures without the current environment.

### Wrong Code
```haskell
eval env (TLam x t) = VLam x (Closure [] t)  -- WRONG!
```

### Correct Code
```haskell
eval env (TLam x t) = VLam x (Closure env t)  -- RIGHT!
```

### Why This Matters
The lambda's body may reference variables from the enclosing scope. Without the environment, those lookups will fail or return wrong values.

### Example
```
let y = 5 in λx. x + y
```
The lambda needs `{y ↦ 5}` in its closure!

### How to Remember
> "Closures close over the current environment."

---

## Mistake 3: Wrong Index/Level Conversion

### The Problem
Mixing up de Bruijn indices and levels.

### Wrong Conversion
```haskell
-- When quoting NVar at level k with current level l
toIndex k l = k  -- WRONG!
```

### Correct Conversion
```haskell
toIndex lvl currentLvl = currentLvl - lvl - 1  -- RIGHT!
```

### Example
At depth 2 (currentLvl = 2):
- Level 0 → Index 1 (= 2 - 0 - 1)
- Level 1 → Index 0 (= 2 - 1 - 1)

### Visual Aid
```
     λ (level 0)
     └─ λ (level 1)
        └─ 0 1    -- indices
           │ └─── refers to level 0 (outer lambda)
           └───── refers to level 1 (inner lambda)
```

### How to Remember
> "Levels count from outside-in, indices from inside-out."

---

## Mistake 4: Not Creating Fresh Variables When Quoting Lambdas

### The Problem
Trying to quote a closure's body directly.

### Wrong Code
```haskell
quote lvl (VLam x (Closure env body)) =
  NfLam x (quote lvl (eval env body))  -- WRONG!
```

### Correct Code
```haskell
quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)
      body = applyClosure closure freshVar
  in NfLam x (quote (lvl + 1) body)  -- RIGHT!
```

### Why This Matters
The closure is a "black box"—we can't see inside without applying it. By applying to a fresh variable, we get a value that represents "what the function does" symbolically.

### How to Remember
> "To peek inside a closure, apply it to a fresh neutral variable."

---

## Mistake 5: Not Incrementing Level After Creating Fresh Variable

### The Problem
Using the same level for nested lambdas.

### Wrong Code
```haskell
quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)
      body = applyClosure closure freshVar
  in NfLam x (quote lvl body)  -- WRONG: should be lvl + 1
```

### Why This Matters
If you use the same level, nested lambdas get the same fresh variable, which is wrong.

### Correct Code
```haskell
in NfLam x (quote (lvl + 1) body)  -- RIGHT!
```

### How to Remember
> "Each lambda adds a level: increment when entering a binder."

---

## Mistake 6: Evaluating Instead of Building Neutral

### The Problem
Trying to reduce when stuck on a variable.

### Wrong Code
```haskell
vApp (VNe neutral) arg =
  applyClosure ... arg  -- WRONG: neutral isn't a closure!
```

### Correct Code
```haskell
vApp (VNe neutral) arg = VNe (NApp neutral arg)  -- RIGHT!
```

### Why This Matters
A neutral value is "stuck"—we can't reduce `x y` without knowing what `x` is. We must preserve the structure.

### How to Remember
> "Neutral in, neutral out. Can't reduce what you don't know."

---

## Mistake 7: Using Environment Index Wrong

### The Problem
Off-by-one errors in environment lookup.

### Wrong Understanding
> "Index 0 is the first variable in the environment."

### Correct Understanding
Yes, but environments are extended at the front:

```haskell
env = [v2, v1, v0]  -- most recently bound first
```

So `env !! 0 = v2` (the innermost binding).

### Example
```
λx. λy. y   -- y is TVar 0
λx. λy. x   -- x is TVar 1
```

When evaluating in `env = [valY, valX]`:
- `TVar 0` → `valY` (correct, y is innermost)
- `TVar 1` → `valX` (correct, x is one level out)

### How to Remember
> "Index 0 = most recently bound = head of environment list."

---

## Mistake 8: Confusing Closure Application with Value Application

### The Problem
Calling `applyClosure` on a value instead of `vApp`.

### Context
```haskell
applyClosure :: Closure -> Val -> Val
vApp :: Val -> Val -> Val
```

### When to Use Which
- `applyClosure`: When you have a `Closure` directly (from inside a `VLam`)
- `vApp`: When you have two `Val`s and want to apply

### Correct Pattern
```haskell
vApp (VLam _ closure) arg = applyClosure closure arg
vApp (VNe neutral) arg = VNe (NApp neutral arg)
```

### How to Remember
> "vApp dispatches. applyClosure does the actual work."

---

## Mistake 9: Forgetting Eta Expansion for Function Types

### The Problem
Quoting a neutral of function type without eta expanding.

### Wrong Result
```haskell
quote lvl (VNe (NVar 0)) = NfNe (NeVar ...)
```

For a neutral `f` of type `A → B`, this gives just `f` instead of `λx. f x`.

### Why Eta Matters
Two functions are equal if they behave the same on all inputs. Without eta, `f` and `λx. f x` look different syntactically even though they're semantically the same.

### Correct Approach (Type-Directed)
```haskell
quote lvl (VNe neutral) (TyArr a b) =
  let freshVar = VNe (NVar lvl)
      body = vApp (VNe neutral) freshVar
  in NfLam "x" (quote (lvl + 1) body b)
```

### How to Remember
> "Eta expand functions: f becomes λx. f x."

---

## Mistake 10: Non-Termination from Wrong Recursion

### The Problem
Creating infinite loops in eval or quote.

### Dangerous Pattern
```haskell
eval env (TFix f) =
  let v = eval env (TApp f (TFix f))  -- Infinite loop!
  in v
```

### Correct Pattern
For fixpoints, use Haskell's laziness:
```haskell
eval env (TFix f) =
  let v = VFix (\x -> vApp (eval env f) x)
  in v
```

Or for languages with explicit fixpoints, handle them carefully in the semantic domain.

### How to Remember
> "Let Haskell's laziness work for you, not against you."

---

## Debugging Checklist

When NbE isn't working:

1. **Check environment capture**: Are closures getting the right env?
2. **Check index/level conversion**: Using the right formula?
3. **Check fresh variable generation**: Incrementing level correctly?
4. **Check neutral handling**: Building structure, not reducing?
5. **Trace step by step**: What does eval return? What does quote produce?

---

## Practice Problems

### Problem 1: Find the Bug

```haskell
eval env (TLam x body) = VLam x (Closure [] body)
```

<details>
<summary>Answer</summary>

Should capture `env`, not empty environment:
```haskell
eval env (TLam x body) = VLam x (Closure env body)
```
</details>

### Problem 2: Find the Bug

```haskell
quote lvl (VLam x closure) =
  let body = applyClosure closure (VNe (NVar lvl))
  in NfLam x (quote lvl body)
```

<details>
<summary>Answer</summary>

Should increment level for the body:
```haskell
in NfLam x (quote (lvl + 1) body)
```
</details>

### Problem 3: Trace the Error

Why does this give wrong results for `λx. λy. x`?

```haskell
-- Suppose we quote at level 0 but don't increment
```

<details>
<summary>Answer</summary>

Both fresh variables get level 0. When we convert to indices:
- For outer lambda: fresh var at 0
- For inner lambda: fresh var at 0 (wrong! should be 1)

When quoting the body `x`, it's `NVar 0`. At depth 2:
- Correct: `2 - 0 - 1 = 1` (refers to outer lambda)
- If we used depth 1: `1 - 0 - 1 = 0` (refers to inner lambda - WRONG!)

The result would be `λx. λy. y` instead of `λx. λy. x`.
</details>
