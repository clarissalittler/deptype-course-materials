# Chapter 18: Normalization by Evaluation - Tutorial

This tutorial walks through NbE with step-by-step examples.

## Part 1: The Problem and Solution

### Why We Need Normalization

In dependent type theory, types can contain arbitrary terms:

```
Vec : Nat → Type
Vec 0        = Unit
Vec (n + 1)  = Pair A (Vec n)
```

To check if `xs : Vec (1 + 1)` can be used where `Vec 2` is expected, we need to know that `1 + 1` equals `2`. This requires **normalization**.

### The Old Way: Reduction

Traditional approach: define reduction rules and apply until stuck.

```
(λx. x + x) 3
→ 3 + 3          -- beta reduction
→ 6              -- arithmetic
```

Problems:
- Many rules to define
- May not terminate
- Hard to prove correct

### The NbE Way

NbE uses Haskell's evaluation:

```
Term ──eval──► Val ──quote──► Nf
```

1. **eval**: Convert syntax to semantic values
2. **quote**: Read back to normal form

The key insight: Haskell already knows how to evaluate! A closure `Closure env body` applied to an argument is just:
```haskell
applyClosure (Closure env body) arg = eval (arg : env) body
```

Haskell does the beta reduction for us.

## Part 2: The Semantic Domain

### Values vs Terms

**Terms** are syntax—what you write:
```haskell
data Term = TVar Int | TLam String Term | TApp Term Term | ...
```

**Values** are semantics—what they mean:
```haskell
data Val = VLam String Closure | VNe Neutral | ...
```

### Closures

A **closure** is a lambda that remembers its environment:

```haskell
data Closure = Closure Env Term
type Env = [Val]
```

Example: Evaluating `λx. λy. x` in empty environment:
```
eval [] (TLam "x" (TLam "y" (TVar 1)))
= VLam "x" (Closure [] (TLam "y" (TVar 1)))
```

To apply this closure to `5`:
```
applyClosure (Closure [] (TLam "y" (TVar 1))) (VInt 5)
= eval [VInt 5] (TLam "y" (TVar 1))
= VLam "y" (Closure [VInt 5] (TVar 1))
```

Now `x = 5` is captured in the closure's environment!

### Neutral Values

A **neutral** value is "stuck" on a free variable:

```haskell
data Neutral = NVar Lvl | NApp Neutral Val | ...
```

Examples:
- `x` → `NVar 0`
- `x 5` → `NApp (NVar 0) (VInt 5)`
- `x (y 3)` → `NApp (NVar 0) (VNe (NApp (NVar 1) (VInt 3)))`

We can't reduce further without knowing what `x` and `y` are.

## Part 3: Evaluation

### The eval Function

```haskell
eval :: Env -> Term -> Val

eval env (TVar i)   = env !! i                    -- Lookup
eval env (TLam x t) = VLam x (Closure env t)      -- Create closure
eval env (TApp t u) = vApp (eval env t) (eval env u)
```

### Value Application (vApp)

This is where beta reduction happens:

```haskell
vApp :: Val -> Val -> Val
vApp (VLam _ closure) arg = applyClosure closure arg  -- BETA!
vApp (VNe neutral) arg    = VNe (NApp neutral arg)    -- Stuck
```

If we have a real lambda, apply it. If we're stuck on a neutral, stay stuck.

### Example: Church Encoding

Let's trace `eval` on `(λf. λx. f x) (λy. y)`:

**Step 1**: Evaluate the application
```
eval [] (TApp (TLam "f" ...) (TLam "y" ...))
= vApp (eval [] (TLam "f" ...)) (eval [] (TLam "y" ...))
```

**Step 2**: Evaluate both parts
```
eval [] (TLam "f" (TLam "x" (TApp (TVar 1) (TVar 0))))
= VLam "f" (Closure [] (TLam "x" (TApp (TVar 1) (TVar 0))))

eval [] (TLam "y" (TVar 0))
= VLam "y" (Closure [] (TVar 0))
```

**Step 3**: Apply
```
vApp (VLam "f" (Closure [] ...)) (VLam "y" (Closure [] ...))
= applyClosure (Closure [] (TLam "x" ...)) (VLam "y" ...)
= eval [VLam "y" (Closure [] ...)] (TLam "x" (TApp (TVar 1) (TVar 0)))
```

**Step 4**: Continue evaluating
```
= VLam "x" (Closure [VLam "y" ...] (TApp (TVar 1) (TVar 0)))
```

We have a value! The inner structure hasn't been reduced yet—that happens when we apply the closure.

## Part 4: Quotation

### The Problem

We have semantic values, but we want syntactic normal forms. How do we "read back" a closure?

### The Solution: Fresh Variables

To quote a lambda:
1. Create a fresh *neutral* variable
2. Apply the closure to it
3. Quote the result

```haskell
quote :: Lvl -> Val -> Nf

quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)              -- Step 1
      body = applyClosure closure freshVar   -- Step 2
  in NfLam x (quote (lvl + 1) body)          -- Step 3

quote lvl (VNe neutral) = NfNe (quoteNe lvl neutral)
```

### Why Fresh Variables?

A closure is opaque—we can't look inside. But we can *observe* its behavior by applying it to something!

By using a neutral variable, we keep track of the "hole" that would be filled by a real argument.

### Example: Quoting Identity

Quote `VLam "x" (Closure [] (TVar 0))`:

```
quote 0 (VLam "x" (Closure [] (TVar 0)))
```

**Step 1**: Create fresh variable at level 0
```
freshVar = VNe (NVar 0)
```

**Step 2**: Apply closure
```
applyClosure (Closure [] (TVar 0)) (VNe (NVar 0))
= eval [VNe (NVar 0)] (TVar 0)
= VNe (NVar 0)
```

**Step 3**: Quote body at level 1
```
quote 1 (VNe (NVar 0))
= NfNe (NeVar ?)
```

Wait—we need to convert level 0 to an index. At depth 1:
```
index = depth - level - 1 = 1 - 0 - 1 = 0
```

So: `NfNe (NeVar 0)`

**Result**: `NfLam "x" (NfNe (NeVar 0))` = `λx. x`

### De Bruijn Levels vs Indices

**Indices** count from the binding site inward:
```
λ. λ. 0 1
      ^ ^
      | inner lambda's variable
      outer lambda's variable
```

**Levels** count from the root outward:
```
λ. λ. x y     (at depth 2)
      ^ ^
      | level 1
      level 0
```

**Conversion**: `index = depth - level - 1`

Why levels? Fresh variable generation is just incrementing!

## Part 5: Normalization

### The Main Function

```haskell
normalize :: Term -> Nf
normalize t = quote 0 (eval [] t)
```

That's it! Evaluate to a value, then quote to a normal form.

### Complete Example: Normalizing K combinator application

Normalize `(λx. λy. x) true false`:

**Step 1**: eval
```
eval [] (TApp (TApp (TLam "x" (TLam "y" (TVar 1))) TTrue) TFalse)
```

Evaluate inner application:
```
vApp (VLam "x" (Closure [] (TLam "y" (TVar 1)))) VTrue
= applyClosure (Closure [] ...) VTrue
= eval [VTrue] (TLam "y" (TVar 1))
= VLam "y" (Closure [VTrue] (TVar 1))
```

Evaluate outer application:
```
vApp (VLam "y" (Closure [VTrue] (TVar 1))) VFalse
= applyClosure (Closure [VTrue] (TVar 1)) VFalse
= eval [VFalse, VTrue] (TVar 1)
= VTrue
```

**Step 2**: quote
```
quote 0 VTrue = NfTrue
```

**Result**: `true`

### Eta Expansion

Something interesting happens with neutral functions:

```
f : A → B    (f is a neutral NVar 0)
```

When we quote at level 0:
```
quote 0 f
-- But f is neutral, not a lambda!
```

Actually, if we know `f` has function type, we can eta-expand:
```
quote 0 f = NfLam "x" (quote 1 (vApp f (VNe (NVar 0))))
          = NfLam "x" (NfNe (NeApp (NeVar 0) (NfNe (NeVar 0))))
          = λx. f x
```

This is desirable for comparing functions by extensionality.

## Part 6: Type Checking with NbE

### Definitional Equality

Two types are definitionally equal if they normalize to the same thing:

```haskell
eqType :: Val -> Val -> Bool
eqType v1 v2 = quote lvl v1 == quote lvl v2
```

### In Practice

When type checking `f e` where `f : (x : A) → B`:
1. Check `e : A`
2. Compute `B[x := e]` by `applyClosure (Closure env B) (eval env e)`
3. That's the type of `f e`

NbE handles the substitution and normalization seamlessly.

## Practice Problems

### Problem 1: Trace eval

Trace `eval [] (TApp (TLam "x" (TApp (TVar 0) (TVar 0))) (TLam "y" (TVar 0)))`.

<details>
<summary>Solution</summary>

This is `(λx. x x) (λy. y)`:

```
eval [] (TApp (TLam "x" (TApp (TVar 0) (TVar 0))) (TLam "y" (TVar 0)))
= vApp (eval [] (TLam "x" ...)) (eval [] (TLam "y" ...))
= vApp (VLam "x" (Closure [] (TApp (TVar 0) (TVar 0))))
       (VLam "y" (Closure [] (TVar 0)))
= applyClosure (Closure [] (TApp (TVar 0) (TVar 0))) (VLam "y" ...)
= eval [VLam "y" ...] (TApp (TVar 0) (TVar 0))
= vApp (eval [VLam "y" ...] (TVar 0)) (eval [VLam "y" ...] (TVar 0))
= vApp (VLam "y" (Closure [] (TVar 0))) (VLam "y" (Closure [] (TVar 0)))
= applyClosure (Closure [] (TVar 0)) (VLam "y" ...)
= eval [VLam "y" ...] (TVar 0)
= VLam "y" (Closure [] (TVar 0))
```

Result: `λy. y` (the identity function)
</details>

### Problem 2: Quote with fresh variables

Quote `VLam "f" (Closure [] (TLam "x" (TApp (TVar 1) (TApp (TVar 1) (TVar 0)))))`.

<details>
<summary>Solution</summary>

This is the closure for `λf. λx. f (f x)`.

```
quote 0 (VLam "f" (Closure [] (TLam "x" (TApp (TVar 1) (TApp (TVar 1) (TVar 0))))))
```

Fresh var at level 0: `f_0 = VNe (NVar 0)`

Apply closure:
```
applyClosure (Closure [] (TLam "x" ...)) f_0
= eval [f_0] (TLam "x" (TApp (TVar 1) (TApp (TVar 1) (TVar 0))))
= VLam "x" (Closure [f_0] (TApp (TVar 1) (TApp (TVar 1) (TVar 0))))
```

Continue quoting at level 1:
```
quote 1 (VLam "x" (Closure [f_0] ...))
```

Fresh var at level 1: `x_1 = VNe (NVar 1)`

Apply:
```
applyClosure (Closure [f_0] (TApp (TVar 1) (TApp (TVar 1) (TVar 0)))) x_1
= eval [x_1, f_0] (TApp (TVar 1) (TApp (TVar 1) (TVar 0)))
= vApp (eval [x_1, f_0] (TVar 1)) (eval [x_1, f_0] (TApp (TVar 1) (TVar 0)))
= vApp f_0 (vApp f_0 x_1)
= vApp (VNe (NVar 0)) (vApp (VNe (NVar 0)) (VNe (NVar 1)))
= vApp (VNe (NVar 0)) (VNe (NApp (NVar 0) (VNe (NVar 1))))
= VNe (NApp (NVar 0) (VNe (NApp (NVar 0) (VNe (NVar 1)))))
```

Quote at level 2:
Convert level 0 → index 1, level 1 → index 0

Result: `NfLam "f" (NfLam "x" (NfNe (NeApp (NeVar 1) (NfNe (NeApp (NeVar 1) (NfNe (NeVar 0)))))))`

Which is: `λf. λx. f (f x)`
</details>

### Problem 3: Why this works

Explain why `(λx. λy. x) a b` normalizes to `a` even though `a` might be a complex term.

<details>
<summary>Solution</summary>

1. When we evaluate `(λx. λy. x) a`, we create `Closure [a_val] (TVar 1)` where `a_val = eval env a`.

2. When we apply to `b`, we evaluate `TVar 1` in environment `[b_val, a_val]`.

3. `TVar 1` looks up index 1, which is `a_val`.

4. So we get back `a_val`, regardless of how complex `a` was.

5. When we quote `a_val`, we get the normal form of `a`.

The key is that we never substituted `a` into the term—we just stored its value in the environment and looked it up when needed. This is much more efficient than textual substitution!
</details>
