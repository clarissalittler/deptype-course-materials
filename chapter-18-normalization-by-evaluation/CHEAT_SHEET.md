# Chapter 18: Normalization by Evaluation - Cheat Sheet

## Core Concept

Normalization by Evaluation (NbE) uses the **host language's evaluation** for beta reduction, then **reads back** the result into normal form.

```
            eval                    quote
    Term  ────────►  Val  ────────►  Nf
           (compute)      (read back)

normalize = quote ∘ eval
```

Why? Haskell does beta reduction for us! No need to define reduction rules.

---

## The Two Phases

### Phase 1: Evaluation (Term → Val)

Convert syntax to semantic values using Haskell functions:

```haskell
eval :: Env -> Term -> Val

eval env (TVar i)   = env !! i           -- Lookup
eval env (TLam x t) = VLam x (Closure env t)  -- Create closure
eval env (TApp t u) = vApp (eval env t) (eval env u)
eval env TU         = VU                 -- Universe
```

### Phase 2: Quotation (Val → Nf)

Read values back to normal forms:

```haskell
quote :: Lvl -> Val -> Nf

quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)          -- Fresh neutral
      body = applyClosure closure freshVar
  in NfLam x (quote (lvl + 1) body)      -- Quote body

quote lvl (VNe neutral) = NfNe (quoteNe lvl neutral)
quote _   VU            = NfU
```

---

## Data Types

### Syntax (Input)

```haskell
data Term
  = TVar Ix              -- Variable (de Bruijn index)
  | TLam Name Term       -- Lambda: λx. t
  | TApp Term Term       -- Application: t u
  | TPi Name Term Term   -- Pi type: (x : A) → B
  | TU                   -- Universe (Type)
```

### Semantic Domain (Evaluation Result)

```haskell
data Val
  = VLam Name Closure    -- Function (closure)
  | VPi Name Val Closure -- Pi type
  | VU                   -- Universe
  | VNe Neutral          -- Stuck (neutral term)

data Closure = Closure Env Term
type Env = [Val]
```

### Normal Forms (Output)

```haskell
data Nf
  = NfLam Name Nf        -- λx. t
  | NfPi Name Nf Nf      -- (x : A) → B
  | NfU                  -- Type
  | NfNe Ne              -- Neutral (can't reduce)

data Ne
  = NeVar Lvl            -- Variable
  | NeApp Ne Nf          -- Application
```

---

## Key Concepts

### Closures: Delayed Substitution

A closure packages a term with its environment:

```
Closure env (λx. body) = "function waiting for argument"
```

When applied:
```haskell
applyClosure (Closure env body) arg = eval (arg : env) body
```

No substitution! Just environment extension.

### Neutral Values: Stuck Terms

A **neutral** is stuck on a free variable:

```haskell
data Neutral = NVar Lvl | NApp Neutral Val | ...
```

Can't reduce `x 5` without knowing what `x` is.

```haskell
vApp :: Val -> Val -> Val
vApp (VLam _ closure) arg = applyClosure closure arg  -- Beta!
vApp (VNe neutral) arg    = VNe (NApp neutral arg)    -- Stuck
```

### Fresh Variables: Peeking Inside Closures

To quote a lambda, apply it to a fresh **neutral** variable:

```haskell
quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)          -- 1. Fresh neutral
      body = applyClosure closure freshVar  -- 2. Apply closure
  in NfLam x (quote (lvl + 1) body)      -- 3. Quote body
```

This "opens" the closure to see what it does.

---

## De Bruijn Levels vs Indices

### Indices (in Terms): Count Inward

```
λ. λ. 0 1
      ^ ^
      | outer lambda (index 1)
      inner lambda (index 0)
```

Count from **binding site** to **variable**.

### Levels (in Semantics): Count Outward

```
λ. λ. x y     (at depth 2)
      ^ ^
      | level 1
      level 0
```

Count from **root** to **binding site**.

### Conversion Formula

```haskell
indexToLevel depth index = depth - index - 1
levelToIndex depth level = depth - level - 1
```

Why levels? Fresh variable generation is just `lvl + 1`!

---

## Complete Example

Normalize `(λx. λy. x) true false`:

### Step 1: Eval

```haskell
eval [] (TApp (TApp (TLam "x" (TLam "y" (TVar 1))) TTrue) TFalse)

-- Eval inner application
vApp (VLam "x" (Closure [] (TLam "y" (TVar 1)))) VTrue
= applyClosure (Closure [] (TLam "y" (TVar 1))) VTrue
= eval [VTrue] (TLam "y" (TVar 1))
= VLam "y" (Closure [VTrue] (TVar 1))

-- Eval outer application
vApp (VLam "y" (Closure [VTrue] (TVar 1))) VFalse
= applyClosure (Closure [VTrue] (TVar 1)) VFalse
= eval [VFalse, VTrue] (TVar 1)
= VTrue  -- env[1] = VTrue
```

### Step 2: Quote

```haskell
quote 0 VTrue = NfTrue
```

**Result**: `true`

---

## Common Patterns

### Pattern 1: Normalizing Identity

```
Term: λx. x
Eval: VLam "x" (Closure [] (TVar 0))
Quote at level 0:
  fresh = VNe (NVar 0)
  body = eval [VNe (NVar 0)] (TVar 0) = VNe (NVar 0)
  quote 1 (VNe (NVar 0)) = NfNe (NeVar 0)
Result: λx. x
```

### Pattern 2: Beta Reduction

```
Term: (λx. x + 1) 5
Eval:
  vApp (VLam "x" (Closure [] (TVar 0 + 1))) (VInt 5)
  = eval [VInt 5] (TVar 0 + 1)
  = 5 + 1 = 6
Quote: 6
Result: 6
```

### Pattern 3: Eta Expansion

```
Term: f (neutral, type A → B)
Quote at level 0:
  Since f has function type, eta-expand:
  λx. f x
```

---

## Type Checking with NbE

### Definitional Equality

Two types are equal if they normalize to the same thing:

```haskell
equal :: Ctx -> Val -> Val -> Bool
equal ctx v1 v2 =
  quote (ctxLvl ctx) v1 == quote (ctxLvl ctx) v2
```

### Applying Pi Types

When checking `f e` where `f : (x : A) → B`:

```haskell
-- Compute B[x := e]
typeOfApp fTy argVal =
  case fTy of
    VPi x a closure -> applyClosure closure argVal
```

NbE handles substitution automatically!

---

## Implementation Skeleton

```haskell
-- Evaluation
eval :: Env -> Term -> Val
eval env (TVar i)   = env !! i
eval env (TLam x t) = VLam x (Closure env t)
eval env (TApp t u) = vApp (eval env t) (eval env u)

vApp :: Val -> Val -> Val
vApp (VLam _ closure) arg = applyClosure closure arg
vApp (VNe neutral) arg    = VNe (NApp neutral arg)

applyClosure :: Closure -> Val -> Val
applyClosure (Closure env body) arg = eval (arg : env) body

-- Quotation
quote :: Lvl -> Val -> Nf
quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)
      body = applyClosure closure freshVar
  in NfLam x (quote (lvl + 1) body)

quote lvl (VNe neutral) = NfNe (quoteNe lvl neutral)

quoteNe :: Lvl -> Neutral -> Ne
quoteNe lvl (NVar l)      = NeVar (levelToIndex lvl l)
quoteNe lvl (NApp neu v)  = NeApp (quoteNe lvl neu) (quote lvl v)

-- Normalization
normalize :: Term -> Nf
normalize t = quote 0 (eval [] t)
```

---

## Common Idioms

### Normalizing Church Numerals

```
two = λf. λx. f (f x)
suc = λn. λf. λx. f (n f x)

normalize (suc two)
= eval then quote
= λf. λx. f (f (f x))  -- three!
```

### Type Equality

```haskell
checkEq :: Term -> Term -> Bool
checkEq t1 t2 =
  let v1 = eval [] t1
      v2 = eval [] t2
  in quote 0 v1 == quote 0 v2
```

### Substitution via Application

Instead of `t[x := u]`:

```haskell
substitute t u =
  let closure = Closure [] t
      val = eval [] u
  in quote 0 (applyClosure closure val)
```

---

## Key Insights

### Why This Works

1. **Haskell functions = lambda terms**: `VLam` uses Haskell's function space
2. **Closures = delayed substitution**: More efficient than textual replacement
3. **Neutrals preserve structure**: Can't reduce unknowns, so keep them symbolic
4. **Fresh variables probe behavior**: Apply closure to see what it does

### Advantages Over Reduction

- **Simpler**: No need to define reduction rules
- **Efficient**: Share structure via closures
- **Correct by construction**: Haskell guarantees beta reduction is right
- **Scales to complex systems**: Works for dependent types, universes, etc.

---

## Implementation Tips

### ✓ Do

- Capture environment when creating closures
- Increment level when entering binders
- Use levels for fresh variables
- Build neutrals when stuck
- Convert level to index when quoting variables

### ✗ Avoid

- Forgetting to capture environment in `Closure env body`
- Not incrementing level: `quote lvl body` → `quote (lvl+1) body`
- Wrong index/level conversion: `index = depth - level - 1`
- Evaluating neutrals: keep them as `VNe`
- Using index in semantic domain (use levels!)

---

## Debugging Checklist

1. Are closures capturing the environment?
2. Is level incremented when quoting lambdas?
3. Is the index/level conversion correct?
4. Are neutrals built (not evaluated) when stuck?
5. Is `applyClosure` called (not direct evaluation)?

---

## Comparison: NbE vs Reduction

| Feature | NbE | Reduction |
|---------|-----|-----------|
| Beta reduction | Haskell does it | Define rules |
| Efficiency | Fast (sharing) | Slow (copying) |
| Implementation | Eval + quote | Many reduction rules |
| Correctness | Haskell guarantees | Must prove |
| Termination | Inherit from host | Must ensure |

---

## Connection to Type Theory

NbE is essential for:
- **Dependent types**: Types contain terms, need normalization for equality
- **Proof assistants**: Coq, Agda, Lean use NbE
- **Type checking**: Check `A ≡ B` by normalizing both
- **Logical relations**: NbE closely related to normalization proofs

---

## Further Reading

- Berger & Schwichtenberg (1991): Original NbE paper
- Coquand & Dybjer (1997): NbE for dependent types
- Abel (2013): Comprehensive treatment
- Löh, McBride, Swierstra (2010): Tutorial implementation
- Kovács (2022): Elaboration zoo (modern implementations)

---

## Next Steps

- **Chapter 19**: Bidirectional type checking (uses NbE)
- **Chapter 20**: Denotational semantics
- **Practice**: Implement NbE for STLC, then extend to Pi types
