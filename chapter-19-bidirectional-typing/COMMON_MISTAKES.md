# Chapter 19: Bidirectional Type Checking - Common Mistakes

This guide covers frequent errors when learning bidirectional typing.

---

## Mistake 1: Wrong Mode for Construct

### The Problem
Using inference when checking is needed, or vice versa.

### Wrong Thinking
> "I'll just infer the type of `λx. x`."

### Correct Understanding
Unannotated lambdas don't infer—they only check:

```
λx. x          -- Cannot infer (no rule applies)
λx. x ⇐ A → A  -- Can check (use expected type)
```

### The Pattern
- **Intro forms** (lambda, pair, inl/inr): Check
- **Elim forms** (app, fst/snd, case): Infer

### How to Remember
> "Creating values needs context. Using values provides context."

---

## Mistake 2: Forgetting Subsumption Fallback

### The Problem
Not implementing the subsumption rule in checking mode.

### Wrong Code
```haskell
check ctx (Lam x e) (TyArr a b) = ...
check ctx (Pair e1 e2) (TyProd a b) = ...
check ctx _ _ = error "Cannot check"  -- WRONG!
```

### Correct Code
```haskell
check ctx (Lam x e) (TyArr a b) = ...
check ctx (Pair e1 e2) (TyProd a b) = ...
check ctx e expected = do           -- Fallback
  inferred <- infer ctx e
  unless (inferred == expected) $
    throwError (TypeMismatch expected inferred)
```

### Why This Matters
Many terms can be both inferred and checked. For example, `true` infers to `Bool` and can be checked against `Bool` via subsumption.

### How to Remember
> "If I can infer it and types match, checking succeeds."

---

## Mistake 3: Wrong Direction in Application

### The Problem
Trying to check the function or infer the argument.

### Wrong Rule
```
Γ ⊢ f ⇐ A → B    Γ ⊢ x ⇒ A
────────────────────────────
Γ ⊢ f x ⇒ B
```

### Correct Rule
```
Γ ⊢ f ⇒ A → B    Γ ⊢ x ⇐ A
────────────────────────────
Γ ⊢ f x ⇒ B
```

### Why It's This Way
- We need to *know* the function's type to know what to check the argument against
- We infer `f` to get `A → B`
- Then we can check `x` against `A`

### How to Remember
> "Function tells us the expected argument type."

---

## Mistake 4: Not Using Expected Type in Lambda Checking

### The Problem
Ignoring the expected type when checking a lambda.

### Wrong Code
```haskell
check ctx (Lam x e) (TyArr a b) = do
  -- Forgot to use 'a' for x's type!
  check ctx e b
```

### Correct Code
```haskell
check ctx (Lam x e) (TyArr a b) = do
  check (extend x a ctx) e b
                  ^
                  Uses 'a' from expected type!
```

### Why This Matters
The whole point of checking mode is that we know the expected type. For lambdas, this tells us the parameter type.

### How to Remember
> "Expected type tells lambda what its parameter type is."

---

## Mistake 5: Confusing Annotated vs Unannotated Lambdas

### The Problem
Treating `λx.e` and `λ(x:A).e` the same.

### The Difference

**Unannotated** (`λx.e`): Checked only
```
Γ, x:A ⊢ e ⇐ B
─────────────────────
Γ ⊢ (λx. e) ⇐ A → B
```

**Annotated** (`λ(x:A).e`): Inferred
```
Γ, x:A ⊢ e ⇒ B
──────────────────────
Γ ⊢ (λx:A. e) ⇒ A → B
```

### Why This Matters
Annotated lambdas provide their own type info, so they can be inferred. Unannotated ones need external type info.

### How to Remember
> "Annotation = I know my type. No annotation = tell me my type."

---

## Mistake 6: Not Switching Modes at Annotation

### The Problem
Staying in the same mode when hitting an annotation.

### Wrong Code
```haskell
infer ctx (Ann e ty) = do
  infer ctx e  -- WRONG: should check!
  return ty
```

### Correct Code
```haskell
infer ctx (Ann e ty) = do
  check ctx e ty  -- Switch to checking mode
  return ty
```

### Why This Matters
Annotations are the bridge between modes. In inference, we use the annotation to check, then return it as the inferred type.

### How to Remember
> "Annotation switches mode: check against it, then return it."

---

## Mistake 7: Wrong Type for Pair Components

### The Problem
Not decomposing the product type correctly.

### Wrong Code
```haskell
check ctx (Pair e1 e2) (TyProd a b) = do
  check ctx e1 (TyProd a b)  -- WRONG!
  check ctx e2 (TyProd a b)  -- WRONG!
```

### Correct Code
```haskell
check ctx (Pair e1 e2) (TyProd a b) = do
  check ctx e1 a  -- First component against first type
  check ctx e2 b  -- Second component against second type
```

### How to Remember
> "Product type = first type × second type. Match them up."

---

## Mistake 8: Checking When Term Can't Have Expected Type

### The Problem
Trying to check a term against an impossible type.

### Example
```haskell
check ctx (Lam x e) TyBool = ???  -- Lambda can't be Bool!
```

### Correct Approach
Let subsumption fail:
```haskell
check ctx (Lam x e) TyBool = do
  inferred <- infer ctx (Lam x e)  -- This will fail
  ...
```

Or add explicit pattern match:
```haskell
check ctx (Lam x e) ty@(TyArr a b) = ...
check ctx (Lam x e) ty =
  throwError (TypeMismatch ty "function type")
```

### How to Remember
> "Intro forms only check against their corresponding types."

---

## Mistake 9: Forgetting to Extend Context

### The Problem
Not adding bound variables to the context.

### Wrong Code
```haskell
check ctx (Lam x e) (TyArr a b) =
  check ctx e b  -- WRONG: x not in context!
```

### Correct Code
```haskell
check ctx (Lam x e) (TyArr a b) =
  check (extend x a ctx) e b  -- x : a added to context
```

### Why This Matters
Inside the lambda body, `x` is bound. Without extending the context, looking up `x` will fail.

### How to Remember
> "Binders extend the context."

---

## Mistake 10: Not Handling All Cases

### The Problem
Missing cases in infer or check.

### Symptom
Runtime error: "Non-exhaustive patterns"

### Example
```haskell
infer ctx (Var x) = ...
infer ctx (App f e) = ...
-- Forgot: LamAnn, Ann, TyApp, ...

check ctx (Lam x e) (TyArr a b) = ...
-- Forgot: Pair, Inl, Inr, TyLam, ...
```

### How to Fix
1. Use `-Wall` to catch missing patterns
2. Have a catch-all that errors clearly
3. Systematically go through all constructors

### How to Remember
> "Every term form needs a case somewhere."

---

## Debugging Checklist

When type checking fails unexpectedly:

1. **Check mode**: Are you inferring when you should check, or vice versa?
2. **Check subsumption**: Did you implement the fallback?
3. **Check context**: Are bound variables added?
4. **Check expected type**: For intros, are you using it correctly?
5. **Check annotation handling**: Mode switch happening?

---

## Practice Problems

### Problem 1: Find the Bug

```haskell
check ctx (Pair e1 e2) ty = do
  check ctx e1 ty
  check ctx e2 ty
```

<details>
<summary>Answer</summary>

Should decompose the product type:
```haskell
check ctx (Pair e1 e2) (TyProd a b) = do
  check ctx e1 a
  check ctx e2 b
check ctx (Pair e1 e2) ty =
  throwError "Expected product type"
```
</details>

### Problem 2: Mode Analysis

What mode(s) can `if c then t else e` be in?

<details>
<summary>Answer</summary>

Both modes work:

**Inference:**
```
Γ ⊢ c ⇐ Bool    Γ ⊢ t ⇒ A    Γ ⊢ e ⇒ A
─────────────────────────────────────────
Γ ⊢ if c then t else e ⇒ A
```

**Checking:**
```
Γ ⊢ c ⇐ Bool    Γ ⊢ t ⇐ A    Γ ⊢ e ⇐ A
─────────────────────────────────────────
Γ ⊢ if c then t else e ⇐ A
```

In inference mode, both branches must synthesize the same type.
</details>

### Problem 3: Why Doesn't This Work?

```
bidir> \x. \y. x
Cannot infer type
```

<details>
<summary>Answer</summary>

`λx. λy. x` has infinitely many types:
- `Bool → Bool → Bool`
- `Nat → Bool → Nat`
- `∀α. ∀β. α → β → α`
- etc.

Without an annotation or expected type, we can't pick one. Use:
```
bidir> (\x. \y. x : Bool -> Bool -> Bool)
```
or
```
bidir> :check \x. \y. x : forall a. forall b. a -> b -> a
```
</details>
