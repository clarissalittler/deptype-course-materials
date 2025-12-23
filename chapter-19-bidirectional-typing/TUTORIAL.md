# Chapter 19: Bidirectional Type Checking - Tutorial

This tutorial walks through bidirectional typing with step-by-step examples.

## Part 1: The Problem

### Type Checking vs Type Inference

**Type checking** (Church-style): Every binder has a type annotation
```
λ(x : Bool). x    -- Clearly Bool → Bool
```

**Type inference** (Curry-style): No annotations needed
```
λx. x    -- Infer: ∀α. α → α (via unification)
```

### The Middle Ground

Full inference is complex (unification, constraint solving) and sometimes undecidable. Full annotation is tedious.

**Bidirectional typing**: Annotate only where necessary.

The key insight:
- Some constructs have "obvious" types (variables, application)
- Some constructs need type context (unannotated lambdas)

## Part 2: Two Modes

### Inference Mode (⇒)

In inference mode, we *compute* the type from the term:

```
Γ ⊢ e ⇒ A    "In context Γ, term e synthesizes type A"
```

Examples:
- Variables: Look up in context
- Application: Infer function type, extract result type
- Annotations: Check against annotation, return it

### Checking Mode (⇐)

In checking mode, we *verify* the term against a known type:

```
Γ ⊢ e ⇐ A    "In context Γ, term e checks against type A"
```

Examples:
- Lambdas: Use expected function type for parameter
- Pairs: Use expected product type for components
- Injections: Use expected sum type

### Mode Switching

The modes call each other:

```
         ┌─────────────────────────────────────┐
         │           Subsumption               │
         │  Γ ⊢ e ⇒ A   A = B                 │
    ┌────┴──────────────────────────┐          │
    │                               ▼          ▼
[Infer] ─────────────────────── [Check]
    ▲                               │
    │                               │
    └───────────────────────────────┘
              Application
         Γ ⊢ f ⇒ A → B   Γ ⊢ x ⇐ A
```

## Part 3: The Rules

### Inference Rules

**Variable**
```
       x : A ∈ Γ
    ───────────────
      Γ ⊢ x ⇒ A
```
Variables always infer: just look up in context.

**Annotated Lambda**
```
      Γ, x:A ⊢ e ⇒ B
    ────────────────────────
      Γ ⊢ (λx:A. e) ⇒ A → B
```
Annotation provides the parameter type; infer the body type.

**Application**
```
      Γ ⊢ f ⇒ A → B    Γ ⊢ x ⇐ A
    ─────────────────────────────────
              Γ ⊢ f x ⇒ B
```
Infer function type, *check* argument against domain, return codomain.

**Annotation**
```
         Γ ⊢ e ⇐ A
    ─────────────────────
      Γ ⊢ (e : A) ⇒ A
```
Check term against annotation, then return the annotation.

### Checking Rules

**Lambda**
```
       Γ, x:A ⊢ e ⇐ B
    ─────────────────────
      Γ ⊢ (λx. e) ⇐ A → B
```
Expected type provides parameter type; check body against codomain.

**Pair**
```
      Γ ⊢ e₁ ⇐ A    Γ ⊢ e₂ ⇐ B
    ────────────────────────────────
          Γ ⊢ (e₁, e₂) ⇐ A × B
```
Expected type provides types for both components.

**Subsumption** (fallback)
```
      Γ ⊢ e ⇒ A    A = B
    ────────────────────────
          Γ ⊢ e ⇐ B
```
If we can infer type A, and it equals the expected type B, succeed.

## Part 4: Worked Examples

### Example 1: Identity Function

Type check `(λx. x : Bool → Bool)`:

```
Goal: {} ⊢ (λx. x : Bool → Bool) ⇒ ?
```

**Step 1**: Apply annotation rule
```
Check: {} ⊢ λx. x ⇐ Bool → Bool
Return type: Bool → Bool
```

**Step 2**: Apply lambda rule (checking)
```
Expected type is Bool → Bool, so:
  - Parameter type: Bool
  - Body type: Bool
Check: {x : Bool} ⊢ x ⇐ Bool
```

**Step 3**: Apply subsumption
```
Infer: {x : Bool} ⊢ x ⇒ Bool   (variable rule)
Bool = Bool? Yes!
Check succeeds.
```

**Result**: `Bool → Bool`

### Example 2: Function Application

Type check `(λ(x:Bool). x) true`:

```
Goal: {} ⊢ (λ(x:Bool). x) true ⇒ ?
```

**Step 1**: Apply application rule
```
Infer: {} ⊢ (λ(x:Bool). x) ⇒ A → B
Check: {} ⊢ true ⇐ A
Return: B
```

**Step 2**: Infer the function (annotated lambda)
```
Infer: {x:Bool} ⊢ x ⇒ Bool
So: {} ⊢ (λ(x:Bool). x) ⇒ Bool → Bool
```

**Step 3**: Check the argument
```
Check: {} ⊢ true ⇐ Bool
Via subsumption: Infer true ⇒ Bool, Bool = Bool? Yes!
```

**Result**: `Bool`

### Example 3: Pair Construction

Type check `((true, false) : Bool × Bool)`:

```
Goal: {} ⊢ ((true, false) : Bool × Bool) ⇒ ?
```

**Step 1**: Annotation rule
```
Check: {} ⊢ (true, false) ⇐ Bool × Bool
Return: Bool × Bool
```

**Step 2**: Pair rule
```
Check: {} ⊢ true ⇐ Bool
Check: {} ⊢ false ⇐ Bool
```

**Step 3**: Both via subsumption
```
true ⇒ Bool, Bool = Bool ✓
false ⇒ Bool, Bool = Bool ✓
```

**Result**: `Bool × Bool`

### Example 4: Why Unannotated Lambda Fails

Try to infer `λx. x`:

```
Goal: {} ⊢ λx. x ⇒ ?
```

We try each inference rule:
- Variable? No, it's a lambda.
- Annotated lambda? No, no annotation.
- Application? No, it's a lambda.
- Annotation? No, no annotation.

**No rule applies!** We cannot infer.

But we *can* check it:
```
Goal: {} ⊢ λx. x ⇐ Bool → Bool

Lambda rule:
  Expected: Bool → Bool
  Parameter type: Bool
  Body type: Bool
  Check: {x:Bool} ⊢ x ⇐ Bool ✓
```

## Part 5: Implementation

### The Type Checker

```haskell
infer :: Ctx -> Term -> Either TypeError Type
check :: Ctx -> Term -> Type -> Either TypeError ()
```

### Inference Cases

```haskell
infer ctx (Var x) =
  lookupVar ctx x

infer ctx (LamAnn x ty body) = do
  bodyTy <- infer (extend x ty ctx) body
  return (TyArr ty bodyTy)

infer ctx (App f arg) = do
  fTy <- infer ctx f
  case fTy of
    TyArr a b -> do
      check ctx arg a
      return b
    _ -> throwError "Expected function type"

infer ctx (Ann e ty) = do
  check ctx e ty
  return ty
```

### Checking Cases

```haskell
check ctx (Lam x body) (TyArr a b) =
  check (extend x a ctx) body b

check ctx (Pair e1 e2) (TyProd a b) = do
  check ctx e1 a
  check ctx e2 b

-- Fallback: subsumption
check ctx e expected = do
  inferred <- infer ctx e
  unless (inferred == expected) $
    throwError (TypeMismatch expected inferred)
```

## Part 6: Common Patterns

### Pattern: Annotation Trick

When inference fails, add an annotation:

```
λx. x                    -- Cannot infer
(λx. x : Bool → Bool)    -- Inferrable!
```

The annotation provides the missing type information.

### Pattern: Type Propagation

Checking mode propagates types inward:

```
Check: ((λx. x, λy. y) : (Bool → Bool) × (Nat → Nat))

By pair rule:
  Check: λx. x ⇐ Bool → Bool
  Check: λy. y ⇐ Nat → Nat
```

One annotation at the outside provides types for everything inside!

### Pattern: Polymorphism

Type abstraction is checked:
```
Check: (Λα. λx. x) ⇐ ∀α. α → α

By type abstraction rule:
  Check: λx. x ⇐ α → α
```

Type application is inferred:
```
Infer: f [Bool]   where f : ∀α. α → α

By type application rule:
  Infer: f ⇒ ∀α. α → α
  Return: Bool → Bool
```

## Practice Problems

### Problem 1: Derivation Tree

Write the full derivation for `(λ(f:Bool→Bool). λ(x:Bool). f x) not`:

<details>
<summary>Solution</summary>

```
1. Goal: {} ⊢ (λ(f:Bool→Bool). λ(x:Bool). f x) not ⇒ ?

2. Application rule:
   - Infer: {} ⊢ (λ(f:Bool→Bool). λ(x:Bool). f x) ⇒ A → B
   - Check: {} ⊢ not ⇐ A
   - Return: B

3. Infer annotated lambda:
   {f:Bool→Bool} ⊢ λ(x:Bool). f x ⇒ C
   So: {} ⊢ (λ(f:...). ...) ⇒ (Bool→Bool) → C

4. Continue:
   {f:Bool→Bool, x:Bool} ⊢ f x ⇒ D

   Application: f ⇒ Bool→Bool, x ⇐ Bool, return Bool
   So D = Bool, C = Bool → Bool

5. Full function type: (Bool→Bool) → Bool → Bool

6. Check not ⇐ (Bool→Bool)
   Via subsumption: not ⇒ Bool→Bool ✓

7. Result: Bool → Bool
```
</details>

### Problem 2: Mode Classification

Classify these as infer (⇒) or check (⇐):
1. `fst p`
2. `(a, b)`
3. `Λα. e`
4. `e [A]`
5. `case e of inl x → a | inr y → b`

<details>
<summary>Solution</summary>

1. `fst p` → **Infer** (elimination: extracts from pair)
2. `(a, b)` → **Check** (introduction: constructs pair)
3. `Λα. e` → **Check** (introduction: constructs polymorphic)
4. `e [A]` → **Infer** (elimination: uses polymorphic)
5. `case` → **Infer** (elimination: uses sum)
</details>

### Problem 3: Add Let Binding

Design bidirectional rules for `let x = e₁ in e₂`:

<details>
<summary>Solution</summary>

Let bindings can be in both modes!

**Inference:**
```
    Γ ⊢ e₁ ⇒ A    Γ, x:A ⊢ e₂ ⇒ B
    ────────────────────────────────
      Γ ⊢ (let x = e₁ in e₂) ⇒ B
```

**Checking:**
```
    Γ ⊢ e₁ ⇒ A    Γ, x:A ⊢ e₂ ⇐ B
    ────────────────────────────────
      Γ ⊢ (let x = e₁ in e₂) ⇐ B
```

Note: We always *infer* the bound expression to get its type for the body.
</details>
