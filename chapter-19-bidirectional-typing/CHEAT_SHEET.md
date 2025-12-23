# Chapter 19: Bidirectional Type Checking - Cheat Sheet

## Core Concept

**Bidirectional typing** combines type inference and type checking through two mutually recursive judgments, minimizing annotations while maintaining decidability.

**Key Insight**: Introduction forms are checked, elimination forms are inferred.

## The Two Judgments

```
Γ ⊢ e ⇒ A     "synthesize/infer type A for e"     (inference mode)
Γ ⊢ e ⇐ A     "check e against type A"            (checking mode)
```

## Mode Classification

| Construct | Mode | Reason |
|-----------|------|--------|
| **Variables** | ⇒ | Look up in context |
| **Annotated lambda** λ(x:A). e | ⇒ | Annotation provides type |
| **Application** e₁ e₂ | ⇒ | Infer function, check argument |
| **Annotation** (e : A) | ⇒ | Check against annotation, return it |
| **Unannotated lambda** λx. e | ⇐ | Need expected type for parameter |
| **Pairs** (e₁, e₂) | ⇐ | Need expected product type |
| **Injections** inl/inr | ⇐ | Need expected sum type |
| **Type abstraction** Λα. e | ⇐ | Need expected ∀ type |
| **Projections** fst/snd | ⇒ | Extract from pair |
| **Case** | ⇒ | Eliminate sum type |
| **Type application** e [A] | ⇒ | Instantiate polymorphism |

## Inference Rules (⇒)

### Variable
```
       x : A ∈ Γ
    ───────────────
      Γ ⊢ x ⇒ A
```

### Annotated Lambda
```
      Γ, x:A ⊢ e ⇒ B
    ────────────────────────
      Γ ⊢ (λx:A. e) ⇒ A → B
```

### Application
```
      Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
    ─────────────────────────────────
              Γ ⊢ e₁ e₂ ⇒ B
```

**Key**: Function is inferred, argument is checked against domain!

### Annotation
```
         Γ ⊢ e ⇐ A
    ─────────────────────
      Γ ⊢ (e : A) ⇒ A
```

### Projection
```
      Γ ⊢ e ⇒ A × B
    ─────────────────
      Γ ⊢ fst e ⇒ A

      Γ ⊢ e ⇒ A × B
    ─────────────────
      Γ ⊢ snd e ⇒ B
```

### Type Application
```
         Γ ⊢ e ⇒ ∀α. A
    ─────────────────────────
      Γ ⊢ e [B] ⇒ A[α := B]
```

## Checking Rules (⇐)

### Lambda
```
       Γ, x:A ⊢ e ⇐ B
    ─────────────────────
      Γ ⊢ (λx. e) ⇐ A → B
```

**Key**: Expected type provides parameter type!

### Pair
```
      Γ ⊢ e₁ ⇐ A    Γ ⊢ e₂ ⇐ B
    ────────────────────────────────
          Γ ⊢ (e₁, e₂) ⇐ A × B
```

### Sum Injections
```
         Γ ⊢ e ⇐ A
    ─────────────────────
      Γ ⊢ inl e ⇐ A + B

         Γ ⊢ e ⇐ B
    ─────────────────────
      Γ ⊢ inr e ⇐ A + B
```

### Type Abstraction
```
         Γ ⊢ e ⇐ A
    ─────────────────────
      Γ ⊢ (Λα. e) ⇐ ∀α. A
```

### Subsumption (Fallback)
```
      Γ ⊢ e ⇒ A    A = B
    ────────────────────────
          Γ ⊢ e ⇐ B
```

**Key**: If we can infer and types match, checking succeeds!

## Implementation Pattern

```haskell
-- The two mutually recursive functions
infer :: Ctx -> Term -> Either TypeError Type
check :: Ctx -> Term -> Type -> Either TypeError ()

-- Inference cases
infer ctx (Var x) = lookupVar ctx x
infer ctx (LamAnn x ty body) = do
  bodyTy <- infer (extend x ty ctx) body
  return (TyArr ty bodyTy)
infer ctx (App e1 e2) = do
  ty <- infer ctx e1
  case ty of
    TyArr a b -> check ctx e2 a >> return b
    _ -> throwError "Expected function type"
infer ctx (Ann e ty) = check ctx e ty >> return ty

-- Checking cases
check ctx (Lam x body) (TyArr a b) =
  check (extend x a ctx) body b
check ctx (Pair e1 e2) (TyProd a b) =
  check ctx e1 a >> check ctx e2 b
check ctx (Inl e) (TySum a b) =
  check ctx e a
check ctx (Inr e) (TySum a b) =
  check ctx e b

-- Fallback: subsumption
check ctx e expected = do
  inferred <- infer ctx e
  unless (inferred == expected) $
    throwError (TypeMismatch expected inferred)
```

## Common Patterns

### Pattern 1: The Annotation Trick

When inference fails, add an annotation:
```
λx. x                    -- Cannot infer
(λx. x : Bool → Bool)    -- Inferrable!
```

### Pattern 2: Type Propagation

Checking mode propagates types inward:
```
((λx. x, λy. y) : (Bool → Bool) × (Nat → Nat))

By pair rule:
  Check: λx. x ⇐ Bool → Bool  ✓
  Check: λy. y ⇐ Nat → Nat    ✓
```

### Pattern 3: Mode Switching at Annotations

Annotations are the bridge between modes:
```
In inference: (e : A)  →  check e against A, then return A
In checking:  already checking against expected type
```

## Quick Reference: When to Use Each Mode

### Use Inference (⇒) When:
- You have a variable (look it up)
- You have an annotated lambda
- You're applying a function
- You have an explicit annotation
- You're eliminating a value (fst, snd, case)

### Use Checking (⇐) When:
- You have an unannotated lambda
- You're constructing a pair
- You're injecting into a sum
- You're creating a polymorphic value (Λα. e)
- You need to verify a specific type

## Common Mistakes to Avoid

1. **Wrong mode for construct**
   - ✗ Trying to infer λx. x
   - ✓ Check λx. x against expected type

2. **Forgetting subsumption**
   - ✗ Only implementing intro forms in check
   - ✓ Add fallback: infer then compare

3. **Wrong direction in application**
   - ✗ Infer argument, check function
   - ✓ Infer function, check argument

4. **Not using expected type in lambda**
   - ✗ `check (Lam x e) (TyArr a b) = check e b`
   - ✓ `check (Lam x e) (TyArr a b) = check (extend x a) e b`

5. **Forgetting to extend context**
   - ✗ `check ctx (Lam x e) ty = ...` (x not in context)
   - ✓ `check (extend x a ctx) e b`

## Comparison with Other Approaches

| Approach | Annotations | Complexity | Decidable | Predictable |
|----------|-------------|------------|-----------|-------------|
| Church-style | All terms | Simple | Yes | Yes |
| Curry-style (HM) | None | High (unification) | Yes | Sometimes |
| **Bidirectional** | **Minimal** | **Medium** | **Yes** | **Yes** |
| Dependent types | Varies | Very high | Often no | No |

## Why Bidirectional?

1. **Minimal annotations**: Only where truly needed
2. **Predictable**: Clear rules for when inference succeeds
3. **Compositional**: Local checking, no global constraints
4. **Extensible**: Easy to add new constructs
5. **Good errors**: Mode indicates what was expected
6. **Scales to advanced features**: Higher-rank types, dependent types

## Extensions

### With Subtyping

Subsumption becomes:
```
Γ ⊢ e ⇒ A    A <: B
────────────────────
Γ ⊢ e ⇐ B
```

### With Higher-Rank Polymorphism

From Dunfield & Krishnaswami:
- Synthesize monotypes
- Check polytypes
- Instantiation at application

### With Dependent Types

Essential for dependent types:
- Types can contain terms
- Type equality requires evaluation
- Mode annotations guide when to reduce

## Debugging Checklist

When type checking fails:
1. Check mode: Are you inferring when you should check?
2. Check subsumption: Did you implement the fallback?
3. Check context: Are bound variables added?
4. Check expected type: For intros, are you using it?
5. Check annotation handling: Mode switch happening?

## Quick Examples

### Example 1: Identity Function
```
Infer: (λx. x : Bool → Bool) ⇒ ?

Annotation rule:
  Check: λx. x ⇐ Bool → Bool
  Return: Bool → Bool

Lambda rule (checking):
  Check: x ⇐ Bool in context {x : Bool}
  Via subsumption: x ⇒ Bool, Bool = Bool ✓

Result: Bool → Bool
```

### Example 2: Application
```
Infer: (λ(x:Bool). x) true ⇒ ?

Application rule:
  Infer: λ(x:Bool). x ⇒ Bool → Bool
  Check: true ⇐ Bool
  Return: Bool

Result: Bool
```

### Example 3: Why Unannotated Lambda Fails
```
Infer: λx. x ⇒ ?

Try each inference rule:
  - Variable? No
  - Annotated lambda? No
  - Application? No
  - Annotation? No

No rule applies! Cannot infer.

But we can check:
  Check: λx. x ⇐ Bool → Bool ✓
```

## Further Reading

1. **Pierce & Turner** - "Local Type Inference" (2000)
   - Foundational paper on bidirectional typing

2. **Dunfield & Krishnaswami** - "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" (2013)
   - Modern treatment with higher-rank types

3. **Löh, McBride & Swierstra** - "A Tutorial Implementation of a Dependently Typed Lambda Calculus" (2010)
   - Practical bidirectional implementation

## Next Steps

After mastering bidirectional typing:
- Implement higher-rank polymorphism
- Add algebraic effects
- Explore dependent types
- Study gradual typing
