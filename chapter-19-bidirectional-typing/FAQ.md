# Chapter 19: Bidirectional Type Checking - Frequently Asked Questions

## Conceptual Questions

### Q: What is bidirectional type checking?

**A:** Bidirectional type checking is a technique that combines type inference and type checking using two mutually recursive judgments:

- **Inference (⇒)**: Compute the type from the term
- **Checking (⇐)**: Verify the term matches an expected type

The key insight is that introduction forms (lambdas, pairs, injections) are checked against an expected type, while elimination forms (application, projection, case) synthesize their types.

### Q: Why is it called "bidirectional"?

**A:** Because type information flows in two directions:

1. **Up (inference)**: Types are computed and returned
2. **Down (checking)**: Expected types are passed in and verified

This is different from:
- Pure inference: Types only flow up
- Pure checking: Types only flow down

### Q: What's the advantage over full type inference (like Hindley-Milner)?

**A:** Several advantages:

1. **Simpler**: No unification algorithm needed
2. **Predictable**: Clear rules for when inference works
3. **Extensible**: Easy to add new features
4. **Good errors**: Mode tells you what was expected
5. **Scales to dependent types**: Where full inference is undecidable

The tradeoff is requiring some annotations.

### Q: What's the advantage over fully annotated (Church-style) typing?

**A:** Fewer annotations! With bidirectional typing:

- Lambda parameters often don't need annotations (when checking)
- Pair components don't need annotations (type comes from outside)
- Only need annotations where inference fails

### Q: What's the subsumption rule?

**A:** Subsumption is the bridge between modes:

```
Γ ⊢ e ⇒ A    A = B
────────────────────
Γ ⊢ e ⇐ B
```

It says: if we can infer type A for e, and A equals the expected type B, then checking succeeds.

This is the "fallback" rule in checking mode. It's tried after all introduction-specific rules.

### Q: What does "introduction forms check, elimination forms infer" mean?

**A:**

**Introduction forms** create values:
- Lambda creates functions
- Pair creates products
- inl/inr create sums

These are ambiguous without context (which function type? which product type?), so they need an expected type—they *check*.

**Elimination forms** use values:
- Application uses functions
- Projection uses products
- Case uses sums

These extract type information from what they operate on—they *infer*.

## Technical Questions

### Q: When should I add a type annotation?

**A:** Add an annotation when:

1. You have an unannotated lambda in inference position:
   ```
   \x. x           -- Can't infer
   (\x. x : A -> A)  -- Now inferrable
   ```

2. You're at the top level without an expected type:
   ```
   main = (\x. x : Int -> Int) 5
   ```

3. The compiler can't figure out which type you want:
   ```
   [] : List Int   -- Which list type?
   ```

### Q: How do I implement `infer` and `check`?

**A:**
```haskell
infer :: Ctx -> Term -> Either TypeError Type
infer ctx (Var x) = lookupVar ctx x
infer ctx (LamAnn x ty body) = do
  bodyTy <- infer (extend x ty ctx) body
  return (TyArr ty bodyTy)
infer ctx (App f arg) = do
  fTy <- infer ctx f
  case fTy of
    TyArr a b -> check ctx arg a >> return b
    _ -> throwError "Expected function"
infer ctx (Ann e ty) = check ctx e ty >> return ty

check :: Ctx -> Term -> Type -> Either TypeError ()
check ctx (Lam x body) (TyArr a b) =
  check (extend x a ctx) body b
check ctx (Pair e1 e2) (TyProd a b) =
  check ctx e1 a >> check ctx e2 b
-- Fallback: subsumption
check ctx e expected = do
  inferred <- infer ctx e
  unless (inferred == expected) $
    throwError (TypeMismatch expected inferred)
```

### Q: How do I add a new construct?

**A:** Decide its mode based on whether it's intro or elim:

**Introduction (checking):**
```haskell
check ctx (MyIntro e) (MyType a) =
  check ctx e a

-- Must also handle subsumption fallback
```

**Elimination (inference):**
```haskell
infer ctx (MyElim e) = do
  ty <- infer ctx e
  case ty of
    MyType a -> return a
    _ -> throwError "Expected MyType"
```

### Q: How do I handle polymorphism?

**A:** Type abstraction checks, type application infers:

```haskell
-- Checking: Λα. e ⇐ ∀α. A
check ctx (TyLam a e) (TyForall a' body) =
  check ctx e (subst a' (TyVar a) body)

-- Inference: e [A] ⇒ B[α := A]
infer ctx (TyApp e ty) = do
  eTy <- infer ctx e
  case eTy of
    TyForall a body -> return (subst a ty body)
    _ -> throwError "Expected forall"
```

### Q: How do de Bruijn indices/levels work with bidirectional typing?

**A:** They work the same as in other systems! The key is that:

- Contexts map indices/levels to types
- When entering a binder, extend the context
- Subsumption compares types, which may need alpha-equivalence

Levels are often preferred because fresh variable generation is simpler.

## Common Confusions

### Q: Can a term be both inferred and checked?

**A:** Yes! Many terms work in both modes.

For example, `true`:
- Infers to `Bool`
- Checks against `Bool` (via subsumption)

The key is that checking mode falls back to subsumption, which invokes inference.

### Q: Why does application mode-switch on the argument?

**A:** In `f x`:
1. We **infer** `f`'s type to get `A → B`
2. We **check** `x` against `A` (from step 1)
3. We return `B`

The mode switch happens because once we know the function type, we know what the argument should be. It would be wasteful to infer the argument's type only to compare it.

### Q: What if subsumption always fails?

**A:** This means the term can only be checked, not inferred. Example:

```
λx. x
```

- Subsumption tries: infer (λx. x) = ???
- No inference rule applies to unannotated lambda
- Subsumption fails
- The only way to type `λx. x` is in checking mode

### Q: How does bidirectional typing relate to dependent types?

**A:** Bidirectional typing is essential for dependent types because:

1. **Types contain terms**: `Vec n` depends on `n`
2. **Type equality requires normalization**: Is `Vec (1+1)` equal to `Vec 2`?
3. **Modes guide reduction**: Only normalize when switching modes

Most dependently-typed languages (Agda, Idris, Coq) use bidirectional typing.

### Q: What about type inference with unification?

**A:** You can combine bidirectional typing with unification for "local type inference":

1. Use unification variables for unknown types
2. Generate constraints during bidirectional checking
3. Solve constraints
4. Check that all variables are solved

This is more complex but allows fewer annotations.

## Troubleshooting

### Q: I get "Cannot infer" for my term. What do I do?

**A:** Either:
1. Add an annotation: `(e : T)`
2. Use in checking mode: `:check e : T`
3. Provide more annotations inside `e`

Check which subterm is causing the issue—it's usually an unannotated lambda or intro form.

### Q: Type mismatch but I think the types are equal.

**A:** Check:
1. Are types normalized? `1+1` vs `2`
2. Are names alpha-equivalent? `∀α.α` vs `∀β.β`
3. Are there invisible differences? (spaces, unicode)

### Q: My recursive function doesn't type check.

**A:** Recursive functions often need annotations:

```
fix (\f. \n. if n == 0 then 1 else n * f (n-1))
```

This needs annotation on `f` or the whole expression:
```
fix (\(f : Nat -> Nat). \n. ...) : Nat -> Nat
```

### Q: I added an annotation but it still doesn't work.

**A:** Check:
1. Is the annotation in the right place? Needs to wrap what can't be inferred.
2. Is the type syntactically correct?
3. Are type variables bound?

```
(\x. x : forall a. a -> a)  -- a is bound in the annotation
((\x. x) : forall a. a -> a)  -- Different! Annotation on application
```
