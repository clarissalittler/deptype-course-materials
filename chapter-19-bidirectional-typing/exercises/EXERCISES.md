# Chapter 19: Bidirectional Type Checking - Exercises

## Learning Objectives

After completing these exercises, you will:
- Understand the fundamental distinction between type synthesis and checking
- Know when terms require annotations vs. when types can be inferred
- Be able to extend bidirectional systems with new constructs
- Appreciate the design tradeoffs in minimizing annotations

---

## Exercise 1: Mode Classification (Conceptual)

For each of the following terms, determine whether their types can be **inferred** (⇒)
or only **checked** (⇐), and explain why:

1. `true`
2. `\x. x`
3. `\(x : Bool). x`
4. `f x` (where `f` and `x` are in context)
5. `(true, false)`
6. `fst p` (where `p` is in context)
7. `inl true`
8. `(\x. x : Bool -> Bool)`

**Hint:** Introduction forms are checked, elimination forms are inferred.

---

## Exercise 2: Derivation Trees

Write out the full bidirectional typing derivation for:

```
⊢ (\(x : Bool). x) true ⇒ Bool
```

Use the rules:
```
Γ, x:A ⊢ e ⇒ B
─────────────────────────
Γ ⊢ (λ(x:A). e) ⇒ A → B

Γ ⊢ e1 ⇒ A → B    Γ ⊢ e2 ⇐ A
────────────────────────────────
Γ ⊢ e1 e2 ⇒ B

Γ ⊢ e ⇒ A    A = B
────────────────────
Γ ⊢ e ⇐ B
```

---

## Exercise 3: Annotation Placement

The following terms cannot be inferred as written. Add **minimal** annotations to make them inferrable:

1. `\x. \y. x`
2. `\f. \x. f (f x)`
3. `(inl true, inr zero)`
4. `\p. (snd p, fst p)`

**Goal:** Use as few annotations as possible while enabling inference.

---

## Exercise 4: Implement Unit Type Checking

Extend the type checker to handle the unit type more uniformly. Currently unit
is inferrable. Consider:

```haskell
-- What should happen here?
check ctx TmUnit TyUnit = ...
check ctx TmUnit otherTy = ...
```

Questions:
1. Should `unit` be checkable against any type?
2. What's the relationship between inference and checking for `unit`?
3. Implement proper handling and add tests.

---

## Exercise 5: Let Polymorphism

Our current implementation infers the type of the bound variable in `let`:

```haskell
Let x e1 e2 -> do
  t1 <- infer ctx e1
  infer (extendCtx x t1 ctx) e2
```

Extend this to support let-polymorphism, where:

```
let id = \(x : a). x in (id true, id zero)
```

Should type-check with `id` being polymorphic in each use.

**Hints:**
- Generalize the inferred type
- Track which type variables are free in the context
- Instantiate the polymorphic type at each use

---

## Exercise 6: Implement Subtyping

Add simple subtyping where `Nat <: Int` (imagine we had integers). Modify:

```haskell
-- Instead of:
unless (typeEq inferred expected) $
  throwError $ TypeMismatch expected inferred

-- Use:
unless (subtype inferred expected) $
  throwError $ TypeMismatch expected inferred
```

Implement `subtype :: Type -> Type -> Bool` with:
- Reflexivity: `A <: A`
- Function contravariance: if `A' <: A` and `B <: B'` then `A → B <: A' → B'`

---

## Exercise 7: Better Error Messages

Current errors lose positional information. Extend the system to track source locations:

1. Add source spans to the AST:
   ```haskell
   data Located a = L Span a
   type LTerm = Located Term'
   ```

2. Thread location through type checking:
   ```haskell
   data TypeError = TypeError Span TypeErrorKind
   ```

3. Print errors with context showing the source location

---

## Exercise 8: Bidirectional Case Analysis

Our current `Case` implementation infers the branches:

```haskell
Case scrut x1 e1 x2 e2 -> do
  t <- infer ctx scrut
  case t of
    TySum a b -> do
      t1 <- infer (extendCtx x1 a ctx) e1
      t2 <- infer (extendCtx x2 b ctx) e2
      ...
```

This means branches must be inferrable. Modify to support **checking** mode
for case expressions:

```haskell
check ctx (Case scrut x1 e1 x2 e2) expectedTy = do
  -- Check branches against expectedTy
  ...
```

What terms become typeable that weren't before?

---

## Exercise 9: Pattern Matching

Extend the language with pattern matching:

```haskell
data Pattern
  = PVar Name
  | PPair Pattern Pattern
  | PInl Pattern
  | PInr Pattern
  | PWild

data Term = ...
  | Match Term [(Pattern, Term)]
```

Implement bidirectional checking for patterns:
- When should pattern types be inferred vs checked?
- How do you bind variables in patterns?

---

## Exercise 10: Refinement Types Preview

Consider extending types with propositions:

```haskell
data Type = ...
  | TyRefined Type Predicate  -- { x : T | P }
```

How would bidirectional checking work?

1. When checking `e ⇐ {x:T | P}`:
   - First check `e ⇐ T`
   - Then verify `P[e/x]` holds

2. When inferring `e ⇒ T`:
   - Can we synthesize a refinement?
   - Or only check against given refinements?

Sketch the implementation.

---

## Challenge Problems

### Challenge A: Complete Bidirectional STLC

Implement a **complete** bidirectional type checker that:
- Infers principal types when possible
- Minimizes required annotations
- Provides good error messages

Test on:
```
(\f. f true) (\x. x)       -- Should infer Bool
let id = \x. x in id id    -- Should work with polymorphism
```

### Challenge B: Bidirectional with Holes

Add "holes" (unfinished parts of programs):

```haskell
data Term = ... | Hole Name
```

When checking `Hole name ⇐ T`, record that the hole needs type `T`.
Return all holes with their expected types after checking.

This is the foundation for type-driven program development.

### Challenge C: Implement Type Inference

Starting from bidirectional checking, implement full Hindley-Milner inference:

1. Add unification variables
2. Generate constraints during bidirectional traversal
3. Solve constraints
4. Generalize let-bound variables

Compare the implementation complexity with standard Algorithm W.

---

## Solutions

### Exercise 1 Solutions

1. `true` - **Inferred** (⇒): Boolean literals have a known type
2. `\x. x` - **Checked** (⇐): No annotation, need expected type to know `x`'s type
3. `\(x : Bool). x` - **Inferred** (⇒): Annotation provides input type
4. `f x` - **Inferred** (⇒): Application is elimination, infer function type
5. `(true, false)` - **Checked** (⇐): Pairs are introduction forms
6. `fst p` - **Inferred** (⇒): Projection is elimination
7. `inl true` - **Checked** (⇐): Injection is introduction, need sum type
8. `(\x. x : Bool -> Bool)` - **Inferred** (⇒): Annotation makes it inferrable

### Exercise 2 Solution

```
                                    ─────────────────── (Var)
                                    x:Bool ⊢ x ⇒ Bool
                     ─────────────────────────────────────── (LamAnn)
                     ⊢ (\(x:Bool). x) ⇒ Bool → Bool
                                                               ───────────────── (True)
                                                               ⊢ true ⇒ Bool
                                                            ───────────────────── (Sub)
                                                               ⊢ true ⇐ Bool
─────────────────────────────────────────────────────────────────────────────────────── (App)
                     ⊢ (\(x:Bool). x) true ⇒ Bool
```

### Exercise 3 Solutions

1. `\(x : A). \y. x` or `(\x. \y. x : A -> B -> A)`
2. `\(f : A -> A). \(x : A). f (f x)` (need both due to interaction)
3. `((inl true, inr zero) : (Bool + A, B + Nat))` (need full type)
4. `\(p : (A, B)). (snd p, fst p)` (type of p determines result)

---

## Reading

- Pierce, "Local Type Inference" (2000) - The foundational paper
- Dunfield & Krishnaswami, "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" (2013) - Modern treatment
- Chlipala, "Certified Programming with Dependent Types" - Bidirectional for dependent types
