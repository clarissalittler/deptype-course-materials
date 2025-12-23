# Chapter 19: Bidirectional Type Checking - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce bidirectional typing concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Mode Classification ⭐
Classify each construct as inference (⇒) or checking (⇐):

a) `fst p`
b) `(a, b)`
c) `λ(x:A). e`
d) `λx. e`
e) `e [A]`
f) `Λα. e`
g) `(e : A)`
h) `inl e`

### Problem 1.2: Can We Infer? ⭐
Which of these can have their type inferred (without expected type)?

a) `true`
b) `\x. x`
c) `\(x : Bool). x`
d) `(true, false)`
e) `(\x. x : Bool -> Bool)`
f) `inl true`

### Problem 1.3: Simple Derivations ⭐
Write the derivation for: `{} ⊢ true ⇒ ?`

### Problem 1.4: Variable Lookup ⭐
What type is inferred for `x` in context `{x : Nat, y : Bool}`?

### Problem 1.5: Annotation Effect ⭐
Explain why this fails: `{} ⊢ λx. x ⇒ ?`
But this succeeds: `{} ⊢ (λx. x : Bool → Bool) ⇒ ?`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Complete Derivation Trees ⭐⭐
Write full derivation trees for:

a) `{} ⊢ (λ(x:Bool). x) true ⇒ ?`
b) `{} ⊢ λx. x ⇐ Nat → Nat`
c) `{} ⊢ ((λx. x, λy. y) : (Bool → Bool) × (Nat → Nat)) ⇒ ?`

### Problem 2.2: Type Propagation ⭐⭐
Given the checking judgment:
```
{} ⊢ (λx. (x, λy. x)) ⇐ Bool → (Bool × (Nat → Bool))
```

Show how the expected type propagates through:
1. The outer lambda
2. The pair
3. The inner lambda

### Problem 2.3: Application Direction ⭐⭐
Explain why the application rule is:
```
Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
────────────────────────────────
Γ ⊢ e₁ e₂ ⇒ B
```

And NOT:
```
Γ ⊢ e₁ ⇐ A → B    Γ ⊢ e₂ ⇒ A
────────────────────────────────
Γ ⊢ e₁ e₂ ⇒ B
```

### Problem 2.4: Subsumption Usage ⭐⭐
For each, determine if subsumption is needed:

a) `{} ⊢ true ⇐ Bool`
b) `{x : Bool} ⊢ x ⇐ Bool`
c) `{} ⊢ λx. x ⇐ Bool → Bool`
d) `{} ⊢ (λ(x:Bool). x) ⇐ Bool → Bool`

### Problem 2.5: Polymorphism ⭐⭐
Write derivations for:

a) `{} ⊢ Λα. λ(x:α). x ⇐ ∀α. α → α`
b) `{f : ∀α. α → α} ⊢ f [Bool] true ⇒ ?`
c) `{} ⊢ (Λα. λx. x : ∀α. α → α) [Nat] ⇒ ?`

### Problem 2.6: Sum Types ⭐⭐
Given:
```
{} ⊢ inl true ⇐ Bool + Nat
```

a) Write the derivation
b) Why can't we infer the type of `inl true`?
c) What annotation would make it inferrable?

### Problem 2.7: Products and Projections ⭐⭐
Complete the derivation:
```
{p : Bool × Nat} ⊢ fst p ⇒ ?
```

Then check:
```
{} ⊢ (true, 5) ⇐ Bool × Nat
```

### Problem 2.8: Let Bindings ⭐⭐
Design bidirectional rules for `let x = e₁ in e₂`:

a) Inference rule
b) Checking rule
c) Explain why e₁ is always inferred

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Mutual Recursion ⭐⭐⭐
Design bidirectional rules for mutually recursive definitions:
```
letrec f : A = e₁
   and g : B = e₂
in e₃
```

Consider:
- Should this infer or check?
- How are type annotations used?
- What about the body types?

### Problem 3.2: Case Expressions ⭐⭐⭐
Design rules for:
```
case e of
| inl x -> e₁
| inr y -> e₂
```

Should it be in both modes? Write both inference and checking rules.

### Problem 3.3: Annotation Placement ⭐⭐⭐
Given the term:
```
λf. λg. λx. f (g x)
```

a) What's the minimal annotation to make this inferrable?
b) Show multiple valid placements
c) Which placement is most natural?

### Problem 3.4: Higher-Rank Types ⭐⭐⭐
Consider:
```
(λf. (f true, f 5)) : ?
```

a) What type would this need in a higher-rank system?
b) Why can't standard bidirectional typing handle this?
c) Sketch how Dunfield & Krishnaswami's algorithm would work

### Problem 3.5: Bidirectional Equality ⭐⭐⭐
Implement algorithmic equality checking for types with:
- Base types (Bool, Nat)
- Function types (A → B)
- Forall types (∀α. A)
- Type variables

### Problem 3.6: Pattern Matching ⭐⭐⭐
Design bidirectional rules for pattern matching:
```
match e with
| (x, y) -> e₁
```

Consider:
- What mode is the scrutinee?
- What mode are the branches?
- How do patterns bind variables?

---

## Implementation Exercises (60-90 minutes)

### Problem 4.1: Add Unit Type ⭐⭐
Extend the type checker with:
- Unit type: `Unit`
- Unit value: `unit`

Write:
a) The syntax extensions
b) The typing rules
c) The implementation in `infer` and `check`

### Problem 4.2: Add Booleans with If ⭐⭐
Add:
```
if e₁ then e₂ else e₃
```

Should it be in inference or checking mode (or both)? Implement it.

### Problem 4.3: Add Type Holes ⭐⭐
Support type holes `_` in annotations:
```
λ(x:_). x + 1
```

The hole should be:
a) Reported to the user
b) Solved if possible
c) Left as a metavariable otherwise

### Problem 4.4: Better Error Messages ⭐⭐
Improve error messages by tracking:
- Expected type (in checking mode)
- Inferred type (in inference mode)
- The term that failed

Design a good error type.

### Problem 4.5: Add Subtyping ⭐⭐⭐
Extend subsumption to support subtyping:
```
Γ ⊢ e ⇒ A    A <: B
────────────────────
Γ ⊢ e ⇐ B
```

Implement subtyping for:
- Reflexivity: `A <: A`
- Function contravariance: `A' <: A, B <: B' ⟹ (A → B) <: (A' → B')`

---

## Debugging Exercises (30 minutes)

### Debug 1: Wrong Mode ⭐
What's wrong with this code?
```haskell
infer ctx (Lam x body) = do
  bodyTy <- infer (extend x ??? ctx) body
  return (TyArr ??? bodyTy)
```

### Debug 2: Missing Context Extension ⭐
Find the bug:
```haskell
check ctx (Lam x body) (TyArr a b) =
  check ctx body b
```

### Debug 3: Wrong Argument Check ⭐⭐
What's wrong?
```haskell
infer ctx (App e1 e2) = do
  argTy <- infer ctx e2
  funTy <- infer ctx e1
  case funTy of
    TyArr a b | a == argTy -> return b
    _ -> throwError "Type mismatch"
```

### Debug 4: Pair Type Confusion ⭐⭐
Fix this:
```haskell
check ctx (Pair e1 e2) ty = do
  check ctx e1 ty
  check ctx e2 ty
```

### Debug 5: Forgotten Subsumption ⭐⭐
This code is incomplete:
```haskell
check ctx (Lam x body) (TyArr a b) =
  check (extend x a ctx) body b
check ctx (Pair e1 e2) (TyProd a b) =
  check ctx e1 a >> check ctx e2 b
-- What's missing?
```

---

## Theoretical Exercises (45 minutes)

### Theory 1: Mode Invariants ⭐⭐
Prove (informally) that:
- If `Γ ⊢ e ⇒ A` then A is unique
- If `Γ ⊢ e ⇐ A` succeeds, then `Γ ⊢ e ⇐ A'` fails for A ≠ A'

### Theory 2: Completeness ⭐⭐⭐
Show that if a term is well-typed in simply-typed lambda calculus with enough annotations, bidirectional typing will accept it.

### Theory 3: Decidability ⭐⭐⭐
Sketch why bidirectional type checking is decidable (assuming type equality is decidable).

### Theory 4: Minimal Annotations ⭐⭐⭐
For each term, find the minimal annotation to make it inferrable:

a) `λf. λx. f x`
b) `λx. (x, x)`
c) `λf. λg. λx. f (g x)`

Prove your annotations are minimal.

---

## Solutions

### Warm-Up Solutions

**1.1**: a) ⇒, b) ⇐, c) ⇒, d) ⇐, e) ⇒, f) ⇐, g) ⇒, h) ⇐

**1.2**: a) Yes, b) No, c) Yes, d) No (pair is intro), e) Yes, f) No (injection needs type)

**1.3**:
```
true : Bool ∈ {}  (built-in)
─────────────────
{} ⊢ true ⇒ Bool
```

**1.4**: `Nat` (look up in context)

**1.5**: Unannotated lambda has no inference rule; annotation provides type info

### Standard Solutions

**2.1a**:
```
                        x:Bool ∈ {x:Bool}
                        ─────────────────
    {x:Bool} ⊢ x ⇒ Bool
    ───────────────────────────────────
    {} ⊢ λ(x:Bool). x ⇒ Bool → Bool      {} ⊢ true ⇐ Bool
    ─────────────────────────────────────────────────────────
    {} ⊢ (λ(x:Bool). x) true ⇒ Bool
```

**2.2**:
1. Outer lambda: expects `Bool → ...`, so `x : Bool`
2. Pair: expects `Bool × ...`, so first component needs `Bool`
3. Inner lambda: expects `Nat → Bool`, so `y : Nat`, body needs `Bool`

**2.3**: We need to know the function's type to determine what to check the argument against. Inferring the argument wouldn't tell us what function type is needed.

**2.4**: a) Yes (subsumption), b) Yes (subsumption), c) No (lambda rule applies), d) Yes (subsumption after annotated lambda infers)

**2.5a**:
```
    {x:α} ⊢ x ⇐ α
    ─────────────────────
    {} ⊢ λ(x:α). x ⇐ α → α
    ──────────────────────────────
    {} ⊢ Λα. λ(x:α). x ⇐ ∀α. α → α
```

**2.6**:
a) By injection rule with checking
b) We don't know what the other component type is
c) `(inl true : Bool + Nat)`

**2.8**:
```
Inference:
    Γ ⊢ e₁ ⇒ A    Γ, x:A ⊢ e₂ ⇒ B
    ────────────────────────────────
    Γ ⊢ (let x = e₁ in e₂) ⇒ B

Checking:
    Γ ⊢ e₁ ⇒ A    Γ, x:A ⊢ e₂ ⇐ B
    ────────────────────────────────
    Γ ⊢ (let x = e₁ in e₂) ⇐ B
```
We infer e₁ to get its type for the binding.

### Challenge Solutions

**3.2**:
```
Inference:
    Γ ⊢ e ⇒ A + B    Γ,x:A ⊢ e₁ ⇒ C    Γ,y:B ⊢ e₂ ⇒ C
    ────────────────────────────────────────────────────
    Γ ⊢ case e of inl x -> e₁ | inr y -> e₂ ⇒ C

Checking:
    Γ ⊢ e ⇒ A + B    Γ,x:A ⊢ e₁ ⇐ C    Γ,y:B ⊢ e₂ ⇐ C
    ────────────────────────────────────────────────────
    Γ ⊢ case e of inl x -> e₁ | inr y -> e₂ ⇐ C
```

**3.3**: Minimal: `λ(f:A→B). λ(g:C→A). λ(x:C). f (g x)` or `(λf. λg. λx. f (g x) : (A→B)→(C→A)→C→B)`

**3.4**:
a) Needs `∀α. (α → α) → ...` (rank-2)
b) Standard bidirectional doesn't handle higher-rank
c) Would use instantiation and polymorphic subsumption

### Debug Solutions

**Debug 1**: Lambda isn't inferred, it's checked. Missing parameter type.

**Debug 2**: Should be `check (extend x a ctx) body b` - forgot to extend context.

**Debug 3**: Should check argument against expected type, not infer it:
```haskell
infer ctx (App e1 e2) = do
  funTy <- infer ctx e1
  case funTy of
    TyArr a b -> check ctx e2 a >> return b
    _ -> throwError "Expected function type"
```

**Debug 4**: Should decompose product type:
```haskell
check ctx (Pair e1 e2) (TyProd a b) = do
  check ctx e1 a
  check ctx e2 b
```

**Debug 5**: Missing subsumption fallback:
```haskell
check ctx e expected = do
  inferred <- infer ctx e
  unless (inferred == expected) $
    throwError (TypeMismatch expected inferred)
```

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 8 easy, 12 medium, 6 hard, 5 debug, 4 theory

**Note**: These problems complement the main exercises. Focus on understanding the mode-switching discipline!
