# Chapter 16: Homotopy Type Theory - Exercises

## Overview

These exercises explore Homotopy Type Theory (HoTT), which interprets types as
spaces and equalities as paths. This perspective provides new insights into
type theory and leads to powerful new axioms like univalence.

---

## Exercise 1: Path Basics (Conceptual)

### 1.1 Understanding Identity Types

In HoTT, the identity type `Id A a b` (also written `a =_A b`) represents
a **path** from `a` to `b` in the space `A`.

**Question:** For each of the following types, describe what paths look like:
1. `Id Bool true false` - Are there any inhabitants?
2. `Id Nat 0 0` - What paths exist?
3. `Id (Nat → Nat) f g` - What would a path between functions mean?

### 1.2 Path Induction

The J eliminator (path induction) says: to prove something for all paths,
it suffices to prove it for reflexivity paths.

```
J : (C : (x y : A) → (x = y) → Type) →
    ((x : A) → C x x refl) →
    (a b : A) → (p : a = b) → C a b p
```

**Question:** Why is this principle valid? Think about what it means for
a path to "connect" two points.

### 1.3 Based Path Induction

There's an equivalent form called based path induction:

```
J' : (a : A) → (C : (y : A) → (a = y) → Type) →
     C a refl →
     (b : A) → (p : a = b) → C b p
```

**Task:** Explain why J and J' are equivalent. Which feels more natural?

---

## Exercise 2: Path Algebra

### 2.1 Groupoid Laws

Paths form a groupoid structure. Verify these laws hold:

1. **Left identity:** `trans refl p = p`
2. **Right identity:** `trans p refl = p`
3. **Inverse law:** `trans p (sym p) = refl`
4. **Associativity:** `trans (trans p q) r = trans p (trans q r)`

**Task:** For each law, explain why it holds in our implementation. Can you
construct paths that demonstrate these?

### 2.2 Implementing Path Operations with J

The operations `sym`, `trans`, and `ap` can all be defined using J.

**Task:** Define sym using J:
```
-- sym : (p : a = b) → (b = a)
-- Hint: What motive C should you use?
sym p = J [???] (λx. refl [A] x) a b p
```

**Task:** Define trans using J:
```
-- trans : (p : a = b) → (q : b = c) → (a = c)
-- Hint: Fix one endpoint and induct on the other path
```

### 2.3 Action on Paths

The `ap` operation shows that functions respect paths:
```
ap : (f : A → B) → (p : a = b) → (f a = f b)
```

**Task:** Verify these properties:
1. `ap id p = p` (identity function preserves paths)
2. `ap (f ∘ g) p = ap f (ap g p)` (composition respects paths)
3. `ap f refl = refl` (functions preserve reflexivity)

---

## Exercise 3: Transport and Path Lifting

### 3.1 Understanding Transport

Transport moves values along paths:
```
transport : (P : A → Type) → (p : a = b) → P a → P b
```

**Question:** If `P x = (x = x)` (the type of loops at x), what does
`transport P p refl` give you? Explain.

### 3.2 Path Lifting

In topology, paths can be "lifted" along fibrations. In type theory:
```
lift : (P : A → Type) → (p : a = b) → (u : P a) →
       Σ(v : P b). transport P p u = v
```

**Task:** Explain why this always exists (hint: what is v?).

### 3.3 Dependent Paths

A dependent path over `p : a = b` in a family `P : A → Type` is:
```
PathOver P p u v ≡ transport P p u = v
```

**Task:** Show that if `P` is constant (doesn't depend on the base point),
then `PathOver P p u v ≃ (u = v)`.

---

## Exercise 4: Higher Paths

### 4.1 Paths Between Paths

Since paths are themselves elements of a type, we can have paths between paths!
```
Id (Id A a b) p q  -- a 2-path or homotopy from p to q
```

**Question:** What does a 2-path represent geometrically?

### 4.2 Loop Spaces

The loop space of A at a is:
```
Ω(A, a) = Id A a a
```

This is the type of loops at a. The double loop space is:
```
Ω²(A, a) = Id (Id A a a) refl refl
```

**Question:** What are elements of Ω²(A, a)? Draw a picture.

### 4.3 The Eckmann-Hilton Argument

For 2-loops (elements of Ω²), there are two natural ways to compose:
- Vertical composition (stacking)
- Horizontal composition (side by side)

**Amazing fact:** These two operations are equal, and moreover, they are
commutative! This is the Eckmann-Hilton argument.

**Task:** Think about why this might be true geometrically.

---

## Exercise 5: Function Extensionality

### 5.1 The Problem

In ordinary type theory, we can't prove:
```
funext : (f g : A → B) → ((x : A) → f x = g x) → f = g
```

This says: pointwise equal functions are equal.

**Question:** Why might this be problematic to prove using only J?
(Hint: think about what J gives you vs. what you need)

### 5.2 Weak Function Extensionality

A weaker form is:
```
weakFunext : (f g : A → B) → ((x : A) → f x = g x) → isContr(f = g)
```

This says the path space is contractible (has a unique element up to path).

**Task:** Explain why weak funext follows from funext.

### 5.3 Happly

The inverse of funext is always definable:
```
happly : (f = g) → ((x : A) → f x = g x)
happly p x = ap (λf. f x) p
```

**Task:** Verify that this definition type-checks.

---

## Exercise 6: The Univalence Axiom

### 6.1 Type Equivalence

An equivalence between types A and B is a function with a quasi-inverse:
```
A ≃ B = Σ(f : A → B). Σ(g : B → A).
        ((x : A) → g(f(x)) = x) × ((y : B) → f(g(y)) = y)
```

**Task:** Show that `A ≃ A` (every type is equivalent to itself).

### 6.2 idtoeqv

We can turn paths into equivalences:
```
idtoeqv : (A = B) → (A ≃ B)
idtoeqv p = transport (λX. X) p
```

**Question:** Why does transport give an equivalence?

### 6.3 The Univalence Axiom

Univalence says idtoeqv is itself an equivalence:
```
ua : (A ≃ B) ≃ (A = B)
```

In other words: **equivalent types are equal**.

**Question:** Why is this not provable in ordinary type theory?
What are the consequences if we assume it?

### 6.4 Boolean Negation

Consider the equivalence `not : Bool ≃ Bool`. By univalence, there's a path:
```
notPath : Bool = Bool
notPath = ua not
```

**Question:** What is `transport (λX. X) notPath true`?

---

## Exercise 7: Higher Inductive Types

### 7.1 The Circle

The circle S¹ is defined as a higher inductive type:
```
data S¹ : Type where
  base : S¹
  loop : base = base
```

**Question:** What makes this different from a regular inductive type?

### 7.2 Circle Induction

The induction principle for S¹:
```
S¹-ind : (P : S¹ → Type) →
         (b : P base) →
         (l : PathOver P loop b b) →
         (x : S¹) → P x
```

**Task:** Compare this to the induction principle for Bool. What's the
key difference?

### 7.3 The Fundamental Group

The fundamental group of S¹ is:
```
π₁(S¹) = Ω(S¹, base) = (base = base)
```

**Theorem:** π₁(S¹) ≃ ℤ

This says loops around the circle are classified by winding number!

**Task:** Explain intuitively why this theorem should be true.

---

## Challenge Problems

### Challenge 1: Encode-Decode

Use the encode-decode method to prove that `Nat = Nat` has exactly two
elements (the identity and... what else could there be?).

**Hint:** Consider what paths `0 = 0`, `(succ 0) = (succ 0)`, etc. exist.

### Challenge 2: Hedberg's Theorem

Prove: If A has decidable equality, then A is a set (all paths between
equal elements are equal).

```
hedberg : ((x y : A) → (x = y) + ¬(x = y)) → isSet A
```

### Challenge 3: The Suspension

Define the suspension of a type:
```
data Σ A : Type where
  north : Σ A
  south : Σ A
  merid : A → north = south
```

Show that Σ Bool ≃ S¹ (the suspension of Bool is the circle).

---

## Solutions Approach

For HoTT exercises:

1. **Think geometrically:** Types are spaces, paths are continuous paths,
   functions are continuous maps

2. **Use path induction:** Most proofs go by induction on paths; the key
   is choosing the right motive C

3. **Draw pictures:** Diagrams help visualize paths and homotopies

4. **Check dimensions:** A path in `A` is 1-dimensional, a path between
   paths is 2-dimensional, etc.

Remember:
- `refl` is the only path constructor
- J says: to prove P(p) for all paths p, prove P(refl)
- Transport moves data along paths
- Univalence is an axiom, not provable from J alone
