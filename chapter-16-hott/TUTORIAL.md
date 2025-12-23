# Chapter 16: Homotopy Type Theory - Tutorial

This tutorial walks through the core concepts of HoTT with step-by-step examples.

## Part 1: The Big Picture

### A New Perspective

Homotopy Type Theory (HoTT) reinterprets type theory through the lens of topology:

| Type Theory | Topology/Geometry |
|-------------|-------------------|
| Type A | Space A |
| Term a : A | Point a in space A |
| a = b (identity type) | Path from a to b |
| Path between paths | Homotopy |

### Why This Matters

Traditional type theory: `a = b` is either true or false.

HoTT: `a = b` is a TYPE whose elements are PATHS from a to b!

```
Id A a b = the type of paths from a to b in A
```

### Multiple Paths?

In topology, there can be many paths between two points:

```
     ___p___
    /       \
   a         b
    \_______/
        q
```

In HoTT, `p` and `q` might be different elements of `Id A a b`.

## Part 2: Identity Types

### The Identity Type

```
Id A a b
```

Read as: "the type of proofs that a equals b in type A."

HoTT interpretation: "the type of paths from a to b in space A."

### Reflexivity

Every point has a trivial path to itself:

```
refl : (a : A) → Id A a a
```

`refl a` is the constant path—"stay at point a."

### Creating Paths

```
refl [Nat] 0 : Id Nat 0 0
-- A path from 0 to 0 (the trivial path)

refl [Bool] true : Id Bool true true
-- A path from true to true
```

## Part 3: Path Induction (J)

### The J Eliminator

J is the fundamental principle for working with paths:

```
J : (C : (x y : A) → Id A x y → Type) →
    ((x : A) → C x x refl) →
    (a b : A) → (p : Id A a b) →
    C a b p
```

### Understanding J's Components

1. **C** (the motive): What we want to prove about paths
   - `C x y p` is a type depending on endpoints x, y and path p

2. **Base case**: Proof for reflexivity
   - `(x : A) → C x x refl`
   - We prove C holds for all refl paths

3. **Result**: C holds for ALL paths
   - Given any a, b, p, we get `C a b p`

### The Key Insight

To prove something for all paths, it SUFFICES to prove it for refl!

Why? Intuitively, all paths are "homotopic" to constant paths (based paths are contractible).

### Computation Rule

```
J C base a a refl = base a
```

When you apply J to refl, you get back the base case.

## Part 4: Derived Operations

### Symmetry (sym)

Reverse a path:

```
sym : Id A a b → Id A b a

-- Definition using J:
sym p = J (λx y p. Id A y x) (λx. refl) a b p

-- Computation:
sym refl = refl
```

Intuition: Walking backwards along a path.

### Transitivity (trans)

Compose two paths:

```
trans : Id A a b → Id A b c → Id A a c

-- On reflexivity:
trans refl q = q
trans p refl = p

-- Computation:
trans refl refl = refl
```

Intuition: Walk path p, then walk path q.

### Action on Paths (ap)

Functions map paths to paths:

```
ap : (f : A → B) → Id A a b → Id B (f a) (f b)

-- Computation:
ap f refl = refl
```

Intuition: If a path connects a to b, and f is continuous, then f maps this path to a path connecting f(a) to f(b).

### Transport

Move data along a path:

```
transport : (P : A → Type) → Id A a b → P a → P b

-- Computation:
transport P refl x = x
```

Intuition: P is a "fibration" over A. A path in A lets us transport elements between fibers.

## Part 5: Path Algebra

### Groupoid Laws

Paths satisfy algebraic laws:

**Left Identity**:
```
trans refl p = p
```
Starting with the trivial path then walking p is just p.

**Right Identity**:
```
trans p refl = p
```
Walking p then staying put is just p.

**Inverse Law**:
```
trans p (sym p) = refl
```
Walking p then walking backwards is like staying put.

**Associativity**:
```
trans (trans p q) r = trans p (trans q r)
```
Grouping doesn't matter for path composition.

### Paths Between Paths

The laws above are themselves PATHS (2-paths):

```
leftId : Id (Id A a b) (trans refl p) p
```

This is a path between paths!

### Higher Structure

- 1-paths: Between points
- 2-paths: Between 1-paths
- 3-paths: Between 2-paths
- ...

This infinite structure makes types into ∞-groupoids.

## Part 6: Worked Examples

### Example 1: Symmetry of Symmetry

Prove: `sym (sym p) = p`

```
-- For any path p : Id A a b
-- We need: Id (Id A a b) (sym (sym p)) p

-- Base case (p = refl):
sym (sym refl)
= sym refl      -- sym refl = refl
= refl          -- sym refl = refl

-- So sym (sym refl) = refl, which equals p when p = refl ✓
```

### Example 2: ap Preserves Identity

Prove: `ap id p = p` where `id = λx. x`

```
-- For any path p : Id A a b
-- We need: Id (Id A a b) (ap id p) p

-- Base case (p = refl):
ap id refl
= refl          -- ap f refl = refl

-- And p = refl, so ap id refl = refl = p ✓
```

### Example 3: ap Preserves Composition

Prove: `ap f (trans p q) = trans (ap f p) (ap f q)`

```
-- Base case (p = refl, q = refl):
ap f (trans refl refl)
= ap f refl             -- trans refl refl = refl
= refl                  -- ap f refl = refl

trans (ap f refl) (ap f refl)
= trans refl refl       -- ap f refl = refl
= refl                  -- trans refl refl = refl

-- Equal! ✓
```

## Part 7: Univalence (Conceptual)

### The Statement

```
(A ≃ B) ≃ (A = B)
```

If A and B are equivalent types, they are equal types!

### What This Means

- Equivalent structures are identical
- Isomorphic types can be used interchangeably
- Function extensionality follows

### Example Implication

If we have `Nat ≃ List Unit` (both represent natural numbers), then `Nat = List Unit` and we can transport any property from one to the other.

## Practice Problems

### Problem 1: Basic Path

What is the type of `refl [Bool] false`?

<details>
<summary>Solution</summary>

`Id Bool false false`

A path from false to false.
</details>

### Problem 2: Symmetry

What does `sym (refl [Nat] 5)` evaluate to?

<details>
<summary>Solution</summary>

`refl [Nat] 5`

Because `sym refl = refl`.
</details>

### Problem 3: Transitivity

What does `trans (refl [Nat] 0) (refl [Nat] 0)` evaluate to?

<details>
<summary>Solution</summary>

`refl [Nat] 0`

Because `trans refl refl = refl`.
</details>

### Problem 4: ap

If `f = λx. succ x`, what is the type of `ap f (refl [Nat] 3)`?

<details>
<summary>Solution</summary>

`Id Nat (succ 3) (succ 3)` = `Id Nat 4 4`

ap f maps the path at 3 to a path at f(3) = 4.
</details>

### Problem 5: Why J?

Why can we define `sym` by only specifying what happens on `refl`?

<details>
<summary>Solution</summary>

The J eliminator (path induction) says that to define something for all paths, it suffices to define it for refl. This is because all paths are "based equivalent" to refl paths—roughly, any path can be continuously deformed to a constant path.
</details>
