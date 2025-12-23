# Chapter 16: Homotopy Type Theory - Frequently Asked Questions

## Conceptual Questions

### Q: What is Homotopy Type Theory?

**A:** HoTT is an approach to type theory that interprets types topologically:

| Concept | Traditional | HoTT |
|---------|-------------|------|
| Type | Set of values | Space |
| Term | Element | Point |
| a = b | Proposition | Path type |
| Proof of a = b | Truth value | Path from a to b |

This geometric view leads to new principles like univalence.

### Q: Why are types called "spaces"?

**A:** Types behave like topological spaces:
- They have "points" (terms)
- Points can be connected by "paths" (equalities)
- Paths can be connected by "homotopies" (2-paths)
- This continues infinitely

This structure is precisely that of an ∞-groupoid.

### Q: What's special about identity types in HoTT?

**A:** In HoTT, `Id A a b` is not just a proposition but a TYPE:
- Its elements are paths from a to b
- There can be 0, 1, or many paths
- Different paths may not be equal
- Paths form a groupoid structure

### Q: What is the J eliminator?

**A:** J is path induction—the elimination principle for identity types:

```
J : (C : (x y : A) → Id A x y → Type) →
    ((x : A) → C x x refl) →
    (a b : A) → (p : Id A a b) →
    C a b p
```

Key insight: To prove something for all paths, prove it for refl.

### Q: Why does J only need the refl case?

**A:** This is based on the principle that all "based paths" are contractible. Intuitively, any path can be continuously shrunk to a point. Technically, the space of paths starting from a fixed point is contractible.

### Q: What is univalence?

**A:** The univalence axiom says:
```
(A ≃ B) ≃ (A = B)
```

Equivalent types (isomorphic structures) are equal types. This is a powerful principle that isn't provable in ordinary type theory.

## Technical Questions

### Q: What does refl represent?

**A:** `refl a : Id A a a` is the reflexivity path—a constant path that stays at point a. Think of it as "no movement."

### Q: How do I reverse a path?

**A:** Use symmetry:
```
sym : Id A a b → Id A b a
sym refl = refl
```

### Q: How do I compose paths?

**A:** Use transitivity:
```
trans : Id A a b → Id A b c → Id A a c
trans refl q = q
```

Note: The endpoint of the first must match the start of the second.

### Q: What is ap?

**A:** ap (action on paths) shows functions are "continuous":
```
ap : (f : A → B) → Id A a b → Id B (f a) (f b)
ap f refl = refl
```

If there's a path from a to b, there's a path from f(a) to f(b).

### Q: What is transport?

**A:** Transport moves data along a path:
```
transport : (P : A → Type) → Id A a b → P a → P b
transport P refl x = x
```

Given a dependent type P over A and a path in A, we can move elements between fibers.

### Q: What are h-levels?

**A:**

| h-level | Name | Property |
|---------|------|----------|
| -2 | Contractible | Unique element up to path |
| -1 | Proposition | At most one element up to path |
| 0 | Set | Equality is propositional |
| 1 | Groupoid | 2-paths are propositional |
| n+1 | (n+1)-type | n-paths are propositional |

### Q: What are higher inductive types?

**A:** HITs are types specified with both point constructors and path constructors:

```
data S¹ where
  base : S¹
  loop : Id S¹ base base   -- A path constructor!
```

This lets us define spaces with non-trivial topology.

## Common Confusions

### Q: Is `Id A a b` the same as a boolean?

**A:** No! It's a TYPE whose elements are paths. It might have:
- Zero elements (a ≠ b)
- One element (like for sets)
- Many elements (for higher types)

### Q: Are all paths between the same points equal?

**A:** Not necessarily! This would be UIP (Uniqueness of Identity Proofs), which is NOT assumed in HoTT. The circle S¹ has distinct paths.

### Q: When does J compute?

**A:** J computes (gives definitional equality) only on refl:
```
J C base a a refl ≡ base a
```

For other paths, you only get propositional equality.

### Q: What's the difference between = and ≡?

**A:** In HoTT contexts:
- `=` or `Id`: Propositional equality (path types)
- `≡`: Definitional/judgmental equality (computation)

### Q: Is univalence constructive?

**A:** In vanilla HoTT, univalence is an axiom without computational content. Cubical type theory gives a constructive version where univalence computes.

## Troubleshooting

### Q: "Cannot unify endpoints"

**A:** Path composition requires matching endpoints:
```
trans p q requires: end of p = start of q
```

Check that your paths chain correctly.

### Q: "J motive has wrong type"

**A:** J's motive must take three arguments:
```
C : (x y : A) → Id A x y → Type
```

Not just one or two!

### Q: "Expected identity type"

**A:** Operations like sym, trans, ap require identity types:
```
sym : Id A a b → ...    -- Input must be Id type
```

Check your input has the right type.

### Q: "Paths don't reduce"

**A:** J only computes on refl. For other paths:
- You get a valid term
- But no definitional equality
- Use the propositional equality

### Q: How do I prove path equalities?

**A:** Use J with an appropriate motive, or:
1. Reduce both sides to same normal form
2. Use path algebra lemmas
3. Apply ap to simpler equalities

## Resources

### Q: Where can I learn more?

**A:**
1. **The HoTT Book** - The comprehensive reference
2. **Egbert Rijke's book** - Modern textbook
3. **Agda with --cubical** - Practical implementation
4. **Arend language** - Purpose-built for HoTT
5. **nLab** - Encyclopedia of categorical/homotopical concepts
