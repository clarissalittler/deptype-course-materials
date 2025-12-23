# Chapter 16: Homotopy Type Theory - Common Mistakes

This guide covers frequent errors when learning HoTT.

---

## Mistake 1: Thinking Paths Are Just Booleans

### The Problem
Treating `Id A a b` as simply true or false.

### Wrong Thinking
```
a = b is either true or false
```

### Correct Understanding
```
Id A a b is a TYPE
- Its elements are proofs/paths
- There may be 0, 1, or many paths!
- Different paths may not be equal
```

### How to Remember
> "Id A a b is a TYPE of paths, not a boolean."

---

## Mistake 2: Ignoring Higher Paths

### The Problem
Assuming any two paths between the same points are equal.

### Wrong Thinking
```
If p, q : Id A a b, then p = q
-- This is UIP, which is NOT assumed in HoTT!
```

### Correct Understanding
```
p and q might be DIFFERENT paths
Id (Id A a b) p q might be empty or have paths
```

The circle S¹ has non-trivial paths!

### How to Remember
> "Paths can be different. Check the higher structure."

---

## Mistake 3: Forgetting J's Computation Rule

### The Problem
Expecting J to compute on all paths.

### Wrong Expectation
```
J C base a b p = base ???  -- For any p
```

### Correct Understanding
```
J C base a a refl = base a    -- Only for refl!
J C base a b p = ???           -- Stuck if p ≠ refl
```

J computes (gives definitional equality) only on refl.

### How to Remember
> "J computes on refl. Other paths: propositional only."

---

## Mistake 4: Wrong Motive in J

### The Problem
Using incorrect motive type in J.

### The Correct Pattern
```
J : (C : (x y : A) → Id A x y → Type) → ...
```

C takes THREE arguments: x, y, and a path from x to y.

### Wrong Motive
```
C = λx. Id A x x    -- Only one argument!
C = λx y. Nat       -- Missing path argument!
```

### Correct Motive
```
C = λx y p. Id A y x    -- For sym
C = λx y p. P x → P y   -- For transport
```

### How to Remember
> "C takes (x : A) (y : A) (p : Id A x y)."

---

## Mistake 5: Confusing Definitional and Propositional Equality

### The Problem
Expecting definitional equality everywhere.

### The Difference
**Definitional equality** (≡): Holds by computation
```
sym refl ≡ refl    -- Reduces immediately
```

**Propositional equality** (=): Requires a proof
```
trans p (sym p) = refl  -- True, but needs proof!
```

### Why It Matters
- Definitional: Can substitute freely, no explicit proof
- Propositional: Need to transport/coerce with the proof

### How to Remember
> "Computation gives definitional. Theorems give propositional."

---

## Mistake 6: Forgetting ap and transport

### The Problem
Manually trying to use paths without ap or transport.

### Wrong Approach
```
-- Have: p : Id Nat n m
-- Want: Id Nat (succ n) (succ m)
-- Wrong: Just use p somehow...
```

### Correct Approach
```
ap succ p : Id Nat (succ n) (succ m)
```

For dependent types:
```
-- Have: p : Id A a b, x : P a
-- Want: P b
transport P p x : P b
```

### How to Remember
> "ap for non-dependent, transport for dependent."

---

## Mistake 7: Wrong Direction with sym

### The Problem
Confusing which direction sym reverses.

### The Type
```
sym : Id A a b → Id A b a
--         ^^^       ^^^
--         from a→b  to b→a
```

### Example
```
-- Have: p : Id Nat 0 1
-- sym p : Id Nat 1 0
```

### How to Remember
> "sym swaps source and target."

---

## Mistake 8: Wrong Order in trans

### The Problem
Getting the argument order wrong for trans.

### The Type
```
trans : Id A a b → Id A b c → Id A a c
--          ^^^       ^^^       ^^^
--          first     then      result
```

The middle point (b) must match!

### Wrong
```
trans (Id A x y) (Id A z w)  -- y ≠ z, doesn't compose!
```

### Correct
```
trans p q where p : Id A x y, q : Id A y z
-- First path ends where second begins
```

### How to Remember
> "trans chains: end of first = start of second."

---

## Mistake 9: Expecting Commutativity

### The Problem
Thinking `trans p q = trans q p`.

### Reality
Path composition is NOT commutative!
```
trans p q ≠ trans q p   -- Different paths!
```

It IS associative:
```
trans (trans p q) r = trans p (trans q r)
```

### Intuition
Walking A→B→C is not the same as walking B→C→A (doesn't even type check!).

### How to Remember
> "Paths are associative, NOT commutative."

---

## Mistake 10: Misunderstanding Univalence

### The Problem
Thinking univalence says "all types are equal."

### Wrong
```
A = B for any A, B   -- NO!
```

### Correct
```
(A ≃ B) ≃ (A = B)
-- Equivalent types are equal
-- NOT: all types are equal
```

You need an equivalence first!

### How to Remember
> "Univalence: equivalence implies equality, not universal equality."

---

## Debugging Checklist

When HoTT proofs go wrong:

1. **Check path types**: Do endpoints match?
2. **Check J motive**: Three arguments (x, y, p)?
3. **Check computation**: Only refl computes with J
4. **Check ap/transport**: Using the right one?
5. **Check direction**: Is sym in right direction?
6. **Check composition**: trans endpoints match?

---

## Practice Problems

### Problem 1: Find the Error

```
sym : Id A a b → Id A a b   -- What's wrong?
```

<details>
<summary>Answer</summary>

Return type is wrong!
```
sym : Id A a b → Id A b a   -- Endpoints swap!
```
</details>

### Problem 2: Fix This

```
ap : (f : A → B) → Id A a b → Id A (f a) (f b)
```

<details>
<summary>Answer</summary>

Result should be in B, not A!
```
ap : (f : A → B) → Id A a b → Id B (f a) (f b)
```
</details>

### Problem 3: Why Wrong?

```
trans : Id A a b → Id A c d → Id A a d
```

<details>
<summary>Answer</summary>

Middle points don't match! b ≠ c in general.
```
trans : Id A a b → Id A b c → Id A a c
-- Second path must START where first ENDS
```
</details>
