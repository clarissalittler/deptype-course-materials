# Chapter 16: Homotopy Type Theory - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce HoTT concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Type Identification ⭐
What are the types of these terms?

a) `refl [Nat] 5`
b) `sym (refl [Bool] true)`
c) `trans (refl [Nat] 0) (refl [Nat] 0)`
d) `ap (\x:Nat. succ x) (refl [Nat] 3)`

### Problem 1.2: Path Directions ⭐
For each, identify the source and target:

a) `p : Id A a b` goes from ? to ?
b) `sym p : Id A ? ?`
c) `trans p q : Id A ? ?` where `p : Id A a b`, `q : Id A b c`
d) `ap f p : Id B ? ?` where `f : A → B`, `p : Id A a b`

### Problem 1.3: Computation ⭐
What do these evaluate to?

a) `sym (refl [Nat] 0)`
b) `trans (refl [Nat] 5) (refl [Nat] 5)`
c) `ap (\x:Nat. x) (refl [Nat] 7)`
d) `transport (\x:Bool. Nat) (refl [Bool] false) 3`

### Problem 1.4: J Motive ⭐
For each goal, what should the motive C be?

a) To define sym, we need `C : ?`
b) To define transport, we need `C : ?`
c) To prove `trans refl p = p`, we need `C : ?`

### Problem 1.5: Path Composition ⭐
Given:
- `p : Id Nat 1 2`
- `q : Id Nat 2 3`
- `r : Id Nat 3 4`

What are the types of:
a) `trans p q`
b) `trans (trans p q) r`
c) `trans p (trans q r)`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Groupoid Laws ⭐⭐
Prove (informally with J) these laws:

a) **Left identity**: `trans refl p = p`
b) **Right identity**: `trans p refl = p`
c) **Left inverse**: `trans (sym p) p = refl`
d) **Right inverse**: `trans p (sym p) = refl`

For each, state the type of the result.

### Problem 2.2: Symmetry Properties ⭐⭐
Prove using J:

a) **Involution**: `sym (sym p) = p`
b) **Distributivity**: `sym (trans p q) = trans (sym q) (sym p)`
c) **Preservation**: `ap f (sym p) = sym (ap f p)`

### Problem 2.3: ap Properties ⭐⭐
Prove:

a) **Identity**: `ap id p = p` where `id = \x. x`
b) **Composition**: `ap (g . f) p = trans (ap f p) (ap g (ap f p))`
   Wait, this isn't quite right! Fix it.
c) **Composition (corrected)**: `ap (g . f) p = ap g (ap f p)`

### Problem 2.4: Transport Properties ⭐⭐
Prove:

a) **Concatenation**: `transport P (trans p q) x = transport P q (transport P p x)`
b) **Constant family**: For constant P, `transport (\_.T) p x = x`
c) **Dependent ap**: If `f : (x:A) → P x`, show how transport relates to ap

### Problem 2.5: Paths Between Paths ⭐⭐
These are 2-paths. Find their types:

a) Left identity law: `trans refl p = p`
   Type: `Id (Id A a b) ? ?`
b) Associativity: `trans (trans p q) r = trans p (trans q r)`
   Type: `Id (Id A a d) ? ?`

### Problem 2.6: J Derivations ⭐⭐
Derive these using J:

a) **Contractibility of singletons**: For any `a:A`, show
   `(b:A, p:Id A a b)` is contractible (has unique element up to path)
b) **Based path induction**: An alternative to J
c) **Transport in identity types**: `transport (Id A a) p refl = p`

### Problem 2.7: Function Extensionality ⭐⭐
Assume function extensionality:

```
funext : ((x:A) → Id B (f x) (g x)) → Id (A→B) f g
```

Prove:
a) `ap (\f. f x) (funext h) = h x`
b) Function extensionality is an equivalence

### Problem 2.8: Whiskering ⭐⭐
Define path "whiskering" operations:

a) **Left whisker**: Given `p : Id A a b` and `q,r : Id A b c` with `α : Id (Id A b c) q r`,
   construct `p * α : Id (Id A a c) (trans p q) (trans p r)`
b) **Right whisker**: Similarly for the other side
c) Show these satisfy the interchange law

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Eckmann-Hilton ⭐⭐⭐
Prove the Eckmann-Hilton argument:

a) For 2-paths at `refl : Id A a a`, show there are two composition operations
b) Prove they coincide
c) Prove they're commutative
d) Conclude higher groupoids are increasingly commutative

### Problem 3.2: Circle S¹ ⭐⭐⭐
Given the circle as a HIT:

```
data S¹ where
  base : S¹
  loop : Id S¹ base base
```

a) Define the eliminator for S¹
b) Compute `transport (λ_. Bool) loop true`
c) Show `Ω(S¹) ≃ Z` (the integers)
d) Implement `not : S¹ → S¹` that swaps the two halves

### Problem 3.3: Truncation Levels ⭐⭐⭐
Define the truncation levels:

a) **IsContr(A)**: A is contractible
b) **IsProp(A)**: A is a proposition (h-level -1)
c) **IsSet(A)**: A is a set (h-level 0)
d) Prove: If A is contractible, then A is a proposition

### Problem 3.4: Univalence Consequences ⭐⭐⭐
Assume univalence. Prove:

a) **Transport is equivalence**: `transport P p : P a ≃ P b`
b) **Path induction from univalence**: Derive J
c) **Function extensionality**: Prove it from univalence
d) **Equivalence extensionality**: Equivalent equivalences are equal

### Problem 3.5: Interval Type ⭐⭐⭐
The interval I has:

```
data I where
  i0, i1 : I
  seg : Id I i0 i1
```

a) Show every type is equivalent to `I → that_type`
b) Define path from `seg`
c) Show `I` is contractible
d) Use I to define function extensionality

### Problem 3.6: Pushouts ⭐⭐⭐
Pushouts are a HIT:

```
data Pushout (f:A→B) (g:A→C) where
  inl : B → Pushout f g
  inr : C → Pushout f g
  glue : (a:A) → Id (Pushout f g) (inl (f a)) (inr (g a))
```

a) Write the eliminator
b) Show the circle is a pushout
c) Define suspension using pushouts
d) Compute `Ω(ΣA)` (loop space of suspension)

---

## Debugging Exercises (30 minutes)

### Debug 1: Wrong Direction ⭐
What's wrong?

```
sym : Id A a b → Id A a b
```

Fix the type.

### Debug 2: Trans Mismatch ⭐
What's wrong?

```
trans : Id A a b → Id A c d → Id A a d
```

Fix the type.

### Debug 3: ap Type Error ⭐⭐
What's wrong?

```
ap : (f : A → B) → Id A a b → Id A (f a) (f b)
```

Fix the return type.

### Debug 4: J Motive ⭐⭐
Student's attempt at sym:

```
sym : Id A a b → Id A b a
sym p = J (\x. Id A x a) (\x. refl) a b p
```

What's wrong with the motive?

### Debug 5: Computation ⭐⭐
Student expects:

```
J C base a b p ≡ ... -- for any p
```

Explain why this doesn't compute in general.

### Debug 6: Path Composition ⭐⭐
What's wrong?

```
assoc : trans (trans p q) r = trans p (trans q r)
assoc = refl
```

Why doesn't this work?

---

## Theoretical Questions (30 minutes)

### Question 1: Why J? ⭐⭐
Explain:

a) Why is J sufficient for all path operations?
b) What does "paths are contractible" mean?
c) Why does J only compute on refl?
d) Could we have a different eliminator?

### Question 2: Higher Paths ⭐⭐
Explain:

a) What is a 2-path?
b) Give an example
c) Why doesn't UIP hold in HoTT?
d) What's an ∞-groupoid?

### Question 3: Univalence ⭐⭐⭐
Explain the univalence axiom:

a) What does `(A ≃ B) ≃ (A = B)` mean?
b) Why is this revolutionary?
c) What does it imply about transport?
d) Why can't we prove it in basic HoTT?

### Question 4: HITs ⭐⭐⭐
Explain higher inductive types:

a) How do they differ from ordinary types?
b) Why is the circle a HIT?
c) What's the difference between point and path constructors?
d) Can we encode HITs in normal type theory?

---

## Proof Exercises (45 minutes)

### Proof 1: Cancellation ⭐⭐
Prove using J:

```
Given p : Id A a b, q : Id A a b
If trans p (sym p) = refl
Then trans (sym p) (trans p q) = q
```

### Proof 2: ap Functoriality ⭐⭐
Prove:

```
ap (g ∘ f) p = ap g (ap f p)
```

Use J and the computation rule.

### Proof 3: Transport Concatenation ⭐⭐
Prove:

```
transport P (trans p q) x = transport P q (transport P p x)
```

### Proof 4: Associativity ⭐⭐⭐
Prove path composition is associative:

```
trans (trans p q) r = trans p (trans q r)
```

This is harder than it looks! You'll need to use J multiple times.

### Proof 5: Naturality of ap ⭐⭐⭐
Prove naturality:

```
Given f : A → B, p : Id A a b, q : Id A a b, α : Id (Id A a b) p q
Then: ap (ap f) α = ap f * α = α * ap f
```

Where * is whiskering.

---

## Solutions

### Warm-Up Solutions

**1.1**:
- a) `Id Nat 5 5`
- b) `Id Bool true true` (evaluates to `refl [Bool] true`)
- c) `Id Nat 0 0` (evaluates to `refl [Nat] 0`)
- d) `Id Nat (succ 3) (succ 3)` = `Id Nat 4 4`

**1.2**:
- a) from `a` to `b`
- b) `Id A b a` (from `b` to `a`)
- c) `Id A a c` (from `a` to `c`)
- d) `Id B (f a) (f b)`

**1.3**:
- a) `refl [Nat] 0`
- b) `refl [Nat] 5`
- c) `refl [Nat] 7`
- d) `3`

**1.4**:
- a) `C = λx y p. Id A y x`
- b) `C = λx y p. P x → P y`
- c) `C = λx y p. Id (Id A a y) (trans refl p) p`

**1.5**:
- a) `Id Nat 1 3`
- b) `Id Nat 1 4`
- c) `Id Nat 1 4`

### Standard Solutions

**2.1**: Each uses J with appropriate motive and base case.
- a) Use J on p, base case: `trans refl refl = refl` ✓
- b) Use J on p, base case: `trans refl refl = refl` ✓
- c) Use J twice, once for sym, once for trans
- d) Similar to c

**2.2**: All use J
- a) Motive: `C = λx y p. Id (Id A a b) (sym (sym p)) p`, base: `sym (sym refl) = refl`
- b) Induct on both paths
- c) Induct on p

**2.3**:
- a) Induct on p: `ap id refl = refl` ✓
- b) Corrected: Should be `ap g (ap f p)`, not trans
- c) Induct on p

**2.4**:
- a) Induct on both p and q
- b) transport along refl is identity
- c) Related via dependent paths (apd)

**2.6**:
- a) Show `(a, refl)` is the center of contraction
- b) Fix one endpoint, induct on the other
- c) Use J with motive about identity types

### Challenge Solutions

**3.1**: Eckmann-Hilton
- Two operations: horizontal and vertical composition of 2-paths
- They coincide via interchange law
- Both are commutative at higher levels

**3.2**: Circle
- Eliminator: specify what happens at base and loop
- Need dependent eliminator for full generality
- Loop space is ℤ via winding number

**3.3**: Truncation
- IsContr(A) = Σ(a:A). Π(x:A). Id A a x
- IsProp(A) = Π(x y:A). Id A x y
- IsSet(A) = Π(x y:A). IsProp(Id A x y)

**3.4**: From univalence
- Transport is equiv: follows from univalence directly
- J from univalence: use that equivalent types are equal
- Funext: functions are determined by pointwise equality

**3.5**: Interval
- I is contractible: seg witnesses
- Paths from I: use path abstraction
- Funext: use I to construct paths between functions

**3.6**: Pushouts
- Eliminator: specify images of inl, inr, and glue
- Circle: pushout of `* ← Bool → *`
- Suspension: pushout of `* ← A → *`
- Ω(ΣA) ≃ A (for pointed types)

### Debug Solutions

**Debug 1**: Should be `Id A b a` (endpoints swap)

**Debug 2**: Should be `Id A b c → ...` (middle points match)

**Debug 3**: Should be `Id B (f a) (f b)` (result type is B)

**Debug 4**: Motive should take 3 args: `\x y p. Id A y x`

**Debug 5**: J only computes on refl by definition. Other paths give propositional equality.

**Debug 6**: Associativity is a 2-path, not refl. Need to prove it with J.

### Theoretical Solutions

**Question 1**:
- J is universal: based paths are contractible
- All paths "look like" refl up to homotopy
- Only refl computes to preserve normalization
- Alternative: path induction (J is most fundamental)

**Question 2**:
- 2-path: path between paths
- Example: `trans refl p = p`
- UIP says all paths are equal—contradicts circle
- ∞-groupoid: infinite tower of path types

**Question 3**:
- Equivalent types can be identified
- Revolutionary: isomorphism = equality
- Transport becomes equivalence
- Requires interval type or cubical structure

**Question 4**:
- HITs have path constructors
- Circle: loop is a path constructor
- Point constructors create elements, path constructors create paths
- Not in vanilla type theory, need extension

### Proof Sketches

**Proof 1**: Use cancellation laws derived from J

**Proof 2**: Induct on p, both sides compute to refl

**Proof 3**: Induct on p, then on q

**Proof 4**: Induct on all three paths in sequence

**Proof 5**: Use Eckmann-Hilton to show commutativity at 2-path level

---

**Estimated Time**: 5-7 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 6 hard, 6 debug, 4 theory, 5 proof

**Note**: HoTT is deep! These problems scaffold understanding of paths and higher structure.
