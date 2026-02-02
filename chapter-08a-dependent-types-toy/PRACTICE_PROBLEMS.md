# Chapter 8: Full Dependent Types - Practice Problems

## Purpose
Master universe hierarchy, propositional equality, J eliminator, and inductive families.

---

## Warm-Up Problems (15 minutes)

### Problem 1.1: Universe Hierarchy ⭐
Determine universe levels:

a) `Nat : ?`
b) `Type₀ : ?`
c) `Type₀ → Type₀ : ?`
d) `(A : Type₀) → A → A : ?`
e) `Type₁ : ?`

### Problem 1.2: J Eliminator ⭐
Use J to prove:

a) Symmetry: `∀(x y : A). x ≡ y → y ≡ x`
b) Apply function: `∀(f : A → B). x ≡ y → f x ≡ f y`

### Problem 1.3: Inductive Families ⭐
Identify which are inductive families:

a) `Vec : Nat → Type → Type`
b) `Fin : Nat → Type`
c) `Eq : (A : Type) → A → A → Type`
d) `List : Type → Type`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Universe Polymorphism ⭐⭐
Write universe-polymorphic functions:

a) `id : (ℓ : Level) → (A : Typeℓ) → A → A`

b) `const : (ℓ₁ ℓ₂ : Level) → (A : Typeℓ₁) → (B : Typeℓ₂) → A → B → A`

c) `pair : (ℓ₁ ℓ₂ : Level) → (A : Typeℓ₁) → (B : Typeℓ₂) →
     A → B → Σ (A : Typeℓ₁) B`

### Problem 2.2: Propositional Equality ⭐⭐
Prove these using J eliminator:

a) **Transitivity**:
   ```
   trans : ∀(A : Type₀) (x y z : A).
     x ≡ y → y ≡ z → x ≡ z
   ```

b) **Congruence**:
   ```
   cong : ∀(A B : Type₀) (f : A → B) (x y : A).
     x ≡ y → f x ≡ f y
   ```

c) **Substitution**:
   ```
   subst : ∀(A : Type₀) (P : A → Type₀) (x y : A).
     x ≡ y → P x → P y
   ```

d) **Transport**:
   ```
   transport : ∀(A B : Type₀).
     A ≡ B → A → B
   ```

### Problem 2.3: Equality of Functions ⭐⭐
Function extensionality:

a) Define: `funext : ∀(A B : Type₀) (f g : A → B).
     (∀(x : A). f x ≡ g x) → f ≡ g`

b) Show this is NOT derivable from J (it's an axiom!)

c) Use funext to prove:
   ```
   (λx. x + 0) ≡ (λx. x)
   ```

### Problem 2.4: Inductive Families ⭐⭐
Define these inductive families:

a) **Well-typed terms**:
   ```
   data Tm : Ctx → Ty → Type where
     Var : ∀(Γ : Ctx) (τ : Ty). τ ∈ Γ → Tm Γ τ
     Lam : ∀(Γ : Ctx) (σ τ : Ty).
       Tm (Γ, σ) τ → Tm Γ (σ → τ)
     App : ∀(Γ : Ctx) (σ τ : Ty).
       Tm Γ (σ → τ) → Tm Γ σ → Tm Γ τ
   ```

b) **Sorted lists**:
   ```
   data Sorted : List Nat → Type where
     SNil : Sorted []
     SCons1 : ∀(x : Nat). Sorted [x]
     SCons2 : ∀(x y : Nat) (xs : List Nat).
       x ≤ y → Sorted (y :: xs) → Sorted (x :: y :: xs)
   ```

c) **Even natural numbers**:
   ```
   data Even : Nat → Type where
     EvenZ : Even 0
     EvenSS : ∀(n : Nat). Even n → Even (S (S n))
   ```

### Problem 2.5: Heterogeneous Equality ⭐⭐
John Major equality (JMEq):

a) Define: `data JMEq : ∀(A B : Type₀) (x : A) (y : B) → Type where
     JMRefl : ∀(A : Type₀) (x : A). JMEq A A x x`

b) Prove: `JMEq A B x y → A ≡ B`

c) Prove: `∀(A : Type₀) (x y : A). JMEq A A x y → x ≡ y`

d) When is JMEq needed vs regular equality?

### Problem 2.6: Quotient Types ⭐⭐
Simulate quotient types:

a) Define setoid (type with equivalence relation):
   ```
   Setoid : Type₁
   Setoid = Σ (A : Type₀)
            Σ (_≈_ : A → A → Type₀)
            (refl : ∀x. x ≈ x) ×
            (sym : ∀x y. x ≈ y → y ≈ x) ×
            (trans : ∀x y z. x ≈ y → y ≈ z → x ≈ z)
   ```

b) Functions respecting equivalence:
   ```
   _⟶_ : Setoid → Setoid → Type₁
   A ⟶ B = Σ (f : A.carrier → B.carrier)
            (∀x y. x ≈_A y → f x ≈_B f y)
   ```

c) Show: Integers as quotient of Nat × Nat

### Problem 2.7: Observational Type Theory ⭐⭐
Define observational equality:

a) `x ≃ y` means "x and y are observationally equal"
   (same behavior in all contexts)

b) Prove: `x ≡ y → x ≃ y` (propositional implies observational)

c) Show: `x ≃ y` does NOT always imply `x ≡ y`
   (functions can be extensionally equal but not propositionally)

### Problem 2.8: Univalence Axiom ⭐⭐
Understand Voevodsky's univalence:

a) Define equivalence of types:
   ```
   _≃_ : Type₀ → Type₀ → Type₀
   A ≃ B = Σ (f : A → B) (isEquiv f)
   ```

b) State univalence axiom:
   ```
   ua : ∀(A B : Type₀). (A ≃ B) ≃ (A ≡ B)
   ```

c) Use univalence to prove: `Bool ≡ Bool` has two proofs
   (identity and negation equivalence)

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Homotopy Type Theory ⭐⭐⭐
Paths as equivalences:

a) **Path space**:
   ```
   PathSpace : (A : Type₀) → A → A → Type₀
   PathSpace A x y = x ≡ y
   ```

b) **Path composition** (transitivity as concatenation):
   ```
   _∙_ : ∀(x y z : A). x ≡ y → y ≡ z → x ≡ z
   ```

c) **Path inverse** (symmetry as reversal):
   ```
   _⁻¹ : ∀(x y : A). x ≡ y → y ≡ x
   ```

d) Prove path composition is associative (up to higher path!)

### Problem 3.2: Cubical Type Theory ⭐⭐⭐
Understand cubical structure:

a) **Interval type** `I : Type`:
   - `i0, i1 : I` (endpoints)
   - Paths are functions `I → A`

b) Define path as:
   ```
   Path : (A : Type₀) → A → A → Type₀
   Path A x y = PathP (λ i. A) x y
   ```

c) **Path application**:
   ```
   _@_ : ∀(x y : A). Path A x y → I → A
   p @ i0 = x
   p @ i1 = y
   ```

d) Prove funext using cubical paths

### Problem 3.3: Induction-Recursion ⭐⭐⭐
Define universe à la Tarski:

a) **Universe codes**:
   ```
   data U : Type₁ where
     nat : U
     pi : (a : U) → (El a → U) → U
   ```

b) **Decoding function** (defined simultaneously):
   ```
   El : U → Type₀
   El nat = Nat
   El (pi a b) = (x : El a) → El (b x)
   ```

c) Show this cannot be expressed without induction-recursion

### Problem 3.4: Proof Irrelevance ⭐⭐⭐
Propositions vs sets:

a) Define: `isProp : Type₀ → Type₀`
   ```
   isProp A = ∀(x y : A). x ≡ y
   ```

b) Define: `isSet : Type₀ → Type₀`
   ```
   isSet A = ∀(x y : A) (p q : x ≡ y). p ≡ q
   ```

c) Prove: `isProp A → isSet A`

d) Show: `Nat` is a set but not a proposition

e) Show: `x ≡ y` (for x y : Nat) is a proposition

---

## Debugging Exercises (30 minutes)

### Debug 1: Universe Inconsistency ⭐⭐
What's wrong?
```
U : Type₀
U = Type₀    -- Girard's paradox!
```

**Fix**: Use universe hierarchy:
```
Type₀ : Type₁ : Type₂ : ...
```

### Debug 2: K Axiom ⭐⭐
Student assumes:
```
K : ∀(A : Type₀) (x : A) (p : x ≡ x). p ≡ refl
```

**Problem**: K is not derivable from J! It's an extra axiom.
With K, we get UIP (Uniqueness of Identity Proofs).
Without K, we can have multiple proofs of equality (HoTT).

### Debug 3: Pattern Matching on Refl ⭐⭐
What's the catch?
```
sym : ∀(x y : A). x ≡ y → y ≡ x
sym refl = refl    -- Looks simple!
```

**Behind the scenes**: This uses K axiom implicitly!
In HoTT, must use J eliminator explicitly.

### Debug 4: Definitional vs Propositional ⭐⭐
Student confused:
```
x + 0 = x           (definitionally by recursion on x)
0 + x = x           (NOT definitionally equal!)
```

Need proof for second:
```
lemma : ∀(x : Nat). 0 + x ≡ x
lemma = ... (by induction)
```

### Debug 5: Universe Levels ⭐⭐
What level?
```
List : Type₀ → Type???
```

**A**: `List : Type₀ → Type₀` (predicative)

But:
```
Set : Type₀ → Type???
```

If we want `Set A` to contain predicates `A → Type₀`:
```
Set : Type₀ → Type₁
```

Universe levels matter!

---

## Code Review Exercises (30 minutes)

### Review 1: Axiom K vs J ⭐⭐⭐
Compare proof styles:

**With K** (UIP holds):
```
sym : ∀(x y : A). x ≡ y → y ≡ x
sym refl = refl    -- Direct pattern match
```

**Without K** (HoTT):
```
sym : ∀(x y : A). x ≡ y → y ≡ x
sym {x} p = J (λ y _. y ≡ x) refl p
```

Discuss:
- Which is more intuitive?
- What do we lose with K?
- When does it matter?

### Review 2: Proof Relevance ⭐⭐⭐
Compare:

**Proof-irrelevant** (Coq, Agda with --prop):
```
Even : Nat → Prop
-- All proofs of Even 4 are equal
```

**Proof-relevant** (HoTT):
```
Even : Nat → Type₀
-- Different proofs of Even 4 may differ
```

When does proof relevance matter?

### Review 3: Extensionality ⭐⭐⭐
Three kinds:

**Function extensionality**:
```
(∀x. f x ≡ g x) → f ≡ g
```

**Propositional extensionality**:
```
(A ↔ B) → A ≡ B
```

**Univalence**:
```
(A ≃ B) ≃ (A ≡ B)
```

Which to assume? Compatibility?

---

## Solutions

### Warm-Up

**1.1**:
- a) `Nat : Type₀`
- b) `Type₀ : Type₁`
- c) `Type₀ → Type₀ : Type₁`
- d) `(A : Type₀) → A → A : Type₁`
- e) `Type₁ : Type₂`

**1.2**:
```
a) sym : ∀(x y : A). x ≡ y → y ≡ x
   sym {x} p = J (λ y _. y ≡ x) refl p

b) cong : ∀(f : A → B). x ≡ y → f x ≡ f y
   cong f p = J (λ y _. f x ≡ f y) refl p
```

**1.3**:
- a) ✓ Indexed by Nat
- b) ✓ Indexed by Nat
- c) ✓ Indexed by A, x, y
- d) ✗ Parameterized by Type (not indexed)

### Standard

**2.1**:
```
id : (ℓ : Level) → (A : Typeℓ) → A → A
id ℓ A x = x

const : (ℓ₁ ℓ₂ : Level) → (A : Typeℓ₁) → (B : Typeℓ₂) →
  A → B → A
const ℓ₁ ℓ₂ A B x y = x
```

**2.2**:
```
trans : ∀(x y z : A). x ≡ y → y ≡ z → x ≡ z
trans {x} p q = J (λ z _. x ≡ z) p q

subst : ∀(P : A → Type₀) (x y : A).
  x ≡ y → P x → P y
subst P x y p px = J (λ y _. P y) px p
```

**2.3**:
```
a) funext is an AXIOM (not derivable from J)

c) Using funext:
   funext Nat Nat (λx. x + 0) (λx. x)
     (λx. plus_zero x)
   where plus_zero : ∀x. x + 0 ≡ x (proved by induction)
```

**2.4**:
```
b) Sorted encodes that list is sorted as type

c) Even n is inhabited iff n is even (proposition as type!)
```

**2.5**:
```
b) By inversion on JMRefl

c) Use proof from (b) to transport

d) JMEq needed when types may differ (e.g., dependent pattern matching)
```

**2.8**:
```
c) Bool ≡ Bool has (at least) two proofs:
   - ua (≃-refl)
   - ua (≃-not)   where ≃-not is equivalence via negation
```

### Challenge

**3.1**: HoTT interprets equality as paths in topological spaces

**3.2**: Cubical gives computational interpretation of univalence

**3.3**: Induction-recursion allows mutually defined inductive type and function

**3.4**:
```
c) If all elements equal, all equalities between elements equal
d) 0 ≢ 1 (different)
e) Any two proofs of n ≡ m (for n m : Nat) are equal
```

### Debug

**Debug 1**: Type : Type leads to Girard's paradox (Russell-like)

**Debug 2**: K is independent of J (assuming only J is more general)

**Debug 3**: Pattern matching on refl uses K behind the scenes

**Debug 4**: Definitional equality is stricter than propositional

**Debug 5**: Universe levels track predicativity

### Review

**Review 1**: K is intuitive but limits us to sets (no higher structure)

**Review 2**: Proof relevance matters for higher-dimensional structure

**Review 3**: These axioms are compatible with intensional type theory

---

## Advanced Topics Preview

These problems touch on cutting-edge research:

1. **Homotopy Type Theory** (HoTT)
   - Equality as paths
   - Higher inductive types
   - Univalence axiom

2. **Cubical Type Theory**
   - Computational univalence
   - Interval type
   - Kan composition

3. **Observational Type Theory** (OTT)
   - Observational equality
   - Proof irrelevance

4. **Quotient Inductive Types** (QITs)
   - Higher inductive types
   - Constructive quotients

---

**Time**: 6-8 hours
**Focus**: Universe hierarchy and J eliminator are foundational

**Next Steps**: Explore proof assistants (Coq, Agda, Lean, Idris)
