# Chapter 8: Real-World Connections

## Proof Assistants in Practice

### Coq: Verified Software

```coq
(* CompCert: Verified C Compiler *)
(* Proves compilation preserves semantics *)

Theorem compile_correct:
  forall p tp,
    compile p = Some tp ->
    forall beh, program_behaves (semantics p) beh ->
           program_behaves (Asm.semantics tp) beh.

(* This guarantees: if source has behavior X,
   compiled code has behavior X *)
```

### Lean: Mathematical Proofs

```lean
-- mathlib: Library of formalized mathematics
-- Thousands of theorems proven!

theorem prime_factors_unique (n : ℕ) (h : n ≥ 2) :
  ∃! l : List ℕ, (∀ p ∈ l, Prime p) ∧ l.prod = n :=
  sorry  -- Proof here

-- Used to verify mathematical conjectures!
```

### Agda: Programming with Proofs

```agda
-- Correct-by-construction sorting
sort : List ℕ → Sorted
sort xs = merge-sort xs

-- Sorted is a dependent type containing:
-- 1. The sorted list
-- 2. A proof that it's sorted
-- 3. A proof it's a permutation of input
```

---

## Universe Hierarchy in Practice

### Agda's Universes

```agda
-- Level hierarchy
Set₀ : Set₁
Set₁ : Set₂
Set₂ : Set₃
-- ...

-- Universe polymorphism
id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

-- Works at any universe level!
```

### Coq's Universes

```coq
(* Prop: logical propositions *)
(* Set: computational types *)
(* Type: predicative hierarchy *)

Check nat.        (* nat : Set *)
Check Set.        (* Set : Type *)
Check Type.       (* Type : Type *)  (* Simplified view *)

(* Actually: Type@{i} : Type@{i+1} *)
```

### Lean's Universe Management

```lean
-- Explicit universe levels
universe u v

def id {α : Type u} (x : α) : α := x

-- Lean handles most universe issues automatically
-- but allows manual control when needed
```

---

## Propositional Equality in Practice

### Agda's Equality

```agda
-- Built-in equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Proving properties
sym : ∀ {A} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl
```

### Coq's eq Type

```coq
(* Built-in equality *)
Inductive eq (A : Type) (x : A) : A -> Prop :=
  | eq_refl : eq A x x.

(* Tactics for equality *)
Theorem plus_comm : forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.
```

### Idris Equality

```idris
-- Equality type
data (=) : a -> b -> Type where
  Refl : x = x

-- Using equality proofs
plusCommutative : (n : Nat) -> (m : Nat) -> n + m = m + n
```

---

## Inductive Families in Action

### Verified Data Structures

```agda
-- Red-black trees with invariants in types
data Color : Set where
  Red Black : Color

data RBTree : Color → ℕ → Set → Set where
  Leaf : RBTree Black 0 A
  RedNode : RBTree Black n A → A → RBTree Black n A
          → RBTree Red n A
  BlackNode : RBTree c₁ n A → A → RBTree c₂ n A
            → RBTree Black (suc n) A

-- Invariants enforced by types:
-- 1. Red nodes have black children
-- 2. All paths have same black height
```

### Format Strings (Idris)

```idris
-- Printf with type safety!
data Format = Lit String | D | S | F

printf : (fmt : List Format) -> interpFormat fmt
printf [] = ""
printf (Lit s :: rest) = s ++ printf rest
printf (D :: rest) = \n => show n ++ printf rest
printf (S :: rest) = \s => s ++ printf rest

-- printf [S, Lit " is ", D] : String -> Int -> String
printf [S, Lit " is ", D] "Answer" 42
-- "Answer is 42"
```

### Finite Sets

```agda
-- Fin n has exactly n elements
data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc  : Fin n → Fin (suc n)

-- Safe indexing into vectors
lookup : Vec A n → Fin n → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

-- Impossible to go out of bounds!
```

---

## Real-World Verified Systems

### CompCert (C Compiler)

- **What**: Formally verified optimizing C compiler
- **Proof**: Compilation preserves program semantics
- **Impact**: Used in aerospace and nuclear industries

```
Source C → [Verified Compilation] → Assembly
              ↓
         Mathematical proof that
         behavior is preserved
```

### seL4 (Operating System Kernel)

- **What**: Formally verified microkernel
- **Proofs**: Memory safety, access control, information flow
- **Impact**: Used in military and aerospace systems

### CertiKOS (Operating System)

- **What**: Certified OS kernel
- **Proofs**: Concurrent programs are race-free
- **Layers**: Compositional verification

### HACL* (Cryptography)

- **What**: Verified cryptographic library
- **Proofs**: Functional correctness, side-channel resistance
- **Used by**: Firefox, Linux kernel

---

## The J Eliminator in Practice

### Equality Reasoning in Agda

```agda
-- Using J (called subst in stdlib)
subst : ∀ {A : Set} {x y : A} (P : A → Set)
      → x ≡ y → P x → P y
subst P refl px = px

-- Example: transport across equality
coerce : A ≡ B → A → B
coerce eq a = subst (λ X → X) eq a
```

### Heterogeneous Equality

```agda
-- When types might differ
data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≅ x

-- Useful for dependent pattern matching
```

---

## Practical Considerations

### When Full Dependent Types Help

1. **Compiler verification**: Prove transformations correct
2. **Cryptographic protocols**: Prove security properties
3. **Smart contracts**: Financial correctness
4. **File formats**: Parse exactly as specified
5. **Network protocols**: State machine compliance

### Challenges

1. **Learning curve**: Steep initial investment
2. **Proof burden**: Must prove everything
3. **Tooling**: Less mature than mainstream
4. **Performance**: Proof erasure needed
5. **Ecosystem**: Smaller libraries

---

## Mainstream Language Features Inspired by DT

### TypeScript Conditional Types

```typescript
// Type-level computation (limited)
type NonNullable<T> = T extends null | undefined ? never : T;

type IsArray<T> = T extends any[] ? true : false;
```

### Rust Const Generics

```rust
// Value in type (limited)
fn create_array<T: Default, const N: usize>() -> [T; N] {
    [(); N].map(|_| T::default())
}
```

### Haskell Singletons

```haskell
-- Simulating dependent types
data SNat :: Nat -> Type where
  SZero :: SNat 'Zero
  SSucc :: SNat n -> SNat ('Succ n)

-- Runtime witness of type-level value
```

---

## Key Takeaways for Practitioners

1. **Universe hierarchy prevents paradox**: Essential for consistency

2. **Equality is a type**: Proofs of equality are first-class

3. **J eliminator is powerful**: Enables equality reasoning

4. **Inductive families express invariants**: Vec, Fin, etc.

5. **Verified software exists**: CompCert, seL4, HACL*

---

## Tools for Verified Programming

### Proof Assistants
- **Coq**: Most mature, large library (mathcomp)
- **Agda**: Clean syntax, cubical type theory
- **Lean**: Modern, mathlib library
- **Idris**: Practical programming focus

### Verification Tools
- **Dafny**: Microsoft, auto-active verification
- **F***: Effectful, security proofs
- **Liquid Haskell**: Refinement types
- **Why3**: Multi-backend prover

### Industrial Use
- **Galois**: Security-focused verification
- **INRIA**: CompCert, Coq development
- **Microsoft Research**: F*, Dafny, Lean
- **Data61/CSIRO**: seL4 kernel

---

## Your Journey Continues

You've completed the course! Next steps:

1. **Try Idris**: Most accessible for programmers
2. **Try Lean**: Great tooling, growing community
3. **Software Foundations**: Coq tutorial (free online)
4. **Programming Language Foundations in Agda**: Also free

**The future of software is verified software.**
