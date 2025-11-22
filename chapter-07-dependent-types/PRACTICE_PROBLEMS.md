# Chapter 7: Dependent Types - Practice Problems

## Purpose
Practice Pi types, Sigma types, and basic dependent programming.

---

## Warm-Up Problems (15 minutes)

### Problem 1.1: Pi Types ⭐
Write types for these dependent functions:

a) Identity on types: `id : (A : Type) → A → A`
b) Const at type level: `const : (A : Type) → (B : Type) → A → B → A`
c) List length: `length : (A : Type) → List A → Nat`

### Problem 1.2: Sigma Types ⭐
Write dependent pairs:

a) `∃n : Nat. Vec n` - "A vector of some length"
b) `∃A : Type. A` - "A value of some type"
c) `∃f : Nat → Nat. (∀n : Nat. f n ≥ n)` - "An increasing function with proof"

### Problem 1.3: Type Families ⭐
Define these indexed types:

a) `Vec : Nat → Type → Type` - Vectors indexed by length
b) `Fin : Nat → Type` - Finite sets (numbers less than n)
c) `Eq : (A : Type) → A → A → Type` - Equality type

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Dependent Functions ⭐⭐
Implement using Pi types:

a) `replicate : (n : Nat) → (A : Type) → A → Vec A n`
   - Create vector of n copies

b) `take : (n : Nat) → (A : Type) → (m : Nat) → Vec A (n + m) → Vec A n`
   - Take first n elements

c) `append : (A : Type) → (m n : Nat) → Vec A m → Vec A n → Vec A (m + n)`
   - Concatenate vectors (length-indexed!)

### Problem 2.2: Dependent Pairs ⭐⭐
Implement using Sigma types:

a) `filter : (A : Type) → (A → Bool) → List A → ∃n : Nat. Vec A n`
   - Filter returns vector of unknown length

b) `partition : (A : Type) → (A → Bool) → (n : Nat) → Vec A n →
     ∃(p q : Nat). (Vec A p × Vec A q × p + q = n)`
   - Split vector, prove lengths sum correctly

c) `lookup : (A : Type) → (n : Nat) → Vec A n → Fin n → A`
   - Safe indexing using bounded indices

### Problem 2.3: Equality Proofs ⭐⭐
Work with equality type:

a) `refl : (A : Type) → (x : A) → Eq A x x`
   - Reflexivity

b) `sym : (A : Type) → (x y : A) → Eq A x y → Eq A y x`
   - Symmetry

c) `trans : (A : Type) → (x y z : A) → Eq A x y → Eq A y z → Eq A x z`
   - Transitivity

d) `cong : (A B : Type) → (f : A → B) → (x y : A) → Eq A x y → Eq B (f x) (f y)`
   - Congruence

### Problem 2.4: Finite Sets ⭐⭐
Implement `Fin n` (numbers 0..n-1):

a) Define constructors:
   ```
   fzero : (n : Nat) → Fin (S n)
   fsucc : (n : Nat) → Fin n → Fin (S n)
   ```

b) `fin_to_nat : (n : Nat) → Fin n → Nat`

c) `nat_to_fin : (n : Nat) → Nat → Maybe (Fin n)`
   - Convert if in bounds

d) `weaken : (n : Nat) → Fin n → Fin (S n)`
   - Weaken bound

### Problem 2.5: Vector Operations ⭐⭐
Length-preserving operations:

a) `map : (A B : Type) → (n : Nat) → (A → B) → Vec A n → Vec B n`

b) `zipWith : (A B C : Type) → (n : Nat) →
     (A → B → C) → Vec A n → Vec B n → Vec C n`

c) `reverse : (A : Type) → (n : Nat) → Vec A n → Vec A n`

d) `transpose : (A : Type) → (m n : Nat) →
     Vec (Vec A n) m → Vec (Vec A m) n`

### Problem 2.6: Leibniz Equality ⭐⭐
Alternative equality definition:

```
Leibniz A x y = (P : A → Type) → P x → P y
```

a) Prove: `Leibniz A x y → Eq A x y`
b) Prove: `Eq A x y → Leibniz A x y`
c) Show they're equivalent (isomorphic)

### Problem 2.7: Decidable Equality ⭐⭐
Decidable equality type:

```
Dec : Type → Type
Dec A = A + (A → ⊥)
```

a) `nat_eq_dec : (n m : Nat) → Dec (Eq Nat n m)`

b) `bool_eq_dec : (b1 b2 : Bool) → Dec (Eq Bool b1 b2)`

c) `list_eq_dec : (A : Type) → ((x y : A) → Dec (Eq A x y)) →
     (xs ys : List A) → Dec (Eq (List A) xs ys)`

### Problem 2.8: Heterogeneous Equality ⭐⭐
When types can differ:

```
HEq : (A B : Type) → A → B → Type
```

a) `heq_refl : (A : Type) → (x : A) → HEq A A x x`

b) `heq_to_eq : (A : Type) → (x y : A) → HEq A A x y → Eq A x y`

c) `subst_type : (x y : Type) → HEq Type Type x y →
     (P : Type → Type) → P x → P y`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Well-Typed Interpreter ⭐⭐⭐
Define expression language with dependent types:

```
data Ty : Type where
  TNat : Ty
  TBool : Ty
  TArrow : Ty → Ty → Ty

Expr : Ty → Type
```

a) Define constructors that guarantee well-typedness:
   ```
   Lit : Nat → Expr TNat
   Bool : Bool → Expr TBool
   If : (t : Ty) → Expr TBool → Expr t → Expr t → Expr t
   Lam : (s t : Ty) → (Expr s → Expr t) → Expr (TArrow s t)
   App : (s t : Ty) → Expr (TArrow s t) → Expr s → Expr t
   ```

b) Define denotation function:
   ```
   denote : (t : Ty) → Type
   denote TNat = Nat
   denote TBool = Bool
   denote (TArrow s t) = denote s → denote t
   ```

c) Type-safe evaluator:
   ```
   eval : (t : Ty) → Expr t → denote t
   ```

### Problem 3.2: Red-Black Tree Invariants ⭐⭐⭐
Encode red-black tree properties:

```
data Color : Type where
  Red : Color
  Black : Color

-- Trees indexed by color and black-height
RBTree : Color → Nat → Type → Type
```

a) Define constructors that enforce:
   - Red nodes have black children
   - All paths have same black height

b) Implement insertion preserving invariants

c) Balance operation with type-level proof

### Problem 3.3: Curry-Howard for Dependent Types ⭐⭐⭐
Programs as proofs:

a) `∧_comm : (A B : Type) → (A × B) → (B × A)`
   - Conjunction commutes

b) `∨_comm : (A B : Type) → (A + B) → (B + A)`
   - Disjunction commutes

c) `∃_∀_dist : (A : Type) → (P Q : A → Type) →
     (∃x : A. P x × Q x) → (∃x : A. P x) × (∃x : A. Q x)`
   - Existential distributes over conjunction

d) **Cannot prove**:
   ```
   ∀_∃_dist : (A : Type) → (P Q : A → Type) →
     ((∀x : A. P x) + (∀x : A. Q x)) → (∀x : A. P x + Q x)
   ```
   Explain why!

### Problem 3.4: Type-Level Computation ⭐⭐⭐
Compute at type level:

a) **Matrix dimensions**:
   ```
   Matrix : Nat → Nat → Type → Type

   mult : (A : Type) → (m n p : Nat) →
     Matrix m n A → Matrix n p A → Matrix m p A
   ```
   Type ensures dimension compatibility!

b) **Type-safe printf**:
   ```
   format : String → Type
   format "" = String
   format "%d" ++ s = Nat → format s
   format "%s" ++ s = String → format s
   format c ++ s = format s

   printf : (fmt : String) → format fmt
   ```

c) Show how dependent types prevent format string bugs

---

## Debugging Exercises (30 minutes)

### Debug 1: Type Dependency ⭐⭐
Student wrote:
```
append : Vec A m → Vec A n → Vec A (m + n)
-- Error: m and n not in scope!
```

Fix:
```
append : (A : Type) → (m n : Nat) → Vec A m → Vec A n → Vec A (m + n)
```

All dependencies must be explicit parameters!

### Debug 2: Dependent Pattern Matching ⭐⭐
What's wrong?
```
head : (A : Type) → (n : Nat) → Vec A n → A
head A n xs = case xs of
  nil => ???    -- Problem: n might be 0!
  cons x xs' => x
```

Fix: Refine type or handle empty case:
```
head : (A : Type) → (n : Nat) → Vec A (S n) → A
head A n (cons x xs') = x
```

### Debug 3: Equality Confusion ⭐⭐
Student confused:
```
x : Nat
y : Nat
p : x = y

Can I use p to replace x with y in expressions?
```

**A**: YES! That's exactly what equality proofs do:
```
subst : (P : Nat → Type) → x = y → P x → P y
```

### Debug 4: Universe Issues ⭐⭐
What's wrong?
```
Type : Type    -- Inconsistent!
```

Need universe hierarchy:
```
Type₀ : Type₁ : Type₂ : ...
```

We'll address this in Chapter 8!

### Debug 5: Sigma Projection ⭐⭐
Student wrote:
```
p : ∃n : Nat. Vec A n
fst p : Nat           -- OK
snd p : Vec A ???     -- What index?
```

Should be:
```
snd p : Vec A (fst p)
```

Second component's type depends on first!

---

## Code Review Exercises (30 minutes)

### Review 1: Safe Head ⭐⭐
Two approaches:

**Version A** (refine type):
```
head : (A : Type) → (n : Nat) → Vec A (S n) → A
```

**Version B** (return Maybe):
```
head : (A : Type) → (n : Nat) → Vec A n → Maybe A
```

Which is better? When to use each?

### Review 2: Dependent vs Non-Dependent ⭐⭐
Compare:

**Non-dependent**:
```
map : (A → B) → List A → List B
```

**Dependent**:
```
map : (A B : Type) → (n : Nat) → (A → B) → Vec A n → Vec B n
```

Tradeoffs:
- Type safety
- Implementation complexity
- Proof burden

### Review 3: Equality Types ⭐⭐⭐
Three equality definitions:

**Definitional**:
```
x = y    (convertible by computation)
```

**Propositional**:
```
data Eq A x y where
  refl : Eq A x x
```

**Leibniz**:
```
Leibniz A x y = (P : A → Type) → P x → P y
```

When to use each?

---

## Solutions

### Warm-Up

**1.1**:
```
a) id : (A : Type) → A → A
   id = λA. λx. x

b) const : (A : Type) → (B : Type) → A → B → A
   const = λA. λB. λx. λy. x

c) length : (A : Type) → List A → Nat
   length = λA. λxs. foldr (λ_. λn. S n) 0 xs
```

**1.2**:
```
a) (n, vec) : (n : Nat × Vec A n)
b) (A, x) : (A : Type × A)
c) (f, proof) : (f : (Nat → Nat) × (∀n. f n ≥ n))
```

**1.3**:
```
a) Vec : Nat → Type → Type
   Vec 0 A = Unit
   Vec (S n) A = A × Vec n A

b) Fin : Nat → Type
   Fin 0 = ⊥
   Fin (S n) = Unit + Fin n

c) Eq : (A : Type) → A → A → Type
   (inductively defined)
```

### Standard

**2.1**:
```
a) replicate : (n : Nat) → (A : Type) → A → Vec A n
   replicate 0 A x = unit
   replicate (S n) A x = (x, replicate n A x)

b) take : (n : Nat) → (A : Type) → (m : Nat) →
     Vec A (n + m) → Vec A n
   take 0 A m v = unit
   take (S n) A m (x, xs) = (x, take n A m xs)

c) append : (A : Type) → (m n : Nat) →
     Vec A m → Vec A n → Vec A (m + n)
   append A 0 n unit ys = ys
   append A (S m) n (x, xs) ys = (x, append A m n xs ys)
```

**2.2**:
```
a) filter : (A : Type) → (A → Bool) → List A →
     ∃n : Nat. Vec A n
   filter A p [] = (0, unit)
   filter A p (x :: xs) =
     let (n, vec) = filter A p xs in
     if p x then (S n, (x, vec)) else (n, vec)
```

**2.3**:
```
a) refl : (A : Type) → (x : A) → Eq A x x
   refl A x = Refl

b) sym : (A : Type) → (x y : A) → Eq A x y → Eq A y x
   sym A x .x Refl = Refl

c) trans : (A : Type) → (x y z : A) →
     Eq A x y → Eq A y z → Eq A x z
   trans A x .x .x Refl Refl = Refl
```

**2.4**:
```
Fin : Nat → Type
data Fin where
  FZero : (n : Nat) → Fin (S n)
  FSucc : (n : Nat) → Fin n → Fin (S n)

fin_to_nat : (n : Nat) → Fin n → Nat
fin_to_nat (S n) (FZero n) = 0
fin_to_nat (S n) (FSucc n i) = S (fin_to_nat n i)
```

**2.5**:
```
map : (A B : Type) → (n : Nat) →
  (A → B) → Vec A n → Vec B n
map A B 0 f unit = unit
map A B (S n) f (x, xs) = (f x, map A B n f xs)
```

### Challenge

**3.1**: Well-typed interpreter ensures no runtime type errors

**3.2**: Red-black trees encoded so invariant violations are type errors

**3.3**:
```
d) Cannot prove ∀_∃_dist because choosing left vs right disjunct
   may depend on specific x (not uniform choice)
```

**3.4**: Dependent types make printf type-safe!

### Debug

**Debug 1**: Dependent types need explicit quantification

**Debug 2**: Pattern matching refines index

**Debug 3**: Equality proofs enable substitution

**Debug 4**: Need universe hierarchy (Chapter 8)

**Debug 5**: Sigma projections: second type depends on first value

### Review

**Review 1**: A prevents errors at compile-time; B is more flexible

**Review 2**: Dependent version statically prevents length mismatches

**Review 3**: Definitional for computation, propositional for proofs, Leibniz for theory

---

**Time**: 5-7 hours
**Focus**: Understanding dependency between types and values is crucial
