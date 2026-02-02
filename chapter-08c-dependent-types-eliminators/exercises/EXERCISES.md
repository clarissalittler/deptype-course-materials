# Chapter 8: Full Dependent Types - Exercises

These exercises explore the full power of dependent types including inductive families, equality types, and theorem proving.

## Exercise 1: Universe Hierarchy

Work with the universe hierarchy to fix the Type-in-Type inconsistency.

### 1a. Universe Levels

**Question**: What is the type of `Type 0`?
**Answer**: `Type 1`

**Question**: What is the type of `Nat → Nat`?
**Answer**: `Type 0` (since both `Nat : Type 0`)

**Question**: What is the type of `Type 0 → Type 0`?
**Answer**: `Type 1` (function between types)

### 1b. Universe Polymorphism

Implement a universe-polymorphic identity function:
```
id : Π(i:Level). Π(A:Type i). A → A
```

In our simplified system (without level polymorphism), implement:
```
id0 : Π(A:Type 0). A → A
id1 : Π(A:Type 1). A → A
```

**Learning Objective**: Understand how universe levels prevent inconsistency.

## Exercise 2: Equality Types and Proofs

Use propositional equality to prove properties.

### 2a. Symmetry of Equality

Prove that equality is symmetric using the J eliminator:
```
sym : Π(A:Type). Π(x:A). Π(y:A). Eq A x y → Eq A y x
```

**Hint**: Use J with the motive `C z eq = Eq A z x`

### 2b. Transitivity of Equality

Prove that equality is transitive:
```
trans : Π(A:Type). Π(x y z:A). Eq A x y → Eq A y z → Eq A x z
```

### 2c. Congruence

Prove that functions respect equality:
```
cong : Π(A B:Type). Π(f:A → B). Π(x y:A). Eq A x y → Eq B (f x) (f y)
```

**Learning Objective**: Understand proof-relevant programming with equality.

## Exercise 3: Natural Number Proofs

Prove properties about natural numbers.

### 3a. Addition is Commutative (Statement)

State (but don't prove) that addition is commutative:
```
add_comm : Π(m n:Nat). Eq Nat (add m n) (add n m)
```

First implement addition using natElim.

### 3b. Zero is Right Identity

Prove `∀n. n + 0 = n`:
```
add_zero_right : Π(n:Nat). Eq Nat (add n zero) n
```

Use natElim to induct on `n`.

### 3c. Successor Distributes

Prove `∀m n. succ (m + n) = m + succ n`:
```
add_succ_right : Π(m n:Nat). Eq Nat (succ (add m n)) (add m (succ n))
```

**Learning Objective**: Write inductive proofs using eliminators.

## Exercise 4: Vector Type (Length-Indexed Lists)

Define and work with length-indexed vectors.

### 4a. Vector Definition (Conceptual)

Vectors would be defined as an inductive family:
```
data Vec : Nat → Type → Type where
  Nil  : Π(A:Type). Vec zero A
  Cons : Π(A:Type). Π(n:Nat). A → Vec n A → Vec (succ n) A
```

In our system, represent vectors using constructors:
```
Nil  : Π(A:Type). Vec zero A
Cons : Π(A:Type). Π(n:Nat). A → Vec n A → Vec (succ n) A
```

### 4b. Safe Head

Implement a head function that can only be called on non-empty vectors:
```
head : Π(A:Type). Π(n:Nat). Vec (succ n) A → A
```

This is type-safe—you cannot call `head` on an empty vector!

### 4c. Vector Append

Implement vector concatenation with dependent types:
```
append : Π(A:Type). Π(m n:Nat). Vec m A → Vec n A → Vec (add m n) A
```

The result length is the sum of input lengths, enforced by the type!

**Learning Objective**: Understand how dependent types encode invariants.

## Exercise 5: Fin Type (Bounded Natural Numbers)

Define Fin n, the type of natural numbers less than n.

### 5a. Fin Definition (Conceptual)

```
data Fin : Nat → Type where
  FZ : Π(n:Nat). Fin (succ n)        -- Zero is less than any successor
  FS : Π(n:Nat). Fin n → Fin (succ n)  -- If i < n then i+1 < n+1
```

**Examples**:
- `Fin 0` is empty (no numbers less than 0)
- `Fin 1 = {FZ 0}` (only 0 < 1)
- `Fin 2 = {FZ 1, FS (FZ 0)}` (0 and 1 are < 2)
- `Fin 3 = {FZ 2, FS (FZ 1), FS (FS (FZ 0))}` (0, 1, 2 are < 3)

### 5b. Safe Lookup

Implement safe array indexing:
```
lookup : Π(A:Type). Π(n:Nat). Vec n A → Fin n → A
```

This can never index out of bounds!

**Learning Objective**: Use indexed types to prevent runtime errors.

## Exercise 6: Empty and Unit Types

Explore the propositions-as-types interpretation.

### 6a. Ex Falso Quodlibet

Implement the principle "from falsehood, anything follows":
```
exFalso : Π(A:Type). Empty → A
```

This is just `emptyElim`!

### 6b. Unit is Inhabited

Prove that Unit has an inhabitant:
```
unitProof : Unit
unitProof = TT
```

### 6c. Negation

Define negation as a function to Empty:
```
Not : Type → Type
Not A = A → Empty
```

Prove double negation introduction:
```
doubleNegIntro : Π(A:Type). A → Not (Not A)
```

**Learning Objective**: Understand the Curry-Howard correspondence.

## Exercise 7: Leibniz Equality

Explore an alternative definition of equality.

### 7a. Leibniz Equality

Define equality using indiscernibility of identicals:
```
LEq : Π(A:Type). A → A → Type
LEq A x y = Π(P:A → Type). P x → P y
```

Two things are equal if they satisfy the same predicates.

### 7b. Reflexivity

Prove Leibniz equality is reflexive:
```
lrefl : Π(A:Type). Π(x:A). LEq A x x
```

### 7c. Symmetry and Transitivity

Prove Leibniz equality is symmetric and transitive.

**Learning Objective**: Understand different formulations of equality.

## Exercise 8: Decidable Equality

Implement decidable equality for specific types.

### 8a. Bool Equality

Implement a function that decides if two bools are equal:
```
bool_eq : Π(b1 b2:Bool). Either (Eq Bool b1 b2) (Not (Eq Bool b1 b2))
```

Where `Either A B = Σ(b:Bool). if b then A else B` (sum type).

### 8b. Nat Equality (Conceptual)

Describe how you would implement decidable equality for Nat:
```
nat_eq : Π(m n:Nat). Either (Eq Nat m n) (Not (Eq Nat m n))
```

**Learning Objective**: Understand decidable vs. undecidable equality.

## Theoretical Exercises

### T1. Type-in-Type vs Universe Hierarchy

**Question**: Why is `Type : Type` inconsistent?

**Answer**: It allows encoding of paradoxes like Girard's paradox (similar to Russell's paradox). With `Type : Type`, we can construct a term of type `Empty`, proving False.

**Question**: How does the universe hierarchy fix this?

**Answer**: With `Type i : Type (i+1)`, there's no way to construct a self-referential type that leads to paradox.

### T2. Intensional vs Extensional Equality

**Question**: What's the difference between intensional and extensional equality?

**Answer**:
- **Intensional**: `Eq A x y` holds only when `x` and `y` are definitionally equal (same up to normalization)
- **Extensional**: `x = y` if they behave the same in all contexts (includes function extensionality)

Our system uses intensional equality.

### T3. The K Rule

**Question**: What is axiom K for equality types?

**Answer**:
```
K : Π(A:Type). Π(x:A). Π(P:Eq A x x → Type).
    P (refl x) → Π(eq:Eq A x x). P eq
```

K says all proofs of `x = x` are equal to `refl x`. This is controversial and not assumed in all systems (e.g., Homotopy Type Theory rejects K).

## Implementation Challenges

### C1. Inductive Families

**Challenge**: Extend the implementation to support full inductive type definitions with:
- Multiple constructors
- Indexed families (Vec, Fin)
- Automatic generation of eliminators

### C2. Pattern Matching Compilation

**Challenge**: Implement pattern matching compilation to eliminators:
- Convert pattern matches to uses of eliminators
- Handle nested patterns
- Ensure coverage checking

### C3. Proof Search

**Challenge**: Implement automatic proof search for simple propositions:
- Reflexivity of equality
- Simple arithmetic facts
- Structural inductions

## References

1. **Martin-Löf, Per** (1984). *Intuitionistic Type Theory*
   - Foundation of dependent type theory with universes

2. **Coquand, Thierry** (1992). "Pattern Matching with Dependent Types"
   - How to compile pattern matching

3. **Norell, Ulf** (2007). "Towards a practical programming language based on dependent type theory"
   - Agda thesis, practical dependent types

4. **The Univalent Foundations Program** (2013). *Homotopy Type Theory*
   - Modern perspective on equality and universes
   - https://homotopytypetheory.org/book/

5. **Sozeau, Matthieu; Mangin, Cyprien** (2019). "Equations Reloaded"
   - Advanced pattern matching in Coq

6. **Brady, Edwin** (2013). "Idris, a general-purpose dependently typed programming language"
   - Practical dependent type programming

7. **Altenkirch, Thorsten; McBride, Conor; Swierstra, Wouter** (2007). "Observational equality, now!"
   - Alternative approaches to equality

## Next Steps

After mastering these exercises, you understand:
- Universe hierarchies and consistency
- Equality types and proofs
- Inductive families (Vec, Fin)
- Eliminators and structural recursion
- Curry-Howard at the deepest level
- Real theorem proving in type theory

This completes the journey from untyped lambda calculus to full dependent types! You now have the foundation to:
- Use Agda, Idris, Coq, or Lean
- Write verified programs
- Prove mathematical theorems
- Understand cutting-edge type theory research

**Congratulations on completing the course!**
