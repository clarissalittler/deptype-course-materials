# Chapter 7: Dependent Types

## Overview

Dependent types represent a fundamental shift in type system design: **types can depend on values**. This allows us to express properties and invariants directly in the type system that were previously only enforceable through runtime checks or external verification.

In previous chapters:
- **System F**: Types abstract over types (`∀A. τ`)
- **System F-omega**: Types abstract over type constructors (`λF::* → *. τ`)
- **Dependent Types**: Types abstract over *terms* (`Π(x:A). B`)

This makes types first-class citizens that can compute and transform based on runtime values.

## Motivation

### The Vector Problem

Consider a function to get the head of a list:

```haskell
-- In Haskell (unsafe!)
head :: [a] -> a
head (x:xs) = x
head []     = error "empty list!"
```

The type doesn't prevent calling `head []`, leading to runtime errors.

With dependent types, we can define length-indexed vectors:

```
Vec : Nat → Type → Type
head : Π(A:Type). Π(n:Nat). Vec (succ n) A → A
```

Now `head` can only be called on non-empty vectors—the type system guarantees it!

### Expressing Invariants

Dependent types let us express:
- **Array bounds**: `lookup : Π(n:Nat). Vec n A → Fin n → A`
- **Sorted lists**: `insert : A → SortedList A → SortedList A`
- **Balanced trees**: `AVLTree : Nat → Type → Type`
- **Protocol states**: `send : Socket Open → Data → Socket Closed`
- **Proofs**: `sorted : List A → Bool` becomes `SortedProof : List A → Type`

## Syntax

### Unified Terms and Types

In dependent type theory, terms and types are unified into a single syntactic category:

```
t ::=                    (terms/types)
    Type                 universe (the type of types)
    x                    variable
    λ(x:A). t            lambda abstraction
    t₁ t₂                application
    Π(x:A). B            dependent function type (Pi type)
    Σ(x:A). B            dependent pair type (Sigma type)
    (t₁, t₂)             pair
    fst t | snd t        projections
    Nat | 0 | succ t     natural numbers
    Bool | true | false  booleans
```

**Key Insight**: There's no separate type syntax—types are terms!

## Pi Types (Dependent Functions)

### Definition

```
Π(x:A). B
```

This is the type of functions that take an argument `x` of type `A` and return a result of type `B`, where **B can mention x**.

### Examples

**Simple Function Type** (non-dependent):
```
Nat → Nat  ≡  Π(x:Nat). Nat
```
Here `B = Nat` doesn't depend on `x`.

**Polymorphic Identity**:
```
id : Π(A:Type). A → A
id = λ(A:Type). λ(x:A). x
```

The return type `A → A` depends on the type argument `A`.

**Vector Constructor**:
```
replicate : Π(A:Type). Π(n:Nat). A → Vec n A
```

The return type `Vec n A` depends on the value `n`.

### Formation, Introduction, Elimination

**Formation** (creating the type):
```
Γ ⊢ A : Type    Γ, x:A ⊢ B : Type
────────────────────────────────── (Π-Form)
Γ ⊢ Π(x:A). B : Type
```

**Introduction** (creating functions):
```
Γ, x:A ⊢ t : B
────────────────────── (Π-Intro)
Γ ⊢ λ(x:A). t : Π(x:A). B
```

**Elimination** (applying functions):
```
Γ ⊢ f : Π(x:A). B    Γ ⊢ a : A
────────────────────────────────── (Π-Elim)
Γ ⊢ f a : [x ↦ a]B
```

Note: The result type `[x ↦ a]B` is `B` with `x` replaced by `a`.

## Sigma Types (Dependent Pairs)

### Definition

```
Σ(x:A). B
```

This is the type of pairs `(a, b)` where:
- `a : A`
- `b : [x ↦ a]B`

The type of the second component **depends on the value** of the first!

### Examples

**Simple Product Type** (non-dependent):
```
Nat × Nat  ≡  Σ(x:Nat). Nat
```

**Dependent Pair**:
```
Σ(n:Nat). Vec n Nat
```

A pair of a length `n` and a vector of that length.

**Existential Type**:
```
∃A. A  ≡  Σ(A:Type). A
```

A pair of a type and a value of that type.

### Formation, Introduction, Elimination

**Formation**:
```
Γ ⊢ A : Type    Γ, x:A ⊢ B : Type
────────────────────────────────── (Σ-Form)
Γ ⊢ Σ(x:A). B : Type
```

**Introduction**:
```
Γ ⊢ a : A    Γ ⊢ b : [x ↦ a]B
──────────────────────────────── (Σ-Intro)
Γ ⊢ (a, b) : Σ(x:A). B
```

**Elimination**:
```
Γ ⊢ p : Σ(x:A). B           Γ ⊢ p : Σ(x:A). B
─────────────────── (Σ-Fst)  ─────────────────── (Σ-Snd)
Γ ⊢ fst p : A                Γ ⊢ snd p : [x ↦ fst p]B
```

## Type Checking

### The Typing Judgment

```
Γ ⊢ t : T
```

Means: "Under context Γ, term t has type T"

### Key Rules

**Universe**:
```
─────────────── (Type-Type)
Γ ⊢ Type : Type
```

⚠️ **Warning**: `Type : Type` is inconsistent (Girard's paradox)! See section on Type-in-Type below.

**Variable**:
```
x:T ∈ Γ
─────────── (Var)
Γ ⊢ x : T
```

**Lambda**:
```
Γ ⊢ A : Type    Γ, x:A ⊢ t : B
──────────────────────────────── (Lam)
Γ ⊢ λ(x:A). t : Π(x:A). B
```

**Application**:
```
Γ ⊢ f : Π(x:A). B    Γ ⊢ a : A
────────────────────────────────── (App)
Γ ⊢ f a : [x ↦ a]B
```

**Conversion**:
```
Γ ⊢ t : A    A ≡ B    Γ ⊢ B : Type
──────────────────────────────────── (Conv)
Γ ⊢ t : B
```

The conversion rule is crucial: if two types are definitionally equal, terms can be converted between them.

### Definitional Equality

Two terms are definitionally equal (`A ≡ B`) if they normalize to the same value:

```
normalize(A) = normalize(B)
```

This includes:
- **α-equivalence**: `λx. x ≡ λy. y` (renaming)
- **β-equivalence**: `(λx. t) s ≡ [x ↦ s]t` (evaluation)
- **η-equivalence**: `λx. f x ≡ f` (extensionality)

## Evaluation

### Call-by-Value Semantics

**Beta Reduction**:
```
(λ(x:A). t) v ⟶ [x ↦ v]t
```

**Pair Projections**:
```
fst (v₁, v₂) ⟶ v₁
snd (v₁, v₂) ⟶ v₂
```

**Normalization**:

All well-typed terms normalize to values (strong normalization property).

### Type-Level Computation

Types can reduce! For example:
```
(λ(A:Type). A → A) Nat
⟶ Nat → Nat
```

This is essential because:
```
λ(x:Nat). x : (λ(A:Type). A → A) Nat
```

Type checking requires normalizing `(λ(A:Type). A → A) Nat` to `Nat → Nat`.

## The Curry-Howard Correspondence

Dependent types establish a deep connection between:
- **Programs** and **Proofs**
- **Types** and **Propositions**

| Logic | Type Theory |
|-------|-------------|
| Proposition P | Type P |
| Proof of P | Term t : P |
| P implies Q | Function type P → Q |
| P and Q | Product type P × Q |
| P or Q | Sum type P + Q |
| For all x, P(x) | Dependent function Π(x:A). P(x) |
| Exists x, P(x) | Dependent pair Σ(x:A). P(x) |
| True | Unit type ⊤ |
| False | Empty type ⊥ |

### Example: Proof as Program

**Proposition**: "For all types A, if we have an A, we can produce an A"

**As a type**:
```
Π(A:Type). A → A
```

**Proof/Program**:
```
λ(A:Type). λ(x:A). x
```

This is the polymorphic identity function—it's both a program AND a proof!

## Type-in-Type Issue

### The Problem

Our implementation uses `Type : Type`, which is logically inconsistent due to **Girard's paradox** (analogous to Russell's paradox in set theory).

With `Type : Type`, we can encode:
```
U = Π(X:Type). (X → Type) → Type
τ = λ(X:U). λ(p:X → Type). Π(x:X). p x → U
```

This leads to a contradiction (a proof of False).

### The Solution: Universe Hierarchy

Proper dependent type systems use a hierarchy:

```
Type₀ : Type₁ : Type₂ : Type₃ : ...
```

Where:
- `Type₀` contains base types: `Nat : Type₀`, `Bool : Type₀`
- `Type₁` contains type constructors: `(Nat → Nat) : Type₁`
- `Typeᵢ : Typeᵢ₊₁` for all i

Agda, Coq, and Idris all implement universe hierarchies.

## Theoretical Properties

### Decidability

**Type Checking**: Decidable ✅
- Given Γ, t, and T, we can check if Γ ⊢ t : T

**Type Inference**: Undecidable ❌
- Given Γ and t, we cannot always infer T such that Γ ⊢ t : T
- We need type annotations on lambdas

### Normalization

**Strong Normalization**: All well-typed terms terminate ✅

**Proof Sketch**:
1. Assign sizes to types
2. Show that reduction decreases size
3. Therefore, reduction must terminate

**Consequence**: We cannot write general recursion! We can only write terminating functions.

To write recursive functions, we need:
- Structural recursion (pattern matching on inductive types)
- Well-founded recursion with a decreasing measure

### Consistency

With proper universe hierarchies, the system is:
- **Consistent**: Cannot prove False
- **Strongly normalizing**: All programs terminate
- **Type safe**: Well-typed programs don't go wrong

## Connection to Real Languages

### Agda

```agda
-- Dependent function
id : (A : Set) → A → A
id A x = x

-- Dependent pair (subset type)
Even : ℕ → Set
even-numbers : Σ ℕ Even
```

### Idris

```idris
-- Length-indexed vectors
data Vect : Nat -> Type -> Type where
  Nil  : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

-- Safe head
head : Vect (S n) a -> a
head (x :: xs) = x  -- No case for Nil needed!
```

### Coq

```coq
(* Dependent product *)
Definition polyId : forall (A : Type), A -> A :=
  fun A x => x.

(* Dependent sum *)
Definition existsNat : {n : nat | n > 0} :=
  exist _ 1 (Nat.lt_0_1).
```

### Lean

```lean
-- Dependent function
def polyId (α : Type) (x : α) : α := x

-- Proof term
theorem nat_implies_nat : Nat → Nat :=
  fun n => n
```

## Implementation

### Project Structure

```
chapter-07-dependent-types/
├── src/
│   ├── Syntax.hs       -- Unified terms/types
│   ├── TypeCheck.hs    -- Bidirectional type checking
│   ├── Eval.hs         -- Normalization
│   ├── Parser.hs       -- Parse dependent types
│   └── Pretty.hs       -- Pretty printer
├── exercises/
│   ├── EXERCISES.md    -- Comprehensive exercises
│   └── Solutions.hs    -- Complete solutions
├── test/
│   └── Spec.hs         -- 39 tests (all passing)
├── package.yaml
└── README.md           -- This file
```

### Building and Testing

```bash
# Build
stack build

# Run tests (39 examples, 0 failures)
stack test

# Load in GHCi
stack ghci
```

### Usage Example

```haskell
import Syntax
import TypeCheck
import Eval
import Parser

-- Parse polymorphic identity
let Right polyId = parseTerm "\\(A:Type). \\(x:A). x"

-- Check its type
typeOf emptyCtx polyId
-- Right (Pi "A" Type (Pi "x" (Var "A") (Var "A")))

-- Apply it to Nat
let term = App polyId Nat

-- Type check
typeOf emptyCtx term
-- Right (Pi "x" Nat Nat)

-- Apply to 0
let term2 = App term Zero

-- Evaluate
eval term2
-- Zero
```

## Key Concepts

1. **Types Depend on Values**: The core innovation
2. **Π Types**: Generalize function types with dependency
3. **Σ Types**: Generalize product types with dependency
4. **Type-Level Computation**: Types reduce just like terms
5. **Curry-Howard**: Types are propositions, terms are proofs
6. **Normalization**: Crucial for type checking
7. **Universe Hierarchy**: Needed for consistency
8. **Strong Normalization**: All programs terminate

## Limitations of This Chapter

This is a **simply typed dependent calculus**—we don't have:

❌ **Inductive Types**: Pattern matching, recursion
❌ **Universe Hierarchy**: Using Type-in-Type
❌ **Equality Types**: Cannot express `a ≡ b`
❌ **Quotient Types**: Cannot mod out by equivalence
❌ **Inductive Families**: Vec, Fin, etc.

These will be covered in **Chapter 8**!

## Exercises

See [EXERCISES.md](exercises/EXERCISES.md) for detailed exercises including:

1. **Basic Dependent Functions** - id, const, compose
2. **Dependent Pairs** - Creation, projections, swap
3. **Type Families** - Conceptual understanding of Vec
4. **Church Encodings** - Polymorphic booleans and numerals
5. **Existential Types** - Encoding via Sigma
6. **Proof-Relevant Programming** - Curry-Howard in action
7. **Dependent Type Utilities** - apply, flip, curry/uncurry

Complete solutions in [exercises/Solutions.hs](exercises/Solutions.hs).

## References

### Foundational Papers

1. **Martin-Löf, Per** (1984). *Intuitionistic Type Theory*
   - Foundational work on dependent types
   - Notes by Giovanni Sambin

2. **de Bruijn, N.G.** (1970). "The Mathematical Language AUTOMATH"
   - First implementation of dependent types
   - Automated Mathematics

3. **Coquand, Thierry; Huet, Gérard** (1988). "The Calculus of Constructions"
   - Combines dependent types with System F
   - Foundation of Coq

4. **Luo, Zhaohui** (1994). *Computation and Reasoning: A Type Theory for Computer Science*
   - Modern treatment of dependent type theory

### Practical Systems

5. **Norell, Ulf** (2007). "Towards a practical programming language based on dependent type theory"
   - PhD thesis on Agda
   - University of Gothenburg

6. **Brady, Edwin** (2013). "Idris, a general-purpose dependently typed programming language"
   - JFP 23(5)
   - Practical dependent types

7. **The Coq Development Team** (2021). *The Coq Proof Assistant Reference Manual*
   - Version 8.13
   - https://coq.inria.fr

8. **de Moura, Leonardo; et al.** (2015). "The Lean Theorem Prover"
   - CADE-25
   - Modern proof assistant

### Tutorials and Books

9. **Nordström, Bengt; Petersson, Kent; Smith, Jan M.** (1990). *Programming in Martin-Löf's Type Theory*
   - Excellent introduction with examples

10. **Bertot, Yves; Castéran, Pierre** (2004). *Interactive Theorem Proving and Program Development: Coq'Art*
    - Practical introduction to Coq

11. **Stump, Aaron** (2016). *Verified Functional Programming in Agda*
    - ACM Books
    - Learn Agda through examples

12. **Wadler, Philip** (2015). "Propositions as Types"
    - Communications of the ACM 58(12)
    - Beautiful explanation of Curry-Howard

## Next Chapter

In [Chapter 8](../chapter-08-full-dependent-types), we extend to **full dependent types** with:

- **Inductive Families**: Vec, Fin, List
- **Pattern Matching**: Structural recursion
- **Equality Types**: Propositional equality
- **Universe Hierarchy**: Fix Type-in-Type
- **Real Theorem Proving**: Verified programs!

This is where dependent types truly shine—we'll prove properties about programs and write programs that carry their own correctness proofs!

---

**Implementation Note**: This chapter uses Type-in-Type for pedagogical simplicity. Production systems use universe hierarchies to maintain consistency.
