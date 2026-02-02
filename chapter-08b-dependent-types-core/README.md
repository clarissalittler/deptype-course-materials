# Chapter 08b: Dependent Types (Bidirectional Core)

This stage focuses on a **sound bidirectional core**: Pi/Sigma/Lam/App with definitional equality. Eliminators, pattern matching, and inductive constructors are intentionally deferred to later stages.

## Table of Contents

1. [Overview](#overview)
2. [Motivation](#motivation)
3. [Universe Hierarchy](#universe-hierarchy)
4. [Equality Types](#equality-types)
5. [Inductive Types and Families](#inductive-types-and-families)
6. [Pattern Matching](#pattern-matching)
7. [Eliminators](#eliminators)
8. [Curry-Howard Correspondence](#curry-howard-correspondence)
9. [Formal Semantics](#formal-semantics)
10. [Examples](#examples)
11. [Comparison with Chapter 7](#comparison-with-chapter-7)
12. [References](#references)

## Overview

Full dependent type theory extends the simply typed dependent calculus (Chapter 7) with:

1. **Universe Hierarchy**: `Type 0 : Type 1 : Type 2 : ...` to avoid inconsistency
2. **Equality Types**: Propositional equality `Eq A x y` with the J eliminator
3. **Inductive Families**: Types indexed by values (like `Vec n A`, `Fin n`)
4. **Pattern Matching**: Structural decomposition of data
5. **Eliminators**: Principled recursion for built-in types (Nat, Bool, Unit, Empty)

This system forms the foundation of modern proof assistants like:
- **Agda**: Dependently typed programming language
- **Coq**: Proof assistant based on the Calculus of Inductive Constructions
- **Lean**: Theorem prover with a powerful type theory
- **Idris**: Practical dependently typed programming language

### Key Features

```haskell
-- Universe hierarchy prevents Type-in-Type paradox
Type 0 : Type 1
Type 1 : Type 2
...

-- Propositional equality
Eq : Π(A:Type 0). A → A → Type 0
refl : Π(A:Type 0). Π(x:A). Eq A x x

-- J eliminator: equality induction
J : Π(A:Type 0).
    Π(C:(z:A) → Eq A x z → Type 0).
    C x (refl x) →
    Π(y:A). Π(eq:Eq A x y). C y eq

-- Inductive families (conceptual)
data Vec : Nat → Type 0 → Type 0 where
  Nil  : Π(A:Type 0). Vec 0 A
  Cons : Π(A:Type 0). Π(n:Nat). A → Vec n A → Vec (succ n) A

-- Pattern matching
match v with
  | Nil _ -> ...
  | Cons _ x xs -> ...
```

## Motivation

### The Type-in-Type Problem (from Chapter 7)

In Chapter 7, we had `Type : Type`, which leads to **Girard's paradox**—a type-level version of Russell's paradox. We can encode the set of all sets that don't contain themselves, leading to a contradiction.

```haskell
-- With Type : Type, we can derive False!
-- This makes the logic inconsistent
```

### The Solution: Universe Hierarchy

Instead of one universe, we have an infinite hierarchy:

```
Type 0 : Type 1 : Type 2 : Type 3 : ...
```

Each universe contains the previous one:
- **Type 0**: Contains "small" types like `Nat`, `Bool`, `String`
- **Type 1**: Contains type operators and `Type 0` itself
- **Type i**: Contains `Type (i-1)` and types quantifying over it

This stratification prevents the self-referential paradox.

### Why Equality Types?

In simply typed lambda calculus, we can only express **definitional equality**—when two terms reduce to the same normal form. But we often want to express **propositional equality**—stating as a type that two terms are equal, which can be proven and manipulated.

```haskell
-- Definitional equality (meta-level)
1 + 1 ≡ 2    -- These reduce to the same thing

-- Propositional equality (object-level type)
Eq Nat (1 + 1) 2    -- A type we can prove
refl 2 : Eq Nat 2 2 -- A proof term
```

Propositional equality allows us to:
- **State theorems**: `∀n. n + 0 = n`
- **Prove properties**: Symmetry, transitivity, congruence
- **Reason about programs**: Correctness proofs

### Why Inductive Families?

Simple inductive types (like `List A`) are uniform—all values have the same type. But sometimes we want types that vary based on their values:

```haskell
-- Vec: Lists with length in the type
data Vec : Nat → Type → Type where
  Nil  : Vec 0 A
  Cons : A → Vec n A → Vec (succ n) A

-- Type safety prevents errors at compile time
head : Vec (succ n) A → A  -- Can only call on non-empty vectors!
```

Inductive families enable **dependent pattern matching**, where the type system learns information from which constructor was matched.

## Universe Hierarchy

### Levels

Our system has infinitely many universes indexed by natural numbers:

```
Type 0, Type 1, Type 2, ...
```

The typing rule is simple:

```
Γ ⊢ Type i : Type (i+1)
```

### Cumulativity (Optional)

Some systems include **cumulativity**, where `Type i` is a subtype of `Type (i+1)`:

```
Γ ⊢ A : Type i
─────────────────── (if j ≥ i)
Γ ⊢ A : Type j
```

Our implementation uses strict universes without cumulativity for simplicity.

### Universe Levels in Pi Types

When forming a dependent function type, the universe level follows this rule:

```
Γ ⊢ A : Type i    Γ, x:A ⊢ B : Type j
─────────────────────────────────────
Γ ⊢ Π(x:A). B : Type (max i j)
```

The result lives in the maximum of the two levels.

### Predicativity

Our system is **predicative**, meaning:
- `Π(x:A). B` lives in `Type (max i j)` where `A : Type i` and `B : Type j`
- We cannot quantify over all types to create a type at the same level

Contrast with **impredicative** systems like Coq's `Prop`, where:
- `∀(A:Type). P A` can live in `Prop` even though we quantify over `Type`

### Examples

```haskell
-- Nat : Type 0
-- Bool : Type 0
-- Nat → Bool : Type 0

-- Type 0 : Type 1
-- (Type 0 → Type 0) : Type 1

-- Polymorphic identity at different levels
id0 : Π(A:Type 0). A → A
id0 = λ(A:Type 0). λ(x:A). x

id1 : Π(A:Type 1). A → A
id1 = λ(A:Type 1). λ(x:A). x

-- id0 : Type 1 (quantifies over Type 0)
-- id1 : Type 2 (quantifies over Type 1)
```

### Why This Works

The universe hierarchy prevents:
1. **Girard's paradox**: Can't construct `Type : Type`
2. **Russell's paradox**: Can't construct self-containing sets
3. **Type-level loops**: Can't have circular type definitions

The price we pay is that we sometimes need multiple versions of the same function at different universe levels.

## Equality Types

### Propositional Equality

The equality type `Eq A x y` represents the proposition that `x` and `y` are equal in type `A`:

```haskell
Eq : Π(A:Type i). A → A → Type i
```

It has one constructor, **reflexivity**:

```haskell
refl : Π(A:Type i). Π(x:A). Eq A x x
```

This says: every term is equal to itself.

### Why Only Reflexivity?

You might wonder: where are symmetry and transitivity? The key insight is that **all equality proofs can be constructed using only reflexivity and the J eliminator**. Symmetry and transitivity are *provable* theorems, not axioms.

### The J Eliminator

The J eliminator is the **induction principle for equality**. It says: if you want to prove a property `C y eq` for all equalities `eq : x = y`, it suffices to prove it for `refl x`.

```haskell
J : Π(A:Type i).
    Π(C:(z:A) → Eq A x z → Type i).
    C x (refl x) →
    Π(y:A). Π(eq:Eq A x y). C y eq
```

**Intuition**: If `x = y`, then anything you can prove about `x` and `refl x` also holds for `y` and the proof that `x = y`.

### Reduction Rule for J

When the equality proof is `refl`:

```
J A C p x x (refl x) ~> p
```

This is the **computation rule** for equality types.

### Deriving Equality Properties

Using J, we can prove:

**Symmetry**:
```haskell
sym : Π(A:Type). Π(x y:A). Eq A x y → Eq A y x
sym A x y eq = J A (λz eq'. Eq A z x) (refl x) y eq
```

**Transitivity**:
```haskell
trans : Π(A:Type). Π(x y z:A). Eq A x y → Eq A y z → Eq A x z
trans A x y z eq1 eq2 =
  J A (λy' eq1'. Eq A y' z → Eq A x z)
      (λeq. eq)  -- When y' = x, we just need eq : x = z
      y eq1 eq2
```

**Congruence**:
```haskell
cong : Π(A B:Type). Π(f:A → B). Π(x y:A). Eq A x y → Eq B (f x) (f y)
cong A B f x y eq =
  J A (λy' eq'. Eq B (f x) (f y'))
      (refl (f x))
      y eq
```

### Intensional vs. Extensional Equality

Our equality is **intensional**:
- `Eq A x y` holds only when `x` and `y` are definitionally equal (reduce to the same thing)
- Function extensionality is not built in: two functions that behave the same may not be provably equal

In **extensional** type theory:
- Two functions are equal if they give the same results on all inputs
- The K axiom holds (all equality proofs between the same endpoints are equal)
- Type checking becomes undecidable

### The K Axiom

The K axiom states that all proofs of `x = x` are equal to `refl x`:

```haskell
K : Π(A:Type). Π(x:A). Π(eq:Eq A x x). Eq (Eq A x x) eq (refl x)
```

Our system does not assume K. In **Homotopy Type Theory**, K is rejected because equality proofs can have interesting structure (higher-dimensional paths).

## Inductive Types and Families

### Simple Inductive Types

A simple inductive type like `Nat` has:
- A set of **constructors**
- An **eliminator** (induction principle)

```haskell
data Nat : Type 0 where
  zero : Nat
  succ : Nat → Nat

-- Eliminator
natElim : Π(P:Nat → Type 0).
          P zero →
          (Π(k:Nat). P k → P (succ k)) →
          Π(n:Nat). P n
```

### Inductive Families

An **inductive family** is indexed by one or more values:

```haskell
data Vec : Nat → Type 0 → Type 0 where
  Nil  : Π(A:Type 0). Vec 0 A
  Cons : Π(A:Type 0). Π(n:Nat). A → Vec n A → Vec (succ n) A
```

The type `Vec n A` represents lists of exactly `n` elements of type `A`.

**Key properties**:
- The index `n` appears in the type, not as a parameter
- Different constructors can return different indices
- `Nil` returns `Vec 0 A`
- `Cons` takes `Vec n A` and returns `Vec (succ n) A`

### Parameters vs. Indices

**Parameters** are uniform across all constructors:
```haskell
data List (A:Type 0) : Type 0 where  -- A is a parameter
  Nil  : List A
  Cons : A → List A → List A
```

**Indices** can vary:
```haskell
data Vec : Nat → Type 0 → Type 0 where  -- n is an index
  Nil  : Vec 0 A
  Cons : Vec n A → Vec (succ n) A
```

### The Fin Type

`Fin n` represents natural numbers less than `n`:

```haskell
data Fin : Nat → Type 0 where
  FZ : Π(n:Nat). Fin (succ n)       -- 0 < n+1
  FS : Π(n:Nat). Fin n → Fin (succ n)  -- if i < n then i+1 < n+1
```

**Examples**:
- `Fin 0` is empty (no numbers < 0)
- `Fin 1` contains only `FZ 0` (representing 0)
- `Fin 3` contains `FZ 2`, `FS (FZ 1)`, `FS (FS (FZ 0))` (representing 0, 1, 2)

### Safe Array Indexing

Using `Fin` and `Vec` together, we can implement array indexing that cannot fail:

```haskell
lookup : Π(A:Type 0). Π(n:Nat). Vec n A → Fin n → A
```

The type guarantees:
- If the vector has length `n`, the index must be less than `n`
- No runtime bounds checking needed!
- Impossible to index out of bounds

## Pattern Matching

### Syntax

Pattern matching allows us to deconstruct data:

```haskell
match t with
  | pattern1 -> rhs1
  | pattern2 -> rhs2
  | ...
```

### Patterns

Our system supports:

1. **Variable patterns**: `x` (binds any value)
2. **Constructor patterns**: `Cons x xs` (matches constructor applications)
3. **Wildcard**: `_` (matches anything without binding)

### Dependent Pattern Matching

In dependent types, pattern matching can refine types:

```haskell
head : Π(A:Type 0). Π(n:Nat). Vec (succ n) A → A
head A n v = match v with
  | Cons _ x xs -> x
  -- No Nil case needed—type system knows v : Vec (succ n) A
```

The type `Vec (succ n) A` tells us `v` cannot be `Nil` (which has type `Vec 0 A`).

### Coverage Checking

The type checker must verify that patterns cover all possible cases. For `head`, only the `Cons` case is needed because:
- `v : Vec (succ n) A`
- `Nil : Vec 0 A`
- `0 ≠ succ n` for any `n`
- Therefore `v` cannot be `Nil`

### Compilation to Eliminators

Pattern matching compiles to uses of eliminators:

```haskell
-- Surface syntax
match n with
  | zero -> e1
  | succ k -> e2

-- Desugars to
natElim (λ_. ResultType) e1 (λk _. e2) n
```

## Eliminators

Eliminators are the principled way to do recursion in type theory. Each inductive type comes with an eliminator that embodies its induction principle.

### Natural Numbers

```haskell
natElim : Π(P:Nat → Type 0).
          P zero →
          (Π(k:Nat). P k → P (succ k)) →
          Π(n:Nat). P n
```

**Intuition**: To prove `P n` for all `n`:
1. Prove the base case `P zero`
2. Prove the inductive step: `P k` implies `P (succ k)`
3. Get `P n` for any `n`

**Reduction rules**:
```
natElim P z s zero      ~> z
natElim P z s (succ n)  ~> s n (natElim P z s n)
```

**Example**: Defining addition
```haskell
add : Nat → Nat → Nat
add m n = natElim (λ_. Nat) m (λk rec. succ rec) n

-- add 2 1
-- = natElim (λ_. Nat) 2 (λk rec. succ rec) 1
-- = natElim (λ_. Nat) 2 (λk rec. succ rec) (succ 0)
-- = (λk rec. succ rec) 0 (natElim (λ_. Nat) 2 (λk rec. succ rec) 0)
-- = succ (natElim (λ_. Nat) 2 (λk rec. succ rec) 0)
-- = succ 2
-- = 3
```

### Booleans

```haskell
boolElim : Π(P:Bool → Type 0).
           P true →
           P false →
           Π(b:Bool). P b
```

**Reduction rules**:
```
boolElim P t f true   ~> t
boolElim P t f false  ~> f
```

### Unit Type

```haskell
unitElim : Π(P:Unit → Type 0).
           P TT →
           Π(x:Unit). P x
```

**Reduction rule**:
```
unitElim P u TT ~> u
```

The Unit type has only one value, so there's only one case.

### Empty Type

```haskell
emptyElim : Π(P:Empty → Type 0).
            Π(e:Empty). P e
```

**No reduction rule needed** because there are no values of type `Empty`.

**Ex falso quodlibet**: From a proof of `Empty`, we can derive anything:

```haskell
exFalso : Π(A:Type 0). Empty → A
exFalso A e = emptyElim (λ_. A) e
```

### Why Eliminators?

Eliminators are better than primitive recursion because:

1. **Expressiveness**: Can prove properties, not just compute values
2. **Termination**: Guaranteed to terminate (structural recursion)
3. **Consistency**: Preserve logical consistency
4. **Uniformity**: Uniform interface for all inductive types

## Curry-Howard Correspondence

In dependent type theory, the Curry-Howard correspondence reaches its fullest expression:

| Logic | Type Theory |
|-------|-------------|
| Proposition | Type |
| Proof | Term |
| True | Unit |
| False | Empty |
| P ∧ Q | Σ(x:P). Q (dependent pair) |
| P ∨ Q | Sum type |
| P → Q | Π(x:P). Q (function type) |
| ∀x. P(x) | Π(x:A). P x |
| ∃x. P(x) | Σ(x:A). P x |
| P = Q | Eq Type P Q |
| x = y in A | Eq A x y |

### Propositions as Types

Every proposition corresponds to a type:
- The proposition is **true** if the type is **inhabited**
- The proposition is **false** if the type is **empty**
- A **proof** of the proposition is a **term** of the type

### Examples

**True**:
```haskell
True = Unit
proof_of_true : True
proof_of_true = TT
```

**False**:
```haskell
False = Empty
-- No proof_of_false exists!
```

**Conjunction** (P and Q):
```haskell
And : Type 0 → Type 0 → Type 0
And P Q = Σ(p:P). Q  -- Or simply Pair P Q

-- To prove P ∧ Q, provide proofs of both P and Q
```

**Disjunction** (P or Q):
```haskell
Or : Type 0 → Type 0 → Type 0
Or P Q = Σ(tag:Bool). if tag then P else Q

-- To prove P ∨ Q, provide either a proof of P or a proof of Q
```

**Implication** (P implies Q):
```haskell
Implies : Type 0 → Type 0 → Type 0
Implies P Q = P → Q

-- A proof is a function transforming P-proofs into Q-proofs
```

**Universal quantification** (∀x. P(x)):
```haskell
Forall : Π(A:Type 0). (A → Type 0) → Type 0
Forall A P = Π(x:A). P x

-- A proof is a dependent function
```

**Existential quantification** (∃x. P(x)):
```haskell
Exists : Π(A:Type 0). (A → Type 0) → Type 0
Exists A P = Σ(x:A). P x

-- A proof is a pair of a witness x and a proof that P x holds
```

**Negation** (¬P):
```haskell
Not : Type 0 → Type 0
Not P = P → Empty

-- To prove ¬P, show that P leads to a contradiction
```

### Proof Examples

**Modus Ponens** (P ∧ (P → Q) → Q):
```haskell
modus_ponens : Π(P Q:Type 0). P → (P → Q) → Q
modus_ponens P Q p f = f p
```

**Double Negation Introduction** (P → ¬¬P):
```haskell
double_neg_intro : Π(P:Type 0). P → Not (Not P)
double_neg_intro P p = λf. f p
```

**Explosion** (⊥ → P):
```haskell
explosion : Π(P:Type 0). Empty → P
explosion P e = emptyElim (λ_. P) e
```

### Proofs are Programs

In this view:
- **Writing a proof** = Writing a program
- **Proof checking** = Type checking
- **Theorem** = Type signature
- **Proof term** = Implementation

This enables **certified programming**: programs whose correctness is guaranteed by types.

## Formal Semantics

### Syntax

```
Levels:
  i, j, k ::= 0 | 1 | 2 | ...

Types/Terms (unified):
  t, T ::= Type i                     (universe)
        |  x                          (variable)
        |  λ(x:T). t                  (abstraction)
        |  t₁ t₂                      (application)
        |  Π(x:T₁). T₂                (dependent product)
        |  Σ(x:T₁). T₂                (dependent sum)
        |  (t₁, t₂)                   (pair)
        |  fst t | snd t              (projections)
        |  Eq T t₁ t₂                 (equality type)
        |  refl t                     (reflexivity)
        |  J(T, C, p, x, y, eq)       (J eliminator)
        |  Nat | zero | succ t        (natural numbers)
        |  natElim(P, z, s, n)        (nat eliminator)
        |  Bool | true | false        (booleans)
        |  boolElim(P, t, f, b)       (bool eliminator)
        |  Unit | TT                  (unit type)
        |  unitElim(P, u, x)          (unit eliminator)
        |  Empty                      (empty type)
        |  emptyElim(P, e)            (empty eliminator)
        |  Ind name                   (inductive type ref)
        |  Con name [t₁, ..., tₙ]     (constructor)
        |  match t with branches      (pattern matching)

Patterns:
  p ::= x                             (variable)
     |  Con name [p₁, ..., pₙ]        (constructor pattern)
     |  _                             (wildcard)

Contexts:
  Γ ::= ∅ | Γ, x:T
```

### Typing Rules

**Universes**:
```
─────────────── U-i
Γ ⊢ Type i : Type (i+1)
```

**Variables**:
```
x:T ∈ Γ
─────────────── Var
Γ ⊢ x : T
```

**Dependent Products**:
```
Γ ⊢ A : Type i    Γ, x:A ⊢ B : Type j
───────────────────────────────────── Pi
Γ ⊢ Π(x:A). B : Type (max i j)
```

```
Γ, x:A ⊢ t : B
──────────────────────── Lam
Γ ⊢ λ(x:A). t : Π(x:A). B
```

```
Γ ⊢ f : Π(x:A). B    Γ ⊢ a : A
─────────────────────────────── App
Γ ⊢ f a : B[x := a]
```

**Equality Types**:
```
Γ ⊢ A : Type i    Γ ⊢ x : A    Γ ⊢ y : A
────────────────────────────────────────── Eq-Form
Γ ⊢ Eq A x y : Type i
```

```
Γ ⊢ x : A
─────────────────────── Refl
Γ ⊢ refl x : Eq A x x
```

**J Eliminator**:
```
Γ ⊢ A : Type i
Γ ⊢ x : A
Γ ⊢ C : Π(z:A). Eq A x z → Type i
Γ ⊢ p : C x (refl x)
Γ ⊢ y : A
Γ ⊢ eq : Eq A x y
───────────────────────────────────────── J-Elim
Γ ⊢ J(A, C, p, x, y, eq) : C y eq
```

**Natural Number Eliminator**:
```
Γ ⊢ P : Nat → Type i
Γ ⊢ z : P zero
Γ ⊢ s : Π(k:Nat). P k → P (succ k)
Γ ⊢ n : Nat
───────────────────────────────────────── Nat-Elim
Γ ⊢ natElim(P, z, s, n) : P n
```

### Reduction Rules

**Beta reduction**:
```
(λ(x:A). t) v  ~>  t[x := v]
```

**J reduction** (equality computation):
```
J(A, C, p, x, x, refl x)  ~>  p
```

**Natural number elimination**:
```
natElim(P, z, s, zero)      ~>  z
natElim(P, z, s, succ n)    ~>  s n (natElim(P, z, s, n))
```

**Boolean elimination**:
```
boolElim(P, t, f, true)   ~>  t
boolElim(P, t, f, false)  ~>  f
```

**Unit elimination**:
```
unitElim(P, u, TT)  ~>  u
```

**Pattern matching**:
```
match (Con name [v₁, ..., vₙ]) with
  | Con name [p₁, ..., pₙ] -> rhs
  | ...

~>  rhs[bindings from matching]
```

### Properties

**Type Safety**: Well-typed terms don't get stuck.

**Strong Normalization**: All well-typed terms terminate.

**Confluence**: Reduction is deterministic (up to alpha-equivalence).

**Consistency**: There is no proof of `Empty` (no term of type `Empty`).

## Examples

### Example 1: Polymorphic Identity at Different Levels

```haskell
-- Identity for small types
id0 : Π(A:Type 0). A → A
id0 = λ(A:Type 0). λ(x:A). x

-- Example use
id0 Nat 42 : Nat  -- evaluates to 42

-- Identity for type operators
id1 : Π(A:Type 1). A → A
id1 = λ(A:Type 1). λ(x:A). x

-- Example use
id1 (Type 0 → Type 0) (λX. X) : Type 0 → Type 0
```

### Example 2: Symmetry of Equality

```haskell
sym : Π(A:Type 0). Π(x:A). Π(y:A). Eq A x y → Eq A y x
sym = λ(A:Type 0). λ(x:A). λ(y:A). λ(eq:Eq A x y).
        J(A,
          λ(z:A). λ(e:Eq A x z). Eq A z x,  -- Motive
          refl x,                           -- Base case
          y,
          eq)

-- Type check
sym Nat 0 0 (refl 0) : Eq Nat 0 0
```

### Example 3: Addition

```haskell
add : Nat → Nat → Nat
add = λ(m:Nat). λ(n:Nat).
        natElim(λ(_:Nat). Nat,
                m,
                λ(k:Nat). λ(rec:Nat). succ rec,
                n)

-- Evaluation
add 2 1
= natElim(λ_. Nat, 2, λk rec. succ rec, 1)
= natElim(λ_. Nat, 2, λk rec. succ rec, succ 0)
= (λk rec. succ rec) 0 (natElim(λ_. Nat, 2, λk rec. succ rec, 0))
= succ (natElim(λ_. Nat, 2, λk rec. succ rec, 0))
= succ 2
= 3
```

### Example 4: Proving n + 0 = n

```haskell
add_zero_right : Π(n:Nat). Eq Nat (add n zero) n
add_zero_right = λ(n:Nat).
  natElim(
    λ(n':Nat). Eq Nat (add n' zero) n',  -- Motive
    refl zero,                            -- Base: add 0 0 = 0
    λ(k:Nat). λ(ih:Eq Nat (add k zero) k).  -- Step
      cong Nat Nat succ (add k zero) k ih,
    n)
```

### Example 5: Safe Head Function

```haskell
head : Π(A:Type 0). Π(n:Nat). Vec (succ n) A → A
head = λ(A:Type 0). λ(n:Nat). λ(v:Vec (succ n) A).
         match v with
           | Cons _ x xs -> x
           -- No Nil case: type system knows it's impossible

-- Usage
head Nat 2 (Cons Nat 1 42 (Cons Nat 0 17 (Nil Nat)))  -- Returns 42

-- Trying to call head on Nil gives a type error:
-- head Nat ??? (Nil Nat)  -- Type error: Nil has type Vec 0 A, not Vec (succ n) A
```

### Example 6: Safe Vector Indexing

```haskell
lookup : Π(A:Type 0). Π(n:Nat). Vec n A → Fin n → A
lookup = λ(A:Type 0). λ(n:Nat). λ(v:Vec n A). λ(i:Fin n).
           match v with
             | Cons _ x xs ->
                 match i with
                   | FZ _ -> x
                   | FS _ i' -> lookup A _ xs i'

-- Usage
myVec = Cons Nat 2 10 (Cons Nat 1 20 (Cons Nat 0 30 (Nil Nat)))
index0 = FZ 2                    -- 0 < 3
index1 = FS 2 (FZ 1)             -- 1 < 3
index2 = FS 2 (FS 1 (FZ 0))      -- 2 < 3

lookup Nat 3 myVec index0  -- Returns 10
lookup Nat 3 myVec index1  -- Returns 20
lookup Nat 3 myVec index2  -- Returns 30

-- Trying to use index 3 gives a type error:
-- There's no way to construct a value of type Fin 3 representing 3
```

## Comparison with Chapter 7

| Feature | Chapter 7 | Chapter 8 |
|---------|-----------|-----------|
| **Universes** | Type : Type (inconsistent) | Type i : Type (i+1) |
| **Equality** | Only definitional | Propositional equality (Eq) |
| **Induction** | Recursion only | Eliminators |
| **Pattern Matching** | Not formalized | Full dependent patterns |
| **Inductive Families** | No | Yes (Vec, Fin) |
| **Consistency** | No (Girard's paradox) | Yes |
| **Proof Capability** | Limited | Full theorem proving |
| **Curry-Howard** | Partial | Complete |

### What Chapter 7 Had

- Unified terms and types
- Pi types and Sigma types
- Dependent functions and pairs
- Type-in-Type (simple but inconsistent)

### What Chapter 8 Adds

- **Universe hierarchy** for consistency
- **Equality types** for propositional reasoning
- **J eliminator** for equality induction
- **Inductive families** (Vec, Fin)
- **Eliminators** for principled recursion
- **Pattern matching** with dependent types
- **Full Curry-Howard** correspondence

### Migration Path

Code from Chapter 7 needs minor updates:

1. Add universe levels to Type
2. Replace primitive recursion with eliminators
3. Use Eq for propositional equality
4. Add universe annotations to polymorphic functions

Example:
```haskell
-- Chapter 7
id : Π(A:Type). A → A

-- Chapter 8
id0 : Π(A:Type 0). A → A
id1 : Π(A:Type 1). A → A
```

## Real-World Connections

Full dependent types with universe hierarchy form the foundation of modern proof assistants and verified programming systems.

### Where You've Seen This

#### **Coq (Most Widely Used)**
```coq
(* Universe hierarchy prevents paradoxes *)
Type 0 : Type 1 : Type 2 : ...

(* Verified software *)
- CompCert: Verified C compiler
- Fiat-Crypto: Verified cryptography
- Mathematical proofs: Four Color Theorem
```

#### **Agda (Research & Education)**
```agda
-- Equality types with J eliminator
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Proofs using equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
```

#### **Lean (Modern Proof Assistant)**
```lean
-- Mathematical proofs
theorem add_comm (m n : ℕ) : m + n = n + m :=
  nat.rec_on n
    (show m + 0 = 0 + m, from ...)
    (λ n ih, show m + succ n = succ n + m, from ...)

-- Used to prove theorems in mathlib
```

#### **F* (Verification-Oriented)**
```fstar
// Verified cryptographic code
val aes_encrypt : key:bytes{length key = 16} ->
                  plaintext:bytes{length plaintext = 16} ->
                  Tot (ciphertext:bytes{length ciphertext = 16})
```

### Real-World Impact

| Project | Language | Achievement |
|---------|----------|-------------|
| **CompCert** | Coq | Verified C compiler |
| **seL4** | Isabelle/HOL | Verified microkernel |
| **Fiat-Crypto** | Coq | Verified cryptography |
| **mathlib** | Lean | Digital mathematics library |
| **HACL*** | F* | Verified crypto (used in Firefox) |

### Key Features

| Feature | Purpose | Example |
|---------|---------|---------|
| **Universe hierarchy** | Avoid paradoxes | `Type 0 : Type 1 : ...` |
| **Equality types** | Propositional equality | `x ≡ y` |
| **Inductive families** | Indexed types | `Vec n a`, `Fin n` |
| **Eliminators** | Induction principles | `natElim`, `vecElim` |

### Why Full Dependent Types Matter

1. **Verified Software**: Prove correctness, not just test
2. **Mathematics**: Digital libraries of proven theorems
3. **Security**: Verified cryptography (HACL*, Fiat-Crypto)
4. **Safety-Critical**: seL4 microkernel in autonomous vehicles
5. **Research**: Foundation for next-generation languages

### The Curry-Howard Correspondence

**Programs are proofs, types are propositions:**

| Logic | Type Theory |
|-------|-------------|
| Proposition P | Type τ |
| Proof of P | Term t : τ |
| P → Q | Function type τ₁ → τ₂ |
| P ∧ Q | Product type τ₁ × τ₂ |
| P ∨ Q | Sum type τ₁ + τ₂ |
| ∀x. P(x) | Π type Π(x:A). B |
| ∃x. P(x) | Σ type Σ(x:A). B |

## References

### Foundational Papers

1. **Martin-Löf, Per** (1984). *Intuitionistic Type Theory*. Bibliopolis.
   Original presentation of dependent type theory. Introduces universes, Pi types, Sigma types, equality types.
   [Google Scholar](https://scholar.google.com/scholar?cluster=9207064863129264920)

2. **Coquand, Thierry; Huet, Gérard** (1988). "The Calculus of Constructions." *Information and Computation* 76(2-3).
   Foundation of Coq. Combines dependent types with polymorphism.
   [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0890540188900053) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=3205596489261661697)

3. **Luo, Zhaohui** (1994). *Computation and Reasoning: A Type Theory for Computer Science*. Oxford University Press.
   Comprehensive treatment of dependent type theory (UTT).
   [Google Scholar](https://scholar.google.com/scholar?cluster=10089970779295728206)

### Universe Hierarchies

4. **Coquand, Thierry** (1986). "An Analysis of Girard's Paradox." *LICS*.
   Explains why Type : Type is inconsistent.
   [IEEE](https://ieeexplore.ieee.org/document/4567845) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=16619146726034287926)

5. **Harper, Robert; Pollack, Robert** (1991). "Type Checking with Universes." *TCS* 89(1).
   Practical aspects of implementing universe hierarchies.
   [ScienceDirect](https://www.sciencedirect.com/science/article/pii/030439759190061P) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=11096623553888858892)

### Equality Types

6. **Hofmann, Martin; Streicher, Thomas** (1998). "The Groupoid Interpretation of Type Theory." *Twenty-Five Years of Constructive Type Theory*.
   Semantic interpretation of equality types. Groupoid model.
   [Google Scholar](https://scholar.google.com/scholar?cluster=16459165867051656800)

7. **The Univalent Foundations Program** (2013). *Homotopy Type Theory: Univalent Foundations of Mathematics*.
   Modern perspective on equality in type theory.
   [HoTT Book](https://homotopytypetheory.org/book/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=7965636527132643706)

### Inductive Types

8. **Coquand, Thierry; Paulin, Christine** (1990). "Inductively Defined Types." *COLOG-88*.
   Formalization of inductive types in type theory.
   [SpringerLink](https://link.springer.com/chapter/10.1007/3-540-52335-9_47) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=7879254568979157738)

9. **Dybjer, Peter** (1994). "Inductive Families." *Formal Aspects of Computing* 6(4).
   Comprehensive treatment of inductive families. Vec and Fin.
   [SpringerLink](https://link.springer.com/article/10.1007/BF01211308) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=5851085224276083426)

10. **McBride, Conor; McKinna, James** (2004). "The View from the Left." *JFP* 14(1).
    Dependent pattern matching. Compilation to eliminators.
    [Cambridge](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/view-from-the-left/3DAE3D6E5DA8A1FC5CC8DB4F0AF0C5E8) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=12231859628990685232)

### Pattern Matching

11. **Coquand, Thierry** (1992). "Pattern Matching with Dependent Types." *Types for Proofs and Programs*.
    Theory of dependent pattern matching.
    [Google Scholar](https://scholar.google.com/scholar?cluster=8168284927953888458)

12. **Goguen, Healfdene; McBride, Conor; McKinna, James** (2006). "Eliminating Dependent Pattern Matching." *Algebra, Meaning, and Computation*.
    Compiling pattern matching to eliminators. Coverage checking.
    [SpringerLink](https://link.springer.com/chapter/10.1007/11780274_27) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=12231859628990685232)

### Proof Assistants

13. **Norell, Ulf** (2007). "Towards a Practical Programming Language Based on Dependent Type Theory." PhD thesis, Chalmers.
    Agda: practical dependent types.
    [Chalmers](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=11787413397362878341)

14. **The Coq Development Team** (2023). *The Coq Proof Assistant Reference Manual*.
    [Coq](https://coq.inria.fr/) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=16890529309851284129)

15. **de Moura, Leonardo et al.** (2015). "The Lean Theorem Prover." *CADE-25*.
    Modern proof assistant with dependent types.
    [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-319-21401-6_26) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=10880568587505839893)

16. **Brady, Edwin** (2013). "Idris, a General-Purpose Dependently Typed Programming Language." *JFP* 23(5).
    Practical dependent programming language.
    [Cambridge](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/idris-a-generalpurpose-dependently-typed-programming-language-design-and-implementation/E0F23BFAE9E34A5E4C94E087C02B69F3) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=11628936203266632654)

### Logical Foundations

17. **Howard, William A.** (1980). "The Formulae-as-Types Notion of Construction." In *To H.B. Curry*.
    Classic paper on Curry-Howard correspondence.
    [Google Scholar](https://scholar.google.com/scholar?cluster=15991881543698967061)

18. **Wadler, Philip** (2015). "Propositions as Types." *CACM* 58(12).
    Modern exposition of Curry-Howard.
    [ACM DL](https://dl.acm.org/doi/10.1145/2699407) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=14430234472936129425)

### Implementation

19. **Löh, Andres; McBride, Conor; Swierstra, Wouter** (2010). "A Tutorial Implementation of a Dependently Typed Lambda Calculus." *Fundamenta Informaticae* 102(2).
    Step-by-step implementation guide.
    [LambdaPi](https://www.andres-loeh.de/LambdaPi/) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=16063276671918451765)

20. **Augustsson, Lennart; Coquand, Thierry** (2007). "A Small Type Checker for a Language with Dependent Types." Video lecture.
    Minimal implementation of dependent types (~200 lines).

### Advanced Topics

21. **Sozeau, Matthieu; Mangin, Cyprien** (2019). "Equations Reloaded." *PACMPL* 3(ICFP).
    Advanced pattern matching in Coq. Well-founded recursion.
    [ACM DL](https://dl.acm.org/doi/10.1145/3341690) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=16469920605620048954)

22. **Altenkirch, Thorsten; McBride, Conor; Swierstra, Wouter** (2007). "Observational Equality, Now!" *PLPV*.
    Alternative approaches to equality.
    [ACM DL](https://dl.acm.org/doi/10.1145/1292597.1292608) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=5099850890325070600)

23. **Licata, Daniel R.; Harper, Robert** (2012). "Canonicity for 2-Dimensional Type Theory." *POPL*.
    Computational interpretation of HoTT.
    [ACM DL](https://dl.acm.org/doi/10.1145/2103656.2103691) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=12310413168096419419)

## Summary

Chapter 8 presents a **full dependent type theory** with:

1. **Universe Hierarchy**: Avoiding inconsistency through stratification
2. **Equality Types**: Propositional equality with the J eliminator
3. **Inductive Families**: Types indexed by values (Vec, Fin)
4. **Pattern Matching**: Dependent pattern matching with coverage checking
5. **Eliminators**: Principled recursion for all types
6. **Curry-Howard**: Complete correspondence between logic and types

This system is:
- **Consistent**: No proof of False
- **Strongly normalizing**: All programs terminate
- **Expressive**: Can express and prove mathematical theorems
- **Practical**: Basis for Agda, Coq, Lean, Idris

**Key Takeaways**:
- Dependent types unify terms and types
- The universe hierarchy prevents paradoxes
- Propositional equality enables theorem proving
- Inductive families encode invariants in types
- The Curry-Howard correspondence is a deep connection between logic and computation

**Next Steps**:
- Explore Agda, Coq, or Lean for practical dependent programming
- Study Homotopy Type Theory for a modern perspective
- Implement certified programs using dependent types
- Prove real mathematical theorems in a proof assistant

This completes the journey from the untyped lambda calculus to full dependent types—from the simplest model of computation to a foundation for mathematics and verified software!
