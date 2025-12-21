# Chapter 16: Homotopy Type Theory

## Overview

Homotopy Type Theory (HoTT) is a revolutionary approach to type theory that
interprets types as **spaces** and equalities as **paths**. This geometric
perspective unifies type theory with homotopy theory and leads to powerful
new principles like the univalence axiom.

This chapter provides a simplified implementation of the core concepts:
identity types, path operations, and the basic path algebra that forms the
foundation of HoTT.

## Learning Objectives

By the end of this chapter, you will:
- Understand identity types as paths between points
- Master the J eliminator (path induction)
- Use path operations: sym, trans, ap, transport
- See how types form higher groupoid structures
- Appreciate the conceptual foundations of univalence

## Key Concepts

### 1. Identity Types as Paths

In HoTT, the identity type `Id A a b` represents a **path** from `a` to `b`
in the space `A`:

```
     a --------p-------> b
         path in A
```

This is a radical reinterpretation of equality:
- Types are spaces (or ∞-groupoids)
- Terms are points in those spaces
- Equalities are paths between points

### 2. Reflexivity (refl)

The canonical path is reflexivity—the constant path at a point:

```
refl : (a : A) → Id A a a
```

Think of this as "staying in place"—a path that doesn't move.

### 3. Path Induction (J)

The J eliminator is the fundamental principle for working with paths:

```
J : (C : (x y : A) → Id A x y → Type) →  -- motive
    ((x : A) → C x x refl) →              -- base case
    (a b : A) → (p : Id A a b) →          -- inputs
    C a b p                                -- result
```

**Intuition:** To prove something for all paths, it suffices to prove it
for reflexivity paths. All paths are "homotopic" to constant paths.

**Computation rule:**
```
J C base a a refl ≡ base a
```

### 4. Path Operations

From J, we derive the groupoid operations on paths:

**Symmetry (path inverse):**
```
sym : Id A a b → Id A b a
sym refl = refl
```

**Transitivity (path composition):**
```
trans : Id A a b → Id A b c → Id A a c
trans refl q = q
```

**Action on paths (functoriality):**
```
ap : (f : A → B) → Id A a b → Id B (f a) (f b)
ap f refl = refl
```

**Transport (path lifting):**
```
transport : (P : A → Type) → Id A a b → P a → P b
transport P refl x = x
```

### 5. Path Algebra

Paths satisfy the groupoid laws:

| Law | Statement |
|-----|-----------|
| Left identity | `trans refl p = p` |
| Right identity | `trans p refl = p` |
| Inverses | `trans p (sym p) = refl` |
| Associativity | `trans (trans p q) r = trans p (trans q r)` |

These equalities are themselves paths—paths between paths!

## Implementation Details

### Syntax

```haskell
data Type
  = TyId Type Term Term    -- Identity type: Id A a b
  | TyVoid                 -- Empty type (for absurdity)
  | TyUniverse             -- Universe of types
  | ...                    -- Standard types

data Term
  = TmRefl Type Term       -- refl : a =_A a
  | TmJ Type Term Term Term Term  -- J eliminator
  | TmSym Term             -- sym : (a = b) → (b = a)
  | TmTrans Term Term      -- trans : (a = b) → (b = c) → (a = c)
  | TmAp Term Term         -- ap f : (a = b) → (f a = f b)
  | TmTransport Type Term Term  -- transport : (a = b) → P a → P b
  | TmAbsurd Type Term     -- ex falso
  | ...                    -- Standard terms
```

### Type Checking

```haskell
-- refl : a =_A a
TmRefl ty a -> do
  tyA <- infer ctx a
  if tyA == ty
    then Right $ TyId ty a a
    else Left $ TypeMismatch ty tyA

-- sym : (a = b) → (b = a)
TmSym t -> do
  ty <- infer ctx t
  case ty of
    TyId tyA a b -> Right $ TyId tyA b a
    _ -> Left $ ExpectedIdentity ty
```

### Evaluation

Path operations compute on reflexivity:

```haskell
-- sym refl = refl
TmSym (TmRefl ty a) -> Just $ TmRefl ty a

-- trans refl refl = refl
TmTrans (TmRefl ty a) (TmRefl _ _) -> Just $ TmRefl ty a

-- ap f refl = refl
TmAp f (TmRefl tyA a) -> Just $ TmRefl tyA (App f a)

-- transport refl t = t
TmTransport _ (TmRefl _ _) t -> Just t

-- J base a a refl = base a
TmJ _ base a a' (TmRefl _ a'')
  | a == a' && a == a'' -> Just $ App base a
```

## Examples

### Basic Path Construction

```
-- Reflexivity at 0
refl [Nat] 0 : Id Nat 0 0

-- Symmetry
sym (refl [Nat] 0) : Id Nat 0 0  -- evaluates to refl

-- Transitivity
trans (refl [Nat] 0) (refl [Nat] 0) : Id Nat 0 0  -- evaluates to refl
```

### Action on Paths

```
-- A function f : Nat → Nat
let f = λx:Nat. succ x in

-- Apply f to a path
ap f (refl [Nat] 0)
-- Type: Id Nat (succ 0) (succ 0)
-- Evaluates to: refl [Nat] (succ 0)
```

### Transport

```
-- Transport along refl does nothing
transport [Nat] (refl [Bool] true) (succ 0)
-- Evaluates to: succ 0
```

## The Bigger Picture

### Univalence (Not Implemented)

The univalence axiom states:
```
(A ≃ B) ≃ (A = B)
```

This says **equivalent types are equal**—a revolutionary principle that
implies function extensionality and much more.

### Higher Inductive Types (Not Implemented)

HoTT also features higher inductive types that specify both points and paths
as constructors:

```
-- The circle
data S¹ where
  base : S¹
  loop : Id S¹ base base

-- The sphere
data S² where
  base : S²
  surf : Id (Id S² base base) refl refl
```

### h-Levels

Types are classified by their "h-level" or truncation level:
- **(-2) Contractible:** Unique element up to path
- **(-1) Propositions:** At most one element up to path
- **(0) Sets:** Paths between elements are propositions
- **(1) Groupoids:** Paths form sets
- And so on...

## Running the Code

```bash
# Build the project
stack build

# Run the REPL
stack exec hott-repl

# Run tests
stack test
```

### REPL Examples

```
hott> :t refl [Nat] 0
Id Nat 0 0

hott> sym (refl [Bool] true)
refl [Bool] true

hott> :t ap (\x:Nat. succ x) (refl [Nat] 0)
Id Nat (succ 0) (succ 0)
```

## Exercises

See `exercises/EXERCISES.md` for practice problems covering:
1. Path algebra and groupoid laws
2. The J eliminator and its computation rule
3. Transport and dependent paths
4. Function extensionality
5. The univalence axiom (conceptual)

## Further Reading

### The Definitive Reference

- **The Univalent Foundations Program, "Homotopy Type Theory: Univalent Foundations of Mathematics" (2013)**
  The HoTT Book - the comprehensive reference written collaboratively by the HoTT community.
  [Official Site](https://homotopytypetheory.org/book/) |
  [arXiv](https://arxiv.org/abs/1308.0729) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=7965636527132643706)

### Introductory Materials

- **Martín Hötzel Escardó, "Introduction to Univalent Foundations of Mathematics with Agda" (2019)**
  A practical introduction to HoTT with verified Agda code.
  [arXiv](https://arxiv.org/abs/1911.00580) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=11288689926672276940)

- **Egbert Rijke, "Introduction to Homotopy Type Theory" (2022)**
  A comprehensive textbook-style introduction to HoTT.
  [arXiv](https://arxiv.org/abs/2212.11082) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=3888694165287583795)

### Foundational Papers

- **Vladimir Voevodsky, "An experimental library of formalized Mathematics based on the univalent foundations" (2015)**
  Describes the UniMath library and univalent foundations.
  [arXiv](https://arxiv.org/abs/1401.0053) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=18260839295497949859)

## Connection to Other Chapters

- **Chapter 15 (Recursive Types):** Higher inductive types generalize recursion
- **Chapter 11 (Refinement Types):** Propositions-as-types meets paths
- **All chapters:** HoTT provides a unifying framework for type theory

## Limitations of This Implementation

This is a simplified presentation that omits:
- Full dependent types (Π and Σ)
- Universe polymorphism
- Higher inductive types
- The univalence axiom
- Interval-based path types (cubical type theory)

For a full HoTT implementation, see Agda with --cubical, or the Arend language.
