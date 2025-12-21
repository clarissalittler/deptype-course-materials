# Chapter 15: Recursive Types (μ Types)

## Overview

This chapter introduces **recursive types**, which allow type definitions to
refer to themselves. Recursive types are essential for representing common data
structures like lists, trees, and streams in typed programming languages.

The key type constructor is **μ** (mu), pronounced "mu" or "least fixed point":
```
μα. T    -- the recursive type where α refers to the whole type
```

## Learning Objectives

By the end of this chapter, you will:
- Understand the difference between iso-recursive and equi-recursive semantics
- Use fold and unfold operations to work with recursive types
- Encode common data structures (lists, trees) as recursive types
- Understand the relationship between recursion and fixed points
- See how recursive types enable general recursion and non-termination

## Key Concepts

### 1. Recursive Type Syntax

A recursive type `μα. T` binds the type variable `α` in the body `T`:

```
NatList = μα. Unit + (Nat × α)
         ^^    ^^^^^^^^^^^^
         |     Body: either empty (Unit) or a pair of Nat and more list (α)
         |
         α refers to NatList itself
```

### 2. Iso-recursive Semantics

This implementation uses **iso-recursive** types, where:
- `μα. T` is isomorphic to `T[μα.T/α]` but **not equal**
- Explicit `fold` and `unfold` operations witness the isomorphism

The typing rules:
```
   Γ ⊢ t : T[μα.T/α]
─────────────────────────── (T-Fold)
 Γ ⊢ fold [μα.T] t : μα.T

      Γ ⊢ t : μα.T
───────────────────────────── (T-Unfold)
 Γ ⊢ unfold [μα.T] t : T[μα.T/α]
```

### 3. Type Substitution

The notation `T[μα.T/α]` means "substitute the full recursive type for α in T":
```
NatList = μα. Unit + (Nat × α)

Unfolding once:
  (Unit + (Nat × α))[NatList/α]
= Unit + (Nat × NatList)
= Unit + (Nat × μα. Unit + (Nat × α))
```

### 4. Working with Recursive Types

**Creating a value** (introduction):
```
-- Empty list (nil)
nil = fold [NatList] (inl unit as Unit + (Nat × NatList))

-- Non-empty list (cons)
cons = λn:Nat. λl:NatList.
  fold [NatList] (inr <n, l> as Unit + (Nat × NatList))
```

**Decomposing a value** (elimination):
```
-- Check if empty
isEmpty = λl:NatList.
  case unfold [NatList] l of
    inl _ => true
  | inr _ => false

-- Get head (unsafe)
head = λl:NatList.
  case unfold [NatList] l of
    inl _ => 0  -- error case
  | inr p => fst p
```

## Implementation Details

### Syntax

```haskell
data Type
  = TyVar TyVar              -- Type variable: α
  | TyBool | TyNat | TyUnit  -- Base types
  | TyFun Type Type          -- Function: T₁ → T₂
  | TyProd Type Type         -- Product: T₁ × T₂
  | TySum Type Type          -- Sum: T₁ + T₂
  | TyMu TyVar Type          -- Recursive: μα. T

data Term
  = ...
  | TmFold Type Term         -- fold [μα.T] t
  | TmUnfold Type Term       -- unfold [μα.T] t
```

### Type Checking

```haskell
-- Type substitution for recursive types
substTyVar :: TyVar -> Type -> Type -> Type

-- Fold: check that inner term has the unfolded type
TmFold muTy@(TyMu v tyBody) t -> do
  tyT <- infer ctx t
  let expected = substTyVar v muTy tyBody
  if tyT == expected then Right muTy else Left $ TypeMismatch expected tyT

-- Unfold: check that term has the recursive type
TmUnfold muTy@(TyMu v tyBody) t -> do
  tyT <- infer ctx t
  if tyT == muTy
    then Right (substTyVar v muTy tyBody)
    else Left $ TypeMismatch muTy tyT
```

### Evaluation

```haskell
-- Values: fold of a value is a value
isValue (TmFold _ t) = isValue t

-- Evaluation: unfold (fold v) → v
evalStep (TmUnfold _ (TmFold _ v)) | isValue v = Just v
```

## Examples

### Natural Number Lists

```
-- Type definition
NatList = μα. Unit + (Nat × α)

-- Constructors
nil  = fold [NatList] (inl unit as Unit + (Nat × NatList))
cons = λn:Nat. λl:NatList. fold [NatList] (inr <n, l> as Unit + (Nat × NatList))

-- Example list [1, 2, 3]
list123 = cons (succ 0) (cons (succ (succ 0)) (cons (succ (succ (succ 0))) nil))

-- Sum function
sum = λl:NatList.
  case unfold [NatList] l of
    inl _ => 0
  | inr p => fst p + sum (snd p)  -- (requires general recursion)
```

### Self-Application

Recursive types allow us to type self-application, which is impossible in
simply typed lambda calculus:

```
-- The type for self-applicable functions
SelfApp = μα. α → Nat

-- The omega combinator (typed!)
omega = λx:SelfApp. (unfold [SelfApp] x) x

-- This type-checks: fold [SelfApp] omega : SelfApp
```

### Streams (Infinite Data)

```
-- Infinite stream of natural numbers
Stream = μα. Nat × α

-- A stream of ones
ones = fold [Stream] <succ 0, ones>  -- (requires general recursion)

-- Accessors
head = λs:Stream. fst (unfold [Stream] s)
tail = λs:Stream. snd (unfold [Stream] s)
```

## Comparison: Iso-recursive vs Equi-recursive

| Aspect | Iso-recursive | Equi-recursive |
|--------|---------------|----------------|
| Type equality | μα.T ≠ T[μα.T/α] | μα.T = T[μα.T/α] |
| Operations | Explicit fold/unfold | Implicit coercions |
| Type checking | Simpler, syntax-directed | Requires coinductive reasoning |
| Annotation | Type annotation needed | Can be inferred |
| Used in | OCaml, Haskell, Rust | Some ML variants |

## Theoretical Notes

### Fixed Points and Recursion

The μ type is the **least fixed point** of a type operator:
```
μα. F(α) is the smallest type T such that T ≅ F(T)
```

This connection to fixed points is why recursive types enable general recursion—we can build a typed Y combinator.

### Positive Occurrences

For well-behaved recursive types, the bound variable should occur only
**positively** (in covariant positions). Negative occurrences can lead to
logical inconsistency in some type systems.

### Termination

Adding μ types breaks strong normalization. With recursive types, we can write
non-terminating programs:
```
let loop = (λx:SelfApp. (unfold [SelfApp] x) x)
           (fold [SelfApp] (λx:SelfApp. (unfold [SelfApp] x) x))
```

## Running the Code

```bash
# Build the project
stack build

# Run the REPL
stack exec recursive-repl

# Run tests
stack test
```

### REPL Examples

```
recursive> :t fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a))
μa. Unit + a

recursive> unfold [mu a. Nat] (fold [mu a. Nat] (succ 0))
succ 0
```

## Exercises

See `exercises/EXERCISES.md` for practice problems covering:
1. Encoding data structures with μ types
2. The relationship between fold/unfold and constructors/pattern matching
3. Self-application and the Y combinator
4. Mutual recursion encodings

## Further Reading

### Textbooks

- **Pierce, "Types and Programming Languages" (2002), Chapter 20: Recursive Types**
  The standard textbook treatment of iso-recursive and equi-recursive types.
  [MIT Press](https://www.cis.upenn.edu/~bcpierce/tapl/) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=2853553209915529600)

### Research Papers

- **Crary, Harper, Puri, "What is a Recursive Module?" (1999)**
  Explores recursive modules and their typing, with connections to recursive types.
  [ACM DL](https://dl.acm.org/doi/10.1145/301631.301641) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=11704685405570553858)

- **Amadio & Cardelli, "Subtyping Recursive Types" (1993)**
  Foundational work on subtyping for recursive types.
  [ACM DL](https://dl.acm.org/doi/10.1145/155183.155231) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=8951422590645919221)

## Connection to Other Chapters

- **Chapter 11 (Refinement Types):** Recursive types + refinements = sized types
- **Chapter 12 (Effect Systems):** Effect handlers often use recursive types
- **Chapter 16 (HoTT):** Higher inductive types generalize recursive types
