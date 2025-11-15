# Chapter 7: Dependent Types - Exercises

These exercises explore dependent types where types can depend on values.

## Exercise 1: Basic Dependent Functions

Implement basic polymorphic functions using dependent types.

### 1a. Polymorphic Identity

Implement the polymorphic identity function:
```
id : Π(A:Type). A → A
id = λ(A:Type). λ(x:A). x
```

**Type**: `Π(A:Type). A → A`
**Test**: `id Nat 0` should evaluate to `0`

### 1b. Polymorphic Const

Implement the polymorphic const function:
```
const : Π(A:Type). Π(B:Type). A → B → A
```

**Meaning**: Returns the first argument, ignores the second

### 1c. Polymorphic Compose

Implement function composition:
```
compose : Π(A:Type). Π(B:Type). Π(C:Type). (B → C) → (A → B) → A → C
```

**Learning Objective**: Understand how Π generalizes function types.

## Exercise 2: Dependent Pairs (Sigma Types)

Work with dependent pairs where the type of the second component depends on the first.

### 2a. Dependent Pair Creation

Create a dependent pair where the second component's type depends on the first:
```
-- A pair of a type A and a value of type A
TypeAndValue : Type
TypeAndValue = Σ(A:Type). A
```

Create an example: `(Nat, 0) : TypeAndValue`

### 2b. Projections

Given `p : Σ(x:Nat). Nat`:
- Implement `fst p` to get the first component
- Implement `snd p` to get the second component

**Note**: The type of `snd p` is `Nat` (but in general, it depends on `fst p`)

### 2c. Sigma Swap

Implement a function that swaps the components of a dependent pair:
```
swap : Σ(x:Nat). Nat → Σ(y:Nat). Nat
swap p = (snd p, fst p)
```

**Learning Objective**: Understand how dependent pairs generalize product types.

## Exercise 3: Type Families (Conceptual)

While we don't have full inductive families in this chapter, we can explore the concept.

### 3a. Vector Type (Conceptual)

In a full dependent type system, we could define:
```
Vec : Nat → Type → Type
Vec 0     A = Unit
Vec (n+1) A = A × Vec n A
```

**Question**: What would be the type of `cons` for vectors?
**Answer**: `Π(A:Type). Π(n:Nat). A → Vec n A → Vec (n+1) A`

### 3b. Length-Indexed Lists

**Question**: How do dependent types help prevent array index out-of-bounds errors?

**Answer**: With vectors, the lookup function would have type:
```
lookup : Π(A:Type). Π(n:Nat). Vec n A → Fin n → A
```
where `Fin n` is the type of natural numbers less than `n`. This makes out-of-bounds access impossible!

**Learning Objective**: Understand how types can encode invariants.

## Exercise 4: Church Encodings with Dependent Types

Extend Church encodings to use dependent types.

### 4a. Polymorphic Church Booleans

Define Church booleans using dependent types:
```
CBool : Type
CBool = Π(A:Type). A → A → A

ctrue : CBool
ctrue = λ(A:Type). λ(t:A). λ(f:A). t

cfalse : CBool
cfalse = λ(A:Type). λ(t:A). λ(f:A). f
```

### 4b. Church Boolean Operations

Implement:
```
cand : CBool → CBool → CBool
cor  : CBool → CBool → CBool
cnot : CBool → CBool
```

### 4c. Polymorphic Church Numerals

Define Church numerals with dependent types:
```
CNat : Type
CNat = Π(A:Type). (A → A) → A → A

czero : CNat
csucc : CNat → CNat
```

**Learning Objective**: See how dependent types make Church encodings more precise.

## Exercise 5: Existential Types via Sigma

Existential types can be encoded using Sigma types.

### 5a. Abstract Data Type

An abstract data type with hidden representation:
```
AbstractNat : Type
AbstractNat = Σ(Rep:Type). (Rep × (Rep → Nat))
```

This is a pair of:
1. A representation type `Rep`
2. A value of type `Rep` and a function to convert it to `Nat`

Create an example using `Bool` as the representation.

### 5b. Interface Implementation

Encode an interface with implementation:
```
Stack : Type
Stack = Σ(S:Type). (S × (Nat → S → S) × (S → Nat))
```

Components:
1. Stack type `S`
2. Empty stack
3. Push function
4. Pop function

**Learning Objective**: Understand the connection between Σ types and existential types.

## Exercise 6: Proof-Relevant Programming

Use types as specifications and terms as proofs.

### 6a. Non-Empty Type

Define a type that represents "a proof that Nat is inhabited":
```
Inhabited : Type → Type
Inhabited A = A

proofNatInhabited : Inhabited Nat
proofNatInhabited = 0
```

### 6b. Function Type as Implication

The type `A → B` can be read as "A implies B".

Create:
```
-- If we have a Nat, we have a Nat
natToNat : Nat → Nat
natToNat n = n
```

This is a proof that "Nat implies Nat".

### 6c. Pair Type as Conjunction

The type `Σ(x:A). B` can be read as "A and B" (when B doesn't depend on x).

Create:
```
-- We have both a Nat and a Bool
natAndBool : Σ(x:Nat). Bool
natAndBool = (0, true)
```

**Learning Objective**: Understand the Curry-Howard correspondence.

## Exercise 7: Dependent Type Utilities

Implement useful utility functions.

### 7a. Apply Function

Apply a function to an argument:
```
apply : Π(A:Type). Π(B:Type). (A → B) → A → B
apply A B f x = f x
```

### 7b. Flip Arguments

Flip the order of arguments:
```
flip : Π(A:Type). Π(B:Type). Π(C:Type). (A → B → C) → B → A → C
```

### 7c. Curry/Uncurry

Convert between curried and uncurried functions:
```
curry : Π(A:Type). Π(B:Type). Π(C:Type).
        (Σ(x:A). B → C) → A → B → C

uncurry : Π(A:Type). Π(B:Type). Π(C:Type).
          (A → B → C) → Σ(x:A). B → C
```

**Learning Objective**: Work comfortably with dependent function types.

## Theoretical Exercises

### T1. Type-in-Type

**Question**: Our implementation uses `Type : Type`. What's the problem with this?

**Answer**: Type-in-Type leads to logical inconsistency via Girard's paradox (similar to Russell's paradox in set theory). A proper system uses a hierarchy of universes: `Type₀ : Type₁ : Type₂ : ...`

### T2. Decidability

**Question**: Is type checking for dependent types decidable?

**Answer**: Yes! Type checking is decidable if:
1. Type inference is decidable
2. Type conversion is decidable (checking if two types are equal)

Our system has both properties.

### T3. Eta Equality

**Question**: Should `λ(x:A). f x` be equal to `f` (η-equality)?

**Answer**: Yes, η-equality for functions is important for extensionality. Our system currently uses syntactic equality, but could be extended with η-rules.

### T4. Comparison with System F

**Question**: How does dependent type theory relate to System F?

**Answer**:
- System F: Types abstract over types (`∀A. τ`)
- Dependent Types: Types abstract over *terms* (`Π(x:A). B`)
- Dependent types are strictly more expressive

## Implementation Challenges

### C1. Normalization

**Challenge**: Implement full normalization including:
- η-expansion for functions
- Normalization under binders

### C2. Equality Checking

**Challenge**: Implement definitional equality checking:
```
defEq : Term → Term → Bool
```

Should handle:
- α-equivalence (renaming)
- β-equivalence (evaluation)
- η-equivalence (extensionality)

### C3. Universe Hierarchy

**Challenge**: Replace `Type : Type` with a hierarchy:
```
Type 0 : Type 1 : Type 2 : ...
```

Modify the type checker to track universe levels.

## References

1. **Martin-Löf, Per** (1984). *Intuitionistic Type Theory*
   - Foundational work on dependent types

2. **Nordström, Bengt; Petersson, Kent; Smith, Jan M.** (1990). *Programming in Martin-Löf's Type Theory*
   - Excellent introduction with examples

3. **Coquand, Thierry; Huet, Gérard** (1988). "The Calculus of Constructions"
   - Combines dependent types with polymorphism

4. **Norell, Ulf** (2007). "Towards a practical programming language based on dependent type theory"
   - PhD thesis on Agda

5. **Brady, Edwin** (2013). "Idris, a general-purpose dependently typed programming language"
   - Practical dependent type programming

## Next Steps

After mastering these exercises, you'll understand:
- How types can depend on values
- The difference between Π and → types
- How Σ types generalize products
- The basics of proof-relevant programming
- The Curry-Howard correspondence

In Chapter 8, we'll explore:
- Full inductive families (Vec, Fin, etc.)
- Equality types and proofs
- Universe hierarchies
- Quotient types
- Real theorem proving!
