# Chapter 2: Simply Typed Lambda Calculus (STLC)

## Overview

The simply typed lambda calculus (STLC) extends the untyped lambda calculus from Chapter 1 with a simple type system. This addition provides two major benefits:

1. **Type Safety**: Well-typed programs cannot "go wrong" (get stuck in an undefined state)
2. **Termination**: All well-typed programs terminate (strong normalization)

This chapter implements STLC with base types (Bool, Nat) and function types.

## Syntax

### Types

```
τ ::=                (types)
    Bool             boolean type
    Nat              natural number type
    τ → τ            function type
```

### Terms

```
t ::=                (terms)
    x                variable
    λx:τ. t          abstraction
    t t              application
    true             constant true
    false            constant false
    if t then t else t  conditional
    0                constant zero
    succ t           successor
    pred t           predecessor
    iszero t         zero test
```

### Values

```
v ::=                (values)
    λx:τ. t          lambda abstraction
    true             true value
    false            false value
    nv               numeric value

nv ::=               (numeric values)
    0                zero value
    succ nv          successor of numeric value
```

## Type System

### Typing Context

A typing context Γ is a finite mapping from variables to types:

```
Γ ::= ∅ | Γ, x:τ
```

### Typing Rules

The typing judgment Γ ⊢ t : τ states that term `t` has type `τ` in context `Γ`.

```
─────────────────── (T-True)
Γ ⊢ true : Bool


─────────────────── (T-False)
Γ ⊢ false : Bool


─────────────────── (T-Zero)
Γ ⊢ 0 : Nat


Γ ⊢ t : Nat
─────────────────── (T-Succ)
Γ ⊢ succ t : Nat


Γ ⊢ t : Nat
─────────────────── (T-Pred)
Γ ⊢ pred t : Nat


Γ ⊢ t : Nat
─────────────────── (T-IsZero)
Γ ⊢ iszero t : Bool


x:τ ∈ Γ
─────────────────── (T-Var)
Γ ⊢ x : τ


Γ, x:τ₁ ⊢ t : τ₂
─────────────────── (T-Abs)
Γ ⊢ λx:τ₁. t : τ₁ → τ₂


Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : τ₁
─────────────────────────────── (T-App)
Γ ⊢ t₁ t₂ : τ₂


Γ ⊢ t₁ : Bool    Γ ⊢ t₂ : τ    Γ ⊢ t₃ : τ
────────────────────────────────────────── (T-If)
Γ ⊢ if t₁ then t₂ else t₃ : τ
```

### Type Checking Algorithm

Type checking is **decidable** for STLC. The algorithm is syntax-directed:

1. For each term construct, apply the corresponding typing rule
2. For variables, look up the type in the context
3. For applications, check that the function type matches the argument
4. For conditionals, ensure the condition is Bool and branches have the same type

## Operational Semantics

### Call-by-Value Evaluation Rules

```
               t₁ → t₁'
        ────────────────────── (E-App1)
        t₁ t₂ → t₁' t₂


               t₂ → t₂'
        ────────────────────── (E-App2)
        v₁ t₂ → v₁ t₂'


        ──────────────────────────── (E-AppAbs)
        (λx:τ. t) v → [x ↦ v]t


               t₁ → t₁'
        ──────────────────────────────────────── (E-If)
        if t₁ then t₂ else t₃ → if t₁' then t₂ else t₃


        ──────────────────────────── (E-IfTrue)
        if true then t₂ else t₃ → t₂


        ──────────────────────────── (E-IfFalse)
        if false then t₂ else t₃ → t₃


               t → t'
        ────────────────────── (E-Succ)
        succ t → succ t'


               t → t'
        ────────────────────── (E-Pred)
        pred t → pred t'


        ────────────────────── (E-PredZero)
        pred 0 → 0


        ────────────────────── (E-PredSucc)
        pred (succ nv) → nv


               t → t'
        ────────────────────── (E-IsZero)
        iszero t → iszero t'


        ────────────────────── (E-IsZeroZero)
        iszero 0 → true


        ──────────────────────────── (E-IsZeroSucc)
        iszero (succ nv) → false
```

## Metatheory

### Progress Theorem

**Theorem (Progress)**: If `t` is a closed, well-typed term (i.e., `⊢ t : τ` for some `τ`), then either:
1. `t` is a value, or
2. there exists a term `t'` such that `t → t'`

**Proof sketch**: By induction on typing derivations.

### Preservation Theorem

**Theorem (Preservation / Subject Reduction)**: If `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`.

**Proof sketch**: By induction on evaluation derivations.

### Type Safety

**Corollary (Type Safety)**: Well-typed terms do not get stuck.

A term is **stuck** if it is not a value and no evaluation rule applies. Type safety follows from Progress and Preservation:
- Progress ensures well-typed terms are either values or can step
- Preservation ensures that evaluation preserves types
- Together, they guarantee that well-typed terms never reach a stuck state

### Strong Normalization

**Theorem (Strong Normalization)**: Every well-typed term in STLC terminates.

This is a remarkable property: by adding types, we've restricted the language so much that all programs halt. This means we've lost Turing-completeness (we cannot express the Y combinator or general recursion in STLC).

## Examples

### Boolean Functions

```
not = λx:Bool. if x then false else true
and = λx:Bool. λy:Bool. if x then y else false
or  = λx:Bool. λy:Bool. if x then true else y
```

### Numeric Functions

```
iszeroLike = λn:Nat. iszero n
add1 = λn:Nat. succ n
sub1 = λn:Nat. pred n
```

### Higher-Order Functions

```
-- Apply a function twice
twice : (Nat → Nat) → Nat → Nat
twice = λf:Nat → Nat. λx:Nat. f (f x)

-- Example: twice add1 0 → succ (succ 0)


-- Boolean identity
idBool : Bool → Bool
idBool = λx:Bool. x

-- Natural number identity
idNat : Nat → Nat
idNat = λx:Nat. x
```

### What We Cannot Express

Due to strong normalization, we cannot express:
- General recursion (no fixed-point combinator)
- Non-terminating computations
- The factorial function (requires recursion)

These limitations are addressed in later chapters.

## Implementation

### Project Structure

```
chapter-02-simply-typed-lambda/
├── src/
│   ├── Syntax.hs       -- AST for types and terms
│   ├── TypeCheck.hs    -- Type checking algorithm
│   ├── Eval.hs         -- Evaluation (CBV semantics)
│   ├── Parser.hs       -- Parser for terms and types
│   └── Pretty.hs       -- Pretty printer
├── test/
│   └── Spec.hs         -- Test suite
├── package.yaml        -- Haskell package configuration
└── README.md           -- This file
```

### Building and Testing

```bash
# Initialize stack (if not already done)
stack init

# Build the project
stack build

# Run tests
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
import Pretty

-- Parse a term
let Right term = parseTerm "(\\x:Bool. x) true"

-- Type check it
let Right ty = typeCheck term  -- ty = TyBool

-- Evaluate it
let result = eval term  -- result = TmTrue

-- Pretty print
putStrLn $ pretty result ++ " : " ++ prettyType ty
-- Output: true : Bool
```

## Key Insights

1. **Types as Specifications**: Types describe what kind of value a term computes
2. **Static vs Dynamic**: Type checking happens before evaluation (static)
3. **Type Safety**: "Well-typed programs don't go wrong" (Milner)
4. **Decidability**: Type checking is decidable (algorithmic)
5. **Termination vs Expressiveness**: Gaining termination means losing Turing-completeness
6. **Annotations**: Lambdas require type annotations (λx:**τ**. t)

## Comparison with Chapter 1

| Feature | Untyped λ-calculus | Simply Typed λ-calculus |
|---------|-------------------|------------------------|
| All programs terminate | No | Yes |
| Turing-complete | Yes | No |
| Type checking | N/A | Decidable |
| Can encode Y combinator | Yes | No |
| Type annotations required | No | Yes (on λ) |
| Type safety | No | Yes |

## Theoretical Properties Summary

| Property | Holds? |
|----------|--------|
| Progress | ✓ |
| Preservation | ✓ |
| Type Safety | ✓ |
| Strong Normalization | ✓ |
| Confluence | ✓ |
| Decidable Type Checking | ✓ |
| Turing Complete | ✗ |

## References

### Essential Reading

1. **Pierce, Benjamin C.** (2002). *Types and Programming Languages*. MIT Press.
   - Chapter 9: Simply Typed Lambda Calculus
   - Chapter 11: Simple Extensions
   - The standard reference for typed λ-calculi

2. **Sørensen, Morten Heine and Urzyczyn, Paweł** (2006). *Lectures on the Curry-Howard Isomorphism*. Elsevier.
   - Chapter 2: The Simply Typed Lambda Calculus
   - Connects types to logic via Curry-Howard

3. **Harper, Robert** (2016). *Practical Foundations for Programming Languages* (2nd ed.). Cambridge University Press.
   - Chapter 10: Function Definitions and Values
   - Modern perspective on type theory

### Theoretical Foundations

4. **Church, Alonzo** (1940). "A Formulation of the Simple Theory of Types." *Journal of Symbolic Logic*, 5(2): 56-68.
   - Original formulation of simple type theory

5. **Curry, Haskell B. and Feys, Robert** (1958). *Combinatory Logic, Volume I*. North-Holland.
   - Early development of typed combinatory logic

6. **Girard, Jean-Yves; Lafont, Yves; and Taylor, Paul** (1989). *Proofs and Types*. Cambridge University Press.
   - Deep dive into the theory of typed systems
   - Available free online

### Strong Normalization

7. **Tait, William W.** (1967). "Intensional Interpretations of Functionals of Finite Type I." *Journal of Symbolic Logic*, 32(2): 198-212.
   - Classic proof of strong normalization for STLC

8. **Barendregt, Henk** (1992). "Lambda Calculi with Types." In *Handbook of Logic in Computer Science*, Volume 2.
   - Comprehensive coverage including normalization proofs

### Implementation

9. **Augustsson, Lennart** (1998). "Cayenne—a language with dependent types." In *ICFP*.
   - Practical implementation insights

### Online Resources

10. **Software Foundations** (Pierce et al.)
    - Vol 2: Programming Language Foundations
    - Coq formalization of STLC
    - https://softwarefoundations.cis.upenn.edu/

11. **Type Theory Study Group Resources**
    - https://github.com/type-theory
    - Implementations and tutorials

## Exercises

1. Extend STLC with pairs (product types)
2. Add let-bindings as syntactic sugar
3. Implement type inference (remove type annotations)
4. Prove preservation by hand for a simple term
5. Add a unit type and prove it's still strongly normalizing
6. Implement Church-style vs Curry-style typing
7. Add type ascription `t as τ`
8. Compare evaluation speeds for different reduction strategies

## Next Chapter

In [Chapter 3](../chapter-03-stlc-adt), we extend STLC with algebraic data types (sums, products, records) and pattern matching, greatly increasing its expressiveness while maintaining type safety.
