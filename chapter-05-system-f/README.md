# Chapter 5: System F (Polymorphic Lambda Calculus)

## Overview

System F, also known as the **polymorphic lambda calculus** or **second-order lambda calculus**, extends STLC with **explicit polymorphism**. Unlike Hindley-Milner (Chapter 4), polymorphism is explicit through **type abstraction** (Λα. t) and **type application** (t [τ]).

**Key Innovation**: First-class polymorphic functions via universal quantification.

## Comparison with Previous Chapters

| Feature | STLC (Ch 2) | Hindley-Milner (Ch 4) | System F (Ch 5) |
|---------|-------------|----------------------|-----------------|
| Polymorphism | None | Implicit (let-poly) | Explicit (∀) |
| Type annotations | Required | Not needed | Required |
| Type abstraction | No | No | Yes (Λα. t) |
| Type application | No | No | Yes (t [τ]) |
| First-class poly | No | No | Yes! |
| Type inference | Decidable | Decidable | **Undecidable** |

## Syntax

### Types

```
τ ::=
    α                type variable
    τ → τ            function type
    ∀α. τ            universal type
    Bool | Nat       base types
```

### Terms

```
t ::=
    x                variable
    λx:τ. t          abstraction
    t t              application
    Λα. t            type abstraction
    t [τ]            type application
    true | false     booleans
    if t then t else t
    0 | succ t | pred t | iszero t
```

### Values

```
v ::=
    λx:τ. t          lambda value
    Λα. t            type lambda value
    true | false
    0 | succ v
```

## Type System

### Typing Context

```
Γ ::= ∅ | Γ, x:τ      (term variable context)
Δ ::= ∅ | Δ, α        (type variable context)
```

### Typing Rules

```
α ∈ Δ
─────────────── (T-TyVar)
Δ; Γ ⊢ α type


Δ; Γ ⊢ τ₁ type    Δ; Γ ⊢ τ₂ type
─────────────────────────────────── (T-Arrow)
Δ; Γ ⊢ τ₁ → τ₂ type


Δ, α; Γ ⊢ τ type
──────────────── (T-Forall)
Δ; Γ ⊢ ∀α. τ type


x:τ ∈ Γ    Δ; Γ ⊢ τ type
─────────────────────────── (T-Var)
Δ; Γ ⊢ x : τ


Δ; Γ ⊢ τ₁ type    Δ; Γ, x:τ₁ ⊢ t : τ₂
──────────────────────────────────── (T-Abs)
Δ; Γ ⊢ λx:τ₁. t : τ₁ → τ₂


Δ; Γ ⊢ t₁ : τ₁ → τ₂    Δ; Γ ⊢ t₂ : τ₁
──────────────────────────────────────── (T-App)
Δ; Γ ⊢ t₁ t₂ : τ₂


Δ, α; Γ ⊢ t : τ
──────────────────────── (T-TyAbs)
Δ; Γ ⊢ Λα. t : ∀α. τ


Δ; Γ ⊢ t : ∀α. τ    Δ; Γ ⊢ τ' type
─────────────────────────────────── (T-TyApp)
Δ; Γ ⊢ t [τ'] : [α ↦ τ']τ
```

## Operational Semantics

### Call-by-Value Evaluation

```
               t₁ → t₁'
        ────────────────────── (E-App1)
        t₁ t₂ → t₁' t₂


               t₂ → t₂'
        ────────────────────── (E-App2)
        v₁ t₂ → v₁ t₂'


        ──────────────────────────── (E-AppAbs)
        (λx:τ. t) v → [x ↦ v]t


               t → t'
        ────────────────────── (E-TyApp)
        t [τ] → t' [τ]


        ──────────────────────────── (E-TyAppTyAbs)
        (Λα. t) [τ] → [α ↦ τ]t
```

## Church Encodings in System F

One of the most remarkable features of System F is that **all data types can be encoded** using only functions and universal quantification!

### Booleans

```
CBool = ∀A. A → A → A

true = ΛA. λt:A. λf:A. t
false = ΛA. λt:A. λf:A. f

not = λb:CBool. ΛA. λt:A. λf:A. b [A] f t
and = λb1:CBool. λb2:CBool. ΛA. λt:A. λf:A. b1 [A] (b2 [A] t f) f
```

### Natural Numbers

```
CNat = ∀A. (A → A) → A → A

zero = ΛA. λf:A→A. λx:A. x
succ = λn:CNat. ΛA. λf:A→A. λx:A. f (n [A] f x)

plus = λm:CNat. λn:CNat. ΛA. λf:A→A. λx:A. m [A] f (n [A] f x)
mult = λm:CNat. λn:CNat. ΛA. λf:A→A. m [A] (n [A] f)
```

### Pairs

```
Pair A B = ∀C. (A → B → C) → C

pair = ΛA. ΛB. λa:A. λb:B. ΛC. λf:A→B→C. f a b
fst = ΛA. ΛB. λp:Pair A B. p [A] (λa:A. λb:B. a)
snd = ΛA. ΛB. λp:Pair A B. p [B] (λa:A. λb:B. b)
```

### Lists

```
List A = ∀R. (A → R → R) → R → R

nil = ΛA. ΛR. λc:A→R→R. λn:R. n
cons = ΛA. λh:A. λt:List A. ΛR. λc:A→R→R. λn:R. c h (t [R] c n)

map = ΛA. ΛB. λf:A→B. λlist:List A.
  list [List B]
    (λa:A. λrest:List B. cons [B] (f a) rest)
    (nil [B])
```

## Parametric Polymorphism

**Parametricity Theorem** (Reynolds): Polymorphic functions cannot inspect type arguments.

**Example**: A function of type `∀A. A → A` **must** be the identity function!

**Proof sketch**: The function cannot know what `A` is, so it cannot create new values of type `A`. It can only return the input.

This gives us "theorems for free" - just from the type signature, we know what the function must do.

## Properties

### Undecidability of Type Inference

**Theorem**: Type inference for System F is **undecidable** (Wells, 1999).

This means we cannot automatically infer types in general—we need type annotations.

### Strong Normalization

**Theorem**: All well-typed System F terms **terminate**.

**Proof**: Uses **logical relations** and **reducibility predicates**.

### Type Safety

**Theorem (Progress)**: Well-typed terms are either values or can step.

**Theorem (Preservation)**: Types are preserved under evaluation.

## Examples

### Polymorphic Identity

```
id = ΛA. λx:A. x
id : ∀A. A → A

-- Use at Bool
id [Bool] true → true

-- Use at Nat
id [Nat] 0 → 0
```

### Polymorphic Composition

```
compose = ΛA. ΛB. ΛC.
  λf:B→C. λg:A→B. λx:A. f (g x)

compose : ∀A. ∀B. ∀C. (B→C) → (A→B) → A → C
```

### Self-Application

Unlike untyped lambda calculus, `λx. x x` **cannot be typed** in System F!

### Church Numerals Example

```
three = ΛA. λf:A→A. λx:A. f (f (f x))

addOne = λn:Nat. succ n

three [Nat] addOne 0 → succ (succ (succ 0))
```

## Comparison with Hindley-Milner

| Aspect | Hindley-Milner | System F |
|--------|----------------|----------|
| Let polymorphism | ✓ | ✓ |
| Lambda polymorphism | ✗ | ✓ |
| First-class polymorphism | ✗ | ✓ |
| Type inference | Decidable | Undecidable |
| Explicit types | Optional | Required |
| Impredicative types | Limited | Full |

**Impredicativity**: In System F, we can instantiate `∀A. τ` with **another polymorphic type**, like `∀B. B → B`.

## Implementation

### Building and Testing

```bash
stack init
stack build
stack test
```

### Usage Example

```haskell
import Syntax
import TypeCheck
import Eval
import Parser

-- Parse polymorphic identity
let Right polyId = parseTerm "/\\A. \\x:A. x"

-- Type check
let Right ty = typeCheck polyId
-- ty = TyForall "A" (TyArr (TyVar "A") (TyVar "A"))

-- Apply to Bool
let Right term = parseTerm "(/\\A. \\x:A. x) [Bool] true"
eval term  -- → TmTrue
```

## Real-World Connections

System F's explicit polymorphism influences generics in Java, C#, TypeScript, and Rust. While no mainstream language implements pure System F, its ideas are everywhere.

### Where You've Seen This

#### **Java Generics**
```java
// Explicit type parameters (like System F type abstraction)
public <T> T identity(T x) { return x; }     // ΛT. λx:T. x

// Type application at call site
String s = identity<String>("hello");        // (Not required, inferred)
Integer n = identity<Integer>(42);
```

#### **C# Generics**
```csharp
// Similar to System F
public T Identity<T>(T x) => x;              // ΛT. λx:T. x

// Constraints (bounded quantification)
public T Max<T>(T a, T b) where T : IComparable<T>
```

#### **TypeScript**
```typescript
// Explicit type parameters
function identity<T>(x: T): T { return x; }  // ΛT. λx:T. x

// Type application
const n = identity<number>(5);               // identity [number] 5
```

#### **Rust**
```rust
// Explicit generics
fn identity<T>(x: T) -> T { x }              // ΛT. λx:T. x

// Trait bounds (type classes)
fn max<T: Ord>(a: T, b: T) -> T { ... }
```

### Church Encodings in Practice

**System F theory** influences how we think about data:

```typescript
// Option type (Church-encoded)
type Option<T> = <R>(none: R, some: (x: T) => R) => R;

const none = <T>(): Option<T> =>
  <R>(n: R, s: (x: T) => R) => n;

const some = <T>(x: T): Option<T> =>
  <R>(n: R, s: (x: T) => R) => s(x);
```

### Parametricity in Real Languages

**Free theorems** guide API design:

```typescript
// f : <T>(xs: T[]) => T[]
// By parametricity: f can only rearrange/duplicate/drop elements!
// Cannot: modify elements, inspect values

// Examples:
reverse    // ✓ Valid
filter     // ✗ Needs predicate
map        // ✗ Needs function
```

### Key Concept Mappings

| System F Concept | Real-World Feature |
|------------------|-------------------|
| **Type abstraction** `ΛT. t` | Generic methods `<T>` |
| **Type application** `t [τ]` | Type parameters (often inferred) |
| **Parametricity** | Generic constraints, free theorems |
| **Church encoding** | Visitor pattern, fold |
| **Existentials** | Abstract types, interfaces |

### Why System F Matters

1. **Generics**: Foundation for Java/C#/TypeScript generics
2. **Type safety**: Parametricity prevents bugs
3. **Abstraction**: Existentials enable data hiding
4. **Theory**: Understanding limits of type systems

## References

### Foundational Papers

1. **Girard, Jean-Yves** (1972). "Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur." PhD thesis, Université Paris VII.
   Independent discovery of System F.
   [Google Scholar](https://scholar.google.com/scholar?cluster=11981351871779498521)

2. **Reynolds, John C.** (1974). "Towards a Theory of Type Structure." *Programming Symposium*.
   Independent discovery, connection to polymorphism.
   [SpringerLink](https://link.springer.com/chapter/10.1007/3-540-06859-7_148) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=3983577454773522827)

3. **Reynolds, John C.** (1983). "Types, Abstraction and Parametric Polymorphism." *IFIP*.
   Parametricity theorem and "theorems for free".
   [Google Scholar](https://scholar.google.com/scholar?cluster=9268645497659309771)

4. **Wadler, Philip** (1989). "Theorems for Free!" *FPCA*.
   Accessible presentation of parametricity.
   [ACM DL](https://dl.acm.org/doi/10.1145/99370.99404) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=15441729363503280111)

### Type Inference

5. **Wells, J. B.** (1999). "Typability and Type Checking in System F are Equivalent and Undecidable." *Annals of Pure and Applied Logic*.
   Proves undecidability of type inference.
   [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0168007298000475) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=10784276429625502641)

6. **Dunfield, Joshua and Krishnaswami, Neelakantan** (2013). "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism." *ICFP*.
   Practical bidirectional type checking.
   [ACM DL](https://dl.acm.org/doi/10.1145/2500365.2500582) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=2231098294608551327)

### Books

7. **Girard, Jean-Yves; Lafont, Yves; Taylor, Paul** (1989). *Proofs and Types*. Cambridge University Press.
   Deep dive into System F and proof theory.
   [PDF](http://www.paultaylor.eu/stable/Proofs+Types.html) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=3529429395025772879)

8. **Pierce, Benjamin C.** (2002). *Types and Programming Languages*. MIT Press.
   Chapter 23: Universal Types. Chapter 24: Existential Types.
   [MIT Press](https://www.cis.upenn.edu/~bcpierce/tapl/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=2853553209915529600)

### Advanced Topics

9. **Boehm, Hans-J.** (1985). "Partial Polymorphic Type Inference is Undecidable." *FOCS*.
   Even partial type inference is hard.
   [IEEE](https://ieeexplore.ieee.org/document/4568156) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=13954903279890373519)

10. **Cardelli, Luca and Wegner, Peter** (1985). "On Understanding Types, Data Abstraction, and Polymorphism." *ACM Computing Surveys*.
    Classic survey on polymorphism.
    [ACM DL](https://dl.acm.org/doi/10.1145/6041.6042) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=2892005929822900967)

## Exercises

1. Implement Church-encoded lists with map and fold
2. Prove parametricity for `∀A. A → A`
3. Add existential types (∃α. τ)
4. Implement bidirectional type checking
5. Add local type inference (partial annotations)
6. Encode recursive types using iso-recursive approach
7. Implement Church-encoded trees
8. Add kind checking for higher-kinded types (preview of Chapter 6)

## Next Steps

**Chapter 6** (System F-omega) adds **type operators** and a **kind system**, allowing types to be parameterized by other types.

**Chapter 7-8** introduce **dependent types**, where types can depend on *values*, not just other types.
