# Chapter 6: System F-omega (Fω)

## Overview

System F-omega extends System F with **higher-kinded types** - types that can take other types as parameters. While System F allows term-level polymorphism (terms abstracted over types), System F-omega adds **type-level polymorphism** (types abstracted over types).

This makes types first-class citizens in their own lambda calculus, complete with abstraction and application at the type level.

## Motivation

In System F, we can write polymorphic functions like identity:
```
id : ∀A::*. A → A
id = ΛA. λx:A. x
```

But we cannot abstract over type constructors like `List` or `Maybe`. In many real programs, we want to write functions that work over any type constructor:

```haskell
-- In Haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

Here, `f` is a type constructor of kind `* → *`. System F cannot express this - we need System F-omega.

## Syntax

### Kinds

Kinds classify types, just as types classify terms:

```
κ ::=                (kinds)
    *                base kind (kind of proper/inhabited types)
    κ₁ → κ₂          kind of type constructors
```

**Examples**:
- `Bool : *` - Bool is a proper type
- `List : * → *` - List takes a type and returns a type
- `Either : * → * → *` - Either takes two types and returns a type
- `Functor : (* → *) → *` - Functor takes a type constructor

### Types

Types now include type-level lambda and application:

```
τ ::=                (types)
    α                type variable
    τ₁ → τ₂          function type
    ∀α::κ. τ         universal quantification (with kind annotation)
    λα::κ. τ         type-level lambda (NEW!)
    τ₁ τ₂            type-level application (NEW!)
    Bool             boolean base type
    Nat              natural number base type
```

**Examples**:
- `λA::*. A` - identity type operator
- `λA::*. λB::*. A` - constant type operator
- `(λA::*. A → A) Bool` - normalizes to `Bool → Bool`

### Terms

Terms are similar to System F but with kinded type abstractions:

```
t ::=                (terms)
    x                variable
    λ(x:τ). t        term abstraction
    t₁ t₂            term application
    Λα::κ. t         type abstraction (now kinded)
    t [τ]            type application
    true | false     booleans
    if t₁ then t₂ else t₃
    0 | succ t | pred t | iszero t
```

## Kinding System

The kinding judgment `Γ ⊢ τ :: κ` means "under kind context Γ, type τ has kind κ".

### Kinding Rules

```
Γ(α) = κ
──────────── (K-Var)
Γ ⊢ α :: κ


Γ ⊢ τ₁ :: *    Γ ⊢ τ₂ :: *
──────────────────────────── (K-Arrow)
Γ ⊢ τ₁ → τ₂ :: *


Γ, α::κ₁ ⊢ τ :: *
──────────────────────── (K-Forall)
Γ ⊢ ∀α::κ₁. τ :: *


Γ, α::κ₁ ⊢ τ :: κ₂
─────────────────────────── (K-Lam)
Γ ⊢ λα::κ₁. τ :: κ₁ → κ₂


Γ ⊢ τ₁ :: κ₁ → κ₂    Γ ⊢ τ₂ :: κ₁
───────────────────────────────────── (K-App)
Γ ⊢ τ₁ τ₂ :: κ₂


──────────────── (K-Bool)
Γ ⊢ Bool :: *


─────────────── (K-Nat)
Γ ⊢ Nat :: *
```

### Kind Checking Algorithm

1. Start with empty kind context `∅`
2. When encountering `λα::κ. τ`, extend context with `α::κ` and check body
3. When encountering type application `τ₁ τ₂`:
   - Check `τ₁ :: κ₁ → κ₂`
   - Check `τ₂ :: κ₁`
   - Result has kind `κ₂`

## Type System

The typing judgment is now `Γ; Δ ⊢ t : τ` where:
- `Γ` is the kind context (maps type variables to kinds)
- `Δ` is the type context (maps term variables to types)

### Key Typing Rules

```
Γ; Δ, x:τ₁ ⊢ t : τ₂    Γ ⊢ τ₁ :: *
──────────────────────────────────── (T-Abs)
Γ; Δ ⊢ λ(x:τ₁). t : τ₁ → τ₂


Γ, α::κ; Δ ⊢ t : τ
────────────────────────── (T-TAbs)
Γ; Δ ⊢ Λα::κ. t : ∀α::κ. τ


Γ; Δ ⊢ t : ∀α::κ. τ₁    Γ ⊢ τ₂ :: κ
───────────────────────────────────── (T-TApp)
Γ; Δ ⊢ t [τ₂] : [α ↦ τ₂]τ₁
```

**Important**: When type-checking, types must be well-kinded. The rule T-Abs requires `Γ ⊢ τ₁ :: *`.

## Operational Semantics

### Type-Level Evaluation

Types form their own lambda calculus with beta-reduction:

```
(λα::κ. τ₁) τ₂ ⟶ [α ↦ τ₂]τ₁
```

**Example**:
```
(λA::*. λB::*. A → B) Bool Nat
⟶ (λB::*. Bool → B) Nat
⟶ Bool → Nat
```

### Term-Level Evaluation

Term evaluation is similar to System F:

```
(λ(x:τ). t) v ⟶ [x ↦ v]t

(Λα::κ. t) [τ] ⟶ [α ↦ τ]t
```

## Type-Level Programming

### Type Operators

**Identity**: `Id = λA::*. A`
- Kind: `* → *`
- `Id Bool` normalizes to `Bool`

**Const**: `Const = λA::*. λB::*. A`
- Kind: `* → * → *`
- `Const Bool Nat` normalizes to `Bool`

**Compose**: `Compose = λF::* → *. λG::* → *. λA::*. F (G A)`
- Kind: `(* → *) → (* → *) → * → *`
- Composes two type constructors

### Church Encodings at Type Level

**List Type Constructor**:
```
List = λA::*. ∀R::*. R → (A → R → R) → R
```

- `List : * → *`
- `List Bool : *`
- A list is encoded as its fold operation

**Maybe Type Constructor**:
```
Maybe = λA::*. ∀R::*. R → (A → R) → R
```

- `Maybe : * → *`
- Optional values encoded as Church pairs

**Either Type Constructor**:
```
Either = λA::*. λB::*. ∀R::*. (A → R) → (B → R) → R
```

- `Either : * → * → *`
- Sum types with two alternatives

## Theoretical Properties

### Strong Normalization

**Theorem**: All well-kinded types in System F-omega normalize (type-level evaluation terminates).

**Proof Sketch**: The kind system prevents self-application at the type level (like `(λA::*. A A)`), which would lead to non-termination.

### Decidable Kind Inference

**Theorem**: Given a type expression, we can algorithmically determine its kind (or report that it's ill-kinded).

This is similar to type inference for simply typed lambda calculus.

### Undecidable Type Inference

**Theorem** (Wells, 1999): Type inference for System F-omega (and System F) is undecidable.

Therefore, type annotations are necessary in practice.

### Type Safety

**Progress**: If `∅; ∅ ⊢ t : τ`, then either `t` is a value or there exists `t'` such that `t ⟶ t'`.

**Preservation**: If `Γ; Δ ⊢ t : τ` and `t ⟶ t'`, then `Γ; Δ ⊢ t' : τ`.

## Connection to Real Languages

### Haskell

Haskell's type system is based on System F-omega:

```haskell
-- Type classes work over type constructors
class Functor f where  -- f :: * → *
  fmap :: (a -> b) -> f a -> f b

-- Higher-kinded type variables
newtype Compose f g a = Compose (f (g a))
-- f :: * → *, g :: * → *, a :: *
```

### Scala

Scala supports higher-kinded types:

```scala
trait Functor[F[_]] {  // F is a type constructor
  def map[A, B](fa: F[A])(f: A => B): F[B]
}
```

### Rust (Limited)

Rust has limited support via associated types:

```rust
trait Functor {
    type F<A>;  // Associated type constructor
    fn map<A, B>(self: Self::F<A>, f: fn(A) -> B) -> Self::F<B>;
}
```

## Implementation

### Project Structure

```
chapter-06-system-f-omega/
├── src/
│   ├── Syntax.hs       -- AST with kinds and type operators
│   ├── TypeCheck.hs    -- Kinding and type checking
│   ├── Eval.hs         -- Type-level and term-level evaluation
│   ├── Parser.hs       -- Parser for extended syntax
│   └── Pretty.hs       -- Pretty printer
├── exercises/
│   ├── EXERCISES.md    -- Exercise descriptions
│   └── Solutions.hs    -- Complete solutions
├── test/
│   └── Spec.hs         -- 46 tests (all passing)
├── package.yaml
└── README.md           -- This file
```

### Building and Testing

```bash
# Build the project
stack build

# Run tests (46 examples, 0 failures)
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

-- Parse a type operator
let Right listType = parseType "/\\A::*. forall R::*. R -> (A -> R -> R) -> R"

-- Check its kind
kinding Map.empty listType  -- Right (* → *)

-- Apply it to Bool
let listBool = TyApp listType TyBool

-- Normalize
normalizeType listBool  -- ∀R::*. R → (Bool → R → R) → R
```

## Key Concepts

1. **Kinds**: Types for types - classify type expressions
2. **Higher-Kinded Types**: Types parameterized by type constructors
3. **Type Operators**: Functions at the type level (λα::κ. τ)
4. **Type-Level Application**: Applying type operators to types
5. **Kinding**: Ensures type expressions are well-formed
6. **Strong Normalization**: Type-level computation always terminates
7. **Type Constructor Polymorphism**: Abstract over `List`, `Maybe`, etc.

## Differences from System F

| Feature | System F | System F-omega |
|---------|----------|----------------|
| Type abstraction | `∀A. τ` | `∀A::κ. τ` (kinded) |
| Type operators | ❌ No | ✅ `λA::κ. τ` |
| Type application | ❌ Not at type level | ✅ `τ₁ τ₂` |
| Kinds | Implicit (*) | Explicit kind system |
| Type constructors | Built-in only | First-class |
| Higher-kinded polymorphism | ❌ No | ✅ Yes |

## Common Patterns

### Functor Pattern

While we can't encode type classes directly, we can express functor-like operations:

```
-- Type constructor
F : * → *

-- Map operation (for a specific F)
map : ∀A::*. ∀B::*. (A → B) → F A → F B
```

### Type-Level Computation

```
-- If-then-else at type level
IfThenElse = λC::*. λT::*. λF::*. C T F

-- With Church booleans:
TrueType = λT::*. λF::*. T
FalseType = λT::*. λF::*. F

-- Example:
IfThenElse TrueType Bool Nat ⟶ Bool
```

## Exercises

See [EXERCISES.md](exercises/EXERCISES.md) for detailed exercises including:

1. **Basic Type Operators** - Identity, Const, Compose
2. **List Type Constructor** - Church-encoded lists
3. **Maybe Type Constructor** - Optional values
4. **Either Type Constructor** - Sum types
5. **Type-Level Church Encodings** - Booleans and conditionals
6. **Advanced Type Operators** - Flip, Twice, and more

Complete solutions in [exercises/Solutions.hs](exercises/Solutions.hs).

## Real-World Connections

System F-omega's higher-kinded types are the foundation for Haskell's type classes, Scala's type system, and advanced TypeScript features.

### Where You've Seen This

#### **Haskell (Native Higher-Kinded Types)**
```haskell
-- Type classes abstract over type constructors
class Functor (f :: * -> *) where
  fmap :: (a -> b) -> f a -> f b

-- f has kind * -> *, not kind *
instance Functor [] where
  fmap = map

instance Functor Maybe where
  fmap = ...
```

#### **Scala (Higher-Kinded Types)**
```scala
// F[_] means F has kind * -> *
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}

// Concrete instances
implicit val listFunctor: Functor[List] = ...
implicit val optionFunctor: Functor[Option] = ...
```

#### **TypeScript (Limited Support)**
```typescript
// TypeScript doesn't have true higher-kinded types
// But conditional types provide some power
type ReturnType<T extends (...args: any) => any> =
  T extends (...args: any) => infer R ? R : any;
```

### Key Concepts

| F-omega | Haskell | Scala | Real Impact |
|---------|---------|-------|-------------|
| Kind `*` | Proper types | Regular types | `Int`, `String` |
| Kind `* → *` | Type constructors | `F[_]` | `List`, `Maybe`, `Option` |
| Type-level λ | Type families | Type lambdas | Generic abstractions |
| Kinding | Kind checking | Kind inference | Type safety at type level |

### Why F-omega Matters

1. **Type Classes**: Haskell's Functor, Monad, etc.
2. **Generic Collections**: Abstract over `List`, `Option`, `Either`
3. **Type-Safe APIs**: Enforce correct usage at compile time
4. **Category Theory**: Proper encoding of functors, monads

## References

### Foundational Papers

1. **Girard, Jean-Yves** (1972). "Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur." PhD thesis, Université Paris VII.
   Original presentation of System F-omega.
   [Google Scholar](https://scholar.google.com/scholar?cluster=11981351871779498521)

2. **Reynolds, John C.** (1985). "Three Approaches to Type Structure." *Mathematical Foundations of Software Development*.
   Alternative presentation of F-omega.
   [SpringerLink](https://link.springer.com/chapter/10.1007/3-540-15198-2_7) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=14937629694168523507)

3. **Barendregt, Henk** (1992). "Lambda Calculi with Types." *Handbook of Logic in Computer Science*, Vol. 2.
   Comprehensive treatment covering System F, F-omega, and beyond.
   [Google Scholar](https://scholar.google.com/scholar?cluster=11654927772893943213)

4. **Mitchell, John C.** (1996). *Foundations for Programming Languages*. MIT Press.
   Chapter 11: Higher-Order Type Systems.
   [Google Scholar](https://scholar.google.com/scholar?cluster=2908587526117199295)

### Applications

5. **Jones, Mark P.; Peyton Jones, Simon; Meijer, Erik** (1997). "Type Classes: An Exploration of the Design Space." *Haskell Workshop*.
   Shows how Haskell's type classes relate to F-omega.
   [Google Scholar](https://scholar.google.com/scholar?cluster=16289167170168545720)

6. **Pierce, Benjamin C.** (2002). *Types and Programming Languages*. MIT Press.
   Chapter 30: Higher-Order Polymorphism.
   [MIT Press](https://www.cis.upenn.edu/~bcpierce/tapl/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=2853553209915529600)

7. **Wadler, Philip; Blott, Stephen** (1989). "How to Make Ad-hoc Polymorphism Less Ad Hoc." *POPL*.
   Type classes in Haskell. Shows practical use of higher-kinded types.
   [ACM DL](https://dl.acm.org/doi/10.1145/75277.75283) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=4466886255570393883)

### Modern Perspectives

8. **Yallop, Jeremy; White, Leo** (2014). "Lightweight Higher-Kinded Polymorphism." *FLOPS*.
   Encoding higher-kinded types in ML.
   [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-319-07151-0_8) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=2107896892396454966)

9. **Chakravarty, Manuel M. T. et al.** (2005). "Associated Types with Class." *POPL*.
   Extension of type classes.
   [ACM DL](https://dl.acm.org/doi/10.1145/1040305.1040306) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=11507021098888180095)

10. **Eisenberg, Richard A.** (2016). "Dependent Types in Haskell: Theory and Practice." PhD Thesis, University of Pennsylvania.
    Connection between F-omega and dependent types.
    [UPenn](https://www.cis.upenn.edu/~sweirich/papers/eisenberg-thesis.pdf) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=16153728211248108959)

## Next Chapter

In [Chapter 7](../chapter-07-simply-typed-dependent-calculus), we take the next major step: **dependent types**, where types can depend on *values*, not just other types. This allows us to express properties like "a vector of length n" directly in the type system.

System F-omega gives us:
- **Type-level abstraction**: `∀A::κ. ...`
- **Type operators**: types depending on types

Dependent types will give us:
- **Value-level dependency**: `∀(n:Nat). Vector n`
- **Propositions as types**: proofs as programs

This progression from λ-calculus → System F → F-omega → Dependent Types shows the increasing expressiveness of type systems!
