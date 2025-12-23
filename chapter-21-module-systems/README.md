# Chapter 21: Module Systems

This chapter implements a module system for organizing and structuring large programs. Module systems provide:
- **Encapsulation**: Hide implementation details behind interfaces (signatures)
- **Parameterization**: Create reusable, parameterized modules (functors)
- **Abstraction**: Define abstract types whose implementation is hidden
- **Composition**: Build complex modules from simpler ones

## Overview

Our module system includes:
- **Structures** (`struct ... end`): Concrete module definitions with values, types, and nested modules
- **Signatures** (`sig ... end`): Module types that specify required components
- **Functors** (`functor(X : S) => M`): Parameterized modules (functions from modules to modules)
- **Module Application** (`F(M)`): Instantiate a functor with a module argument
- **Sealing** (`M :> S`): Restrict a module to a signature, hiding extra components

## Core Concepts

### 1. Structures

A structure is a concrete module containing declarations:

```ocaml
struct
  type t = Nat
  val x : t = 5
  val y : Bool = true
end
```

Structures can contain:
- **Value declarations**: `val x : τ = t`
- **Type declarations**: `type t = τ` (manifest) or `type t` (abstract)
- **Module declarations**: `module M = ...`

### 2. Signatures

A signature specifies what a module must provide:

```ocaml
sig
  type t
  val x : t
  val y : Bool
end
```

Signatures contain specifications:
- **Value specs**: `val x : τ`
- **Type specs**: `type t` (abstract) or `type t = τ` (manifest)
- **Module specs**: `module M : S`

### 3. Signature Matching

A module `M` matches signature `S` (written `M <: S`) if:
- Every value spec in `S` has a matching value in `M` with the same type
- Every type spec in `S` has a matching type in `M`
  - Abstract type specs (`type t`) match any type definition
  - Manifest type specs (`type t = τ`) require exact type equality
- Every module spec in `S` has a matching module in `M`
- `M` may have **additional** components not mentioned in `S` (width subtyping)

Example:
```ocaml
-- This module:
struct
  type t = Nat
  val x : t = 5
  val y : Bool = true
end

-- Matches this signature:
sig
  type t
  val x : t
end

-- Because it provides everything required (and more)
```

### 4. Functors

Functors are parameterized modules - functions from modules to modules:

```ocaml
functor(X : sig val n : Nat end) =>
  struct
    val m : Nat = succ X.n
    val doubled : Nat = succ (succ X.n)
  end
```

Apply a functor to a module:
```ocaml
(F)(M)  -- Apply functor F to module M
```

### 5. Sealing (Signature Ascription)

Sealing restricts a module to a signature, hiding extra components:

```ocaml
(struct
  type t = Nat
  val x : t = 5
  val secret : Nat = 42
end :> sig
  type t
  val x : t
end)
```

After sealing:
- `secret` is hidden
- Type `t` becomes abstract (its definition `Nat` is hidden)

## Typing Rules

### Structure Typing

```
Γ ⊢ d₁ : spec₁ ~> Γ₁
Γ₁ ⊢ d₂ : spec₂ ~> Γ₂
...
Γₙ₋₁ ⊢ dₙ : specₙ ~> Γₙ
─────────────────────────────────
Γ ⊢ struct d₁ ... dₙ end : sig spec₁ ... specₙ end
```

Each declaration:
1. Type checks under the extended context from previous declarations
2. Produces a specification
3. Extends the context for subsequent declarations

### Value Declaration

```
Γ ⊢ t : τ'    τ = τ'
────────────────────────────
Γ ⊢ val x : τ = t : val x : τ ~> Γ, x : τ
```

### Type Declaration

Manifest (concrete) type:
```
────────────────────────────────────
Γ ⊢ type t = τ : type t = τ ~> Γ, t = τ
```

Abstract type:
```
────────────────────────────────
Γ ⊢ type t : type t ~> Γ, t
```

### Module Variable

```
Γ(M) = S
────────────
Γ ⊢ M : S
```

### Functor

```
Γ, X : S₁ ⊢ M : S₂
────────────────────────────────────
Γ ⊢ functor(X : S₁) => M : S₁ → S₂
```

### Functor Application

```
Γ ⊢ F : S₁ → S₂
Γ ⊢ M : S₃
S₃ <: S₁
──────────────────
Γ ⊢ F(M) : S₂
```

The argument module `M` must match the functor's parameter signature.

### Sealing

```
Γ ⊢ M : S₁
S₁ <: S₂
──────────────────
Γ ⊢ (M :> S₂) : S₂
```

Sealing strengthens the type by restricting visible components.

### Signature Matching (Subtyping)

```
sig spec₁ ... specₙ ... specₘ end <: sig spec₁ ... specₙ end
```

Width subtyping: more specifications implies subtype.

For each specification:

**Values**:
```
val x : τ  in  impl
───────────────────────────
impl <: sig val x : τ end
```

**Abstract types**:
```
type t  or  type t = τ  in  impl
─────────────────────────────────
impl <: sig type t end
```

**Manifest types**:
```
type t = τ  in  impl
─────────────────────────────
impl <: sig type t = τ end
```

**Modules**:
```
module M : S₁  in  impl    S₁ <: S₂
────────────────────────────────────
impl <: sig module M : S₂ end
```

## Examples

### Example 1: Basic Structure

```ocaml
struct
  val x : Nat = 5
  val y : Nat = succ x
end
```

Signature: `sig val x : Nat; val y : Nat end`

### Example 2: Abstract Types

```ocaml
struct
  type counter = Nat
  val zero : counter = 0
  val increment : counter -> counter = \c:counter. succ c
end
```

Can be sealed to hide the implementation:
```ocaml
(... :> sig
  type counter
  val zero : counter
  val increment : counter -> counter
end)
```

Now `counter` is abstract - clients can't know it's `Nat`.

### Example 3: Simple Functor

```ocaml
functor(X : sig val n : Nat end) =>
  struct
    val double : Nat = succ (succ X.n)
  end
```

Apply to a module:
```ocaml
(F)(struct val n : Nat = 5 end)
-- Results in: struct val double : Nat = 10 end
```

### Example 4: Functor Composition

```ocaml
-- Increment functor
functor(X : sig val n : Nat end) =>
  struct val m : Nat = succ X.n end

-- Double functor
functor(Y : sig val n : Nat end) =>
  struct val m : Nat = succ (succ Y.n) end

-- Compose them:
(Double)((Inc)(struct val n : Nat = 5 end))
```

### Example 5: Nested Modules

```ocaml
struct
  module Math = struct
    val add : Nat -> Nat -> Nat = ...
    val mult : Nat -> Nat -> Nat = ...
  end

  module Utils = struct
    val isEven : Nat -> Bool = ...
  end

  val result : Nat = Math.add 3 5
end
```

## Real-World Applications

### 1. Standard ML Modules

SML has a sophisticated module system with structures, signatures, and functors:

```sml
signature ORDERED = sig
  type t
  val compare : t * t -> order
end

structure IntOrdered : ORDERED = struct
  type t = int
  val compare = Int.compare
end

functor SetFn(Elem : ORDERED) = struct
  (* Set implementation parameterized by element type *)
end
```

### 2. OCaml Modules

OCaml extends SML's modules with:
- First-class modules
- Module type inference
- Applicative functors

```ocaml
module type COMPARABLE = sig
  type t
  val compare : t -> t -> int
end

module Make(Ord : COMPARABLE) = struct
  type elem = Ord.t
  (* ... *)
end
```

### 3. Rust Traits and Modules

Rust combines modules with trait-based generics:

```rust
mod math {
    pub trait Numeric {
        fn add(self, other: Self) -> Self;
    }

    pub fn double<T: Numeric>(x: T) -> T {
        x.add(x)
    }
}
```

### 4. Haskell Type Classes

While not modules, type classes provide similar abstraction:

```haskell
class Eq a where
  (==) :: a -> a -> Bool

instance Eq Int where
  x == y = ...
```

### 5. Java/C# Interfaces

Object-oriented interfaces are a limited form of signatures:

```java
interface Collection<E> {
    void add(E element);
    int size();
}

class ArrayList<E> implements Collection<E> {
    // Implementation
}
```

## Key Insights

### Encapsulation

Modules let you hide implementation details:
- Define abstract types whose representation is hidden
- Expose only the interface clients need
- Change implementation without breaking clients

### Parameterization

Functors enable code reuse:
- Write generic data structures once
- Instantiate with different element types
- Type-safe polymorphism

### Large-Scale Structure

Module systems scale to large programs:
- Organize code into logical units
- Manage dependencies explicitly
- Separate interface from implementation

### Phase Distinction

Module systems often have a **phase distinction**:
- **Compile time**: Module signatures are checked
- **Run time**: Module bodies are linked and executed

This enables:
- Separate compilation
- Type-safe linking
- Optimizations based on signatures

## Comparison with Other Mechanisms

| Feature | Modules | Objects | Type Classes |
|---------|---------|---------|--------------|
| Encapsulation | Yes (sealing) | Yes (private) | Limited |
| Parameterization | Yes (functors) | No | Yes (instances) |
| Multiple implementations | Yes | Yes (subtyping) | Yes |
| First-class | Sometimes | Yes | No |
| Type abstraction | Yes | Limited | No |
| Separate compilation | Yes | Sometimes | No |

## Advanced Topics

### Recursive Modules

Some languages support mutually recursive modules:

```ocaml
module rec A : SIG_A = struct
  (* Can reference B *)
end
and B : SIG_B = struct
  (* Can reference A *)
end
```

### First-Class Modules

OCaml allows modules as values:

```ocaml
let module M = (val m : S) in
  M.x
```

### Higher-Order Functors

Functors that take functors as arguments:

```ocaml
functor(F : functor(X : S₁) => S₂) =>
  functor(Y : S₃) =>
    F(Y)
```

### Dependent Types in Modules

More advanced systems (like Agda, Coq) integrate modules with dependent types:
- Module types can depend on values
- Enables very precise specifications

## Exercises

1. **Basic Structures**: Define a structure with values and types
2. **Signature Matching**: Check if structures match signatures
3. **Abstract Types**: Create an abstract stack type
4. **Simple Functors**: Write a functor that increments a counter
5. **Functor Composition**: Compose two functors
6. **Sealing**: Hide implementation details with signatures
7. **Nested Modules**: Build a module hierarchy
8. **Parameterized Data Structures**: Implement a generic list functor

## Further Reading

### Foundational Papers

1. **"A Module System for a Programming Language"** - MacQueen (1984)
   - Original ML modules
   - [Google Scholar](https://scholar.google.com/scholar?q=MacQueen+module+system+programming+language+1984)

2. **"A Modular Module System"** - Dreyer, Crary, Harper (2003)
   - Advanced module calculus
   - [Google Scholar](https://scholar.google.com/scholar?q=Dreyer+Crary+Harper+modular+module+system+2003)

3. **"F-ing Modules"** - Rossberg, Russo, Dreyer (2014)
   - Modules as first-class values
   - [Google Scholar](https://scholar.google.com/scholar?q=Rossberg+Russo+Dreyer+F-ing+modules+2014)

### Books

4. **"Types and Programming Languages"** - Pierce (2002)
   - Doesn't cover modules extensively but provides foundation

5. **"Advanced Topics in Types and Programming Languages"** - Pierce (2004)
   - Chapter on module systems

6. **"Practical Foundations for Programming Languages"** - Harper (2016)
   - Comprehensive treatment of modules

### Implementations

7. **Standard ML of New Jersey** - [smlnj.org](https://www.smlnj.org/)
   - Classic ML module system

8. **OCaml** - [ocaml.org](https://ocaml.org/)
   - Extended module system with first-class modules

9. **Agda** - [agda.readthedocs.io](https://agda.readthedocs.io/)
   - Modules in dependently typed setting

## Building and Running

```bash
# Build the project
stack build

# Run tests
stack test

# Run the REPL
stack run module-systems-repl

# Build with file watching
stack build --file-watch
```

## REPL Examples

```
modules> struct val x : Nat = 5 end
  : sig
      val x : Nat
    end

modules> :mod M = struct val x : Nat = 5 val y : Nat = 10 end
module M : sig
             val x : Nat
             val y : Nat
           end

modules> :mod Inc = functor(X : sig val n : Nat end) => struct val m : Nat = succ X.n end
module Inc : ...

modules> (Inc)(struct val n : Nat = 5 end)
  : sig
      val m : Nat
    end
```

## Summary

Module systems provide:
1. **Organization**: Structure large programs into manageable units
2. **Abstraction**: Hide implementation details behind interfaces
3. **Reuse**: Parameterize modules for generic programming
4. **Safety**: Type-check module interfaces separately

This chapter implements a core module system with structures, signatures, functors, and sealing - the essential features found in languages like ML and OCaml.
