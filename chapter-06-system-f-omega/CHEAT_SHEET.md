# Chapter 6: System F-omega (Higher-Kinded Types) - Cheat Sheet

## Key Idea

**Types can abstract over type constructors**, not just types.

## Kind System

```
κ ::= * | κ → κ          (kinds)

*           : kind of proper types (Nat, Bool, Nat → Bool)
* → *       : kind of type constructors (List, Maybe)
(* → *) → * : kind of higher-order type constructors (Functor, Monad)
```

## Syntax

```
τ ::= α | τ → τ | ∀α:κ. τ | λα:κ. τ | τ τ    (types)
t ::= x | λx:τ. t | t t | Λα:κ. t | t [τ]     (terms)
```

## Kinding Rules

```
α:κ ∈ Δ
─────────  (K-Var)
Δ ⊢ α : κ

Δ, α:κ₁ ⊢ τ : κ₂
────────────────────  (K-Abs)
Δ ⊢ λα:κ₁. τ : κ₁ → κ₂

Δ ⊢ τ₁ : κ₁ → κ₂    Δ ⊢ τ₂ : κ₁
───────────────────────────────  (K-App)
Δ ⊢ τ₁ τ₂ : κ₂
```

## Type-Level Computation

### Type-Level Lambda
```
List = λα:*. ...       : * → *
Maybe = λα:*. ...      : * → *
Either = λα:*. λβ:*. ... : * → * → *
```

### Type-Level Application
```
List Nat    : *
Maybe Bool  : *
Either Nat Bool : *
```

## Common Type Operators

### List
```
List : * → *
List = λα:*. μβ:*. Unit + (α × β)
```

### Functor (Type Class Encoding)
```
Functor : (* → *) → *
Functor = λF:* → *. ∀α:*. ∀β:*. (α → β) → F α → F β
```

### Monad
```
Monad : (* → *) → *
Monad = λM:* → *.
  { return : ∀α:*. α → M α
  , bind : ∀α:*. ∀β:*. M α → (α → M β) → M β
  }
```

## Real-World Connections

| F-omega Concept | Haskell | Scala | TypeScript |
|-----------------|---------|-------|------------|
| `* → *` | `* -> *` | `F[_]` | `F<T>` |
| Type lambdas | Type families | Type lambdas | Conditional types |
| Higher-kinded | Type classes | Higher-kinded types | Limited support |

### Haskell Example
```haskell
-- F-omega-style type operators
class Functor (f :: * -> *) where
  fmap :: (a -> b) -> f a -> f b

-- f has kind * -> *
instance Functor [] where
  fmap = map
```

### Scala Example
```scala
// Higher-kinded types
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}

// F has kind * -> *
implicit val listFunctor: Functor[List] = new Functor[List] {
  def map[A, B](fa: List[A])(f: A => B) = fa.map(f)
}
```

## Type-Level Functions

### Compose (Type Composition)
```
Compose : (* → *) → (* → *) → * → *
Compose = λF:* → *. λG:* → *. λα:*. F (G α)

-- Example
Compose List Maybe Nat  ≡  List (Maybe Nat)
```

### Const (Constant Type Function)
```
Const : * → * → *
Const = λα:*. λβ:*. α

-- Always returns first type
Const Nat Bool  ≡  Nat
```

## Remember

### ✓ Do
- Think about kinds (types of types)
- Use type-level abstraction for generic patterns
- Abstract over type constructors (not just types)

### ✗ Avoid
- Confusing types and kinds
- Applying type operators to wrong kinds

## Comparison

| System | Type Abstraction | Kind System |
|--------|------------------|-------------|
| **System F** | Over types (*) | No kinds |
| **F-omega** | Over type constructors | Yes (* and κ → κ) |

## Quick Reference

### Example: Generic Map
```
map : ∀F:* → *. ∀α:*. ∀β:*. (α → β) → F α → F β

-- Can work with any F : * → *
map [List] [Nat] [Bool] isZero [1, 2, 3]
map [Maybe] [Nat] [Bool] isZero (Just 5)
```

## Why F-omega Matters

1. **Type Classes**: Foundation for Haskell's type classes
2. **Generic Programming**: Abstract over containers
3. **Functors/Monads**: Proper encoding
4. **Type-Level Programming**: Powerful abstractions

## Next Steps

→ **Chapter 7**: Dependent types (types depend on *values*!)
