# Chapter 7: Dependent Types - Cheat Sheet

## Key Idea

**Types can depend on values!** Function return types can vary based on argument values.

## Syntax (Unified Terms & Types)

```
t ::= x | λx:t. t | t t | Π(x:t). t | Σ(x:t). t | Type | ...

Everything is a term (including types)!
```

## Π Types (Dependent Functions)

### Syntax
```
Π(x:A). B    where B may depend on x
```

### Non-Dependent Case
```
Π(x:A). B  ≡  A → B    (when B doesn't use x)
```

### Examples
```
-- Vector constructor
vec : Π(n:Nat). Type → Type
vec n A = "vector of length n with elements of type A"

-- Safe head
head : Π(n:Nat). Π(A:Type). Vec (succ n) A → A
```

## Σ Types (Dependent Pairs)

### Syntax
```
Σ(x:A). B    where B may depend on x
```

### Non-Dependent Case
```
Σ(x:A). B  ≡  A × B    (when B doesn't use x)
```

### Examples
```
-- Existential package
package : Σ(n:Nat). Vec n Nat
package = (3, [1, 2, 3])

-- Dependent record
DependentPair : Type
DependentPair = Σ(A:Type). A
```

## Type Checking

### Π-Type
```
Γ ⊢ A : Type    Γ, x:A ⊢ B : Type
────────────────────────────────────
Γ ⊢ Π(x:A). B : Type
```

### Σ-Type
```
Γ ⊢ A : Type    Γ, x:A ⊢ B : Type
────────────────────────────────────
Γ ⊢ Σ(x:A). B : Type
```

## Common Patterns

### Length-Indexed Vectors
```
Vec : Nat → Type → Type

Vec 0 A = Unit
Vec (succ n) A = A × Vec n A

-- Or as inductive type:
data Vec (A : Type) : Nat → Type where
  nil : Vec A 0
  cons : Π(n:Nat). A → Vec A n → Vec A (succ n)
```

### Safe List Operations
```
-- head that can't fail
head : Π(n:Nat). Π(A:Type). Vec (succ n) A → A

-- tail that preserves length
tail : Π(n:Nat). Π(A:Type). Vec (succ n) A → Vec n A

-- append that sums lengths
append : Π(m n:Nat). Π(A:Type). Vec m A → Vec n A → Vec (m + n) A
```

## Normalization-Based Equality

```
Terms are equal if they normalize to the same value:

t₁ ≡ t₂  iff  norm(t₁) = norm(t₂)
```

## Real-World Examples

### Idris
```idris
-- Safe array indexing
index : Fin n -> Vect n a -> a

-- Type-level addition
(++) : Vect m a -> Vect n a -> Vect (m + n) a
```

### Agda
```agda
-- Sorted lists
data Sorted : List ℕ → Set where
  nil : Sorted []
  single : (x : ℕ) → Sorted (x ∷ [])
  cons : (x y : ℕ) → x ≤ y → Sorted (y ∷ ys) → Sorted (x ∷ y ∷ ys)
```

## Remember

### ✓ Do
- Use Π for functions where return type depends on argument
- Use Σ for pairs where second type depends on first value
- Normalize terms to check equality
- Encode invariants in types

### ✗ Avoid
- Confusing value-level and type-level
- Forgetting that types are terms too
- Non-terminating functions (breaks type checking!)

## Comparison

| Feature | System F | Dependent Types |
|---------|----------|-----------------|
| Types depend on | Types | Values |
| Function types | `∀α. τ → τ` | `Π(x:A). B` |
| Pair types | `∀α. α × β` | `Σ(x:A). B` |
| Power | Polymorphism | Verification |

## Common Encodings

### Natural Numbers
```
Nat : Type
zero : Nat
succ : Nat → Nat
```

### Booleans
```
Bool : Type
true : Bool
false : Bool
```

### Equality
```
Eq : Π(A:Type). A → A → Type
refl : Π(A:Type). Π(x:A). Eq A x x
```

## Quick Reference

### Example: Safe Division
```
-- Division that requires non-zero divisor
div : Π(m:Nat). Π(n:Nat). (n ≠ 0) → Nat
```

### Example: Dependent Record
```
Record : Type
Record = Σ(A:Type). Σ(x:A). Eq A x x
```

## Why Dependent Types Matter

1. **Correctness**: Prove properties at compile-time
2. **No Runtime Errors**: Type system guarantees safety
3. **Verified Code**: CompCert C compiler
4. **Mathematics**: Formalize proofs

## Next Steps

→ **Chapter 8**: Universe hierarchy, equality types, full dependent types
