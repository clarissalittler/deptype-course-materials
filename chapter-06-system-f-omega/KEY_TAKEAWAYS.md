# Chapter 6: Key Takeaways

## The Big Picture

**System F-omega adds type-level computation.** Types can now take type arguments (higher-kinded types), enabling abstraction over type constructors like `List`, `Maybe`, and `Functor`.

---

## Core Concepts

### 1. Kinds: Types of Types
```
*           - kind of proper types (Nat, Bool)
* → *       - kind of type constructors (List, Maybe)
* → * → *   - kind of binary type constructors (Either, Pair)
```

Just as types classify terms, **kinds classify types**.

### 2. Type Operators
```
List : * → *
Maybe : * → *
Either : * → * → *
```

Type constructors take type arguments and return types.

### 3. Type-Level Lambda (Λ at type level)
```
Pair = λα:*. λβ:*. α × β
```

We can define type functions that compute new types!

### 4. Higher-Kinded Polymorphism
```
∀F:(* → *). ∀α:*. F α → F α
```

We can abstract over type constructors themselves.

---

## Most Important Rules

### Kinding Judgment
```
Δ ⊢ τ :: κ
```
"In type context Δ, type τ has kind κ"

### K-TyLam (Type-Level Lambda)
```
Δ, α::κ₁ ⊢ τ :: κ₂
─────────────────────────
Δ ⊢ λα::κ₁. τ :: κ₁ → κ₂
```

### K-TyApp (Type-Level Application)
```
Δ ⊢ τ₁ :: κ₁ → κ₂    Δ ⊢ τ₂ :: κ₁
──────────────────────────────────
Δ ⊢ τ₁ τ₂ :: κ₂
```

---

## What You Should Be Able To Do

After this chapter, you should be able to:

- [ ] Assign kinds to type constructors
- [ ] Write type operators using type-level lambdas
- [ ] Abstract over type constructors (like `List`, `Maybe`)
- [ ] Understand Functor, Applicative, Monad at the type level
- [ ] Encode type-level natural numbers

---

## Key Examples

### Functor Signature
```
Functor : (* → *) → *
Functor F = ∀α. ∀β. (α → β) → F α → F β
```

### Type-Level Identity
```
Id = λα:*. α
Id Nat = Nat
```

### Type-Level Composition
```
Compose = λF:(* → *). λG:(* → *). λα:*. F (G α)
Compose List Maybe = λα. List (Maybe α)
```

### Church Numerals at Kind Level
```
Zero = λF:(* → *). λα:*. α
One  = λF:(* → *). λα:*. F α
Two  = λF:(* → *). λα:*. F (F α)
```

---

## Common Pitfalls

1. **Confusing types and kinds**: `Nat : *` but `List : * → *`
2. **Forgetting kind annotations**: Type lambdas need kind annotations
3. **Kind mismatch**: `List Nat Nat` is ill-kinded (List takes 1 arg)
4. **Mixing term and type levels**: λ vs Λ at term level, λ at type level

---

## The Kind Hierarchy

```
Terms : Types : Kinds
  5   :  Nat  :  *
  id  : ∀α.α→α : *
 List : * → * : □ (the "kind of kinds")
```

F-omega stops at kinds. Dependent types (Chapter 7+) collapse this hierarchy.

---

## Connection to Next Chapter

Chapter 7 introduces **Dependent Types**:
- Types can depend on values: `Vec n α`
- Terms and types unified into one syntax
- Curry-Howard correspondence becomes explicit

The distinction between types and kinds begins to blur.

---

## One-Sentence Summary

> System F-omega adds kinds and type-level computation, letting us abstract over type constructors and write truly generic code at the type level.
