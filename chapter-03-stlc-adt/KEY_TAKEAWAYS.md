# Chapter 3: Key Takeaways

## The Big Picture

**Algebraic Data Types (ADTs) let us model real data.** Products combine data ("and"), sums offer choices ("or"), and pattern matching extracts data safely.

---

## Core Concepts

### 1. Product Types (Pairs, Records)
```
τ₁ × τ₂    - pair of τ₁ AND τ₂
⟨t₁, t₂⟩   - pair constructor
fst p      - extract first component
snd p      - extract second component
```

**Intuition**: A product holds multiple values simultaneously.

### 2. Sum Types (Variants, Unions)
```
τ₁ + τ₂           - either τ₁ OR τ₂
inl t : τ₁ + τ₂   - inject left
inr t : τ₁ + τ₂   - inject right
case t of inl x => ... | inr y => ...
```

**Intuition**: A sum holds one of several possible values.

### 3. Pattern Matching
```
case x of
  inl a => handleLeft a
| inr b => handleRight b
```

Pattern matching is:
- **Exhaustive**: Must cover all cases
- **Safe**: Type system ensures correct handling
- **Compositional**: Patterns can nest

### 4. The Algebra of Types
```
A × B  ≈  A and B  ≈  multiplication
A + B  ≈  A or B   ≈  addition
A → B  ≈  B^A      ≈  exponentiation
Unit   ≈  1
Void   ≈  0
```

Types follow algebraic laws! `A × (B + C) ≅ (A × B) + (A × C)`

---

## Most Important Rules

### T-Pair
```
Γ ⊢ t₁ : τ₁    Γ ⊢ t₂ : τ₂
───────────────────────────
Γ ⊢ ⟨t₁, t₂⟩ : τ₁ × τ₂
```

### T-Case
```
Γ ⊢ t : τ₁ + τ₂
Γ, x:τ₁ ⊢ t₁ : τ
Γ, y:τ₂ ⊢ t₂ : τ
────────────────────────────────────────────
Γ ⊢ case t of inl x => t₁ | inr y => t₂ : τ
```

Note: Both branches must return the **same type** τ.

---

## What You Should Be Able To Do

After this chapter, you should be able to:

- [ ] Define custom data types using products and sums
- [ ] Write functions using pattern matching
- [ ] Check exhaustiveness of pattern matches
- [ ] Encode common types: Option, Either, List, Tree
- [ ] Understand the algebra of types

---

## Common Pitfalls

1. **Branches with different types**: Both case branches must have the same type
2. **Non-exhaustive patterns**: Must handle all constructors
3. **Forgetting type annotations on injections**: `inl 5` needs annotation `inl 5 : Nat + Bool`
4. **Nested patterns**: Require nested case expressions in basic STLC

---

## Key Patterns

### Option/Maybe Type
```
Option A = A + Unit
some x = inl x
none   = inr unit
```

### Either Type
```
Either A B = A + B
left x  = inl x
right y = inr y
```

### List Type (with recursion)
```
List A = Unit + (A × List A)
nil       = inl unit
cons x xs = inr ⟨x, xs⟩
```

---

## Connection to Next Chapter

Chapter 4 introduces **type inference** (Hindley-Milner):
- No more type annotations on lambdas!
- Compiler figures out types automatically
- Polymorphism: `id : ∀α. α → α`

The ADTs from this chapter will gain automatic type inference.

---

## One-Sentence Summary

> Algebraic data types give us the building blocks (products and sums) to model any data structure, while pattern matching lets us safely decompose that data.
