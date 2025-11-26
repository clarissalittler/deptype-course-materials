# Chapter 7: Key Takeaways

## The Big Picture

**Dependent types unify terms and types.** Types can now depend on values, enabling precise specifications like "vector of length n" or "sorted list." This is the foundation for proof assistants.

---

## Core Concepts

### 1. Types Depend on Values
```
Vec : Nat → Type → Type
Vec 3 Nat  -- vector of exactly 3 natural numbers
```

The type includes runtime information (length 3).

### 2. Pi Types (Dependent Functions)
```
Π(n:Nat). Vec n α → Vec n α
```
The return type depends on the input value. This generalizes `→`:
- `A → B` is `Π(_:A). B` where B doesn't use the input

### 3. Sigma Types (Dependent Pairs)
```
Σ(n:Nat). Vec n α
```
The second component's type depends on the first. This is an "existential": a vector of *some* length.

### 4. Unified Syntax
```
Term = Type = Kind
```
Everything is a term. `Nat : Type`, `Type : Type` (in our simplified version).

---

## Most Important Rules

### Π-Formation
```
Γ ⊢ A : Type    Γ, x:A ⊢ B : Type
──────────────────────────────────
Γ ⊢ Π(x:A). B : Type
```

### Π-Introduction
```
Γ, x:A ⊢ t : B
────────────────────
Γ ⊢ λx:A. t : Π(x:A). B
```

### Π-Elimination
```
Γ ⊢ f : Π(x:A). B    Γ ⊢ a : A
──────────────────────────────
Γ ⊢ f a : [x ↦ a]B
```

---

## What You Should Be Able To Do

After this chapter, you should be able to:

- [ ] Write dependent function types (Π types)
- [ ] Write dependent pair types (Σ types)
- [ ] Understand the Curry-Howard correspondence
- [ ] See types as propositions and terms as proofs
- [ ] Explain why Type:Type is problematic (Girard's paradox)

---

## Curry-Howard Correspondence

| Logic | Type Theory |
|-------|-------------|
| Proposition | Type |
| Proof | Term |
| A implies B | A → B |
| A and B | A × B |
| A or B | A + B |
| For all x, P(x) | Π(x:A). P x |
| Exists x, P(x) | Σ(x:A). P x |
| True | Unit |
| False | Empty |

**A type is inhabited iff the corresponding proposition is provable.**

---

## Common Pitfalls

1. **Type-in-Type inconsistency**: Our `Type : Type` is unsound (fixed in Ch8)
2. **Normalization for equality**: Types are equal if they normalize to the same form
3. **Dependent pattern matching**: More complex than simple pattern matching
4. **Universe confusion**: What type does `Type` have?

---

## Key Examples

### Length-Indexed Vectors
```
Vec : Nat → Type → Type
nil  : Vec 0 α
cons : α → Vec n α → Vec (n+1) α
```

### Safe Head (No Runtime Error!)
```
head : Π(n:Nat). Vec (n+1) α → α
```
Type guarantees non-empty input.

### Proofs as Types
```
-- "n equals n" as a type
Eq Nat n n  -- inhabited by refl

-- A proof that addition is commutative would have type:
Π(m:Nat). Π(n:Nat). Eq Nat (plus m n) (plus n m)
```

---

## The Problem: Type-in-Type

```
Type : Type   -- Allows Girard's paradox!
```

This is Russell's paradox at the type level. We can encode:
```
R = { x | x ∉ x }
```

**Solution** (Chapter 8): Universe hierarchy `Type₀ : Type₁ : Type₂ : ...`

---

## Connection to Next Chapter

Chapter 8 adds:
- **Universe hierarchy**: Avoids paradox
- **Propositional equality**: `Eq A x y` with J eliminator
- **Inductive families**: Vec, Fin properly defined
- **Consistent foundation**: Suitable for proofs

---

## One-Sentence Summary

> Dependent types let types contain values, unifying programming and logic through the Curry-Howard correspondence—but we need universes to avoid paradox.
