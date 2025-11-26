# Chapter 5: Key Takeaways

## The Big Picture

**System F makes polymorphism explicit and first-class.** Unlike HM where polymorphism is inferred, System F requires you to write type abstractions and applications—but in return, polymorphic values can be passed around freely.

---

## Core Concepts

### 1. Type Abstraction (Λ)
```
Λα. λx:α. x   :   ∀α. α → α
```
Capital lambda (Λ) introduces a type parameter. This creates a polymorphic value.

### 2. Type Application ([τ])
```
(Λα. λx:α. x) [Nat]   :   Nat → Nat
```
Square brackets apply a type argument. This instantiates polymorphism.

### 3. Universal Types (∀)
```
∀α. α → α
```
"For all types α, a function from α to α"

### 4. Parametricity
Polymorphic functions can't inspect their type parameters. A function `∀α. α → α` can **only** be the identity—it can't do anything type-specific.

---

## Most Important Rules

### T-TyAbs (Type Abstraction)
```
Δ, α; Γ ⊢ t : τ
─────────────────────
Δ; Γ ⊢ Λα. t : ∀α. τ
```

### T-TyApp (Type Application)
```
Δ; Γ ⊢ t : ∀α. τ
────────────────────────
Δ; Γ ⊢ t [τ'] : [α ↦ τ']τ
```

### Type β-Reduction
```
(Λα. t) [τ]  →  [α ↦ τ]t
```

---

## What You Should Be Able To Do

After this chapter, you should be able to:

- [ ] Write polymorphic functions with explicit Λ and []
- [ ] Type check System F terms (bidirectional)
- [ ] Encode data types using Church encodings
- [ ] Derive free theorems from types
- [ ] Explain why type inference is undecidable

---

## Church Encodings in System F

### Booleans
```
Bool = ∀α. α → α → α
true = Λα. λt:α. λf:α. t
false = Λα. λt:α. λf:α. f
```

### Natural Numbers
```
Nat = ∀α. (α → α) → α → α
zero = Λα. λs:α→α. λz:α. z
succ n = Λα. λs:α→α. λz:α. s (n [α] s z)
```

### Pairs
```
Pair A B = ∀γ. (A → B → γ) → γ
pair a b = Λγ. λf:A→B→γ. f a b
```

---

## Common Pitfalls

1. **Forgetting type applications**: `id 5` should be `id [Nat] 5`
2. **Mixing λ and Λ**: λ is for terms, Λ is for types
3. **Expecting inference**: You must write type annotations
4. **Impredicativity confusion**: `id [∀α. α → α]` is valid!

---

## Key Insight: Parametricity

From the type alone, we know:
```
∀α. α → α           -- must be identity
∀α. α → α → α       -- must be const or flip
∀α. List α → List α -- can only reorder/filter, not change elements
```

**"Theorems for free"**: Types constrain behavior so much that we can derive properties automatically.

---

## Trade-offs: HM vs System F

| Hindley-Milner | System F |
|----------------|----------|
| Type inference | No inference (undecidable) |
| Let-polymorphism only | First-class polymorphism |
| Simpler | More expressive |
| Predicative | Impredicative |

---

## Connection to Next Chapter

Chapter 6 introduces **System F-omega**:
- Higher-kinded types: `* → *`
- Type operators: `λα. List α`
- Type-level computation

This lets us abstract over type constructors like `List`, `Maybe`, `Either`.

---

## One-Sentence Summary

> System F makes polymorphism explicit with type abstraction (Λ) and application ([τ]), enabling first-class polymorphic values at the cost of decidable type inference.
