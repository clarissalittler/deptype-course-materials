# Chapter 4: Key Takeaways

## The Big Picture

**Hindley-Milner gives us the best of both worlds**: polymorphism (like untyped) with safety (like STLC), and the compiler figures out types automatically.

---

## Core Concepts

### 1. Type Inference
```
λx. x   has type   ∀α. α → α
```
No annotations needed! The algorithm discovers the most general type.

### 2. Polymorphism via Type Schemes
```
Monotype: Nat → Nat
Polytype: ∀α. α → α
```

Type schemes (polytypes) have universal quantifiers. They represent "works for any type."

### 3. Let-Polymorphism
```
let id = λx. x in (id 5, id true)  -- WORKS!
(λid. (id 5, id true)) (λx. x)     -- FAILS!
```

**Critical distinction**:
- `let`-bound variables are **polymorphic** (can be used at multiple types)
- `λ`-bound variables are **monomorphic** (fixed to one type)

### 4. Unification
```
unify(α → β, Nat → Bool) = {α ↦ Nat, β ↦ Bool}
```

Finding substitutions that make types equal. The heart of type inference.

---

## Most Important Rules

### Algorithm W (Simplified)
```
infer(Γ, x)       = (instantiate(Γ(x)), [])
infer(Γ, λx. t)   = let (τ, S) = infer(Γ ∪ {x:α}, t) in (α → τ, S)
infer(Γ, t₁ t₂)   = unify and compose substitutions
infer(Γ, let x=t₁ in t₂) = generalize t₁'s type, then infer t₂
```

### Generalization
```
generalize(Γ, τ) = ∀ᾱ. τ   where ᾱ = FV(τ) \ FV(Γ)
```

Only generalize variables that aren't "in scope" from the environment.

### Instantiation
```
instantiate(∀α. α → α) = β → β   (fresh β each time!)
```

Replace quantified variables with fresh type variables.

---

## What You Should Be Able To Do

After this chapter, you should be able to:

- [ ] Infer types for lambda terms without annotations
- [ ] Implement Robinson's unification algorithm
- [ ] Explain why `λx. x x` fails the occurs check
- [ ] Distinguish let-polymorphism from lambda-monomorphism
- [ ] Find principal (most general) types

---

## Common Pitfalls

1. **Occurs check failure**: `α = α → τ` creates infinite type
2. **Let vs. Lambda**: Only `let` generalizes!
3. **Forgetting to apply substitutions**: Thread them through!
4. **Wrong composition order**: `S₂ ∘ S₁` means apply S₁ first

---

## The Three Laws of HM

### 1. Occurs Check
```
unify(α, τ) fails if α ∈ FV(τ)
```
Prevents infinite types.

### 2. Let Generalizes, Lambda Doesn't
```
let f = λx. x in ...    -- f : ∀α. α → α
(λf. ...) (λx. x)       -- f : β → β (fixed)
```

### 3. Principal Types Exist
Every typeable term has a unique most general type. No guessing needed.

---

## Key Insight: What HM Can't Do

```
-- This doesn't work in HM:
λf. (f 0, f true)   -- f would need type ∀α. α → α
```

Lambda parameters can't be polymorphic in HM. For that, you need System F (Chapter 5).

---

## Connection to Next Chapter

Chapter 5 introduces **System F** (explicit polymorphism):
- Type abstraction: `Λα. t`
- Type application: `t [τ]`
- First-class polymorphism (pass polymorphic functions around)

Trade-off: More expressive, but type inference is undecidable.

---

## One-Sentence Summary

> Hindley-Milner achieves the "sweet spot" of type systems: automatic inference, polymorphism, and principal types—but it requires let-binding for polymorphic reuse.
