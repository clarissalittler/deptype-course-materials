# Chapter 2: Key Takeaways

## The Big Picture

**Types prevent errors before runtime.** Simply Typed Lambda Calculus (STLC) is the simplest typed language, and it introduces the fundamental concepts that all type systems build upon.

---

## Core Concepts

### 1. Types Classify Terms
```
Nat     - natural numbers (0, 1, 2, ...)
Bool    - booleans (true, false)
τ₁ → τ₂ - functions from τ₁ to τ₂
```

Every well-typed term has exactly one type.

### 2. Typing Judgment
```
Γ ⊢ t : τ
```
"In context Γ, term t has type τ"

The context Γ tracks variable types: `{x: Nat, y: Bool}`

### 3. Type Safety = Progress + Preservation
- **Progress**: Well-typed terms don't get stuck
- **Preservation**: Types are preserved during evaluation

Together: **Well-typed programs don't go wrong.**

### 4. Functions Require Type Annotations
```
λx:Nat. x + 1  :  Nat → Nat
```
Unlike untyped lambda calculus, we must specify parameter types.

---

## Most Important Rules

### T-Var (Variable)
```
x:τ ∈ Γ
─────────
Γ ⊢ x : τ
```

### T-Abs (Abstraction)
```
Γ, x:τ₁ ⊢ t : τ₂
─────────────────────
Γ ⊢ λx:τ₁. t : τ₁ → τ₂
```

### T-App (Application)
```
Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : τ₁
─────────────────────────────────
Γ ⊢ t₁ t₂ : τ₂
```

---

## What You Should Be Able To Do

After this chapter, you should be able to:

- [ ] Assign types to lambda terms (or explain why they don't type)
- [ ] Build typing derivation trees
- [ ] Implement a type checker
- [ ] Explain why `λx. x x` doesn't type check
- [ ] State and understand Progress and Preservation
- [ ] Add new types and operations to STLC

---

## Common Pitfalls

1. **Forgetting the context** when checking variable types
2. **Confusing type checking and evaluation** - they're separate!
3. **Expecting self-application to work** - `λx. x x` doesn't type
4. **Missing type annotations** on lambda parameters

---

## Key Insight: The Trade-off

| Untyped | Simply Typed |
|---------|--------------|
| Can write `λx. x x` | Cannot write self-application |
| Programs may loop forever | All programs terminate |
| No guarantees | Strong safety guarantees |
| Maximum flexibility | Some programs rejected |

STLC is **strongly normalizing**: every well-typed term reaches a normal form. This means no infinite loops, but also no general recursion without `fix`.

---

## Connection to Next Chapter

Chapter 3 adds **algebraic data types**:
- Product types (pairs): `τ₁ × τ₂`
- Sum types (variants): `τ₁ + τ₂`
- Pattern matching

These let us build real data structures while keeping type safety.

---

## One-Sentence Summary

> Simply Typed Lambda Calculus proves that types can guarantee program safety—well-typed programs never crash—at the cost of rejecting some valid programs.
