# Chapter 4: Hindley-Milner Type Inference - Cheat Sheet

## Key Idea

**No type annotations needed!** The compiler infers types automatically.

## Syntax (No Type Annotations!)

```
t ::=                  (terms)
    x                  variable
    λx. t              abstraction (NO type annotation!)
    t t                application
    let x = t in t     let binding (enables polymorphism)
    primitives...
```

## Type Schemes

```
σ ::= τ | ∀α. σ        (type schemes)
τ ::= α | τ → τ | ...  (monotypes)
```

**Key**: Only let-bound variables get type schemes (∀α. τ).
Lambda-bound variables stay monomorphic (τ).

## Algorithm W (Simplified)

```haskell
infer Γ x = instantiate(Γ(x))

infer Γ (λx. t) =
  α fresh
  τ = infer (Γ, x:α) t
  return α → τ

infer Γ (t₁ t₂) =
  τ₁ = infer Γ t₁
  τ₂ = infer Γ t₂
  α fresh
  unify τ₁ with τ₂ → α
  return α

infer Γ (let x = t₁ in t₂) =
  τ₁ = infer Γ t₁
  σ = generalize Γ τ₁        -- Create type scheme!
  return infer (Γ, x:σ) t₂
```

## Unification

**Goal**: Make two types equal by substitution.

```
unify(α, τ) = [α ↦ τ]        (if α ∉ FV(τ))  -- Occurs check!
unify(τ, α) = [α ↦ τ]
unify(τ₁ → τ₂, τ₃ → τ₄) = unify(τ₁, τ₃) ∪ unify(τ₂, τ₄)
unify(τ, τ) = []
unify(τ₁, τ₂) = fail         (if incompatible)
```

**Occurs Check**: α = α → β is INFINITE TYPE (reject!)

## Let-Polymorphism

### Works ✓
```haskell
let id = λx. x                  -- id : ∀α. α → α
in (id 5, id true)              -- ✓ Each use instantiates α differently
```

### Doesn't Work ✗
```haskell
(λid. (id 5, id true)) (λx. x)  -- ✗ id : τ → τ (monomorphic!)
```

## Type Inference Examples

### Example 1: Identity
```
infer ∅ (λx. x)
→ α fresh, x:α ⊢ x : α
→ Result: α → α
→ Rename: ∀α. α → α
```

### Example 2: Composition
```
infer ∅ (λf. λg. λx. f (g x))
→ ...
→ Result: (β → γ) → (α → β) → α → γ
```

### Example 3: Self-Application (Fails!)
```
infer ∅ (λx. x x)
→ α fresh, x:α ⊢ x x
→ x : α, need x : α → β
→ unify α with α → β
→ ✗ Occurs check fails!
```

## Generalization vs. Instantiation

### Generalization (at let)
```
generalize Γ τ = ∀(FV(τ) \ FV(Γ)). τ
```
Bind free type variables.

### Instantiation (at use)
```
instantiate (∀α. τ) = [α ↦ fresh]τ
```
Replace bound variables with fresh ones.

## Common Idioms (Inferred Types)

| Term | Inferred Type |
|------|---------------|
| `λx. x` | `∀α. α → α` |
| `λf. λg. λx. f (g x)` | `∀α β γ. (β→γ) → (α→β) → α→γ` |
| `λf. λx. f (f x)` | `∀α. (α→α) → α→α` |
| `λx. λy. x` | `∀α β. α → β → α` |

## Remember

### ✓ Do
- Omit type annotations (inferred!)
- Use let for polymorphic bindings
- Trust the inferencer
- Let generalization makes code polymorphic

### ✗ Avoid
- Self-application: `λx. x x` (doesn't type-check)
- Expecting lambda-bound polymorphism
- Infinite types (occurs check prevents)

## Comparison

| Feature | STLC | HM | System F |
|---------|------|-----|----------|
| Annotations | Required | None | Required |
| Polymorphism | No | Let-poly | Full |
| Type inference | Trivial | Algorithm W | Undecidable |
| Expressiveness | Low | Medium | High |

## Real Languages

| Language | HM-based | Extensions |
|----------|----------|------------|
| **Haskell** | Yes | Type classes, GADTs, etc. |
| **OCaml** | Yes | Objects, modules |
| **F#** | Yes | .NET integration |
| **Rust** | Partial | Local inference |
| **TypeScript** | No | Structural typing |

## Debugging Type Errors

1. **Read error carefully** - Shows constraint that failed
2. **Check let vs lambda** - Only let is polymorphic
3. **Trace unification** - Where did types conflict?
4. **Add annotations temporarily** - Narrow down issue

## Quick Reference

### Key Theorem
**Principal Types**: Every well-typed term has a most general type.

### Decidability
Type inference is **decidable** (unlike System F).

### Complexity
**DEXPTIME-complete** in theory, but fast in practice.

## Next Steps

→ **Chapter 5**: System F (explicit polymorphism, more power, no inference)
