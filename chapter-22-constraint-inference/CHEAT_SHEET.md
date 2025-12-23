# Constraint-Based Inference Cheat Sheet

## Core Algorithm

### Two Phases

1. **Generate Constraints**: `Γ ⊢ e ⇝ τ | C`
2. **Solve Constraints**: `solve(C) = σ`

### Constraint Generation Rules

```
[Var]     x:∀ᾱ.τ ∈ Γ    β̄ fresh
          ────────────────────────
          Γ ⊢ x ⇝ τ[ᾱ↦β̄] | ∅

[Lam]     α fresh    Γ,x:α ⊢ e ⇝ τ | C
          ────────────────────────────────
          Γ ⊢ λx.e ⇝ α → τ | C

[App]     Γ ⊢ e₁ ⇝ τ₁ | C₁    Γ ⊢ e₂ ⇝ τ₂ | C₂    α fresh
          ─────────────────────────────────────────────────────
          Γ ⊢ e₁ e₂ ⇝ α | C₁ ∪ C₂ ∪ {τ₁ ≡ τ₂ → α}

[Let]     Γ ⊢ e₁ ⇝ τ₁ | C₁    Γ,x:gen(τ₁) ⊢ e₂ ⇝ τ₂ | C₂
          ─────────────────────────────────────────────────────
          Γ ⊢ let x=e₁ in e₂ ⇝ τ₂ | C₁ ∪ C₂
```

## Unification

### Robinson's Algorithm

```haskell
unify(τ, τ)         = {}
unify(α, τ)         = {α ↦ τ}  if α ∉ ftv(τ)
unify(τ, α)         = {α ↦ τ}  if α ∉ ftv(τ)
unify(τ₁→τ₂, τ₃→τ₄) = σ₂ ∘ σ₁  where σ₁=unify(τ₁,τ₃)
                                       σ₂=unify(σ₁(τ₂),σ₁(τ₄))
unify(τ₁, τ₂)       = fail
```

### Occurs Check

Before binding `α ↦ τ`, check `α ∉ ftv(τ)` to prevent infinite types.

## Implementation Patterns

### Fresh Variables

```haskell
fresh :: ConstraintGen Type
fresh = do
  n <- get
  put (n + 1)
  return $ TyVar ("t" ++ show n)
```

### Constraint Solving

```haskell
solve :: ConstraintSet -> Either Error Subst
solve = go emptySubst
  where
    go s [] = return s
    go s (Equal t1 t2 : cs) = do
      let t1' = applySubst s t1
      let t2' = applySubst s t2
      s' <- unify t1' t2'
      go (s' `composeSubst` s) cs
```

## Common Patterns

### Identity

```
⊢ λx. x ⇝ α → α | ∅
```

### Application

```
⊢ f x ⇝ β | {τ_f ≡ τ_x → β}
```

### Let-Polymorphism

```
⊢ let id = λx.x in (id 0, id true) ⇝ Nat × Bool
```

Constraints from each use are independent!

## Error Cases

### Occurs Check

```
⊢ λx. x x ⇝ ERROR
Constraint: α ≡ α → β  (α occurs in α → β!)
```

### Type Mismatch

```
⊢ if 0 then true else false ⇝ ERROR
Constraint: Nat ≡ Bool  (cannot unify!)
```

### Non-Polymorphic Lambda

```
⊢ λf. (f 0, f true) ⇝ ERROR
Constraints: α ≡ Nat → β, α ≡ Bool → γ
           ⇒ Nat ≡ Bool  (fail!)
```

## REPL Commands

```
:type term              Infer type
:constraints term       Show constraints
:solve term            Show solving process
:unify ty1 ty2         Test unification
```

## Quick Reference

| Term | Type | Constraints |
|------|------|-------------|
| `λx. x` | `α → α` | `∅` |
| `λx. succ x` | `Nat → Nat` | `{α ≡ Nat}` |
| `λf. λx. f x` | `(α→β) → α → β` | `{γ ≡ α→β}` |
| `λx. (x, x)` | `α → α×α` | `∅` |
| `let id=λx.x in id` | `α→α` | `∅` |

## Tips

1. **Generate first, solve later** - separate concerns
2. **Fresh variables everywhere** - avoid accidental sharing
3. **Apply substitutions incrementally** - compose as you go
4. **Check occurs check** - prevent infinite types
5. **Generalize only at let** - lambdas are monomorphic
