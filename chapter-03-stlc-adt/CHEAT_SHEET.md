# Chapter 3: STLC with Algebraic Data Types - Cheat Sheet

## Syntax Extensions

```
τ ::= ... | τ × τ | τ + τ | {labels: τ} | <labels: τ> | List τ | Unit

t ::= ...
    | (t, t) | fst t | snd t                    (products)
    | inl[τ] t | inr[τ] t | case t of ...       (sums)
    | {label=t, ...} | t.label                  (records)
    | <label=t> as τ | case t of <...>          (variants)
    | [] | t::t | match t with ...              (lists)
    | unit                                       (unit type)
```

## Product Types (Pairs)

### Typing Rules
```
Γ ⊢ t₁ : τ₁    Γ ⊢ t₂ : τ₂
────────────────────────────  (T-Pair)
Γ ⊢ (t₁, t₂) : τ₁ × τ₂

Γ ⊢ t : τ₁ × τ₂
───────────────  (T-Fst)
Γ ⊢ fst t : τ₁

Γ ⊢ t : τ₁ × τ₂
───────────────  (T-Snd)
Γ ⊢ snd t : τ₂
```

### Evaluation
```
fst (v₁, v₂) → v₁
snd (v₁, v₂) → v₂
```

## Sum Types (Tagged Unions)

### Typing Rules
```
Γ ⊢ t : τ₁
─────────────────────  (T-Inl)
Γ ⊢ inl[τ₂] t : τ₁ + τ₂

Γ ⊢ t : τ₂
─────────────────────  (T-Inr)
Γ ⊢ inr[τ₁] t : τ₁ + τ₂

Γ ⊢ t : τ₁ + τ₂    Γ, x:τ₁ ⊢ t₁ : τ    Γ, y:τ₂ ⊢ t₂ : τ
────────────────────────────────────────────────────────  (T-Case)
Γ ⊢ case t of inl x ⇒ t₁ | inr y ⇒ t₂ : τ
```

### Evaluation
```
case (inl v) of inl x ⇒ t₁ | inr y ⇒ t₂  →  [x ↦ v]t₁
case (inr v) of inl x ⇒ t₁ | inr y ⇒ t₂  →  [y ↦ v]t₂
```

## Records (Named Products)

### Typing
```
Γ ⊢ tᵢ : τᵢ  for each i
─────────────────────────────  (T-Record)
Γ ⊢ {lᵢ=tᵢ ⁱ} : {lᵢ:τᵢ ⁱ}

Γ ⊢ t : {l: τ, ...}
───────────────────  (T-Proj)
Γ ⊢ t.l : τ
```

### Evaluation
```
{lᵢ=vᵢ ⁱ}.lⱼ → vⱼ
```

## Variants (Named Sums)

### Typing
```
Γ ⊢ t : τᵢ
──────────────────────────────────  (T-Variant)
Γ ⊢ <lᵢ=t> as <l₁:τ₁, ..., lₙ:τₙ> : <l₁:τ₁, ..., lₙ:τₙ>

Γ ⊢ t : <lᵢ:τᵢ ⁱ>    Γ, xᵢ:τᵢ ⊢ tᵢ : τ  for each i
─────────────────────────────────────────────────────  (T-Case-Variant)
Γ ⊢ case t of <lᵢ=xᵢ> ⇒ tᵢ ⁱ : τ
```

## Lists

### Typing
```
─────────────────  (T-Nil)
Γ ⊢ [] : List τ

Γ ⊢ t₁ : τ    Γ ⊢ t₂ : List τ
──────────────────────────────  (T-Cons)
Γ ⊢ t₁::t₂ : List τ

Γ ⊢ t : List τ    Γ ⊢ t₁ : τ'    Γ, x:τ, xs:List τ ⊢ t₂ : τ'
───────────────────────────────────────────────────────────────  (T-Match)
Γ ⊢ match t with [] ⇒ t₁ | x::xs ⇒ t₂ : τ'
```

### Evaluation
```
match [] with [] ⇒ t₁ | x::xs ⇒ t₂  →  t₁
match (v::vs) with [] ⇒ t₁ | x::xs ⇒ t₂  →  [x ↦ v, xs ↦ vs]t₂
```

## Common Encodings

### Option Type
```
Option τ = Unit + τ

none : Option τ = inl[τ] unit
some : τ → Option τ = λx:τ. inr[Unit] x

match_option : Option τ → τ' → (τ → τ') → τ'
```

### Either Type
```
Either τ₁ τ₂ = τ₁ + τ₂

left : τ₁ → Either τ₁ τ₂ = λx:τ₁. inl[τ₂] x
right : τ₂ → Either τ₁ τ₂ = λx:τ₂. inr[τ₁] x
```

### Binary Tree
```
Tree τ = <leaf: Unit, node: τ × Tree τ × Tree τ>

leaf : Tree τ = <leaf=unit> as Tree τ
node : τ → Tree τ → Tree τ → Tree τ
```

## Pattern Matching

### Exhaustiveness Checking
Compiler must verify all constructors are covered:

```
// Exhaustive ✓
match opt with
  | None → ...
  | Some x → ...

// Non-exhaustive ✗ (missing Some case)
match opt with
  | None → ...
```

### Nested Patterns
```
match tree with
  | <leaf=_> → ...
  | <node=(v, (left, right))> → ...
```

## Real-World Mappings

| STLC+ADT | Rust | TypeScript | Haskell |
|----------|------|------------|---------|
| `τ₁ × τ₂` | `(T1, T2)` | `[T1, T2]` | `(T1, T2)` |
| `τ₁ + τ₂` | `enum E { A(T1), B(T2) }` | `{kind:'a',val:T1}\|{kind:'b',val:T2}` | `Either T1 T2` |
| `{x:τ₁, y:τ₂}` | `struct S { x: T1, y: T2 }` | `{x: T1, y: T2}` | `data S = S {x::T1, y::T2}` |
| `<a:τ₁, b:τ₂>` | `enum E { A(T1), B(T2) }` | `{kind:'a',val:T1}\|{kind:'b',val:T2}` | `data E = A T1 \| B T2` |
| `List τ` | `Vec<T>` | `T[]` | `[T]` |
| `match` | `match` | `switch` | `case` |

## Remember

### ✓ Do
- Use sum types instead of null
- Pattern match exhaustively
- Use records for named fields
- Use variants for state machines

### ✗ Avoid
- Returning null (use Option)
- Using booleans for state (use variants)
- Incomplete pattern matches

## Common Patterns

### Option/Maybe Pattern
```
safe_div : Nat → Nat → Option Nat
safe_div m n = if iszero n then none else some (m / n)
```

### Result/Either Pattern
```
validate : String → Either String User
validate s = if valid s then right (parse s) else left "Invalid"
```

### State Machine Pattern
```
State = <idle: Unit, processing: JobId, completed: Result>
```

## Quick Reference

### Product Type Operations
- **Create**: `(t₁, t₂)`
- **Destroy**: `fst t`, `snd t`
- **Type**: `τ₁ × τ₂`

### Sum Type Operations
- **Create**: `inl[τ₂] t₁` or `inr[τ₁] t₂`
- **Destroy**: `case t of inl x ⇒ ... | inr y ⇒ ...`
- **Type**: `τ₁ + τ₂`

### List Operations
- **Create**: `[]`, `x::xs`
- **Destroy**: `match xs with [] ⇒ ... | h::t ⇒ ...`
- **Type**: `List τ`

## Next Steps

→ **Chapter 4**: Type inference (no more annotations!)
→ **Chapter 5**: Polymorphism (generic ADTs)
