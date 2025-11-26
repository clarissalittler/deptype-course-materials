# Chapter 2: Visual Aids

## Type Derivation Trees

### Variable Rule (T-Var)

```
          x:Nat ∈ {x:Nat}
         ─────────────────  T-Var
          {x:Nat} ⊢ x : Nat
```

### Abstraction Rule (T-Abs)

**For `λx:Nat. x`**
```
                x:Nat ∈ {x:Nat}
               ─────────────────  T-Var
               {x:Nat} ⊢ x : Nat
         ────────────────────────────  T-Abs
           {} ⊢ λx:Nat. x : Nat → Nat
```

### Application Rule (T-App)

**For `(λx:Nat. x) 5`**
```
                    x:Nat ∈ {x:Nat}
                   ─────────────────  T-Var
                   {x:Nat} ⊢ x : Nat
             ────────────────────────────  T-Abs        ────────  T-Nat
              {} ⊢ λx:Nat. x : Nat → Nat               {} ⊢ 5 : Nat
         ─────────────────────────────────────────────────────────────  T-App
                            {} ⊢ (λx:Nat. x) 5 : Nat
```

### Complex Example

**For `λf:Nat→Nat. λx:Nat. f x`**
```
                                    f:Nat→Nat ∈ Γ         x:Nat ∈ Γ
                                   ──────────────────    ─────────────
                                   Γ ⊢ f : Nat → Nat     Γ ⊢ x : Nat
                                ──────────────────────────────────────  T-App
                                         Γ ⊢ f x : Nat
                         ──────────────────────────────────────────────  T-Abs
                          Γ' ⊢ λx:Nat. f x : Nat → Nat
         ─────────────────────────────────────────────────────────────────  T-Abs
           {} ⊢ λf:Nat→Nat. λx:Nat. f x : (Nat → Nat) → Nat → Nat

where Γ  = {f:Nat→Nat, x:Nat}
      Γ' = {f:Nat→Nat}
```

---

## Why Self-Application Fails

**Attempting to type `λx. x x`**
```
                    x:? ∈ {x:?}       x:? ∈ {x:?}
                   ─────────────     ─────────────
                   {x:?} ⊢ x : ?     {x:?} ⊢ x : ?
                 ─────────────────────────────────  T-App (need ? = ? → τ)
                        {x:?} ⊢ x x : τ

For T-App to work:
  - First x must have type ? → τ (function)
  - Second x must have type ?
  - So x : ? and x : ? → τ
  - Therefore ? = ? → τ

  INFINITE TYPE! ✗

  ? = ? → τ
    = (? → τ) → τ
    = ((? → τ) → τ) → τ
    = ...
```

---

## Type Context

### Context as Stack

```
┌─────────────────────┐
│   TYPE CONTEXT Γ    │
├─────────────────────┤
│  y : Bool           │  ← most recently added
│  x : Nat            │
│  f : Nat → Nat      │  ← oldest
└─────────────────────┘

When checking λz:Nat. ...:

┌─────────────────────┐
│   TYPE CONTEXT Γ'   │
├─────────────────────┤
│  z : Nat            │  ← NEW (shadowing possible)
│  y : Bool           │
│  x : Nat            │
│  f : Nat → Nat      │
└─────────────────────┘
```

### Shadowing

```
λx:Nat. λx:Bool. x

Outer scope:        Inner scope:
┌──────────┐        ┌──────────┐
│ x : Nat  │   →    │ x : Bool │  ← shadows outer x
└──────────┘        │ x : Nat  │  ← hidden
                    └──────────┘

The inner x : Bool is found first!
```

---

## Evaluation Trace

### Simple Application

```
(λx:Nat. succ x) 5

     ┌───────────────┐
     │ Is this a     │  YES
     │ redex?        │ ────→  β-reduce
     └───────────────┘
              │
              ▼
        [x ↦ 5](succ x)
              │
              ▼
          succ 5
              │
              ▼
            6  ✓ (value)
```

### Nested Application

```
(λf:Nat→Nat. λx:Nat. f x) succ 3

Step 1: (λf. λx. f x) succ
        ─────────────────────
                 │
                 ▼  [f ↦ succ]
            λx:Nat. succ x

Step 2: (λx:Nat. succ x) 3
        ────────────────────
                 │
                 ▼  [x ↦ 3]
              succ 3

Step 3: succ 3
        ───────
           │
           ▼
           4  ✓
```

---

## Progress and Preservation

### Progress Theorem

```
If  ⊢ t : τ  (closed, well-typed)
Then either:

    ┌─────────────────┐
    │     t : τ       │
    └────────┬────────┘
             │
      ┌──────┴──────┐
      │             │
      ▼             ▼
  ┌───────┐    ┌─────────┐
  │ Value │    │ t → t'  │
  │  (v)  │    │ (steps) │
  └───────┘    └─────────┘
```

### Preservation Theorem

```
If  Γ ⊢ t : τ   AND   t → t'
Then  Γ ⊢ t' : τ

  ┌─────────────┐
  │  t : τ      │
  └──────┬──────┘
         │ step
         ▼
  ┌─────────────┐
  │  t' : τ     │  ← same type!
  └─────────────┘
```

### Combined: Type Safety

```
Start: ⊢ t₀ : τ

  t₀ : τ                    Well-typed
    │
    │ step (Progress)
    ▼
  t₁ : τ                    Still well-typed (Preservation)
    │
    │ step
    ▼
  t₂ : τ
    │
    │ ...
    ▼
  v : τ                     Value of type τ ✓

No "stuck" states possible!
```

---

## Type Checking Algorithm

### Flowchart

```
                    ┌─────────────┐
                    │  typeOf(t)  │
                    └──────┬──────┘
                           │
              ┌────────────┼────────────┐
              │            │            │
              ▼            ▼            ▼
         ┌────────┐   ┌────────┐   ┌────────┐
         │  Var   │   │  Lam   │   │  App   │
         └────┬───┘   └────┬───┘   └────┬───┘
              │            │            │
              ▼            ▼            ▼
         lookup in    check body    check both
         context Γ    with x:τ      and match
              │            │            │
              ▼            ▼            ▼
           return      return       return
             τ         τ₁ → τ₂        τ₂
```

### Detailed App Case

```
typeOf(Γ, t₁ t₂):

    ┌─────────────────────────────┐
    │  τ₁ = typeOf(Γ, t₁)        │
    └──────────────┬──────────────┘
                   │
    ┌──────────────┴──────────────┐
    │  τ₂ = typeOf(Γ, t₂)        │
    └──────────────┬──────────────┘
                   │
         ┌─────────┴─────────┐
         │  Is τ₁ = τa → τb? │
         └─────────┬─────────┘
              │         │
           YES│         │NO
              ▼         ▼
    ┌──────────────┐  ┌───────────────┐
    │ Is τ₂ = τa?  │  │ ERROR:        │
    └───────┬──────┘  │ Not a function│
         │      │     └───────────────┘
      YES│      │NO
         ▼      ▼
    ┌────────┐ ┌────────────────┐
    │Return τb│ │ERROR: Type    │
    └────────┘ │mismatch τ₂≠τa │
               └────────────────┘
```

---

## Type Syntax Diagram

```
Types:

  τ ::= Nat              ┌─────────────────┐
      │ Bool             │  Base Types     │
      │ Unit             └─────────────────┘

      │ τ → τ            ┌─────────────────┐
                         │  Function Type  │
                         │  (right assoc)  │
                         └─────────────────┘

Example type trees:

  Nat → Bool              Nat → Nat → Nat

      →                        →
     / \                      / \
   Nat Bool                 Nat  →
                                / \
                              Nat Nat
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│              SIMPLY TYPED LAMBDA CALCULUS                   │
├─────────────────────────────────────────────────────────────┤
│  TYPES                                                      │
│    τ ::= Nat | Bool | τ → τ                                │
│                                                             │
│  TYPING RULES                                               │
│                                                             │
│         x:τ ∈ Γ              Γ, x:τ₁ ⊢ t : τ₂              │
│        ──────────           ─────────────────────           │
│        Γ ⊢ x : τ            Γ ⊢ λx:τ₁. t : τ₁→τ₂           │
│                                                             │
│    Γ ⊢ t₁ : τ₁→τ₂    Γ ⊢ t₂ : τ₁                          │
│   ────────────────────────────────                          │
│           Γ ⊢ t₁ t₂ : τ₂                                   │
│                                                             │
│  TYPE SAFETY                                                │
│    Progress:     ⊢ t : τ  ⟹  t is value OR t → t'         │
│    Preservation: ⊢ t : τ, t → t'  ⟹  ⊢ t' : τ             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```
