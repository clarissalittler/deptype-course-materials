# Chapter 5: Visual Aids

## Type Abstraction and Application

### Polymorphic Identity

```
Λα. λx:α. x   :   ∀α. α → α

Term structure:                Type structure:
     TyAbs                          ∀
       │                            │
       α                            α
       │                            │
      Lam                           →
     /   \                         / \
    x:α  Var                      α   α
          │
          x
```

### Type Application

```
(Λα. λx:α. x) [Nat]   :   Nat → Nat

Before:                          After:
    TyApp                         Lam
   /     \                       /   \
 TyAbs   Nat                   x:Nat  Var
   │                                   │
   α                                   x
   │
  Lam                    [α ↦ Nat]
 /   \            ──────────────────►
x:α  Var
      │
      x
```

---

## Typing Derivation

### For `Λα. λx:α. x`

```
                        x:α ∈ {x:α}
                      ───────────────  T-Var
                       {x:α} ⊢ x : α
              ─────────────────────────────  T-Abs
              {α}; {} ⊢ λx:α. x : α → α
        ─────────────────────────────────────  T-TyAbs
         {}; {} ⊢ Λα. λx:α. x : ∀α. α → α
```

### For Type Application

```
        Δ; Γ ⊢ t : ∀α. τ        Δ ⊢ τ' :: *
       ────────────────────────────────────  T-TyApp
              Δ; Γ ⊢ t [τ'] : [α ↦ τ']τ


Example: id [Nat]

  {}; {} ⊢ id : ∀α. α → α      {} ⊢ Nat :: *
 ─────────────────────────────────────────────  T-TyApp
        {}; {} ⊢ id [Nat] : Nat → Nat
```

---

## Two Contexts: Δ and Γ

```
┌─────────────────────────────────────────────────────────┐
│  Δ (Type Context)          Γ (Term Context)            │
│  ─────────────────         ──────────────────           │
│  Tracks type variables     Tracks term variables        │
│                                                         │
│  Example:                  Example:                     │
│  {α, β}                    {x:α, f:α→β, y:Nat}         │
│                                                         │
│  Used for:                 Used for:                    │
│  - Kinding (τ :: *)        - Typing (t : τ)            │
│  - Scope of type vars      - Scope of term vars        │
└─────────────────────────────────────────────────────────┘

Combined judgment: Δ; Γ ⊢ t : τ
```

---

## Church Encodings

### Booleans

```
Bool = ∀α. α → α → α

true  = Λα. λt:α. λf:α. t
false = Λα. λt:α. λf:α. f

        TyAbs                     TyAbs
          │                         │
          α                         α
          │                         │
         Lam                       Lam
        /   \                     /   \
      t:α   Lam                 t:α   Lam
           /   \                     /   \
         f:α   Var                 f:α   Var
                │                         │
                t                         f
           (return t)              (return f)
```

### Natural Numbers

```
Nat = ∀α. (α → α) → α → α

zero = Λα. λs:α→α. λz:α. z
one  = Λα. λs:α→α. λz:α. s z
two  = Λα. λs:α→α. λz:α. s (s z)

Visual representation:

zero:    z
one:     s ── z
two:     s ── s ── z
three:   s ── s ── s ── z
```

### Pairs

```
Pair A B = ∀γ. (A → B → γ) → γ

pair : ∀α. ∀β. α → β → Pair α β
pair = Λα. Λβ. λa:α. λb:β. Λγ. λf:α→β→γ. f a b

fst : ∀α. ∀β. Pair α β → α
fst = Λα. Λβ. λp:Pair α β. p [α] (λa:α. λb:β. a)

snd : ∀α. ∀β. Pair α β → β
snd = Λα. Λβ. λp:Pair α β. p [β] (λa:α. λb:β. b)
```

---

## Parametricity

### Functions Constrained by Types

```
∀α. α → α

What can this function do?

  Input: some value x of unknown type α
  Output: must return something of type α

  Can't create α values (don't know what α is)
  Can't inspect x (don't know how)
  Can only return x!

  ┌─────────────┐
  │   x : α     │──────────────────────► x : α
  └─────────────┘
       │
       │  Can't peek inside!
       │  Can't make new α!
       │
       └────► Must be identity
```

### For List Functions

```
∀α. List α → List α

What can this function do?

  Input: [x₁, x₂, x₃, ...] of type [α]

  CAN:                      CAN'T:
  ────                      ──────
  - Return []               - Change elements
  - Reorder elements        - Filter by value
  - Duplicate elements      - Create new elements
  - Drop elements           - Inspect elements

  Examples of valid functions:
  - reverse
  - take n
  - drop n
  - duplicate each element
  - identity
```

---

## Free Theorems

### Map Fusion

```
For map : ∀α. ∀β. (α → β) → List α → List β

Free theorem:
  map g ∘ map f = map (g ∘ f)

Visually:

[a₁, a₂, a₃]
     │
     │ map f
     ▼
[f a₁, f a₂, f a₃]           [a₁, a₂, a₃]
     │                            │
     │ map g                      │ map (g ∘ f)
     ▼                            ▼
[g(f a₁), g(f a₂), g(f a₃)]  [g(f a₁), g(f a₂), g(f a₃)]
     │                            │
     └────────────────────────────┘
               Same!
```

### Identity Preservation

```
For f : ∀α. α → α

Free theorem: f = id

Proof idea:
  f [Nat] : Nat → Nat
  For any n : Nat,
  f [Nat] n = ?

  Since f can't inspect n and can't create Nat values,
  f [Nat] n = n

  This works for ALL types, so f = id
```

---

## Impredicativity

### Self-Application in System F

```
id : ∀α. α → α

Can we apply id to itself?

id [∀β. β → β] id : (∀β. β → β) → (∀β. β → β)

     id
      │
      │ [∀β. β → β]
      ▼
   id : (∀β. β → β) → (∀β. β → β)
      │
      │ id
      ▼
   id : ∀β. β → β

This is impredicative: we instantiate α with a
type that itself contains ∀.
```

---

## Why Type Inference is Undecidable

```
Problem: Where to insert type applications?

Example:

  let id = Λα. λx:α. x in
  id ??? true

What goes in ???

  - Need to figure out: id [Bool] true
  - No annotation tells us
  - Infinitely many possible instantiations

In HM: id is ∀α. α → α, instantiation is automatic
In System F: You must write [Bool] explicitly!

┌─────────────────────────────────────────────────┐
│  Hindley-Milner         System F               │
│  ─────────────          ────────               │
│  id true                id [Bool] true         │
│  ↑                      ↑                      │
│  Inferred!              Must write explicitly  │
└─────────────────────────────────────────────────┘
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│                    SYSTEM F                                 │
├─────────────────────────────────────────────────────────────┤
│  SYNTAX                                                     │
│    Types: τ ::= α | τ → τ | ∀α. τ                          │
│    Terms: t ::= x | λx:τ. t | t t | Λα. t | t [τ]         │
│                                                             │
│  TYPE RULES                                                 │
│    Δ, α; Γ ⊢ t : τ                                         │
│    ─────────────────────  T-TyAbs                          │
│    Δ; Γ ⊢ Λα. t : ∀α. τ                                    │
│                                                             │
│    Δ; Γ ⊢ t : ∀α. τ                                        │
│    ─────────────────────  T-TyApp                          │
│    Δ; Γ ⊢ t [τ'] : [α↦τ']τ                                 │
│                                                             │
│  CHURCH ENCODINGS                                           │
│    Bool = ∀α. α → α → α                                    │
│    Nat  = ∀α. (α → α) → α → α                              │
│    Pair A B = ∀γ. (A → B → γ) → γ                          │
│                                                             │
│  PARAMETRICITY                                              │
│    ∀α. α → α  can only be identity                         │
└─────────────────────────────────────────────────────────────┘
```
