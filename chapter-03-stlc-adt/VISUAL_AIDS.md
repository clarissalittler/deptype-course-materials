# Chapter 3: Visual Aids

## Product Types

### Pair Structure

```
⟨a, b⟩ : A × B

      Pair
     /    \
    a      b
   : A    : B

Operations:
  fst ⟨a, b⟩ = a
  snd ⟨a, b⟩ = b
```

### Type Derivation for Pair

```
      Γ ⊢ 5 : Nat         Γ ⊢ true : Bool
     ─────────────────────────────────────  T-Pair
          Γ ⊢ ⟨5, true⟩ : Nat × Bool
```

### Nested Products

```
⟨⟨1, 2⟩, 3⟩ : (Nat × Nat) × Nat

          Pair
         /    \
      Pair     3
     /    \
    1      2

Accessing:
  fst (fst ⟨⟨1,2⟩,3⟩) = 1
  snd (fst ⟨⟨1,2⟩,3⟩) = 2
  snd ⟨⟨1,2⟩,3⟩ = 3
```

---

## Sum Types

### Sum Structure

```
inl a : A + B          inr b : A + B

    inl                    inr
     |                      |
     a                      b
   : A                    : B
```

### Type Derivation for Sum

```
                      Γ ⊢ 5 : Nat
     ─────────────────────────────────────────  T-Inl
          Γ ⊢ inl 5 : Nat + Bool
```

### Case Expression

```
case x of
  inl a => t₁
| inr b => t₂

            x : A + B
           /         \
    x = inl a      x = inr b
         |              |
         ▼              ▼
        t₁             t₂
       : τ             : τ
                  ↑
        Both branches same type!
```

---

## Pattern Matching

### Simple Pattern Match

```
case ⟨5, true⟩ of
  (x, y) => if y then x else 0

           ⟨5, true⟩
           /       \
          5       true
          ↓         ↓
          x         y
          │         │
          └────┬────┘
               ▼
        if true then 5 else 0
               │
               ▼
               5
```

### Nested Pattern Match

```
case inl ⟨1, 2⟩ of
  inl (a, b) => a + b
| inr c => c

        inl ⟨1, 2⟩
             │
        matches inl
             │
             ▼
          (a, b) ← ⟨1, 2⟩
             │
             ▼
           a = 1
           b = 2
             │
             ▼
          1 + 2 = 3
```

---

## Exhaustiveness Checking

### Complete Match

```
match x : Bool + Nat with
| inl true  => ...  ✓
| inl false => ...  ✓
| inr n     => ...  ✓

Coverage tree:
         Bool + Nat
        /          \
      inl          inr
       |            |
     Bool          Nat
    /    \          |
  true  false       ✓
   ✓      ✓

All leaves covered ✓
```

### Incomplete Match

```
match x : Bool + Nat with
| inl true => ...

Coverage tree:
         Bool + Nat
        /          \
      inl          inr
       |            |
     Bool          Nat
    /    \          |
  true  false       ✗
   ✓      ✗

Missing: inl false, inr _
```

---

## Common ADT Patterns

### Option Type

```
Option A = A + Unit

Some a:                    None:
  inl a : A + Unit           inr () : A + Unit

      inl                       inr
       |                         |
       a                        ()
     : A                      : Unit
```

### Either Type

```
Either A B = A + B

Left a:                    Right b:
  inl a : A + B              inr b : A + B
```

### List Type (Recursive)

```
List A = Unit + (A × List A)

Empty:                     Cons:
  inl () : List A           inr ⟨a, as⟩ : List A

Example: [1, 2, 3]

  inr ⟨1, inr ⟨2, inr ⟨3, inl ()⟩⟩⟩

  Visually:
       cons
      /    \
     1     cons
          /    \
         2     cons
              /    \
             3     nil
```

---

## Type Algebra

### Cardinality

```
|A × B| = |A| × |B|    (multiplication)
|A + B| = |A| + |B|    (addition)
|A → B| = |B|^|A|      (exponentiation)
|Unit| = 1
|Void| = 0

Examples:
  |Bool × Bool| = 2 × 2 = 4
  |Bool + Bool| = 2 + 2 = 4
  |Bool → Bool| = 2² = 4
```

### Algebraic Laws

```
A × (B + C) ≅ (A × B) + (A × C)    (distributive)

Left side:              Right side:
  ⟨a, inl b⟩             inl ⟨a, b⟩
  ⟨a, inr c⟩             inr ⟨a, c⟩

Isomorphic! Same number of inhabitants, same structure.
```

### Unit and Void Laws

```
A × Unit ≅ A           (identity for ×)
A + Void ≅ A           (identity for +)
A × Void ≅ Void        (annihilator)
```

---

## Evaluation with ADTs

### Product Evaluation

```
fst ⟨succ 0, true⟩

Step 1: Evaluate pair contents (CBV)
        ⟨1, true⟩

Step 2: Apply fst
        fst ⟨1, true⟩ → 1

Result: 1
```

### Case Evaluation

```
case (inl (succ 0)) of
  inl x => x
| inr y => 0

Step 1: Evaluate scrutinee
        inl 1

Step 2: Match pattern
        inl 1 matches (inl x) with x = 1

Step 3: Evaluate chosen branch
        x → 1

Result: 1
```

---

## Type Derivation for Case

```
            Γ ⊢ e : A + B
            Γ, x:A ⊢ t₁ : τ
            Γ, y:B ⊢ t₂ : τ
─────────────────────────────────────────────────  T-Case
   Γ ⊢ case e of inl x => t₁ | inr y => t₂ : τ


Example:

     x:Nat+Bool ∈ Γ       {a:Nat} ⊢ a : Nat      {b:Bool} ⊢ 0 : Nat
    ───────────────       ─────────────────      ──────────────────
    Γ ⊢ x : Nat+Bool             │                       │
          │                      │                       │
          └──────────────────────┴───────────────────────┘
                                 │
                                 ▼
        Γ ⊢ case x of inl a => a | inr b => 0 : Nat
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│            ALGEBRAIC DATA TYPES                             │
├─────────────────────────────────────────────────────────────┤
│  PRODUCTS (A × B)                                           │
│    Constructor:  ⟨t₁, t₂⟩                                   │
│    Eliminators:  fst, snd                                   │
│    Meaning:      A AND B (both values)                      │
│                                                             │
│  SUMS (A + B)                                               │
│    Constructors: inl, inr                                   │
│    Eliminator:   case...of                                  │
│    Meaning:      A OR B (one value)                         │
│                                                             │
│  PATTERN MATCHING                                           │
│    case e of p₁ => t₁ | p₂ => t₂ | ...                     │
│    Must be exhaustive!                                      │
│                                                             │
│  COMMON TYPES                                               │
│    Option A = A + Unit                                      │
│    Either A B = A + B                                       │
│    List A = Unit + (A × List A)                            │
└─────────────────────────────────────────────────────────────┘
```
