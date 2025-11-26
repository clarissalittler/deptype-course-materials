# Chapter 7: Visual Aids

## Unified Syntax

### Before: Separate Hierarchies

```
SYSTEM F-OMEGA:

  Terms          Types          Kinds
    │              │              │
    5           Nat             *
   λx.x        Nat→Nat         *→*
    │              │              │
    └──────────────┴──────────────┘
         Separate levels!
```

### After: Single Hierarchy

```
DEPENDENT TYPES:

         Everything is a Term!
              │
    ┌─────────┼─────────┐
    │         │         │
    5        Nat      Type
   λx.x     Nat→Nat   Type
  Π(n:Nat)  Vec n     Type
    │         │         │
    └─────────┴─────────┘
        All the same syntax!
```

---

## Pi Types (Π)

### Non-Dependent Function

```
Nat → Bool    =    Π(_:Nat). Bool
                      │
              (underscore means unused)

        Π
       / \
     _:Nat  Bool

"A function from Nat to Bool"
```

### Dependent Function

```
Π(n:Nat). Vec n α

        Π
       / \
     n:Nat   Vec n α
               │
         depends on n!

"Given a natural number n, returns a vector of length n"
```

### Visual Comparison

```
NON-DEPENDENT:              DEPENDENT:
   A → B                    Π(x:A). B(x)
                                  │
   ┌───┐    ┌───┐          ┌───┐ │ ┌─────────┐
   │ A │───►│ B │          │ A │─┼─►│ B(x)    │
   └───┘    └───┘          └───┘ │ └─────────┘
                                 │      │
                                 x      │
                                 │      │
                                 └──────┘
                            return type depends on input!
```

---

## Sigma Types (Σ)

### Non-Dependent Pair

```
A × B    =    Σ(_:A). B

       Σ
      / \
    _:A   B

"A pair of A and B"
```

### Dependent Pair

```
Σ(n:Nat). Vec n α

       Σ
      / \
    n:Nat   Vec n α
              │
        depends on n!

"A number n paired with a vector of that length"
```

### Visual

```
Σ(n:Nat). Vec n α

Examples:
  (0, [])           : Σ(n:Nat). Vec n Nat
  (2, [1, 2])       : Σ(n:Nat). Vec n Nat
  (3, [a, b, c])    : Σ(n:Nat). Vec n Char

The second component's type depends on the first component's value!

  ┌───┐
  │ n │────────────────────────┐
  └───┘                        │
    │                          │
    │                          ▼
    │                    ┌─────────────┐
    └────────────────────│  Vec n α    │
                         └─────────────┘
```

---

## Curry-Howard Correspondence

### Propositions as Types

```
┌─────────────────────────────────────────────────────────────┐
│         LOGIC                    TYPE THEORY               │
├─────────────────────────────────────────────────────────────┤
│  Proposition P                   Type P                     │
│  Proof of P                      Term of type P             │
│                                                             │
│  A implies B                     A → B                      │
│  A and B                         A × B  (Σ)                 │
│  A or B                          A + B                      │
│  For all x, P(x)                 Π(x:A). P x                │
│  Exists x, P(x)                  Σ(x:A). P x                │
│  True                            Unit (has inhabitant)      │
│  False                           Empty (no inhabitants)     │
└─────────────────────────────────────────────────────────────┘
```

### Example: Proof of A → A

```
Proposition: A implies A (trivially true)

As a type: A → A

Proof (term):
  λa:A. a

         Lam
        /   \
      a:A   Var
             │
             a

"Given a proof of A, return that same proof"
= The identity function!
```

### Example: ∀n. n = n

```
Proposition: For all n, n equals n

As a type: Π(n:Nat). Eq Nat n n

Proof:
  λn:Nat. refl n

For each n, refl n proves n = n.
```

---

## Vec: Length-Indexed Lists

```
Vec : Nat → Type → Type

Vec 0 α:              Vec 3 α:
  nil                   cons a₁ (cons a₂ (cons a₃ nil))
   │                         │
   └── empty                 └── three elements

Type ensures length!

          Vec 0 α                    Vec 3 α
             │                          │
             ▼                          ▼
           nil                   ┌──────┴──────┐
                                 │   │   │     │
                                a₁  a₂  a₃   nil


Safe head:
  head : Π(n:Nat). Vec (suc n) α → α
              │
              └── n+1 means non-empty!

  head cannot be called on Vec 0 α (empty vector)
```

---

## Type Checking with Normalization

### Types Equal After Reduction

```
Are these types equal?

  Vec (1 + 1) Nat    ?=    Vec 2 Nat

Step 1: Normalize (1 + 1)
  1 + 1 = 2

Step 2: Compare
  Vec 2 Nat  =  Vec 2 Nat  ✓

Types are equal if they normalize to the same form.
```

### Checking Application

```
f : Π(n:Nat). Vec n α
x : Vec (2 + 3) α

f 5 x : ???

Step 1: f 5 : Vec 5 α

Step 2: Check x : Vec 5 α
  - x has type Vec (2+3) α
  - Normalize: 2+3 = 5
  - Vec 5 α = Vec 5 α ✓

Step 3: Result type
  f 5 x : α  (if f returns element)
```

---

## Type-in-Type Problem

### Girard's Paradox (Simplified)

```
If Type : Type, we can encode Russell's paradox:

R = { x | x ∉ x }

As a type:
  R = Σ(T:Type). (T → Empty)

Is R : R?

If R : R, then R ∉ R (by definition)
If R ∉ R, then R : R (by definition)

CONTRADICTION!

┌─────────────────────────────────────┐
│  Type : Type  leads to paradox!    │
│                                     │
│  Solution (Chapter 8):             │
│  Universe hierarchy                │
│  Type₀ : Type₁ : Type₂ : ...       │
└─────────────────────────────────────┘
```

---

## Typing Derivation Example

### For `λn:Nat. λv:Vec n α. v`

```
                           v : Vec n α ∈ Γ
                          ─────────────────
                          Γ ⊢ v : Vec n α
              ───────────────────────────────────────────
              {n:Nat} ⊢ λv:Vec n α. v : Vec n α → Vec n α
    ─────────────────────────────────────────────────────────────
    {} ⊢ λn:Nat. λv:Vec n α. v : Π(n:Nat). Vec n α → Vec n α

Where Γ = {n:Nat, v:Vec n α}
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│                   DEPENDENT TYPES                           │
├─────────────────────────────────────────────────────────────┤
│  UNIFIED SYNTAX                                             │
│    Term = Type = Kind (all one thing!)                     │
│                                                             │
│  PI TYPES (Dependent Functions)                             │
│    Π(x:A). B    where B may contain x                      │
│    A → B = Π(_:A). B  (non-dependent)                      │
│                                                             │
│  SIGMA TYPES (Dependent Pairs)                              │
│    Σ(x:A). B    where B may contain x                      │
│    A × B = Σ(_:A). B  (non-dependent)                      │
│                                                             │
│  CURRY-HOWARD                                               │
│    Propositions = Types                                     │
│    Proofs = Terms                                          │
│    ∀x.P(x) = Π(x:A). P x                                   │
│    ∃x.P(x) = Σ(x:A). P x                                   │
│                                                             │
│  TYPE EQUALITY                                              │
│    Via normalization (β-reduction)                         │
└─────────────────────────────────────────────────────────────┘
```
