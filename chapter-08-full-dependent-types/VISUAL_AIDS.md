# Chapter 8: Visual Aids

## Universe Hierarchy

### The Problem with Type:Type

```
INCONSISTENT:                    CONSISTENT:
     Type                         Type 2
       │                            │
       │ : (has type)               │ :
       ▼                            ▼
     Type                         Type 1
                                    │
                                    │ :
                                    ▼
  Allows paradox!                 Type 0
                                    │
                                    │ :
                                    ▼
                                   Nat, Bool, ...
```

### Universe Levels

```
┌──────────────────────────────────────────────────────────┐
│  Level    Contains               Example                 │
├──────────────────────────────────────────────────────────┤
│  Type 0   Small types           Nat, Bool, Nat→Nat      │
│  Type 1   Type 0 and large      Type 0, Π(A:Type 0).A   │
│  Type 2   Type 1 and larger     Type 1, Π(A:Type 1).A   │
│  Type n   Type (n-1)...         ...                     │
└──────────────────────────────────────────────────────────┘

Rule: Type i : Type (i+1)
```

### Cumulativity

```
If A : Type i, then A : Type j (for j > i)

          Type 2
         /      \
      Type 1   Nat (lifted)
      /    \
  Type 0   Nat
    │
   Nat

Nat : Type 0
Nat : Type 1  (by cumulativity)
Nat : Type 2  (by cumulativity)
```

---

## Propositional Equality

### The Eq Type

```
Eq : (A : Type) → A → A → Type

Eq A x y  =  "x equals y in type A"

      Eq
     /│\
    A x y

Only constructor:
  refl : (x : A) → Eq A x x

        refl
         │
         x

"x equals itself" is the only way to construct equality
```

### Equality Proofs

```
refl 5 : Eq Nat 5 5        ✓ (5 = 5)
refl true : Eq Bool true true    ✓

??? : Eq Nat 3 5           ✗ (cannot construct!)
```

### Symmetry

```
sym : Eq A x y → Eq A y x

Given:
  p : Eq A x y    (proof that x = y)

Return:
  sym p : Eq A y x    (proof that y = x)

Visually:
     x ═══════ y        y ═══════ x
         p        →         sym p
```

### Transitivity

```
trans : Eq A x y → Eq A y z → Eq A x z

Given:
  p : x = y
  q : y = z

Return:
  trans p q : x = z

Visually:
  x ═══ y ═══ z
     p     q
        │
        ▼
  x ═══════════ z
     trans p q
```

### Congruence

```
cong : (f : A → B) → Eq A x y → Eq B (f x) (f y)

Given:
  f : A → B
  p : x = y

Return:
  cong f p : f x = f y

Visually:
       x ════════ y
           p
           │
    f      │      f
    │      ▼      │
    ▼             ▼
   f x ═══════ f y
      cong f p
```

---

## The J Eliminator

### Concept

```
J : To prove P for all equalities,
    it suffices to prove P for reflexivity.

Why? Every equality proof is "morally" refl!

  ┌─────────────────────────────────────────────┐
  │  If you can prove P(x, x, refl x)          │
  │  for arbitrary x,                           │
  │                                             │
  │  then you get P(x, y, p)                   │
  │  for any p : Eq x y                        │
  └─────────────────────────────────────────────┘
```

### Type Signature

```
J : Π(A : Type).
    Π(P : Π(x y : A). Eq A x y → Type).
    (Π(x : A). P x x (refl x)) →
    Π(x y : A). Π(p : Eq A x y). P x y p

Unpacked:
  A     : the type we're working with
  P     : what we want to prove (depends on equality)
  base  : proof for reflexivity case
  x, y  : the two values
  p     : proof they're equal
  ─────
  result: P x y p  (what we wanted!)
```

### Example: Proving Symmetry with J

```
sym : Π(A:Type). Π(x y:A). Eq A x y → Eq A y x

Using J:
  A = A
  P = λx y p. Eq A y x
  base = λx. refl x : Π(x:A). Eq A x x

  J A P base x y p : Eq A y x
```

---

## Inductive Families

### Vec (Vectors)

```
data Vec (A : Type) : Nat → Type where
  nil  : Vec A 0
  cons : (n : Nat) → A → Vec A n → Vec A (suc n)

                   Vec A
                   /   \
                  /     \
               nil     cons
                │      / | \
             Vec A 0  n  a  as
                         │   │
                         │   └── Vec A n
                         │        │
                         └────────┴──► Vec A (suc n)
```

### Fin (Finite Sets)

```
data Fin : Nat → Type where
  fzero : Fin (suc n)
  fsuc  : Fin n → Fin (suc n)

Fin n = {0, 1, 2, ..., n-1}

Fin 0 = {}           (empty!)
Fin 1 = {fzero}
Fin 2 = {fzero, fsuc fzero}
Fin 3 = {fzero, fsuc fzero, fsuc (fsuc fzero)}

       Fin 3
      /  |  \
     0   1   2
```

### Safe Indexing

```
lookup : Π(A:Type). Π(n:Nat). Vec A n → Fin n → A

The types guarantee safety!

  Vec A 3 = [a, b, c]
  Fin 3 = {0, 1, 2}

  lookup A 3 [a,b,c] 0 = a  ✓
  lookup A 3 [a,b,c] 1 = b  ✓
  lookup A 3 [a,b,c] 2 = c  ✓

  lookup A 3 [a,b,c] 3 = ???
                        ↑
                   Fin 3 has no 3!
                   Cannot construct this call!
```

---

## Pattern Matching with Dependent Types

### Dependent Elimination

```
case v : Vec A (suc n) of
  cons m x xs → ...

In this branch:
  - m : Nat
  - x : A
  - xs : Vec A m
  - Constraint: suc m = suc n, so m = n
  - Therefore: xs : Vec A n

The pattern match refines the type!
```

### Example: Safe Tail

```
tail : Π(A:Type). Π(n:Nat). Vec A (suc n) → Vec A n

tail A n (cons .n x xs) = xs

          cons .n x xs : Vec A (suc n)
                    │
                    └── xs : Vec A n  (exactly what we need!)
```

---

## Type-Level Computation

### Plus at Type Level

```
plus : Nat → Nat → Nat
plus 0 n = n
plus (suc m) n = suc (plus m n)

Vec A (plus 2 3) normalizes to Vec A 5

     plus 2 3
         │
         ▼  plus (suc 1) 3
     suc (plus 1 3)
         │
         ▼  plus (suc 0) 3
     suc (suc (plus 0 3))
         │
         ▼  plus 0 3
     suc (suc 3)
         │
         ▼
         5
```

### Append with Type Proof

```
append : Π(A:Type). Π(m n:Nat).
         Vec A m → Vec A n → Vec A (plus m n)

append A 0 n nil ys = ys
  -- plus 0 n = n ✓

append A (suc m) n (cons .m x xs) ys =
  cons (plus m n) x (append A m n xs ys)
  -- plus (suc m) n = suc (plus m n) ✓
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│              FULL DEPENDENT TYPES                           │
├─────────────────────────────────────────────────────────────┤
│  UNIVERSES                                                  │
│    Type 0 : Type 1 : Type 2 : ...                          │
│    No Type : Type (avoids paradox)                         │
│                                                             │
│  EQUALITY                                                   │
│    Eq : (A:Type) → A → A → Type                            │
│    refl : (x:A) → Eq A x x                                 │
│    J : ... → Π(x y:A). Eq A x y → P x y                    │
│                                                             │
│  INDUCTIVE FAMILIES                                         │
│    Vec : Type → Nat → Type                                 │
│    Fin : Nat → Type                                        │
│                                                             │
│  KEY PROPERTIES                                             │
│    - Consistent (no paradoxes)                             │
│    - Types as propositions                                 │
│    - Programs as proofs                                    │
│    - Foundation for verified programming                   │
└─────────────────────────────────────────────────────────────┘
```
