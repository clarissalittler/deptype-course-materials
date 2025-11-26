# Chapter 3 Review Cards: STLC with Algebraic Data Types

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: What are ADTs?
**Q:** What are algebraic data types? Why "algebraic"?

<details>
<summary>Answer</summary>

**Algebraic Data Types** combine types using:
- **Sum types** (`+`): "either A or B" — like addition
- **Product types** (`×`): "both A and B" — like multiplication

The algebra: |A + B| = |A| + |B|, |A × B| = |A| × |B|

Example: `Bool = 1 + 1` (two values), `Pair A B = A × B`
</details>

---

### Card 2: Product Types
**Q:** What is a product type? Give the introduction and elimination rules.

<details>
<summary>Answer</summary>

**Product type** (A × B): Contains BOTH an A and a B

**Introduction** (pair creation):
```
Γ ⊢ e₁ : A    Γ ⊢ e₂ : B
─────────────────────────
Γ ⊢ (e₁, e₂) : A × B
```

**Elimination** (projections):
```
Γ ⊢ e : A × B          Γ ⊢ e : A × B
───────────── fst      ───────────── snd
Γ ⊢ fst e : A          Γ ⊢ snd e : B
```
</details>

---

### Card 3: Sum Types
**Q:** What is a sum type? Give the introduction rules.

<details>
<summary>Answer</summary>

**Sum type** (A + B): Contains EITHER an A or a B

**Introduction** (injection):
```
Γ ⊢ e : A                    Γ ⊢ e : B
─────────────── inl          ─────────────── inr
Γ ⊢ inl e : A + B            Γ ⊢ inr e : A + B
```

`inl` = "inject left", `inr` = "inject right"
</details>

---

### Card 4: Pattern Matching (Case)
**Q:** Write the typing rule for case/match on sum types.

<details>
<summary>Answer</summary>

```
Γ ⊢ e : A + B    Γ,x:A ⊢ e₁ : C    Γ,y:B ⊢ e₂ : C
──────────────────────────────────────────────────
       Γ ⊢ case e of inl x → e₁ | inr y → e₂ : C
```

- Scrutinee `e` has sum type A + B
- Left branch handles A case
- Right branch handles B case
- Both branches must return same type C
</details>

---

### Card 5: Unit Type
**Q:** What is the unit type? What is it useful for?

<details>
<summary>Answer</summary>

**Unit type** (written `()` or `1` or `Unit`):
- Has exactly ONE value: `()`
- The "zero-tuple" — product of nothing

Uses:
- Return type for side-effectful functions
- Placeholder when you need a type but don't care about the value
- `A → ()` means "function that doesn't return meaningful info"
</details>

---

### Card 6: Void/Empty Type
**Q:** What is the void/empty type? Can you construct a value of it?

<details>
<summary>Answer</summary>

**Void/Empty type** (written `⊥` or `0` or `Void`):
- Has **zero** values — NO constructors
- Cannot be constructed!

Uses:
- Represents impossibility
- `Void → A` is always valid (vacuously true)
- `absurd : Void → A` is the eliminator

If you have a `Void`, something went very wrong!
</details>

---

### Card 7: Maybe/Option Type
**Q:** Define the Maybe type. What is it used for?

<details>
<summary>Answer</summary>

```
Maybe A = Nothing | Just A
        = Unit + A
        = 1 + A
```

Uses:
- Representing optional values
- Safe failure (instead of null/exceptions)
- `head : List A → Maybe A` — safe head

Pattern: `case mx of Nothing → default | Just x → use x`
</details>

---

### Card 8: Either Type
**Q:** Define the Either type. How does it differ from Maybe?

<details>
<summary>Answer</summary>

```
Either A B = Left A | Right B
           = A + B
```

Unlike Maybe:
- **Maybe**: "value or nothing"
- **Either**: "value or different value"

Common use: `Either Error Result`
- `Left err` = failure with error info
- `Right val` = success with result
</details>

---

### Card 9: Recursive Types
**Q:** Define the List type as a recursive algebraic type.

<details>
<summary>Answer</summary>

```
List A = Nil | Cons A (List A)
       = Unit + (A × List A)
       = 1 + A × List A
```

Recursive: List is defined in terms of itself!

Values:
- `Nil` = empty list
- `Cons 1 (Cons 2 Nil)` = [1, 2]
</details>

---

### Card 10: Natural Numbers as ADT
**Q:** Define Nat as an algebraic data type.

<details>
<summary>Answer</summary>

```
Nat = Zero | Succ Nat
    = Unit + Nat
    = 1 + Nat
```

Values:
- `Zero` = 0
- `Succ Zero` = 1
- `Succ (Succ Zero)` = 2

This is **Peano arithmetic**!
</details>

---

### Card 11: Exhaustiveness
**Q:** What is exhaustiveness checking? Why is it important?

<details>
<summary>Answer</summary>

**Exhaustiveness**: Pattern match covers ALL cases

```haskell
-- Non-exhaustive (warning!):
f :: Maybe Int -> Int
f (Just x) = x
-- Missing: f Nothing = ???

-- Exhaustive:
f :: Maybe Int -> Int
f Nothing  = 0
f (Just x) = x
```

Important: Prevents runtime pattern match failures!
</details>

---

### Card 12: Records
**Q:** How are records related to products?

<details>
<summary>Answer</summary>

**Records** = labeled products

```haskell
-- Anonymous product:
type Person = (String, Int, Bool)

-- Record (named fields):
data Person = Person { name :: String, age :: Int, active :: Bool }
```

Benefits:
- Named fields (self-documenting)
- Field order doesn't matter
- Automatic accessor functions
</details>

---

### Card 13: Type Algebra Laws
**Q:** What algebraic laws do ADTs satisfy?

<details>
<summary>Answer</summary>

**Sum laws:**
- `A + 0 ≅ A` (Void is identity)
- `A + B ≅ B + A` (commutative)
- `(A + B) + C ≅ A + (B + C)` (associative)

**Product laws:**
- `A × 1 ≅ A` (Unit is identity)
- `A × 0 ≅ 0` (Void annihilates)
- `A × B ≅ B × A` (commutative)

**Distributive:**
- `A × (B + C) ≅ (A × B) + (A × C)`
</details>

---

### Card 14: Fold/Catamorphism
**Q:** What is a fold over a list? Write its type.

<details>
<summary>Answer</summary>

```haskell
foldr :: (A -> B -> B) -> B -> List A -> B
foldr f z Nil         = z
foldr f z (Cons x xs) = f x (foldr f z xs)
```

Fold replaces:
- `Nil` with `z`
- `Cons` with `f`

Example: `foldr (+) 0 [1,2,3] = 1 + (2 + (3 + 0)) = 6`
</details>

---

### Card 15: Binary Trees
**Q:** Define a binary tree ADT with values at leaves.

<details>
<summary>Answer</summary>

```haskell
data Tree A
  = Leaf A
  | Branch (Tree A) (Tree A)
```

Algebraic form:
```
Tree A = A + Tree A × Tree A
```

Values:
- `Leaf 5` — single value
- `Branch (Leaf 1) (Leaf 2)` — two leaves
- `Branch (Branch (Leaf 1) (Leaf 2)) (Leaf 3)` — nested
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. `Maybe A = ___ + ___`
2. `List A = ___ + A × ___`
3. Product of 3 values and 2 values has ___ values
4. Sum of 3 values and 2 values has ___ values
5. The eliminator for sum types is called: ___

<details>
<summary>Answers</summary>

1. `Unit + A` (or `1 + A`)
2. `Unit + A × List A` (or `1 + A × List A`)
3. 6 (3 × 2)
4. 5 (3 + 2)
5. `case`/`match`/pattern matching
</details>

---

## Spaced Repetition Schedule

Review these cards on this schedule:
- **Day 1**: All cards
- **Day 3**: Cards you got wrong + random 5
- **Day 7**: All cards
- **Day 14**: Cards you got wrong + random 5
- **Day 30**: All cards

Mark cards as "mastered" when you get them right 3 times in a row.
