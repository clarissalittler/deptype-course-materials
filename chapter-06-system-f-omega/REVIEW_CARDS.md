# Chapter 6 Review Cards: System F-omega

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: What is System Fω?
**Q:** What does System Fω add to System F?

<details>
<summary>Answer</summary>

System Fω adds **type operators** (type-level functions):

- Types that take types as arguments
- Types that return types
- Higher-kinded types

Example: `List` is not a type, it's a type operator: `* → *`
</details>

---

### Card 2: What are Kinds?
**Q:** What is a kind? Why do we need them?

<details>
<summary>Answer</summary>

**Kinds** are "types of types."

- `*` (star): Kind of ordinary types (Int, Bool, etc.)
- `* → *`: Kind of type constructors (List, Maybe)
- `* → * → *`: Kind of binary type constructors (Either, Pair)

We need kinds to classify types and prevent ill-formed types like `Int Int`.
</details>

---

### Card 3: Kind Syntax
**Q:** What are the kinds of these types?
- `Int`
- `List`
- `Either`
- `StateT`

<details>
<summary>Answer</summary>

- `Int :: *` — A proper type
- `List :: * → *` — Takes one type, returns a type
- `Either :: * → * → *` — Takes two types
- `StateT :: * → (* → *) → * → *` — Takes a type, a monad, and another type

Higher kinds: `(* → *) → *` etc.
</details>

---

### Card 4: Type Operators
**Q:** What is a type operator? Give an example.

<details>
<summary>Answer</summary>

**Type operator**: A function at the type level.

```
Pair = λα:*. λβ:*. (α, β)
Pair :: * → * → *
```

Apply like functions:
```
Pair Int Bool = (Int, Bool)
```

Type operators compute at compile time!
</details>

---

### Card 5: Type-Level Lambda
**Q:** Write a type operator that takes a type and returns a pair of it with itself.

<details>
<summary>Answer</summary>

```
Dup = λα:*. (α, α)
Dup :: * → *
```

Applications:
- `Dup Int = (Int, Int)`
- `Dup Bool = (Bool, Bool)`
- `Dup (List Int) = (List Int, List Int)`
</details>

---

### Card 6: Kinding Rules
**Q:** What is the kinding rule for type application?

<details>
<summary>Answer</summary>

```
Γ ⊢ F :: κ₁ → κ₂    Γ ⊢ A :: κ₁
───────────────────────────────── K-App
         Γ ⊢ F A :: κ₂
```

Like function application, but for types:
- F is a type operator of kind κ₁ → κ₂
- A is a type of kind κ₁
- Result F A has kind κ₂
</details>

---

### Card 7: Higher-Kinded Types
**Q:** What is a higher-kinded type? Why is it useful?

<details>
<summary>Answer</summary>

**Higher-kinded type**: A type that takes type constructors as parameters.

```haskell
class Functor (f :: * → *) where
  fmap :: (a → b) → f a → f b
```

Here `f` has kind `* → *` — it's a type constructor!

Useful for: Functors, Monads, generic programming over containers.
</details>

---

### Card 8: Functor Type
**Q:** What is the kind of Functor? Why?

<details>
<summary>Answer</summary>

```
Functor :: (* → *) → Constraint
```

Or as a type synonym:
```
Functor :: (* → *) → *
```

It takes a type constructor (like `List` or `Maybe`) and produces... well, a typeclass constraint, or you can think of it as producing a dictionary type.

The `(* → *)` shows it needs a one-argument type constructor.
</details>

---

### Card 9: Type Families
**Q:** What are type families? How do they relate to Fω?

<details>
<summary>Answer</summary>

**Type families** = Type-level functions defined by pattern matching.

```haskell
type family Add (m :: Nat) (n :: Nat) :: Nat where
  Add Zero     n = n
  Add (Succ m) n = Succ (Add m n)
```

This is type-level computation in Haskell, essentially Fω features!
</details>

---

### Card 10: Type Synonyms vs Type Families
**Q:** What's the difference between type synonyms and type families?

<details>
<summary>Answer</summary>

**Type synonyms**: Simple aliases, no computation
```haskell
type Pair a = (a, a)  -- Just textual substitution
```

**Type families**: Computed types, can branch
```haskell
type family If (b :: Bool) (t :: *) (f :: *) :: * where
  If True  t f = t
  If False t f = f
```

Type families can do actual computation!
</details>

---

### Card 11: Type-Level Natural Numbers
**Q:** How can natural numbers be represented at the type level?

<details>
<summary>Answer</summary>

```haskell
data Nat = Zero | Succ Nat  -- Promoted to kinds!

-- Type-level numbers:
type One   = Succ Zero
type Two   = Succ (Succ Zero)
type Three = Succ (Succ (Succ Zero))
```

With DataKinds, data constructors become type constructors!

`Zero :: Nat`, `Succ :: Nat → Nat` (at kind level)
</details>

---

### Card 12: Kind Polymorphism
**Q:** What is kind polymorphism?

<details>
<summary>Answer</summary>

**Kind polymorphism**: Abstracting over kinds like we abstract over types.

```haskell
type family Id (a :: k) :: k where
  Id a = a
```

Here `k` is a kind variable! Works for any kind:
- `Id Int :: *`
- `Id Maybe :: * → *`
- `Id Either :: * → * → *`
</details>

---

### Card 13: Type-Level Church Numerals
**Q:** Define Church numerals at the type level.

<details>
<summary>Answer</summary>

```
-- Kind of type-level Church numerals
TyNat :: (* → *) → * → *

Zero = λf:*→*. λz:*. z
One  = λf:*→*. λz:*. f z
Two  = λf:*→*. λz:*. f (f z)

Succ = λn:TyNat. λf:*→*. λz:*. f (n f z)
Plus = λm:TyNat. λn:TyNat. m Succ n
```

Type-level computation!
</details>

---

### Card 14: GADTs and Fω
**Q:** How do GADTs relate to System Fω?

<details>
<summary>Answer</summary>

**GADTs** allow constructors to specify return type indices:

```haskell
data Vec (n :: Nat) (a :: *) where
  Nil  :: Vec Zero a
  Cons :: a -> Vec n a -> Vec (Succ n) a
```

This uses:
- Type-level naturals (kind `Nat`)
- Type indices (the `n` parameter)
- Constrained return types

GADTs are a practical application of Fω ideas!
</details>

---

### Card 15: Lambda Cube Position
**Q:** Where does System Fω sit in the Lambda Cube?

<details>
<summary>Answer</summary>

The Lambda Cube has three axes:
- Terms depending on types (polymorphism)
- Types depending on types (type operators)
- Types depending on terms (dependent types)

```
       Fω ————— λC (CoC)
      / |      / |
     F  |     λP  |
    /   |    /    |
STLC————λω  λ→————λP
```

Fω = STLC + polymorphism + type operators

It's NOT dependent (types don't depend on terms).
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. Kind of `List`: ___
2. Kind of `* → *`: ___
3. `λα:*. (α, α)` has kind: ___
4. Type families allow type-level ___
5. Higher-kinded type parameter example: `Functor (f :: ___)`

<details>
<summary>Answers</summary>

1. `* → *`
2. It IS a kind (not a "kind of a kind")
3. `* → *`
4. computation/functions
5. `* → *`
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
