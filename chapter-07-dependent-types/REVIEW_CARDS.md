# Chapter 7 Review Cards: Dependent Types

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: What are Dependent Types?
**Q:** What makes types "dependent"?

<details>
<summary>Answer</summary>

**Dependent types**: Types that depend on **values**.

```
Vec : Nat → Type → Type
Vec 3 Int  -- Vector of exactly 3 integers
```

The TYPE varies based on a VALUE (the number 3).

This is the key distinction from System Fω where types only depend on other types.
</details>

---

### Card 2: Pi Types
**Q:** What is a Pi type (Π)? How does it generalize function types?

<details>
<summary>Answer</summary>

**Pi type** `Π(x:A). B(x)`: Dependent function type

- Parameter: `x` of type `A`
- Return type: `B(x)` which can mention `x`

Regular function `A → B` is special case where B doesn't use x:
```
A → B = Π(_:A). B
```

Example: `Π(n:Nat). Vec n Int` — return type depends on input!
</details>

---

### Card 3: Sigma Types
**Q:** What is a Sigma type (Σ)? How does it generalize pairs?

<details>
<summary>Answer</summary>

**Sigma type** `Σ(x:A). B(x)`: Dependent pair type

- First component: `x` of type `A`
- Second component: type `B(x)` depends on first!

Regular pair `A × B` is special case:
```
A × B = Σ(_:A). B
```

Example: `Σ(n:Nat). Vec n Int` — pair of length and vector of that length.
</details>

---

### Card 4: Vec Type
**Q:** Define the Vec (length-indexed vector) type.

<details>
<summary>Answer</summary>

```
data Vec : Nat → Type → Type where
  Nil  : Vec 0 a
  Cons : a → Vec n a → Vec (n+1) a
```

Properties:
- `Nil` has length 0
- `Cons` adds 1 to length
- Type tracks exact length!

Example: `Cons 1 (Cons 2 Nil) : Vec 2 Nat`
</details>

---

### Card 5: Safe Head
**Q:** Write a type for safe `head` that can't be called on empty vectors.

<details>
<summary>Answer</summary>

```
head : Vec (n+1) a → a
```

Or equivalently:
```
head : Π(n:Nat). Vec (Succ n) a → a
```

Since the type requires `n+1` (at least 1), you **can't pass an empty vector**.

The compiler rejects `head Nil` — no runtime check needed!
</details>

---

### Card 6: Fin Type
**Q:** What is the Fin type? What is it used for?

<details>
<summary>Answer</summary>

**Fin n**: Type of numbers less than n (finite set {0, 1, ..., n-1})

```
data Fin : Nat → Type where
  FZero : Fin (n+1)           -- 0 < n+1
  FSucc : Fin n → Fin (n+1)   -- if i < n, then i+1 < n+1
```

Use: Safe array indexing!
```
index : Vec n a → Fin n → a
```

`Fin n` guarantees the index is in bounds.
</details>

---

### Card 7: Type-Level Computation
**Q:** How does `append` demonstrate type-level computation?

<details>
<summary>Answer</summary>

```
append : Vec m a → Vec n a → Vec (m + n) a
```

The return type `m + n` is **computed** at the type level!

```
append : Vec 2 Int → Vec 3 Int → Vec 5 Int
```

The type checker must compute `2 + 3 = 5`. Types are computed, not just declared.
</details>

---

### Card 8: Curry-Howard for Pi
**Q:** What logical concept corresponds to Pi types under Curry-Howard?

<details>
<summary>Answer</summary>

**Pi type = Universal quantification (∀)**

```
Π(x:A). B(x) ↔ ∀x:A. B(x)
```

A function of type `Π(x:A). B(x)` is a proof that "for all x in A, B(x) holds."

Example:
```
all_succ_positive : Π(n:Nat). IsPositive (succ n)
```
is a proof that all successors are positive.
</details>

---

### Card 9: Curry-Howard for Sigma
**Q:** What logical concept corresponds to Sigma types under Curry-Howard?

<details>
<summary>Answer</summary>

**Sigma type = Existential quantification (∃)**

```
Σ(x:A). B(x) ↔ ∃x:A. B(x)
```

A pair of type `Σ(x:A). B(x)` is a proof that "there exists an x in A such that B(x)."

Example:
```
(4, refl) : Σ(n:Nat). IsEven n
```
is proof that there exists an even number (namely 4).
</details>

---

### Card 10: Universe Hierarchy
**Q:** What is Type:Type problematic? What's the solution?

<details>
<summary>Answer</summary>

**Type:Type is inconsistent!** (Girard's paradox)

If `Type : Type`, you can construct logical paradoxes.

**Solution**: Universe hierarchy
```
Type₀ : Type₁ : Type₂ : Type₃ : ...
```

- `Nat : Type₀`
- `Type₀ : Type₁`
- Each level can only talk about lower levels
</details>

---

### Card 11: Dependent Pattern Matching
**Q:** How does pattern matching work with dependent types?

<details>
<summary>Answer</summary>

Pattern matching refines types in each branch:

```
head : Vec (n+1) a → a
head (Cons x xs) = x
-- No Nil case needed! Type says n+1, so can't be 0
```

When matching `Cons`, the type checker learns:
- Input is `Vec (Succ m) a` for some m
- This refines what's possible in the branch
</details>

---

### Card 12: With Abstraction
**Q:** What is "with" abstraction? Why is it needed?

<details>
<summary>Answer</summary>

**With abstraction**: Pattern match on intermediate results.

```agda
filter : (a → Bool) → Vec n a → Σ(m:Nat). Vec m a
filter p Nil = (0, Nil)
filter p (Cons x xs) with p x | filter p xs
...                     | true  | (m, ys) = (m+1, Cons x ys)
...                     | false | (m, ys) = (m, ys)
```

Needed because result type depends on runtime value (`p x`).
</details>

---

### Card 13: Singleton Types
**Q:** What is a singleton type? Give an example.

<details>
<summary>Answer</summary>

**Singleton type**: Type with exactly one inhabitant.

```haskell
data SNat : Nat → Type where
  SZero : SNat Zero
  SSucc : SNat n → SNat (Succ n)
```

`SNat n` has exactly one value for each `n`:
- `SNat 0` → only `SZero`
- `SNat 1` → only `SSucc SZero`
- etc.

Use: Runtime witness of a type-level value.
</details>

---

### Card 14: Proof Relevance
**Q:** What's the difference between proof-relevant and proof-irrelevant types?

<details>
<summary>Answer</summary>

**Proof-relevant**: Different proofs are distinguishable
```
-- Two different proofs of Even 4:
proof1 = Even_SS (Even_SS Even_Z)
proof2 = ... (some other proof)
```

**Proof-irrelevant**: All proofs are considered equal
```
-- In Prop universe (Coq) or with Squash:
all proofs of Even 4 are equal
```

Irrelevance enables erasure at runtime!
</details>

---

### Card 15: Decidable Equality
**Q:** What is decidable equality? How is it expressed with dependent types?

<details>
<summary>Answer</summary>

**Decidable equality**: For any a, b, we can decide if a = b.

```
DecEq : (a : A) → (b : A) → Either (a = b) (Not (a = b))
```

Either:
- `Left refl` : proof they're equal
- `Right proof` : proof they're different

Not all types have decidable equality (e.g., functions).
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. Pi type `Π(x:A). B` when B doesn't mention x simplifies to: ___
2. `Vec 0 Int` can only have value: ___
3. `Fin 3` represents: ___
4. `head : Vec (n+1) a → a` prevents: ___
5. Sigma type `Σ(x:A). B(x)` corresponds to logic: ___

<details>
<summary>Answers</summary>

1. `A → B` (regular function type)
2. `Nil`
3. {0, 1, 2} (numbers less than 3)
4. calling head on empty vector
5. ∃ (existential quantification)
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
