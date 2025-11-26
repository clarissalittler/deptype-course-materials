# Chapter 8 Review Cards: Full Dependent Types

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: Equality Types
**Q:** What is the equality type (propositional equality)? Define it.

<details>
<summary>Answer</summary>

```
data Eq : (A : Type) → A → A → Type where
  Refl : (x : A) → Eq A x x
```

`Eq A x y` is a type — inhabited if x = y, empty otherwise.

- `Refl x : Eq A x x` — reflexivity proof
- If you have `p : Eq A x y`, then x and y are provably equal
</details>

---

### Card 2: J Eliminator
**Q:** What is the J eliminator? Why is it important?

<details>
<summary>Answer</summary>

**J**: The elimination principle for equality.

```
J : (A : Type)
  → (P : (x y : A) → Eq A x y → Type)
  → ((x : A) → P x x (Refl x))
  → (x y : A) → (p : Eq A x y) → P x y p
```

"If P holds for Refl, it holds for any equality proof"

J is the ONLY way to use an equality proof! It embodies the fact that Refl is the only equality constructor.
</details>

---

### Card 3: Transport
**Q:** What is transport? Derive it from J.

<details>
<summary>Answer</summary>

**Transport**: If `x = y`, convert `P x` to `P y`.

```
transport : (P : A → Type) → Eq A x y → P x → P y
transport P (Refl x) px = px
```

Or via J:
```
transport P p = J A (λx y _. P x → P y) (λx. id) x y p
```

Key idea: Equal things can be substituted.
</details>

---

### Card 4: Symmetry Proof
**Q:** Prove symmetry of equality: if x = y then y = x.

<details>
<summary>Answer</summary>

```
sym : Eq A x y → Eq A y x
sym (Refl x) = Refl x
```

Pattern matching on Refl reveals x = y, so Refl x works for both Eq A x x cases.

Or via J:
```
sym = J A (λx y _. Eq A y x) (λx. Refl x) x y
```
</details>

---

### Card 5: Transitivity Proof
**Q:** Prove transitivity: if x = y and y = z, then x = z.

<details>
<summary>Answer</summary>

```
trans : Eq A x y → Eq A y z → Eq A x z
trans (Refl x) (Refl _) = Refl x
```

Both equalities force all three to be the same.

Or:
```
trans : Eq A x y → Eq A y z → Eq A x z
trans p q = transport (Eq A x) q p
```

Use q to transport p from `Eq A x y` to `Eq A x z`.
</details>

---

### Card 6: Congruence
**Q:** Prove congruence: if x = y then f(x) = f(y).

<details>
<summary>Answer</summary>

```
cong : (f : A → B) → Eq A x y → Eq B (f x) (f y)
cong f (Refl x) = Refl (f x)
```

Functions preserve equality.

This is essential for rewriting under function applications.
</details>

---

### Card 7: Uniqueness of Identity Proofs
**Q:** What is UIP (Uniqueness of Identity Proofs)?

<details>
<summary>Answer</summary>

**UIP**: All proofs of the same equality are equal.

```
UIP : (p q : Eq A x y) → Eq (Eq A x y) p q
```

In other words: for any x = y, there's only ONE proof up to equality.

**Note**: UIP is NOT provable in plain MLTT! It's an axiom (or consequence of axiom K).
</details>

---

### Card 8: Axiom K
**Q:** What is Axiom K? How does it relate to UIP?

<details>
<summary>Answer</summary>

**Axiom K**: All proofs of x = x are equal to Refl.

```
K : (p : Eq A x x) → Eq (Eq A x x) p (Refl x)
```

K + J implies UIP.

Axiom K is rejected in HoTT because it conflicts with univalence.
</details>

---

### Card 9: Heterogeneous Equality
**Q:** What is heterogeneous equality? Why is it useful?

<details>
<summary>Answer</summary>

**Heterogeneous equality**: Equality between different types.

```
data HEq : (A : Type) → A → (B : Type) → B → Type where
  HRefl : HEq A x A x
```

Useful when types depend on values you're proving equal:
```
-- If n = m, we might want to say
-- v : Vec n A is "equal" to w : Vec m A
```
</details>

---

### Card 10: Induction Principles
**Q:** What is an induction principle? Give example for Nat.

<details>
<summary>Answer</summary>

**Induction principle**: How to prove properties of all values of a type.

```
natInd : (P : Nat → Type)
       → P Zero
       → ((n : Nat) → P n → P (Succ n))
       → (n : Nat) → P n
```

To prove P holds for all Nat:
1. Prove P Zero (base case)
2. Prove P n → P (Succ n) (inductive step)
3. Then P n holds for all n
</details>

---

### Card 11: Proof of plus_zero_right
**Q:** Prove n + 0 = n (by induction).

<details>
<summary>Answer</summary>

```
plus_zero_right : (n : Nat) → Eq Nat (plus n Zero) n
plus_zero_right Zero = Refl Zero
plus_zero_right (Succ n) =
  cong Succ (plus_zero_right n)
```

Base: `plus Zero Zero = Zero` by definition, so `Refl Zero`.

Step: `plus (Succ n) Zero = Succ (plus n Zero)`. Need `Succ (plus n Zero) = Succ n`. By IH, `plus n Zero = n`, apply `cong Succ`.
</details>

---

### Card 12: Universe Polymorphism
**Q:** What is universe polymorphism? Why is it needed?

<details>
<summary>Answer</summary>

**Universe polymorphism**: Abstracting over universe levels.

```
id : {l : Level} → (A : Type l) → A → A
id x = x
```

Without it, you'd need:
```
id₀ : (A : Type₀) → A → A
id₁ : (A : Type₁) → A → A
...
```

Universe polymorphism avoids duplicating definitions for each level.
</details>

---

### Card 13: Proof Irrelevance
**Q:** What is proof irrelevance? How is it achieved?

<details>
<summary>Answer</summary>

**Proof irrelevance**: Multiple proofs of the same proposition are indistinguishable.

Achieved via:
1. **Prop universe** (Coq): Types in Prop have at most one inhabitant
2. **Squash types**: `||A||` has one value if A is inhabited
3. **Axiom**: Assert all proofs equal

```
irr : (p q : P) → p = q  -- When P is proof-irrelevant
```

Enables: erasure, program extraction, efficiency.
</details>

---

### Card 14: Definitional vs Propositional Equality
**Q:** What's the difference between definitional and propositional equality?

<details>
<summary>Answer</summary>

**Definitional equality (≡)**: Types that are equal by computation.
- Checked by type checker automatically
- `2 + 2 ≡ 4` (by evaluation)
- No proof term needed

**Propositional equality (=)**: Equality we prove.
- `Eq A x y` is a type
- Requires explicit proof term
- `plus n 0 = n` needs proof by induction

Definitional → propositional (Refl), but not vice versa.
</details>

---

### Card 15: Dependent Elimination
**Q:** What is the general form of a dependent eliminator?

<details>
<summary>Answer</summary>

For data type D with constructors c₁, ..., cₙ:

```
D-elim : (P : D → Type)
       → (method for c₁)
       → ...
       → (method for cₙ)
       → (d : D) → P d
```

Each method handles one constructor, preserving type refinements.

Example (List):
```
list-elim : (P : List A → Type)
          → P Nil
          → ((x : A) → (xs : List A) → P xs → P (Cons x xs))
          → (l : List A) → P l
```
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. `Refl x : Eq A ___ ___`
2. `transport P eq px` converts `P x` to `P ___`
3. To prove `n + 0 = n`, we use ___
4. J eliminator: if property holds for ___, it holds for all equality proofs
5. UIP says all proofs of `x = y` are ___

<details>
<summary>Answers</summary>

1. `x x` (reflexivity: x = x)
2. `y` (where eq : Eq A x y)
3. induction on n
4. Refl
5. equal
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
