# Chapter 5 Review Cards: System F (Polymorphic Lambda Calculus)

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: What is System F?
**Q:** What does System F add to STLC?

<details>
<summary>Answer</summary>

System F adds **explicit type abstraction and application**:

- `Λα. e` — Type abstraction (take a type as parameter)
- `e [τ]` — Type application (apply term to a type)

This enables **parametric polymorphism** — writing code that works for any type.
</details>

---

### Card 2: Type Abstraction
**Q:** What is the typing rule for type abstraction (Λ)?

<details>
<summary>Answer</summary>

```
Γ ⊢ e : τ    (α not free in Γ)
────────────────────────────── T-TAbs
     Γ ⊢ Λα. e : ∀α. τ
```

Conditions:
- Type variable α must not be free in context Γ
- Abstracts over a type variable in the body
- Creates a universally quantified type
</details>

---

### Card 3: Type Application
**Q:** What is the typing rule for type application?

<details>
<summary>Answer</summary>

```
Γ ⊢ e : ∀α. τ
─────────────────── T-TApp
Γ ⊢ e [σ] : τ[α := σ]
```

- Apply a polymorphic term to a concrete type
- Substitute the type variable with the actual type
- `e [σ]` reads "e instantiated at type σ"
</details>

---

### Card 4: Polymorphic Identity
**Q:** Write the polymorphic identity function in System F.

<details>
<summary>Answer</summary>

```
id = Λα. λx:α. x
```

Type: `∀α. α → α`

Usage:
- `id [Int] 5` → `5`
- `id [Bool] true` → `true`

Explicit type application tells which type to use.
</details>

---

### Card 5: Church Booleans in System F
**Q:** Define Church booleans with their System F types.

<details>
<summary>Answer</summary>

```
true  = Λα. λt:α. λf:α. t  : ∀α. α → α → α
false = Λα. λt:α. λf:α. f  : ∀α. α → α → α
```

Type `∀α. α → α → α` says:
"For any type α, given two α values, returns an α"

Usage: `true [Int] 1 2` → `1`
</details>

---

### Card 6: Church Naturals in System F
**Q:** What is the System F type of Church numerals?

<details>
<summary>Answer</summary>

```
Nat = ∀α. (α → α) → α → α
```

Church numeral n = "apply function n times":
```
zero = Λα. λf:α→α. λz:α. z
one  = Λα. λf:α→α. λz:α. f z
two  = Λα. λf:α→α. λz:α. f (f z)
```

Instantiate to use: `two [Int] (+1) 0` → `2`
</details>

---

### Card 7: Parametricity
**Q:** What is parametricity? What does it guarantee?

<details>
<summary>Answer</summary>

**Parametricity**: Polymorphic functions can't inspect their type parameters.

A function `f : ∀α. α → α` must work uniformly for ALL types.

Consequences (free theorems):
- `f : ∀α. α → α` must be identity
- `f : ∀α. α → α → α` must return one of its arguments
- `f : ∀α. [α] → [α]` can only reorder/drop elements, not create new ones
</details>

---

### Card 8: Free Theorems
**Q:** What can you deduce about `f : ∀α. [α] → [α]`?

<details>
<summary>Answer</summary>

**Free theorem**: For any function `g : A → B`:
```
map g ∘ f = f ∘ map g
```

This means `f` can only:
- Reorder elements
- Drop elements
- Duplicate elements
- Return empty list

It CANNOT:
- Create new elements
- Inspect element values
</details>

---

### Card 9: Impredicativity
**Q:** What makes System F impredicative?

<details>
<summary>Answer</summary>

**Impredicative**: ∀ types can quantify over ALL types, including themselves.

```
∀α. α → α
```

Here α can be instantiated to `∀β. β → β` itself!

```
id [∀α. α → α] id
```

This self-reference makes type inference undecidable.
</details>

---

### Card 10: System F vs HM
**Q:** What's the key difference between System F and Hindley-Milner?

<details>
<summary>Answer</summary>

| System F | Hindley-Milner |
|----------|----------------|
| Explicit type abstraction | Implicit generalization |
| Explicit type application | Implicit instantiation |
| ∀ anywhere in types | ∀ only at top level |
| Impredicative | Predicative |
| Type checking decidable | Type inference decidable |
| Full System F | Restricted subset |
</details>

---

### Card 11: Encoding Products
**Q:** How can pairs be encoded in System F?

<details>
<summary>Answer</summary>

```
Pair A B = ∀α. (A → B → α) → α
```

Constructor:
```
pair = Λα. Λβ. λa:α. λb:β. Λγ. λf:α→β→γ. f a b
```

Projections:
```
fst p = p [A] (λa. λb. a)
snd p = p [B] (λa. λb. b)
```
</details>

---

### Card 12: Encoding Sums
**Q:** How can Either/sums be encoded in System F?

<details>
<summary>Answer</summary>

```
Either A B = ∀α. (A → α) → (B → α) → α
```

Constructors:
```
left  = Λα. Λβ. λa:α. Λγ. λl:α→γ. λr:β→γ. l a
right = Λα. Λβ. λb:β. Λγ. λl:α→γ. λr:β→γ. r b
```

Pattern matching via elimination:
```
case e of left a → e1 | right b → e2
= e [C] (λa. e1) (λb. e2)
```
</details>

---

### Card 13: Existential Types
**Q:** What is an existential type? How is it encoded?

<details>
<summary>Answer</summary>

**Existential type** `∃α. τ`: "There exists some type α such that..."

Encoding via double negation:
```
∃α. τ = ∀β. (∀α. τ → β) → β
```

Use cases:
- Abstract data types
- Information hiding
- Packages with hidden implementation
</details>

---

### Card 14: System F Strong Normalization
**Q:** Is System F strongly normalizing? What does this mean?

<details>
<summary>Answer</summary>

**Yes**, System F is strongly normalizing.

Meaning:
- Every well-typed term reduces to a normal form
- No infinite reduction sequences
- Self-application `(λx. x x)` is NOT typeable

Trade-off: Can't express all computable functions (like HM/STLC).

Proof: Girard's proof using reducibility candidates.
</details>

---

### Card 15: Type Application Reduction
**Q:** How does type application reduce?

<details>
<summary>Answer</summary>

```
(Λα. e) [τ] → e[α := τ]
```

Substitute τ for α in the body e.

Example:
```
(Λα. λx:α. x) [Int]
→ λx:Int. x
```

This is analogous to beta-reduction but at the type level.
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. Type of `Λα. λx:α. x`: ___
2. `id [Int] 5` where `id = Λα. λx:α. x` reduces to: ___
3. Church boolean type: ___
4. System F is impredicative means: ___
5. Parametricity says `f : ∀α. α → α` must be: ___

<details>
<summary>Answers</summary>

1. `∀α. α → α`
2. `5`
3. `∀α. α → α → α`
4. ∀ can quantify over types that include ∀
5. The identity function
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
