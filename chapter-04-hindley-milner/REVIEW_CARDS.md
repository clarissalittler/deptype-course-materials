# Chapter 4 Review Cards: Hindley-Milner Type Inference

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: What is Type Inference?
**Q:** What problem does type inference solve?

<details>
<summary>Answer</summary>

Type inference **automatically deduces types** without annotations.

Instead of:
```haskell
f :: Int -> Int
f (x :: Int) = (x + 1 :: Int)
```

You write:
```haskell
f x = x + 1
```

Compiler figures out `f :: Int -> Int`!
</details>

---

### Card 2: Monotypes vs Polytypes
**Q:** What's the difference between monotypes and polytypes (type schemes)?

<details>
<summary>Answer</summary>

**Monotype** (τ): No quantifiers
- `Int`, `Int → Bool`, `α → α`

**Polytype/Type Scheme** (σ): Has ∀ quantifiers
- `∀α. α → α`
- `∀α β. α → β → α`

Key rule: Only let-bound variables get polytypes!
</details>

---

### Card 3: Type Scheme Syntax
**Q:** What does `∀α β. α → β → α` mean?

<details>
<summary>Answer</summary>

"For any types α and β, this has type α → β → α"

- `∀` introduces type variables
- Can instantiate to any concrete types
- `∀α β. α → β → α` can become:
  - `Int → Bool → Int`
  - `String → Nat → String`
  - etc.
</details>

---

### Card 4: Algorithm W
**Q:** What are the main steps of Algorithm W?

<details>
<summary>Answer</summary>

For each expression:

1. **Var**: Look up in environment, instantiate fresh
2. **Lam**: Create fresh var for param, infer body
3. **App**: Infer function & arg types, unify, return result
4. **Let**: Infer binding, generalize, add to env, infer body

Key operations: **fresh variables**, **unification**, **generalization**
</details>

---

### Card 5: Unification
**Q:** What is unification? Give an example.

<details>
<summary>Answer</summary>

**Unification**: Find substitution making two types equal.

Example: Unify `α → Int` with `Bool → β`
- α = Bool
- β = Int
- Substitution: [α ↦ Bool, β ↦ Int]

Result: Both become `Bool → Int`
</details>

---

### Card 6: Unification Algorithm
**Q:** How does unification handle the main cases?

<details>
<summary>Answer</summary>

```
unify(α, τ) = [α ↦ τ]     (if α ∉ FV(τ))
unify(τ, α) = [α ↦ τ]     (if α ∉ FV(τ))
unify(τ₁→τ₂, σ₁→σ₂) =
  let S₁ = unify(τ₁, σ₁)
      S₂ = unify(S₁(τ₂), S₁(σ₂))
  in S₂ ∘ S₁
unify(C, C) = []          (same base type)
unify(_, _) = error       (everything else)
```
</details>

---

### Card 7: Occurs Check
**Q:** What is the occurs check? Why is it needed?

<details>
<summary>Answer</summary>

**Occurs check**: When unifying `α` with `τ`, verify `α ∉ FV(τ)`

Without it, unifying `α` with `α → Int` gives:
```
α = α → Int = (α → Int) → Int = ...
```

Infinite type! The occurs check prevents this.

Error: "Cannot construct infinite type"
</details>

---

### Card 8: Generalization
**Q:** When and how do we generalize types?

<details>
<summary>Answer</summary>

**When**: At `let` bindings (not lambda parameters!)

**How**: Quantify over free type variables not in environment

```
generalize(Γ, τ) = ∀(FV(τ) - FV(Γ)). τ
```

Example:
- `Γ = {x : Int}`
- `τ = α → Int`
- `FV(τ) - FV(Γ) = {α}`
- Result: `∀α. α → Int`
</details>

---

### Card 9: Instantiation
**Q:** What is instantiation? When does it happen?

<details>
<summary>Answer</summary>

**Instantiation**: Replace quantified vars with fresh type vars.

When: Looking up a polymorphic variable

```
instantiate(∀α β. α → β → α) = τ₁ → τ₂ → τ₁
```
(where τ₁, τ₂ are fresh)

This allows `id` to be used at different types in same expression!
</details>

---

### Card 10: Let Polymorphism
**Q:** Why can `let id = λx.x in (id 1, id true)` work, but not `(λid. (id 1, id true))(λx.x)`?

<details>
<summary>Answer</summary>

**Let** generalizes: `id : ∀α. α → α`
- Each use instantiates fresh: `id : Int → Int`, `id : Bool → Bool`

**Lambda** doesn't generalize: `id : τ` (some unknown type)
- Must pick ONE type for both uses
- Can't be both `Int → Int` and `Bool → Bool`

This is the **let-polymorphism** distinction!
</details>

---

### Card 11: Principal Types
**Q:** What is a principal type? Does HM always find it?

<details>
<summary>Answer</summary>

**Principal type**: Most general type for an expression

Example: `λx. x` has principal type `∀α. α → α`
- More general than `Int → Int` or `Bool → Bool`
- All other valid types are instances

**Yes!** Algorithm W always finds the principal type (when one exists).

This is the **Principal Type Property**.
</details>

---

### Card 12: Substitution Composition
**Q:** How do you compose substitutions?

<details>
<summary>Answer</summary>

`(S₂ ∘ S₁)(τ) = S₂(S₁(τ))`

Apply S₁ first, then S₂.

When composing:
```
S₂ ∘ S₁ = S₂ ∪ {α ↦ S₂(τ) | α ↦ τ ∈ S₁}
```

S₂'s bindings take precedence, but apply S₂ to S₁'s results.
</details>

---

### Card 13: Type Inference Example
**Q:** Trace type inference for `λf. λx. f x`.

<details>
<summary>Answer</summary>

```
1. λf: fresh α₀ for f
2. λx: fresh α₁ for x
3. f x:
   - f : α₀
   - x : α₁
   - fresh α₂ for result
   - unify(α₀, α₁ → α₂) → [α₀ ↦ α₁ → α₂]
   - result: α₂
4. Build:
   - inner λ: α₁ → α₂
   - outer λ: (α₁ → α₂) → α₁ → α₂

Final: ∀α₁ α₂. (α₁ → α₂) → α₁ → α₂
```
</details>

---

### Card 14: Monomorphism Restriction
**Q:** What is the monomorphism restriction?

<details>
<summary>Answer</summary>

**Monomorphism restriction**: Don't generalize bindings that look like values but might compute.

```haskell
-- This might not be generalized:
f = expensive_computation
```

Why: If `f : ∀α. α`, it would recompute for each use!

Haskell applies this by default (can disable with NoMonomorphismRestriction).
</details>

---

### Card 15: Value Restriction
**Q:** What is the value restriction?

<details>
<summary>Answer</summary>

**Value restriction**: Only generalize syntactic values (lambdas, constructors).

```ml
(* Can generalize - it's a lambda: *)
let id = fun x -> x   (* ∀α. α → α *)

(* Can't generalize - it's an application: *)
let r = ref []        (* fixed type, not ∀α. α list ref *)
```

Why: Prevents unsoundness with mutable references.
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. Unify `α` with `Int`: ___
2. Unify `α → Bool` with `Int → β`: ___
3. Generalize `α → β` in empty context: ___
4. Instantiate `∀α. α → α` with fresh vars: ___
5. Can't unify `α` with `α → Int` because: ___

<details>
<summary>Answers</summary>

1. `[α ↦ Int]`
2. `[α ↦ Int, β ↦ Bool]`
3. `∀α β. α → β`
4. `τ₁ → τ₁` (fresh τ₁)
5. Occurs check fails (infinite type)
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
