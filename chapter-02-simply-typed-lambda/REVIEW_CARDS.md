# Chapter 2 Review Cards: Simply Typed Lambda Calculus

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: Why Add Types?
**Q:** What problem do types solve that untyped lambda calculus has?

<details>
<summary>Answer</summary>

Types prevent **runtime errors** and **non-termination**:

1. **Stuck terms**: `true 5` (applying a boolean)
2. **Non-termination**: `(λx. x x)(λx. x x)` (omega)
3. **Meaningless computation**: `5 + true`

With types: these are rejected at compile time!
</details>

---

### Card 2: Function Type Syntax
**Q:** What does the type `Nat → Bool` mean?

<details>
<summary>Answer</summary>

A function that:
- **Takes**: a value of type `Nat`
- **Returns**: a value of type `Bool`

Arrow associates to the right:
`A → B → C` means `A → (B → C)`
</details>

---

### Card 3: Typing Judgment
**Q:** What does `Γ ⊢ t : τ` mean?

<details>
<summary>Answer</summary>

"Under context Γ, term t has type τ"

- **Γ** (Gamma): Type environment mapping variables to types
- **⊢**: "proves" or "entails"
- **t : τ**: term t has type τ

Example: `{x:Nat} ⊢ x + 1 : Nat`
</details>

---

### Card 4: T-Var Rule
**Q:** State the typing rule for variables.

<details>
<summary>Answer</summary>

```
x : τ ∈ Γ
────────── T-Var
Γ ⊢ x : τ
```

"If x has type τ in the context Γ, then under Γ, x has type τ"

Just look up the variable in the context!
</details>

---

### Card 5: T-Abs Rule
**Q:** State the typing rule for lambda abstractions.

<details>
<summary>Answer</summary>

```
Γ, x : τ₁ ⊢ e : τ₂
────────────────────── T-Abs
Γ ⊢ λx:τ₁. e : τ₁ → τ₂
```

To type a function:
1. Add parameter x with type τ₁ to context
2. Type the body e, get type τ₂
3. Function has type τ₁ → τ₂
</details>

---

### Card 6: T-App Rule
**Q:** State the typing rule for application.

<details>
<summary>Answer</summary>

```
Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
─────────────────────────────── T-App
        Γ ⊢ e₁ e₂ : τ₂
```

To apply e₁ to e₂:
1. e₁ must be a function from τ₁ to τ₂
2. e₂ must have type τ₁ (the input type)
3. Result has type τ₂ (the output type)
</details>

---

### Card 7: Type Derivation Tree
**Q:** Build a type derivation for `(λx:Nat. x) 5`.

<details>
<summary>Answer</summary>

```
                    x:Nat ∈ {x:Nat}
                    ──────────────── T-Var
{x:Nat} ⊢ x : Nat                      ∅ ⊢ 5 : Nat
─────────────────────── T-Abs          ─────────── T-Nat
∅ ⊢ λx:Nat. x : Nat→Nat
───────────────────────────────────────────────── T-App
              ∅ ⊢ (λx:Nat. x) 5 : Nat
```
</details>

---

### Card 8: Type Safety
**Q:** What are the two parts of type safety?

<details>
<summary>Answer</summary>

1. **Progress**: A well-typed term is either a value or can take a step
   - No "stuck" terms

2. **Preservation**: If `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`
   - Types are preserved during evaluation

Together: "Well-typed programs don't go wrong"
</details>

---

### Card 9: Base Types
**Q:** What are base types and why do we need them?

<details>
<summary>Answer</summary>

**Base types** are primitive types that aren't built from other types:
- `Nat`, `Bool`, `Int`, `String`, etc.

We need them because:
- Can't have only function types (what would functions operate on?)
- Provide "ground" for the type system
- Example: `Nat → Bool` needs both `Nat` and `Bool` as base types
</details>

---

### Card 10: Curry-Howard Correspondence
**Q:** What is the Curry-Howard correspondence for STLC?

<details>
<summary>Answer</summary>

**Types = Propositions, Programs = Proofs**

| Logic | Types |
|-------|-------|
| Proposition A | Type A |
| A implies B | A → B |
| Proof of A→B | Function from A to B |

Example: A function `f : A → B` is a proof that "if A then B"!
</details>

---

### Card 11: Untypeable Term
**Q:** Why can't `λx. x x` be typed in STLC?

<details>
<summary>Answer</summary>

If `x : τ`, then for `x x`:
- First `x` must be a function: `τ = σ → ρ`
- Second `x` must be argument: `τ = σ`

So `τ = σ → ρ` AND `τ = σ`

This means `σ = σ → ρ`, which is infinite!

No finite type can satisfy this. Self-application is untypeable.
</details>

---

### Card 12: Strong Normalization
**Q:** What does "strongly normalizing" mean for STLC?

<details>
<summary>Answer</summary>

**Every** well-typed term reduces to a normal form in **finite** steps.

- No infinite reduction sequences
- Evaluation always terminates
- No omega: `(λx. x x)(λx. x x)` isn't typeable

Trade-off: STLC can't express all computable functions (it's not Turing-complete).
</details>

---

### Card 13: Substitution Lemma
**Q:** What does the substitution lemma say?

<details>
<summary>Answer</summary>

If `Γ, x:τ₁ ⊢ e : τ₂` and `Γ ⊢ v : τ₁`

Then `Γ ⊢ e[x := v] : τ₂`

In words: Substituting a well-typed value for a variable preserves typing.

This is crucial for proving preservation!
</details>

---

### Card 14: Type Checking Algorithm
**Q:** Outline the type checking algorithm for STLC.

<details>
<summary>Answer</summary>

```haskell
typeOf ctx (Var x) = lookup x ctx
typeOf ctx (Lam x ty body) =
  let bodyTy = typeOf (extend ctx x ty) body
  in Arrow ty bodyTy
typeOf ctx (App e1 e2) =
  case typeOf ctx e1 of
    Arrow t1 t2 ->
      if typeOf ctx e2 == t1
      then t2
      else error "argument type mismatch"
    _ -> error "expected function"
```
</details>

---

### Card 15: Context Extension
**Q:** What is context shadowing?

<details>
<summary>Answer</summary>

When adding a binding that already exists:

`Γ, x:Nat, x:Bool ⊢ x : Bool`

The **innermost** binding wins. The outer `x:Nat` is "shadowed."

Example:
```
(λx:Nat. λx:Bool. x) 5 true → true : Bool
```

The inner `x` refers to `Bool`, not `Nat`.
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. `Γ ⊢ λx:τ₁. e : ___` (given `Γ,x:τ₁ ⊢ e : τ₂`)
2. Progress says: well-typed terms are ___ or can ___
3. `A → B → C` associates as: ___
4. Type of `(λx:Nat. x)`: ___
5. STLC is strongly normalizing, meaning: ___

<details>
<summary>Answers</summary>

1. `τ₁ → τ₂`
2. values, take a step
3. `A → (B → C)`
4. `Nat → Nat`
5. All well-typed terms terminate
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
