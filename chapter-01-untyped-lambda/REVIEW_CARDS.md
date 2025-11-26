# Chapter 1 Review Cards: Untyped Lambda Calculus

Use these flashcards for spaced repetition review. Cover the answer, try to recall, then check.

---

## Core Concepts

### Card 1: Lambda Calculus Syntax
**Q:** What are the three forms of lambda calculus expressions?

<details>
<summary>Answer</summary>

1. **Variable**: `x`
2. **Abstraction** (function): `λx. e`
3. **Application**: `e₁ e₂`

That's it! All computation can be expressed with just these three forms.
</details>

---

### Card 2: What is a Redex?
**Q:** What does "redex" stand for and what is it?

<details>
<summary>Answer</summary>

**Redex** = **Red**ucible **Ex**pression

A redex is an expression of the form `(λx. e) v` — a function applied to an argument that can be reduced via beta-reduction.

Example: `(λx. x + 1) 5` is a redex that reduces to `5 + 1`.
</details>

---

### Card 3: Beta Reduction
**Q:** What is beta reduction? Write the rule.

<details>
<summary>Answer</summary>

**Beta reduction** is function application:

```
(λx. e) v → e[x := v]
```

Replace all occurrences of `x` in `e` with `v`.

Example: `(λx. x x) y → y y`
</details>

---

### Card 4: Free vs Bound Variables
**Q:** In `λx. x y`, which variables are free and which are bound?

<details>
<summary>Answer</summary>

- **`x`** is **bound** — it's declared by the λ
- **`y`** is **free** — it's not declared in this expression

A variable is bound if it appears under a λ that declares it.
</details>

---

### Card 5: Alpha Equivalence
**Q:** Are `λx. x` and `λy. y` the same? Why?

<details>
<summary>Answer</summary>

**Yes!** They are **alpha-equivalent**.

Alpha equivalence means two expressions are the same up to renaming of bound variables.

`λx. x` ≡α `λy. y` ≡α `λz. z`

They all represent the identity function.
</details>

---

### Card 6: Capture-Avoiding Substitution
**Q:** What goes wrong with naive substitution in `(λy. x)[x := y]`?

<details>
<summary>Answer</summary>

Naive substitution gives `λy. y`, which is WRONG!

The free `y` we're substituting gets "captured" by the `λy`.

**Correct approach**: Rename bound variable first:
- `λy. x` → `λz. x` (alpha conversion)
- `(λz. x)[x := y]` → `λz. y` ✓
</details>

---

### Card 7: Normal Form
**Q:** What is a normal form? Is `λx. (λy. y) x` in normal form?

<details>
<summary>Answer</summary>

A **normal form** is an expression with no redexes — it cannot be reduced further.

`λx. (λy. y) x` is **NOT** in normal form.

It contains the redex `(λy. y) x` which reduces to `x`.

Normal form: `λx. x`
</details>

---

### Card 8: Evaluation Strategies
**Q:** What's the difference between call-by-value and call-by-name?

<details>
<summary>Answer</summary>

**Call-by-value**: Evaluate argument first, then substitute
- `(λx. x) ((λy. y) z)` → first reduce inner: `(λx. x) z` → `z`

**Call-by-name**: Substitute unevaluated argument
- `(λx. x) ((λy. y) z)` → substitute: `(λy. y) z` → `z`

Both reach the same result (if they terminate), but CBN may not evaluate unused arguments.
</details>

---

### Card 9: Church Booleans
**Q:** Define Church encodings for `true` and `false`.

<details>
<summary>Answer</summary>

```
true  = λt. λf. t    (select first argument)
false = λt. λf. f    (select second argument)
```

Think of them as "if-then-else" with the condition built in:
- `true A B → A`
- `false A B → B`
</details>

---

### Card 10: Church Numerals
**Q:** How are 0, 1, 2 encoded as Church numerals?

<details>
<summary>Answer</summary>

A Church numeral n is "apply f to z, n times":

```
0 = λf. λz. z           (zero applications)
1 = λf. λz. f z         (one application)
2 = λf. λz. f (f z)     (two applications)
3 = λf. λz. f (f (f z)) (three applications)
```

Pattern: n = λf. λz. fⁿ(z)
</details>

---

### Card 11: Successor Function
**Q:** Write the successor function for Church numerals.

<details>
<summary>Answer</summary>

```
succ = λn. λf. λz. f (n f z)
```

It takes a numeral n, and returns one that applies f one more time.

Trace: `succ 2`
= `λf. λz. f (2 f z)`
= `λf. λz. f (f (f z))`
= `3` ✓
</details>

---

### Card 12: Omega Combinator
**Q:** What is Ω (omega)? What happens when you reduce it?

<details>
<summary>Answer</summary>

```
ω = λx. x x
Ω = ω ω = (λx. x x) (λx. x x)
```

Reduction:
```
(λx. x x) (λx. x x)
→ (λx. x x) (λx. x x)
→ (λx. x x) (λx. x x)
→ ... (infinite loop!)
```

Ω has no normal form — it reduces to itself forever.
</details>

---

### Card 13: Y Combinator
**Q:** What is the Y combinator used for?

<details>
<summary>Answer</summary>

The **Y combinator** enables recursion in lambda calculus:

```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

Property: `Y g = g (Y g)`

This lets you define recursive functions without naming them!

Example: factorial = Y (λf. λn. if n=0 then 1 else n * f(n-1))
</details>

---

### Card 14: De Bruijn Indices
**Q:** Convert `λx. λy. x y` to de Bruijn notation.

<details>
<summary>Answer</summary>

```
λ. λ. 1 0
```

- Count λ's between variable use and its binding
- `y` is bound by nearest λ → index 0
- `x` is bound by next λ out → index 1

Benefits: No variable names, no capture issues!
</details>

---

### Card 15: Confluence
**Q:** What does the Church-Rosser theorem guarantee?

<details>
<summary>Answer</summary>

**Confluence**: If a term can reduce in multiple ways, all paths can eventually reach the same result.

```
      t
     / \
    ↓   ↓
   t₁   t₂
    \   /
     ↓ ↓
      t'
```

This means: evaluation order doesn't affect the final result (if one exists).
</details>

---

## Quick Recall

### Rapid Fire: Complete These

1. `(λx. e) v → ___`
2. Free variables of `λx. y x` = ___
3. `true A B → ___`
4. `succ = λn. λf. λz. ___`
5. Normal form of `(λx. x) (λy. y)` = ___

<details>
<summary>Answers</summary>

1. `e[x := v]`
2. `{y}`
3. `A`
4. `f (n f z)`
5. `λy. y`
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
