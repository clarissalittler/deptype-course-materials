# Chapter 20: Denotational Semantics - Exercises

## Learning Objectives

After completing these exercises, you will:
- Understand the mathematical foundations of denotational semantics
- Know how to interpret syntax as mathematical objects in domains
- Understand fixed points and why they model recursion
- Be able to relate denotational and operational semantics
- Appreciate the role of continuity in semantic definitions

---

## Exercise 1: Computing Denotations (Warm-up)

Compute the denotations of the following terms by hand, showing your work:

1. `[[λx. x]] ∅` (identity function)
2. `[[(λx. suc x) 5]] ∅`
3. `[[let y = 3 in y + y]] ∅` (assuming + is defined)
4. `[[if true then 0 else 1]] ∅`

For each, write out the semantic equations used.

---

## Exercise 2: Flat Domain Drawing

Draw the Hasse diagram for the following flat domains:

1. `Bool = {⊥, true, false}`
2. `Nat = {⊥, 0, 1, 2, ...}`
3. A three-element set `Color = {⊥, red, green, blue}`

For each, indicate which elements are comparable under ⊑.

---

## Exercise 3: Function Domain Analysis

Consider the domain `Bool → Bool` of continuous functions from Bool to Bool.

1. List all the elements of this domain (there are 4).
2. Draw the partial order.
3. Which function is the least element?

**Hint:** Consider what happens on inputs ⊥, true, false.

---

## Exercise 4: Fixed Point Iteration

For the function:
```
f = λg. λn. if iszero n then 1 else n * g(n-1)
```

Compute by hand:
1. `f⁰(⊥)` (what is ⊥ in the function domain?)
2. `f¹(⊥)` (apply f to ⊥)
3. `f²(⊥)`
4. `f³(⊥)`

What is the pattern? How does this relate to factorial?

---

## Exercise 5: Continuity

A function `f : D → E` is continuous if for all directed sets S ⊆ D:
```
f(⊔S) = ⊔{f(s) | s ∈ S}
```

Prove or disprove that the following functions are continuous:

1. `λn. n + 1` on flat Nat
2. `λb. if b then 0 else 1` on flat Bool
3. The "parallel or" function on Bool × Bool:
   ```
   por(⊥, true) = true
   por(true, ⊥) = true
   por(false, false) = false
   ```

**Hint:** For non-continuous functions, find a directed set where the equation fails.

---

## Exercise 6: Strict vs. Non-strict Semantics

The conditional has two possible semantics:

**Strict:** `cond(⊥, t, e) = ⊥`
**Non-strict:** Only evaluate the branch that's taken

1. Give the full semantic definition for each version.
2. What is `[[if ⊥ then 0 else Ω]]` under each? (where Ω loops forever)
3. Which does Haskell use? Which does strict ML use?

---

## Exercise 7: Adding Products

Extend our denotational semantics with product types:

1. Define the domain `[[A × B]]` in terms of `[[A]]` and `[[B]]`.
2. Give the denotation of pair formation: `[[(e1, e2)]]ρ = ?`
3. Give the denotations of projections: `[[fst e]]ρ = ?` and `[[snd e]]ρ = ?`
4. What is `[[fst ⊥]]`? What is `[[fst (⊥, 0)]]`?

---

## Exercise 8: Recursive Types

Consider the type of natural number lists: `List = 1 + (Nat × List)`

1. Write the domain equation for `[[List]]`.
2. Use fixed points to show this has a solution.
3. What does `⊥ : List` represent?
4. What does `inl () : List` represent (assuming inl is left injection)?

---

## Exercise 9: Adequacy

A semantics is **adequate** if:
```
[[e]] = [[e']] implies e ≃ e' (observationally equivalent)
```

1. Define observational equivalence for our language.
2. Show that `fix (λx. x)` and `fix (λx. fix (λy. y))` have the same denotation.
3. Are they observationally equivalent?

---

## Exercise 10: Full Abstraction

A semantics is **fully abstract** if:
```
e ≃ e' implies [[e]] = [[e']]
```

This is harder to achieve! Consider:

1. The term `λf. f(⊥)` tests if f is strict.
2. Can you distinguish `λx. 0` from `λx. if x then 0 else 0` observationally?
3. What about denotationally?

---

## Challenge Problems

### Challenge A: Implementing Domain Approximation

Implement a function that computes and displays the approximation chain:

```haskell
showApproximations :: Int -> Term -> IO ()
showApproximations n (Fix f) = ...
```

Display `⊥, f(⊥), f²(⊥), ...` up to n iterations.

### Challenge B: Adding State

Extend the semantics to handle mutable state:

1. Define a store `σ : Loc → Val`
2. Modify denotations to thread state: `[[e]]ρσ = (v, σ')`
3. Add `ref`, `!`, and `:=` operations
4. What is the domain of references?

### Challenge C: Continuation Semantics

Rewrite the denotational semantics in continuation-passing style:

```
[[e]]ρκ = κ([[e]]ρ)
```

1. Define continuations: `Cont = Val → Ans`
2. Give CPS denotations for all constructs
3. How does this relate to control operators like call/cc?

---

## Solutions

### Exercise 1 Solutions

1. `[[λx. x]] ∅`
   ```
   = λd ∈ Nat. [[x]][x↦d]
   = λd ∈ Nat. d
   = id_Nat
   ```

2. `[[(λx. suc x) 5]] ∅`
   ```
   = [[λx. suc x]] ∅ ([[5]] ∅)
   = (λd. [[suc x]][x↦d]) (5)
   = [[suc x]][x↦5]
   = suc([[x]][x↦5])
   = suc(5)
   = 6
   ```

3. `[[let y = 3 in y + y]] ∅`
   ```
   = [[y + y]][y↦[[3]]∅]
   = [[y + y]][y↦3]
   = 3 + 3
   = 6
   ```

4. `[[if true then 0 else 1]] ∅`
   ```
   = cond([[true]]∅, [[0]]∅, [[1]]∅)
   = cond(true, 0, 1)
   = 0
   ```

### Exercise 3 Solution

Functions in `Bool → Bool`:
1. `⊥` (always undefined)
2. `λx. ⊥` (strict constant bottom)
3. `λx. true` (constant true)
4. `λx. false` (constant false)

Wait, that's only considering the constant functions. We also need:
5. `id = λx. x`
6. `not = λx. if x then false else true`

Actually, for a flat domain Bool → Bool, we have 4 total functions:
- `⊥` (bottom function)
- `λx. true` (constant true, ignoring input)
- `λx. false` (constant false, ignoring input)
- `id` (identity)

Hmm, what about not? `not(⊥) = ⊥` (by strictness), so not is one of the above.

The partial order:
```
    const_true    id    const_false
         \        |         /
          \       |        /
           \      |       /
            \     |      /
              ⊥_fun
```

---

## Reading

1. **Scott & Strachey** - "Toward a Mathematical Semantics for Computer Languages" (1971)
   - The foundational paper

2. **Winskel** - "The Formal Semantics of Programming Languages"
   - Chapter 8 covers domain theory

3. **Gunter** - "Semantics of Programming Languages"
   - Comprehensive treatment of domain theory

4. **Amadio & Curien** - "Domains and Lambda-Calculi"
   - Deep mathematical foundations
