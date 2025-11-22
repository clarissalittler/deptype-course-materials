# Chapter 4: Hindley-Milner Type Inference - Self-Check Quiz

## Instructions

This quiz tests your understanding of Chapter 4 concepts. Try to answer each question without looking at the materials, then check your answers at the end.

**Scoring Guide**:
- 28-30 correct: Excellent! Ready for Chapter 5
- 24-27 correct: Good! Review any missed topics
- 20-23 correct: Decent! Spend more time with weak areas
- Below 20: Review the chapter and tutorial before continuing

---

## Section 1: Type Variables and Substitutions (Questions 1-5)

### Question 1
What is the result of applying the substitution `[α ↦ Nat, β ↦ Bool]` to the type `α → β → α`?

A) `Nat → Bool → Nat`
B) `Nat → Bool → Bool`
C) `Bool → Nat → Bool`
D) `α → β → α` (unchanged)

### Question 2
What is the result of the substitution composition `S₁ ∘ S₂` where `S₁ = [α ↦ Nat]` and `S₂ = [β ↦ α]`?

A) `[α ↦ Nat, β ↦ α]`
B) `[α ↦ Nat, β ↦ Nat]`
C) `[β ↦ Nat]`
D) `[α ↦ β, β ↦ Nat]`

### Question 3
Which of the following is a monotype (not a polytype)?

A) `∀α. α → α`
B) `α → β`
C) `∀α β. α → β → α`
D) `∀γ. (γ → γ) → γ`

### Question 4
Given type `(α → β) → α → β`, which variables are free?

A) {α}
B) {β}
C) {α, β}
D) {} (no free variables)

### Question 5
What does the type variable `α` in `α → α` represent?

A) The type Nat
B) The type Bool
C) Any single type
D) A different type for each occurrence

---

## Section 2: Unification (Questions 6-10)

### Question 6
What is the result of `unify(α, Nat)`?

A) `[]` (empty substitution)
B) `[α ↦ Nat]`
C) `[Nat ↦ α]`
D) FAIL

### Question 7
What is the result of `unify(α → β, Nat → Bool)`?

A) `[α ↦ Nat]`
B) `[β ↦ Bool]`
C) `[α ↦ Nat, β ↦ Bool]`
D) FAIL

### Question 8
What is the result of `unify(α, α → Nat)`?

A) `[α ↦ α → Nat]`
B) `[α ↦ Nat]`
C) `[]`
D) FAIL (occurs check)

### Question 9
What is the purpose of the occurs check in unification?

A) To prevent duplicate type variables
B) To prevent infinite types
C) To ensure type variables are used consistently
D) To check if a variable occurs in the environment

### Question 10
What is the result of `unify(α → α, Nat → β)`?

A) `[α ↦ Nat]`
B) `[α ↦ Nat, β ↦ Nat]`
C) `[α ↦ β]`
D) FAIL

---

## Section 3: Type Schemes and Polymorphism (Questions 11-15)

### Question 11
Given environment `Γ = {x : α}`, what is `generalize(Γ, α → β)`?

A) `∀α β. α → β`
B) `∀β. α → β`
C) `∀α. α → β`
D) `α → β` (no generalization)

### Question 12
What does `instantiate(∀α β. α → β)` produce?

A) `α → β` (same)
B) `γ → δ` (fresh variables)
C) `Nat → Bool`
D) `∀α β. α → β` (unchanged)

### Question 13
In the type scheme `∀α. α → β`, which variables are quantified?

A) α only
B) β only
C) Both α and β
D) Neither

### Question 14
Why can't we generalize variables that are free in the environment?

A) It would be inefficient
B) They represent specific (though unknown) types
C) It would make type checking undecidable
D) It would violate the occurs check

### Question 15
How many times can you instantiate a type scheme `∀α. α → α`?

A) Once
B) Twice
C) As many times as needed, each with fresh variables
D) It cannot be instantiated

---

## Section 4: Algorithm W (Questions 16-20)

### Question 16
When inferring the type of `λx. t`, what type is initially assigned to `x`?

A) A specific base type like Nat or Bool
B) A fresh type variable
C) The type of t
D) No type (x is untyped)

### Question 17
In the W-App rule, after inferring types for `t₁` and `t₂`, what do we unify?

A) The types of t₁ and t₂ directly
B) The type of t₁ with `t₂'s type → fresh variable`
C) The type of t₂ with `t₁'s type → fresh variable`
D) Both types with a fresh variable

### Question 18
What is the principal type of `λx. x`?

A) `Nat → Nat`
B) `Bool → Bool`
C) `α → α`
D) `∀α. α → α`

### Question 19
What is the principal type of `λf. λx. f x`?

A) `(Nat → Nat) → Nat → Nat`
B) `(α → α) → α → α`
C) `∀α β. (α → β) → α → β`
D) `∀α. (α → α) → α → α`

### Question 20
In Algorithm W, why do we thread substitutions through the inference?

A) For efficiency
B) To track what we've learned about type variables
C) To prevent infinite loops
D) To enable polymorphism

---

## Section 5: Let-Polymorphism (Questions 21-25)

### Question 21
Consider: `let id = λx. x in (id true, id 0)`. Does this type check?

A) Yes
B) No, because id can't have two different types
C) No, because true and 0 have different types
D) Yes, but only if we add type annotations

### Question 22
Consider: `(λid. (id true, id 0)) (λx. x)`. Does this type check?

A) Yes
B) No, cannot unify Bool and Nat
C) No, lambda expressions can't be applied
D) Yes, but only with explicit type annotations

### Question 23
Why is let-polymorphism called "let-polymorphism"?

A) Because it only works with let bindings
B) Because let is a polymorphic keyword
C) Because let bindings generalize their type, lambdas don't
D) Because let introduces multiple types

### Question 24
In `let f = t₁ in t₂`, when is the type of `t₁` generalized?

A) Immediately when encountering the let
B) After inferring the type of t₁, before typing t₂
C) After typing the entire let expression
D) Never - let doesn't generalize

### Question 25
What would happen if we allowed lambda-bound variables to be polymorphic?

A) Programs would be more efficient
B) Type inference would become undecidable
C) Nothing - it's just a design choice
D) All programs would be polymorphic

---

## Section 6: Principal Types (Questions 26-27)

### Question 26
What does it mean for a type to be "principal"?

A) It's the first type we try
B) It's the most general type
C) It's the most specific type
D) It's the type the programmer intended

### Question 27
For the term `λx. λy. x`, which of these is the principal type?

A) `Nat → Nat → Nat`
B) `Bool → Bool → Bool`
C) `α → α → α`
D) `∀α β. α → β → α`

---

## Section 8: Practical Understanding (Questions 28-30)

### Question 28
Which real-world languages use Hindley-Milner type inference?

A) JavaScript and Python
B) Java and C++
C) Haskell and OCaml
D) C and Rust

### Question 29
What is the main advantage of type inference over explicit type annotations?

A) Programs run faster
B) Less code to write while maintaining type safety
C) More flexible types
D) Easier to learn

### Question 30
What is the main limitation of Hindley-Milner compared to System F?

A) No polymorphism at all
B) No first-class polymorphic functions
C) Type inference is undecidable
D) Programs don't terminate

---

## Answer Key

### Section 1: Type Variables and Substitutions
1. **A** - `Nat → Bool → Nat` (substitute α with Nat, β with Bool)
2. **B** - `[α ↦ Nat, β ↦ Nat]` (compose: first S₂ makes β→α, then S₁ makes α→Nat)
3. **B** - `α → β` (no ∀, so it's a monotype)
4. **C** - {α, β} (both appear unquantified)
5. **C** - Any single type (α is a type variable representing any type)

### Section 2: Unification
6. **B** - `[α ↦ Nat]` (bind α to Nat)
7. **C** - `[α ↦ Nat, β ↦ Bool]` (unify both sides)
8. **D** - FAIL (occurs check: α appears in α → Nat)
9. **B** - To prevent infinite types (like α = α → Nat → ...)
10. **B** - `[α ↦ Nat, β ↦ Nat]` (α unifies with Nat, then α unifies with β)

### Section 3: Type Schemes and Polymorphism
11. **B** - `∀β. α → β` (α is free in Γ, so don't quantify it; only quantify β)
12. **B** - `γ → δ` (fresh variables replace quantified variables)
13. **A** - α only (β is not under the ∀)
14. **B** - They represent specific (though unknown) types (free variables in environment are fixed)
15. **C** - As many times as needed, each with fresh variables

### Section 4: Algorithm W
16. **B** - A fresh type variable (we don't know the type yet)
17. **B** - The type of t₁ with `t₂'s type → fresh variable`
18. **D** - `∀α. α → α` (after generalization; before: `α → α`)
19. **C** - `∀α β. (α → β) → α → β` (most general function application type)
20. **B** - To track what we've learned about type variables

### Section 5: Let-Polymorphism
21. **A** - Yes (id is generalized to ∀α. α → α, can be used at different types)
22. **B** - No, cannot unify Bool and Nat (id is monomorphic in lambda)
23. **C** - Because let bindings generalize their type, lambdas don't
24. **B** - After inferring the type of t₁, before typing t₂
25. **B** - Type inference would become undecidable (would need System F)

### Section 6: Principal Types
26. **B** - It's the most general type
27. **D** - `∀α β. α → β → α` (most general - α and β can be different)

### Section 8: Practical Understanding
28. **C** - Haskell and OCaml (also F#, Standard ML)
29. **B** - Less code to write while maintaining type safety
30. **B** - No first-class polymorphic functions (can't pass polymorphic functions as arguments)

---

## Detailed Explanations

### Question 2 Explanation
Substitution composition `S₁ ∘ S₂` means "apply S₂ first, then S₁":
- Start with β
- Apply S₂: `[β ↦ α]` gives α
- Apply S₁: `[α ↦ Nat]` gives Nat
- So β maps to Nat in the composed substitution

### Question 8 Explanation
The occurs check prevents infinite types:
- If we allowed `[α ↦ α → Nat]`, we'd get:
  - α = α → Nat
  - α = (α → Nat) → Nat
  - α = ((α → Nat) → Nat) → Nat
  - ... infinite!

### Question 11 Explanation
Generalization only quantifies variables that are:
- Free in the type (both α and β are free in `α → β`)
- BUT not free in the environment (α is free in Γ = {x : α})
- So we only quantify β: `∀β. α → β`

### Question 21-22 Explanation
These questions illustrate the key difference:
- **Let**: Generalizes the type to `∀α. α → α`, each use gets fresh instantiation
- **Lambda**: Keeps the monomorphic type, all uses must share the same type variable

### Question 27 Explanation
For `λx. λy. x`:
- We could give it type `Nat → Nat → Nat` ✓
- Or `Bool → Bool → Bool` ✓
- Or `α → α → α` ✓
- But `∀α β. α → β → α` is most general ✓✓
  - x has type α
  - y has type β (can be different!)
  - result has type α

---

## Self-Assessment

Count your correct answers:

**28-30 correct (93%+)**: Excellent! You have a strong grasp of Hindley-Milner type inference. You understand unification, let-polymorphism, and Algorithm W. Ready for Chapter 5!

**24-27 correct (80-90%)**: Good! You understand the core concepts. Review any questions you missed, especially:
- Substitution composition
- Let-polymorphism vs lambda
- Generalization rules

**20-23 correct (67-80%)**: Decent foundation, but some gaps. Focus on:
- Unification algorithm (especially occurs check)
- When and why generalization happens
- Algorithm W step-by-step

**Below 20 (< 67%)**: Review the chapter more carefully. Focus on:
1. TUTORIAL.md: Work through all examples step-by-step
2. COMMON_MISTAKES.md: Understand common pitfalls
3. Use the REPL to experiment
4. Retake the quiz

---

## Topics to Review Based on Missed Questions

**Questions 1-5**: Review type variables, substitutions, and monotypes vs polytypes
- TUTORIAL.md: Parts 1-2
- CHEAT_SHEET.md: Type Schemes section

**Questions 6-10**: Review unification algorithm
- TUTORIAL.md: Part 3
- COMMON_MISTAKES.md: Occurs Check section
- Practice more unification by hand

**Questions 11-15**: Review generalization and instantiation
- TUTORIAL.md: Part 4
- README.md: Type Schemes section

**Questions 16-20**: Review Algorithm W
- TUTORIAL.md: Parts 5 and 8
- README.md: Algorithm W section
- Trace through more examples

**Questions 21-25**: Review let-polymorphism
- TUTORIAL.md: Part 6
- COMMON_MISTAKES.md: Let vs Lambda section
- This is the most important concept!

**Questions 26-27**: Review principal types
- TUTORIAL.md: Part 7
- README.md: Principal Types section

**Questions 28-30**: Review practical applications
- README.md: Real-World Connections
- README.md: Limitations section

---

## Next Steps

### If you scored well (80%+)
- Complete all exercises in exercises/EXERCISES.md
- Experiment with the REPL
- Try implementing extensions
- Move on to Chapter 5 when ready

### If you need more practice
- Review TUTORIAL.md sections you struggled with
- Work through examples by hand
- Use the REPL to verify your work
- Consult COMMON_MISTAKES.md
- Retake the quiz after reviewing

Remember: Type inference is subtle! Don't be discouraged if it takes time to fully grasp.
