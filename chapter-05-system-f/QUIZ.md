# Chapter 5: System F (Polymorphic Lambda Calculus) - Self-Check Quiz

## Instructions

This quiz tests your understanding of System F concepts. Try to answer each question without looking at the materials, then check your answers at the end.

**Scoring Guide**:
- 27-30 correct: Excellent! Ready for Chapter 6
- 23-26 correct: Good! Review any missed topics
- 18-22 correct: Decent! Spend more time with weak areas
- Below 18: Review the chapter and tutorial before continuing

**Time estimate**: 45-60 minutes

---

## Section 1: Basic Syntax and Concepts (Questions 1-5)

### Question 1
What is the difference between `λ` and `Λ` in System F?

A) λ is for term abstraction, Λ is for type abstraction
B) λ is lowercase lambda, Λ is uppercase lambda (same meaning)
C) λ is for functions, Λ is for recursive functions
D) There is no difference - they are interchangeable

### Question 2
What is the type of the polymorphic identity function `Λα. λx:α. x`?

A) `α → α`
B) `∀α. α`
C) `∀α. α → α`
D) `λα. α → α`

### Question 3
How do you apply the polymorphic identity to the type `Bool`?

A) `id Bool`
B) `id [Bool]`
C) `id<Bool>`
D) `id {Bool}`

### Question 4
Which of the following is NOT a valid System F term?

A) `Λα. λx:α. x`
B) `(Λα. λx:α. x) [Bool]`
C) `λx:∀α. α → α. x`
D) `Λα. α`

### Question 5
What does the ∀ symbol mean in System F types?

A) "There exists"
B) "For all"
C) "Maybe"
D) "Function"

---

## Section 2: Type Abstraction and Application (Questions 6-10)

### Question 6
What is the result of the type application `(Λα. λx:α. x) [Nat]`?

A) `λx:α. x`
B) `λx:Nat. x`
C) `Nat → Nat`
D) `∀α. Nat → Nat`

### Question 7
Consider: `const = Λα. Λβ. λx:α. λy:β. x`. What is its type?

A) `α → β → α`
B) `∀α. ∀β. α → β → α`
C) `∀α. α → ∀β. β → α`
D) Both B and C are equivalent and correct

### Question 8
How many type applications are needed to use `const` fully?

A) 0
B) 1
C) 2
D) 4

### Question 9
What is the type β-reduction rule for System F?

A) `(λx:τ. t) v → [x ↦ v]t`
B) `(Λα. t) [τ] → [α ↦ τ]t`
C) `(Λα. t) v → [α ↦ v]t`
D) `(λx:τ. t) [τ'] → [x ↦ τ']t`

### Question 10
Evaluate: `(Λα. λx:α. succ x) [Nat] 0`

A) `succ [Nat] 0`
B) `succ 0`
C) `1`
D) Both B and C (depending on evaluation depth)

---

## Section 3: Universal Types (Questions 11-15)

### Question 11
In the type `∀α. α → (∀β. β → α)`, which type variable has wider scope?

A) α
B) β
C) They have the same scope
D) Neither has scope

### Question 12
Can you instantiate a type variable with a polymorphic type in System F?

Example: `id [∀β. β → β]`

A) No, this is not allowed
B) Yes, this is called impredicativity
C) Yes, but only in Hindley-Milner
D) Only if β ≠ α

### Question 13
What is the type of: `λf:∀α. α → α. f [Bool] true`?

A) `Bool → Bool`
B) `(∀α. α → α) → Bool`
C) `∀α. (α → α) → Bool`
D) `Bool`

### Question 14
Which of the following types represents a polymorphic pair?

A) `∀α. ∀β. α × β`
B) `∀α. ∀β. (α → β → ∀γ. γ) → ∀γ. γ`
C) `∀α. ∀β. ∀γ. (α → β → γ) → γ`
D) Both B and C (equivalent encodings)

### Question 15
What does "first-class polymorphism" mean in System F?

A) Polymorphism is faster than in other systems
B) Polymorphic functions can be passed as arguments and returned from functions
C) Polymorphism is more important than other features
D) Only the first class of types can be polymorphic

---

## Section 4: Typing Rules (Questions 16-20)

### Question 16
In System F, we use two contexts: Δ and Γ. What does each track?

A) Δ tracks terms, Γ tracks types
B) Δ tracks types, Γ tracks terms
C) Δ tracks type variables, Γ tracks term variables (with their types)
D) Δ tracks functions, Γ tracks values

### Question 17
What is the T-TyAbs rule?

A) `Δ, α; Γ ⊢ t : τ  ⟹  Δ; Γ ⊢ Λα. t : ∀α. τ`
B) `Δ; Γ, α ⊢ t : τ  ⟹  Δ; Γ ⊢ Λα. t : ∀α. τ`
C) `Δ; Γ ⊢ t : τ  ⟹  Δ; Γ ⊢ Λα. t : τ`
D) `Δ; Γ ⊢ t : ∀α. τ  ⟹  Δ, α; Γ ⊢ t : τ`

### Question 18
What happens in the T-TyApp rule when you apply `t : ∀α. τ` to type `τ'`?

A) The result has type `τ`
B) The result has type `τ'`
C) The result has type `[α ↦ τ']τ` (substitute τ' for α in τ)
D) Type error - cannot apply types

### Question 19
To type check `Λα. Λβ. λx:α. λy:β. x`, you need to:

A) Add α to Δ, then add β to Δ, then add x and y to Γ
B) Add α and β to Γ, then check the term
C) Add x and y to Δ, then check
D) No contexts needed

### Question 20
Can a term variable's type contain free type variables?

Example: `x : α` where α is not in Δ

A) Yes, always allowed
B) No, all type variables in Γ must be in Δ
C) Only if α is bound by ∀
D) Only in closed terms

---

## Section 5: Church Encodings (Questions 21-25)

### Question 21
What is the Church encoding of booleans in System F?

A) `Bool = ∀α. α → α`
B) `CBool = ∀α. α → α → α`
C) `CBool = Bool → Bool → Bool`
D) `CBool = ∀α. Bool → α`

### Question 22
What is the Church encoding of natural numbers?

A) `CNat = ∀α. α → α`
B) `CNat = Nat`
C) `CNat = ∀α. (α → α) → α → α`
D) `CNat = ∀α. α → (α → α) → α`

### Question 23
How is the number 3 encoded as a Church numeral?

A) `Λα. λf:α→α. λx:α. x`
B) `Λα. λf:α→α. λx:α. f (f (f x))`
C) `Λα. λf:α→α. λx:α. f x x x`
D) `λn:Nat. succ (succ (succ n))`

### Question 24
What is the type of Church-encoded pairs?

A) `Pair α β = α × β`
B) `Pair α β = ∀γ. (α → β → γ) → γ`
C) `Pair α β = α → β`
D) `Pair α β = ∀γ. γ → (α → β → γ)`

### Question 25
What is the Church encoding of lists?

A) `List α = ∀R. R → (α → R) → R`
B) `List α = ∀R. (α → R → R) → R → R`
C) `List α = [α]`
D) `List α = ∀R. R → R → α`

---

## Section 6: Parametricity (Questions 26-30)

### Question 26
What is parametricity?

A) A polymorphic function can inspect its type parameters
B) A polymorphic function cannot inspect or create values of its type parameters
C) All functions must have parameters
D) Types must be parameters to functions

### Question 27
Why must a function of type `∀α. α → α` be the identity function?

A) It's defined that way by convention
B) The compiler enforces it
C) It cannot create or inspect values of type α, so can only return the input
D) For performance reasons

### Question 28
What can a function of type `∀α. List α → List α` do?

A) Filter elements by value
B) Modify element values
C) Create new elements
D) Rearrange, duplicate, or drop elements

### Question 29
What is a "free theorem"?

A) A theorem you get for free from the library
B) A property that follows from a type signature alone, due to parametricity
C) A theorem that doesn't require proof
D) A theorem about freedom of choice

### Question 30
For `map : ∀α. ∀β. (α → β) → List α → List β`, which is a free theorem?

A) `map f [] = []`
B) `map id = id`
C) `map g ∘ map f = map (g ∘ f)`
D) All of the above

---

## Section 7: Advanced Topics (Questions 31-35)

### Question 31
What is impredicativity?

A) Types cannot depend on values
B) You can quantify over all types, including polymorphic ones
C) Type inference is impossible
D) Predicates are not allowed in types

### Question 32
How are existential types encoded in System F?

A) `∃α. τ = ∀α. τ`
B) `∃α. τ = ∀R. (∀α. τ → R) → R`
C) `∃α. τ = τ` (if α doesn't appear in τ)
D) Existentials cannot be encoded

### Question 33
What is strong normalization?

A) All well-typed terms terminate (reach a normal form)
B) Types are normalized before type checking
C) Variables must be in normal form
D) Evaluation order doesn't matter

### Question 34
Why is type inference undecidable in System F?

A) Because of the ∀ quantifier
B) Because you need to "guess" type applications, which has infinitely many possibilities
C) Because Church encodings are too complex
D) It's actually decidable with the right algorithm

### Question 35
Compared to Hindley-Milner, System F is:

A) Less expressive but has decidable inference
B) More expressive but has undecidable inference
C) Equally expressive with decidable inference
D) Less expressive with undecidable inference

---

## Answer Key

### Section 1: Basic Syntax and Concepts
1. **A** - λ is for term abstraction, Λ is for type abstraction
2. **C** - `∀α. α → α` (universal quantification over α)
3. **B** - `id [Bool]` (square brackets for type application)
4. **D** - `Λα. α` is invalid (α is a type, not a term)
5. **B** - "For all" (universal quantifier)

### Section 2: Type Abstraction and Application
6. **B** - `λx:Nat. x` (substitute Nat for α)
7. **D** - Both B and C are equivalent (∀ associates to the right)
8. **C** - 2 type applications (one for α, one for β)
9. **B** - `(Λα. t) [τ] → [α ↦ τ]t` (type β-reduction)
10. **D** - Both B and C (evaluates to `succ 0`, which reduces to `1`)

### Section 3: Universal Types
11. **A** - α has wider scope (it's bound by the outer ∀)
12. **B** - Yes, this is called impredicativity
13. **B** - `(∀α. α → α) → Bool`
14. **C** - `∀α. ∀β. ∀γ. (α → β → γ) → γ` (Church encoding)
15. **B** - Polymorphic functions can be passed as arguments and returned from functions

### Section 4: Typing Rules
16. **C** - Δ tracks type variables, Γ tracks term variables with their types
17. **A** - Add α to Δ in the premise
18. **C** - The result has type `[α ↦ τ']τ`
19. **A** - Add α to Δ, then β to Δ, then x and y to Γ
20. **B** - No, all type variables in Γ must be in Δ (well-formedness)

### Section 5: Church Encodings
21. **B** - `CBool = ∀α. α → α → α`
22. **C** - `CNat = ∀α. (α → α) → α → α`
23. **B** - `Λα. λf:α→α. λx:α. f (f (f x))` (apply f three times)
24. **B** - `Pair α β = ∀γ. (α → β → γ) → γ`
25. **B** - `List α = ∀R. (α → R → R) → R → R` (fold encoding)

### Section 6: Parametricity
26. **B** - A polymorphic function cannot inspect or create values of its type parameters
27. **C** - It cannot create or inspect values of type α, so can only return the input
28. **D** - Can only rearrange, duplicate, or drop elements (cannot inspect values)
29. **B** - A property that follows from a type signature alone, due to parametricity
30. **D** - All of the above (all are free theorems for map)

### Section 7: Advanced Topics
31. **B** - You can quantify over all types, including polymorphic ones
32. **B** - `∃α. τ = ∀R. (∀α. τ → R) → R`
33. **A** - All well-typed terms terminate
34. **B** - Need to "guess" type applications, which has infinitely many possibilities
35. **B** - More expressive but has undecidable inference

---

## Score Interpretation

**30/30 - Perfect!** You have mastered System F!

**27-29 - Excellent!** You understand System F deeply. Minor review may help, but you're ready for Chapter 6.

**23-26 - Good!** Solid understanding. Review sections where you missed questions:
- Section 1-2: Practice basic syntax and applications
- Section 3-4: Study typing rules more carefully
- Section 5: Work through Church encoding examples
- Section 6: Read more about parametricity
- Section 7: Review advanced topics in README.md

**18-22 - Decent!** You grasp the concepts but need more practice:
- Work through TUTORIAL.md examples step-by-step
- Practice typing derivations by hand
- Implement Church encodings in the REPL
- Review COMMON_MISTAKES.md

**Below 18 - Needs Review!** Take more time with the material:
1. Re-read README.md carefully
2. Work through TUTORIAL.md with the REPL open
3. Practice typing derivations for simple terms
4. Complete exercises 1-3
5. Use CHEAT_SHEET.md as reference
6. Retake quiz after review

---

## What to Review Based on Weak Areas

### Missed Section 1-2 questions?
→ Review TUTORIAL.md Parts 1-2: Basic syntax and type applications

### Missed Section 3-4 questions?
→ Review TUTORIAL.md Parts 3-4: Universal types and typing rules
→ Practice building derivation trees

### Missed Section 5 questions?
→ Review TUTORIAL.md Parts 6-8: Church encodings
→ Implement encodings in the REPL

### Missed Section 6 questions?
→ Review TUTORIAL.md Part 9: Parametricity
→ Read Wadler's "Theorems for Free!" (optional)

### Missed Section 7 questions?
→ Review TUTORIAL.md Parts 10-12: Advanced topics
→ Read README.md: Properties section

---

## Next Steps

Once you score 23+ on this quiz:
- Complete all exercises in exercises/EXERCISES.md
- Experiment with the REPL
- Read about real-world applications in README.md
- Move on to Chapter 6: System F-omega

Good luck!
