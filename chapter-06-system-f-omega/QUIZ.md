# Chapter 6: System F-omega (Higher-Kinded Types) - Self-Check Quiz

## Instructions

This quiz tests your understanding of System F-omega concepts. Try to answer each question without looking at the materials, then check your answers at the end.

**Scoring Guide**:
- 20-23 correct: Excellent! Ready for Chapter 7
- 16-19 correct: Good! Review any missed topics
- 12-15 correct: Decent! Spend more time with weak areas
- Below 12: Review the chapter and tutorial before continuing

---

## Section 1: Kinds and the Kind System (Questions 1-5)

### Question 1
What is the kind of `Bool`?

A) `Bool` has no kind - it's a type
B) `*`
C) `* → *`
D) `(* → *) → *`

### Question 2
What is the kind of `List`?

A) `*`
B) `* → *`
C) `* → * → *`
D) `List` doesn't have a kind

### Question 3
What is the kind of `Either`?

A) `*`
B) `* → *`
C) `* → * → *`
D) `(* → *) → *`

### Question 4
If `F :: * → *` and `A :: *`, what is the kind of `F A`?

A) `*`
B) `* → *`
C) `* → * → *`
D) Ill-kinded (doesn't have a kind)

### Question 5
What kind would a type constructor `Functor` have that takes a type constructor and produces a type?

A) `*`
B) `* → *`
C) `(* → *) → *`
D) `* → * → *`

---

## Section 2: Type-Level Lambda (Questions 6-9)

### Question 6
What is the kind of `λA::*. A → A`?

A) `*`
B) `* → *`
C) `* → * → *`
D) `A → A`

### Question 7
What does `(λA::*. A) Bool` normalize to?

A) `λA::*. Bool`
B) `Bool`
C) `A`
D) Doesn't normalize - type error

### Question 8
What is the kind of `λF::* → *. λA::*. F A`?

A) `* → *`
B) `(* → *) → *`
C) `(* → *) → * → *`
D) `* → * → *`

### Question 9
What does `(λA::*. λB::*. A) Bool Nat` normalize to?

A) `Bool`
B) `Nat`
C) `Bool → Nat`
D) `λB::*. Bool`

---

## Section 3: Kinding Rules (Questions 10-12)

### Question 10
Under the kinding rule K-Lam, if `Γ, α::κ₁ ⊢ τ :: κ₂`, what is the kind of `λα::κ₁. τ`?

A) `κ₁`
B) `κ₂`
C) `κ₁ → κ₂`
D) `*`

### Question 11
In the K-App rule, if `Γ ⊢ τ₁ :: κ₁ → κ₂` and `Γ ⊢ τ₂ :: κ₁`, what is the kind of `τ₁ τ₂`?

A) `κ₁`
B) `κ₂`
C) `κ₁ → κ₂`
D) `*`

### Question 12
Can the type `(λA::*. A A)` be well-kinded?

A) Yes, it has kind `* → *`
B) Yes, it has kind `*`
C) No, it's ill-kinded because A would need two different kinds
D) Yes, it has kind `(* → *) → *`

---

## Section 4: Type-Level Computation (Questions 13-15)

### Question 13
What does `Compose Maybe List Bool` normalize to?
(Where `Compose = λF::* → *. λG::* → *. λA::*. F (G A)`)

A) `List (Maybe Bool)`
B) `Maybe (List Bool)`
C) `Bool`
D) `Maybe List`

### Question 14
What does `(λF::* → *. λA::*. F (F A)) Maybe Nat` normalize to?

A) `Maybe Nat`
B) `Maybe (Maybe Nat)`
C) `Nat`
D) `(Maybe Maybe) Nat`

### Question 15
Given `Const = λA::*. λB::*. A`, what does `Const (Bool → Nat) (List Bool)` normalize to?

A) `Bool → Nat`
B) `List Bool`
C) `Bool`
D) `Nat`

---

## Section 5: Typing with Kinds (Questions 16-18)

### Question 16
In the typing judgment `Γ; Δ ⊢ t : τ`, what does Γ represent?

A) Type context (maps term variables to types)
B) Kind context (maps type variables to kinds)
C) Term context (maps variables to terms)
D) Expression context

### Question 17
In the T-Abs rule for F-omega, why must we check `Γ ⊢ τ₁ :: *`?

A) To ensure the parameter type is a proper type that can classify terms
B) To ensure τ₁ is a type constructor
C) To ensure τ₁ is polymorphic
D) This check is not required

### Question 18
In the T-TApp rule, if `Γ; Δ ⊢ t : ∀α::κ. τ₁` and we apply it to type `τ₂`, what must we check about `τ₂`?

A) `τ₂` must have kind `*`
B) `τ₂` must have kind `κ`
C) `τ₂` must be a type variable
D) No check needed

---

## Section 6: Church Encodings (Questions 19-21)

### Question 19
What is the kind of the List type constructor?
(Where `List = λA::*. ∀R::*. R → (A → R → R) → R`)

A) `*`
B) `* → *`
C) `* → * → *`
D) `∀R::*. R → (A → R → R) → R`

### Question 20
What does `List Bool` normalize to?

A) `List`
B) `Bool`
C) `∀R::*. R → (Bool → R → R) → R`
D) `λA::*. ∀R::*. R → (A → R → R) → R`

### Question 21
What is the kind of the Either type constructor?
(Where `Either = λA::*. λB::*. ∀R::*. (A → R) → (B → R) → R`)

A) `*`
B) `* → *`
C) `* → * → *`
D) `(* → *) → *`

---

## Section 7: Advanced Type Operators (Questions 22-24)

### Question 22
Given `Flip = λF::* → * → *. λA::*. λB::*. F B A`, what is the kind of `Flip`?

A) `* → * → *`
B) `(* → * → *) → * → * → *`
C) `(* → *) → * → *`
D) `* → * → * → *`

### Question 23
What does `Flip Either Bool Nat` normalize to?

A) `Either Bool Nat`
B) `Either Nat Bool`
C) `Bool → Nat`
D) `Nat → Bool`

### Question 24
Given `Twice = λF::* → *. λA::*. F (F A)`, what does `Twice Maybe Bool` normalize to?

A) `Maybe Bool`
B) `Maybe (Maybe Bool)`
C) `Bool`
D) `(Maybe Maybe) Bool`

---

## Section 8: Real-World Connections (Questions 25-26)

### Question 25
In Haskell, what kind must a type constructor `f` have to be a Functor?

A) `*`
B) `* → *`
C) `* → * → *`
D) `(* → *) → *`

### Question 26
Which language has native support for higher-kinded types similar to F-omega?

A) JavaScript
B) Python
C) Haskell
D) C++

---

## Section 9: Theoretical Properties (Questions 27-28)

### Question 27
Does type-level beta reduction in F-omega always terminate?

A) No, it can loop forever like untyped lambda calculus
B) Yes, due to strong normalization
C) Only if we use call-by-value evaluation
D) Only for simple type operators

### Question 28
Why can't we have the type `λA::*. A A` in F-omega?

A) Syntax doesn't allow it
B) It would require A to have two different kinds simultaneously
C) It's syntactically valid but doesn't normalize
D) It would make the system Turing-complete

---

## Section 10: Conceptual Understanding (Questions 29-30)

### Question 29
What's the fundamental difference between System F and System F-omega?

A) F-omega adds dependent types
B) F-omega allows types to abstract over type constructors
C) F-omega removes polymorphism
D) F-omega adds mutation

### Question 30
What does the kind `(* → *) → * → *` represent?

A) A proper type
B) A simple type constructor
C) A higher-order type constructor that takes a type constructor and a type
D) An invalid kind expression

---

## Answers

<details>
<summary>Click to reveal answers</summary>

### Section 1: Kinds and the Kind System
1. **B** - `Bool :: *` (Bool is a proper type)
2. **B** - `List :: * → *` (List takes a type and returns a type)
3. **C** - `Either :: * → * → *` (Either takes two types)
4. **A** - `F A :: *` (applying a type constructor to a type gives a proper type)
5. **C** - `Functor :: (* → *) → *` (takes a type constructor, returns a type)

### Section 2: Type-Level Lambda
6. **B** - `λA::*. A → A :: * → *` (takes a type, returns a type)
7. **B** - `(λA::*. A) Bool ⟶ Bool` (simple substitution)
8. **C** - `λF::* → *. λA::*. F A :: (* → *) → * → *`
9. **A** - `(λA::*. λB::*. A) Bool Nat ⟶ Bool` (constant type operator)

### Section 3: Kinding Rules
10. **C** - `λα::κ₁. τ :: κ₁ → κ₂` (lambda creates function kind)
11. **B** - `τ₁ τ₂ :: κ₂` (application returns result kind)
12. **C** - No, A would need to be both `* → *` and `*`, which is impossible

### Section 4: Type-Level Computation
13. **B** - `Maybe (List Bool)` (F is Maybe, G is List)
14. **B** - `Maybe (Maybe Nat)` (applies Maybe twice)
15. **A** - `Bool → Nat` (Const returns first argument)

### Section 5: Typing with Kinds
16. **B** - Γ is the kind context
17. **A** - Must ensure parameter type can classify terms
18. **B** - τ₂ must have the same kind κ as the type variable

### Section 6: Church Encodings
19. **B** - `List :: * → *` (takes a type parameter)
20. **C** - `∀R::*. R → (Bool → R → R) → R`
21. **C** - `Either :: * → * → *` (takes two type parameters)

### Section 7: Advanced Type Operators
22. **B** - `Flip :: (* → * → *) → * → * → *`
23. **B** - `Either Nat Bool` (arguments flipped)
24. **B** - `Maybe (Maybe Bool)` (nested Maybe)

### Section 8: Real-World Connections
25. **B** - `f :: * → *` (Functor requires type constructors)
26. **C** - Haskell has native higher-kinded types

### Section 9: Theoretical Properties
27. **B** - Yes, strong normalization guarantees termination
28. **B** - A would need kinds `* → *` and `*` simultaneously

### Section 10: Conceptual Understanding
29. **B** - F-omega allows abstraction over type constructors
30. **C** - Higher-order type constructor taking `(* → *)` and `*`

</details>

---

## Score Interpretation

### 26-30 correct (87-100%)
**Outstanding!** You have an excellent grasp of System F-omega. You understand:
- The kind system and why it matters
- Type-level computation and lambda abstraction
- Church encodings at the type level
- Connections to real programming languages

You're ready for Chapter 7 (Dependent Types)!

### 21-25 correct (70-83%)
**Very Good!** You understand most concepts but may want to review:
- Kinding derivations (if you missed Section 3)
- Type-level computation (if you missed Section 4)
- Advanced type operators (if you missed Section 7)

Review those specific sections and try the exercises.

### 16-20 correct (53-67%)
**Decent Progress** but more study needed. Focus on:
- TUTORIAL.md for step-by-step examples
- COMMON_MISTAKES.md for common pitfalls
- Practice building kinding derivations
- Work through type-level reduction examples

Don't move to Chapter 7 yet - solidify your foundation first.

### Below 16 correct (below 53%)
**More Practice Needed**. Recommendations:
1. Re-read README.md sections carefully
2. Work through TUTORIAL.md with all examples
3. Study COMMON_MISTAKES.md
4. Practice exercises 1-4 before attempting advanced ones
5. Use the REPL to experiment
6. Retake the quiz after studying

Take your time - these concepts are challenging but crucial!

---

## Key Concepts to Master

Based on common mistakes, make sure you understand:

1. **Kinds vs Types**: Kinds classify types, types classify terms
2. **Kind `*`**: Proper types that can classify terms
3. **Kind `* → *`**: Type constructors taking one type
4. **Type-Level Lambda**: `λα::κ. τ` creates type operators
5. **Kinding Rules**: How to derive kinds for type expressions
6. **Type Application**: `(λA::*. τ) σ ⟶ [A ↦ σ]τ`
7. **Higher-Order Kinds**: `(* → *) → *` for abstracting over constructors
8. **Church Encodings**: List, Maybe, Either as type operators
9. **Strong Normalization**: Type-level computation terminates
10. **Real-World Impact**: Foundation for Haskell's type classes

If any of these seem unclear, review the corresponding tutorial section!

---

## Next Steps

After scoring well on this quiz:

1. **Complete all exercises** in exercises/EXERCISES.md
2. **Review** CHEAT_SHEET.md for quick reference
3. **Read** about Chapter 7 (Dependent Types) in README.md
4. **Experiment** with the REPL - try creating your own type operators
5. **Connect** to real languages - study Haskell's kind system

You're on your way to mastering advanced type systems!
