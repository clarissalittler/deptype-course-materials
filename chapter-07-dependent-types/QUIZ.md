# Chapter 7: Dependent Types - Self-Check Quiz

## Instructions

This quiz tests your understanding of dependent types concepts. Try to answer each question without looking at the materials, then check your answers at the end.

**Scoring Guide**:
- 23-25 correct: Excellent! Ready for Chapter 8
- 19-22 correct: Good! Review any missed topics
- 15-18 correct: Decent! Spend more time with weak areas
- Below 15: Review the chapter and tutorial before continuing

---

## Section 1: Unified Syntax and Basic Concepts (Questions 1-5)

### Question 1
In dependent type theory, which of the following is true?

A) Types and terms have separate syntaxes
B) Types are terms, but terms are not types
C) Terms and types are unified - types are terms whose type is Type
D) Types are static and cannot compute

### Question 2
What is the type of `Type` in our system?

A) `Type` (Type-in-Type)
B) `Type₁` (universe hierarchy)
C) `Type` has no type - it's a primitive
D) `Kind`

### Question 3
Which of these is a valid term?

A) `Type → Type`
B) `λ(A:Type). A`
C) `Π(x:Type). x`
D) All of the above

### Question 4
What does it mean for types to "depend on values"?

A) Type checking happens at runtime
B) Types can mention value-level variables
C) Values can be used as types
D) Type inference is easier

### Question 5
In a properly designed system (not Type-in-Type), what should `Type : ?` be?

A) `Type`
B) `Type₁`
C) `Kind`
D) Types don't have types

---

## Section 2: Pi Types (Questions 6-10)

### Question 6
What is `Π(x:Nat). Bool` equivalent to?

A) `Nat → Bool`
B) `∀x:Nat. Bool`
C) `Σ(x:Nat). Bool`
D) It's not equivalent to anything simpler

### Question 7
Given `f : Π(A:Type). A → A`, what is the type of `f Nat`?

A) `Type`
B) `A → A`
C) `Nat → Nat`
D) `Π(A:Type). A`

### Question 8
Which of these types is dependent (the return type mentions the parameter)?

A) `Nat → Nat`
B) `Π(x:Nat). Nat`
C) `Π(A:Type). A → A`
D) `Bool → Bool`

### Question 9
What is the type of polymorphic identity?

A) `∀A. A → A`
B) `Π(A:Type). A → A`
C) `Type → Type`
D) `λ(A:Type). λ(x:A). x`

### Question 10
In the application rule for Π types, if `f : Π(x:A). B` and `a : A`, what is the type of `f a`?

A) `B`
B) `[x ↦ a]B`
C) `A → B`
D) `Π(x:A). B`

---

## Section 3: Sigma Types (Questions 11-15)

### Question 11
What is `Σ(x:Nat). Bool` equivalent to?

A) `Nat → Bool`
B) `Nat × Bool`
C) `Π(x:Nat). Bool`
D) `∃x:Nat. Bool`

### Question 12
Given `p : Σ(A:Type). A`, what is the type of `snd p`?

A) `A`
B) `Type`
C) The type that `fst p` denotes
D) `Σ(A:Type). A`

### Question 13
What does `Σ(A:Type). A` represent?

A) A pair of two types
B) An existential package: a type and a value of that type
C) A function from types to types
D) A dependent function

### Question 14
Given the pair `(3, true) : Σ(x:Nat). Bool`, what is `fst (3, true)`?

A) `3`
B) `true`
C) `Nat`
D) `Bool`

### Question 15
How do we encode existential types in dependent type theory?

A) Using Π types
B) Using Σ types
C) Using Type : Type
D) We can't encode them

---

## Section 4: Type Checking and Normalization (Questions 16-20)

### Question 16
What does definitional equality (`A ≡ B`) mean?

A) A and B are syntactically identical
B) A and B normalize to the same term
C) A and B are α-equivalent
D) A and B can be converted to each other

### Question 17
What does `(λ(A:Type). A → A) Nat` normalize to?

A) `A → A`
B) `Nat`
C) `Nat → Nat`
D) `Type → Type`

### Question 18
Why is normalization crucial for type checking?

A) It makes type checking faster
B) It's needed to compare types for equality
C) It's required for type inference
D) It prevents infinite loops

### Question 19
Which of these pairs are definitionally equal?

A) `Nat ≡ Bool`
B) `(λ(x:Nat). x) 0 ≡ 0`
C) `Type ≡ Nat`
D) `fst (1, 2) ≡ 2`

### Question 20
The conversion rule allows us to:

A) Convert between syntactically different but definitionally equal types
B) Convert any type to any other type
C) Convert terms to types
D) Convert types to terms

---

## Section 5: Type-Level Computation (Questions 21-23)

### Question 21
What is a "type family"?

A) A family of related types
B) A type indexed by values
C) A group of types with similar structure
D) A type that contains other types

### Question 22
For length-indexed vectors `Vec : Nat → Type → Type`, what is `Vec 3 Nat`?

A) A function
B) A type
C) A value
D) A kind

### Question 23
How do dependent types prevent array bounds errors?

A) By checking bounds at runtime
B) By making the index part of the type
C) By using exceptions
D) They don't - they're still possible

---

## Section 6: Curry-Howard Correspondence (Questions 24-28)

### Question 24
In the Curry-Howard correspondence, what does a type represent?

A) A value
B) A proposition
C) A program
D) A proof

### Question 25
In the Curry-Howard correspondence, what does a term represent?

A) A value
B) A proposition
C) A program and a proof
D) A type

### Question 26
The type `A → B` corresponds to which logical statement?

A) A and B
B) A or B
C) A implies B
D) Not A

### Question 27
The type `Π(x:A). P(x)` corresponds to which logical statement?

A) For all x in A, P(x)
B) Exists x in A such that P(x)
C) A implies P
D) P or A

### Question 28
The type `Σ(x:A). P(x)` corresponds to which logical statement?

A) For all x in A, P(x)
B) Exists x in A such that P(x)
C) A implies P
D) P and A

---

## Section 7: Church Encodings (Questions 29-31)

### Question 29
What is the type of polymorphic Church booleans?

A) `Bool`
B) `Π(A:Type). A → A`
C) `Π(A:Type). A → A → A`
D) `Type → Type`

### Question 30
What does `ctrue Nat 5 0` evaluate to?

A) `true`
B) `5`
C) `0`
D) `Nat`

### Question 31
What is the advantage of polymorphic Church encodings over untyped ones?

A) They're faster
B) They're type-safe
C) They're easier to write
D) They're more expressive

---

## Section 8: Theoretical Properties (Questions 32-36)

### Question 32
Is type checking decidable for dependent types?

A) Yes, always
B) No, never
C) Only with type annotations
D) Only for simple types

### Question 33
Is type inference decidable for dependent types?

A) Yes, always
B) No, it's undecidable
C) Only with annotations
D) Only for Π types

### Question 34
What is strong normalization?

A) All terms reduce to the same normal form
B) Normalization is fast
C) All well-typed terms terminate in finite steps
D) Normal forms are unique

### Question 35
Can you write an infinite loop in dependent type theory?

A) Yes, using recursion
B) Yes, using the Y combinator
C) No, all well-typed programs terminate
D) Only if you use Type : Type

### Question 36
What's the trade-off of strong normalization?

A) Type checking is slower
B) We can't write general recursion (without additional features)
C) Programs are less efficient
D) Type inference is harder

---

## Section 9: Type-in-Type and Universes (Questions 37-40)

### Question 37
What is Girard's paradox?

A) A proof that Type : Type is inconsistent
B) A paradox about dependent types
C) A paradox about normalization
D) A paradox about type inference

### Question 38
Why is `Type : Type` problematic?

A) It makes type checking undecidable
B) It leads to logical inconsistency
C) It breaks normalization
D) It makes inference impossible

### Question 39
How do real systems (Agda, Coq, Idris) solve the Type : Type problem?

A) They forbid Type entirely
B) They use universe hierarchies (Type₀ : Type₁ : Type₂ : ...)
C) They use kind systems
D) They don't solve it - they live with it

### Question 40
Why does this chapter use Type : Type anyway?

A) It's actually safe
B) For pedagogical simplicity
C) It's required for dependent types
D) Modern research has solved the paradox

---

## Section 10: Advanced Concepts (Questions 41-45)

### Question 41
How do we encode abstract data types with existentials?

A) Using Π types
B) Using Σ types to hide the representation
C) Using Type : Type
D) We can't

### Question 42
What is a "dependent pair"?

A) A pair where both components have the same type
B) A pair where the second type depends on the first value
C) A pair of types
D) A pair of dependent functions

### Question 43
What does `Π(n:Nat). Vec (succ n) A → A` ensure?

A) The vector can be empty
B) The vector must have at least one element
C) The vector has exactly n elements
D) Nothing special

### Question 44
In a properly typed system, can `head []` compile?

A) Yes, but it fails at runtime
B) No, it's a type error
C) Yes, and it returns a default value
D) Only with a warning

### Question 45
What does "proof-relevant programming" mean?

A) Programs care about their proofs
B) Proofs are values that can be computed with
C) Programming requires proofs
D) Proofs and programs are the same thing

---

## Answers

### Section 1: Unified Syntax and Basic Concepts
1. C - Terms and types are unified - types are terms whose type is Type
2. A - `Type` (Type-in-Type in our system)
3. D - All of the above are valid
4. B - Types can mention value-level variables
5. B - `Type₁` (in a universe hierarchy)

### Section 2: Pi Types
6. A - `Nat → Bool` (when the result doesn't depend on x)
7. C - `Nat → Nat` (substitute Nat for A)
8. C - `Π(A:Type). A → A` (return type mentions A)
9. B - `Π(A:Type). A → A`
10. B - `[x ↦ a]B` (substitute a for x in B)

### Section 3: Sigma Types
11. B - `Nat × Bool` (when second type doesn't depend on first)
12. C - The type that `fst p` denotes
13. B - An existential package: a type and a value of that type
14. A - `3`
15. B - Using Σ types

### Section 4: Type Checking and Normalization
16. B - A and B normalize to the same term
17. C - `Nat → Nat`
18. B - It's needed to compare types for equality
19. B - `(λ(x:Nat). x) 0 ≡ 0` (by β-reduction)
20. A - Convert between syntactically different but definitionally equal types

### Section 5: Type-Level Computation
21. B - A type indexed by values
22. B - A type
23. B - By making the index part of the type

### Section 6: Curry-Howard Correspondence
24. B - A proposition
25. C - A program and a proof
26. C - A implies B
27. A - For all x in A, P(x)
28. B - Exists x in A such that P(x)

### Section 7: Church Encodings
29. C - `Π(A:Type). A → A → A`
30. B - `5` (true selects first argument)
31. B - They're type-safe

### Section 8: Theoretical Properties
32. C - Only with type annotations (bidirectional checking)
33. B - No, it's undecidable
34. C - All well-typed terms terminate in finite steps
35. C - No, all well-typed programs terminate
36. B - We can't write general recursion (without additional features)

### Section 9: Type-in-Type and Universes
37. A - A proof that Type : Type is inconsistent
38. B - It leads to logical inconsistency
39. B - They use universe hierarchies (Type₀ : Type₁ : Type₂ : ...)
40. B - For pedagogical simplicity

### Section 10: Advanced Concepts
41. B - Using Σ types to hide the representation
42. B - A pair where the second type depends on the first value
43. B - The vector must have at least one element
44. B - No, it's a type error
45. D - Proofs and programs are the same thing

---

## Scoring

Count your correct answers:

**41-45 correct**: Outstanding! You have a deep understanding of dependent types. You're ready for Chapter 8 and could even start reading advanced papers.

**36-40 correct**: Excellent! You understand dependent types well. Review any missed questions and you'll be well-prepared for Chapter 8.

**31-35 correct**: Very Good! You grasp the core concepts. Spend some time reviewing weak areas before moving on.

**26-30 correct**: Good! You have the basics down. Review the tutorial and try the exercises for topics you missed.

**20-25 correct**: Decent! You're getting there. Review the chapter carefully, focusing on:
- Pi types and Sigma types
- Type-level computation
- Curry-Howard correspondence

**15-19 correct**: Fair! You need more practice. Focus on:
- The difference between Π and →
- The difference between Σ and ×
- Understanding normalization
- Curry-Howard basics

**Below 15**: You should review the chapter thoroughly before continuing. Focus on:
1. TUTORIAL.md - work through all examples
2. LESSON_PLAN.md - follow the structured approach
3. exercises/EXERCISES.md - try basic exercises
4. REPL - experiment with the type checker

Don't get discouraged! Dependent types are genuinely difficult. Take your time and work through the materials systematically.

---

## Review Recommendations by Section

### If you missed questions in Section 1-2 (Basics and Pi Types)
- Review TUTORIAL.md Part 1-2
- Study CHEAT_SHEET.md Pi types section
- Try exercises/EXERCISES.md Exercise 1
- Use REPL to type check Pi type examples

### If you missed questions in Section 3 (Sigma Types)
- Review TUTORIAL.md Part 3
- Study CHEAT_SHEET.md Sigma types section
- Try exercises/EXERCISES.md Exercise 2
- Practice creating dependent pairs

### If you missed questions in Section 4 (Type Checking)
- Review TUTORIAL.md Part 4-5
- Study normalization examples
- Practice type checking by hand
- Use REPL `:step` command

### If you missed questions in Section 5 (Type-Level Computation)
- Review TUTORIAL.md Part 6
- Study vector examples from README.md
- Read about type families
- Consider real-world examples (Idris, Agda)

### If you missed questions in Section 6 (Curry-Howard)
- Review TUTORIAL.md Part 7
- Study the correspondence table
- Try exercises/EXERCISES.md Exercise 6
- Read Wadler's "Propositions as Types" (optional)

### If you missed questions in Section 7 (Church Encodings)
- Review TUTORIAL.md Part 8
- Compare with Chapter 1 encodings
- Try exercises/EXERCISES.md Exercise 4
- Practice writing polymorphic encodings

### If you missed questions in Section 8-9 (Theory)
- Review TUTORIAL.md Part 9, 11
- Read README.md theoretical properties section
- Understand strong normalization
- Study universe hierarchies

### If you missed questions in Section 10 (Advanced)
- Review all tutorial sections
- Try all exercises
- Read implementation code
- Experiment with REPL

---

## Next Steps

- **Score 80%+**: You're ready for Chapter 8! Move forward with confidence.
- **Score 60-79%**: Review missed topics, then start Chapter 8.
- **Score 40-59%**: Work through exercises before Chapter 8.
- **Score < 40%**: Complete the full lesson plan before continuing.

Remember: dependent types are a significant conceptual leap. Taking time to master them now will make everything easier later!
