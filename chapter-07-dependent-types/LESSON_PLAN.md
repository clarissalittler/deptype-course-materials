# Chapter 7: Dependent Types - Lesson Plan

## Overview

This lesson plan guides you through the fundamental shift to dependent types, where **types can depend on values**. This is a significant conceptual leap that enables expressing invariants and properties directly in the type system.

**Total Estimated Time**: 12-16 hours (can be spread over 2-3 weeks)

**Prerequisites**:
- Completed Chapters 1-6
- Strong understanding of type checking and type inference
- Familiarity with System F (polymorphism)
- Comfortable with normalization and reduction

**Key Innovation**: In previous chapters, types were static. Now types can compute based on runtime values, unifying the term and type levels.

---

## Lesson 7.1: Motivation - Why Dependent Types? (45-60 minutes)

### Learning Objectives
- Understand the limitations of previous type systems
- See how dependent types solve real problems
- Appreciate the types-as-specifications paradigm

### Materials
- README.md: "Overview" and "Motivation" sections
- Real-world examples from Idris, Agda, and Coq

### Activities
1. **Recall Limitations** (15 min): Review problems from previous chapters:
   - Can't express "non-empty list" in the type
   - Array access can fail at runtime
   - No way to encode "sorted list" as a type
2. **Read** (20 min): Motivation section - the vector problem
3. **Explore** (15 min): Look at Idris examples of safe array indexing

### Self-Check ✓
- [ ] Can you explain the "head of empty list" problem?
- [ ] Why can't System F express length-indexed vectors?
- [ ] What does "types depending on values" mean intuitively?

### Key Insight
Dependent types blur the line between terms and types - types become first-class citizens that can compute!

---

## Lesson 7.2: Unified Term and Type Syntax (60 minutes)

### Learning Objectives
- Understand that terms and types are now unified
- Write dependent type expressions
- See Type as a term

### Materials
- README.md: "Syntax" section
- CHEAT_SHEET.md: First page
- TUTORIAL.md: "Part 1: Unified Syntax"

### Activities
1. **Read** (25 min): Syntax section - unified terms/types
2. **Understand** (20 min): Key insight: there's no separate type grammar!
   - `Type : Type` (for now - we'll address this later)
   - `Nat : Type`
   - `Bool : Type`
   - `(Nat → Nat) : Type`
3. **Practice** (15 min): Identify which of these are types:
   - `Type`
   - `Nat → Bool`
   - `λ(x:Nat). x`
   - `Π(A:Type). A`

### Self-Check ✓
- [ ] Can you explain why we don't have separate type syntax anymore?
- [ ] What does `Type : Type` mean?
- [ ] Is `λ(x:Nat). x` a type or a term? (Trick question - it's a term!)

### Common Pitfall
Everything is now a term, but not all terms are types. Types are terms that have kind Type.

---

## Lesson 7.3: Pi Types - Dependent Functions (90 minutes)

### Learning Objectives
- Understand Π(x:A). B syntax
- See how Π generalizes →
- Work with dependent function types

### Materials
- README.md: "Pi Types" section
- TUTORIAL.md: "Part 2: Pi Types"
- CHEAT_SHEET.md: Π-Type rules

### Activities
1. **Read** (30 min): Pi types definition and formation rule
2. **Compare** (20 min): See how `A → B` is just `Π(x:A). B` when B doesn't use x
3. **Examples** (25 min): Study these:
   - `Π(A:Type). A → A` (polymorphic identity type)
   - `Π(n:Nat). Vec n Nat` (vector constructor)
   - `Π(n:Nat). Π(A:Type). Vec (succ n) A → A` (safe head)
4. **Practice** (15 min): Write types for:
   - Polymorphic const
   - Polymorphic compose
   - A function taking a nat n and returning Vec n Bool

### Self-Check ✓
- [ ] Can you explain when `Π(x:A). B` reduces to `A → B`?
- [ ] Do you understand why the return type can mention the parameter?
- [ ] Can you write a dependent function type from scratch?

### Key Insight
Π types let the return type "know" the value of the argument!

### Practice Problems
From QUIZ.md: Questions 1-5
From exercises/EXERCISES.md: Exercise 1

---

## Lesson 7.4: Sigma Types - Dependent Pairs (90 minutes)

### Learning Objectives
- Understand Σ(x:A). B syntax
- See how Σ generalizes ×
- Work with dependent pairs

### Materials
- README.md: "Sigma Types" section
- TUTORIAL.md: "Part 3: Sigma Types"
- CHEAT_SHEET.md: Σ-Type rules

### Activities
1. **Read** (30 min): Sigma types definition and formation rule
2. **Compare** (20 min): See how `A × B` is just `Σ(x:A). B` when B doesn't use x
3. **Examples** (25 min): Study these:
   - `Σ(n:Nat). Vec n Nat` (pair of length and vector)
   - `Σ(A:Type). A` (existential package)
   - `Σ(x:Nat). (x > 0)` (positive number with proof)
4. **Practice** (15 min): Create:
   - A pair of a type and a value of that type
   - A dependent record type
   - An existential type encoding

### Self-Check ✓
- [ ] Can you explain when `Σ(x:A). B` reduces to `A × B`?
- [ ] Do you understand how the second component's type depends on the first?
- [ ] What's the type of `snd p` for `p : Σ(x:A). B`?

### Key Insight
Sigma types let the second component's type "know" the first component's value!

### Practice Problems
From QUIZ.md: Questions 6-10
From exercises/EXERCISES.md: Exercise 2

---

## Lesson 7.5: Type Checking with Dependency (75-90 minutes)

### Learning Objectives
- Apply typing rules for Π and Σ types
- Understand the conversion rule
- Check types with dependencies

### Materials
- README.md: "Type Checking" section
- TUTORIAL.md: "Part 4: Type Checking"
- CHEAT_SHEET.md: Type checking rules

### Activities
1. **Read** (25 min): Typing judgment and key rules
2. **Study** (20 min): The crucial conversion rule:
   ```
   Γ ⊢ t : A    A ≡ B    Γ ⊢ B : Type
   ──────────────────────────────────── (Conv)
   Γ ⊢ t : B
   ```
3. **Practice** (30 min): Type check these terms:
   - `λ(A:Type). λ(x:A). x`
   - `(λ(A:Type). A → A) Nat`
   - `λ(n:Nat). λ(A:Type). λ(v:Vec (succ n) A). head v`
4. **REPL Exercise** (15 min):
   ```bash
   cd chapter-07-dependent-types
   stack run
   ```
   Try `:type \(A:Type). \(x:A). x`

### Self-Check ✓
- [ ] Can you apply the Π-Intro rule?
- [ ] Can you apply the Π-Elim rule?
- [ ] Why is the conversion rule necessary?

### Common Pitfall
The application rule substitutes the argument into the return type: `Π(x:A). B` applied to `a` gives `[x ↦ a]B`.

---

## Lesson 7.6: Definitional Equality and Normalization (75 minutes)

### Learning Objectives
- Understand definitional equality (≡)
- See why normalization is crucial for type checking
- Compute normal forms

### Materials
- README.md: "Definitional Equality" section
- TUTORIAL.md: "Part 5: Normalization"
- COMMON_MISTAKES.md: "Normalization Errors"

### Activities
1. **Read** (25 min): Definition of A ≡ B via normalization
2. **Understand** (20 min): Why we need this:
   - `(λ(A:Type). A → A) Nat` ≡ `Nat → Nat`
   - Type checking requires comparing types
   - Types can reduce!
3. **Practice** (20 min): Normalize these:
   - `(λ(x:Nat). x) 0`
   - `(λ(A:Type). A → A) Bool`
   - `fst (0, true)`
4. **REPL Exercise** (10 min): Use `:step` to see reductions

### Self-Check ✓
- [ ] Can you explain why normalization is needed for type checking?
- [ ] What does it mean for two types to be definitionally equal?
- [ ] Can types reduce just like terms?

### Key Insight
Type-level computation is essential! Types are terms that can evaluate.

---

## Lesson 7.7: Type-Level Computation (60-75 minutes)

### Learning Objectives
- See types computing with values
- Understand type families conceptually
- Work through examples of dependent types in action

### Materials
- README.md: "Type-Level Computation" section
- TUTORIAL.md: "Part 6: Type-Level Computation"
- Real-world examples from Idris

### Activities
1. **Read** (20 min): Type-level computation examples
2. **Explore** (25 min): Vector examples:
   - `Vec : Nat → Type → Type`
   - How `Vec 3 Nat` is a different type than `Vec 4 Nat`
   - Why append has type `Vec m A → Vec n A → Vec (m+n) A`
3. **Conceptual** (15 min): Even without full inductive types:
   - How would you define Vec?
   - What makes it "indexed by length"?
4. **Compare** (10 min): Look at Idris vector definitions

### Self-Check ✓
- [ ] Can you explain what a "type family" is?
- [ ] Why is `Vec 3 Nat` a different type than `Vec 4 Nat`?
- [ ] How do dependent types prevent array bounds errors?

### Practice Problems
From QUIZ.md: Questions 11-13
From exercises/EXERCISES.md: Exercise 3

---

## Lesson 7.8: The Curry-Howard Correspondence (60-75 minutes)

### Learning Objectives
- Understand propositions as types
- See proofs as programs
- Connect logic and computation

### Materials
- README.md: "Curry-Howard Correspondence" section
- TUTORIAL.md: "Part 7: Propositions as Types"
- Wadler's "Propositions as Types" paper (optional)

### Activities
1. **Read** (25 min): The correspondence table
2. **Examples** (25 min): See how:
   - `A → B` means "A implies B"
   - `A × B` means "A and B"
   - `Π(x:A). P(x)` means "for all x, P(x)"
   - `Σ(x:A). P(x)` means "exists x, P(x)"
3. **Practice** (15 min): Write proofs as programs:
   - Prove: `A → A` (identity)
   - Prove: `A → B → A` (const)
   - Prove: `(A → B) → (B → C) → (A → C)` (transitivity)

### Self-Check ✓
- [ ] Can you explain the Curry-Howard correspondence?
- [ ] What does it mean for a term to be a "proof"?
- [ ] How does Π relate to "for all"?
- [ ] How does Σ relate to "exists"?

### Key Insight
Programming and proving are the same activity in dependent type theory!

### Practice Problems
From QUIZ.md: Questions 14-16
From exercises/EXERCISES.md: Exercise 6

---

## Lesson 7.9: Church Encodings with Dependent Types (60 minutes)

### Learning Objectives
- Extend Church encodings to dependent types
- Make encodings more precise with polymorphism
- Understand the role of dependent types in encodings

### Materials
- TUTORIAL.md: "Part 8: Church Encodings"
- exercises/EXERCISES.md: Exercise 4

### Activities
1. **Review** (15 min): Recall Church encodings from Chapter 1
2. **Upgrade** (25 min): See dependent versions:
   - `CBool = Π(A:Type). A → A → A`
   - `CNat = Π(A:Type). (A → A) → A → A`
3. **Practice** (20 min): Implement:
   - `ctrue`, `cfalse` with dependent types
   - `cand`, `cor`, `cnot`
   - `czero`, `csucc`

### Self-Check ✓
- [ ] How do dependent types make Church encodings more precise?
- [ ] Can you implement polymorphic Church booleans?
- [ ] What's the advantage over untyped encodings?

### Practice Problems
From exercises/EXERCISES.md: Exercise 4

---

## Lesson 7.10: Type-in-Type and Universe Hierarchies (45-60 minutes)

### Learning Objectives
- Understand the Type : Type problem
- Learn about Girard's paradox
- See how real systems use universe hierarchies

### Materials
- README.md: "Type-in-Type Issue" section
- TUTORIAL.md: "Part 9: Universes"
- COMMON_MISTAKES.md: "Type-in-Type"

### Activities
1. **Read** (20 min): The Type : Type problem
2. **Understand** (15 min): Girard's paradox (like Russell's paradox)
3. **Solution** (15 min): Universe hierarchies:
   - `Type₀ : Type₁ : Type₂ : ...`
   - How Agda, Coq, Idris handle this
4. **Reflect** (10 min): Why our implementation uses Type : Type (pedagogical simplicity)

### Self-Check ✓
- [ ] Can you explain why Type : Type is inconsistent?
- [ ] What is Girard's paradox?
- [ ] How do universe hierarchies solve the problem?
- [ ] Why do we use Type : Type in this chapter anyway?

### Key Insight
Type-in-Type is logically inconsistent but pedagogically useful. Real systems need universe hierarchies.

---

## Lesson 7.11: Existential Types via Sigma (45 minutes)

### Learning Objectives
- Encode existential types using Σ
- Understand abstract data types
- See the connection between Σ and ∃

### Materials
- TUTORIAL.md: "Part 10: Existential Types"
- exercises/EXERCISES.md: Exercise 5

### Activities
1. **Read** (15 min): Existential encoding
2. **Examples** (20 min):
   - `Σ(A:Type). A` as "exists a type A and a value of A"
   - Abstract data types with hidden representations
   - Interface implementations
3. **Practice** (10 min): Create an existential package

### Self-Check ✓
- [ ] How does `Σ(A:Type). A` encode ∃A. A?
- [ ] Can you create an abstract data type?
- [ ] Why are Σ types more expressive than simple products?

### Practice Problems
From exercises/EXERCISES.md: Exercise 5

---

## Lesson 7.12: Implementation Study (60-90 minutes)

### Learning Objectives
- Understand bidirectional type checking
- See how normalization is implemented
- Read the Haskell implementation

### Materials
- Source code: src/TypeCheck.hs, src/Eval.hs, src/Syntax.hs
- README.md: "Implementation" section

### Activities
1. **Read Code** (40 min):
   - `src/Syntax.hs` - unified Term type
   - `src/TypeCheck.hs` - type checking with normalization
   - `src/Eval.hs` - evaluation and normalization
2. **Trace** (25 min): Follow type checking for:
   - `λ(A:Type). λ(x:A). x`
   - Application with substitution
3. **REPL** (15 min): Use all REPL commands:
   - `:type` to check types
   - `:step` to see evaluation
   - `:normalize` to get normal forms

### Self-Check ✓
- [ ] Do you understand the unified Term datatype?
- [ ] How is normalization used during type checking?
- [ ] Can you trace through a type checking example?

---

## Lesson 7.13: Theoretical Properties (60 minutes)

### Learning Objectives
- Understand decidability of type checking
- Appreciate strong normalization
- See the trade-offs

### Materials
- README.md: "Theoretical Properties" section
- TUTORIAL.md: "Part 11: Theory"

### Activities
1. **Read** (30 min): Decidability and normalization theorems
2. **Understand** (20 min):
   - Type checking is decidable ✓
   - Type inference is undecidable ✗
   - All programs terminate (strong normalization)
3. **Reflect** (10 min): What can't we write?
   - No general recursion (yet)
   - Need structural recursion or well-founded recursion

### Self-Check ✓
- [ ] Is type checking decidable?
- [ ] Is type inference decidable?
- [ ] Why do all well-typed programs terminate?
- [ ] What's the trade-off?

---

## Lesson 7.14: Exercises and Practice (3-5 hours)

### Learning Objectives
- Solidify understanding through practice
- Implement dependent type utilities
- Work with Π and Σ types

### Materials
- exercises/EXERCISES.md (all exercises)
- exercises/Solutions.hs (for reference)
- test/Spec.hs (automated tests)

### Activities
1. **Complete Exercises** (3-4 hours):
   - Exercise 1: Basic dependent functions (45 min)
   - Exercise 2: Dependent pairs (45 min)
   - Exercise 3: Type families (conceptual) (30 min)
   - Exercise 4: Church encodings (60 min)
   - Exercise 5: Existential types (45 min)
   - Exercise 6: Proof-relevant programming (30 min)
   - Exercise 7: Utilities (45 min)
2. **Test Your Work** (30 min):
   ```bash
   stack test --test-arguments "--match Exercises"
   ```
3. **Review Solutions** (30 min): Compare your solutions

### Self-Check ✓
- [ ] Have you completed at least Exercises 1-4?
- [ ] Do all tests pass?
- [ ] Do you understand the solutions?

---

## Lesson 7.15: Review and Integration (60 minutes)

### Learning Objectives
- Review all major concepts
- Test comprehensive understanding
- Prepare for Chapter 8

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Next Chapter" section

### Activities
1. **Self-Quiz** (30 min): Complete all questions in QUIZ.md
2. **Review** (20 min): Go over any missed topics
3. **Look Ahead** (10 min): Preview Chapter 8 (full dependent types)

### Final Self-Check ✓
Before moving to Chapter 8, you should be able to:
- [ ] Write Π and Σ types fluently
- [ ] Understand types depending on values
- [ ] Type check dependent type terms
- [ ] Explain the Curry-Howard correspondence
- [ ] Understand the Type-in-Type issue
- [ ] Work with normalization-based equality
- [ ] Score 80%+ on the quiz

### If You're Not There Yet
Review specific lessons where you struggled. Focus on:
1. Π and Σ types (most fundamental)
2. Type-level computation (most conceptually important)
3. Normalization (most technically crucial)

---

## Additional Resources

### If You Want More Practice
- Implement the theoretical exercises from EXERCISES.md
- Try encoding more data structures with dependent types
- Explore the Agda or Idris tutorials

### If You Want Deeper Theory
- Read Martin-Löf's "Intuitionistic Type Theory"
- Study the Calculus of Constructions (Coquand & Huet)
- Explore connections to category theory

### If You Want More Implementation
- Implement universe hierarchies
- Add η-equality
- Implement better error messages
- Add more type families

---

## Study Tips

### Time Management
- **Minimum**: 1.5-2 hours per day for 8-10 days
- **Recommended**: 3-4 hour sessions, 3-4 times per week
- **Intensive**: Complete in 5-6 days with 3-4 hour sessions

### Learning Strategies
1. **Build on System F**: Π is like ∀, but for values
2. **Draw Type Derivations**: Visual understanding helps
3. **Use the REPL**: Experiment constantly
4. **Compare with Previous Chapters**: See what's new
5. **Think About Real Examples**: Vectors, sorted lists, etc.
6. **Embrace Curry-Howard**: Types are specifications!

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Check if you need to normalize types
3. Use the REPL's `:type` command
4. Review TUTORIAL.md relevant section
5. Draw out the type derivation on paper

### Signs You're Ready for Chapter 8
- You understand Π and Σ types deeply
- Type-level computation makes sense
- You can write dependent types for real problems
- Curry-Howard correspondence is intuitive
- You're curious about inductive families

---

## Progress Tracker

Use this checklist to track your progress:

- [ ] Lesson 7.1: Motivation - Why Dependent Types?
- [ ] Lesson 7.2: Unified Term and Type Syntax
- [ ] Lesson 7.3: Pi Types - Dependent Functions
- [ ] Lesson 7.4: Sigma Types - Dependent Pairs
- [ ] Lesson 7.5: Type Checking with Dependency
- [ ] Lesson 7.6: Definitional Equality and Normalization
- [ ] Lesson 7.7: Type-Level Computation
- [ ] Lesson 7.8: The Curry-Howard Correspondence
- [ ] Lesson 7.9: Church Encodings with Dependent Types
- [ ] Lesson 7.10: Type-in-Type and Universe Hierarchies
- [ ] Lesson 7.11: Existential Types via Sigma
- [ ] Lesson 7.12: Implementation Study
- [ ] Lesson 7.13: Theoretical Properties
- [ ] Lesson 7.14: Exercises and Practice
- [ ] Lesson 7.15: Review and Integration

**Completed**: _____ / 15 lessons

---

## What's Next?

Once you've completed this chapter, you're ready for:

**Chapter 8: Full Dependent Types with Inductive Families**
- Inductive type families (Vec, Fin, List)
- Pattern matching and structural recursion
- Equality types and propositional equality
- Universe hierarchies (fixing Type-in-Type)
- Real theorem proving!
- Verified programs with correctness proofs

This is where dependent types truly shine - you'll prove properties about programs and write programs that carry their own correctness proofs!

The journey to verified programming continues!
