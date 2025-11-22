# Chapter 6: System F-omega (Higher-Kinded Types) - Lesson Plan

## Overview

This lesson plan guides you through System F-omega, which extends System F with **higher-kinded types** - allowing types to abstract over type constructors, not just types. This is the foundation for type classes, functors, and monads in real programming languages.

**Total Estimated Time**: 12-16 hours (can be spread over 1-2 weeks)

**Prerequisites**:
- Completed Chapter 5 (System F)
- Comfortable with type abstraction and type application
- Understanding of polymorphism
- Familiarity with System F's limitations (helpful)

**Key Addition**: In System F, types can be polymorphic over types. In F-omega, types can be polymorphic over **type constructors** - types that take types as parameters.

---

## Lesson 6.1: Motivation - Why Higher-Kinded Types? (30-45 minutes)

### Learning Objectives
- Understand what "higher-kinded" means
- See the limitations of System F
- Recognize higher-kinded types in real languages

### Materials
- README.md: "Overview" and "Motivation" sections
- Compare with Chapter 5's limitations

### Activities
1. **Recall System F** (10 min): Review polymorphic identity `∀A. A → A`
2. **Read** (15 min): Why we can't abstract over List, Maybe, etc. in System F
3. **Explore** (10 min): Real-world examples in Haskell and Scala

### Self-Check
- [ ] Can you explain why System F can't express Functor?
- [ ] What does "higher-kinded" mean?
- [ ] Do you understand the difference between `*` and `* → *`?

### Key Insight
System F lets us abstract over types like `Bool` and `Nat`. F-omega lets us abstract over type constructors like `List` and `Maybe`.

---

## Lesson 6.2: Kinds - Types of Types (60 minutes)

### Learning Objectives
- Understand the kind system
- Distinguish between `*`, `* → *`, and higher kinds
- Compute kinds for type expressions

### Materials
- README.md: "Syntax - Kinds" section
- CHEAT_SHEET.md: Kind system
- TUTORIAL.md: "Part 1: Understanding Kinds"

### Activities
1. **Read** (20 min): Kind syntax and intuition
2. **Examples** (25 min): Work through kinds of:
   - `Bool` (kind `*`)
   - `List` (kind `* → *`)
   - `Either` (kind `* → * → *`)
   - `Functor` (kind `(* → *) → *`)
3. **Practice** (15 min): Determine kinds for compound type expressions

### Self-Check
- [ ] Can you explain what kind `*` means?
- [ ] What kind does a type constructor like `List` have?
- [ ] Can you compute the kind of `(* → *) → * → *`?

### Common Pitfall
Don't confuse kinds with types! Kinds classify types, just as types classify terms.

---

## Lesson 6.3: Type-Level Lambda Abstraction (60-75 minutes)

### Learning Objectives
- Write type-level lambda terms
- Understand type operators
- Apply type-level beta reduction

### Materials
- README.md: "Syntax - Types" section
- TUTORIAL.md: "Part 2: Type-Level Lambda"
- CHEAT_SHEET.md: Type operators

### Activities
1. **Read** (20 min): Type-level lambda syntax `λα::κ. τ`
2. **Examples** (30 min): Work through:
   - Identity type operator: `λA::*. A`
   - Constant type operator: `λA::*. λB::*. A`
   - Compose type operator: `λF::* → *. λG::* → *. λA::*. F (G A)`
3. **Practice** (15 min): Write your own type operators

### Self-Check
- [ ] Can you write a type-level lambda?
- [ ] What's the kind of `λA::*. A`?
- [ ] Can you apply type operators to arguments?

### Key Insight
Types now form their own lambda calculus! All the concepts from Chapter 1 apply at the type level.

---

## Lesson 6.4: Kinding Rules (75-90 minutes)

### Learning Objectives
- Apply kinding rules to check type expressions
- Build kinding derivations
- Understand kind checking algorithm

### Materials
- README.md: "Kinding System" section
- TUTORIAL.md: "Part 3: Kinding Rules and Derivations"
- CHEAT_SHEET.md: Kinding rules

### Activities
1. **Read** (25 min): Kinding judgment `Γ ⊢ τ :: κ` and rules
2. **Practice** (40 min): Build kinding derivations for:
   - `λA::*. A → A` (should have kind `* → *`)
   - `λF::* → *. λA::*. F A` (should have kind `(* → *) → * → *`)
   - `(λA::*. A) Bool` (should have kind `*`)
3. **Algorithm** (15 min): Trace through kind checking algorithm

### Self-Check
- [ ] Can you apply K-Lam rule?
- [ ] Can you apply K-App rule?
- [ ] Can you build a complete kinding derivation?

### Practice Problems
From QUIZ.md: Questions 1-4

---

## Lesson 6.5: Type-Level Application and Reduction (60 minutes)

### Learning Objectives
- Apply type operators to type arguments
- Perform type-level beta reduction
- Normalize type expressions

### Materials
- README.md: "Type-Level Programming" section
- TUTORIAL.md: "Part 4: Type-Level Computation"

### Activities
1. **Read** (15 min): Type application and beta reduction at type level
2. **Practice** (30 min): Reduce these step-by-step:
   - `(λA::*. A) Bool`
   - `(λA::*. λB::*. A) Bool Nat`
   - `(λF::* → *. λG::* → *. λA::*. F (G A)) List Maybe Nat`
3. **Verify** (15 min): Check your work in the REPL

### Self-Check
- [ ] Can you apply the type-level beta reduction rule?
- [ ] Can you normalize type expressions?
- [ ] Do you see the parallel with term-level reduction?

---

## Lesson 6.6: Extended Type System (60-75 minutes)

### Learning Objectives
- Understand dual contexts (kind and type)
- Apply typing rules with kind checking
- Build complete typing derivations

### Materials
- README.md: "Type System" section
- TUTORIAL.md: "Part 5: Typing with Kinds"

### Activities
1. **Read** (20 min): Typing judgment `Γ; Δ ⊢ t : τ`
2. **Understand** (25 min): How kinding integrates with typing:
   - T-Abs requires well-kinded types
   - T-TAbs extends kind context
   - T-TApp checks kinds
3. **Practice** (20 min): Type check terms with kind checking

### Self-Check
- [ ] Can you explain the two contexts Γ and Δ?
- [ ] Why does T-Abs require `Γ ⊢ τ₁ :: *`?
- [ ] Can you apply T-TAbs and T-TApp?

### Key Insight
Type checking now has two levels: kind checking (are types well-formed?) and type checking (are terms well-typed?).

---

## Lesson 6.7: Church Encodings at Type Level (75-90 minutes)

### Learning Objectives
- Define Church-encoded type constructors
- Implement List, Maybe, and Either at type level
- Understand type-level data representation

### Materials
- README.md: "Type-Level Programming - Church Encodings" section
- TUTORIAL.md: "Part 6: Church-Encoded Type Constructors"
- exercises/EXERCISES.md: Exercises 2-4

### Activities
1. **Read** (20 min): Church encoding of List, Maybe, Either
2. **Understand** (30 min): Why these encodings work:
   - List as fold: `λA::*. ∀R::*. R → (A → R → R) → R`
   - Maybe as case analysis: `λA::*. ∀R::*. R → (A → R) → R`
   - Either as choice: `λA::*. λB::*. ∀R::*. (A → R) → (B → R) → R`
3. **Practice** (25 min): Exercises 2-4 (implement constructors)

### Self-Check
- [ ] Can you explain List's type-level encoding?
- [ ] What kind does `List` have?
- [ ] Can you apply `List` to `Bool` to get `List Bool`?

### Key Insight
Algebraic data types can be encoded as higher-kinded types using Church encoding!

---

## Lesson 6.8: Advanced Type Operators (60-75 minutes)

### Learning Objectives
- Write complex type operators
- Compose type constructors
- Implement type-level functions

### Materials
- TUTORIAL.md: "Part 7: Advanced Type Operators"
- exercises/EXERCISES.md: Exercises 1, 6, 8

### Activities
1. **Study Examples** (20 min):
   - Identity: `λA::*. A`
   - Const: `λA::*. λB::*. A`
   - Compose: `λF::* → *. λG::* → *. λA::*. F (G A)`
   - Flip: `λF::* → * → *. λA::*. λB::*. F B A`
2. **Practice** (35 min): Complete exercises 1, 6, 8
3. **Experiment** (10 min): Create your own type operators

### Self-Check
- [ ] Can you write Compose from scratch?
- [ ] Can you determine the kind of complex type operators?
- [ ] Do you understand type operator composition?

### Practice Problems
From exercises/EXERCISES.md: Exercises 1, 6, 8

---

## Lesson 6.9: Functor Pattern (60 minutes)

### Learning Objectives
- Understand the Functor pattern
- See how type classes relate to F-omega
- Implement functor-like operations

### Materials
- README.md: "Common Patterns - Functor Pattern" section
- TUTORIAL.md: "Part 8: The Functor Pattern"

### Activities
1. **Read** (20 min): Functor kind and operations
2. **Compare** (20 min): How Haskell's Functor relates to F-omega
3. **Understand** (20 min): Why we can't fully encode type classes

### Self-Check
- [ ] What kind must a type constructor have to be a Functor?
- [ ] Can you explain the connection to Haskell's type classes?
- [ ] Why does F-omega need extensions for full type class support?

### Real-World Connection
This is the foundation for Haskell's Functor, Applicative, and Monad type classes!

---

## Lesson 6.10: Implementation Study (75-90 minutes)

### Learning Objectives
- Understand kind checker implementation
- Read extended type checker code
- See how type-level evaluation works

### Materials
- Source code: src/Syntax.hs, src/TypeCheck.hs, src/Eval.hs
- README.md: "Implementation" section

### Activities
1. **Read Code** (40 min):
   - `src/Syntax.hs` - Kind and Type definitions
   - `src/TypeCheck.hs` - Kinding and type checking
   - `src/Eval.hs` - Type-level normalization
2. **Trace** (25 min): Follow kind checking for a type operator
3. **Experiment** (15 min): Try examples in GHCi

### Self-Check
- [ ] Do you understand the Kind datatype?
- [ ] How is type-level application implemented?
- [ ] Can you trace through kinding for a simple type?

---

## Lesson 6.11: Theoretical Properties (60 minutes)

### Learning Objectives
- Understand strong normalization at type level
- See why type checking is decidable
- Appreciate the theoretical foundations

### Materials
- README.md: "Theoretical Properties" section
- TUTORIAL.md: "Part 9: Metatheory"

### Activities
1. **Read** (30 min): Strong normalization, decidability theorems
2. **Reflect** (15 min): Why these properties matter
3. **Compare** (15 min): F-omega vs System F theoretical properties

### Self-Check
- [ ] Why does type-level computation always terminate?
- [ ] Is kind inference decidable?
- [ ] Why is type inference undecidable?

### Key Insight
The kind system prevents type-level non-termination, just as the type system in STLC prevents term-level non-termination!

---

## Lesson 6.12: Real-World Connections (45-60 minutes)

### Learning Objectives
- See F-omega in Haskell
- See F-omega in Scala
- Understand practical applications

### Materials
- README.md: "Connection to Real Languages" section
- TUTORIAL.md: "Part 10: Real-World Impact"

### Activities
1. **Haskell** (20 min): Study type classes and higher-kinded types
2. **Scala** (15 min): Look at higher-kinded type parameters
3. **Compare** (10 min): What can/can't be expressed

### Self-Check
- [ ] Can you recognize higher-kinded types in Haskell?
- [ ] How does Scala's `F[_]` relate to F-omega?
- [ ] What extensions do real languages add?

### Real-World Examples
```haskell
-- Haskell: Functor type class
class Functor f where  -- f :: * → *
  fmap :: (a -> b) -> f a -> f b
```

---

## Lesson 6.13: Exercises and Practice (3-5 hours)

### Learning Objectives
- Solidify understanding through practice
- Implement all type operators
- Verify solutions with tests

### Materials
- exercises/EXERCISES.md (all exercises)
- exercises/Solutions.hs (for hints)
- test/Spec.hs (automated tests)

### Activities
1. **Exercise 1** (45 min): Basic type operators (Id, Const, Compose)
2. **Exercise 2** (60 min): List type constructor
3. **Exercise 3** (45 min): Maybe type constructor
4. **Exercise 4** (60 min): Either type constructor
5. **Exercise 5** (30 min): Functor kind (conceptual)
6. **Exercise 6** (45 min): Type-level Church encodings
7. **Exercise 7** (30 min): Product and Sum operators
8. **Exercise 8** (45 min): Advanced operators (optional)

### Self-Check
- [ ] Have you completed exercises 1-7?
- [ ] Do all tests pass?
- [ ] Do you understand the solutions?

### Don't Give Up!
Some exercises (like Compose and Either) are conceptually challenging. Take your time!

---

## Lesson 6.14: Review and Integration (60 minutes)

### Learning Objectives
- Review all major concepts
- Test comprehensive understanding
- Prepare for Chapter 7

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Next Chapter" section

### Activities
1. **Self-Quiz** (30 min): Complete all questions in QUIZ.md
2. **Review** (20 min): Go over anything you missed
3. **Look Ahead** (10 min): Preview Chapter 7 (Dependent Types)

### Final Self-Check
Before moving to Chapter 7, you should be able to:
- [ ] Explain what kinds are and why we need them
- [ ] Write and kind-check type operators
- [ ] Perform type-level computation
- [ ] Understand Church-encoded type constructors
- [ ] See the connection to real language features
- [ ] Score 80%+ on the quiz

### If You're Not There Yet
Review specific lessons where you struggled. Focus on:
1. Kinding rules (most fundamental)
2. Type-level lambda and application (core mechanism)
3. Church encodings (most practical skill)

---

## Study Tips

### Time Management
- **Minimum**: 1.5-2 hours per day for 7-10 days
- **Recommended**: 2-3 hour sessions, 4-5 times per week
- **Intensive**: Complete in 4-5 days with 3-4 hour sessions

### Learning Strategies
1. **Master Kinds First**: Everything builds on understanding `*` vs `* → *`
2. **Draw Kind Diagrams**: Visualize type operator applications
3. **Compare with System F**: See what's new vs what's the same
4. **Use the REPL**: Experiment with type normalization
5. **Connect to Languages**: Relate to Haskell/Scala features
6. **Practice Type Operators**: Write many small examples

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Compare kinds carefully (most common issue)
3. Draw out type operator applications
4. Use the REPL to normalize types
5. Review TUTORIAL.md relevant section
6. Look at working examples

### Signs You're Ready for Chapter 7
- You can write type operators fluently
- Kinding makes intuitive sense
- You understand the List, Maybe, Either encodings
- You see how this relates to real programming languages
- You're curious about types depending on values (dependent types!)

---

## Progress Tracker

Use this checklist to track your progress:

- [ ] Lesson 6.1: Motivation - Why Higher-Kinded Types?
- [ ] Lesson 6.2: Kinds - Types of Types
- [ ] Lesson 6.3: Type-Level Lambda Abstraction
- [ ] Lesson 6.4: Kinding Rules
- [ ] Lesson 6.5: Type-Level Application and Reduction
- [ ] Lesson 6.6: Extended Type System
- [ ] Lesson 6.7: Church Encodings at Type Level
- [ ] Lesson 6.8: Advanced Type Operators
- [ ] Lesson 6.9: Functor Pattern
- [ ] Lesson 6.10: Implementation Study
- [ ] Lesson 6.11: Theoretical Properties
- [ ] Lesson 6.12: Real-World Connections
- [ ] Lesson 6.13: Exercises and Practice
- [ ] Lesson 6.14: Review and Integration

**Completed**: _____ / 14 lessons

---

## Additional Resources

### If You Want More Practice
- Implement "Additional Challenges" from EXERCISES.md
- Try encoding other type constructors (Tree, Stream, etc.)
- Implement type-level natural numbers

### If You Want Deeper Theory
- Read Barendregt's "Lambda Calculi with Types" (Chapter on F-omega)
- Study Girard's original presentation
- Explore connections to category theory (functors as mathematical functors)

### If You Want More Implementation
- Implement kind inference
- Add kind polymorphism
- Build a type-level evaluator with trace output
- Extend to System F-omega-mu (recursive types)

---

## What's Next?

Once you've completed this chapter, you're ready for:

**Chapter 7: Simply Typed Dependent Calculus (λΠ)**
- Types that depend on values (not just types!)
- Propositions as types, proofs as programs
- Π-types (dependent function types)
- The Curry-Howard correspondence
- Foundation for proof assistants like Coq and Agda

The journey from F-omega to dependent types is profound:
- F-omega: Types depending on types
- Dependent types: Types depending on values
- Full spectrum dependent types: The ultimate unification!

You're approaching the cutting edge of type theory!
