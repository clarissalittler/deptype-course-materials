# Chapter 8: Full Dependent Types - Lesson Plan

## Overview

This lesson plan guides you through the culmination of our journey: **full dependent type theory** with universe hierarchy, equality types, inductive families, and eliminators. This is the foundation of modern proof assistants like Coq, Agda, Lean, and Idris.

**Total Estimated Time**: 16-20 hours (can be spread over 2-3 weeks)

**Prerequisites**:
- Completed Chapter 7 (Simply Typed Dependent Lambda Calculus)
- Strong understanding of Pi types and Sigma types
- Comfortable with dependent functions and type-level computation
- Understanding of the Type-in-Type problem from Chapter 7

**Key Achievement**: By the end of this chapter, you'll understand the theoretical foundation of modern proof assistants and be ready to use Coq, Agda, Lean, or Idris for verified programming and theorem proving.

---

## Lesson 8.1: Motivation - The Type-in-Type Problem (45-60 minutes)

### Learning Objectives
- Understand why Type : Type is inconsistent
- See how Girard's paradox breaks the logic
- Appreciate the need for universe hierarchy
- Understand the trade-offs of stratification

### Materials
- README.md: "Motivation" section
- Chapter 7 materials (for comparison)
- TUTORIAL.md: "Part 1: The Type-in-Type Problem"

### Activities
1. **Review** (15 min): Recall Chapter 7's Type : Type
2. **Read** (20 min): Understanding Girard's paradox
3. **Reflect** (10 min): Why does this matter?
4. **Preview** (10 min): How universe hierarchy solves this

### Self-Check ✓
- [ ] Can you explain why Type : Type leads to inconsistency?
- [ ] Do you understand what "inconsistency" means (proving False)?
- [ ] Can you see the analogy to Russell's paradox?

### Key Insight
Type-in-Type lets us encode paradoxes. With `Type : Type`, we can prove False, making the entire system useless for proving theorems.

---

## Lesson 8.2: Universe Hierarchy Basics (60-75 minutes)

### Learning Objectives
- Understand the infinite hierarchy Type 0 : Type 1 : Type 2 : ...
- Compute universe levels for types
- Apply the Pi-type level rule
- Understand predicativity

### Materials
- README.md: "Universe Hierarchy" section
- CHEAT_SHEET.md: Universe levels
- TUTORIAL.md: "Part 2: Universe Hierarchy"

### Activities
1. **Read** (25 min): Universe hierarchy rules and levels
2. **Practice** (30 min): Compute levels for:
   - `Nat`, `Bool`, `Nat → Bool`
   - `Type 0 → Type 0`
   - `Π(A:Type 0). A → A`
   - `Π(A:Type 1). A → A`
3. **Understand** (15 min): Why do we need different levels of `id`?

### Self-Check ✓
- [ ] Can you state the typing rule for Type i?
- [ ] Can you compute the level of `Π(x:A). B` given levels of A and B?
- [ ] Do you understand predicativity vs. impredicativity?

### Common Pitfall
The level of `Π(x:A). B` is max(level(A), level(B)), not their sum!

---

## Lesson 8.3: Cumulativity and Level Inference (45 minutes)

### Learning Objectives
- Understand cumulativity (Type i ⊆ Type (i+1))
- See why cumulativity simplifies usage
- Understand the trade-offs (complexity vs. convenience)

### Materials
- README.md: "Cumulativity" section
- TUTORIAL.md: "Part 3: Cumulativity"

### Activities
1. **Read** (20 min): Cumulativity rules
2. **Compare** (15 min): Systems with and without cumulativity
3. **Explore** (10 min): How real systems handle this (Coq, Agda)

### Self-Check ✓
- [ ] Can you explain what cumulativity means?
- [ ] Why does it make the system easier to use?
- [ ] What complexity does it add?

### Optional Deep Dive
Our implementation uses strict universes (no cumulativity) for simplicity. Real systems like Coq include cumulativity.

---

## Lesson 8.4: Propositional Equality - Introduction (60-75 minutes)

### Learning Objectives
- Distinguish definitional from propositional equality
- Understand the Eq type constructor
- Use reflexivity (refl)
- See why we only need refl (not sym/trans as constructors)

### Materials
- README.md: "Equality Types" section
- TUTORIAL.md: "Part 4: Propositional Equality"
- CHEAT_SHEET.md: Equality types

### Activities
1. **Read** (25 min): Definitional vs. propositional equality
2. **Understand** (20 min): Why `Eq A x y` is a type
3. **Practice** (15 min): Write equality types:
   - `Eq Nat 2 2`
   - `Eq Nat (1 + 1) 2`
   - `Eq (Nat → Nat) (λn. n) (λm. m)`
4. **Reflect** (10 min): When can we use `refl`?

### Self-Check ✓
- [ ] Can you explain the difference between ≡ (definitional) and Eq (propositional)?
- [ ] Why does `refl 2 : Eq Nat 2 2` type check?
- [ ] Why doesn't `refl : Eq Nat (n + 0) n` work without proof?

### Key Insight
Definitional equality is what the type checker knows automatically. Propositional equality is what we can prove.

---

## Lesson 8.5: The J Eliminator (90-120 minutes)

### Learning Objectives
- Understand the J eliminator as equality induction
- Apply J to derive symmetry, transitivity, and congruence
- See the computation rule for J
- Understand why J is the fundamental principle for equality

### Materials
- README.md: "The J Eliminator" section
- TUTORIAL.md: "Part 5: The J Eliminator"
- exercises/EXERCISES.md: Exercise 2

### Activities
1. **Read** (30 min): J eliminator type and intuition
2. **Study** (30 min): Deriving symmetry using J
3. **Practice** (40 min): Exercise 2 - derive transitivity and congruence
4. **REPL Exercise** (15 min): Test your implementations

### Self-Check ✓
- [ ] Can you state the type of J from memory?
- [ ] Do you understand the computation rule: `J A C p x x (refl x) ~> p`?
- [ ] Can you explain why J is sufficient to derive all equality properties?
- [ ] Can you derive symmetry using J?

### This Is Hard!
J is one of the most conceptually challenging parts of type theory. Take your time. Draw diagrams. Work through examples slowly.

### Practice Problems
From exercises/EXERCISES.md: Exercise 2 (Equality Types and Proofs)

---

## Lesson 8.6: Equality Proofs in Practice (60-75 minutes)

### Learning Objectives
- Write concrete equality proofs
- Use congruence to build larger proofs
- Understand proof composition
- See examples of arithmetic proofs

### Materials
- TUTORIAL.md: "Part 6: Writing Equality Proofs"
- README.md: Examples section
- CHEAT_SHEET.md: Common proofs

### Activities
1. **Read** (20 min): Examples of equality proofs
2. **Practice** (35 min): Prove:
   - Symmetry of a specific equality
   - Transitivity chain
   - `succ (n + m) = (succ n) + m` using congruence
3. **REPL Exercise** (15 min): Check your proofs

### Self-Check ✓
- [ ] Can you write a proof of symmetry for a specific case?
- [ ] Can you chain together equality proofs using transitivity?
- [ ] Do you understand how congruence lets you apply functions to equalities?

### Practice Problems
From exercises/EXERCISES.md: Exercise 3 (Natural Number Proofs)

---

## Lesson 8.7: Inductive Families - Vectors (75-90 minutes)

### Learning Objectives
- Understand inductive families vs. simple inductive types
- See how Vec encodes length in the type
- Distinguish parameters from indices
- Implement safe operations on vectors

### Materials
- README.md: "Inductive Families" section
- TUTORIAL.md: "Part 7: Inductive Families - Vectors"
- CHEAT_SHEET.md: Vec definition

### Activities
1. **Read** (25 min): Inductive families and the Vec type
2. **Understand** (20 min): How Vec's constructors work
3. **Practice** (30 min): Exercise 4 - implement head and append for vectors
4. **REPL Exercise** (10 min): Create and manipulate vectors

### Self-Check ✓
- [ ] Can you explain the difference between parameters and indices?
- [ ] Why does `Nil` have type `Vec 0 A` and not `Vec n A`?
- [ ] Why can `head` only be called on `Vec (succ n) A`?
- [ ] How does the type system prevent calling head on empty vectors?

### Key Insight
Inductive families let indices vary across constructors, encoding invariants directly in types.

### Practice Problems
From exercises/EXERCISES.md: Exercise 4 (Vector Type)

---

## Lesson 8.8: The Fin Type - Bounded Numbers (60 minutes)

### Learning Objectives
- Understand Fin n as natural numbers less than n
- See how Fin prevents array bounds errors
- Implement safe indexing using Fin
- Understand the "propositions as types" interpretation

### Materials
- README.md: "The Fin Type" section
- TUTORIAL.md: "Part 8: Bounded Natural Numbers (Fin)"
- exercises/EXERCISES.md: Exercise 5

### Activities
1. **Read** (20 min): Fin type definition and intuition
2. **Explore** (15 min): Count inhabitants of Fin 0, Fin 1, Fin 3
3. **Practice** (20 min): Exercise 5 - implement safe lookup
4. **Reflect** (5 min): How does this prevent bugs?

### Self-Check ✓
- [ ] Can you construct all inhabitants of Fin 3?
- [ ] Why is Fin 0 empty?
- [ ] Can you explain the type of lookup: `Vec n A → Fin n → A`?
- [ ] How does this guarantee no out-of-bounds errors?

### Real-World Impact
This is how Idris prevents array indexing errors at compile time!

---

## Lesson 8.9: Eliminators and Induction Principles (75-90 minutes)

### Learning Objectives
- Understand eliminators as induction principles
- Use natElim to define functions
- See how eliminators guarantee termination
- Understand the difference between recursion and elimination

### Materials
- README.md: "Eliminators" section
- TUTORIAL.md: "Part 9: Eliminators"
- CHEAT_SHEET.md: Key eliminators

### Activities
1. **Read** (25 min): Eliminators for Nat, Bool, Unit, Empty
2. **Practice** (30 min): Implement using eliminators:
   - Addition using natElim
   - Multiplication using natElim
   - Boolean AND using boolElim
3. **Compare** (15 min): Eliminators vs. pattern matching
4. **Understand** (10 min): Why eliminators guarantee termination

### Self-Check ✓
- [ ] Can you state the type of natElim?
- [ ] Can you implement addition using natElim?
- [ ] Do you understand why eliminators always terminate?
- [ ] Can you explain the connection to mathematical induction?

### Key Insight
Eliminators are the principled way to do recursion in type theory. They embody induction principles.

---

## Lesson 8.10: Pattern Matching (60-75 minutes)

### Learning Objectives
- Use pattern matching syntax
- Understand dependent pattern matching
- See how pattern matching refines types
- Understand compilation to eliminators

### Materials
- README.md: "Pattern Matching" section
- TUTORIAL.md: "Part 10: Pattern Matching"

### Activities
1. **Read** (20 min): Pattern matching syntax and semantics
2. **Practice** (25 min): Implement using pattern matching:
   - head for vectors
   - tail for vectors
   - Boolean operations
3. **Understand** (15 min): How patterns refine types
4. **Study** (10 min): Coverage checking

### Self-Check ✓
- [ ] Can you write a pattern match for Nat?
- [ ] Why doesn't head need a Nil case?
- [ ] How does matching on constructors refine types?
- [ ] What is coverage checking?

### Key Insight
Pattern matching is syntactic sugar for eliminators, but with type refinement.

---

## Lesson 8.11: Curry-Howard Correspondence (75-90 minutes)

### Learning Objectives
- Understand propositions as types
- See proofs as programs
- Map logical connectives to type constructors
- Write proofs as functional programs

### Materials
- README.md: "Curry-Howard Correspondence" section
- TUTORIAL.md: "Part 11: Propositions as Types"
- CHEAT_SHEET.md: Logic/Type correspondence table

### Activities
1. **Read** (30 min): Complete Curry-Howard correspondence
2. **Study** (20 min): How each logical connective maps to types
3. **Practice** (25 min): Exercise 6 - write proofs of:
   - Modus ponens
   - Double negation introduction
   - Explosion (ex falso quodlibet)

### Self-Check ✓
- [ ] Can you map AND, OR, IMPLIES to type constructors?
- [ ] What is the type corresponding to `∀x. P(x)`?
- [ ] What is the type corresponding to `∃x. P(x)`?
- [ ] Why is `Empty → A` the principle of explosion?

### Mind-Blowing Insight
Proofs are programs. Type checking is proof checking. Types are propositions.

### Practice Problems
From exercises/EXERCISES.md: Exercise 6 (Empty and Unit Types)

---

## Lesson 8.12: Real-World Proof Assistants (60-75 minutes)

### Learning Objectives
- See how Chapter 8 concepts appear in Coq
- Understand Agda's syntax and approach
- Explore Lean's tactics
- Appreciate real-world verified software

### Materials
- README.md: "Real-World Connections" section
- CHEAT_SHEET.md: Real-world systems examples

### Activities
1. **Read** (20 min): Overview of Coq, Agda, Lean, Idris
2. **Explore** (25 min): Look at example proofs in each system
3. **Research** (15 min): Pick one verified project (CompCert, seL4, etc.)
4. **Compare** (10 min): Chapter 8 vs. real systems

### Self-Check ✓
- [ ] Can you name three proof assistants based on dependent types?
- [ ] What is CompCert and why is it significant?
- [ ] Can you recognize universe levels in Coq/Agda syntax?
- [ ] Which proof assistant appeals to you most?

### Real-World Impact
- **CompCert**: Verified C compiler (zero bugs in 10+ years)
- **seL4**: Verified microkernel in autonomous vehicles
- **HACL***: Verified cryptography in Firefox
- **mathlib**: Formalized mathematics in Lean

---

## Lesson 8.13: Intensional vs. Extensional Equality (45-60 minutes)

### Learning Objectives
- Understand intensional equality
- See the limitations (no function extensionality)
- Understand the K axiom
- Appreciate Homotopy Type Theory's rejection of K

### Materials
- README.md: "Intensional vs. Extensional Equality" section
- TUTORIAL.md: "Part 12: Advanced Equality Topics"

### Activities
1. **Read** (25 min): Intensional vs. extensional equality
2. **Understand** (15 min): Why function extensionality doesn't hold
3. **Explore** (10 min): The K axiom and its consequences
4. **Preview** (10 min): Homotopy Type Theory (optional)

### Self-Check ✓
- [ ] Can you explain intensional equality?
- [ ] Why might two behaviorally equal functions not be provably equal?
- [ ] What is the K axiom?
- [ ] Why does HoTT reject K?

### Advanced Topic
This is cutting-edge research! HoTT provides a new foundation for mathematics.

---

## Lesson 8.14: Implementation Study (90-120 minutes)

### Learning Objectives
- Understand the implementation of universe levels
- See how equality types are implemented
- Study the eliminator implementations
- Read and understand the Haskell code

### Materials
- Source code: src/Syntax.hs, src/TypeCheck.hs, src/Eval.hs
- README.md: "Implementation" section
- REPL_GUIDE.md

### Activities
1. **Read Code** (45 min):
   - `src/Syntax.hs` - How are universes represented?
   - `src/TypeCheck.hs` - How is universe checking implemented?
   - `src/Eval.hs` - How are eliminators evaluated?
2. **Trace** (30 min): Follow type checking for a term with universes
3. **Experiment** (30 min):
   - Load the REPL: `stack run`
   - Try universe level examples
   - Test equality proofs
   - Use eliminators

### Self-Check ✓
- [ ] Do you understand the Universe datatype?
- [ ] How are universe levels checked?
- [ ] Can you trace through natElim evaluation?
- [ ] Have you successfully run the REPL?

### Optional Deep Dive
Try implementing:
- Cumulativity
- Universe polymorphism
- Additional inductive types

---

## Lesson 8.15: Exercises and Practice (4-6 hours)

### Learning Objectives
- Solidify understanding through comprehensive practice
- Implement proofs and data structures
- Work with universe hierarchy
- Complete all chapter exercises

### Materials
- exercises/EXERCISES.md (all exercises)
- test/ExerciseSpec.hs (automated tests)

### Activities
1. **Complete All Exercises** (4-5 hours):
   - Exercise 1: Universe hierarchy
   - Exercise 2: Equality types and proofs
   - Exercise 3: Natural number proofs
   - Exercise 4: Vector type
   - Exercise 5: Fin type
   - Exercise 6: Empty and Unit types
   - Exercise 7: Leibniz equality
   - Exercise 8: Decidable equality
2. **Test Your Work** (30 min):
   ```bash
   stack test --test-arguments "--match Exercises"
   ```
3. **Review** (30 min): Compare with any provided solutions

### Self-Check ✓
- [ ] Have you completed Exercises 1-6?
- [ ] Have you attempted the theoretical exercises?
- [ ] Do your proofs type check?
- [ ] Do you understand the solutions?

### This Is Challenging!
These exercises are significantly harder than previous chapters. Take breaks. Ask for help. Work through examples slowly.

---

## Lesson 8.16: Review and Integration (90 minutes)

### Learning Objectives
- Review all major concepts
- Test comprehensive understanding
- Connect concepts together
- Prepare for real proof assistant use

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Summary" section

### Activities
1. **Self-Quiz** (40 min): Complete all questions in QUIZ.md
2. **Review Mistakes** (20 min): Study anything you got wrong
3. **Cheat Sheet** (15 min): Ensure you understand everything
4. **Synthesis** (15 min): How do all the pieces fit together?

### Final Self-Check ✓
Before using real proof assistants, you should be able to:
- [ ] Explain why we need universe hierarchy
- [ ] Write equality proofs using J
- [ ] Work with inductive families (Vec, Fin)
- [ ] Understand eliminators and induction principles
- [ ] Map between logic and types (Curry-Howard)
- [ ] Recognize these concepts in Coq/Agda/Lean
- [ ] Score 75%+ on the quiz

### If You're Not There Yet
Focus on:
1. Universe hierarchy (most fundamental)
2. J eliminator (most powerful)
3. Inductive families (most practical)
4. Curry-Howard correspondence (most mind-bending)

---

## Additional Resources

### If You Want More Practice
- Install Coq and work through Software Foundations (Volume 1)
- Try Agda tutorials
- Explore Lean's Natural Number Game
- Implement additional inductive families

### If You Want Deeper Theory
- Read Martin-Löf's "Intuitionistic Type Theory"
- Study Homotopy Type Theory book
- Explore categorical semantics of type theory
- Read about observational equality

### If You Want Practical Application
- Use Coq to verify small programs
- Write proofs in Agda
- Try Idris for dependently typed programming
- Contribute to mathlib in Lean

### Recommended Next Steps
1. **Software Foundations** (Coq): https://softwarefoundations.cis.upenn.edu/
2. **Agda Tutorial**: https://agda.readthedocs.io/
3. **Lean's Natural Number Game**: https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/
4. **HoTT Book**: https://homotopytypetheory.org/book/

---

## Study Tips

### Time Management
- **Minimum**: 2 hours per day for 8-10 days
- **Recommended**: 3-4 hour sessions, 4-5 times per week
- **Intensive**: Complete in 5-7 days with 3-4 hour sessions

### Learning Strategies
1. **Build on Chapter 7**: This extends what you already know
2. **Draw Diagrams**: Visualize universe levels, equality proofs
3. **Write Things Out**: Derivation trees, proof terms
4. **Use the REPL**: Test everything
5. **Work Examples**: Don't just read - do!
6. **Connect to Logic**: Use your mathematical intuition
7. **Be Patient**: This is the hardest chapter - it's supposed to be challenging

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Work simpler examples first
3. Draw out the types and terms
4. Use the REPL to check intermediate steps
5. Review relevant tutorial sections
6. Look at CHEAT_SHEET.md for quick reference
7. Take a break and come back fresh

### Signs You're Ready for Real Proof Assistants
- Universe levels make sense
- You can derive equality properties using J
- Inductive families feel natural
- You see the Curry-Howard connection
- You're excited to prove real theorems!

---

## Progress Tracker

Use this checklist to track your progress:

- [ ] Lesson 8.1: Motivation - The Type-in-Type Problem
- [ ] Lesson 8.2: Universe Hierarchy Basics
- [ ] Lesson 8.3: Cumulativity and Level Inference
- [ ] Lesson 8.4: Propositional Equality - Introduction
- [ ] Lesson 8.5: The J Eliminator
- [ ] Lesson 8.6: Equality Proofs in Practice
- [ ] Lesson 8.7: Inductive Families - Vectors
- [ ] Lesson 8.8: The Fin Type - Bounded Numbers
- [ ] Lesson 8.9: Eliminators and Induction Principles
- [ ] Lesson 8.10: Pattern Matching
- [ ] Lesson 8.11: Curry-Howard Correspondence
- [ ] Lesson 8.12: Real-World Proof Assistants
- [ ] Lesson 8.13: Intensional vs. Extensional Equality
- [ ] Lesson 8.14: Implementation Study
- [ ] Lesson 8.15: Exercises and Practice
- [ ] Lesson 8.16: Review and Integration

**Completed**: _____ / 16 lessons

---

## What's Next?

Congratulations on completing the course! You've journeyed from the untyped lambda calculus to full dependent types. You now understand:

- The foundations of computation (Chapters 1-2)
- Type systems and their guarantees (Chapters 2-4)
- Polymorphism and type inference (Chapter 4)
- Subtyping and object-oriented features (Chapter 5)
- System F and parametric polymorphism (Chapter 6)
- Dependent types and type-level programming (Chapter 7)
- Full dependent types and proof assistants (Chapter 8)

### Where to Go From Here

**Option 1: Become a Coq User**
- Work through Software Foundations
- Verify real programs
- Contribute to verified software projects

**Option 2: Explore Agda**
- Learn practical dependently typed programming
- Write proofs as programs
- Explore cubical Agda (modern HoTT)

**Option 3: Use Lean**
- Learn mathematical theorem proving
- Contribute to mathlib
- Use powerful tactics for automation

**Option 4: Try Idris**
- Practical dependently typed programming
- Build real applications with types
- Explore type-driven development

**Option 5: Go Deeper**
- Study Homotopy Type Theory
- Explore categorical semantics
- Research in type theory

### The Journey Continues

You've mastered the theoretical foundations. Now it's time to apply them:
- Prove real theorems
- Verify actual programs
- Build certified systems
- Advance the field

**Welcome to the world of dependently typed programming and mechanized theorem proving!**

You're ready. Go build amazing things. 🎓
