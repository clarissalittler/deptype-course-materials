# Chapter 4: Hindley-Milner Type Inference - Lesson Plan

## Overview

This lesson plan guides you through the crown jewel of type systems: **automatic type inference**. You'll learn how to write programs without type annotations while maintaining complete type safety. This is the system that powers ML, OCaml, Haskell, F#, and many other functional languages.

**Total Estimated Time**: 12-16 hours (can be spread over 2 weeks)

**Prerequisites**:
- Completed Chapter 2 (Simply Typed Lambda Calculus)
- Understanding of typing rules and type checking
- Comfortable with substitution (from Chapter 1)
- Chapter 3 (STLC with ADTs) helpful but not required

**Key Innovation**: In Chapter 2, you wrote `λx:Bool. x`. In Chapter 4, you write `λx. x` and the type is **automatically inferred**!

---

## Lesson 4.1: Motivation - Why Type Inference? (30-45 minutes)

### Learning Objectives
- Understand the limitations of explicit type annotations
- See how type inference improves productivity
- Appreciate the balance between safety and convenience
- Recognize type inference in real programming languages

### Materials
- README.md: "Overview" section
- Compare with Chapter 2's explicit annotations
- CHEAT_SHEET.md: "Key Idea" section

### Activities
1. **Recall Pain Points** (10 min): From Chapter 2, remember writing:
   - `λf:Nat→Nat. λx:Nat. f (f x)` - so many annotations!
   - What if you could just write: `λf. λx. f (f x)`?
2. **Read** (15 min): Overview and real-world connections
3. **Explore** (10 min): Look at Haskell/OCaml examples where types are inferred

### Self-Check
- [ ] Can you explain the trade-off: STLC vs Hindley-Milner?
- [ ] What does "principal type" mean?
- [ ] Which real-world languages use Hindley-Milner?

### Key Insight
Type inference isn't magic - it's a clever algorithm that solves equations!

---

## Lesson 4.2: Type Variables and Monotypes (45-60 minutes)

### Learning Objectives
- Understand type variables (α, β, γ)
- Distinguish monotypes from polytypes
- Write types with variables
- See how type variables enable generality

### Materials
- README.md: "Syntax" section (Types)
- TUTORIAL.md: "Part 1: Type Variables"
- CHEAT_SHEET.md: Type schemes

### Activities
1. **Read** (20 min): Type syntax with variables
2. **Practice** (25 min): Work with type variables:
   - `α → α` (identity type)
   - `α → β → α` (const type)
   - `(β → γ) → (α → β) → α → γ` (compose type)
3. **Understand** (10 min): Why variables? They represent "any type"

### Self-Check
- [ ] Can you explain what `α` represents?
- [ ] What's the difference between `α → α` and `α → β`?
- [ ] Why do we need type variables for polymorphism?

---

## Lesson 4.3: Type Substitutions (60 minutes)

### Learning Objectives
- Understand type substitutions [α ↦ τ]
- Apply substitutions to types
- Compose substitutions
- See substitutions as solutions to equations

### Materials
- README.md: "Type Substitutions" section
- TUTORIAL.md: "Part 2: Type Substitutions"
- COMMON_MISTAKES.md: "Substitution Composition" section

### Activities
1. **Read** (20 min): Substitution definition and operations
2. **Practice** (30 min): Apply substitutions:
   - `[α ↦ Nat](α → α)` = `Nat → Nat`
   - `[α ↦ Bool, β ↦ Nat](α → β)` = `Bool → Nat`
   - `[α ↦ β → γ](α → α)` = `(β → γ) → (β → γ)`
3. **Compose** (10 min): Practice substitution composition

### Self-Check
- [ ] Can you apply a substitution to a type?
- [ ] Do you understand substitution composition?
- [ ] Can you see substitutions as "solving for type variables"?

### Key Insight
Substitutions are like solutions to algebra: if `α = Nat`, replace all `α` with `Nat`.

---

## Lesson 4.4: Unification Algorithm (75-90 minutes)

### Learning Objectives
- Understand the unification problem
- Apply Robinson's unification algorithm
- Perform the occurs check
- Find most general unifiers (mgu)

### Materials
- README.md: "Unification" section
- TUTORIAL.md: "Part 3: Unification"
- COMMON_MISTAKES.md: "Occurs Check" section

### Activities
1. **Read** (25 min): Unification algorithm and examples
2. **Practice** (40 min): Unify these type pairs:
   - `unify(α, Nat)` = `[α ↦ Nat]`
   - `unify(α → β, Nat → Bool)` = `[α ↦ Nat, β ↦ Bool]`
   - `unify(α, α → β)` = **FAIL** (occurs check!)
   - `unify(α → α, β → Nat)` = `[α ↦ Nat, β ↦ Nat]`
3. **Occurs Check** (15 min): Why is `α = α → β` impossible?
4. **REPL Exercise** (10 min): See unification in action

### Self-Check
- [ ] Can you unify two types by hand?
- [ ] Do you understand the occurs check?
- [ ] Why does `α = α → β` create an infinite type?
- [ ] What is the "most general unifier"?

### Common Pitfall
Forgetting the occurs check leads to infinite types!

### Key Insight
Unification is like solving equations: `α → β = Nat → Bool` means `α = Nat` and `β = Bool`.

---

## Lesson 4.5: Type Schemes and Polymorphism (60 minutes)

### Learning Objectives
- Understand type schemes (∀α. τ)
- Distinguish polymorphic from monomorphic types
- Apply generalization
- Apply instantiation

### Materials
- README.md: "Type Schemes and Generalization" section
- TUTORIAL.md: "Part 4: Type Schemes"
- CHEAT_SHEET.md: Generalization vs. Instantiation

### Activities
1. **Read** (20 min): Type schemes, generalization, instantiation
2. **Practice Generalization** (15 min):
   - `gen(∅, α → α)` = `∀α. α → α`
   - `gen({x:α}, α → β)` = `∀β. α → β` (α not generalized!)
3. **Practice Instantiation** (15 min):
   - `inst(∀α. α → α)` = `β → β` (β fresh)
   - Each use gets fresh variables!
4. **Understand** (10 min): Why generalize at let, not lambda?

### Self-Check
- [ ] What does ∀α mean?
- [ ] When do we generalize?
- [ ] When do we instantiate?
- [ ] Why can't we generalize variables free in the environment?

### Key Insight
Generalization: "capture the variables". Instantiation: "make fresh copies".

---

## Lesson 4.6: Algorithm W - The Core (90-120 minutes)

### Learning Objectives
- Understand Algorithm W
- Apply W to infer types for variables
- Apply W to infer types for abstractions
- Apply W to infer types for applications
- Build complete type derivations

### Materials
- README.md: "Algorithm W" section
- TUTORIAL.md: "Part 5: Algorithm W Step-by-Step"
- CHEAT_SHEET.md: Algorithm W simplified

### Activities
1. **Read** (30 min): Algorithm W rules and intuition
2. **Simple Examples** (30 min): Infer types for:
   - `λx. x` → `α → α`
   - `λx. λy. x` → `α → β → α`
   - `λf. λx. f x` → `(α → β) → α → β`
3. **Complex Examples** (40 min):
   - `λf. λx. f (f x)` → `(α → α) → α → α`
   - `λf. λg. λx. f (g x)` → `(β → γ) → (α → β) → α → γ`
4. **REPL Exercise** (20 min): Use `:type` to verify your answers

### Self-Check
- [ ] Can you apply the W-Var rule?
- [ ] Can you apply the W-Abs rule?
- [ ] Can you apply the W-App rule?
- [ ] Can you trace through a complete type inference?

### Common Pitfall
Forgetting to apply substitutions from sub-derivations!

### Key Insight
Algorithm W threads substitutions through: each step refines our knowledge about types.

---

## Lesson 4.7: Let-Polymorphism (75-90 minutes)

### Learning Objectives
- Understand let-polymorphism
- See why let is special (vs lambda)
- Recognize polymorphic uses of variables
- Understand the value restriction

### Materials
- README.md: "Let-Polymorphism" section
- TUTORIAL.md: "Part 6: Let-Polymorphism"
- COMMON_MISTAKES.md: "Let vs Lambda" section

### Activities
1. **Read** (25 min): Let-polymorphism and why it matters
2. **Works** (20 min): Verify this type checks:
   ```
   let id = λx. x in (id true, id 0)
   ```
   - `id` gets type `∀α. α → α`
   - First use: `α = Bool`
   - Second use: `α = Nat`
3. **Doesn't Work** (20 min): Verify this FAILS:
   ```
   (λid. (id true, id 0)) (λx. x)
   ```
   - `id` gets monomorphic type
   - Can't unify `Bool` with `Nat`
4. **Understand Why** (15 min): Why the difference?

### Self-Check
- [ ] Can you explain let-polymorphism?
- [ ] Why can't lambda-bound variables be polymorphic?
- [ ] What would happen if we allowed polymorphic lambdas?
- [ ] Can you identify polymorphic vs monomorphic uses?

### Key Insight
Let generalizes, lambda doesn't. This is a deliberate design choice for decidability!

---

## Lesson 4.8: Principal Types (45-60 minutes)

### Learning Objectives
- Understand the principal types theorem
- See that Algorithm W finds the most general type
- Appreciate uniqueness (up to renaming)
- Connect to practical type inference

### Materials
- README.md: "Principal Types" section
- TUTORIAL.md: "Part 7: Principal Types"

### Activities
1. **Read** (20 min): Principal types theorem
2. **Examples** (25 min): See that these are principal:
   - `λx. x` has principal type `α → α`
   - Could also have `Nat → Nat`, but `α → α` is more general
   - `λf. λx. f x` has principal type `(α → β) → α → β`
3. **Understand** (10 min): Why is this useful?

### Self-Check
- [ ] What is a principal type?
- [ ] Why is "most general" important?
- [ ] Does every term have a principal type?
- [ ] How does this relate to type inference?

### Key Insight
Principal types mean there's always a "best" type - no arbitrary choices!

---

## Lesson 4.9: Complete Type Inference Examples (90 minutes)

### Learning Objectives
- Put it all together
- Infer types for complex terms
- Handle let-polymorphism correctly
- Trace complete Algorithm W executions

### Materials
- TUTORIAL.md: "Part 8: Complete Examples"
- Examples from exercises/EXERCISES.md

### Activities
1. **Example 1** (30 min): Infer type of S combinator
   ```
   λx. λy. λz. x z (y z)
   ```
2. **Example 2** (30 min): Infer with let-polymorphism
   ```
   let id = λx. x in
   let a = id true in
   let b = id 0 in (a, b)
   ```
3. **Example 3** (30 min): Infer for compose
   ```
   λf. λg. λx. f (g x)
   ```

### Self-Check
- [ ] Can you infer types without looking at solutions?
- [ ] Do you correctly handle let-polymorphism?
- [ ] Can you explain each step of your derivation?
- [ ] Do your answers match the REPL?

---

## Lesson 4.10: Comparison with STLC (45 minutes)

### Learning Objectives
- Compare Hindley-Milner with STLC
- Understand what we gain
- Understand what we give up
- See the expressiveness/decidability trade-off

### Materials
- README.md: "Limitations" section
- TUTORIAL.md: "Part 9: HM vs STLC vs System F"

### Activities
1. **Read** (20 min): Comparison and limitations
2. **Reflect** (15 min): What can HM do that STLC can't?
   - Polymorphic functions!
   - No annotations!
3. **Reflect** (10 min): What can't HM do?
   - No first-class polymorphism
   - No higher-rank types

### Self-Check
- [ ] How is HM more expressive than STLC?
- [ ] What limitation does let-polymorphism have?
- [ ] Why can't we pass polymorphic functions as arguments?
- [ ] What will Chapter 5 (System F) add?

---

## Lesson 4.11: Implementation Study (90-120 minutes)

### Learning Objectives
- Understand the type inference implementation
- Read and comprehend Infer.hs
- See how substitutions are represented
- Trace through inference examples in code

### Materials
- README.md: "Implementation" section
- Source code: src/Infer.hs, src/Syntax.hs
- REPL_GUIDE.md

### Activities
1. **Read Code** (50 min):
   - `src/Syntax.hs` - Type and TypeScheme definitions
   - `src/Infer.hs` - Algorithm W implementation
   - `src/Infer.hs` - Unification implementation
2. **Trace** (30 min): Follow inference for a simple term
3. **REPL** (20 min):
   - Use `:type` to check types
   - Use `:step` to see inference steps (if available)
   - Try `:examples`

### Self-Check
- [ ] Do you understand the Type datatype?
- [ ] How are substitutions represented?
- [ ] Can you trace through `infer` for a simple term?
- [ ] Have you successfully run the REPL?

### Optional Deep Dive
- Implement better error messages
- Add type annotations (local inference)
- Optimize unification

---

## Lesson 4.12: Theoretical Properties (60 minutes)

### Learning Objectives
- Understand soundness and completeness
- Appreciate decidability
- See the connection to STLC
- Understand termination

### Materials
- README.md: "Properties" section
- TUTORIAL.md: "Part 10: Metatheory"

### Activities
1. **Read** (30 min): Soundness, completeness, decidability
2. **Understand** (20 min): What do these properties guarantee?
3. **Connect** (10 min): How does HM relate to STLC?

### Self-Check
- [ ] What does soundness mean?
- [ ] What does completeness mean?
- [ ] Is type inference decidable?
- [ ] Do well-typed programs terminate?

### Key Insight
HM has it all: expressiveness, decidability, and safety!

---

## Lesson 4.13: Exercises (4-6 hours)

### Learning Objectives
- Solidify understanding through practice
- Implement polymorphic functions
- Demonstrate let-polymorphism
- Extend the type system

### Materials
- exercises/EXERCISES.md (all exercises)
- exercises/Solutions.hs
- test/ExerciseSpec.hs

### Activities
1. **Exercise 1** (60 min): Type inference practice
   - Manually infer types
   - Verify with type checker
2. **Exercise 2** (90 min): Polymorphic list operations
   - Implement map, filter, fold
   - See polymorphism in action
3. **Exercise 3** (60 min): Let-polymorphism vs lambda
   - Demonstrate the difference
   - Understand why
4. **Exercise 4** (90 min): Mutual recursion (advanced)
5. **Exercise 5** (60 min): Polymorphic trees

### Self-Check
- [ ] Have you completed at least Exercises 1-3?
- [ ] Do all tests pass?
- [ ] Do you understand polymorphic types?

---

## Lesson 4.14: Review and Integration (60 minutes)

### Learning Objectives
- Review all major concepts
- Test comprehensive understanding
- Prepare for Chapter 5

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Next Chapter" section

### Activities
1. **Self-Quiz** (30 min): Complete all questions in QUIZ.md
2. **Review** (20 min): Go over anything you missed
3. **Look Ahead** (10 min): Preview Chapter 5 (System F)

### Final Self-Check
Before moving to Chapter 5, you should be able to:
- [ ] Perform type inference by hand using Algorithm W
- [ ] Apply unification to solve type equations
- [ ] Explain let-polymorphism and why it matters
- [ ] Understand principal types
- [ ] Recognize the limitations of HM
- [ ] Score 80%+ on the quiz

---

## Study Tips

### Time Management
- **Minimum**: 1-2 hours per day for 8-10 days
- **Recommended**: 2-4 hour sessions, 3-4 times per week
- **Intensive**: Complete in 4-6 days with 3-4 hour sessions

### Learning Strategies
1. **Build on Chapter 2**: You know typing rules - now automate them!
2. **Practice Unification**: This is the heart of the algorithm
3. **Draw Derivation Trees**: Visual understanding helps
4. **Compare Examples**: let vs lambda, polymorphic vs monomorphic
5. **Use the REPL**: Verify your manual inference

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Try simpler examples first
3. Draw out the unification steps
4. Use the REPL's `:type` command
5. Compare with worked examples in TUTORIAL.md
6. Check that you're applying substitutions correctly

### Signs You're Ready for Chapter 5
- Type inference feels natural
- You understand why let is special
- You see the limitation (no first-class polymorphism)
- You're curious about explicit type abstraction

---

## Progress Tracker

Use this checklist to track your progress:

- [ ] Lesson 4.1: Motivation - Why Type Inference?
- [ ] Lesson 4.2: Type Variables and Monotypes
- [ ] Lesson 4.3: Type Substitutions
- [ ] Lesson 4.4: Unification Algorithm
- [ ] Lesson 4.5: Type Schemes and Polymorphism
- [ ] Lesson 4.6: Algorithm W - The Core
- [ ] Lesson 4.7: Let-Polymorphism
- [ ] Lesson 4.8: Principal Types
- [ ] Lesson 4.9: Complete Type Inference Examples
- [ ] Lesson 4.10: Comparison with STLC
- [ ] Lesson 4.11: Implementation Study
- [ ] Lesson 4.12: Theoretical Properties
- [ ] Lesson 4.13: Exercises
- [ ] Lesson 4.14: Review and Integration

**Completed**: _____ / 14 lessons

---

## What's Next?

Once you've completed this chapter, you're ready for:

**Chapter 5: System F (Polymorphic Lambda Calculus)**
- Explicit type abstraction (Λα. t)
- Explicit type application (t [τ])
- First-class polymorphism
- Higher-rank types
- More power, but no inference!

The journey continues - from inferred types to explicit polymorphism!
