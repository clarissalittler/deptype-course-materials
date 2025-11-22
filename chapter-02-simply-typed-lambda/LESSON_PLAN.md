# Chapter 2: Simply Typed Lambda Calculus - Lesson Plan

## Overview

This lesson plan guides you through adding types to lambda calculus. You'll learn how types prevent runtime errors and guarantee termination - fundamental properties that make programming languages safe and predictable.

**Total Estimated Time**: 10-14 hours (can be spread over 1-2 weeks)

**Prerequisites**:
- Completed Chapter 1 (Untyped Lambda Calculus)
- Comfortable with substitution and β-reduction
- Understanding of Church encodings (helpful but not required)

**Key Difference from Chapter 1**: In Chapter 1, anything goes! In Chapter 2, the type system rejects programs before they run.

---

## Lesson 2.1: Motivation - Why Types? (30-45 minutes)

### Learning Objectives
- Understand the problems with untyped lambda calculus
- See how types prevent runtime errors
- Appreciate the trade-off between safety and expressiveness

### Materials
- README.md: "Overview" section
- Compare with Chapter 1's limitations

### Activities
1. **Recall Problems** (10 min): Remember from Chapter 1:
   - `(λx. x x) (λx. x x)` loops forever
   - Church encodings are fragile (no safety)
   - No way to prevent applying wrong types of values
2. **Read** (15 min): Overview section about type safety
3. **Explore** (10 min): Try typing `true + false` - should this make sense?

### Self-Check ✓
- [ ] Can you name three problems that types solve?
- [ ] What do we give up when we add types?
- [ ] Do you understand the phrase "well-typed programs don't go wrong"?

---

## Lesson 2.2: Type Syntax and Expressions (45-60 minutes)

### Learning Objectives
- Write type expressions
- Understand function types
- Annotate lambda abstractions with types

### Materials
- README.md: "Syntax" section
- CHEAT_SHEET.md: Types and terms
- TUTORIAL.md: "Part 1: Type Syntax"

### Activities
1. **Read** (20 min): Type syntax - Bool, Nat, and function types
2. **Practice** (20 min): Write types for:
   - A function from Bool to Bool
   - A function from Nat to Nat
   - A function from Bool to (Nat → Nat)
   - The identity function on Booleans
3. **REPL Exercise** (15 min):
   ```bash
   cd chapter-02-simply-typed-lambda
   stack run
   ```
   Try typing: `\x:Bool. x`

### Self-Check ✓
- [ ] Can you write `τ₁ → τ₂ → τ₃` correctly?
- [ ] Do you understand that `→` associates to the right?
- [ ] Can you annotate lambda terms with types?

### Key Insight
Function types `τ₁ → τ₂` are read as "functions from τ₁ to τ₂"

---

## Lesson 2.3: Typing Rules - Variables and Abstraction (60 minutes)

### Learning Objectives
- Understand typing contexts (Γ)
- Apply the T-Var rule
- Apply the T-Abs rule
- Build typing derivations

### Materials
- README.md: "Typing Rules" section
- TUTORIAL.md: "Part 2: Typing Contexts and Variables"
- CHEAT_SHEET.md: Typing rules

### Activities
1. **Read** (25 min): Typing contexts and rules for variables and abstraction
2. **Practice** (25 min): Derive types for:
   - `x` under context `x:Bool`
   - `λx:Bool. x` under empty context
   - `λx:Nat. λy:Bool. x` under empty context
3. **Understand** (10 min): Why do we need contexts?

### Self-Check ✓
- [ ] Can you explain what Γ represents?
- [ ] Can you apply T-Var to look up variables?
- [ ] Can you build a typing derivation for a simple abstraction?

### Common Pitfall
The context in T-Abs is extended: `Γ, x:τ₁ ⊢ t : τ₂`

---

## Lesson 2.4: Application and Type Checking (60-75 minutes)

### Learning Objectives
- Apply the T-App rule
- Check that function types match arguments
- Understand type checking failures

### Materials
- README.md: "Type Checking Algorithm" section
- TUTORIAL.md: "Part 3: Application and Type Checking"
- COMMON_MISTAKES.md: "Type Mismatches" section

### Activities
1. **Read** (20 min): T-App rule and type checking
2. **Practice** (30 min): Type check these:
   - `(λx:Bool. x) true`
   - `(λx:Bool. λy:Nat. y) false 0`
   - `(λf:Nat→Bool. λx:Nat. f x) iszero 5`
3. **Failures** (15 min): Why do these fail?
   - `(λx:Bool. x) 0`
   - `(λx:Nat. x) true`
   - `(λx:Bool. x x) false`

### Self-Check ✓
- [ ] Can you check if function and argument types match?
- [ ] Can you identify type errors before evaluating?
- [ ] Do you understand why `λx:Bool. x x` doesn't type check?

### Key Insight
Type checking happens BEFORE evaluation - catching errors early!

---

## Lesson 2.5: Booleans and Conditionals (45-60 minutes)

### Learning Objectives
- Type boolean expressions
- Understand conditional typing
- Ensure branch types match

### Materials
- README.md: Boolean typing rules
- TUTORIAL.md: "Part 4: Booleans and Conditionals"

### Activities
1. **Read** (15 min): Typing rules for true, false, and if-then-else
2. **Practice** (25 min): Type check:
   - `if true then false else true`
   - `if iszero 0 then 1 else 2`
   - `if true then (λx:Bool. x) else (λy:Bool. y)`
3. **Failures** (10 min): Why does this fail?
   - `if true then 0 else false`

### Self-Check ✓
- [ ] Why must both branches have the same type?
- [ ] Can you type check conditionals?
- [ ] What type does `if iszero n then 0 else succ n` have?

---

## Lesson 2.6: Natural Numbers (45 minutes)

### Learning Objectives
- Type natural number expressions
- Understand successor and predecessor
- Use iszero correctly

### Materials
- README.md: Natural number typing rules
- TUTORIAL.md: "Part 5: Natural Numbers"

### Activities
1. **Read** (15 min): Typing rules for 0, succ, pred, iszero
2. **Practice** (20 min): Type check:
   - `succ (succ 0)`
   - `pred (succ 0)`
   - `iszero (pred (succ 0))`
   - `if iszero n then 0 else pred n`

### Self-Check ✓
- [ ] What type does `succ` have (as a term)?
- [ ] What type does `iszero` return?
- [ ] Can you chain operations correctly?

---

## Lesson 2.7: Complete Type Derivations (75-90 minutes)

### Learning Objectives
- Build complete typing derivations
- Combine multiple rules
- Verify complex terms

### Materials
- TUTORIAL.md: "Part 6: Complete Type Derivations"
- Practice problems

### Activities
1. **Learn** (20 min): How to build derivation trees
2. **Practice** (50 min): Build complete derivations for:
   - `λf:Nat→Nat. λx:Nat. f (f x)`
   - `λx:Bool. if x then 0 else 1`
   - `(λx:Nat→Bool. λy:Nat. x y) iszero 5`

### Example Derivation Tree
```
         ─────────── (T-Zero)
         Γ ⊢ 0 : Nat
      ──────────────────── (T-Succ)
      Γ ⊢ succ 0 : Nat
   ─────────────────────────── (T-Succ)
   Γ ⊢ succ (succ 0) : Nat
```

### Self-Check ✓
- [ ] Can you build a complete derivation tree?
- [ ] Can you identify which rule applies at each step?
- [ ] Do you understand bottom-up vs top-down checking?

---

## Lesson 2.8: Evaluation with Types (60 minutes)

### Learning Objectives
- Evaluate well-typed terms
- See that evaluation preserves types
- Understand call-by-value with values

### Materials
- README.md: "Operational Semantics" section
- TUTORIAL.md: "Part 7: Evaluation"
- REPL: Use `:step` command

### Activities
1. **Read** (20 min): Evaluation rules (similar to Chapter 1 but with types)
2. **Practice** (30 min): Evaluate step-by-step:
   - `(λx:Bool. x) true`
   - `(λx:Nat. succ x) 0`
   - `if iszero 0 then 1 else 2`
3. **REPL Exercise** (10 min): Use `:step` to verify

### Self-Check ✓
- [ ] Does evaluation change from Chapter 1?
- [ ] What are "values" in STLC?
- [ ] Can you trace evaluation step by step?

---

## Lesson 2.9: Progress and Preservation (60-75 minutes)

### Learning Objectives
- Understand the Progress theorem
- Understand the Preservation theorem
- See how these guarantee type safety

### Materials
- README.md: "Metatheory" section
- TUTORIAL.md: "Part 8: Type Safety"

### Activities
1. **Read** (30 min): Progress and Preservation theorems
2. **Understand** (25 min): Work through proof sketches
3. **Connect** (10 min): How do these relate to "well-typed programs don't go wrong"?

### Progress
**If** ⊢ t : τ **then either**:
- t is a value, **OR**
- t → t' for some t'

(Well-typed programs never get "stuck")

### Preservation
**If** Γ ⊢ t : τ **and** t → t' **then** Γ ⊢ t' : τ

(Evaluation preserves types)

### Self-Check ✓
- [ ] Can you explain Progress in plain language?
- [ ] Can you explain Preservation in plain language?
- [ ] Why do these two theorems together give type safety?

### Key Insight
Progress + Preservation = Type Safety: "Well-typed programs don't go wrong"

---

## Lesson 2.10: Strong Normalization (45-60 minutes)

### Learning Objectives
- Understand that STLC always terminates
- See the trade-off: safety vs expressiveness
- Recognize non-expressible programs

### Materials
- README.md: "Strong Normalization" section
- TUTORIAL.md: "Part 9: Termination and Expressiveness"

### Activities
1. **Read** (20 min): Strong normalization theorem
2. **Reflect** (20 min): What can't we write in STLC?
   - Infinite loops
   - General recursion (without fix)
   - Self-application (λx. x x)
3. **Compare** (10 min): STLC vs Untyped LC

### Self-Check ✓
- [ ] Why does STLC guarantee termination?
- [ ] What's the trade-off we make?
- [ ] Can you write a non-terminating program in STLC?

### Key Insight
STLC is NOT Turing-complete! We can't write general recursive programs (yet).

---

## Lesson 2.11: Implementation Study (60-90 minutes)

### Learning Objectives
- Understand the type checker implementation
- See how contexts are managed
- Read and understand Haskell code

### Materials
- Source code: src/TypeCheck.hs, src/Syntax.hs
- README.md: "Implementation" section

### Activities
1. **Read Code** (40 min):
   - `src/Syntax.hs` - Type and Term definitions
   - `src/TypeCheck.hs` - Type checking algorithm
2. **Trace** (20 min): Follow type checking for a simple term
3. **REPL** (15 min): Use `:type` command to check terms

### Self-Check ✓
- [ ] Do you understand the Type datatype?
- [ ] How are contexts represented?
- [ ] Can you trace through typeCheck for a simple term?

---

## Lesson 2.12: Exercises (3-5 hours)

### Learning Objectives
- Solidify understanding through practice
- Extend the type system
- Implement new features

### Materials
- exercises/EXERCISES.md
- exercises/Solutions.hs
- test/ExerciseSpec.hs

### Activities
1. **Exercise 1** (45 min): Add arithmetic operations (mult, lt, eq)
2. **Exercise 2** (90 min): Implement product types (pairs)
3. **Exercise 3** (90 min): Implement sum types
4. **Exercise 4** (30 min): Add let-bindings
5. **Exercise 5** (60 min): Add fixed-point combinator

### Self-Check ✓
- [ ] Have you completed at least Exercises 1-2?
- [ ] Do all tests pass?
- [ ] Do you understand the solutions?

---

## Lesson 2.13: Review and Integration (60 minutes)

### Learning Objectives
- Review all major concepts
- Test comprehensive understanding
- Prepare for Chapter 3

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Next Chapter" section

### Activities
1. **Self-Quiz** (30 min): Complete all questions in QUIZ.md
2. **Review** (20 min): Go over anything you missed
3. **Look Ahead** (10 min): Preview Chapter 3 (ADTs)

### Final Self-Check ✓
Before moving to Chapter 3, you should be able to:
- [ ] Write type annotations for lambda terms
- [ ] Build complete typing derivations
- [ ] Type check terms by hand
- [ ] Explain Progress and Preservation
- [ ] Understand the expressiveness trade-off
- [ ] Score 80%+ on the quiz

---

## Study Tips

### Time Management
- **Minimum**: 1-1.5 hours per day for 7-10 days
- **Recommended**: 2-3 hour sessions, 3-4 times per week
- **Intensive**: Complete in 4-5 days with 3-4 hour sessions

### Learning Strategies
1. **Build on Chapter 1**: Types are added to what you know
2. **Draw Derivation Trees**: Visual understanding helps
3. **Use the REPL**: Check your work constantly
4. **Compare with Untyped**: See what changes and what doesn't
5. **Understand the Theorems**: Progress and Preservation are crucial

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Draw out the typing derivation on paper
3. Use the REPL's `:type` command
4. Review TUTORIAL.md relevant section
5. Compare with working examples

---

## Progress Tracker

- [ ] Lesson 2.1: Motivation - Why Types?
- [ ] Lesson 2.2: Type Syntax and Expressions
- [ ] Lesson 2.3: Typing Rules - Variables and Abstraction
- [ ] Lesson 2.4: Application and Type Checking
- [ ] Lesson 2.5: Booleans and Conditionals
- [ ] Lesson 2.6: Natural Numbers
- [ ] Lesson 2.7: Complete Type Derivations
- [ ] Lesson 2.8: Evaluation with Types
- [ ] Lesson 2.9: Progress and Preservation
- [ ] Lesson 2.10: Strong Normalization
- [ ] Lesson 2.11: Implementation Study
- [ ] Lesson 2.12: Exercises
- [ ] Lesson 2.13: Review and Integration

**Completed**: _____ / 13 lessons

---

## What's Next?

**Chapter 3: STLC with Algebraic Data Types**
- Add sum and product types
- Pattern matching
- Build real data structures
- More expressive, still safe!
