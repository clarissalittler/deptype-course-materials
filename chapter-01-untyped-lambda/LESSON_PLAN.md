# Chapter 1: Untyped Lambda Calculus - Lesson Plan

## Overview

This lesson plan breaks down Chapter 1 into manageable study sessions with clear objectives, time estimates, and self-check points. Follow this plan to build a solid foundation in lambda calculus.

**Total Estimated Time**: 8-12 hours (can be spread over 1-2 weeks)

**Prerequisites**:
- Basic programming experience (any language)
- Familiarity with functions
- Read [CHAPTER_0_PREREQUISITES.md](../CHAPTER_0_PREREQUISITES.md)

---

## Lesson 1.1: Introduction and Motivation (30-45 minutes)

### Learning Objectives
By the end of this lesson, you will be able to:
- Explain what lambda calculus is and why it matters
- Identify lambda calculus concepts in modern programming languages
- Understand the historical significance of lambda calculus

### Materials
- README.md: "Overview" and "Real-World Connections" sections
- CHAPTER_0_PREREQUISITES.md: "What is this course about?" section

### Activities
1. **Read** (15 min): Overview section of README.md
2. **Explore** (10 min): Scan through "Real-World Connections" - find examples in languages you know
3. **Reflect** (5 min): Think about where you've used anonymous functions or closures

### Self-Check ✓
Before moving on, you should be able to answer:
- [ ] What are the three syntactic forms of lambda calculus?
- [ ] Name three modern programming languages influenced by lambda calculus
- [ ] Why is lambda calculus called "untyped"?

### Next Steps
If you're confident with these questions, move to Lesson 1.2. Otherwise, review the Overview section.

---

## Lesson 1.2: Syntax and Basic Terms (45-60 minutes)

### Learning Objectives
- Write lambda terms using proper syntax
- Identify variables, abstractions, and applications
- Understand parentheses and precedence rules

### Materials
- README.md: "Syntax" section
- CHEAT_SHEET.md: First page
- TUTORIAL.md: "Part 1: Basic Syntax"

### Activities
1. **Read** (20 min): Syntax section and examples
2. **Practice** (20 min): Write these lambda terms yourself:
   - Identity function
   - Constant function
   - Apply function: `λf. λx. f x`
   - Compose function: `λf. λg. λx. f (g x)`
3. **REPL Exercise** (15 min):
   ```bash
   cd chapter-01-untyped-lambda
   stack run
   ```
   - Try typing `:examples` in the REPL
   - Type `\x. x` (the identity function)
   - Try applying it: `(\x. x) y`

### Self-Check ✓
- [ ] Can you write the identity function from memory?
- [ ] Do you understand that `x y z` means `(x y) z`?
- [ ] Do you know that `λx. λy. t` means `λx. (λy. t)`?
- [ ] Can you identify the bound and free variables in `λx. x y`?

### Common Pitfalls
- Forgetting that application associates left: `a b c` = `(a b) c` not `a (b c)`
- Wrong precedence: `λx. x y` ≠ `(λx. x) y`

---

## Lesson 1.3: Free and Bound Variables (45 minutes)

### Learning Objectives
- Distinguish between free and bound variables
- Calculate the free variables of a term
- Understand variable scope in lambda calculus

### Materials
- README.md: "Free and Bound Variables" section
- TUTORIAL.md: "Part 2: Free and Bound Variables"
- CHEAT_SHEET.md: Free Variables (FV) section

### Activities
1. **Read** (15 min): Mathematical definition of free variables
2. **Practice** (20 min): Calculate FV for these terms:
   - `λx. x`
   - `λx. x y`
   - `λx. λy. x y z`
   - `(λx. x) y`
3. **Verify** (10 min): Check your answers using the formal definition

### Self-Check ✓
- [ ] Can you compute FV(t) for any term t?
- [ ] Do you understand why `y` is free in `λx. x y` but `x` is not?
- [ ] Can you explain what "scope" means in lambda calculus?

### Practice Problems
From QUIZ.md: Questions 1-3

---

## Lesson 1.4: Substitution and α-Conversion (60-90 minutes)

### Learning Objectives
- Perform capture-avoiding substitution
- Apply α-conversion to rename bound variables
- Understand why variable capture is a problem

### Materials
- README.md: "Substitution" section
- TUTORIAL.md: "Part 3: Substitution and Alpha-Conversion"
- COMMON_MISTAKES.md: "Variable Capture" section

### Activities
1. **Read** (20 min): Substitution definition and α-conversion
2. **Watch Out!** (15 min): Read the variable capture section in COMMON_MISTAKES.md
3. **Practice** (30 min): Perform these substitutions:
   - `[x ↦ y]x`
   - `[x ↦ y](λz. x)`
   - `[x ↦ y](λx. x)` (tricky - x is shadowed!)
   - `[y ↦ x](λx. y)` (DANGER - needs α-conversion!)
4. **REPL Exercise** (15 min): Try `:step` command to see substitution in action

### Self-Check ✓
- [ ] Can you explain why `[y ↦ x](λx. y)` requires renaming?
- [ ] Do you know when to apply α-conversion?
- [ ] Can you perform substitution correctly with shadowed variables?

### Key Insight
Variable capture is THE most common mistake beginners make. When in doubt, rename!

### Practice Problems
From QUIZ.md: Questions 4-6

---

## Lesson 1.5: β-Reduction and Evaluation (60 minutes)

### Learning Objectives
- Apply β-reduction to evaluate lambda terms
- Recognize when a term is in normal form
- Perform multi-step reductions

### Materials
- README.md: "Operational Semantics" section
- TUTORIAL.md: "Part 4: Beta-Reduction and Evaluation"
- CHEAT_SHEET.md: "Core Reduction Rule" and "Evaluation Examples"

### Activities
1. **Read** (20 min): β-reduction rule and examples
2. **Practice** (25 min): Evaluate these step-by-step:
   - `(λx. x) y`
   - `(λx. λy. x) a b`
   - `(λf. λx. f x) (λy. y) z`
3. **REPL Exercise** (15 min):
   - Use `:step` to see each reduction
   - Try the examples from the CHEAT_SHEET

### Self-Check ✓
- [ ] Can you apply the β-reduction rule?
- [ ] Do you know when a term is "stuck" (in normal form)?
- [ ] Can you trace through multi-step evaluations?

### Practice Problems
From QUIZ.md: Questions 7-9

---

## Lesson 1.6: Evaluation Strategies (60-75 minutes)

### Learning Objectives
- Understand the three evaluation strategies (normal-order, call-by-name, call-by-value)
- Explain when different strategies matter
- Recognize which strategy modern languages use

### Materials
- README.md: "Evaluation Strategies" section
- TUTORIAL.md: "Part 5: Evaluation Strategies"
- CHEAT_SHEET.md: "Evaluation Strategies" table

### Activities
1. **Read** (25 min): All three strategies and their differences
2. **Compare** (20 min): Evaluate `(λx. λy. y) ((λz. z z) (λz. z z)) v` using:
   - Normal-order (terminates!)
   - Call-by-value (loops forever!)
3. **REPL Exercise** (15 min):
   - Try different evaluation modes in the REPL
   - See how the strategies differ
4. **Real-World** (10 min): Read about how JavaScript (CBV) and Haskell (lazy) differ

### Self-Check ✓
- [ ] Can you explain the difference between normal-order and call-by-value?
- [ ] Do you understand why normal-order is "complete"?
- [ ] Which strategy does your favorite programming language use?

### Key Insight
Evaluation strategy matters! Some terms terminate under normal-order but loop under call-by-value.

### Practice Problems
From QUIZ.md: Questions 10-11

---

## Lesson 1.7: Church Encodings - Booleans (45-60 minutes)

### Learning Objectives
- Understand Church encoding of booleans
- Implement boolean operations using only lambda terms
- See how data can be represented as functions

### Materials
- README.md: "Church Encodings - Booleans" section
- TUTORIAL.md: "Part 6: Church Encodings - Booleans"
- exercises/EXERCISES.md: Exercise 1

### Activities
1. **Read** (15 min): Church boolean encodings
2. **Understand** (20 min): Work through how `if` works using the encoding
3. **Practice** (15 min): Try exercises 1a-1c (AND, OR, XOR)
4. **REPL Exercise** (10 min): Test your boolean operations

### Self-Check ✓
- [ ] Can you explain why `true = λt. λf. t` "selects" the first argument?
- [ ] Can you write `and` from scratch?
- [ ] Do you see the pattern: data = behavior?

### Practice Problems
From exercises/EXERCISES.md: Exercise 1
From QUIZ.md: Questions 12-13

---

## Lesson 1.8: Church Encodings - Numbers (60-90 minutes)

### Learning Objectives
- Understand Church numerals
- Implement arithmetic operations
- Appreciate the power of function encoding

### Materials
- README.md: "Church Encodings - Natural Numbers" section
- TUTORIAL.md: "Part 7: Church Numerals"
- exercises/EXERCISES.md: Exercise 2

### Activities
1. **Read** (20 min): Church numeral encoding
2. **Understand** (25 min):
   - Why `2 = λf. λx. f (f x)`?
   - How does `succ` work?
   - Trace through `plus 1 2`
3. **Practice** (30 min): Exercises 2a-2c
   - Implement predecessor (this is hard!)
   - Implement subtraction
   - Implement equality test
4. **REPL Exercise** (15 min): Test your implementations

### Self-Check ✓
- [ ] Can you write Church numerals 0, 1, 2, 3 from memory?
- [ ] Can you explain how `plus` works?
- [ ] Why is `pred` so much harder than `succ`?

### Key Insight
Church numerals represent numbers by behavior (how many times to apply a function), not by structure.

### Practice Problems
From exercises/EXERCISES.md: Exercise 2
From QUIZ.md: Questions 14-16

---

## Lesson 1.9: Church Encodings - Pairs and Lists (60 minutes)

### Learning Objectives
- Encode pairs and lists as lambda terms
- Implement list operations
- Understand the universality of lambda calculus

### Materials
- README.md: "Church Encodings - Pairs" section
- TUTORIAL.md: "Part 8: Pairs and Lists"
- exercises/EXERCISES.md: Exercise 5

### Activities
1. **Read** (15 min): Pair and list encodings
2. **Practice** (30 min): Exercise 5
   - Implement `length`
   - Implement `map`
   - Implement `filter`
   - Implement `fold`
3. **REPL Exercise** (15 min): Build and manipulate lists

### Self-Check ✓
- [ ] Can you explain how `pair x y` "packages" two values?
- [ ] How does `fst` "extract" the first element?
- [ ] Can you see the similarity between `fold` and the list encoding itself?

### Practice Problems
From exercises/EXERCISES.md: Exercise 5
From QUIZ.md: Questions 17-18

---

## Lesson 1.10: Fixed-Point Combinator and Recursion (75-90 minutes)

### Learning Objectives
- Understand the Y combinator
- Implement recursive functions without named recursion
- Distinguish between Y and Z combinators

### Materials
- README.md: "Fixed-Point Combinator" section
- TUTORIAL.md: "Part 9: The Y Combinator and Recursion"
- exercises/EXERCISES.md: Exercise 3

### Activities
1. **Read** (25 min): Y combinator definition and properties
2. **Mind-Bending** (20 min): Work through how `Y f = f (Y f)`
3. **Practice** (30 min): Exercise 3
   - Implement Y combinator
   - Implement factorial using Y
   - Implement fibonacci
4. **Important** (10 min): Learn about Z combinator for call-by-value

### Self-Check ✓
- [ ] Can you explain (intuitively) how Y enables recursion?
- [ ] Do you understand why Y doesn't work with call-by-value?
- [ ] Can you write a recursive function using Y?

### Key Insight
The Y combinator seems magical, but it's just self-application cleverly arranged!

### Practice Problems
From exercises/EXERCISES.md: Exercise 3
From QUIZ.md: Questions 19-20

---

## Lesson 1.11: Implementation Study (60-90 minutes)

### Learning Objectives
- Understand how to implement a lambda calculus interpreter
- Read and understand the Haskell implementation
- See theory put into practice

### Materials
- README.md: "Implementation" section
- Source code: src/Syntax.hs, src/Eval.hs, src/Parser.hs
- REPL_GUIDE.md

### Activities
1. **Read Code** (30 min):
   - Open `src/Syntax.hs` - how are terms represented?
   - Open `src/Eval.hs` - how is evaluation implemented?
   - Look at `src/Parser.hs` - how are terms parsed?
2. **Experiment** (30 min):
   - Load the REPL: `stack run`
   - Try `:help` to see all commands
   - Try all the `:examples`
   - Use `:type` to explore terms (even though we're untyped!)
3. **Build** (15 min):
   - Run `stack test` to see all tests pass
   - Look at `test/Spec.hs` to see what's tested

### Self-Check ✓
- [ ] Do you understand the Term datatype?
- [ ] Can you trace through one step of evaluation in the code?
- [ ] Have you successfully run the REPL?

### Optional Deep Dive
Try implementing a small extension:
- Add η-reduction
- Add tracing/debugging output
- Implement DeBruijn indices

---

## Lesson 1.12: Theoretical Foundations (45-60 minutes)

### Learning Objectives
- Understand confluence (Church-Rosser theorem)
- Appreciate the theoretical properties of lambda calculus
- See the connection to computation theory

### Materials
- README.md: "Theoretical Properties" section
- TUTORIAL.md: "Part 10: Theoretical Properties"

### Activities
1. **Read** (30 min): Church-Rosser theorem and standardization
2. **Reflect** (15 min): Why do these properties matter?
3. **Connect** (10 min): Review "Key Concepts" section in README

### Self-Check ✓
- [ ] Can you explain what "confluence" means?
- [ ] Why is the uniqueness of normal forms important?
- [ ] What does it mean that lambda calculus is Turing-complete?

### Practice Problems
From QUIZ.md: Questions 21-23

---

## Lesson 1.13: Exercises and Practice (2-4 hours)

### Learning Objectives
- Solidify understanding through practice
- Implement complete solutions to all exercises
- Verify solutions with automated tests

### Materials
- exercises/EXERCISES.md (all exercises)
- exercises/Solutions.hs (for hints, but try on your own first!)
- test/ExerciseSpec.hs (automated tests)

### Activities
1. **Complete All Exercises** (2-3 hours):
   - Exercise 1: Boolean operations
   - Exercise 2: Arithmetic operations
   - Exercise 3: Recursion and Y combinator
   - Exercise 4: Advanced combinators
   - Exercise 5: List operations
2. **Test Your Work** (30 min):
   ```bash
   stack test --test-arguments "--match Exercises"
   ```
3. **Review Solutions** (30 min): Compare your solutions with provided ones

### Self-Check ✓
- [ ] Have you completed all exercises?
- [ ] Do all tests pass?
- [ ] Do you understand the solutions (even if you had to look at them)?

### Don't Give Up!
Some exercises (like `pred` and Y combinator) are genuinely difficult. It's okay to peek at hints!

---

## Lesson 1.14: Review and Integration (60 minutes)

### Learning Objectives
- Review all major concepts
- Identify gaps in understanding
- Prepare for Chapter 2

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Next Chapter" section

### Activities
1. **Self-Quiz** (30 min): Complete all questions in QUIZ.md
2. **Review Mistakes** (15 min): Go over anything you got wrong
3. **Cheat Sheet** (10 min): Make sure you understand everything on the cheat sheet
4. **Look Ahead** (5 min): Skim Chapter 2 README to see what's coming

### Final Self-Check ✓
Before moving to Chapter 2, you should be able to:
- [ ] Write lambda terms fluently
- [ ] Perform β-reduction correctly (with proper substitution)
- [ ] Implement data structures using Church encoding
- [ ] Explain evaluation strategies
- [ ] Use the Y combinator for recursion
- [ ] Read and understand the implementation code
- [ ] Score 80%+ on the quiz

### If You're Not There Yet
That's okay! Review specific lessons where you struggled. Focus on:
1. Substitution and variable capture (most common issue)
2. Church encodings (most practical skill)
3. Evaluation strategies (most conceptually important)

---

## Additional Resources

### If You Want More Practice
- Implement the "Additional Challenges" from EXERCISES.md
- Try writing classic algorithms (sorting, searching) in pure lambda calculus
- Read Chapters 5-7 of Pierce's TAPL

### If You Want Deeper Theory
- Read Barendregt's "The Lambda Calculus" (advanced)
- Study the Curry-Howard correspondence
- Explore connections to category theory

### If You Want More Implementation
- Implement DeBruijn indices
- Add α-conversion as an explicit step
- Build a web-based visualizer
- Optimize the evaluator with sharing/memoization

---

## Study Tips

### Time Management
- **Minimum**: 1 hour per day for 8-10 days
- **Recommended**: 2-3 hour sessions, 3-4 times per week
- **Intensive**: Complete in 3-4 days with 3-4 hour sessions

### Learning Strategies
1. **Don't Skip the Basics**: Lessons 1.2-1.5 are foundational
2. **Practice, Practice, Practice**: Do all exercises
3. **Use the REPL**: Experiment constantly
4. **Draw Pictures**: Visualize reduction steps
5. **Teach Someone**: Explaining helps you understand
6. **Take Breaks**: Let concepts sink in

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Try simpler examples
3. Use the REPL's `:step` command
4. Look at Solutions.hs (with hints first)
5. Review relevant tutorial sections
6. Ask for help (community forums, study groups)

### Signs You're Ready for Chapter 2
- You can write and evaluate lambda terms without hesitation
- Church encodings make sense (even if they're not intuitive)
- You understand why we need types (from experiencing untyped issues)
- You're curious about how to prevent infinite loops

---

## Progress Tracker

Use this checklist to track your progress:

- [ ] Lesson 1.1: Introduction and Motivation
- [ ] Lesson 1.2: Syntax and Basic Terms
- [ ] Lesson 1.3: Free and Bound Variables
- [ ] Lesson 1.4: Substitution and α-Conversion
- [ ] Lesson 1.5: β-Reduction and Evaluation
- [ ] Lesson 1.6: Evaluation Strategies
- [ ] Lesson 1.7: Church Encodings - Booleans
- [ ] Lesson 1.8: Church Encodings - Numbers
- [ ] Lesson 1.9: Church Encodings - Pairs and Lists
- [ ] Lesson 1.10: Fixed-Point Combinator
- [ ] Lesson 1.11: Implementation Study
- [ ] Lesson 1.12: Theoretical Foundations
- [ ] Lesson 1.13: Exercises and Practice
- [ ] Lesson 1.14: Review and Integration

**Completed**: _____ / 14 lessons

---

## What's Next?

Once you've completed this chapter, you're ready for:

**Chapter 2: Simply Typed Lambda Calculus**
- Learn how types prevent infinite loops
- See how type checking works
- Understand type safety (Progress and Preservation)
- Experience the trade-off: safety vs. expressiveness

The journey continues! 🚀
