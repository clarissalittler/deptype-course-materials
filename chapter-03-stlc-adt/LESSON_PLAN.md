# Chapter 3: STLC with Algebraic Data Types - Lesson Plan

## Overview

This lesson plan guides you through extending the Simply Typed Lambda Calculus with algebraic data types (ADTs). You'll learn how to build complex, type-safe data structures using products, sums, and pattern matching - fundamental features found in modern functional languages.

**Total Estimated Time**: 12-16 hours (can be spread over 1-2 weeks)

**Prerequisites**:
- Completed Chapter 2 (Simply Typed Lambda Calculus)
- Comfortable with type checking and type derivations
- Understanding of Progress and Preservation theorems

**Key Difference from Chapter 2**: In Chapter 2, we could only represent functions, booleans, and natural numbers. In Chapter 3, we can build rich data structures like pairs, tuples, tagged unions, records, and lists - all type-safe!

---

## Lesson 3.1: Motivation - Why Algebraic Data Types? (30-45 minutes)

### Learning Objectives
- Understand the limitations of STLC without ADTs
- See how ADTs solve real-world problems
- Recognize ADTs in modern programming languages

### Materials
- README.md: "Overview" and "Real-World Connections" sections
- Compare with Chapter 2's limitations

### Activities
1. **Recall Limitations** (10 min): From Chapter 2:
   - Can't return multiple values
   - Can't represent "optional" values
   - Can't model state machines or tagged data
2. **Read** (15 min): Overview section about ADTs
3. **Explore** (10 min): Real-world connections - find ADTs in languages you know

### Self-Check ✓
- [ ] Can you name three problems that ADTs solve?
- [ ] What are the two fundamental operations: products and sums?
- [ ] Can you recognize Option/Maybe types in modern languages?

### Next Steps
If confident, move to Lesson 3.2. Otherwise, review the Overview section.

---

## Lesson 3.2: Product Types - Pairs and Tuples (60-75 minutes)

### Learning Objectives
- Understand product types (τ₁ × τ₂)
- Create and use pairs with fst/snd
- Build complete typing derivations for products

### Materials
- README.md: "Product Types" section
- CHEAT_SHEET.md: Product types reference
- TUTORIAL.md: "Part 1: Product Types"

### Activities
1. **Read** (20 min): Product type syntax and typing rules
2. **Practice** (30 min): Type check these terms:
   - `(true, 0)`
   - `fst (false, succ 0)`
   - `λp:Bool×Nat. snd p`
   - `λx:Nat. λy:Bool. (x, y)`
3. **REPL Exercise** (15 min):
   ```bash
   cd chapter-03-stlc-adt
   stack run
   ```
   - Try creating pairs: `(true, 0)`
   - Project elements: `fst (1, 2)`
   - Build functions returning pairs

### Self-Check ✓
- [ ] Can you write the type `τ₁ × τ₂`?
- [ ] Do you understand the T-Pair, T-Fst, T-Snd rules?
- [ ] Can you derive the type of `fst (v₁, v₂)`?

### Key Insight
Product types let you combine multiple values into one - like tuples or structs in other languages!

---

## Lesson 3.3: Sum Types - Tagged Unions (75-90 minutes)

### Learning Objectives
- Understand sum types (τ₁ + τ₂)
- Use inl/inr to construct sum values
- Use case expressions to eliminate sums
- Build complete typing derivations for sums

### Materials
- README.md: "Sum Types" section
- TUTORIAL.md: "Part 2: Sum Types and Case Analysis"
- CHEAT_SHEET.md: Sum types reference

### Activities
1. **Read** (25 min): Sum type syntax, typing rules, and case analysis
2. **Understand** (20 min): Work through how case analysis type checks:
   - Both branches must return the same type
   - Variables in branches get appropriate types
3. **Practice** (30 min): Type check these:
   - `inl[Nat] true : Bool + Nat`
   - `case (inl[Nat] true) of inl x => x | inr y => false`
   - `λx:Bool+Nat. case x of inl b => b | inr n => iszero n`
4. **REPL Exercise** (15 min): Create and pattern match on sums

### Self-Check ✓
- [ ] Why do we need type annotations on inl/inr?
- [ ] Can you explain the T-Case rule?
- [ ] Do you understand why both branches must have the same type?

### Key Insight
Sum types let you choose between alternatives - the foundation of Option, Either, and enums!

---

## Lesson 3.4: The Option Type Pattern (45-60 minutes)

### Learning Objectives
- Encode Option types using Unit + τ
- Implement none and some constructors
- Use pattern matching on options
- Understand null safety

### Materials
- README.md: "Option Type" example
- TUTORIAL.md: "Part 3: The Option Type Pattern"
- COMMON_MISTAKES.md: "Encoding Option" section

### Activities
1. **Read** (15 min): Option type encoding as `Unit + τ`
2. **Implement** (25 min):
   - Define none and some
   - Implement getOrDefault
   - Implement map for Option
3. **Connect** (10 min): How does this compare to null in other languages?
4. **REPL Exercise** (10 min): Test your Option implementations

### Self-Check ✓
- [ ] Can you implement `none : Option τ`?
- [ ] Can you implement `some : τ → Option τ`?
- [ ] Do you understand why Option is safer than null?

### Real-World Connection
This is exactly how Rust's `Option<T>`, Haskell's `Maybe a`, and Swift's `Optional<T>` work!

---

## Lesson 3.5: Records - Named Products (60 minutes)

### Learning Objectives
- Define record types with named fields
- Create and access record values
- Understand record typing rules
- Compare with objects/structs

### Materials
- README.md: "Record Types" section
- TUTORIAL.md: "Part 4: Records"
- CHEAT_SHEET.md: Record operations

### Activities
1. **Read** (20 min): Record syntax and typing rules
2. **Practice** (25 min): Type check:
   - `{x=0, y=1} : {x:Nat, y:Nat}`
   - `{x=0, y=1}.x`
   - `λp:{x:Nat, y:Nat}. p.x`
   - Define a Point type and operations
3. **REPL Exercise** (15 min): Build and manipulate records

### Self-Check ✓
- [ ] Can you define a record type?
- [ ] Can you access fields with projection?
- [ ] Do you see how records are "named products"?

### Key Insight
Records are products with named fields - much more readable than `fst` and `snd`!

---

## Lesson 3.6: Variants - Named Sums (60-75 minutes)

### Learning Objectives
- Define variant types with named alternatives
- Create variant values with tags
- Pattern match on variants
- Build state machines with variants

### Materials
- README.md: "Variant Types" section
- TUTORIAL.md: "Part 5: Variants and State Machines"
- exercises/EXERCISES.md: Variant examples

### Activities
1. **Read** (20 min): Variant syntax and typing rules
2. **Practice** (30 min):
   - Define a Shape variant
   - Implement constructors (makeCircle, makeSquare)
   - Implement operations using case analysis
3. **State Machine** (15 min): Model a simple state machine with variants
4. **REPL Exercise** (10 min): Test variant operations

### Self-Check ✓
- [ ] Can you define a variant type?
- [ ] Can you pattern match on all constructors?
- [ ] Do you see how variants are "named sums"?

### Real-World Connection
Variants are enums in Rust, discriminated unions in TypeScript, and data types in Haskell!

---

## Lesson 3.7: Lists and Recursive Types (75-90 minutes)

### Learning Objectives
- Understand the List type
- Create lists with [] and ::
- Pattern match on lists
- Implement list operations

### Materials
- README.md: "List Types" section
- TUTORIAL.md: "Part 6: Lists and Recursive Data"
- exercises/EXERCISES.md: Exercise 1

### Activities
1. **Read** (25 min): List syntax, typing rules, and pattern matching
2. **Understand** (20 min): How lists are recursive:
   - Empty list []
   - Cons x::xs (element prepended to list)
3. **Practice** (30 min): Exercises 1a-1c:
   - Implement append
   - Implement reverse
   - Implement length
4. **REPL Exercise** (15 min): Build and manipulate lists

### Self-Check ✓
- [ ] Can you create a list of naturals?
- [ ] Can you pattern match with [] and ::?
- [ ] Do you understand list recursion?

### Key Insight
Lists are our first truly recursive data structure - they're defined in terms of themselves!

---

## Lesson 3.8: Pattern Matching Fundamentals (60-75 minutes)

### Learning Objectives
- Understand pattern syntax
- Match on multiple constructors
- Use nested patterns
- Understand exhaustiveness checking

### Materials
- README.md: "Pattern Matching Semantics" section
- TUTORIAL.md: "Part 7: Advanced Pattern Matching"
- COMMON_MISTAKES.md: "Pattern Matching Mistakes"

### Activities
1. **Read** (25 min): Pattern matching rules and semantics
2. **Practice** (30 min): Write patterns for:
   - Matching pairs: `(x, y)`
   - Matching nested pairs: `((x, y), z)`
   - Matching lists: `[]`, `x::xs`, `x::y::rest`
   - Matching variants with nested data
3. **Understand** (15 min): What is exhaustiveness checking?

### Self-Check ✓
- [ ] Can you write nested patterns?
- [ ] Do you know when a match is exhaustive?
- [ ] Can you identify incomplete patterns?

### Common Pitfall
Forgetting to handle all cases leads to non-exhaustive patterns!

---

## Lesson 3.9: Type Safety with ADTs (60 minutes)

### Learning Objectives
- Extend Progress theorem to ADTs
- Extend Preservation theorem to ADTs
- Understand why ADTs maintain type safety
- See that strong normalization still holds

### Materials
- README.md: "Metatheory" section
- TUTORIAL.md: "Part 8: Type Safety Proofs"

### Activities
1. **Read** (30 min): Progress and Preservation with ADTs
2. **Understand** (20 min): Proof sketches:
   - How do products preserve types?
   - How do sums preserve types?
   - Why does pattern matching maintain safety?
3. **Connect** (10 min): How does this relate to Chapter 2?

### Self-Check ✓
- [ ] Does Progress still hold? Why?
- [ ] Does Preservation still hold? Why?
- [ ] Does strong normalization still hold?

### Key Insight
ADTs increase expressiveness WITHOUT sacrificing type safety or termination!

---

## Lesson 3.10: Real-World ADT Patterns (60-75 minutes)

### Learning Objectives
- Recognize common ADT patterns
- Implement Option, Either, Result patterns
- Build binary trees
- Express expression languages

### Materials
- README.md: Examples section
- TUTORIAL.md: "Part 9: Common Patterns"
- exercises/EXERCISES.md: Exercises 2-4

### Activities
1. **Option Pattern** (15 min): Implement map, bind, getOrElse
2. **Either Pattern** (15 min): Implement error handling
3. **Tree Pattern** (20 min): Exercise 2 - Binary trees
4. **Expression Pattern** (15 min): Exercise 4 - Simple interpreter

### Self-Check ✓
- [ ] Can you implement Option operations?
- [ ] Can you use Either for error handling?
- [ ] Can you define recursive tree types?

### Real-World Connection
These patterns appear everywhere in production code!

---

## Lesson 3.11: Implementation Study (60-90 minutes)

### Learning Objectives
- Understand the type checker for ADTs
- See how pattern matching is implemented
- Read and understand the Haskell code

### Materials
- Source code: src/TypeCheck.hs, src/Syntax.hs, src/Eval.hs
- README.md: "Implementation" section

### Activities
1. **Read Code** (40 min):
   - `src/Syntax.hs` - How are ADTs represented?
   - `src/TypeCheck.hs` - How is pattern type checking done?
   - `src/Eval.hs` - How is pattern matching evaluated?
2. **Trace** (20 min): Follow type checking for a case expression
3. **REPL** (15 min): Use `:type` and `:step` to explore
4. **Build** (15 min): Run `stack test` to see tests pass

### Self-Check ✓
- [ ] Do you understand the Type datatype?
- [ ] How are patterns represented?
- [ ] Can you trace through pattern matching?

---

## Lesson 3.12: Exercises and Practice (3-5 hours)

### Learning Objectives
- Solidify understanding through practice
- Implement complete solutions to all exercises
- Build real data structures

### Materials
- exercises/EXERCISES.md (all exercises)
- exercises/Solutions.hs (for hints)
- test/ExerciseSpec.hs (automated tests)

### Activities
1. **Exercise 1** (45 min): List operations (append, reverse, length)
2. **Exercise 2** (90 min): Binary trees (height, mirror, map, fold)
3. **Exercise 3** (60 min): Option type operations
4. **Exercise 4** (90 min): Expression evaluator
5. **Exercise 5** (45 min): Record operations
6. **Test Your Work** (30 min):
   ```bash
   stack test --test-arguments "--match 'Chapter 3'"
   ```

### Self-Check ✓
- [ ] Have you completed at least Exercises 1-3?
- [ ] Do all tests pass?
- [ ] Do you understand the solutions?

---

## Lesson 3.13: Review and Integration (60 minutes)

### Learning Objectives
- Review all major concepts
- Test comprehensive understanding
- Prepare for Chapter 4

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Next Chapter" section

### Activities
1. **Self-Quiz** (30 min): Complete all questions in QUIZ.md
2. **Review** (20 min): Go over anything you missed
3. **Look Ahead** (10 min): Preview Chapter 4 (Hindley-Milner)

### Final Self-Check ✓
Before moving to Chapter 4, you should be able to:
- [ ] Define and use product types
- [ ] Define and use sum types
- [ ] Implement Option and Either patterns
- [ ] Use records and variants
- [ ] Pattern match exhaustively
- [ ] Understand type safety with ADTs
- [ ] Score 80%+ on the quiz

---

## Study Tips

### Time Management
- **Minimum**: 1.5 hours per day for 8-10 days
- **Recommended**: 2-3 hour sessions, 4-5 times per week
- **Intensive**: Complete in 4-5 days with 3-4 hour sessions

### Learning Strategies
1. **Build on Chapter 2**: ADTs extend what you know
2. **Practice Pattern Matching**: This is the most practical skill
3. **Draw Type Derivations**: Visualize the typing rules
4. **Use the REPL**: Experiment constantly
5. **Connect to Real Languages**: See ADTs in Rust, TypeScript, etc.
6. **Focus on Patterns**: Option, Either, trees are everywhere

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Draw out the typing derivation on paper
3. Use the REPL's `:type` and `:step` commands
4. Try simpler examples first
5. Review relevant TUTORIAL.md sections
6. Compare with working examples from README

---

## Progress Tracker

Use this checklist to track your progress:

- [ ] Lesson 3.1: Motivation - Why ADTs?
- [ ] Lesson 3.2: Product Types
- [ ] Lesson 3.3: Sum Types
- [ ] Lesson 3.4: The Option Type Pattern
- [ ] Lesson 3.5: Records
- [ ] Lesson 3.6: Variants
- [ ] Lesson 3.7: Lists and Recursive Types
- [ ] Lesson 3.8: Pattern Matching Fundamentals
- [ ] Lesson 3.9: Type Safety with ADTs
- [ ] Lesson 3.10: Real-World ADT Patterns
- [ ] Lesson 3.11: Implementation Study
- [ ] Lesson 3.12: Exercises and Practice
- [ ] Lesson 3.13: Review and Integration

**Completed**: _____ / 13 lessons

---

## What's Next?

Once you've completed this chapter, you're ready for:

**Chapter 4: Hindley-Milner Type Inference**
- Write code without type annotations!
- Understand unification and type inference
- See how languages like OCaml and Haskell infer types
- Learn about let-polymorphism

The journey continues - from explicit types to inferred types!
