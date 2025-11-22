# Chapter 5: System F (Polymorphic Lambda Calculus) - Lesson Plan

## Overview

This lesson plan guides you through System F, where polymorphism becomes **explicit** and **first-class**. Unlike Hindley-Milner's implicit polymorphism, System F requires you to explicitly abstract over types and apply them - making the type structure fully visible.

**Total Estimated Time**: 12-16 hours (can be spread over 2-3 weeks)

**Prerequisites**:
- Completed Chapter 2 (Simply Typed Lambda Calculus)
- Completed Chapter 4 (Hindley-Milner Type Inference) - strongly recommended
- Comfortable with typing derivations
- Understanding of polymorphism concept

**Key Difference from Previous Chapters**:
- **Chapter 2**: No polymorphism at all
- **Chapter 4**: Implicit polymorphism (let-bound only)
- **Chapter 5**: Explicit polymorphism everywhere (but undecidable inference!)

---

## Lesson 5.1: Motivation - Why Explicit Polymorphism? (45-60 minutes)

### Learning Objectives
- Understand the limitations of Hindley-Milner
- See why first-class polymorphism requires explicit types
- Appreciate the expressiveness vs inference trade-off

### Materials
- README.md: "Overview" and "Comparison with Previous Chapters" sections
- Chapter 4 README.md: Review let-polymorphism limitations

### Activities
1. **Recall Chapter 4** (10 min): Remember that HM has let-polymorphism only
   - Can't pass polymorphic functions as arguments
   - Can't return polymorphic functions from functions
   - Can't store polymorphic functions in data structures
2. **Read** (20 min): Overview section about System F's explicit approach
3. **Compare** (15 min): Study the comparison table - what do we gain and lose?
4. **Reflect** (10 min): Why is first-class polymorphism worth the annotation burden?

### Self-Check
- [ ] Can you explain why `λf. f 1, f true` doesn't work in Hindley-Milner?
- [ ] Do you understand that System F makes type abstraction explicit?
- [ ] What's the trade-off: explicit types vs first-class polymorphism?

### Key Insight
System F is more expressive than HM, but you must write all type abstractions and applications explicitly. Type inference is **undecidable**!

---

## Lesson 5.2: New Syntax - Type Abstraction and Application (60-75 minutes)

### Learning Objectives
- Write type abstractions (Λα. t)
- Write type applications (t [τ])
- Understand universal types (∀α. τ)
- Distinguish term-level from type-level operations

### Materials
- README.md: "Syntax" section
- CHEAT_SHEET.md: First page
- TUTORIAL.md: "Part 1: Type Abstraction and Application"

### Activities
1. **Read** (25 min): Syntax of types and terms in System F
2. **Practice** (25 min): Write these functions:
   - Polymorphic identity: `Λα. λx:α. x`
   - Constant function: `Λα. Λβ. λx:α. λy:β. x`
   - Self-application of polyId: `polyId [∀β. β → β] polyId`
3. **Compare** (15 min):
   - Term abstraction `λx:τ. t` vs Type abstraction `Λα. t`
   - Term application `t₁ t₂` vs Type application `t [τ]`
4. **REPL Exercise** (10 min):
   ```bash
   cd chapter-05-system-f
   stack run
   ```
   Try typing: `/\A. \x:A. x`

### Self-Check
- [ ] Can you write a type abstraction from scratch?
- [ ] Do you understand the difference between `λ` and `Λ`?
- [ ] Can you write the type of polymorphic identity?
- [ ] Do you know when to use `[τ]` for type application?

### Common Pitfall
Don't forget type applications! `id true` is wrong - must write `id [Bool] true`

---

## Lesson 5.3: Universal Types (∀α. τ) (60 minutes)

### Learning Objectives
- Understand universal quantification
- Write types with ∀
- Distinguish between type variables and concrete types
- Understand the scope of type variables

### Materials
- README.md: "Type System" section
- TUTORIAL.md: "Part 2: Universal Types"
- CHEAT_SHEET.md: Universal types

### Activities
1. **Read** (20 min): Universal types and quantification
2. **Practice** (25 min): Write types for:
   - Polymorphic identity: `∀α. α → α`
   - Apply function: `∀α. ∀β. (α → β) → α → β`
   - Composition: `∀α. ∀β. ∀γ. (β → γ) → (α → β) → α → γ`
3. **Understand** (15 min): How type variables scope in ∀

### Self-Check
- [ ] Can you read ∀α. τ as "for all types α, τ"?
- [ ] Do you understand that α is a type variable?
- [ ] Can you write the type of compose?

### Key Insight
Universal types `∀α. τ` mean "this works for ANY type α" - true parametric polymorphism!

---

## Lesson 5.4: Typing Rules - T-TyAbs and T-TyApp (75-90 minutes)

### Learning Objectives
- Apply the T-TyAbs rule for type abstraction
- Apply the T-TyApp rule for type application
- Build typing derivations with type contexts (Δ)
- Understand type substitution [α ↦ τ']τ

### Materials
- README.md: "Typing Rules" section
- TUTORIAL.md: "Part 3: Typing Rules for Polymorphism"
- CHEAT_SHEET.md: Typing rules

### Activities
1. **Read** (25 min): T-TyAbs and T-TyApp rules
2. **Understand Contexts** (20 min):
   - Δ: type variable context (which type vars are in scope)
   - Γ: term variable context (which terms are in scope)
3. **Practice** (30 min): Build derivations for:
   - `Λα. λx:α. x : ∀α. α → α`
   - `(Λα. λx:α. x) [Bool] : Bool → Bool`
   - Type substitution: `[α ↦ Bool](α → α)`

### Self-Check
- [ ] Can you apply the T-TyAbs rule?
- [ ] Can you apply the T-TyApp rule?
- [ ] Do you understand how Δ tracks type variables?
- [ ] Can you perform type substitution?

### Common Pitfall
Type application requires checking that the type is well-formed (Δ; Γ ⊢ τ' type)

---

## Lesson 5.5: Complete Type Derivations (90 minutes)

### Learning Objectives
- Build complete typing derivations for System F terms
- Combine term-level and type-level rules
- Verify complex polymorphic functions

### Materials
- TUTORIAL.md: "Part 4: Complete Type Derivations"
- Practice problems

### Activities
1. **Learn** (20 min): How to build derivation trees with both contexts
2. **Practice** (50 min): Build complete derivations for:
   - Polymorphic const: `Λα. Λβ. λx:α. λy:β. x`
   - Composition: `Λα. Λβ. Λγ. λf:β→γ. λg:α→β. λx:α. f (g x)`
   - Self-application: `(Λα. λx:α. x) [∀β. β → β] (Λγ. λy:γ. y)`
3. **Verify** (20 min): Check your derivations step-by-step

### Self-Check
- [ ] Can you build a complete derivation tree?
- [ ] Can you handle both Δ and Γ contexts correctly?
- [ ] Can you trace type substitution through applications?

### Key Insight
Type derivations in System F interleave type-level and term-level reasoning!

---

## Lesson 5.6: Operational Semantics and Evaluation (60 minutes)

### Learning Objectives
- Evaluate type abstractions and applications
- Understand type β-reduction: (Λα. t) [τ] → [α ↦ τ]t
- See how evaluation differs from STLC

### Materials
- README.md: "Operational Semantics" section
- TUTORIAL.md: "Part 5: Evaluation"
- REPL: Use `:step` command

### Activities
1. **Read** (20 min): Evaluation rules E-TyApp and E-TyAppTyAbs
2. **Practice** (25 min): Evaluate step-by-step:
   - `(Λα. λx:α. x) [Bool] true`
   - `(Λα. λx:α. succ x) [Nat] 0`
   - `(Λα. Λβ. λx:α. x) [Nat] [Bool] 5`
3. **REPL Exercise** (15 min): Use `:step` to verify your evaluations

### Self-Check
- [ ] Can you apply type β-reduction?
- [ ] Do you understand that type abstractions are values?
- [ ] Can you trace multi-step evaluation with type applications?

### Key Insight
Type applications evaluate just like term applications, but substitute types!

---

## Lesson 5.7: Church Encodings in System F - Booleans (60 minutes)

### Learning Objectives
- Encode booleans using System F
- Understand how universal types enable encoding
- Implement boolean operations
- See the connection to continuation-passing style

### Materials
- README.md: "Church Encodings - Booleans" section
- TUTORIAL.md: "Part 6: Church Encodings with Universal Types"
- exercises/EXERCISES.md: Exercise 1a

### Activities
1. **Read** (20 min): Church boolean encoding with ∀
   ```
   CBool = ∀A. A → A → A
   true = ΛA. λt:A. λf:A. t
   false = ΛA. λt:A. λf:A. f
   ```
2. **Understand** (20 min): Why do we need ∀A? What does it mean?
3. **Practice** (15 min): Implement `and`, `or`, `not` operations
4. **Test** (5 min): Verify your implementations in the REPL

### Self-Check
- [ ] Can you explain why `CBool = ∀A. A → A → A`?
- [ ] Do you see how true/false "select" arguments?
- [ ] Can you implement boolean operations?

### Key Insight
Universal quantification allows data types to be polymorphic over their result type!

---

## Lesson 5.8: Church Numerals in System F (60 minutes)

### Learning Objectives
- Encode natural numbers with universal types
- Implement arithmetic operations
- Understand the pattern: iteration encoded as function

### Materials
- README.md: "Church Encodings - Natural Numbers" section
- TUTORIAL.md: "Part 7: Church Numerals with ∀"
- exercises/EXERCISES.md: Exercise 3

### Activities
1. **Read** (20 min): Church numeral encoding
   ```
   CNat = ∀A. (A → A) → A → A
   zero = ΛA. λf:A→A. λx:A. x
   succ = λn:CNat. ΛA. λf:A→A. λx:A. f (n [A] f x)
   ```
2. **Practice** (25 min): Implement:
   - `plus : CNat → CNat → CNat`
   - `mult : CNat → CNat → CNat`
   - `exp : CNat → CNat → CNat` (exponentiation)
3. **Test** (15 min): Verify with concrete numbers

### Self-Check
- [ ] Can you explain the type `∀A. (A → A) → A → A`?
- [ ] Why do we need type application `n [A]`?
- [ ] Can you implement plus and mult?

### Practice Problems
From exercises/EXERCISES.md: Exercise 3

---

## Lesson 5.9: Pairs and Lists in System F (75 minutes)

### Learning Objectives
- Encode pairs with universal types
- Encode lists using System F
- Implement list operations (map, fold)
- See the power of Church encodings

### Materials
- README.md: "Church Encodings - Pairs" and "Lists" sections
- TUTORIAL.md: "Part 8: Pairs and Lists"
- exercises/EXERCISES.md: Exercise 2

### Activities
1. **Read** (25 min): Pair and list encodings
   ```
   Pair A B = ∀C. (A → B → C) → C
   List A = ∀R. (A → R → R) → R → R
   ```
2. **Understand** (20 min): Why these types work
3. **Practice** (30 min): Implement:
   - `fst`, `snd` for pairs
   - `nil`, `cons` for lists
   - `map : ∀A. ∀B. (A → B) → List A → List B`

### Self-Check
- [ ] Can you explain the Pair encoding?
- [ ] Can you see lists as "fold" encoded?
- [ ] Can you implement map?

### Key Insight
All data structures can be encoded as their elimination forms!

---

## Lesson 5.10: Parametricity and Free Theorems (90 minutes)

### Learning Objectives
- Understand parametricity theorem
- Derive "theorems for free" from types
- See how polymorphism restricts implementations
- Appreciate the connection to abstraction

### Materials
- README.md: "Parametric Polymorphism" section
- TUTORIAL.md: "Part 9: Parametricity and Free Theorems"
- Wadler's "Theorems for Free!" paper (optional)

### Activities
1. **Read** (30 min): Parametricity theorem and examples
2. **Understand** (30 min): Why `∀α. α → α` must be identity
   - Cannot create values of type α from nothing
   - Cannot inspect values of type α
   - Can only return the input!
3. **Practice** (30 min): What can these functions do?
   - `f : ∀α. List α → List α`
   - `f : ∀α. ∀β. (α → β) → List α → List β`
   - `f : ∀α. α → α → α`

### Self-Check
- [ ] Can you explain parametricity in plain language?
- [ ] Why must `∀α. α → α` be identity?
- [ ] Can you use types to constrain implementations?

### Key Insight
"Theorems for free!" - The type signature tells you what the function must do!

---

## Lesson 5.11: Existential Types and Data Abstraction (75-90 minutes)

### Learning Objectives
- Encode existential types (∃α. τ)
- Implement abstract data types
- Understand information hiding
- See the duality between ∀ and ∃

### Materials
- README.md: "Existential Types" (if present in full README)
- TUTORIAL.md: "Part 10: Existential Types"
- CHEAT_SHEET.md: Existential encoding
- exercises/EXERCISES.md: Exercise 4

### Activities
1. **Read** (25 min): Existential encoding using ∀
   ```
   ∃α. τ  ≡  ∀R. (∀α. τ → R) → R
   ```
2. **Understand** (20 min): How this encoding works
3. **Practice** (30 min): Implement Counter ADT from Exercise 4b
4. **Advanced** (15 min): Compare with interfaces in Java/TypeScript

### Self-Check
- [ ] Can you explain the existential encoding?
- [ ] Do you understand pack/unpack operations?
- [ ] Can you implement an abstract data type?

### Key Insight
Existentials enable information hiding - the type α is "hidden" inside the package!

---

## Lesson 5.12: Impredicativity and Higher-Rank Types (60 minutes)

### Learning Objectives
- Understand impredicative instantiation
- See self-application of polymorphic functions
- Compare with predicative systems (like HM)

### Materials
- README.md: "Comparison with Hindley-Milner" section
- TUTORIAL.md: "Part 11: Impredicativity"
- CHEAT_SHEET.md: Impredicativity examples

### Activities
1. **Read** (25 min): What impredicativity means
2. **Example** (20 min): Trace through:
   ```
   id : ∀α. α → α
   id [∀β. β → β] id : ∀β. β → β
   ```
   This works! We instantiated α with a polymorphic type!
3. **Compare** (15 min): Why doesn't this work in Hindley-Milner?

### Self-Check
- [ ] Can you explain impredicativity?
- [ ] Do you understand self-application in System F?
- [ ] Can you see the difference from HM?

### Key Insight
System F allows quantifying over ALL types, including polymorphic ones!

---

## Lesson 5.13: Properties and Metatheory (60-75 minutes)

### Learning Objectives
- Understand strong normalization
- See that type inference is undecidable
- Appreciate type safety (Progress and Preservation)
- Understand the limitations

### Materials
- README.md: "Properties" section
- TUTORIAL.md: "Part 12: Metatheory"

### Activities
1. **Read** (30 min): Three key properties:
   - Strong normalization (all well-typed terms terminate)
   - Type safety (Progress + Preservation)
   - Undecidability of type inference (Wells 1999)
2. **Reflect** (20 min): Why is inference undecidable?
3. **Compare** (15 min): System F vs HM vs untyped LC

### Self-Check
- [ ] Do you understand that all System F programs terminate?
- [ ] Why is type inference undecidable?
- [ ] Can you explain Progress and Preservation for System F?

### Key Insight
Expressiveness comes at a cost: we must write type annotations because inference is impossible!

---

## Lesson 5.14: Implementation Study (60-90 minutes)

### Learning Objectives
- Understand the System F type checker
- See how type substitution is implemented
- Read and understand the Haskell code
- Use the REPL effectively

### Materials
- Source code: src/TypeCheck.hs, src/Syntax.hs, src/Eval.hs
- README.md: "Implementation" section
- REPL_GUIDE.md (if present)

### Activities
1. **Read Code** (40 min):
   - `src/Syntax.hs` - Type and Term definitions
   - `src/TypeCheck.hs` - Type checking with Δ and Γ
   - `src/Eval.hs` - Evaluation with type substitution
2. **Trace** (20 min): Follow type checking for polymorphic identity
3. **Experiment** (20 min): Use REPL commands:
   - `:type` to check types
   - `:step` to see evaluation
   - `:examples` for pre-defined examples

### Self-Check
- [ ] Do you understand the Type and Term datatypes?
- [ ] Can you trace through typeCheck for a simple term?
- [ ] Have you successfully used the REPL?

---

## Lesson 5.15: Real-World Connections (45-60 minutes)

### Learning Objectives
- See System F concepts in modern languages
- Understand generics in Java, C#, TypeScript, Rust
- Connect theory to practice
- Appreciate the influence of System F

### Materials
- README.md: "Real-World Connections" section
- TUTORIAL.md: "Part 13: System F in the Wild"

### Activities
1. **Read** (20 min): How System F influenced modern languages
2. **Compare** (20 min): System F vs Java generics vs TypeScript
3. **Reflect** (10 min): Where have you used these concepts?

### Self-Check
- [ ] Can you see System F in Java generics?
- [ ] Do you understand how TypeScript uses ∀?
- [ ] Can you explain parametricity in real languages?

---

## Lesson 5.16: Exercises and Practice (4-6 hours)

### Learning Objectives
- Solidify understanding through practice
- Implement Church encodings
- Work with existential types
- Prove free theorems

### Materials
- exercises/EXERCISES.md (all exercises)
- exercises/Solutions.hs (for hints)
- test/ExerciseSpec.hs (automated tests)

### Activities
1. **Exercise 1** (60 min): Church encodings (Option, Either)
2. **Exercise 2** (90 min): Polymorphic data structures (Trees)
3. **Exercise 3** (60 min): Church numerals extended
4. **Exercise 4** (90 min): Existential types and ADTs
5. **Exercise 5** (60 min): Parametricity proofs
6. **Test** (30 min):
   ```bash
   stack test --test-arguments "--match 'Chapter 5'"
   ```

### Self-Check
- [ ] Have you completed Exercises 1-3?
- [ ] Have you attempted Exercises 4-5?
- [ ] Do all tests pass?

---

## Lesson 5.17: Review and Integration (60 minutes)

### Learning Objectives
- Review all major concepts
- Test comprehensive understanding
- Identify gaps
- Prepare for Chapter 6

### Materials
- QUIZ.md (complete all questions)
- CHEAT_SHEET.md (review)
- README.md: "Next Steps" section

### Activities
1. **Self-Quiz** (30 min): Complete all questions in QUIZ.md
2. **Review** (20 min): Go over anything you missed
3. **Look Ahead** (10 min): Preview Chapter 6 (System F-omega)

### Final Self-Check
Before moving to Chapter 6, you should be able to:
- [ ] Write type abstractions and applications fluently
- [ ] Build complete typing derivations with Δ and Γ
- [ ] Implement Church encodings with ∀
- [ ] Explain parametricity and derive free theorems
- [ ] Understand existential types
- [ ] Appreciate the power and cost of explicit polymorphism
- [ ] Score 80%+ on the quiz

---

## Study Tips

### Time Management
- **Minimum**: 1.5 hours per day for 8-10 days
- **Recommended**: 3-4 hour sessions, 3-4 times per week
- **Intensive**: Complete in 4-5 days with 4-5 hour sessions

### Learning Strategies
1. **Master the Notation**: Λ vs λ, [τ] vs application
2. **Draw Derivation Trees**: Visualize Δ and Γ contexts
3. **Use the REPL**: Test everything!
4. **Compare with HM**: See what's different and why
5. **Focus on Parametricity**: It's the most powerful concept
6. **Practice Church Encodings**: They reveal System F's expressiveness

### When You're Stuck
1. Review COMMON_MISTAKES.md
2. Check your type applications - did you forget `[τ]`?
3. Draw out the derivation with both contexts
4. Use the REPL's `:type` and `:step` commands
5. Compare with working examples in TUTORIAL.md
6. Review relevant sections of README.md

### Signs You're Ready for Chapter 6
- You can write polymorphic functions without hesitation
- Type abstractions and applications feel natural
- You understand parametricity intuitively
- You're curious about type-level computation
- You want to abstract over type constructors, not just types

---

## Progress Tracker

- [ ] Lesson 5.1: Motivation - Why Explicit Polymorphism?
- [ ] Lesson 5.2: New Syntax - Type Abstraction and Application
- [ ] Lesson 5.3: Universal Types (∀α. τ)
- [ ] Lesson 5.4: Typing Rules - T-TyAbs and T-TyApp
- [ ] Lesson 5.5: Complete Type Derivations
- [ ] Lesson 5.6: Operational Semantics and Evaluation
- [ ] Lesson 5.7: Church Encodings in System F - Booleans
- [ ] Lesson 5.8: Church Numerals in System F
- [ ] Lesson 5.9: Pairs and Lists in System F
- [ ] Lesson 5.10: Parametricity and Free Theorems
- [ ] Lesson 5.11: Existential Types and Data Abstraction
- [ ] Lesson 5.12: Impredicativity and Higher-Rank Types
- [ ] Lesson 5.13: Properties and Metatheory
- [ ] Lesson 5.14: Implementation Study
- [ ] Lesson 5.15: Real-World Connections
- [ ] Lesson 5.16: Exercises and Practice
- [ ] Lesson 5.17: Review and Integration

**Completed**: _____ / 17 lessons

---

## What's Next?

Once you've completed this chapter, you're ready for:

**Chapter 6: System F-omega (λω)**
- Higher-kinded types
- Type operators (type-level functions)
- Kind system (* vs * → *)
- Type-level computation
- Foundation for Haskell's type system

The journey continues - from polymorphism to type-level programming!
