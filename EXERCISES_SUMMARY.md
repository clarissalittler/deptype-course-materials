# Course Exercises Summary

## Overview

Each chapter includes a progression of exercises from easy to hard, with full solutions and tests.

## Chapter 1: Untyped Lambda Calculus ✓

**Status**: Complete with 36 exercise tests (all passing)

**Exercise Progression**:
1. **Easy**: Church Boolean Operations (AND, OR, XOR)
2. **Medium**: Church Numeral Arithmetic (predecessor, subtraction, equality)
3. **Hard**: Recursion with Y/Z Combinator (factorial, fibonacci)
4. **Hard**: Advanced Combinators (S, K, I, Ω)
5. **Medium-Hard**: List Operations (length, map, filter, fold)

**Files**:
- `exercises/EXERCISES.md` - Problem descriptions
- `exercises/Solutions.hs` - Complete implementations
- `test/ExerciseSpec.hs` - 36 tests

**Total Tests**: 57 (21 original + 36 exercises)

---

## Chapter 2: Simply Typed Lambda Calculus

**Status**: Exercises defined

**Exercise Progression**:
1. **Easy**: Arithmetic Extensions (mult, lt, eq)
2. **Medium**: Product Types (pairs with fst/snd)
3. **Medium**: Sum Types (disjoint unions with case)
4. **Medium**: Let Bindings (syntactic sugar)
5. **Hard**: Fixed Point Combinator (factorial with fix)
6. **Hard**: Type Safety Proofs (progress and preservation)

**Key Concepts**:
- Extending type systems systematically
- Product and sum types
- Recursion in typed settings
- Type safety theorems

**Files**:
- `exercises/EXERCISES.md` - Complete ✓
- `exercises/Solutions.hs` - To implement
- `test/ExerciseSpec.hs` - To create

---

## Chapter 3: STLC with ADTs

**Suggested Exercises**:

1. **Easy**: List Operations
   - Implement `append : List τ → List τ → List τ`
   - Implement `reverse : List τ → List τ`
   - Implement `length : List τ → Nat`

2. **Medium**: Tree Data Type
   - Define `Tree τ = Leaf τ | Node (Tree τ) (Tree τ)`
   - Implement `height : Tree τ → Nat`
   - Implement `mirror : Tree τ → Tree τ`
   - Implement `map : (τ₁ → τ₂) → Tree τ₁ → Tree τ₂`

3. **Medium**: Option Type Operations
   - `Option τ = None | Some τ`
   - Implement `map : (τ₁ → τ₂) → Option τ₁ → Option τ₂`
   - Implement `bind : Option τ₁ → (τ₁ → Option τ₂) → Option τ₂`
   - Implement `getOrElse : Option τ → τ → τ`

4. **Hard**: Expression Evaluator
   - Define: `Expr = Lit Nat | Add Expr Expr | Mul Expr Expr | Let Var Expr Expr`
   - Implement: `eval : Expr → Nat`
   - Implement: `optimize : Expr → Expr` (constant folding)

5. **Hard**: Pattern Matching Exhaustiveness
   - Implement exhaustiveness checker for pattern matches
   - Detect unreachable patterns
   - Ensure all cases are covered

**Key Concepts**:
- Recursive data structures
- Pattern matching
- Type-driven development
- ADT design patterns

---

## Chapter 4: Hindley-Milner Type Inference

**Suggested Exercises**:

1. **Easy**: Type Inference Practice
   - Infer types of: `λf. λg. λx. f (g x)`
   - Infer types of: `λx. λy. λz. x z (y z)`
   - Infer types of: `λf. λx. f (f x)`

2. **Medium**: Polymorphic List Operations
   - Implement with full type inference:
     - `map : (α → β) → List α → List β`
     - `filter : (α → Bool) → List α → List α`
     - `foldl : (β → α → β) → β → List α → β`
     - `zipWith : (α → β → γ) → List α → List β → List γ`

3. **Medium**: Polymorphic Tree Operations
   - `map : (α → β) → Tree α → Tree β`
   - `fold : (α → β → β → β) → β → Tree α → β`

4. **Hard**: Let-Polymorphism vs Lambda-Polymorphism
   - Demonstrate: `let f = λx. x in (f 1, f true)` ✓
   - Demonstrate: `(λf. (f 1, f true)) (λx. x)` ✗
   - Explain the difference

5. **Hard**: Mutual Recursion
   - Extend with: `let rec f₁ = t₁ and f₂ = t₂ in t`
   - Implement type inference for mutually recursive functions
   - Example: `isEven` and `isOdd`

6. **Hard**: Type Error Messages
   - Improve unification errors
   - Show type mismatch locations
   - Suggest fixes for common errors

**Key Concepts**:
- Principal types
- Let-polymorphism
- Unification
- Type schemes and instantiation

---

## Chapter 5: System F (Polymorphic Lambda Calculus)

**Suggested Exercises**:

1. **Easy**: Church Encodings in System F
   - **Option**: `Option α = ∀R. R → (α → R) → R`
     - `none : ∀α. Option α`
     - `some : ∀α. α → Option α`
     - `match : ∀α. ∀R. Option α → R → (α → R) → R`

   - **Either**: `Either α β = ∀R. (α → R) → (β → R) → R`
     - `left : ∀α. ∀β. α → Either α β`
     - `right : ∀α. ∀β. β → Either α β`

2. **Medium**: Polymorphic Data Structures
   - **Binary Trees**:
     ```
     Tree α = ∀R. R → (α → R → R → R) → R
     leaf : ∀α. Tree α
     node : ∀α. α → Tree α → Tree α → Tree α
     ```
   - Implement: `map`, `fold`, `height`

3. **Medium**: Church Numerals Extended
   - Implement: `exp : CNat → CNat → CNat` (exponentiation)
   - Implement: `factorial : CNat → CNat`
   - Implement: `div : CNat → CNat → CNat` (integer division)

4. **Hard**: Existential Types
   - Encode existentials using universals:
     ```
     ∃α. τ  ≡  ∀R. (∀α. τ → R) → R
     ```
   - Implement abstract data type (ADT) for a counter:
     ```
     Counter = ∃α. { new : α, inc : α → α, get : α → Nat }
     ```

5. **Hard**: Parametricity
   - Prove: `∀α. List α → List α` can only be identity or return empty list
   - Prove: `∀α. ∀β. (α → β) → List α → List β` must be `map`
   - Demonstrate free theorems

6. **Hard**: Impredicative Instantiation
   - Create: `id : ∀α. α → α`
   - Instantiate with: `∀β. β → β`
   - Show: `id [∀β. β → β] id` is well-typed

**Key Concepts**:
- Explicit polymorphism
- Church encodings at type level
- Existential types
- Parametricity and free theorems
- Impredicativity

---

## Implementation Roadmap

### Phase 1: Complete Chapter 1 ✓
- ✓ 36 exercises implemented
- ✓ All tests passing
- ✓ Solutions documented

### Phase 2: Chapter 2-5 (Recommended Approach)

For each chapter, create:

1. **EXERCISES.md** - Problem descriptions ✓ (Ch 1, 2)
2. **Key Examples** - 2-3 fully worked examples per difficulty level
3. **Test Stubs** - Test cases for students to run
4. **Solutions Branch** - Full solutions in separate directory

### Alternative: Self-Study Format

Instead of complete implementations, provide:
- **Starter Code**: Type signatures and TODO comments
- **Hints File**: Progressive hints for each exercise
- **Discussion**: Common pitfalls and insights
- **Further Reading**: Papers and resources for each topic

---

## Exercise Statistics

| Chapter | Difficulty | Estimated Exercises | Concepts Covered |
|---------|-----------|---------------------|------------------|
| 1 | Easy-Hard | 15 problems | Church encodings, recursion, combinators |
| 2 | Easy-Hard | 10 problems | Extensions, products, sums, fix, safety |
| 3 | Easy-Hard | 12 problems | ADTs, trees, evaluators, exhaustiveness |
| 4 | Medium-Hard | 10 problems | Inference, polymorphism, mutual recursion |
| 5 | Medium-Hard | 12 problems | Church encodings, existentials, parametricity |

**Total**: ~59 exercises across 5 chapters

---

## How to Use These Exercises

### For Instructors
- Each chapter builds on previous concepts
- Exercises progress from mechanical to creative
- Solutions demonstrate best practices
- Tests ensure correctness

### For Self-Study
1. Read the chapter README
2. Attempt exercises without looking at solutions
3. Run tests to check your work
4. Review solutions for alternative approaches
5. Extend with your own variations

### For Workshops
- Easy exercises: 30-60 minutes
- Medium exercises: 1-2 hours
- Hard exercises: 2-4 hours
- Can be done in pairs or small groups

---

## Future Additions

### Chapter 6: System F-omega
- Kind inference
- Type-level functions
- Higher-kinded polymorphism
- Generic programming

### Chapter 7-8: Dependent Types
- Dependent pairs and functions
- Equality proofs
- Vector operations
- Certified programming

---

## Contributing

To add exercises:
1. Follow the chapter structure
2. Provide clear problem statements
3. Include type signatures
4. Write comprehensive tests
5. Document edge cases
6. Add references to relevant papers

---

Last Updated: 2025-11-13
