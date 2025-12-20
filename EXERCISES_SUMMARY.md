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

## Chapter 2: Simply Typed Lambda Calculus ✓

**Status**: Complete with exercise tests

**Exercise Progression**:
1. **Easy**: Arithmetic Operations (add, mult, lt, eq)
2. **Easy**: Boolean Operations (AND, OR, NOT, XOR)
3. **Medium**: Higher-Order Functions (compose, twice, const, flip)
4. **Medium**: Conditional Expressions (max, min, absDiff)
5. **Medium**: Let Bindings (syntactic sugar demonstration)
6. **Hard**: Type Safety Proofs (progress and preservation)
7. **Hard**: Advanced Examples (factorial-like, sign, boolToNat)

**Key Concepts**:
- Extending type systems systematically
- Higher-order functions
- Let as syntactic sugar
- Type safety theorems

**Files**:
- `exercises/EXERCISES.md` - Complete ✓
- `exercises/Solutions.hs` - Complete ✓
- `test/ExerciseSpec.hs` - Complete ✓

---

## Chapter 3: STLC with ADTs ✓

**Status**: Complete with exercise tests

**Exercise Progression**:
1. **Easy**: List Operations (append, reverse, length)
2. **Medium**: Binary Trees (height, mirror, map)
3. **Medium**: Option Type (map, bind, getOrElse)
4. **Hard**: Expression Evaluator (eval with Lit, Add, Mul)
5. **Medium**: Record Operations (update field)

**Key Concepts**:
- Recursive data structures
- Pattern matching
- Type-driven development
- ADT design patterns

**Files**:
- `exercises/EXERCISES.md` - Complete ✓
- `exercises/Solutions.hs` - Complete ✓
- `test/ExerciseSpec.hs` - Complete ✓

---

## Chapter 4: Hindley-Milner Type Inference ✓

**Status**: Complete with exercise tests

**Exercise Progression**:
1. **Easy**: Type Inference Practice (compose, S combinator, twice, flip)
2. **Medium**: Polymorphic List Operations (map, filter, length, foldl, foldr)
3. **Hard**: Let-Polymorphism vs Lambda-Polymorphism demonstration
4. **Medium**: Polymorphic Tree Operations (map, fold, height)

**Key Concepts**:
- Principal types
- Let-polymorphism
- Unification
- Type schemes and instantiation

**Files**:
- `exercises/EXERCISES.md` - Complete ✓
- `exercises/Solutions.hs` - Complete ✓
- `test/ExerciseSpec.hs` - Complete ✓

---

## Chapter 5: System F (Polymorphic Lambda Calculus) ✓

**Status**: Complete with exercise tests

**Exercise Progression**:
1. **Easy**: Church Encodings (Option type with none, some, matchOption)
2. **Easy**: Either Type (left, right, matchEither)
3. **Medium**: Polymorphic Trees (leaf, node, treeMap, treeFold, treeHeight)
4. **Medium**: Church Numerals Extended (add, mult, exp, factorial, div)
5. **Hard**: Existential Types (encoding with universals, abstract counter)
6. **Hard**: Impredicativity (self-application, polyTwice)

**Key Concepts**:
- Explicit polymorphism
- Church encodings at type level
- Existential types
- Parametricity and free theorems
- Impredicativity

**Files**:
- `exercises/EXERCISES.md` - Complete ✓
- `exercises/Solutions.hs` - Complete ✓
- `test/ExerciseSpec.hs` - Complete ✓

---

## Exercise Statistics

| Chapter | Status | Test Count | Concepts Covered |
|---------|--------|------------|------------------|
| 1 | ✓ Complete | 36 tests | Church encodings, recursion, combinators |
| 2 | ✓ Complete | 50+ tests | Arithmetic, booleans, higher-order, type safety |
| 3 | ✓ Complete | 40+ tests | Lists, trees, options, evaluators, records |
| 4 | ✓ Complete | 30+ tests | Inference, polymorphism, let vs lambda |
| 5 | ✓ Complete | 60+ tests | Church encodings, existentials, parametricity |
| 6 | ✓ Complete | Included | Type operators, higher-kinded types |
| 7 | ✓ Complete | Included | Pi/Sigma types, dependent functions |
| 8 | ✓ Complete | Included | Equality proofs, vectors, theorem proving |

**Total**: 200+ exercise tests across 8 chapters

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

## Contributing

To add exercises:
1. Follow the chapter structure
2. Provide clear problem statements
3. Include type signatures
4. Write comprehensive tests
5. Document edge cases
6. Add references to relevant papers

---

Last Updated: 2025-12-20
