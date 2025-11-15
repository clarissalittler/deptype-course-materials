# Exercise Implementation Status

## Summary

This document tracks the status of exercise implementations across all chapters.

## ✓ Chapter 1: Untyped Lambda Calculus - COMPLETE

**Status**: Fully implemented with working solutions and tests
**Test Count**: 36 exercise tests (all passing)
**Total Tests**: 57 (21 original + 36 exercises)

### Files
- `exercises/EXERCISES.md` - Complete problem descriptions
- `exercises/Solutions.hs` - Full working implementations
- `test/ExerciseSpec.hs` - Comprehensive test suite

### Topics Covered
1. Church Boolean Operations (AND, OR, XOR)
2. Church Numeral Arithmetic (predecessor, subtraction, equality)
3. Recursion with Y/Z Combinator (factorial, fibonacci)
4. SKI Combinators and Omega
5. List Operations (length, map, filter, fold)

### Key Implementations
- `churchAnd`, `churchOr`, `churchXor` - Boolean operations
- `churchPred` - Predecessor function using the pair trick
- `church Sub`, `churchIsEqual` - Arithmetic operations
- `zCombinator` - Call-by-value fixed point
- `churchFactorial`, `churchFibonacci` - Recursive functions
- `combS`, `combK`, `combI` - Combinator basis
- `churchLength`, `churchMap`, `churchFilter`, `churchFold` - List operations

## Chapter 2: Simply Typed Lambda Calculus - IN PROGRESS

**Status**: Exercise descriptions complete, solutions partially implemented
**Files Created**:
- `exercises/EXERCISES.md` - Complete ✓
- `exercises/Solutions.hs` - Partially implemented
- `test/ExerciseSpec.hs` - Test framework created

### Completed
- Equality (`tmEq`) and less-than (`tmLt`) operations
- Let binding desugaring
- Product and sum type definitions with typing rules
- Progress and preservation demonstrations
- Example programs

### Notes
Full implementation requires extending the base syntax with products, sums, and fix.
Solutions demonstrate the concepts using extended data types.

## Chapter 3: STLC with ADTs

**Status**: Exercise descriptions complete
**Files**: `exercises/EXERCISES.md` ✓

### Planned Exercises
1. List Operations (append, reverse, length)
2. Binary Trees (height, mirror, map, fold)
3. Option Type (map, bind, getOrElse)
4. Expression Evaluator with constant folding
5. Record Operations
6. Pattern Matching Exhaustiveness Checker

### Implementation Strategy
These exercises build on the existing ADT implementation in Chapter 3.
Students can extend the existing `Syntax.hs` and `TypeCheck.hs` files.

## Chapter 4: Hindley-Milner

**Status**: Exercise descriptions complete
**Files**: `exercises/EXERCISES.md` ✓

### Planned Exercises
1. Type Inference Practice (manual then verified)
2. Polymorphic List Operations (map, filter, fold)
3. Let-Polymorphism vs Lambda demonstrations
4. Mutual Recursion extension
5. Polymorphic Trees
6. Type Error Improvements
7. Constraint-Based Inference

### Implementation Strategy
Exercises use the existing type inference engine.
Advanced exercises extend the inference algorithm.

## Chapter 5: System F

**Status**: Exercise descriptions complete
**Files**: `exercises/EXERCISES.md` ✓

### Planned Exercises
1. Church Encodings (Option, Either)
2. Polymorphic Data Structures (Trees, Rose Trees)
3. Extended Church Numerals (exp, factorial, div)
4. Existential Types and ADTs
5. Parametricity Proofs
6. Impredicativity demonstrations
7. System F Limitations

### Implementation Strategy
Build on existing System F implementation with Church encodings.

## Implementation Approach

### Completed Approach (Chapter 1)
1. Define clear problem statements in EXERCISES.md
2. Implement solutions in Solutions.hs
3. Create comprehensive tests in test/ExerciseSpec.hs
4. Update package.yaml to include exercises directory
5. Integrate tests into main test suite
6. Verify all tests pass

### Recommended Approach (Chapters 2-5)

Given the complexity of extending type systems, we recommend a **tutorial-style approach**:

#### For Instructors / Full Implementation
1. **Extend Base Syntax**: Add new constructs to `Syntax.hs`
2. **Extend Type Checker**: Add typing rules to `TypeCheck.hs`
3. **Extend Evaluator**: Add evaluation rules to `Eval.hs`
4. **Add Parser Support**: Update `Parser.hs`
5. **Write Tests**: Create comprehensive test cases
6. **Document**: Explain the extensions

#### For Students / Self-Study
1. Read EXERCISES.md for problem descriptions
2. Attempt implementation without solutions
3. Refer to typing rules and semantics in chapter README
4. Use existing implementations as templates
5. Test manually or write own tests
6. Compare with reference solutions (when available)

## Testing Summary

| Chapter | Description | Tests | Status |
|---------|-------------|-------|--------|
| 1 | Untyped Lambda | 57 | ✓ All passing |
| 2 | STLC | 27 orig | ✓ All passing |
| 3 | STLC + ADTs | 34 orig | ✓ All passing |
| 4 | Hindley-Milner | 21 orig | ✓ All passing |
| 5 | System F | 17 orig | ✓ All passing |

**Original Implementation Tests**: 156 total (all passing)
**Exercise Tests**: 36 for Chapter 1
**Grand Total**: 192+ tests

## Exercise Catalog

### Total Exercise Problems: ~59

- Chapter 1: 15 problems (fully implemented)
- Chapter 2: 10 problems (descriptions + partial solutions)
- Chapter 3: 12 problems (descriptions)
- Chapter 4: 10 problems (descriptions)
- Chapter 5: 12 problems (descriptions)

## Next Steps

### Short Term (For Complete Implementation)
1. Finish Chapter 2 solutions and tests
2. Implement Chapter 3 exercises
3. Implement Chapter 4 exercises
4. Implement Chapter 5 exercises

### Alternative (Tutorial Approach)
1. Create skeleton code with TODOs
2. Provide hints files
3. Create step-by-step guides
4. Provide reference solutions separately

### Recommended (Hybrid)
1. Keep Chapter 1 as fully worked example ✓
2. Provide 2-3 fully worked examples per chapter
3. Leave remaining exercises as practice problems
4. Provide hints and discussion for each
5. Make full solutions available in separate branch

## Usage

### Running Exercises

```bash
# Chapter 1 (complete)
cd chapter-01-untyped-lambda
stack test

# Other chapters (run original tests)
cd chapter-02-simply-typed-lambda
stack test
```

### Working on Exercises

1. Read `exercises/EXERCISES.md` in each chapter
2. Attempt implementation
3. For Chapter 1: Compare with `exercises/Solutions.hs`
4. For Chapters 2-5: Use chapter README as reference

## References

Each EXERCISES.md file includes:
- Problem descriptions
- Type signatures
- Hints
- Learning objectives
- Relevant paper references

## Conclusion

**Chapter 1 provides a complete, working example** of how exercises should be implemented, with full solutions and comprehensive tests.

**Chapters 2-5 provide detailed exercise descriptions** that can be used for:
- Self-study and practice
- Classroom assignments
- Workshop materials
- Further development

The framework is in place for full implementation when desired.

---

Last Updated: 2025-11-13
Primary Implementation: Chapter 1 (57/57 tests passing)
Exercise Descriptions: All 5 chapters complete
