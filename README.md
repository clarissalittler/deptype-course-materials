# Type Systems: From Lambda Calculus to Dependent Types

A comprehensive course on implementing type systems in Haskell, progressing from untyped lambda calculus through System F to full dependent types with equality types and inductive families.

## Course Overview

This course provides **complete, tested implementations** of major type systems, with formal semantics, comprehensive documentation, and progressive exercises.

### Chapters

1. **Untyped Lambda Calculus** ✓ - Foundation of computation
2. **Simply Typed Lambda Calculus (STLC)** ✓ - Type safety and termination
3. **STLC with ADTs** ✓ - Algebraic data types and pattern matching
4. **Hindley-Milner Type Inference** ✓ - Automatic polymorphic type inference
5. **System F** ✓ - Explicit polymorphism and parametricity
6. **System F-omega** ✓ - Higher-kinded types and type operators
7. **Dependent Types** ✓ - Pi and Sigma types, unified terms and types
8. **Full Dependent Types** ✓ - Universe hierarchy, equality types, inductive families

## Quick Start

```bash
# Clone the repository
cd deptype-course-materials

# Build and test Chapter 1
cd chapter-01-untyped-lambda
stack init
stack build
stack test  # 57/57 tests passing

# Try other chapters
cd ../chapter-02-simply-typed-lambda
stack build && stack test  # 27/27 tests passing
```

## Course Statistics

- **8 Complete Chapters** with full implementations
- **282 Total Tests** (all passing)
  - 246 implementation tests
  - 36 exercise tests (Chapter 1)
- **~85+ Exercise Problems** documented across all chapters
- **Comprehensive Documentation** with formal semantics (~5000+ lines)
- **Extensive References** to foundational papers (100+ references)

## Chapter Details

### Chapter 1: Untyped Lambda Calculus ✓

**Features**:
- Three evaluation strategies (normal order, call-by-name, call-by-value)
- Church encodings (booleans, numerals, pairs, lists)
- Parser with λ syntax support
- **Complete exercise suite** (36 tests)

**Key Files**:
- `src/Syntax.hs` - AST, substitution, alpha equivalence
- `src/Eval.hs` - Multiple evaluation strategies
- `src/Parser.hs` - Megaparsec parser
- `exercises/Solutions.hs` - Y combinator, SKI combinators, list ops
- `README.md` - Formal semantics and theory

**Tests**: 57/57 passing (21 implementation + 36 exercises)

### Chapter 2: Simply Typed Lambda Calculus ✓

**Features**:
- Full type checker with typing rules
- Type safety proofs (Progress, Preservation)
- Booleans, natural numbers, conditionals
- Call-by-value evaluation

**Key Files**:
- `src/TypeCheck.hs` - Complete type checker
- `src/Eval.hs` - CBV evaluation
- `exercises/EXERCISES.md` - Extensions (products, sums, fix)

**Tests**: 27/27 passing
**Exercises**: 10 problems documented

### Chapter 3: STLC with Algebraic Data Types ✓

**Features**:
- Product types (pairs, tuples)
- Sum types (disjoint unions)
- Records and variants
- Lists with pattern matching
- Comprehensive pattern matching

**Key Files**:
- `src/Syntax.hs` - Extended AST with all ADT constructs
- `src/TypeCheck.hs` - Pattern type checking
- `src/Eval.hs` - Pattern matching evaluation

**Tests**: 34/34 passing
**Exercises**: 12 problems (lists, trees, evaluators, exhaustiveness)

### Chapter 4: Hindley-Milner Type Inference ✓

**Features**:
- Full Algorithm W implementation
- Robinson's unification with occurs check
- Let-polymorphism (generalization/instantiation)
- Type schemes with ∀ quantifiers
- No type annotations on lambdas

**Key Files**:
- `src/Infer.hs` - Algorithm W, unification, substitution
- `README.md` - Detailed type inference theory

**Tests**: 21/21 passing
**Exercises**: 10 problems (polymorphic operations, mutual recursion)

**Key Insight**: Let-bound variables are polymorphic; lambda-bound are not.

### Chapter 5: System F ✓

**Features**:
- Explicit polymorphism (Λα. t and t [τ])
- Universal quantification (∀α. τ)
- Bidirectional type checking
- Church encodings at type level
- Parametricity

**Key Files**:
- `src/Syntax.hs` - Type abstraction and application
- `src/TypeCheck.hs` - Bidirectional type checking with kinds
- `README.md` - Church encodings, parametricity, undecidability

**Tests**: 17/17 passing
**Exercises**: 12 problems (existentials, parametricity, impredicativity)

**Key Property**: Type inference is undecidable (Wells, 1999)

### Chapter 6: System F-omega ✓

**Features**:
- Kind system (*, * → *, (* → *) → *)
- Type-level lambda abstraction (Λα::κ. τ)
- Type-level application (τ₁ τ₂)
- Higher-kinded polymorphism
- Type operators (List, Maybe, Either)
- Church encodings at kind level

**Key Files**:
- `src/Syntax.hs` - Kinds, type operators, TyLam/TyApp
- `src/TypeCheck.hs` - Kinding judgment, kind inference
- `src/Eval.hs` - Type-level beta reduction
- `exercises/Solutions.hs` - Type operators, functors, monads

**Tests**: 46/46 passing
**Exercises**: 10 problems (type-level computation, Church encodings)

**Key Property**: Adds expressiveness for type-level programming

### Chapter 7: Dependent Types ✓

**Features**:
- Unified terms and types (single syntax)
- Pi types (Π(x:A). B) - dependent functions
- Sigma types (Σ(x:A). B) - dependent pairs
- Type-in-Type (simplified, inconsistent)
- Natural numbers, booleans, lists
- Curry-Howard correspondence

**Key Files**:
- `src/Syntax.hs` - Unified Term data type
- `src/TypeCheck.hs` - Normalization-based equality
- `src/Eval.hs` - Beta reduction with substitution
- `exercises/Solutions.hs` - Dependent functions, Church encodings

**Tests**: 39/39 passing
**Exercises**: 7 problems (polymorphic types, Church encodings)

**Key Insight**: Types can depend on values, but Type:Type is inconsistent

### Chapter 8: Full Dependent Types ✓

**Features**:
- Universe hierarchy (Type 0 : Type 1 : Type 2 : ...)
- Propositional equality (Eq A x y)
- J eliminator for equality induction
- Inductive families (Vec, Fin)
- Pattern matching with dependent types
- Eliminators (natElim, boolElim, unitElim, emptyElim)
- Full Curry-Howard correspondence

**Key Files**:
- `src/Syntax.hs` - Universe levels, equality types, patterns, inductive families
- `src/TypeCheck.hs` - Universe-aware type checking
- `src/Eval.hs` - Pattern matching, eliminators, J reduction
- `exercises/Solutions.hs` - Equality proofs, vector operations, theorem proving

**Tests**: 41/41 passing
**Exercises**: 8 problems (equality proofs, inductive families, decidable equality)

**Key Achievement**: Consistent foundation for mathematics and verified programming

## Exercises

### Chapter 1: Fully Implemented ✓

36 exercise tests covering:
- Church boolean operations (AND, OR, XOR)
- Church numeral arithmetic (predecessor, subtraction, equality)
- Fixed-point combinators (Y/Z, factorial, fibonacci)
- SKI combinators
- Church-encoded list operations (map, filter, fold)

See `chapter-01-untyped-lambda/exercises/` for complete solutions.

### Chapters 2-8: Documented

Each chapter includes detailed `exercises/EXERCISES.md` with:
- Problem descriptions
- Type signatures and formal specifications
- Hints and learning objectives
- References to relevant papers

Chapters 6-8 additionally include complete `exercises/Solutions.hs` implementations:
- **Chapter 6**: Type operators, functors, monads in F-omega
- **Chapter 7**: Dependent functions, Church encodings with Pi types
- **Chapter 8**: Equality proofs, vector operations, theorem proving

**Total**: ~85+ exercise problems across all chapters

See `EXERCISES_SUMMARY.md` for complete overview.

## Documentation

Each chapter includes:
- **README.md** - Theory, formal semantics, typing rules, references
- **EXERCISES.md** - Progressive exercise problems
- **Comprehensive comments** in source code
- **References** to foundational papers

### Self-Study Learning Materials (NEW!)

**All 8 chapters now include comprehensive self-study materials** designed for students to learn independently:

Each chapter contains:
- **LESSON_PLAN.md** - Structured lesson-by-lesson guide with:
  - Time estimates (12-20 hours per chapter)
  - Clear learning objectives for each lesson
  - Activities and practice exercises
  - Self-check questions to verify understanding
  - Progress tracking checklists

- **TUTORIAL.md** - Step-by-step worked examples with:
  - Plain language explanations
  - Complete derivations and type checking examples
  - Practice problems with solutions
  - Real-world connections to modern languages
  - Conversational, accessible tone

- **QUIZ.md** - Self-assessment quizzes with:
  - 20-45 multiple choice questions per chapter
  - Complete answer keys with explanations
  - Scoring guides and interpretation
  - Targeted review recommendations

- **COMMON_MISTAKES.md** - Practical debugging guides with:
  - 8-11 common pitfalls per chapter
  - Recognition strategies
  - How to fix each mistake
  - Practice problems with solutions
  - Debugging checklists

**Total Learning Materials**: Over 600KB of educational content across all chapters, designed to make the course immediately accessible to independent learners.

### Key Documents

- `CHAPTER_0_PREREQUISITES.md` - What you need to know before starting
- `STUDY_GUIDE.md` - Multiple learning paths and study strategies
- `GLOSSARY.md` - Comprehensive terminology reference
- `EXERCISES_SUMMARY.md` - Complete exercise catalog

## Technology Stack

- **Language**: Haskell (GHC 9.6.6)
- **Build System**: Stack (resolver lts-22.28)
- **Parser**: Megaparsec
- **Testing**: Hspec
- **Key Libraries**: containers, mtl, text

## Learning Path

### Self-Study Track (Recommended for Independent Learners)
1. **Start with prerequisites**: Read `CHAPTER_0_PREREQUISITES.md`
2. **Choose your path**: See `STUDY_GUIDE.md` for multiple learning tracks
3. **For each chapter**:
   - Follow the `LESSON_PLAN.md` (includes time estimates and structure)
   - Work through `TUTORIAL.md` for step-by-step examples
   - Complete exercises from `exercises/EXERCISES.md`
   - Take the `QUIZ.md` to verify understanding
   - Reference `COMMON_MISTAKES.md` when stuck
   - Use the REPL to experiment interactively
4. **Track progress**: Each lesson plan includes a progress tracker
5. **Time estimate**: 8-20 hours per chapter (100-160 hours total for all 8 chapters)

### For Beginners (Traditional Approach)
1. Start with Chapter 1 (Untyped Lambda Calculus)
2. Read the README for theoretical foundation
3. Study the implementation in `src/`
4. Attempt exercises in `exercises/EXERCISES.md`
5. Compare with `exercises/Solutions.hs`
6. Run tests to verify understanding

### For Intermediate Students
1. Start with Chapter 2 or 3
2. Understand typing rules
3. Implement exercises
4. Study type safety proofs
5. Progress to Chapters 4-5 for advanced topics

### For Advanced Study
1. Focus on Chapters 4-8
2. Study Algorithm W and unification
3. Understand parametricity and free theorems
4. Explore dependent types and proof systems
5. Read referenced papers for depth

## Build All Chapters

```bash
# Build all chapters
for dir in chapter-*/; do
  (cd "$dir" && echo "Building $dir..." && stack build)
done

# Test all chapters
for dir in chapter-*/; do
  (cd "$dir" && echo "Testing $dir..." && stack test)
done
```

## Key Features

### Theoretical Rigor
- Formal syntax and semantics
- Typing rules with inference rules
- Metatheory proofs (Progress, Preservation)
- References to foundational papers

### Practical Implementation
- Clean, idiomatic Haskell
- Comprehensive test coverage (192 tests)
- Parser for concrete syntax
- Pretty printer for output
- Error messages with type information

### Educational Value
- Progressive complexity
- Extensive documentation
- Working examples
- Exercise problems with solutions
- Suitable for self-study or classroom use

## References

### Foundational Papers

1. **Church** (1936) - Untyped lambda calculus
2. **Curry & Feys** (1958) - Simply typed lambda calculus
3. **Milner** (1978) - Type polymorphism (Hindley-Milner)
4. **Damas & Milner** (1982) - Principal type schemes
5. **Girard** (1972) & **Reynolds** (1974) - System F (independent discoveries)
6. **Reynolds** (1983) - Parametric polymorphism
7. **Wadler** (1989) - Theorems for free!
8. **Wells** (1999) - Undecidability of System F type inference

### Key Books

- **Pierce** (2002) - *Types and Programming Languages* (TAPL)
- **Harper** (2016) - *Practical Foundations for Programming Languages*
- **Barendregt** (1984) - *Lambda Calculus: Its Syntax and Semantics*
- **Girard, Lafont, Taylor** (1989) - *Proofs and Types*

See individual chapter READMEs for more specific references.

## Project Structure

```
deptype-course-materials/
├── README.md                          # This file
├── EXERCISES_SUMMARY.md               # Exercise catalog
├── chapter-01-untyped-lambda/
│   ├── src/                          # Core implementation
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ 57 tests
│   └── README.md                     # ✓ Full documentation
├── chapter-02-simply-typed-lambda/
│   ├── src/                          # ✓ Type checker, evaluator
│   ├── exercises/                    # Descriptions complete
│   ├── test/                         # ✓ 27 tests
│   └── README.md                     # ✓ Typing rules, metatheory
├── chapter-03-stlc-adt/
│   ├── src/                          # ✓ ADTs, pattern matching
│   ├── exercises/                    # Descriptions complete
│   ├── test/                         # ✓ 34 tests
│   └── README.md                     # ✓ ADT semantics
├── chapter-04-hindley-milner/
│   ├── src/                          # ✓ Algorithm W
│   ├── exercises/                    # Descriptions complete
│   ├── test/                         # ✓ 21 tests
│   └── README.md                     # ✓ Type inference theory
├── chapter-05-system-f/
│   ├── src/                          # ✓ System F implementation
│   ├── exercises/                    # Descriptions complete
│   ├── test/                         # ✓ 17 tests
│   └── README.md                     # ✓ Parametricity, Church encodings
├── chapter-06-system-f-omega/
│   ├── src/                          # ✓ Kinds, type operators
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ 46 tests
│   └── README.md                     # ✓ Higher-kinded types
├── chapter-07-dependent-types/
│   ├── src/                          # ✓ Pi/Sigma types
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ 39 tests
│   └── README.md                     # ✓ Dependent types theory
└── chapter-08-full-dependent-types/
    ├── src/                          # ✓ Universe hierarchy, equality types
    ├── exercises/                    # ✓ Complete solutions
    ├── test/                         # ✓ 41 tests
    └── README.md                     # ✓ Full dependent types, proof theory
```

## Contributing

This is an educational resource. Potential contributions:
- Additional exercise implementations for Chapters 2-5
- More examples and test cases
- Improved documentation and explanations
- Additional proofs and theorems for Chapters 7-8
- Extensions (e.g., linear types, effect systems, gradual typing)
- Bug fixes and clarifications

## License

BSD3

## Acknowledgments

Built with Claude Code (Anthropic) as an educational resource for understanding type system implementation.

## Contact

This project demonstrates progressive type system implementation from first principles.
Perfect for:
- Students learning type theory
- Implementers of programming languages
- Researchers exploring type systems
- Anyone interested in the foundations of programming languages

---

**Status**: ✓ ALL 8 CHAPTERS COMPLETE | 282/282 tests passing | ~85+ exercises documented | **NEW: Complete self-study materials for all chapters!**

**Journey**: Untyped Lambda Calculus → Simply Typed → ADTs → Type Inference → System F → System F-omega → Dependent Types → Full Dependent Types with Universe Hierarchy

**Achievement**: Complete implementation from first principles to a foundation for mathematics and verified programming - now with comprehensive learning materials for independent study!

**New in 2025**: Phase 1 learning materials (LESSON_PLAN, TUTORIAL, QUIZ, COMMON_MISTAKES) for all 8 chapters, making this course fully self-study ready.

Last Updated: 2025-12-20
