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
9. **Subtyping** ✓ - Width/depth subtyping, covariance/contravariance, Top/Bot
10. **Linear Types** ✓ - Resource tracking, multiplicities, bang types
11. **Refinement Types** ✓ - Predicate refinements, subtyping via implication
12. **Effect Systems** ✓ - Tracking computational effects in types
13. **Gradual Typing** ✓ - Mixing static and dynamic typing
14. **Row Types** ✓ - Extensible records and polymorphic variants
15. **Recursive Types** ✓ - Iso-recursive and equi-recursive approaches
16. **Homotopy Type Theory** ✓ - Univalence and higher inductive types
17. **Abstract Machines** ✓ - CEK, SECD, and Krivine machines
18. **Normalization by Evaluation** ✓ - Semantic normalization and type-directed quotation
19. **Bidirectional Type Checking** ✓ - Inference/checking modes, minimal annotations
20. **Denotational Semantics** ✓ - Domain theory and fixed points
21. **Module Systems** ✓ - Structures, signatures, functors, sealing
22. **Constraint-Based Inference** ✓ - Two-phase inference, constraint generation and solving

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

- **22 Complete Chapters** with full implementations
- **800+ Total Tests** (all passing)
  - 700+ implementation tests
  - 100+ exercise tests
- **~190+ Exercise Problems** documented across all chapters
- **Comprehensive Documentation** with formal semantics (~15000+ lines)
- **Extensive References** to foundational papers (200+ references with Google Scholar links)
- **Interactive REPLs** for all chapters with step-by-step evaluation

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

### Chapter 9: Subtyping ✓

**Features**:
- Width subtyping (more fields = subtype)
- Depth subtyping (more specific field types = subtype)
- Function subtyping (contravariant/covariant)
- Top and Bot types
- Subsumption rule
- Join and meet (LUB/GLB)
- Type ascription

**Key Files**:
- `src/Syntax.hs` - Types with Top, Bot, records
- `src/TypeCheck.hs` - Subtyping algorithm, join/meet
- `src/Eval.hs` - CBV evaluation with records
- `exercises/EXERCISES.md` - Variance, bounded quantification

**Tests**: 74/74 passing
**Exercises**: 10 problems + 3 challenges (variance, row polymorphism, F<:)

**Key Insight**: Subtyping allows implicit upcasting based on structural relationships

### Chapter 10: Linear Types ✓

**Features**:
- Multiplicities (linear/unrestricted)
- Usage tracking in type checker
- Pair types (tensor product)
- Bang types for unrestricted values
- Linear/unrestricted function types

**Key Files**:
- `src/Syntax.hs` - Types with multiplicities
- `src/TypeCheck.hs` - Usage tracking, linearity enforcement
- `src/Eval.hs` - CBV evaluation with pairs
- `exercises/EXERCISES.md` - Session types, graded modalities

**Tests**: 45/45 passing
**Exercises**: 8 problems + 3 challenges (session types, fractional permissions)

**Key Insight**: Linear types ensure resources are used exactly once

### Chapter 11: Refinement Types ✓

**Features**:
- Refinement types {x: T | φ(x)}
- Predicate language (arithmetic, comparisons, boolean ops)
- Subtyping via predicate implication
- Path sensitivity (branch-aware typing)
- Dependent function types
- Predicate validity checking

**Key Files**:
- `src/Syntax.hs` - Types with refinements, predicates
- `src/TypeCheck.hs` - Subtyping via implication, path sensitivity
- `src/Eval.hs` - CBV evaluation
- `exercises/EXERCISES.md` - Liquid types, SMT integration

**Tests**: 82/82 passing
**Exercises**: 10 problems + 4 challenges (SMT integration, liquid types)

**Key Insight**: Refinement types bridge simple types and full dependent types

### Chapter 12: Effect Systems ✓

**Features**:
- Effect annotations on function types
- Effect polymorphism
- Effect inference
- Row-based effect tracking
- Common effects: IO, State, Exception

**Key Files**:
- `src/Syntax.hs` - Types with effect annotations
- `src/TypeCheck.hs` - Effect checking and inference
- `src/Eval.hs` - Effect-aware evaluation
- `exercises/EXERCISES.md` - Effect handlers, algebraic effects

**Tests**: 40+ passing
**Exercises**: 8 problems + challenges (algebraic effects, effect handlers)

**Key Insight**: Effects track what computations *do*, not just what they return

### Chapter 13: Gradual Typing ✓

**Features**:
- Dynamic type (?)
- Consistency relation
- Cast insertion
- Blame tracking
- Gradual guarantee

**Key Files**:
- `src/Syntax.hs` - Types with dynamic type
- `src/TypeCheck.hs` - Consistency checking, cast insertion
- `src/Eval.hs` - Runtime cast evaluation with blame
- `exercises/EXERCISES.md` - Blame calculus, AGT

**Tests**: 35+ passing
**Exercises**: 8 problems + challenges (blame tracking, space efficiency)

**Key Insight**: Gradual typing allows incremental migration between dynamic and static typing

### Chapter 14: Row Types ✓

**Features**:
- Row polymorphism
- Extensible records
- Polymorphic variants
- Record extension and restriction
- Lack/presence constraints

**Key Files**:
- `src/Syntax.hs` - Row types, record/variant types
- `src/TypeCheck.hs` - Row unification, constraint solving
- `src/Eval.hs` - Record and variant operations
- `exercises/EXERCISES.md` - Effect rows, scoped labels

**Tests**: 45+ passing
**Exercises**: 10 problems + challenges (effect systems via rows)

**Key Insight**: Row polymorphism enables flexible, extensible data structures

### Chapter 15: Recursive Types ✓

**Features**:
- Iso-recursive types (explicit fold/unfold)
- Equi-recursive types (structural equality)
- μ-types and fixed points
- Recursive type checking
- Coinductive interpretation

**Key Files**:
- `src/Syntax.hs` - Mu types, fold/unfold
- `src/TypeCheck.hs` - Recursive type equality
- `src/Eval.hs` - Fold/unfold evaluation
- `exercises/EXERCISES.md` - Infinite data, corecursion

**Tests**: 40+ passing
**Exercises**: 8 problems + challenges (streams, coinduction)

**Key Insight**: Recursive types enable self-referential data structures like lists and trees

### Chapter 16: Homotopy Type Theory ✓

**Features**:
- Identity types and path induction
- Univalence axiom
- Higher inductive types
- Function extensionality
- Propositional truncation
- n-Types and h-levels

**Key Files**:
- `src/Syntax.hs` - Path types, higher inductive types
- `src/TypeCheck.hs` - Path induction, univalence
- `src/Eval.hs` - Path operations
- `exercises/EXERCISES.md` - Circle type, fundamental group

**Tests**: 35+ passing
**Exercises**: 10 problems + challenges (synthetic homotopy theory)

**Key Insight**: HoTT provides a computational interpretation of homotopy theory

### Chapter 17: Abstract Machines ✓

**Features**:
- CEK machine (environments + continuations)
- SECD machine (classic architecture)
- Krivine machine (call-by-name)
- Explicit evaluation contexts
- Step-by-step execution traces

**Key Files**:
- `src/CEK.hs` - CEK machine with frames
- `src/SECD.hs` - Stack-based SECD
- `src/Krivine.hs` - Call-by-name evaluation
- `exercises/EXERCISES.md` - Machine extensions, CPS

**Tests**: 35+ passing
**Exercises**: 10 problems + challenges (control operators, abstract machine design)

**Key Insight**: Abstract machines bridge high-level semantics and low-level execution

### Chapter 18: Normalization by Evaluation ✓

**Features**:
- Semantic domain with closures
- Type-directed quotation
- Normalization for STLC
- De Bruijn indices/levels
- Neutral terms and normal forms

**Key Files**:
- `src/NbE.hs` - Eval, quote, normalize
- `src/Semantic.hs` - Semantic domain
- `src/TypeCheck.hs` - NbE-based equality
- `exercises/EXERCISES.md` - Extensions, proofs

**Tests**: 42+ passing
**Exercises**: 10 problems + challenges (dependent types NbE, reflection)

**Key Insight**: NbE uses the host language's evaluation to normalize terms

### Chapter 19: Bidirectional Type Checking ✓

**Features**:
- Inference mode (⇒) for elimination forms
- Checking mode (⇐) for introduction forms
- Minimal type annotations
- Subsumption rule
- Polymorphism support

**Key Files**:
- `src/TypeCheck.hs` - Bidirectional checking
- `src/Syntax.hs` - Annotated/unannotated lambdas
- `exercises/EXERCISES.md` - Extensions, error messages

**Tests**: 29+ passing
**Exercises**: 10 problems + challenges (subtyping, holes, inference)

**Key Insight**: Bidirectional typing minimizes annotations while maintaining decidability

### Chapter 20: Denotational Semantics ✓

**Features**:
- Domain theory (CPOs)
- Fixed point semantics
- Denotation function [[·]]
- Least fixed point (Kleene)
- Continuity and approximation

**Key Files**:
- `src/Domain.hs` - Semantic domains
- `src/Denotation.hs` - [[·]] function
- `exercises/EXERCISES.md` - Adequacy, full abstraction

**Tests**: 28+ passing
**Exercises**: 10 problems + challenges (state, continuations)

**Key Insight**: Denotational semantics gives mathematical meaning to programs as fixed points

## Exercises

### Chapter 1: Fully Implemented ✓

36 exercise tests covering:
- Church boolean operations (AND, OR, XOR)
- Church numeral arithmetic (predecessor, subtraction, equality)
- Fixed-point combinators (Y/Z, factorial, fibonacci)
- SKI combinators
- Church-encoded list operations (map, filter, fold)

See `chapter-01-untyped-lambda/exercises/` for complete solutions.

### Chapters 2-16: Documented

Each chapter includes detailed `exercises/EXERCISES.md` with:
- Problem descriptions
- Type signatures and formal specifications
- Hints and learning objectives
- References to relevant papers

Chapters 6-8 additionally include complete `exercises/Solutions.hs` implementations:
- **Chapter 6**: Type operators, functors, monads in F-omega
- **Chapter 7**: Dependent functions, Church encodings with Pi types
- **Chapter 8**: Equality proofs, vector operations, theorem proving

**Total**: ~130+ exercise problems across all chapters

See `EXERCISES_SUMMARY.md` for complete overview.

## Documentation

Each chapter includes:
- **README.md** - Theory, formal semantics, typing rules, references
- **EXERCISES.md** - Progressive exercise problems
- **Comprehensive comments** in source code
- **References** to foundational papers

### Self-Study Learning Materials

**All 20 chapters now include comprehensive self-study materials** designed for students to learn independently:

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

- **FAQ.md** - Frequently asked questions covering:
  - Conceptual questions and intuitions
  - Technical details and edge cases
  - Common confusions and clarifications
  - Troubleshooting tips

**Total Learning Materials**: Over 2MB of educational content across all 20 chapters, designed to make the course immediately accessible to independent learners.

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
5. **Time estimate**: 8-20 hours per chapter (160-400 hours total for all 20 chapters)

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
├── chapter-08a-dependent-types-toy/
│   ├── src/                          # ✓ Toy dependent types (baseline)
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ Tests for toy checker
│   └── README.md                     # ✓ Intro & limitations
├── chapter-08b-dependent-types-core/
│   ├── src/                          # ✓ Bidirectional core + definitional equality
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ Core checker tests
│   └── README.md                     # ✓ Sound core rules
├── chapter-08c-dependent-types-eliminators/
│   ├── src/                          # ✓ Sound eliminators (Nat/Bool/Unit/Empty/J)
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ Eliminator typing tests
│   └── README.md                     # ✓ Eliminator rules
├── chapter-08d-dependent-types-patterns/
│   ├── src/                          # ✓ Typed patterns (non-dependent)
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ Pattern typing tests
│   └── README.md                     # ✓ Pattern typing & limits
├── chapter-08e-dependent-types-full/
│   ├── src/                          # ✓ NBE + universe discipline
│   ├── exercises/                    # ✓ Complete solutions
│   ├── test/                         # ✓ Full checker tests
│   └── README.md                     # ✓ Full dependent types (notes on positivity)
├── chapter-09-subtyping/
│   ├── src/                          # ✓ Subtyping, join/meet, records
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 74 tests
│   └── README.md                     # ✓ Subtyping theory, variance
├── chapter-10-linear-types/
│   ├── src/                          # ✓ Multiplicities, usage tracking
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 45 tests
│   └── README.md                     # ✓ Linear types, session types
├── chapter-11-refinement-types/
│   ├── src/                          # ✓ Refinements, predicates
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 82 tests
│   └── README.md                     # ✓ Refinement types, predicate validity
├── chapter-12-effect-systems/
│   ├── src/                          # ✓ Effect annotations, inference
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 40+ tests
│   └── README.md                     # ✓ Effect tracking, algebraic effects
├── chapter-13-gradual-typing/
│   ├── src/                          # ✓ Casts, blame tracking
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 35+ tests
│   └── README.md                     # ✓ Gradual guarantee, consistency
├── chapter-14-row-types/
│   ├── src/                          # ✓ Row polymorphism
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 45+ tests
│   └── README.md                     # ✓ Extensible records, variants
├── chapter-15-recursive-types/
│   ├── src/                          # ✓ Iso/equi-recursive
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 40+ tests
│   └── README.md                     # ✓ Mu types, fold/unfold
├── chapter-16-hott/
│   ├── src/                          # ✓ Paths, HITs
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 35+ tests
│   └── README.md                     # ✓ Univalence, homotopy theory
├── chapter-17-abstract-machines/
│   ├── src/                          # ✓ CEK, SECD, Krivine
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 35+ tests
│   └── README.md                     # ✓ Machine semantics
├── chapter-18-normalization-by-evaluation/
│   ├── src/                          # ✓ NbE, semantic domain
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 42+ tests
│   └── README.md                     # ✓ Normalization theory
├── chapter-19-bidirectional-typing/
│   ├── src/                          # ✓ Infer/check modes
│   ├── exercises/                    # ✓ Complete exercises
│   ├── test/                         # ✓ 29+ tests
│   └── README.md                     # ✓ Bidirectional typing
└── chapter-20-denotational-semantics/
    ├── src/                          # ✓ Domains, denotation
    ├── exercises/                    # ✓ Complete exercises
    ├── test/                         # ✓ 28+ tests
    └── README.md                     # ✓ Domain theory
```

## Contributing

This is an educational resource. Potential contributions:
- Additional exercise implementations
- More examples and test cases
- Improved documentation and explanations
- Agda/Coq formalizations of metatheory
- Additional chapters (abstract machines, NbE, denotational semantics)
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

**Status**: ✓ ALL 20 CHAPTERS COMPLETE | 700+ tests passing | ~160+ exercises documented | **Complete self-study materials!**

**Journey**: Untyped λ → STLC → ADTs → Hindley-Milner → System F → F-omega → Dependent Types → Full Dependent Types → Subtyping → Linear Types → Refinement Types → Effect Systems → Gradual Typing → Row Types → Recursive Types → HoTT → Abstract Machines → NbE → Bidirectional Typing → Denotational Semantics

**Achievement**: Complete implementation from first principles to a foundation for mathematics and verified programming - from lambda calculus to denotational semantics!

**New in 2025**: Full 20-chapter sequence including Abstract Machines, Normalization by Evaluation, Bidirectional Type Checking, and Denotational Semantics. All references include Google Scholar links.

Last Updated: 2025-12-21
