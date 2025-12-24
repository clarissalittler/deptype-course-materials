# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a comprehensive course on implementing type systems in Haskell, progressing from untyped lambda calculus through System F to full dependent types. Each chapter is a standalone Haskell project with its own Stack configuration.

## Build Commands

Each chapter is built independently. Navigate to a chapter directory first:

```bash
cd chapter-01-untyped-lambda  # or any chapter-XX-* directory

# Build the project
stack build

# Run tests
stack test

# Run the REPL (interactive)
stack run <chapter-name>-repl
# Examples: stack run untyped-lambda-repl, stack run hindley-milner-repl, etc.

# Build with file watching
stack build --file-watch
```

To build/test all chapters:
```bash
for dir in chapter-*/; do (cd "$dir" && stack build && stack test); done
```

## Architecture

### Consistent Module Structure Across Chapters

Each chapter follows the same pattern:
- `src/Syntax.hs` - AST definitions (Term, Type, Pattern data types)
- `src/Eval.hs` - Evaluation/reduction semantics
- `src/Parser.hs` - Megaparsec-based parser for the language
- `src/Pretty.hs` - Pretty printer for terms and types
- `src/TypeCheck.hs` - Type checker (Chapters 2+)
- `src/Infer.hs` - Type inference (Chapter 4 only, Algorithm W)
- `exercises/Solutions.hs` - Complete exercise solutions
- `app/Main.hs` + `app/REPL.hs` - Interactive REPL executable

### Type System Progression

The chapters build upon each other:

1. **Chapter 1 (Untyped Lambda)**: Core lambda calculus - `Var | Lam Var Term | App Term Term`
2. **Chapter 2 (Simply Typed)**: Adds `Type` with `TyBool | TyNat | TyArr Type Type`
3. **Chapter 3 (ADTs)**: Adds products, sums, records, variants, lists, pattern matching
4. **Chapter 4 (Hindley-Milner)**: Adds `TypeScheme` with ∀ quantification, unification in `Infer.hs`
5. **Chapter 5 (System F)**: Explicit polymorphism - `TyAbs`/`TyApp` and `TyForall`
6. **Chapter 6 (System F-ω)**: Adds `Kind` system and type-level lambdas (`TyLam`/`TyTApp`)
7. **Chapter 7 (Dependent Types)**: Unified Term for types and values, `Pi`/`Sigma` types, `Type:Type`
8. **Chapter 8 (Full Dependent)**: Universe hierarchy (`Universe Level`), equality types (`Eq`/`Refl`/`J`), inductive families
9. **Chapter 9 (Subtyping)**: `TyTop`/`TyBot`, `isSubtype`, join/meet, record width/depth subtyping
10. **Chapter 10 (Linear Types)**: Multiplicities (`One`/`Many`), `TyFun Mult`, usage tracking, bang types
11. **Chapter 11 (Refinement Types)**: Predicate refinements `{x:T | p}`, SMT-style validity checking
12. **Chapter 12 (Effect Systems)**: Effect rows, handlers, perform/handle
13. **Chapter 13 (Gradual Typing)**: Dynamic type `?`, consistency, casts
14. **Chapter 14 (Row Types)**: Extensible records, row variables, variants
15. **Chapter 15 (Recursive Types)**: `μα.T`, fold/unfold, iso-recursive
16. **Chapter 16 (HoTT)**: Identity types, J eliminator, paths, transport
17. **Chapter 17 (Abstract Machines)**: CEK, SECD, Krivine machines
18. **Chapter 18 (NbE)**: Normalization by evaluation, semantic domains
19. **Chapter 19 (Bidirectional)**: Inference/checking modes, annotations
20. **Chapter 20 (Denotational)**: Domain theory, fixed points, CPOs
21. **Chapter 21 (Module Systems)**: Structures, signatures, functors, sealing
22. **Chapter 22 (Constraint Inference)**: Two-phase inference, constraint generation/solving

### Key Implementation Patterns

- **Capture-avoiding substitution**: All chapters use `freshVar`/`freshName` to avoid variable capture
- **Alpha equivalence**: `alphaEq` function compares terms up to bound variable renaming
- **Bidirectional type checking**: Used in System F and dependent type chapters
- **Normalization**: Dependent type chapters compare types by normalizing to weak-head normal form

## Technology Stack

- GHC 9.6.6 with Stack (resolver lts-22.28)
- Parser: Megaparsec
- Testing: Hspec
- Core libraries: containers, mtl, text
- Agda 2.6.x (for formal proofs)

## Agda Formalizations

Select chapters include Agda formalizations with machine-checked proofs. These are in the `agda/` subdirectory of each chapter.

### Building Agda Files

```bash
cd chapter-01-untyped-lambda/agda  # or any chapter with agda/

# Type-check all modules
agda All.agda

# Type-check individual module
agda Syntax.agda
```

### Agda Module Structure

Each Agda formalization follows this pattern:
- `Syntax.agda` - AST definition (using de Bruijn indices)
- `Evaluation.agda` - Small-step operational semantics
- `Progress.agda` - Progress theorem (typed chapters)
- `Preservation.agda` - Preservation theorem (typed chapters)
- `Properties.agda` - Additional properties (determinism, etc.)
- `All.agda` - Re-exports all modules

### Chapters with Agda Formalizations

| Chapter | Key Proofs |
|---------|------------|
| 1. Untyped Lambda | Determinism, Ω diverges |
| 2. Simply Typed | Progress, Preservation, Type Safety |
| 3. STLC with ADTs | Progress, Determinism (products, sums) |
| 5. System F | Polymorphic types, type abstraction/application |
| 7. Dependent Types | Pi/Sigma types, well-scoped terms, Type:Type |

### Intrinsic vs Extrinsic Typing

The Haskell implementations use **extrinsic typing**: terms are defined separately, then a type checker validates them. The Agda formalizations use different approaches:

- **Chapters 1-3, 5**: Use **intrinsic typing** where terms are indexed by their types. Ill-typed terms cannot be constructed, making preservation trivial.
- **Chapter 7**: Uses **extrinsic typing** with well-scoped terms. This matches how real dependent type checkers work and allows stating properties about type checking.

## Test Structure

Tests are in `test/Spec.hs` and `test/ExerciseSpec.hs` (where applicable). Run with `stack test`. Total: 800+ tests across all 22 chapters.

## Completed Expansions

### Chapter 9: Subtyping ✓
- **Focus**: Subtype relations, covariance/contravariance, width/depth subtyping
- **Key types**: `isSubtype`, `TyTop`/`TyBot`, join/meet operations
- **Theory**: Record subtyping, function variance
- **Tests**: 74 passing

### Chapter 10: Linear Types ✓
- **Focus**: Resources used exactly once, ownership tracking
- **Key types**: Linear arrow `-o`, multiplicities (1/ω), bang types `!`
- **Theory**: Linear logic, usage tracking
- **Tests**: 45 passing

## Future Expansion (Planned)

### Chapter 11: Refinement Types (TODO)
- **Focus**: Types with logical predicates, compile-time verification
- **Key types**: `{x: τ | φ(x)}` where φ is a predicate
- **Theory**: SMT-based type checking, liquid types
- **Real-world**: Liquid Haskell, F*, Dafny, Ada SPARK

### Chapter Structure Template
Each new chapter should include:
```
chapter-XX-name/
├── src/
│   ├── Syntax.hs      # AST with new type constructs
│   ├── TypeCheck.hs   # Subtyping/linearity/refinement checking
│   ├── Eval.hs        # Evaluation (may be unchanged)
│   ├── Parser.hs      # Extended syntax
│   └── Pretty.hs      # Pretty printing
├── agda/              # Optional: Agda formalization
│   ├── Syntax.agda    # De Bruijn indexed terms
│   ├── Evaluation.agda # Small-step semantics
│   ├── Progress.agda  # Progress theorem
│   ├── Preservation.agda # Preservation theorem
│   ├── All.agda       # Re-exports all modules
│   └── README.md      # Formalization guide
├── exercises/
│   ├── EXERCISES.md   # Problem descriptions
│   ├── Solutions.hs   # Reference implementations
│   └── Hints.hs       # Progressive hints
├── test/
│   ├── Spec.hs        # Implementation tests
│   └── ExerciseSpec.hs
├── app/
│   ├── Main.hs
│   └── REPL.hs
├── README.md          # Theory, typing rules, references
├── FAQ.md             # Common questions
├── TUTORIAL.md        # Step-by-step walkthrough
├── LESSON_PLAN.md     # Structured lessons
├── QUIZ.md            # Self-assessment
├── COMMON_MISTAKES.md # Pitfalls and debugging
├── PRACTICE_PROBLEMS.md
├── CHEAT_SHEET.md
├── REPL_GUIDE.md
├── QUICK_START.md
├── package.yaml
└── stack.yaml
```

### Implementation Priority
1. **Chapter 9 (Subtyping)** - Start here, foundational for understanding OOP type systems
2. **Chapter 10 (Linear Types)** - Build on STLC, add linearity tracking
3. **Chapter 11 (Refinement Types)** - Most complex, requires SMT concepts
