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

## Test Structure

Tests are in `test/Spec.hs` and `test/ExerciseSpec.hs` (where applicable). Run with `stack test`. Total: 401 tests across all chapters.

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
