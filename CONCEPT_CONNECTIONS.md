# Type Systems Course - Concept Connections Map

## Purpose

This document shows how concepts connect across chapters, helping you understand the big picture and see how ideas build on each other.

## Visual Concept Dependency Graph

```
FOUNDATIONS
│
├─ Lambda Calculus (Ch1)
│   ├─ Variables
│   ├─ Abstraction (λ)
│   ├─ Application
│   ├─ Substitution ────────────┐
│   ├─ Alpha equivalence        │
│   └─ Beta reduction ───────────┼──> Used in ALL later chapters
│                                │
└─ Simply Typed LC (Ch2)         │
    ├─ Type checking             │
    ├─ Typing rules              │
    ├─ Progress & Preservation   │
    └─ Type safety          ────┐│
                                ││
STRUCTURED DATA                 ││
│                               ││
└─ ADTs (Ch3)                   ││
    ├─ Product types            ││
    ├─ Sum types                ││
    ├─ Pattern matching    ─────┼┼──> Used in Ch7-8
    └─ Type constructors   ─────┘│
                                 │
TYPE INFERENCE                   │
│                                │
└─ Hindley-Milner (Ch4)          │
    ├─ Algorithm W               │
    ├─ Unification          ─────┼──> Core technique
    ├─ Substitution (from Ch1) ──┘
    ├─ Let-polymorphism
    └─ Principal types

EXPLICIT POLYMORPHISM
│
├─ System F (Ch5)
│   ├─ Type abstraction (Λα)
│   ├─ Type application [T]
│   ├─ Universal types (∀)
│   ├─ Parametricity
│   └─ Church encodings ───────┐
│                              │
└─ System F-omega (Ch6)        │
    ├─ Kinds (*, *→*)          │
    ├─ Type-level lambda       │
    ├─ Higher-kinded types     │
    └─ Type operators      ────┼──> Generalized in Ch7-8
                               │
DEPENDENT TYPES                │
│                              │
├─ Basic Dependent Types (Ch7) │
│   ├─ Pi types (Π)            │
│   ├─ Sigma types (Σ)         │
│   ├─ Terms = Types           │
│   ├─ Curry-Howard     ───────┼──> Fundamental connection
│   └─ Type-in-Type (unsound)  │
│                              │
└─ Full Dependent Types (Ch8)  │
    ├─ Universe hierarchy      │
    ├─ Propositional equality  │
    ├─ J eliminator            │
    ├─ Inductive families ─────┘
    └─ Complete Curry-Howard
```

## Concept Evolution Table

| Concept | Ch1 | Ch2 | Ch3 | Ch4 | Ch5 | Ch6 | Ch7 | Ch8 |
|---------|-----|-----|-----|-----|-----|-----|-----|-----|
| **Variables** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Functions** | ✓ (λx.t) | ✓ (λx:T.t) | ✓ | ✓ (inferred) | ✓ (/\A) | ✓ | ✓ | ✓ |
| **Types** | ✗ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ (=terms!) | ✓ |
| **Polymorphism** | ✗ | ✗ | ✗ | ✓ (implicit) | ✓ (explicit) | ✓ | ✓ (Π) | ✓ |
| **Type checking** | ✗ | ✓ | ✓ | ✓ (inference!) | ✓ | ✓ | ✓ | ✓ |
| **Data types** | Church | Built-in | ADTs | Inferred | Church | Church | Inductive | Inductive families |
| **Equality** | ✗ | Syntactic | Syntactic | Unification | Syntactic | Syntactic | Definitional | Propositional! |
| **Curry-Howard** | ✗ | Basic | ✓ | ✓ | ✓✓ | ✓✓ | ✓✓✓ | ✓✓✓✓ |

Legend: ✓ = present, ✓✓ = enhanced, ✗ = absent

## Core Techniques Progression

### Substitution

```
Ch1: Term substitution t[x := s]
  → Ch2: Still term substitution (with types)
  → Ch4: TYPE substitution σ[α := τ]  ← NEW!
  → Ch5-8: Both term and type substitution
```

### Evaluation Strategies

```
Ch1: Multiple strategies (normal, CBV, CBN)
  → Ch2-8: Mostly call-by-value
  → Ch7-8: Normalization for type checking
```

### Type Checking

```
Ch2: Simple type checking (algorithm given)
  → Ch3: Type checking with ADTs
  → Ch4: Type INFERENCE (algorithm W)  ← MAJOR CHANGE
  → Ch5: Bidirectional type checking
  → Ch6-8: Dependent type checking (with normalization)
```

## Concept Cross-References

### Where Ideas First Appear

| Concept | First Appearance | Used In |
|---------|-----------------|---------|
| Lambda abstraction | Ch1 | All chapters |
| Substitution | Ch1 | All chapters |
| Type annotations | Ch2 | Ch2-3, Ch5-8 (not Ch4!) |
| Type safety proofs | Ch2 | Ch2-8 |
| Sum types | Ch3 | Ch3, Ch7-8 |
| Product types | Ch3 | Ch3, Ch7-8 (as Σ) |
| Type variables | Ch4 | Ch4-8 |
| Unification | Ch4 | Ch4 (core!), appears in Ch5-8 |
| Universal quantification | Ch4 (∀) | Ch4-8 |
| Explicit type abstraction | Ch5 | Ch5-8 |
| Kinds | Ch6 | Ch6-8 |
| Dependent types | Ch7 | Ch7-8 |
| Universe hierarchy | Ch8 | Ch8 only |
| Propositional equality | Ch8 | Ch8 only |

### Cumulative Complexity

```
Ch1: λ-calculus (3 constructs)
  + Ch2: Types (2 base types, 1 type constructor)
    + Ch3: ADTs (3 new type constructors)
      +/- Ch4: Type inference (removes annotations, adds algorithm)
        + Ch5: Explicit polymorphism (2 new term constructs, ∀)
          + Ch6: Higher-kinded types (kinds, type-level λ)
            + Ch7: Dependent types (Π, Σ, unification)
              + Ch8: Full dependent types (universes, Eq, J, inductive families)
```

## Parallel Tracks

### Track 1: Lambda Calculus → STLC → ADTs
**Focus**: Basic type systems
**Skills**: Type checking, pattern matching
**Prerequisite for**: Track 2 or Track 3

### Track 2: STLC → Hindley-Milner → System F → System F-omega
**Focus**: Polymorphism
**Skills**: Type inference, parametricity, higher-kinded types
**Path**: Practical type systems (ML, Haskell, Scala)

### Track 3: System F → Dependent Types → Full Dependent Types
**Focus**: Verification
**Skills**: Proof construction, theorem proving
**Path**: Proof assistants (Agda, Coq, Lean)

You can follow:
- **Straight through** (recommended for complete understanding)
- **Track 1 → Track 2** (for practical PL work)
- **Track 1 → Track 3** (for verification/proofs)

## Key Turning Points

### Turning Point 1: Chapter 2 (Adding Types)
**What changes**: Programs can be rejected before running
**Why it matters**: Foundation of type safety
**Mental shift**: Not all programs are valid

### Turning Point 2: Chapter 4 (Type Inference)
**What changes**: Types inferred automatically
**Why it matters**: Convenience without sacrificing safety
**Mental shift**: Types as constraints to be solved

### Turning Point 3: Chapter 5 (Explicit Polymorphism)
**What changes**: You control polymorphism
**Why it matters**: More expressive, but verbose
**Mental shift**: Types as first-class entities

### Turning Point 4: Chapter 7 (Dependent Types)
**What changes**: Types can depend on values
**Why it matters**: Precise specifications in types
**Mental shift**: Types and terms unified

### Turning Point 5: Chapter 8 (Consistency & Equality)
**What changes**: System becomes sound, equality provable
**Why it matters**: Foundation for real verification
**Mental shift**: Programs as mathematical proofs

## Conceptual Hierarchy

```
Level 0: Computation
  └─ Lambda calculus (Ch1)

Level 1: Safety
  └─ Types prevent errors (Ch2-3)

Level 2: Convenience
  └─ Type inference (Ch4)

Level 3: Generality
  └─ Polymorphism (Ch4-6)

Level 4: Precision
  └─ Dependent types (Ch7-8)

Level 5: Verification
  └─ Proofs (Ch8)
```

## Prerequisites by Chapter

```
Ch1: None (start here!)
Ch2: Ch1 (or lambda calculus background)
Ch3: Ch2
Ch4: Ch2 (Ch3 helpful but not required)
Ch5: Ch2 OR Ch4 (either path works)
Ch6: Ch5
Ch7: Ch2 AND Ch5 (need both tracks!)
Ch8: Ch7
```

## Recommended Learning Paths

### Path A: Complete Foundation
```
Ch1 → Ch2 → Ch3 → Ch4 → Ch5 → Ch6 → Ch7 → Ch8
Time: 16-24 weeks
Best for: Comprehensive understanding
```

### Path B: Fast Track to Dependent Types
```
Ch1 → Ch2 → Ch5 → Ch7 → Ch8
Time: 10-14 weeks
Best for: Getting to verification quickly
Skip: Ch3 (ADTs), Ch4 (inference), Ch6 (higher-kinded)
```

### Path C: Practical Type Systems
```
Ch1 → Ch2 → Ch3 → Ch4 → Ch5 → (Ch6 optional)
Time: 10-14 weeks
Best for: Understanding ML/Haskell/Scala
Stop at: Ch5 or Ch6 (Ch7-8 optional for interest)
```

### Path D: Proof Assistant Preparation
```
Ch1 → Ch2 → Ch5 → Ch6 → Ch7 → Ch8
Time: 12-18 weeks
Best for: Learning Agda/Coq/Lean
Focus: Ch7-8 (spend most time here)
```

## Frequently Asked Questions

### Q: Can I skip Chapter 1?
**A**: Only if you already know lambda calculus well. It's the foundation for everything.

### Q: Do I need Chapter 3 for Chapter 4?
**A**: No! Ch4 (Hindley-Milner) only needs Ch2. Ch3 teaches ADTs which are orthogonal.

### Q: Can I learn Chapter 7 without Chapters 5-6?
**A**: Technically yes if you have Ch2, but Ch5 (System F) helps understand polymorphism as special case of Π types.

### Q: Should I do all chapters in order?
**A**: If you have time, yes! But paths B-D above are valid alternatives.

### Q: Which chapters are most important?
**A**: Depends on goals:
- **For PL design**: Ch1-5
- **For verification**: Ch1, Ch2, Ch7, Ch8
- **For Haskell**: Ch1-4, optionally Ch5-6
- **For Rust**: Ch1-3, Ch5 concepts
- **For complete understanding**: All!

## Real-World Connections Map

```
Ch1 (λ-calculus)
  ↓
  ├→ Lisp/Scheme (direct implementation)
  ├→ JavaScript functions (closures)
  └→ Python lambdas

Ch2 (STLC)
  ↓
  ├→ Java (pre-generics)
  ├→ C++ (basic typing)
  ├→ Go (simple type system)
  └→ Early TypeScript

Ch3 (ADTs)
  ↓
  ├→ Rust enums (sum types)
  ├→ TypeScript unions (sum types)
  ├→ Haskell data types
  └→ Swift enums with associated values

Ch4 (Hindley-Milner)
  ↓
  ├→ OCaml
  ├→ F#
  ├→ Haskell (mostly)
  └→ Rust (local inference)

Ch5 (System F)
  ↓
  ├→ Java generics
  ├→ C# generics
  ├→ Scala type parameters
  └→ Haskell (under the hood)

Ch6 (F-omega)
  ↓
  ├→ Haskell type families
  ├→ Scala higher-kinded types
  └→ TypeScript advanced types

Ch7-8 (Dependent Types)
  ↓
  ├→ Agda
  ├→ Coq
  ├→ Idris
  └→ Lean 4
```

## Summary: What Each Chapter Adds

| Chapter | Main Addition | Enables |
|---------|--------------|---------|
| 1 | Computation | Understanding execution |
| 2 | Types | Safety guarantees |
| 3 | Data structures | Real programming |
| 4 | Type inference | Convenience |
| 5 | Explicit polymorphism | Expressiveness |
| 6 | Higher-kinded types | Abstraction over type constructors |
| 7 | Dependent types | Precision in specifications |
| 8 | Consistency & equality | Verified programming & proofs |

---

**Use this map** to:
- Understand where concepts come from
- See how chapters connect
- Choose your learning path
- Know when to review earlier material
- Appreciate the progression of ideas

**Remember**: Type systems build incrementally. Each chapter adds ONE major idea to what came before!
