# Study Guide: Learning Paths Through Type Systems

This guide helps you navigate the course materials based on your background, goals, and available time.

## Table of Contents

1. [Quick Navigation](#quick-navigation)
2. [Learning Paths](#learning-paths)
3. [By Time Available](#by-time-available)
4. [By Learning Goal](#by-learning-goal)
5. [Chapter Dependencies](#chapter-dependencies)
6. [Week-by-Week Study Plan](#week-by-week-study-plan)
7. [Connection Map](#connection-map)

## Quick Navigation

### By Background

**I'm a complete beginner to PL theory:**
1. Start with [Chapter 0: Prerequisites](CHAPTER_0_PREREQUISITES.md)
2. Read [GLOSSARY.md](GLOSSARY.md) for reference
3. Begin with [Chapter 1: Untyped Lambda Calculus](chapter-01-untyped-lambda/)
4. Progress sequentially through chapters

**I know lambda calculus but not type systems:**
→ Skip to [Chapter 2: Simply Typed Lambda Calculus](chapter-02-simply-typed-lambda/)

**I'm familiar with basic type systems:**
→ Jump to [Chapter 4: Hindley-Milner Type Inference](chapter-04-hindley-milner/)

**I want to learn about dependent types:**
→ Review [Chapter 5: System F](chapter-05-system-f/) for context
→ Then proceed to [Chapter 7: Dependent Types](chapter-07-dependent-types/)

### By Learning Goal

**"I want to understand lambda calculus"**
→ [Chapter 1: Untyped Lambda Calculus](chapter-01-untyped-lambda/)

**"I want to learn type checking"**
→ [Chapter 2: Simply Typed Lambda Calculus](chapter-02-simply-typed-lambda/)

**"I want to understand algebraic data types"**
→ [Chapter 3: STLC with ADTs](chapter-03-stlc-adt/)

**"I want to learn type inference"**
→ [Chapter 4: Hindley-Milner Type Inference](chapter-04-hindley-milner/)

**"I want to understand polymorphism"**
→ [Chapter 5: System F](chapter-05-system-f/)

**"I want to learn about higher-kinded types"**
→ [Chapter 6: System F-omega](chapter-06-system-f-omega/)

**"I want to learn dependent types"**
→ [Chapter 7](chapter-07-dependent-types/) then the staged series:
[08a](chapter-08a-dependent-types-toy/),
[08b](chapter-08b-dependent-types-core/),
[08c](chapter-08c-dependent-types-eliminators/),
[08d](chapter-08d-dependent-types-patterns/),
[08e](chapter-08e-dependent-types-full/)

**"I want to build a proof assistant"**
→ Complete all chapters, focusing on [Chapter 08e](chapter-08e-dependent-types-full/)

## Learning Paths

### Path 1: Complete Beginner Track

**Goal:** Master type systems from scratch
**Time:** 6-12 months (casual pace)
**Prerequisites:** Basic programming in any language

```
Chapter 0: Prerequisites (1 week)
    ↓
Chapter 1: Untyped Lambda Calculus (2-3 weeks)
    ↓
Chapter 2: Simply Typed Lambda Calculus (2 weeks)
    ↓
Chapter 3: STLC with ADTs (2 weeks)
    ↓
Chapter 4: Hindley-Milner (3 weeks)
    ↓
Chapter 5: System F (3 weeks)
    ↓
Chapter 6: System F-omega (3 weeks)
    ↓
Chapter 7: Dependent Types (3 weeks)
    ↓
Chapter 8: Full Dependent Types (4 weeks)
```

**Weekly Commitment:** 5-10 hours

### Path 2: Type Systems Fast Track

**Goal:** Learn core type system concepts quickly
**Time:** 2 months
**Prerequisites:** Functional programming experience

```
Chapter 1: Lambda Calculus (1 week)
    ↓
Chapter 2: STLC (1 week)
    ↓
Chapter 4: Hindley-Milner (2 weeks)
    ↓
Chapter 5: System F (2 weeks)
    ↓
Chapter 8: Full Dependent Types (2 weeks)
```

**Weekly Commitment:** 10-15 hours
**Note:** Skip chapters 3, 6, 7 initially; return later for depth

### Path 3: Dependent Types Focus

**Goal:** Understand dependent type theory for proof assistants
**Time:** 6-8 weeks
**Prerequisites:** Comfortable with type systems

```
Review: Chapter 2 (if needed) (1 week)
    ↓
Chapter 5: System F (1 week)
    ↓
Chapter 6: System F-omega (2 weeks)
    ↓
Chapter 7: Dependent Types (2 weeks)
    ↓
Chapter 8: Full Dependent Types (3 weeks)
```

**Weekly Commitment:** 15-20 hours

### Path 4: Practical Type Systems

**Goal:** Learn type systems useful in industry
**Time:** 6 weeks
**Prerequisites:** Professional programming experience

```
Chapter 2: STLC (1 week)
    ↓
Chapter 3: ADTs (1 week)
    ↓
Chapter 4: Hindley-Milner (2 weeks)
    ↓
Chapter 5: System F (2 weeks)
```

**Focus:** How these appear in TypeScript, Rust, Haskell, OCaml
**Weekly Commitment:** 10 hours

### Path 5: Research Preparation

**Goal:** Prepare for PL research
**Time:** 3-4 months
**Prerequisites:** Strong CS background

```
All chapters 1-8 sequentially

Plus:
- All exercises completed
- All referenced papers read
- Implementation experiments
- Original extensions
```

**Weekly Commitment:** 20-25 hours

## By Time Available

### One Weekend (12-16 hours)

**Crash Course:**
- Read Chapter 1 README (2 hours)
- Implement basic evaluator (3 hours)
- Read Chapter 2 README (2 hours)
- Implement simple type checker (4 hours)
- Explore examples and tests (2 hours)

**Outcome:** Solid grasp of lambda calculus and type checking basics

### One Week (40 hours)

**Intensive Week:**
- Monday: Chapter 1 (8 hours)
- Tuesday: Chapter 2 (8 hours)
- Wednesday: Chapter 3 (8 hours)
- Thursday: Chapter 4 (8 hours)
- Friday: Chapter 5 (8 hours)

**Outcome:** Working knowledge of major type systems

### One Month (80-100 hours)

**Structured Month:**
- Week 1: Chapters 1-2
- Week 2: Chapters 3-4
- Week 3: Chapters 5-6
- Week 4: Chapters 7-8

**Outcome:** Deep understanding of all material

### One Semester (14 weeks)

**Academic Semester:**
- Weeks 1-2: Chapter 1 (with all exercises)
- Weeks 3-4: Chapter 2 (with all exercises)
- Weeks 5-6: Chapter 3 (with all exercises)
- Weeks 7-8: Chapter 4 (with all exercises)
- Weeks 9-10: Chapter 5 (with all exercises)
- Week 11: Chapter 6
- Week 12: Chapter 7
- Weeks 13-14: Chapter 8 + final project

**Outcome:** Mastery with ability to extend and research

## Chapter Dependencies

### Dependency Graph

```
Chapter 1 (Untyped)
    │
    └─→ Chapter 2 (STLC)
            │
            ├─→ Chapter 3 (ADTs)
            │       │
            │       └─→ (Optional for Ch4)
            │
            └─→ Chapter 4 (HM)
                    │
                    └─→ Chapter 5 (System F)
                            │
                            ├─→ Chapter 6 (F-omega)
                            │       │
                            │       └─→ Chapter 7 (Dep Types)
                            │               │
                            └───────────────┴─→ Chapter 8 (Full DT)
```

### Minimal Paths

**Path to Type Inference:**
Ch1 → Ch2 → Ch4

**Path to Polymorphism:**
Ch1 → Ch2 → Ch5

**Path to Dependent Types:**
Ch1 → Ch2 → Ch5 → Ch7 → Ch8

**Path to Higher-Kinded Types:**
Ch1 → Ch2 → Ch5 → Ch6

## Week-by-Week Study Plan

### Standard 12-Week Semester Plan

#### Week 1: Foundations
- **Monday:** Read Chapter 0, set up environment
- **Wednesday:** Chapter 1 README sections 1-4
- **Friday:** Chapter 1 README sections 5-8
- **Weekend:** Implement examples, start exercises

#### Week 2: Lambda Calculus Deep Dive
- **Monday-Wednesday:** Complete Chapter 1 exercises 1-5
- **Thursday-Friday:** Chapter 1 exercises 6-10
- **Weekend:** Review, compare with solutions

#### Week 3: Enter Type Systems
- **Monday:** Chapter 2 README introduction
- **Wednesday:** Chapter 2 typing rules and metatheory
- **Friday:** Implement type checker
- **Weekend:** Chapter 2 exercises 1-3

#### Week 4: Type Safety
- **Monday-Tuesday:** Chapter 2 exercises 4-6
- **Wednesday-Thursday:** Progress and preservation proofs
- **Friday:** Review and consolidation
- **Weekend:** Prepare for ADTs

#### Week 5: Algebraic Data Types
- **Monday:** Chapter 3 README, product types
- **Wednesday:** Sum types and pattern matching
- **Friday:** Implement pattern matching
- **Weekend:** Chapter 3 exercises 1-4

#### Week 6: Advanced ADTs
- **Monday-Wednesday:** Chapter 3 exercises 5-8
- **Thursday-Friday:** Exhaustiveness checking
- **Weekend:** Build small language with ADTs

#### Week 7: Type Inference Introduction
- **Monday:** Chapter 4 README, unification
- **Wednesday:** Algorithm W
- **Friday:** Implement unifier
- **Weekend:** Study let-polymorphism

#### Week 8: Hindley-Milner Mastery
- **Monday-Tuesday:** Complete Algorithm W implementation
- **Wednesday-Thursday:** Chapter 4 exercises
- **Friday:** Principal types
- **Weekend:** Mini inference project

#### Week 9: Parametric Polymorphism
- **Monday:** Chapter 5 README, System F motivation
- **Wednesday:** Type abstraction and application
- **Friday:** Implement bidirectional type checker
- **Weekend:** Church encodings

#### Week 10: System F Deep Dive
- **Monday-Tuesday:** Parametricity
- **Wednesday-Thursday:** Chapter 5 exercises
- **Friday:** Free theorems
- **Weekend:** Review chapters 1-5

#### Week 11: Higher-Kinded Types
- **Monday:** Chapter 6 README, kinds
- **Wednesday:** Type operators
- **Friday:** Chapter 6 implementation
- **Weekend:** Chapter 6 exercises

#### Week 12: Dependent Types
- **Monday-Tuesday:** Chapter 7 README and Pi types
- **Wednesday-Thursday:** Sigma types, implementation
- **Friday:** Chapter 7 exercises
- **Weekend:** Begin Chapter 8

#### Week 13: Universe Hierarchy
- **Monday:** Chapter 8 README, universes
- **Wednesday:** Equality types and J eliminator
- **Friday:** Inductive families
- **Weekend:** Chapter 8 exercises 1-4

#### Week 14: Full Dependent Types & Review
- **Monday-Tuesday:** Chapter 8 exercises 5-8
- **Wednesday:** Final project planning
- **Thursday-Friday:** Implementation
- **Weekend:** Presentation preparation

## Connection Map

### Connections Between Chapters

**Chapter 1 → Chapter 2:**
- **Adds:** Types, type checker
- **Keeps:** Lambda abstraction, application
- **Changes:** Not all terms type check
- **Connection:** Types restrict λ-calculus to prevent errors

**Chapter 2 → Chapter 3:**
- **Adds:** Products, sums, patterns
- **Keeps:** Functions, type checking
- **Changes:** More expressive types
- **Connection:** ADTs make data structures explicit

**Chapter 2/3 → Chapter 4:**
- **Adds:** Type inference, let-polymorphism
- **Removes:** Need for type annotations
- **Changes:** Automatic type derivation
- **Connection:** Inference makes types ergonomic

**Chapter 4 → Chapter 5:**
- **Adds:** Explicit polymorphism, type abstraction
- **Changes:** More expressive than HM
- **Trade-off:** Expressiveness vs. inference
- **Connection:** System F is HM without restrictions

**Chapter 5 → Chapter 6:**
- **Adds:** Kinds, type operators
- **Changes:** Types become first-class
- **Connection:** Type-level computation

**Chapter 5 → Chapter 7:**
- **Adds:** Dependent types, unified syntax
- **Changes:** Types depend on values
- **Connection:** Curry-Howard becomes powerful

**Chapter 7 → Chapter 8:**
- **Adds:** Universe hierarchy, equality types
- **Fixes:** Type-in-Type inconsistency
- **Changes:** Full theorem proving capability
- **Connection:** From programs to proofs

### Real-World Connections

**Chapter 1** → Understanding interpreters, metaprogramming
**Chapter 2** → Java, C++, Go, TypeScript basics
**Chapter 3** → Rust enums, Haskell data types, TypeScript unions
**Chapter 4** → Rust type inference, OCaml, F#, Haskell
**Chapter 5** → Java generics, C++ templates, Haskell (under hood)
**Chapter 6** → Haskell type families, Scala higher-kinded types
**Chapter 7-8** → Agda, Coq, Idris, Lean, verified programming

## Study Tips by Chapter

### Chapter 1: Untyped Lambda Calculus
- **Focus:** Understanding reduction strategies
- **Key Exercise:** Implement Church numerals
- **Common Pitfall:** Name capture in substitution
- **Time Saver:** Master substitution first

### Chapter 2: Simply Typed Lambda Calculus
- **Focus:** Type checking algorithm
- **Key Exercise:** Progress and preservation proofs
- **Common Pitfall:** Confusing typing and evaluation
- **Time Saver:** Understand typing rules thoroughly

### Chapter 3: STLC with ADTs
- **Focus:** Pattern matching compilation
- **Key Exercise:** Exhaustiveness checking
- **Common Pitfall:** Missing pattern cases
- **Time Saver:** Draw pattern match trees

### Chapter 4: Hindley-Milner
- **Focus:** Unification algorithm
- **Key Exercise:** Implementing occurs check
- **Common Pitfall:** Let vs lambda polymorphism
- **Time Saver:** Trace unification by hand first

### Chapter 5: System F
- **Focus:** Bidirectional type checking
- **Key Exercise:** Church encodings at type level
- **Common Pitfall:** Forgetting type applications
- **Time Saver:** Understand parametricity intuitively

### Chapter 6: System F-omega
- **Focus:** Kinding judgment
- **Key Exercise:** Higher-kinded type operators
- **Common Pitfall:** Confusing types and kinds
- **Time Saver:** Think "types of types"

### Chapter 7: Dependent Types
- **Focus:** Normalization-based equality
- **Key Exercise:** Dependent functions
- **Common Pitfall:** Type-in-Type paradox (acknowledged)
- **Time Saver:** Focus on intuition over formalism

### Chapter 8: Full Dependent Types
- **Focus:** Universe hierarchy, equality proofs
- **Key Exercise:** Implementing J eliminator
- **Common Pitfall:** Complex equality proofs
- **Time Saver:** Study equality examples carefully

## Progress Tracking

### Chapter Completion Checklist

For each chapter, check off when complete:

**Chapter 1:**
- [ ] Read README
- [ ] Understand all examples
- [ ] Run all tests
- [ ] Complete exercises 1-5
- [ ] Complete exercises 6-10
- [ ] Can explain Church encodings

**Chapter 2:**
- [ ] Read README
- [ ] Understand typing rules
- [ ] Implement type checker
- [ ] Complete exercises 1-3
- [ ] Complete exercises 4-6
- [ ] Understand progress and preservation

**[Continue for all chapters...]**

### Mastery Indicators

You've mastered a chapter when you can:
1. ✅ Explain key concepts to someone else
2. ✅ Implement core algorithms from scratch
3. ✅ Complete all exercises
4. ✅ Modify examples to explore edge cases
5. ✅ Connect to real-world applications

## Getting Unstuck

### When to Ask for Help

**Try for 30 minutes first:**
- Re-read relevant sections
- Check GLOSSARY.md for terms
- Review previous chapters
- Add debug output
- Simplify the problem

**Still stuck? Time to:**
- Check GitHub Issues/Discussions
- Ask on Stack Overflow (tag: `[haskell]` `[type-systems]`)
- Review solution code (if available)
- Skip and return later

### Common Sticking Points

**"I don't understand the notation"**
→ Review [Chapter 0: Reading Formal Notation](CHAPTER_0_PREREQUISITES.md#reading-formal-notation)
→ Check [GLOSSARY.md](GLOSSARY.md)

**"The code is too abstract"**
→ Add concrete examples
→ Add print/trace statements
→ Draw diagrams

**"I can't solve the exercises"**
→ Start with easier problems
→ Look at solution structure (not implementation)
→ Break into smaller sub-problems

**"It's taking too long"**
→ This is normal! Type theory is dense
→ Take breaks
→ Focus on understanding over speed

## Next Steps

Choose your learning path from above and dive in!

**Quick Links:**
- [Main README](README.md)
- [Chapter 0: Prerequisites](CHAPTER_0_PREREQUISITES.md)
- [Glossary](GLOSSARY.md)
- [Chapter 1: Start Here](chapter-01-untyped-lambda/README.md)

---

**Remember:** The journey from untyped lambda calculus to dependent types is challenging but deeply rewarding. Take your time, ask questions, and enjoy discovering the beautiful world of type systems!
