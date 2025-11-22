# Chapter 7: Dependent Types - Quick Start

## TL;DR

**Types that depend on VALUES!** Π(n:Nat). Vec Nat n means "function that takes n and returns vector of length n". Terms and types UNIFIED. This is the foundation for Agda, Coq, Idris, Lean.

**Time**: 3-4 weeks | **Prerequisites**: Chapters 2 and 5

## What You'll Build

- Pi types (Π) - dependent functions
- Sigma types (Σ) - dependent pairs
- Type-level computation
- Curry-Howard correspondence

**Outcome**: Types that express precise properties!

## 5-Minute Setup

```bash
cd chapter-07-dependent-types
stack build
stack exec dependent-types-repl
```

### Quick Win (3 minutes)

```
λΠ> Π(n:Nat). Vec Nat n
  : Type
  (function type that depends on n!)

λΠ> \(A:Type). \(x:A). x
  : Π(A:Type). A → A
  (polymorphism as dependent type!)

λΠ> Σ(n:Nat). Vec Nat n
  : Type
  (pair of number and vector of that length!)
```

**Achievement**: Types depending on values! 🎓

## Key Insight

```
Non-dependent:  Nat → Nat
Dependent:      Π(n:Nat). Vec Nat n
                            ↑ uses n!
```

## Next Steps

1. **Must Read**: `FAQ.md` - dependent types explained
2. **Tutorial**: `TUTORIAL.md` (2 hours) - Pi/Sigma deep dive
3. **Practice**: `REPL_GUIDE.md`
4. **Exercises**: `exercises/EXERCISES.md`
5. **Test**: `QUIZ.md`

## Quick Reference

```
# Pi Types (Dependent Functions)
Π(x:A). B              # Dependent function
A -> B                 # Non-dependent (sugar)

# Sigma Types (Dependent Pairs)
Σ(x:A). B              # Dependent pair

# Unified Syntax
Type                   # Type of types
Terms = Types          # Same language!
```

## Success Criteria

- [ ] Understand Π vs →
- [ ] Grasp Σ types
- [ ] Write type-level functions
- [ ] Complete exercises 1-4

**Time**: 16-24 hours | **Help**: `FAQ.md` (MUST READ!), `REPL_GUIDE.md`
