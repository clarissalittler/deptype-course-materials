# Chapter 3: STLC with ADTs - Quick Start

## TL;DR

Add **Algebraic Data Types** (products, sums, unit) to STLC. Now you can model real data structures! This is how Rust enums, TypeScript unions, and Haskell data types work.

**Time**: 1-2 weeks | **Prerequisites**: Chapter 2

## What You'll Build

-Pattern matching on sum types
- Product types (pairs/tuples)
- Optional values and error handling patterns
- Foundation for real programming languages

**Outcome**: Model complex data with type safety!

## 5-Minute Setup

```bash
cd chapter-03-stlc-adt
stack build
stack exec stlc-adt-repl
```

### Quick Win (3 minutes)

```
λ> pair true zero
  : Bool * Nat
  (true, 0)

λ> fst (pair true zero)
  : Bool
  true

λ> inl true : Bool + Nat
  : Bool + Nat
  inl true

λ> case (inl true : Bool + Nat) of
     inl x => x
   | inr y => false
  : Bool
  true
```

**Achievement**: Data structures with type safety! 📦

## Next Steps

1. **Tutorial**: Read `TUTORIAL.md` (45-60 min)
2. **Practice**: Try `REPL_GUIDE.md` exercises
3. **Exercises**: Complete `exercises/EXERCISES.md` 1-4
4. **Test**: Take `QUIZ.md`

## When to Skip

**Skip if**: Solid on ADTs from other languages
**Don't skip if**: First time with sum/product types

## Quick Reference

```
# Product Types (Pairs)
pair <t1> <t2>      # Create pair
fst <pair>          # First element
snd <pair>          # Second element
T1 * T2             # Pair type

# Sum Types (Either)
inl <t> : T1 + T2   # Left injection
inr <t> : T1 + T2   # Right injection
case <t> of         # Pattern match
  inl x => ...
| inr y => ...

# Unit Type
unit : Unit         # Single value
```

## Success Criteria

Ready for Chapter 4 when you:
- [ ] Understand products vs sums
- [ ] Can pattern match
- [ ] Model optionals and errors
- [ ] Complete exercises 1-5

**Time**: 8-14 hours | **Help**: `COMMON_MISTAKES.md`, `REPL_GUIDE.md`

Welcome to real data modeling! 🎨
