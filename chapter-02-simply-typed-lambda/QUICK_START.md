# Chapter 2: Simply Typed Lambda Calculus - Quick Start

## TL;DR (30 seconds)

Add types to lambda calculus to prevent runtime errors! Every term must have a type, and the type checker rejects ill-typed programs before they run. This is the foundation of type safety in Java, C++, Go, and TypeScript.

**Who**: Students with Chapter 1 background (or lambda calculus familiarity)
**Time**: 1-2 weeks
**Payoff**: Understand type checking, type safety, Progress + Preservation

## What You'll Build

- Type checker that prevents errors at compile-time
- Understanding of type safety guarantees
- Basic type system with functions, booleans, naturals
- Proofs that well-typed programs don't get stuck

**Tangible Outcome**: Write programs that are GUARANTEED not to crash!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-02-simply-typed-lambda
stack build
stack exec simply-typed-lambda-repl
```

### Step 2: Your First Typed Term (1 minute)

```
λ> \x:Nat. x
  : Nat -> Nat
  λx:Nat. x
```

Notice: The type `Nat -> Nat` is displayed first!

### Step 3: Type Checking in Action (1 minute)

```
λ> if true then zero else false
  Type error: Expected Nat but got Bool
```

The type checker caught the error BEFORE running!

### Step 4: Something Useful (1 minute)

```
λ> :let twice = \f:Nat->Nat. \x:Nat. f (f x)
  twice : (Nat -> Nat) -> Nat -> Nat

λ> twice (\x:Nat. succ x) zero
  : Nat
  2
```

You just wrote a higher-order function with type safety!

## Your First Success - Type-Safe Functions (10 minutes)

### 1. Basic Types
```
λ> zero
  : Nat
  0

λ> true
  : Bool
  true

λ> succ zero
  : Nat
  1
```

### 2. Function Types
```
λ> :let id = \x:Nat. x
  id : Nat -> Nat

λ> :type \x:Bool. if x then false else true
  ... : Bool -> Bool
```

### 3. Type Safety
```
λ> :let safe = \x:Nat. succ x
λ> safe zero              ✓ Works
λ> safe true              ✗ Type error!
```

**Achievement Unlocked**: Type systems prevent bugs! 🛡️

## Next Steps

### For Students from Chapter 1
1. Read `TUTORIAL.md` (60 minutes) - builds on lambda calculus
2. Follow `LESSON_PLAN.md` lessons 1-4
3. Compare with Chapter 1 - see what types add
4. Complete first 3 exercises

### For Type System Learners
1. Read `README.md` sections on typing rules (45 minutes)
2. Understand Progress and Preservation
3. Work through all exercises
4. Take `QUIZ.md`

### For Practitioners
1. See `REPL_GUIDE.md` for full examples
2. Implement exercises in `exercises/EXERCISES.md`
3. Read `COMMON_MISTAKES.md` to avoid pitfalls
4. Move to Chapter 3 for ADTs

## When to Skip This Chapter

**Skip if**:
- You're already solid on STLC
- You've completed TAPL chapters 8-9
- You want to jump to type inference (go to Chapter 4)

**Don't skip if**:
- This is your first type system
- You want to understand type safety
- You're new to type checking algorithms

## Quick Reference

```bash
# Build & Run
cd chapter-02-simply-typed-lambda && stack build
stack exec simply-typed-lambda-repl

# REPL Commands
:type <term>        # Show type
:let name = term    # Save definition
:step               # Step through evaluation
:check              # Enable type checking (default)

# Types
Nat                 # Natural numbers
Bool                # Booleans
T1 -> T2            # Function types

# Terms (MUST annotate lambdas!)
\x:Nat. x           # Lambda (type required!)
zero, succ, pred    # Natural number operations
true, false         # Booleans
if b then t else e  # Conditionals
```

## Success Criteria

Ready for Chapter 3 when you can:
- [ ] Write type-correct terms
- [ ] Understand type checking vs type inference
- [ ] Explain Progress and Preservation
- [ ] Debug type errors
- [ ] Complete exercises 1-4

**Time**: 6-12 hours for solid understanding

## Help & Resources

- **Type errors?** Check `COMMON_MISTAKES.md`
- **Examples?** See `REPL_GUIDE.md`
- **Structure?** Follow `LESSON_PLAN.md`
- **Test?** Take `QUIZ.md`

Welcome to type safety! 🎯
