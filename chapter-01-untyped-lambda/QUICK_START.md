# Chapter 1: Untyped Lambda Calculus - Quick Start

## TL;DR (30 seconds)

Lambda calculus is the simplest universal programming language: just variables, functions (λx. body), and function application. This chapter teaches computation from first principles using only these three constructs. In 5 minutes, you'll evaluate your first lambda term!

**Who**: Complete beginners to PL theory
**Time**: 2-3 weeks (or 1 intensive week)
**Payoff**: Foundation for all programming languages

## What You'll Build

- Evaluator for pure lambda calculus
- Understanding of Church encodings (data from nothing but functions!)
- Three different evaluation strategies
- Grasp of computation without built-in data types

**Tangible Outcome**: Run a factorial function written entirely in lambda calculus!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-01-untyped-lambda
stack build
stack exec untyped-lambda-repl
```

You should see:
```
Welcome to the Untyped Lambda Calculus REPL!
λ>
```

### Step 2: Your First Lambda Term (1 minute)

```
λ> \x. x
  λx. x
```

Congrats! You just wrote the identity function!

### Step 3: Function Application (1 minute)

```
λ> (\x. x) (\y. y)
  λy. y
```

The first function was applied to the second. They're equal!

### Step 4: Something Useful (1 minute)

```
λ> :let true = \t f. t
λ> :let false = \t f. f
λ> :let if = \b t f. b t f
λ> if true (\x. x) (\y. y y)
  λx. x
```

You just implemented booleans using only functions!

## Your First Success - Church Booleans (10 minutes)

Follow this mini-tutorial to cement your understanding:

### 1. Define Booleans
```
λ> :let true = \t f. t
λ> :let false = \t f. f
```

### 2. Boolean Operations
```
λ> :let and = \p q. p q p
λ> and true false
  λt f. f
```

It worked! `true AND false = false`

### 3. Try More
```
λ> and true true
λ> :let or = \p q. p p q
λ> or true false
λ> or false false
```

**Achievement Unlocked**: You just implemented boolean logic with nothing but functions! 🎉

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - gentle, step-by-step
2. Follow `LESSON_PLAN.md` - structured 8-12 hour course
3. Use `REPL_GUIDE.md` as reference when stuck
4. Try the first 3 exercises in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Work through exercises 1-10 (2-3 hours)
3. Check your answers against `exercises/Solutions.hs`
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all the examples
2. Implement your own encodings
3. Explore different evaluation strategies with `:strategy`
4. Use `:step` to understand reduction step-by-step

## When to Skip This Chapter

**Skip if**:
- You're already comfortable with lambda calculus
- You've worked through significant parts of TAPL Chapter 5
- You just want to learn type systems (start Chapter 2)

**Don't skip if**:
- This is your first time with lambda calculus
- You want deep understanding of computation
- You're new to functional programming concepts

## Quick Reference

```bash
# Build
cd chapter-01-untyped-lambda && stack build

# Run REPL
stack exec untyped-lambda-repl

# Essential REPL Commands
:help               # Show help
:let name = term    # Save a definition
:step               # Step-by-step evaluation
:examples           # See lots of examples
:quit               # Exit

# Lambda Syntax
\x. x               # Identity function
\x y. x             # Const function (ignores y)
(\x. x) (\y. y)     # Application

# Your First Definitions
:let id = \x. x
:let true = \t f. t
:let false = \t f. f
:let zero = \f x. x
```

## Success Criteria

You're ready for Chapter 2 when you can:
- [ ] Write and evaluate lambda terms
- [ ] Explain alpha, beta, eta
- [ ] Implement Church booleans
- [ ] Understand evaluation strategies
- [ ] Complete exercises 1-5

**Minimum**: Understand identity, const, and Church booleans
**Ideal**: Complete all exercises and understand evaluation strategies

## Time Investment

- **Minimum**: 4 hours (basics only)
- **Recommended**: 8-12 hours (solid understanding)
- **Complete**: 20 hours (all exercises + deep exploration)

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Reference**: `CHEAT_SHEET.md` for quick lookup

Good luck! You're starting an amazing journey into the foundations of computation! 🚀
