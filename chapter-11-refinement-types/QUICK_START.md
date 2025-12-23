# Chapter 11: Refinement Types - Quick Start

## TL;DR (30 seconds)

Refinement types extend simple types with logical predicates, allowing you to express precise constraints like "positive numbers" or "non-empty lists" directly in the type system. This chapter teaches how to prevent runtime errors at compile time by encoding invariants as types.

**Who**: Those who understand simple types and want precise specifications
**Time**: 2-3 weeks (or 1 intensive week)
**Payoff**: Statically prevent division by zero, null dereferencing, array bounds errors

## What You'll Build

- Type checker with refinement types and predicates
- Subtyping via predicate implication
- Path-sensitive type checking for conditionals
- Understanding of dependent function types
- Connection to automated verification

**Tangible Outcome**: Write types that prevent common runtime errors at compile time!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-11-refinement-types
stack build
stack exec refinement-repl
```

You should see:
```
Welcome to the Refinement Types REPL!
refinement>
```

### Step 2: Your First Refinement Type (1 minute)

```
refinement> :type λx : {n : Nat | n > 0}. x
{n : Nat | n > 0} -> {n : Nat | n > 0}
```

Congrats! You just wrote a type for positive numbers!

### Step 3: Check a Predicate (1 minute)

```
refinement> :check 5 > 0
Valid (always true)

refinement> :check 5 > 10
Invalid (always false)
```

### Step 4: See Subtyping in Action (1 minute)

```
refinement> :subtype {x: Nat | x > 10} <: {x: Nat | x > 5}
true

refinement> :subtype {x: Nat | x > 5} <: {x: Nat | x > 10}
false
```

More specific types (stronger predicates) are subtypes!

## Your First Success - Safe Division (10 minutes)

Follow this mini-tutorial to cement your understanding:

### 1. The Problem

Regular division is unsafe:
```
refinement> :type λn. λd. n `div` d
Nat -> Nat -> Nat
```

What if `d` is zero? Runtime error!

### 2. The Solution - Refinement Types

```
refinement> :type λn : Nat. λd : {d: Nat | d > 0}. n `div` d
Nat -> {d: Nat | d > 0} -> Nat
```

Now the type system prevents division by zero!

### 3. Try It Out

```
refinement> :let safeDiv = λn : Nat. λd : {d: Nat | d > 0}. n `div` d
safeDiv : Nat -> {d: Nat | d > 0} -> Nat

refinement> :eval safeDiv 10 2
5

refinement> :eval safeDiv 10 0
Type error: 0 does not satisfy {d: Nat | d > 0}
```

### 4. Path Sensitivity

Refinements work with conditionals:

```
refinement> :let safePred = λx : Nat. if iszero x then 0 else pred x
safePred : Nat -> Nat

refinement> :eval safePred 5
4

refinement> :eval safePred 0
0
```

In the `else` branch, the type checker knows `x > 0`, making `pred x` safe!

**Achievement Unlocked**: You just prevented runtime errors with types!

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - gentle, step-by-step introduction
2. Follow `LESSON_PLAN.md` - structured 14-18 hour course
3. Use `REPL_GUIDE.md` as reference when stuck
4. Try the first 5 exercises in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Read the subtyping and path sensitivity sections carefully
3. Work through exercises 1-10 (2-3 hours)
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all the examples
2. Experiment with different predicates
3. Try to break the type checker (find its limits)
4. Compare to LiquidHaskell examples online

## When to Skip This Chapter

**Skip if**:
- You're already comfortable with refinement types
- You've used LiquidHaskell or F* extensively
- You just want to learn effect systems (jump to Chapter 12)

**Don't skip if**:
- This is your first time with refinement types
- You want to understand automated verification
- You're interested in practical bug prevention

## Quick Reference

```bash
# Build
cd chapter-11-refinement-types && stack build

# Run REPL
stack exec refinement-repl

# Essential REPL Commands
:help                  # Show help
:type <expr>           # Check type of expression
:check <pred>          # Check if predicate is valid
:subtype <t1> <: <t2>  # Check subtyping
:eval <expr>           # Evaluate expression
:quit                  # Exit

# Refinement Syntax
{x: Nat | x > 0}       # Positive naturals
{x: Nat | x < 10}      # Naturals less than 10
{x: Bool | x == true}  # Singleton type (only true)

# Dependent Functions
(x: T1) -> T2          # T2 can mention x
(n: Nat) -> {m: Nat | m > n}  # Result greater than input

# Predicates
x > 0                  # Comparison
x > 0 && x < 10        # Conjunction
!x                     # Negation (for booleans)
x == 5                 # Equality
```

## Core Concepts in 2 Minutes

### 1. Refinement Types
`{x: T | φ(x)}` = values of type T satisfying predicate φ

**Example**: `{x: Nat | x > 0}` means "positive naturals"

### 2. Subtyping via Implication
If `φ(x) ⟹ ψ(x)`, then `{x: T | φ} <: {x: T | ψ}`

**Intuition**: More specific types (stronger predicates) are subtypes

**Example**: `{x: Nat | x > 10}` <: `{x: Nat | x > 5}` because x > 10 implies x > 5

### 3. Path Sensitivity
In branches, conditions refine types:

```
if x > 0 then
  -- here: x : {n: Nat | n > 0}
else
  -- here: x : {n: Nat | n <= 0}, i.e., x == 0
```

### 4. Dependent Functions
Function types where result type mentions argument:

```
replicate : (n: Nat) -> a -> {xs: List a | length xs == n}
```

## Success Criteria

You're ready for Chapter 12 when you can:
- [ ] Write refinement type annotations with predicates
- [ ] Determine subtyping relationships via implication
- [ ] Understand path-sensitive type checking
- [ ] Design functions with refinement types
- [ ] Complete exercises 1-8

**Minimum**: Understand basic refinements and subtyping
**Ideal**: Complete all exercises and understand path sensitivity

## Time Investment

- **Minimum**: 4 hours (basics only)
- **Recommended**: 14-18 hours (solid understanding)
- **Complete**: 30 hours (all exercises + deep exploration)

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md` for common errors
- **Need examples?** See `REPL_GUIDE.md` for interactive examples
- **Want structure?** Follow `LESSON_PLAN.md` step-by-step
- **Test yourself**: Take `QUIZ.md` when ready
- **Quick lookup**: Use `CHEAT_SHEET.md` as reference

## Common First Questions

### Q: Why not just use Maybe?
**A**: `Maybe` loses precision. Compare:

```
div : Nat -> Nat -> Maybe Nat  -- Must check Nothing everywhere
div : Nat -> {d: Nat | d > 0} -> Nat  -- Guaranteed safe!
```

Refinements move the check to the call site, where you often have more information.

### Q: How does this relate to dependent types?
**A**: Refinement types are a restricted form of dependent types:
- Dependent types: Arbitrary terms in types
- Refinement types: Only predicates in types
- Tradeoff: Less expressive but more automated

### Q: What's an SMT solver?
**A**: A tool (like Z3) that proves logical formulas. For complex predicates like "x > 10 ⟹ x > 5", we need SMT solvers. Our simple implementation uses basic rules.

### Q: Can I use this in real code?
**A**: Yes! See:
- **LiquidHaskell**: Refinement types for Haskell
- **F***: Microsoft's verification-oriented language
- **Dafny**: Verification with refinements

## First Exercises to Try

After the quick start, try these from `exercises/EXERCISES.md`:

1. **Exercise 1**: Write refinement types for common patterns
2. **Exercise 2**: Check subtyping relationships
3. **Exercise 3**: Use path sensitivity in conditionals
4. **Exercise 4**: Write safe list operations
5. **Exercise 5**: Implement safe array indexing

## What Makes This Chapter Special

Unlike simple types, refinement types let you:
- **Prevent errors**: Division by zero, null dereferencing, bounds errors
- **Express invariants**: "This list is sorted", "This file is open"
- **Document precisely**: Types are verified specifications
- **Enable optimization**: Compiler knows more about values

## Real-World Applications

Refinement types are used for:
- **Security**: Information flow control (F*)
- **Correctness**: Verified systems code
- **API design**: Express precise contracts
- **Optimization**: Eliminate runtime checks

## The "Aha!" Moment

Most students have their breakthrough when they realize:

> "The type checker is proving theorems about my code!"

When you write `{x: Nat | x > 0}`, you're asserting a theorem. When the type checker accepts your program, it has proven that theorem holds.

## Your Journey

```
Simple Types → Refinement Types → Full Dependent Types
   ↑              ↑                      ↑
  Safe       Safe + Precise        Safe + Expressive + Proofs
```

Refinement types hit a sweet spot: precise enough to prevent bugs, simple enough for automation.

Good luck! You're learning a powerful technique used in cutting-edge verification systems!
