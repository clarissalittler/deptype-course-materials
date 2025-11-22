# Chapter 2: Simply Typed Lambda Calculus - REPL User Guide

## Overview

The Simply Typed Lambda Calculus REPL provides an interactive environment for experimenting with typed lambda terms, type checking, and type-safe evaluation. Unlike Chapter 1's untyped calculus, every term must have a valid type.

**Key Feature**: Automatic type checking before evaluation - ill-typed programs are rejected!

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-02-simply-typed-lambda
stack build

# Run the REPL
stack exec simply-typed-lambda-repl
```

### Your First Typed Term

```
λ> \x:Bool. x
  : Bool -> Bool
  λx:Bool. x

λ> \x:Bool. if x then false else true
  : Bool -> Bool
  λx:Bool. if x then false else true

λ> :help
  [Shows available commands]
```

## Features

### 1. Type Annotations Required

Unlike untyped lambda calculus, you must annotate lambda parameters with types:

```
λ> \x:Nat. succ x
  : Nat -> Nat
  λx:Nat. succ x

λ> \f:Nat->Nat. \x:Nat. f (f x)
  : (Nat -> Nat) -> Nat -> Nat
  λf:Nat->Nat. \x:Nat. f (f x)
```

**Note**: The REPL displays the inferred type first (`: Type`), then the term.

### 2. Automatic Type Checking

The REPL type-checks every term before evaluation:

```
λ> if true then zero else false
  Type error: Expected Nat but got Bool

λ> (\x:Bool. succ x) true
  Type error: Expected Nat but got Bool in succ application
```

### 3. Query Types with :type

Check the type of any term without evaluating it:

```
λ> :type \f:Nat->Nat. \x:Nat. f (f x)
  \f:Nat->Nat. \x:Nat. f (f x) : (Nat -> Nat) -> Nat -> Nat

λ> :type if true then zero else succ zero
  if true then zero else succ zero : Nat

λ> :type \x:Bool. \y:Bool. if x then y else false
  \x:Bool. \y:Bool. if x then y else false : Bool -> Bool -> Bool
```

### 4. Base Types

STLC includes two base types:

#### Bool Type
```
λ> true
  : Bool
  true

λ> false
  : Bool
  false

λ> if true then false else true
  : Bool
  false
```

#### Nat Type
```
λ> zero
  : Nat
  0

λ> succ zero
  : Nat
  1

λ> succ (succ (succ zero))
  : Nat
  3

λ> pred (succ zero)
  : Nat
  1

λ> iszero zero
  : Bool
  true
```

### 5. Conditional Expressions

```
λ> if true then zero else succ zero
  : Nat
  0

λ> if iszero zero then succ zero else zero
  : Nat
  1

λ> if false then \x:Nat. x else \y:Nat. succ y
  : Nat -> Nat
  λy:Nat. succ y
```

### 6. Function Types

Functions have arrow types (→):

```
λ> :type \x:Nat. x
  \x:Nat. x : Nat -> Nat

λ> :type \x:Bool. \y:Nat. if x then y else zero
  \x:Bool. \y:Nat. if x then y else zero : Bool -> Nat -> Nat

λ> :type \f:Nat->Nat. \g:Nat->Nat. \x:Nat. f (g x)
  ... : (Nat -> Nat) -> (Nat -> Nat) -> Nat -> Nat
```

**Note**: `A -> B -> C` means `A -> (B -> C)` (right-associative)

### 7. Named Bindings with Type Tracking

Define and reuse typed terms:

```
λ> :let id = \x:Nat. x
  id : Nat -> Nat
  id = λx:Nat. x

λ> :let not = \x:Bool. if x then false else true
  not : Bool -> Bool
  not = λx:Bool. if x then false else true

λ> :let twice = \f:Nat->Nat. \x:Nat. f (f x)
  twice : (Nat -> Nat) -> Nat -> Nat
  twice = λf:Nat->Nat. λx:Nat. f (f x)

λ> twice (\x:Nat. succ x) zero
  : Nat
  2

λ> :bindings
Current bindings:
  id : Nat -> Nat
  not : Bool -> Bool
  twice : (Nat -> Nat) -> Nat -> Nat
```

### 8. Step-by-Step Evaluation

Watch how typed terms evaluate:

```
λ> :step
Step mode enabled

λ> (\f:Nat->Nat. \x:Nat. f (f x)) (\y:Nat. succ y) zero
  : Nat
  (λf:Nat->Nat. λx:Nat. f (f x)) (λy:Nat. succ y) 0
    [Press Enter to step]
→ (λx:Nat. (λy:Nat. succ y) ((λy:Nat. succ y) x)) 0
    [Press Enter to step]
→ (λy:Nat. succ y) ((λy:Nat. succ y) 0)
    [Press Enter to step]
→ (λy:Nat. succ y) (succ 0)
    [Press Enter to step]
→ succ (succ 0)
    [Press Enter to step]
→ 2
  (normal form)
```

### 9. Evaluation Traces

Show all evaluation steps at once:

```
λ> :trace
Evaluation trace enabled

λ> (\x:Nat. succ (succ x)) (pred (succ zero))
  : Nat
  (λx:Nat. succ (succ x)) (pred 1)
  (λx:Nat. succ (succ x)) 0
  succ (succ 0)
  succ 1
  2
```

### 10. Toggle Type Checking

For experimentation, you can disable type checking (use with caution!):

```
λ> :nocheck
Type checking disabled (unsafe mode)

λ> if true then zero else false
  0
  (evaluation may produce nonsense without type checking)

λ> :check
Type checking enabled
```

## Command Reference

### Essential Commands
- `:help` - Show help and syntax reference
- `:quit` or `:q` - Exit the REPL
- `:type <term>` - Show the type of a term
- `:let <name> = <term>` - Bind a term to a name

### Environment Commands
- `:bindings` or `:env` - Show all current bindings
- `:reset` - Clear all bindings
- `:clear` - Clear the screen

### Evaluation Commands
- `:step` - Enable step-by-step evaluation mode
- `:nostep` - Disable step mode
- `:trace` - Show all evaluation steps
- `:notrace` - Hide evaluation steps

### Type Checking Commands
- `:check` - Enable type checking (default)
- `:nocheck` - Disable type checking (unsafe!)

### Information Commands
- `:examples` - Show comprehensive examples
- `:syntax` - Show syntax reference

## Guided Exploration

### Exercise 1: Understanding Types (5 minutes)

Try these and observe the types:

```
λ> :type true
λ> :type zero
λ> :type \x:Bool. x
λ> :type \x:Nat. \y:Nat. x
λ> :type if
```

**Question**: What's the type of the `if` expression?

### Exercise 2: Type Errors (5 minutes)

Try to create these type errors and understand the error messages:

```
λ> if zero then true else false
λ> succ true
λ> (\x:Bool. succ x) false
λ> pred false
```

**Question**: Why does each one fail?

### Exercise 3: Higher-Order Functions (10 minutes)

Build up complexity:

```
λ> :let apply = \f:Nat->Nat. \x:Nat. f x
λ> apply (\x:Nat. succ x) zero

λ> :let compose = \f:Nat->Nat. \g:Nat->Nat. \x:Nat. f (g x)
λ> compose (\x:Nat. succ x) (\y:Nat. succ y) zero

λ> :let twice = \f:Nat->Nat. \x:Nat. f (f x)
λ> twice (\x:Nat. succ x) zero
```

**Challenge**: Can you write a `thrice` function?

### Exercise 4: Boolean Logic (10 minutes)

Implement boolean operations:

```
λ> :let and = \x:Bool. \y:Bool. if x then y else false
λ> and true false

λ> :let or = \x:Bool. \y:Bool. if x then true else y
λ> or true false

λ> :let not = \x:Bool. if x then false else true
λ> not true
```

**Challenge**: Implement XOR using `and`, `or`, and `not`.

### Exercise 5: Natural Number Arithmetic (15 minutes)

Build basic arithmetic:

```
λ> :let add = \x:Nat. \y:Nat.
                 if iszero x
                 then y
                 else succ (add (pred x) y)
λ> add (succ zero) (succ (succ zero))

λ> :let mult = \x:Nat. \y:Nat.
                  if iszero x
                  then zero
                  else add y (mult (pred x) y)
λ> mult (succ (succ zero)) (succ (succ (succ zero)))
```

**Note**: Recursion requires the fix-point combinator (covered in exercises).

### Exercise 6: Type Safety in Action (10 minutes)

Explore type preservation:

```
λ> :let safeTerm = \x:Nat. succ x
λ> :type safeTerm
λ> safeTerm (succ zero)
λ> :type safeTerm (succ zero)
```

**Observation**: The type is preserved through evaluation!

Try an unsafe term:
```
λ> :nocheck
λ> :let unsafeTerm = if true then zero else false
λ> :check
```

**Question**: What happens when you re-enable type checking?

## Common REPL Workflows

### Workflow 1: Exploring a Concept
1. Read about the concept in README.md or TUTORIAL.md
2. Use `:type` to understand type signatures
3. Try simple examples
4. Use `:step` to understand evaluation
5. Build more complex examples

### Workflow 2: Solving an Exercise
1. Read the exercise description
2. Start with a type signature using `:type`
3. Build up the term incrementally
4. Test with `:let` to bind intermediate results
5. Use `:trace` to debug unexpected results

### Workflow 3: Understanding Type Errors
1. Try the term
2. Read the error message carefully
3. Use `:type` on sub-expressions to find the issue
4. Check COMMON_MISTAKES.md for similar errors
5. Fix and retry

## Tips and Tricks

### Tip 1: Start with Types
Before writing a complex term, figure out what type you need:
```
λ> :type \f:Nat->Nat. \g:Nat->Nat. \x:Nat. f (g x)
```
This helps understand the structure.

### Tip 2: Build Incrementally
Don't write complex terms all at once:
```
λ> :let f = \x:Nat. succ x
λ> :let g = \x:Nat. succ (succ x)
λ> :let compose = \f:Nat->Nat. \g:Nat->Nat. \x:Nat. f (g x)
λ> compose f g zero
```

### Tip 3: Use Parentheses Liberally
When in doubt, add parentheses:
```
λ> \f:Nat->Nat. \x:Nat. f (f x)  ✓ Clear
λ> \f:Nat->Nat. \x:Nat. f f x    ✗ Confusing!
```

### Tip 4: Check Subterms
If a large term has a type error, check parts:
```
λ> :type \f:Nat->Nat. \x:Nat. f (f x)
λ> :type f (f x)  -- With f and x in scope
```

### Tip 5: Save Your Work
Before trying risky experiments:
```
λ> :bindings  -- Save current state
λ> -- Experiment
λ> :reset     -- If things go wrong
λ> -- Restore bindings manually
```

## Troubleshooting

### Problem: "Parse error"
**Cause**: Syntax mistake
**Solution**: Check for:
- Missing type annotations: `\x. x` should be `\x:Nat. x`
- Mismatched parentheses
- Invalid names

### Problem: "Type error: Expected X but got Y"
**Cause**: Type mismatch
**Solution**:
- Use `:type` to check subterms
- Ensure function arguments match parameter types
- Check COMMON_MISTAKES.md for patterns

### Problem: "Unbound variable"
**Cause**: Using a name not in scope
**Solution**:
- Use `:bindings` to see available names
- Define it with `:let`
- Check spelling

### Problem: "Evaluation doesn't terminate"
**Cause**: Infinite loop
**Solution**:
- Press Ctrl+C to interrupt
- Use `:step` to see where it loops
- Check recursion has a base case

### Problem: "The REPL feels slow"
**Cause**: Complex evaluation
**Solution**:
- Simplify terms
- Use `:nocheck` for quick experiments (then re-enable)
- Break complex terms into named parts with `:let`

## Syntax Reference

### Types
```
Bool                    -- Boolean type
Nat                     -- Natural number type
T1 -> T2               -- Function type (right-associative)
(T1 -> T2) -> T3       -- Use parens for left-associativity
```

### Terms
```
true, false            -- Boolean values
zero                   -- Natural number zero
succ <term>            -- Successor (add 1)
pred <term>            -- Predecessor (subtract 1)
iszero <term>          -- Test if zero
if <b> then <t> else <e>  -- Conditional
\x:T. <term>           -- Lambda abstraction (typed)
<term> <term>          -- Application
```

### Numbers
The REPL displays natural numbers using numeric literals:
```
0   = zero
1   = succ zero
2   = succ (succ zero)
...
```

## Comparison with Chapter 1

| Feature | Chapter 1 (Untyped) | Chapter 2 (Typed) |
|---------|-------------------|-------------------|
| Lambda syntax | `\x. t` | `\x:T. t` |
| Type safety | No types | Guaranteed type-safe |
| Evaluation | May diverge or get stuck | Well-typed programs don't get stuck |
| Errors caught | Runtime (stuck terms) | Compile-time (type errors) |
| Flexibility | More permissive | More restrictive |
| Guarantees | None | Progress + Preservation |

## Connection to Real Languages

This type system is the foundation for:
- **Java**: Basic types, function types (pre-generics)
- **C++**: Static typing, function pointers
- **Go**: Simple type system
- **TypeScript**: Core type system (before advanced features)

## Next Steps

After mastering this REPL:
1. Complete the exercises in `exercises/EXERCISES.md`
2. Work through `TUTORIAL.md` for deeper understanding
3. Take the `QUIZ.md` to test your knowledge
4. Move on to Chapter 3 for algebraic data types
5. Explore `COMMON_MISTAKES.md` when debugging

## Quick Reference Card

```
# Building
stack build && stack exec simply-typed-lambda-repl

# Essential Commands
:help           -- Show help
:quit           -- Exit
:type <term>    -- Show type
:let x = <term> -- Bind name

# Exploration
:step           -- Step-by-step mode
:trace          -- Show all steps
:bindings       -- Show environment

# Base Values
true, false     -- Booleans
zero, succ, pred, iszero  -- Naturals
if-then-else    -- Conditionals

# Lambda Syntax
\x:T. body      -- Lambda (MUST annotate type)
f x             -- Application
```

Happy type checking! 🎯
