# Chapter 1: REPL User Guide

## Overview

The Untyped Lambda Calculus REPL provides an interactive environment for experimenting with lambda terms, evaluation strategies, and Church encodings.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-01-untyped-lambda
stack build

# Run the REPL
stack exec untyped-lambda-repl
```

### Quick Start

```
λ> \x. x
  λx. x

λ> (\x. x) (\y. y)
  λy. y

λ> :help
  [Shows available commands]
```

## Features

### 1. Term Evaluation

Simply type a lambda term to evaluate it:

```
λ> (\x y. x) (\a. a) (\b. b)
  λa. a
```

The REPL automatically reduces terms to normal form using the selected evaluation strategy.

### 2. Evaluation Strategies

Choose between different evaluation strategies:

#### Call-by-Value (Default)
```
λ> :strategy cbv
Evaluation strategy: Call-by-value

λ> (\x. \y. y) ((\z. z z) (\z. z z))
  (diverges - argument evaluated first)
```

#### Normal Order
```
λ> :strategy normal
Evaluation strategy: Normal order

λ> (\x. \y. y) ((\z. z z) (\z. z z))
  λy. y
```

#### Call-by-Name
```
λ> :strategy cbn
Evaluation strategy: Call-by-name
```

### 3. Step-by-Step Evaluation

Enable step mode to manually step through reductions:

```
λ> :step
Step mode enabled

λ> (\x. x x) (\y. y)
  (λx. x x) (λy. y)
    [Press Enter to step]
→ (λy. y) (λy. y)
    [Press Enter to step]
→ λy. y
  (normal form)
```

Press Enter to advance one step, or type `:q` to exit step mode.

### 4. Evaluation Traces

Show all intermediate evaluation steps:

```
λ> :trace
Evaluation trace enabled

λ> (\f x. f (f x)) (\y. y) (\z. z)
  (λf. λx. f (f x)) (λy. y) (λz. z)
  (λx. (λy. y) ((λy. y) x)) (λz. z)
  (λy. y) ((λy. y) (λz. z))
  (λy. y) (λz. z)
  λz. z
```

Disable with `:notrace`.

### 5. Bindings

Define and reuse named terms:

```
λ> :let id = \x. x
  id = λx. x

λ> :let const = \x y. x
  const = λx y. x

λ> const id (\a. a a)
  λx. x

λ> :bindings
Current bindings:
  id = λx. x
  const = λx y. x
```

### 6. Church Encodings

The REPL is perfect for experimenting with Church encodings:

#### Church Booleans

```
λ> :let true = \t f. t
λ> :let false = \t f. f
λ> :let if = \b t f. b t f
λ> :let and = \p q. p q p
λ> :let or = \p q. p p q
λ> :let not = \p. p false true

λ> if true (\x. x) (\y. y y)
  λx. x

λ> and true false
  λt f. f
```

#### Church Numerals

```
λ> :let zero = \f x. x
λ> :let one = \f x. f x
λ> :let two = \f x. f (f x)
λ> :let three = \f x. f (f (f x))

λ> :let succ = \n f x. f (n f x)
λ> :let add = \m n f x. m f (n f x)
λ> :let mult = \m n f. m (n f)

λ> succ two
  λf x. f (f (f x))

λ> add two three
  λf x. f (f (f (f (f x))))

λ> mult two three
  λf. (λx. f (f (f (f (f (f x)))))))
```

#### Church Pairs

```
λ> :let pair = \x y f. f x y
λ> :let fst = \p. p (\x y. x)
λ> :let snd = \p. p (\x y. y)

λ> :let myPair = pair true false
λ> fst myPair
  λt f. t

λ> snd myPair
  λt f. f
```

#### Church Lists

```
λ> :let nil = \c n. n
λ> :let cons = \h t c n. c h (t c n)
λ> :let isNil = \l. l (\h t. false) true

λ> :let list123 = cons one (cons two (cons three nil))
λ> isNil list123
  λt f. f

λ> isNil nil
  λt f. t
```

### 7. Session Management

#### Save Bindings

```
λ> :save mybindings.lam
Saved 15 bindings to mybindings.lam
```

#### Load Bindings

```
λ> :load mybindings.lam
Loaded 15 bindings
```

#### Clear Bindings

```
λ> :clear
[Clears all bindings]
```

## Command Reference

### Evaluation Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:step` | | Enable step-by-step evaluation |
| `:nostep` | | Disable step-by-step evaluation |
| `:trace` | | Show all evaluation steps |
| `:notrace` | | Hide evaluation steps |
| `:strategy normal` | | Use normal order reduction |
| `:strategy cbv` | | Use call-by-value |
| `:strategy cbn` | | Use call-by-name |

### Binding Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:let name = term` | | Define a binding |
| `:bindings` | `:b` | Show all bindings |
| `:clear` | `:c` | Clear all bindings |
| `:load file` | | Load bindings from file |
| `:save file` | | Save bindings to file |

### Information Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:help` | `:h`, `:?` | Show help message |
| `:examples` | `:ex` | Show example terms |
| `:quit` | `:q`, `:exit` | Exit the REPL |

## Lambda Term Syntax

### Variables
```
x, y, z, foo, bar
```

### Lambda Abstraction
```
\x. x              Single argument
\x y z. x          Multiple arguments (λx. λy. λz. x)
λx. x              Unicode lambda (λ)
```

### Application
```
f x                Simple application
f x y              Left-associative: (f x) y
(f x) (g y)        Parentheses for grouping
```

## Advanced Examples

### Fixed-Point Combinators

#### Y Combinator
```
λ> :let Y = \f. (\x. f (x x)) (\x. f (x x))
```

**Warning**: Applying Y directly will diverge! Use normal order:
```
λ> :strategy normal
λ> Y (\f n. ...)  [factorial using Y]
```

#### Z Combinator (works in call-by-value)
```
λ> :let Z = \f. (\x. f (\y. x x y)) (\x. f (\y. x x y))
```

### Recursion Examples

#### Factorial (using Z combinator)
```
λ> :strategy cbv
λ> :let Z = \f. (\x. f (\y. x x y)) (\x. f (\y. x x y))
λ> :let fact = Z (\f n. isZero n one (mult n (f (pred n))))
```

### Church Encoding Complete Library

```
# Booleans
:let true = \t f. t
:let false = \t f. f
:let if = \b t f. b t f
:let and = \p q. p q p
:let or = \p q. p p q
:let not = \p. p false true

# Numerals
:let zero = \f x. x
:let succ = \n f x. f (n f x)
:let add = \m n f x. m f (n f x)
:let mult = \m n f. m (n f)
:let isZero = \n. n (\x. false) true

# Pairs
:let pair = \x y f. f x y
:let fst = \p. p (\x y. x)
:let snd = \p. p (\x y. y)

# Lists
:let nil = \c n. n
:let cons = \h t c n. c h (t c n)
:let isNil = \l. l (\h t. false) true
:let head = \l. l (\h t. h) nil
:let tail = \l. fst (l (\x p. pair (snd p) (cons x (snd p))) (pair nil nil))
```

## Tips and Tricks

### 1. Reducing Non-Terminating Terms

Some terms don't terminate. Use normal order strategy when possible:

```
λ> :strategy normal
λ> (\x. \y. y) ((\z. z z) (\z. z z))
  λy. y
```

### 2. Debugging Complex Terms

Use `:trace` to see all reduction steps:

```
λ> :trace
λ> mult two three
  [Shows all intermediate steps]
```

### 3. Building a Library

Save common encodings to a file:

```
# church.lam
true = \t f. t
false = \t f. f
zero = \f x. x
one = \f x. f x
succ = \n f x. f (n f x)
```

Load in REPL:
```
λ> :load church.lam
```

### 4. Testing Alpha Equivalence

Different variable names, same term:

```
λ> \x. x
  λx. x

λ> \y. y
  λy. y
```

Both are α-equivalent (same identity function).

### 5. Understanding Evaluation Order

Compare strategies:

```
# Call-by-value evaluates arguments first
λ> :strategy cbv
λ> (\x. \y. y) ((\z. z z) (\z. z z))
  [Diverges! Argument never terminates]

# Normal order reduces leftmost-outermost first
λ> :strategy normal
λ> (\x. \y. y) ((\z. z z) (\z. z z))
  λy. y
  [Argument discarded without evaluation]
```

## Common Patterns

### Identity Function
```
λ> \x. x
```

### Constant Function
```
λ> \x y. x
```

### Self-Application
```
λ> \x. x x
```

### Function Composition
```
λ> :let compose = \f g x. f (g x)
λ> compose (\x. x) (\y. y)
  λx. x
```

### Boolean Conditionals
```
λ> :let ifthenelse = \b t f. b t f
λ> ifthenelse true (\x. x) (\y. y y)
  λx. x
```

## Exercises

Try these exercises to learn lambda calculus:

### Exercise 1: Church Booleans
Implement `xor` using Church booleans.

### Exercise 2: Church Numerals
Implement `pred` (predecessor function) for Church numerals.

### Exercise 3: Church Pairs
Implement `swap` that swaps the elements of a Church pair.

### Exercise 4: Church Lists
Implement `length` that returns the length of a Church list.

### Exercise 5: Combinators
Explore the SKI combinator calculus:
- S = `\x y z. x z (y z)`
- K = `\x y. x`
- I = `\x. x`

Verify that `S K K = I`.

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected 'λ'`

**Solution**: Use backslash `\` instead of `λ`, or ensure your terminal supports Unicode.

### Non-Termination

**Problem**: Term never reduces to normal form.

**Solutions**:
1. Switch to normal order: `:strategy normal`
2. Use step mode to see where it diverges: `:step`
3. Set a step limit (built-in: 1000 steps)

### Stack Overflow

**Problem**: Very large terms cause stack overflow.

**Solution**: Use simpler terms or refactor to avoid deep nesting.

## Further Reading

- [Chapter 1 README](README.md) - Complete theory and exercises
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- Pierce's TAPL Chapter 5 - Untyped Lambda Calculus
- Barendregt's "Lambda Calculus" - Comprehensive reference

## Next Steps

After mastering the untyped lambda calculus REPL:
- Chapter 2: Simply Typed Lambda Calculus (adds types!)
- Chapter 3: STLC with ADTs (products, sums, records)
- Chapter 4: Hindley-Milner Type Inference (automatic types)

Have fun exploring the lambda calculus! 🎉
