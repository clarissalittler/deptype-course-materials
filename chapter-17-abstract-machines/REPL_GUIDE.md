# Chapter 17: Abstract Machines - REPL User Guide

## Overview

The Abstract Machines REPL lets you experiment with three classic abstract machines (CEK, SECD, Krivine), compare evaluation strategies, and see step-by-step execution traces.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-17-abstract-machines
stack build

# Run the REPL
stack exec abstract-machines-repl
```

### Quick Start

```
am> (\x. x) 5
Result: 5

am> :help
[Shows available commands]
```

## Features

### 1. Multiple Machines

Switch between three abstract machines:

#### CEK Machine (Default)
```
am> :machine cek
Switched to CEK machine (call-by-value)

am> (\x. x + 1) 5
Result: 6
```

#### SECD Machine
```
am> :machine secd
Switched to SECD machine (compiled bytecode)

am> :compile \x. x + 1
Compiled to:
  IClosure [IAccess 0, IConst 1, IAdd, IReturn]

am> (\x. x + 1) 5
Result: 6
```

#### Krivine Machine
```
am> :machine krivine
Switched to Krivine machine (call-by-name, lazy)

am> (\x. 42) error
Result: 42  -- error never evaluated!
```

### 2. Evaluation Traces

See complete execution traces:

```
am> :trace (\x. x) 5
CEK trace (7 steps):
  1. Eval ((\x. x) 5) env={} kont=[]
  2. Eval (\x. x) env={} kont=[FApp1 5 {}]
  3. Apply kont=[FApp1 5 {}] val=<λx.x, {}>
  4. Eval 5 env={} kont=[FApp2 <λx.x, {}>]
  5. Apply kont=[FApp2 <λx.x, {}>] val=5
  6. Eval x env={x→5} kont=[]
  7. Apply kont=[] val=5

Result: 5
```

Disable traces with `:notrace`.

### 3. Step-by-Step Execution

Step through evaluation manually:

```
am> :step (\x. x + 1) 5
Step 1/10: Eval ((\x. x+1) 5) env={} kont=[]
  [Press Enter to continue, 'q' to quit]

Step 2/10: Eval (\x. x+1) env={} kont=[FApp1 5 {}]
  [Press Enter to continue, 'q' to quit]

...
```

### 4. Compilation (SECD only)

View compiled bytecode:

```
am> :machine secd
am> :compile \f. \x. f (f x)

Compiled to:
  IClosure [
    IClosure [
      IAccess 1,
      IAccess 1,
      IAccess 0,
      IApply,
      IApply,
      IReturn
    ],
    IReturn
  ]
```

### 5. Environment Inspection

See closures and environments:

```
am> :env let x = 5 in \y. x + y

Result: <λy. x+y, {x→5}>
Environment captured:
  x → 5
```

### 6. Let Bindings

Define reusable terms:

```
am> :let id = \x. x
Defined: id = λx. x

am> :let const = \x. \y. x
Defined: const = λx. λy. x

am> const id (\a. a a)
Result: λx. x

am> :bindings
Current bindings:
  id = λx. x
  const = λx. λy. x
```

## Term Syntax

### Lambda Abstraction

```
\x. x                 Single argument
\x y. x               Multiple arguments (λx. λy. x)
λx. x                 Unicode lambda
```

### Application

```
f x                   Simple application
f x y                 Left-associative: (f x) y
(f x) (g y)           Parentheses for grouping
```

### Let Bindings

```
let x = 5 in x + 1
let f = \x. x in f 5
```

### Conditionals

```
if0 n then 1 else 2   Branch on zero
```

### Arithmetic

```
x + y                 Addition
x - y                 Subtraction
x * y                 Multiplication
```

### Literals

```
0, 1, 42, -5          Integers
```

## Command Reference

### Machine Commands

| Command | Description |
|---------|-------------|
| `:machine cek` | Switch to CEK machine |
| `:machine secd` | Switch to SECD machine |
| `:machine krivine` | Switch to Krivine machine |
| `:current` | Show current machine |

### Evaluation Commands

| Command | Description |
|---------|-------------|
| `term` | Evaluate term with current machine |
| `:trace term` | Show full evaluation trace |
| `:step term` | Step through evaluation manually |
| `:notrace` | Disable automatic traces |

### Inspection Commands

| Command | Description |
|---------|-------------|
| `:env term` | Show environment captured by closure |
| `:compile term` | Compile to SECD bytecode (SECD only) |
| `:frames` | Show continuation frames (CEK only) |
| `:stack` | Show argument stack (Krivine only) |

### Binding Commands

| Command | Description |
|---------|-------------|
| `:let name = term` | Define a binding |
| `:bindings` | Show all bindings |
| `:clear` | Clear all bindings |

### Information Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help message |
| `:examples` | Show example programs |
| `:quit` | Exit the REPL |

## Advanced Examples

### CEK: Closures and Environments

```
am> :machine cek

# Closure captures environment
am> let y = 10 in \x. x + y
Result: <λx. x+y, {y→10}>

# Lexical scoping
am> let x = 1 in let f = \y. x + y in let x = 100 in f 5
Result: 6  -- f captured x=1, not x=100

# Higher-order functions
am> let twice = \f. \x. f (f x) in twice (\n. n + 1) 0
Result: 2
```

### SECD: Bytecode and Stack Execution

```
am> :machine secd

# See compiled bytecode
am> :compile let x = 5 in x + 1
Compiled to:
  IClosure [IAccess 0, IConst 1, IAdd, IReturn]
  IConst 5
  IApply

# Trace stack-based execution
am> :trace (\x. x) 5
SECD trace:
  ([], [], [IClosure [...], IConst 5, IApply], [])
  ([<closure>], [], [IConst 5, IApply], [])
  ([5, <closure>], [], [IApply], [])
  ([], [5], [IAccess 0, IReturn], [([],[], [])])
  ([5], [5], [IReturn], [([],[], [])])
  ([5], [], [], [])
Result: 5
```

### Krivine: Lazy Evaluation

```
am> :machine krivine

# Arguments not evaluated until needed
am> :trace (\x. 42) (1 + 2)
Krivine trace:
  State ((\x. 42) (1+2)) env={} stack=[]
  State (\x. 42) env={} stack=[Thunk(1+2, {})]
  State 42 env={x→Thunk(1+2, {})} stack=[]
Result: 42  -- 1+2 never evaluated!

# But evaluated when used
am> :trace (\x. x) (1 + 2)
Krivine trace:
  State ((\x. x) (1+2)) env={} stack=[]
  State (\x. x) env={} stack=[Thunk(1+2, {})]
  State x env={x→Thunk(1+2, {})} stack=[]
  State (1+2) env={} stack=[]
  State 3 env={} stack=[]
Result: 3  -- Now evaluated because used!
```

## Comparing Machines

### Same Result, Different Paths

```
# Define a term
am> :let term = (\x. x + 1) 5

# Evaluate in CEK
am> :machine cek
am> :trace term
[Shows CEK trace with frames]

# Evaluate in SECD
am> :machine secd
am> :trace term
[Shows SECD trace with stack]

# Evaluate in Krivine
am> :machine krivine
am> :trace term
[Shows Krivine trace with thunks]

# All give same result: 6
```

### Divergence Example

```
# Define a diverging term
am> :let omega = (\x. x x) (\x. x x)

# CEK and SECD diverge
am> :machine cek
am> (\x. 42) omega
[Diverges - Ctrl+C to stop]

# Krivine terminates
am> :machine krivine
am> (\x. 42) omega
Result: 42
```

## Practice Exercises

### Exercise 1: Trace Analysis

Trace this term in all three machines:

```
am> (\f. \x. f (f x)) (\n. n + 1) 0
```

Questions:
- How many steps in each machine?
- What closures are created?
- What's on the continuation/stack at each step?

### Exercise 2: Closure Capture

Predict the result before running:

```
am> let x = 5 in
    let f = \y. x + y in
    let x = 10 in
    f 3
```

Then trace to verify:
```
am> :trace [paste term]
```

### Exercise 3: Lazy vs Strict

Find the difference:

```
# CEK (strict)
am> :machine cek
am> (\x. \y. y) (1/0) 42

# Krivine (lazy)
am> :machine krivine
am> (\x. \y. y) (1/0) 42
```

Which diverges? Why?

### Exercise 4: Bytecode Understanding

Compile and explain each instruction:

```
am> :machine secd
am> :compile \x. \y. x + y
```

What does each IAccess refer to?

### Exercise 5: Continuation Inspection

At what point is the continuation largest?

```
am> :machine cek
am> :trace ((1 + 2) + 3) + 4
```

## Common Patterns

### Identity Function

```
am> \x. x
Result: λx. x

am> (\x. x) 42
Result: 42
```

### Constant Function

```
am> \x. \y. x
Result: λx. λy. x

am> (\x. \y. x) 5 10
Result: 5
```

### Self-Application

```
# Terminating
am> (\x. x x) (\y. y)
Result: λy. y

# Non-terminating (Krivine can handle)
am> :machine krivine
am> (\x. \y. y) ((\z. z z) (\z. z z))
Result: λy. y
```

### Church Numerals

```
am> :let zero = \f. \x. x
am> :let one = \f. \x. f x
am> :let two = \f. \x. f (f x)
am> :let succ = \n. \f. \x. f (n f x)

am> succ two
Result: λf. λx. f (f (f x))  -- three!
```

### Fixed Point

```
# Y combinator (works in Krivine)
am> :machine krivine
am> :let Y = \f. (\x. f (x x)) (\x. f (x x))

# Factorial
am> :let fact = Y (\f. \n. if0 n then 1 else n * f (n - 1))
am> fact 5
Result: 120
```

## Troubleshooting

### Non-Termination

**Problem**: Evaluation never finishes.

**Solutions**:
1. Use Krivine for lazy evaluation
2. Check for infinite loops (omega combinator)
3. Press Ctrl+C to interrupt
4. Use `:step` mode to see where it loops

### Parse Errors

**Problem**: `Parse error: unexpected token`

**Solutions**:
- Check parentheses: `(\x. x) 5` not `\x. x 5`
- Use spaces: `x+y` might fail, use `x + y`
- Lambda needs dot: `\x. x` not `\x x`

### Wrong Machine Behavior

**Problem**: Different result than expected.

**Solutions**:
- Check current machine: `:current`
- Switch machine: `:machine cek`
- Compare traces in different machines

### Environment Confusion

**Problem**: Variable has wrong value.

**Solution**:
- Use `:env` to inspect closures
- Trace to see environment at each step
- Remember: closures capture definition-time environment

## Further Reading

- [Chapter 17 README](README.md) - Complete theory
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step examples
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- Landin (1964): Original SECD paper
- Krivine (2007): The Krivine machine

## Next Steps

After mastering the abstract machines REPL:
- Chapter 18: Normalization by Evaluation (different evaluation approach)
- Chapter 20: Denotational Semantics (mathematical semantics)

Have fun exploring the abstract machines!
