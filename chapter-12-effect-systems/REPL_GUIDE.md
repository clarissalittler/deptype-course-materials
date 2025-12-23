# Chapter 12: REPL User Guide - Effect Systems

## Overview

The Effect Systems REPL provides an interactive environment for experimenting with algebraic effects, effect handlers, row polymorphism, and continuation-based semantics.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-12-effect-systems
stack build

# Run the REPL
stack exec effect-repl
```

### Quick Start

```
effect> :type λx : Unit. perform State.get ()
Unit -> s ! {State s}

effect> :effects
Available effects:
  State s: get, put
  Exception: throw
  IO: print, read
  Choice: choose

effect> :help
[Shows available commands]
```

## Features

### 1. Effect-Annotated Type Checking

Type check expressions with effect annotations:

```
effect> :type λx. x + 1
Nat -> Nat ! {}

effect> :type λx. perform State.get ()
Unit -> s ! {State s}

effect> :type λx. perform State.get () + perform IO.read ()
Unit -> Nat ! {State Nat, IO}
```

The REPL automatically tracks effects!

### 2. Effect Operations

Perform operations from built-in effects:

```
effect> :type perform State.get ()
s ! {State s}

effect> :type perform State.put 5
Unit ! {State Nat}

effect> :type perform IO.print 42
Unit ! {IO}

effect> :type perform Exception.throw ()
Unit ! {Exception}

effect> :type perform Choice.choose true
Bool ! {Choice}
```

### 3. Effect Handlers

Handle effects to give them meaning:

```
effect> :eval handle (perform State.get ()) with runState 0
0

effect> :eval handle (perform State.get () + 1) with runState 5
6

effect> :eval handle (
  perform State.put 10;
  perform State.get ()
) with runState 0
10
```

### 4. Handler Tracing

See how handlers interpret effects:

```
effect> :trace
effect> :eval handle (perform State.get () + 1) with runState 5
Steps:
  1. perform State.get ()
  2. Handler intercepts get operation
  3. Continuation k = λv. v + 1
  4. Handler calls k 5
  5. Result: 6
```

### 5. Effect Composition

Combine multiple effects:

```
effect> :type λ_.
  let x = perform State.get () in
  perform IO.print x;
  perform State.put (x + 1)
Unit -> Unit ! {State Nat, IO}

effect> :eval handle (
  handle computation with runState 0
) with collectIO
([0], ((), 1))
```

## Built-in Effects

### State Effect

Mutable state operations:

```
effect> :let counter = λ_.
  let n = perform State.get () in
  perform State.put (n + 1);
  n
counter : Unit -> Nat ! {State Nat}

effect> :eval handle (counter ()) with runState 0
0

effect> :eval handle (counter (); counter (); counter ()) with runState 0
2
```

### Exception Effect

Exception throwing:

```
effect> :let safe = λx. if x > 0 then x else perform Exception.throw ()
safe : Nat -> Nat ! {Exception}

effect> :eval handle (safe 5) with tryCatch 0
5

effect> :eval handle (safe 0) with tryCatch 99
99
```

### IO Effect

Input/output operations:

```
effect> :let greet = λ_.
  perform IO.print 72;
  perform IO.print 105
greet : Unit -> Unit ! {IO}

effect> :eval handle (greet ()) with collectIO
([72, 105], ())
```

### Choice Effect

Nondeterministic choice:

```
effect> :let branch = λ_.
  if perform Choice.choose true
  then 1
  else 2
branch : Unit -> Nat ! {Choice}

effect> :eval handle (branch ()) with allChoices
[1, 2]

effect> :eval handle (branch ()) with firstChoice
1
```

## Effect Handlers

### runState - State Handler

Thread state through computation:

```
effect> :type runState
Nat -> (Unit -> A ! {State Nat | ρ}) -> (A, Nat) ! ρ

effect> :eval runState 0 (λ_.
  perform State.put 5;
  perform State.get ()
)
(5, 5)
```

Usage:
- Initial state: `0`
- Final state returned with result
- State is threaded through continuations

### tryCatch - Exception Handler

Catch exceptions with default value:

```
effect> :type tryCatch
A -> (Unit -> A ! {Exception | ρ}) -> A ! ρ

effect> :eval tryCatch 99 (λ_. 42)
42

effect> :eval tryCatch 99 (λ_. perform Exception.throw ())
99
```

Usage:
- Default value: `99`
- If exception thrown, return default
- Otherwise, return result

### collectIO - IO Handler

Collect all print operations:

```
effect> :type collectIO
(Unit -> A ! {IO | ρ}) -> (A, [Nat]) ! ρ

effect> :eval collectIO (λ_.
  perform IO.print 1;
  perform IO.print 2;
  perform IO.print 3
)
((), [1, 2, 3])
```

Usage:
- Returns value and list of printed numbers
- `read` operations return 0 (mock input)

### allChoices - Choice Handler

Explore all branches:

```
effect> :type allChoices
(Unit -> A ! {Choice | ρ}) -> [A] ! ρ

effect> :eval allChoices (λ_.
  let x = if perform Choice.choose true then 1 else 2 in
  let y = if perform Choice.choose true then 10 else 20 in
  x + y
)
[11, 21, 12, 22]
```

Usage:
- Returns all possible results
- Each `choose` doubles the number of results

## Effect Polymorphism

### Row Variables

Write polymorphic effectful functions:

```
effect> :let twice = Λρ. λf : Unit -> Unit ! ρ. λ_. f (); f ()
twice : ∀ρ. (Unit -> Unit ! ρ) -> Unit -> Unit ! ρ

effect> :eval handle (twice [{State Nat}] counter ()) with runState 0
(1, 2)

effect> :eval handle (
  twice [{IO}] (λ_. perform IO.print 42) ()
) with collectIO
((), [42, 42])
```

### Row Extension

Add effects to polymorphic row:

```
effect> :let addState = Λρ. λf : Unit -> A ! ρ. λ_.
  perform State.put 0;
  f ()
addState : ∀ρ. (Unit -> A ! ρ) -> Unit -> A ! {State Nat | ρ}

effect> :type addState [{IO}]
(Unit -> A ! {IO}) -> Unit -> A ! {State Nat, IO}
```

## Advanced Examples

### Example 1: Stateful Counter with Reset

```
effect> :let counterWithReset = λ_.
  let n = perform State.get () in
  if n >= 10 then
    (perform State.put 0; 10)
  else
    (perform State.put (n + 1); n)

effect> :eval handle (
  counterWithReset ();
  counterWithReset ();
  counterWithReset ()
) with runState 9
(10, 1)
```

### Example 2: Exception Recovery

```
effect> :let tryTwice = λf.
  handle (f ()) with {
    Exception:
    return x -> x
    throw () k ->
      handle (f ()) with {
        Exception:
        return x -> x
        throw () k2 -> 0  -- Give up
      }
  }

effect> :eval tryTwice (λ_. perform Exception.throw ())
0
```

### Example 3: Nondeterministic Search

```
effect> :let pythagorean = λ_.
  let a = perform Choice.choose; perform Choice.choose; ... in
  let b = perform Choice.choose; perform Choice.choose; ... in
  let c = perform Choice.choose; perform Choice.choose; ... in
  if a*a + b*b == c*c then (a, b, c) else perform Exception.throw ()

effect> :eval handle (
  handle (pythagorean ()) with allChoices
) with filterExceptions
[(3, 4, 5), (4, 3, 5), ...]
```

### Example 4: Logging with State

```
effect> :let loggedCounter = λ_.
  let n = perform State.get () in
  perform IO.print n;
  perform State.put (n + 1);
  n

effect> :eval handle (
  handle (
    loggedCounter ();
    loggedCounter ();
    loggedCounter ()
  ) with runState 0
) with collectIO
([0, 1, 2], (2, 3))
```

## Command Reference

### Type and Evaluation Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:type <expr>` | Infer type with effects | `:type perform State.get ()` |
| `:eval <expr>` | Evaluate expression | `:eval runState 0 counter` |
| `:effects` | List available effects | `:effects` |
| `:handlers` | List available handlers | `:handlers` |

### Effect-Specific Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:trace` | Enable effect tracing | `:trace` |
| `:notrace` | Disable tracing | `:notrace` |
| `:row <row>` | Check row well-formedness | `:row {State, IO}` |
| `:unify <r1> <r2>` | Check row unification | `:unify ρ {State}` |

### Context Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:let name = expr` | Define binding | `:let x = perform State.get ()` |
| `:context` | Show typing context | `:context` |
| `:clear` | Clear all bindings | `:clear` |

### Information Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help message |
| `:examples` | Show example effects |
| `:quit` | Exit the REPL |

## Syntax Guide

### Effect Annotations

```
T ! {}                   -- Pure (no effects)
T ! {State}              -- Single effect
T ! {State, IO}          -- Multiple effects
T ! {E | ρ}              -- Effect E plus row variable
T ! ρ                    -- Just row variable
```

### Function Types

```
A -> B ! ε               -- Effectful function
∀ρ. A -> B ! ρ           -- Effect-polymorphic
∀ρ. A ! {E | ρ} -> B ! ρ -- Row extension
```

### Effect Operations

```
perform State.get ()     -- Perform get operation
perform State.put 5      -- Perform put with argument
perform IO.print 42      -- Perform print
perform Exception.throw () -- Perform throw
```

### Handlers

```
handle <expr> with {
  Effect:
  return x -> <body>      -- Handle pure return
  op param k -> <body>    -- Handle operation
}
```

### Effect Abstraction

```
Λρ. <expr>              -- Abstract over effect row
<expr> [<row>]          -- Apply to effect row
```

## Practical Patterns

### Pattern 1: Pure Function Wrapper

```
effect> :let pure = Λρ. λf : A -> B. λx : A. f x
pure : ∀ρ. (A -> B) -> A -> B ! ρ
```

### Pattern 2: State Initialization

```
effect> :let withState = λinit. λf.
  handle (f ()) with runState init

effect> :eval withState 100 (λ_. perform State.get ())
100
```

### Pattern 3: Error Handling

```
effect> :let orElse = λf. λg.
  handle (f ()) with {
    Exception:
    return x -> x
    throw () k -> g ()
  }

effect> :eval orElse (λ_. perform Exception.throw ()) (λ_. 42)
42
```

### Pattern 4: Effect Isolation

```
effect> :let isolated = λf.
  handle (
    handle (f ()) with runState 0
  ) with tryCatch default

effect> :type isolated
(Unit -> A ! {State, Exception}) -> A
```

### Pattern 5: Nondeterministic List

```
effect> :let fromList = λxs.
  case xs of
    [] -> perform Exception.throw ()
    (x:xs) ->
      if perform Choice.choose true
      then x
      else fromList xs

effect> :eval handle (
  handle (fromList [1,2,3]) with allChoices
) with filterExceptions
[1, 2, 3]
```

## Tips and Tricks

### 1. Understanding Effect Propagation

Effects combine through operations:

```
effect> :type perform State.get () + perform IO.read ()
Nat ! {State Nat, IO}

# Effects union: {State Nat} ∪ {IO} = {State Nat, IO}
```

### 2. Handler Order Matters

Different orders give different semantics:

```
# State outer, Exception inner
handle (handle f with exceptionH) with stateH
# State changes visible even if exception thrown

# Exception outer, State inner
handle (handle f with stateH) with exceptionH
# State changes rolled back on exception
```

### 3. Row Variable Instantiation

```
effect> :let poly = Λρ. λ_. ()
poly : ∀ρ. Unit -> Unit ! ρ

effect> :type poly [{}]
Unit -> Unit ! {}

effect> :type poly [{State}]
Unit -> Unit ! {State}
```

### 4. Debugging Effect Mismatches

Use `:type` to check effects:

```
effect> :type myFunction
Unit -> Nat ! {State, IO}

# If error: "Expected {State} but got {State, IO}"
# Fix: Handle IO or add IO to expected type
```

### 5. Testing with Mock Handlers

```
# Production
handle app with realIO

# Testing
handle app with mockIO

# Same code, different behavior!
```

## Exercises

Try these in the REPL:

### Exercise 1: Basic Effects
Determine the effect of:
```
λ_. perform State.get () + 1
λ_. if perform State.get () > 0 then perform IO.print 1 else ()
```

### Exercise 2: Write a Handler
Write a handler that counts State operations:
```
countStateOps : (Unit -> A ! {State | ρ}) -> (A, Nat) ! ρ
```

### Exercise 3: Effect Composition
Combine State and IO to implement a logging counter.

### Exercise 4: Nondeterminism
Use Choice to find all pairs (x, y) where x + y = 10.

### Exercise 5: Custom Effect
Design a Logger effect with operations:
- `log : String -> Unit`
- `warn : String -> Unit`

Implement a handler that collects messages.

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected '!'`

**Solution**: Ensure proper effect annotation syntax: `T ! ε`

### Effect Mismatch

**Problem**: "Effect mismatch: expected {...} but got {...}"

**Debug**:
```
effect> :type <your-expr>
# Check actual effects

effect> :row <your-row>
# Check row is well-formed
```

### Handler Not Matching

**Problem**: Handler doesn't intercept operations

**Solutions**:
1. Check effect name case: `State` not `state`
2. Ensure handler wraps computation
3. Verify operation names match exactly

### Continuation Type Errors

**Problem**: "Cannot call continuation with type X"

**Solution**: Ensure continuation called with correct type:
```
State.get : Unit -> s
# So k expects type s

get () k -> k "hello"  -- Error if s is Nat
get () k -> k 42       -- Correct if s is Nat
```

## Further Reading

- [Chapter 12 README](README.md) - Complete theory and formal rules
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step tutorial
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- Koka documentation - Production effect system
- "Handlers in Action" paper - Effect handlers guide

## Next Steps

After mastering the effect systems REPL:
- Chapter 13: Gradual Typing (mix static and dynamic)
- Study Koka for real-world effects
- Explore OCaml 5 effects for concurrency
- Compare to Haskell monad transformers

Have fun making effects explicit!
