# Chapter 12: Effect Systems - Tutorial

This tutorial walks through algebraic effect systems with step-by-step examples.

## Part 1: Why Effect Systems?

### The Problem

Consider these functions:
```
add : Int -> Int -> Int
add x y = x + y

getCounter : Unit -> Int
getCounter () = <reads some global counter>
```

Both have type `... -> Int`, but they're fundamentally different:
- `add` is pure: same inputs always give same output
- `getCounter` has a side effect: reads mutable state

**Problem**: Simple types don't distinguish pure from effectful.

### The Solution

Effect systems add effect annotations to types:
```
add : Int -> Int -> Int ! {}           -- Pure (no effects)
getCounter : Unit -> Int ! {State}     -- Uses State effect
```

Now the type tells us what might happen!

## Part 2: Effect Types

### Basic Syntax

An effect-annotated type has the form:
```
T ! ε
```
Where:
- `T` is the result type
- `ε` is the effect row (set of effects)

### Examples

```
Int ! {}                -- Pure Int value
String ! {IO}           -- String with IO effect
Bool ! {State, Exception}  -- Bool with State and Exception
```

### Effect Rows

Effect rows are sets of effects:
```
{}                      -- Empty (pure)
{State}                 -- Just State
{State, IO}             -- Both State and IO
{E | ρ}                 -- Effect E plus row variable ρ
```

### Function Types

Functions track effects in the return type:
```
A -> B ! ε              -- Takes A, returns B with effects ε

Int -> Int ! {}         -- Pure function
Int -> Int ! {State}    -- Stateful function
```

## Part 3: Effect Operations

### Defining Effects

An effect is defined by its operations:

```
State:
  get : Unit -> Nat       -- Read current state
  put : Nat -> Unit       -- Write new state

Exception:
  throw : Unit -> Unit    -- Raise an exception

IO:
  print : Nat -> Unit     -- Output a number
  read : Unit -> Nat      -- Input a number

Choice:
  choose : Bool -> Bool   -- Nondeterministic choice
```

### Performing Operations

Use `perform` to execute an effect operation:

```
perform State.get ()     -- Returns current state value
perform State.put 42     -- Sets state to 42
perform Exception.throw ()  -- Raises exception
```

### Effect Typing

When you perform an operation, you incur that effect:

```
perform State.get () : Nat ! {State}
perform IO.print 5 : Unit ! {IO}
```

### Worked Example

What's the type of this function?

```
counter : Unit -> Nat ! ???
counter = λ_.
  let n = perform State.get () in
  perform State.put (n + 1);
  n
```

Analysis:
1. `perform State.get ()` has type `Nat ! {State}`
2. `perform State.put (n + 1)` has type `Unit ! {State}`
3. Return `n` of type `Nat`
4. Combined: `Unit -> Nat ! {State}`

## Part 4: Effect Propagation

### How Effects Combine

Effects accumulate through the program:

**Sequencing**:
```
let x = t₁ in t₂
-- Effects: effects(t₁) ∪ effects(t₂)
```

**Application**:
```
f x
-- Effects: effects(f) ∪ effects(x) ∪ effects(f's body)
```

### Example

```
example : Unit -> Unit ! ???
example = λ_.
  perform State.put 0;      -- {State}
  perform IO.print 5;       -- {IO}
  ()
```

Combined effects: `{State, IO}`

Result type: `Unit -> Unit ! {State, IO}`

### Pure Functions

Creating a lambda is always pure:
```
λx. perform State.get ()
-- Type: Nat -> Nat ! {State}
-- But creating this function: ! {}
```

The effects happen when the function is CALLED.

## Part 5: Effect Handlers

### What Handlers Do

Handlers "catch" effect operations and provide implementations:

```
handle <computation> with {
  <Effect>:
  return x -> <what to do with result>
  op₁ p k -> <how to handle op₁>
  op₂ p k -> <how to handle op₂>
}
```

### The Continuation

In `op p k`:
- `p` is the operation's parameter
- `k` is the continuation ("rest of computation")

```
handle (perform State.get () + 1) with {
  State:
  return x -> x
  get () k -> k 0        -- Resume with value 0
  put n k -> k ()
}
```

Execution:
1. `perform State.get ()` triggers handler
2. Handler calls `k 0` (continue with 0)
3. Continuation computes `0 + 1`
4. Result: `1`

### State Handler Example

Implementing stateful computation:

```
runState : S -> (Unit -> A ! {State | ρ}) -> A ! ρ
runState init f = handle (f ()) with {
  State:
  return x -> x
  get () k -> k init      -- Return current state
  put n k -> k ()         -- (simplified: ignores new state)
}
```

Better version (threads state):
```
runStateWith : S -> (Unit -> A ! {State | ρ}) -> (A, S) ! ρ
runStateWith s computation =
  handle (computation ()) with {
    State:
    return x -> (x, s)           -- Return value with final state
    get () k -> k s              -- Resume with state
    put newS k -> runStateWith newS (λ_. k ())  -- Update and continue
  }
```

### Exception Handler

```
tryCatch : (Unit -> A ! {Exception | ρ}) -> A -> A ! ρ
tryCatch computation default =
  handle (computation ()) with {
    Exception:
    return x -> x                -- Normal return
    throw () k -> default        -- Don't call k, return default
  }
```

Not calling `k` aborts the computation!

## Part 6: Effect Polymorphism

### The Problem

Without polymorphism:
```
map_pure : (A -> B ! {}) -> List A -> List B ! {}
map_state : (A -> B ! {State}) -> List A -> List B ! {State}
map_io : (A -> B ! {IO}) -> List A -> List B ! {IO}
-- Redundant!
```

### Row Variables

Use a row variable to abstract over effects:
```
map : ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ
```

This works with ANY effect row!

### Effect Abstraction

```
Λρ. λf : A -> B ! ρ. ...    -- Abstract over effect row
expr [ε]                     -- Instantiate with concrete effects
```

### Example

```
-- Polymorphic twice
twice : ∀ρ. (Unit -> Unit ! ρ) -> Unit -> Unit ! ρ
twice = Λρ. λf. λ_. f (); f ()

-- Use with State
twice [{State}] increment ()

-- Use with IO
twice [{IO}] (λ_. perform IO.print 1) ()
```

### Row Extension

Add effects to a polymorphic row:
```
{State | ρ}     -- State plus whatever ρ is
```

Useful for saying "at least these effects":
```
needsState : ∀ρ. (Unit -> A ! {State | ρ}) -> A ! {State | ρ}
```

## Part 7: Handlers and Continuations

### Deep Dive into Continuations

When you `perform op`, execution stops and creates a continuation:

```
perform State.get () + 1
-- Continuation: k = λv. v + 1
-- Handler sees: get, (), k
```

### Multiple Continuations

A handler can call `k` multiple times:

```
handle (if perform Choice.choose true then 1 else 2) with {
  Choice:
  return x -> [x]
  choose b k -> k true ++ k false  -- Both branches!
}
-- Result: [1, 2]
```

### Not Calling Continuation

If handler doesn't call `k`, computation aborts:

```
handle (perform Exception.throw (); 42) with {
  Exception:
  return x -> x
  throw () k -> 0    -- Don't call k!
}
-- Result: 0 (42 never evaluated)
```

### Deep vs Shallow

**Deep handlers** (our implementation): Re-handle subsequent effects
```
handle ... with H
-- H handles ALL occurrences of the effect
```

**Shallow handlers**: Handle only first occurrence
```
-- Would need explicit re-handling for subsequent operations
```

## Practice Problems

### Problem 1: Effect Typing

What's the effect of this expression?
```
λx. perform State.get () + perform IO.read ()
```

<details>
<summary>Solution</summary>

Function type: `Nat -> Nat ! {State, IO}`

- `perform State.get ()` contributes `{State}`
- `perform IO.read ()` contributes `{IO}`
- Combined: `{State, IO}`
</details>

### Problem 2: Write a Handler

Write a handler that counts how many times `get` is called:

<details>
<summary>Solution</summary>

```
countGets : (Unit -> A ! {State | ρ}) -> (A, Nat) ! ρ
countGets computation =
  handle (computation ()) with {
    State:
    return x -> (x, 0)
    get () k ->
      let (result, count) = k 0 in
      (result, count + 1)
    put n k -> k ()
  }
```
</details>

### Problem 3: Effect Polymorphism

What's the most general type for:
```
λf. λx. f (f x)
```

<details>
<summary>Solution</summary>

```
∀ρ. (A -> A ! ρ) -> A -> A ! ρ
```

The function is applied twice, so effects accumulate, but since it's the same effect row, we just get `ρ`.

With the effect-tracking rule:
- `f x` has type `A ! ρ`
- `f (f x)` has type `A ! ρ ∪ ρ = A ! ρ`
</details>

### Problem 4: Handler Design

Design a handler for `Logger` effect that collects all log messages:

```
Logger:
  log : String -> Unit
```

<details>
<summary>Solution</summary>

```
collectLogs : (Unit -> A ! {Logger | ρ}) -> (A, List String) ! ρ
collectLogs computation =
  handle (computation ()) with {
    Logger:
    return x -> (x, [])
    log msg k ->
      let (result, msgs) = k () in
      (result, msg :: msgs)
  }
```

Each `log` call adds to the list, final result pairs value with all messages.
</details>

### Problem 5: Why Wrong?

Why doesn't this type check?
```
bad : Unit -> Nat ! {}
bad = λ_. perform State.get ()
```

<details>
<summary>Solution</summary>

`perform State.get ()` has effect `{State}`, but the function claims to be pure (`! {}`).

Fix:
```
good : Unit -> Nat ! {State}
good = λ_. perform State.get ()
```

The effect annotation must include all effects that may occur.
</details>
