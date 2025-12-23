# Chapter 17: Abstract Machines - Exercises

## Overview

These exercises help you understand abstract machines by implementing variations
and exploring their properties.

## Exercise 1: Extend the CEK Machine (Easy)

Add support for pairs to the CEK machine:

```haskell
data Term = ...
  | TmPair Term Term      -- (e1, e2)
  | TmFst Term            -- fst e
  | TmSnd Term            -- snd e

data Value = ...
  | VPair Value Value
```

Tasks:
1. Add the new term constructors to `Syntax.hs`
2. Add corresponding frames to `CEK.hs`
3. Implement the transition rules
4. Add test cases

## Exercise 2: Call-by-Name CEK (Medium)

Modify the CEK machine to implement call-by-name instead of call-by-value.

Key insight: Instead of evaluating arguments before application, pass them as thunks.

```haskell
data Thunk = Thunk Term Env

data Value = ...
  | VThunk Thunk  -- Unevaluated computation
```

Compare the behavior with call-by-value on:
- `(\x. 42) ((\y. y y) (\y. y y))`
- `(\x. x + x) (expensive_computation)`

## Exercise 3: Environment Machine (Medium)

Implement a simpler abstract machine that uses de Bruijn indices
instead of named variables. This eliminates the need for alpha-renaming.

```haskell
data Term
  = TmVar Int       -- de Bruijn index
  | TmLam Term      -- no variable name needed
  | TmApp Term Term
  | ...

type Env = [Value]  -- List lookup by index
```

## Exercise 4: Tail Call Optimization (Medium)

Modify the CEK machine to recognize and optimize tail calls.

A call is in tail position if there's nothing to do after it returns.
For tail calls, we can reuse the current continuation instead of pushing a new frame.

```haskell
-- Non-tail call: (\x. x + 1) 5
-- Tail call: (\x. (\y. y) x) 5  -- inner application is in tail position
```

Implement `isTailPosition` and modify `step` to handle tail calls.

## Exercise 5: State Monad Machine (Medium)

Extend the CEK machine with mutable state:

```haskell
data Term = ...
  | TmRef Term        -- ref e (create reference)
  | TmDeref Term      -- !e (dereference)
  | TmAssign Term Term -- e1 := e2 (assignment)

data Value = ...
  | VRef Loc          -- Reference (location in store)

type Store = Map Loc Value
type Loc = Int
```

The machine state now includes a store: `(C, E, K, S)`.

## Exercise 6: Exception Handling (Medium)

Add exception handling to the CEK machine:

```haskell
data Term = ...
  | TmThrow Term          -- throw e
  | TmCatch Term Var Term -- try e1 catch x -> e2

data Frame = ...
  | FCatch Var Term Env   -- Exception handler
```

When `throw v` is evaluated, unwind the continuation until finding a `FCatch` frame.

## Exercise 7: Continuation Marks (Hard)

Implement continuation marks (as in Racket) for the CEK machine.

Continuation marks allow attaching metadata to continuation frames:
```haskell
data Term = ...
  | TmWithMark Term Term Term  -- with-mark key val body
  | TmGetMarks Term            -- get-marks key

data Frame = ...
  | FMark Value Value  -- Mark with key and value
```

## Exercise 8: Abstract Machine for System F (Hard)

Extend the CEK machine to handle System F (polymorphic lambda calculus):

```haskell
data Term = ...
  | TmTyLam Term        -- Λα. e
  | TmTyApp Term Type   -- e [τ]

data Value = ...
  | VTyLam Term Env     -- Type abstraction closure
```

The key insight is that type application is a runtime operation.

## Exercise 9: ZAM (Zinc Abstract Machine) (Hard)

Implement a simplified version of the Zinc Abstract Machine used in OCaml:

The ZAM uses:
- Compiled bytecode instead of terms
- An accumulator register
- Multiple stacks

```haskell
data Instr
  = GRAB          -- Start of function
  | PUSH          -- Push accumulator
  | APPLY         -- Apply function
  | ACCESS Int    -- Access environment
  | ...
```

## Exercise 10: Proving Correctness (Theory)

Prove that the CEK machine correctly implements call-by-value semantics.

Define a relation between CEK states and substitution-based terms:
```
⟦Eval t ρ κ⟧ = κ[ρ(t)]
```

Prove: If `t →* v` in substitution semantics, then
`inject(t) →* Apply [] v'` where `v ≈ v'`.

## Challenge: Supercompilation

Implement a simple supercompiler that:
1. Runs the CEK machine symbolically
2. Performs deforestation (eliminating intermediate data structures)
3. Generates optimized code

Example:
```
map f (map g xs)  →  map (f . g) xs
```

## Challenge: Debugger

Build an interactive debugger for the CEK machine:
- Step forward/backward through execution
- Set breakpoints on terms
- Inspect environment and continuation
- Pretty-print the current state

## Challenge: Concurrent CEK

Extend the CEK machine to handle concurrent processes:

```haskell
data Term = ...
  | TmFork Term      -- fork e (spawn new process)
  | TmChan           -- chan (create channel)
  | TmSend Term Term -- send c v
  | TmRecv Term      -- recv c

-- Global state: list of processes
type Processes = [State]
```

Implement a round-robin scheduler.
