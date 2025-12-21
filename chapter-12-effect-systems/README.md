# Chapter 12: Effect Systems

## Overview

This chapter introduces **algebraic effect systems**, which track computational effects (like state, exceptions, I/O) in the type system. Effect systems allow precise reasoning about what side effects a computation may perform.

## Core Concepts

### What Are Effects?

Effects represent computational side effects:
- **State**: Reading and writing mutable state
- **Exception**: Throwing and catching errors
- **I/O**: Input/output operations
- **Nondeterminism**: Making choices

Traditional type systems don't distinguish pure functions from effectful ones. Effect systems add this distinction to types.

### Key Ideas

1. **Effect Tracking**: Types annotate what effects a computation may perform
2. **Effect Rows**: Collections of effects, supporting polymorphism
3. **Algebraic Effects**: Effects defined by their operations
4. **Effect Handlers**: Interpret effect operations with custom semantics

## Syntax

### Types

```
T ::= Unit | Bool | Nat             -- Base types
    | T₁ -> T₂ ! ε                   -- Effectful function
    | ∀ρ. T                          -- Effect polymorphism
```

### Effect Rows

```
ε ::= {}                             -- Pure (no effects)
    | {E₁, E₂, ...}                  -- Concrete effects
    | {E | ρ}                        -- Effect plus row variable
    | ρ                              -- Row variable
```

### Terms

```
t ::= x | λx : T. t | t₁ t₂          -- Core lambda calculus
    | perform E.op t                  -- Perform effect operation
    | handle t with h                 -- Handle effects
    | return t                        -- Pure value in effectful context
    | Λρ. t | t [ε]                   -- Effect abstraction/application
```

### Handlers

```
handler {
  E:
  return x -> body                   -- Handle pure values
  op₁ p k -> body                    -- Handle operation (p=param, k=continuation)
  op₂ p k -> body
  ...
}
```

## Type System

### Effect Tracking Rule

The key judgment is `Γ ⊢ t : T ! ε` meaning "t has type T with effects ε".

```
   Γ, x:A ⊢ t : B ! ε
  ─────────────────────── (Lam)
  Γ ⊢ λx:A. t : A -> B!ε ! {}

   Γ ⊢ t₁ : A -> B!ε₁ ! ε₂    Γ ⊢ t₂ : A ! ε₃
  ───────────────────────────────────────────── (App)
          Γ ⊢ t₁ t₂ : B ! ε₁ ∪ ε₂ ∪ ε₃
```

### Effect Operations

```
   op : A -> B ∈ E
  ────────────────────────────────── (Perform)
  Γ ⊢ perform E.op t : B ! {E}
```

### Effect Handlers

```
   Γ ⊢ t : A ! {E | ε}    handler h handles E
  ──────────────────────────────────────────── (Handle)
     Γ ⊢ handle t with h : B ! ε
```

Handlers "catch" effect operations and provide implementations.

## Built-in Effects

### State

```
State:
  get : Unit -> Nat      -- Read current state
  put : Nat -> Unit      -- Update state
```

### Exception

```
Exception:
  throw : Unit -> Unit   -- Raise exception
```

### IO

```
IO:
  print : Nat -> Unit    -- Print to output
  read : Unit -> Nat     -- Read from input
```

### Choice

```
Choice:
  choose : Bool -> Bool  -- Nondeterministic choice
```

## Examples

### Pure vs Effectful Functions

```
-- Pure: no effects
add : Nat -> Nat -> Nat ! {}
add = λx. λy. x + y

-- Effectful: uses State
increment : Unit -> Nat ! {State}
increment = λ_. let n = perform State.get () in
                perform State.put (succ n);
                n
```

### Effect Polymorphism

```
-- Works with any additional effects
map : ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ
```

### Simple Handler

```
-- Handler that runs State with initial value 0
runState : (Unit -> A ! {State}) -> A
runState = λf. handle f () with {
  State:
  return x -> x
  get () k -> k 0 0
  put n k -> k () n
}
```

## Algebraic Effects Theory

### Why "Algebraic"?

Effects are algebraic in the sense that:
1. Operations are defined by signatures (parameter type → return type)
2. Handlers give semantics via equations
3. Effects compose algebraically (effect rows)

### Continuation-Based Semantics

When an operation is performed:
1. Execution suspends at that point
2. A continuation captures "what happens next"
3. Handler receives the operation and continuation
4. Handler decides how to resume (or not)

```
perform State.get ()
-- Creates continuation: k = λresult. <rest of computation>
-- Handler receives: get, (), k
-- Handler can: k 42  (resume with value 42)
```

### Deep vs Shallow Handlers

- **Deep handlers**: Re-handle effects in continuation (our implementation)
- **Shallow handlers**: Only handle first occurrence

## Implementation Highlights

### TypeCheck.hs

```haskell
data TypeAndEffect = TypeAndEffect Type EffectRow

-- Effect row operations
rowContains :: EffectLabel -> EffectRow -> Bool
rowUnion :: EffectRow -> EffectRow -> EffectRow
rowRemove :: EffectLabel -> EffectRow -> EffectRow
```

### Effect Propagation

Effects propagate through function application:
```haskell
-- In application t₁ t₂:
-- Result effects = effects of t₁ ∪ effects of t₂ ∪ effects of function body
```

## Running the REPL

```bash
stack build
stack exec effect-repl
```

Example session:
```
effect> :type λx : Unit. perform State.get ()
Unit -> Nat ! {State}

effect> :effects
Available effects:
  State: get, put
  Exception: throw
  IO: print, read
  Choice: choose
```

## Connections to Real Languages

- **Koka**: Full algebraic effects with row polymorphism
- **Eff**: Research language for effects
- **OCaml 5**: Algebraic effects for concurrency
- **Haskell**: Monad transformers (different approach)
- **Scala 3**: Contextual effects (capabilities)

## Exercises

See `exercises/EXERCISES.md` for:
- Understanding effect rows
- Writing handlers
- Effect polymorphism
- Implementing new effects

## Key Theorems

1. **Effect Safety**: Well-typed programs only perform declared effects
2. **Handler Soundness**: Handled effects are correctly eliminated from type
3. **Effect Polymorphism**: Functions can be generic over effects

## References

### Foundational Papers

- **Plotkin & Power, "Algebraic Operations and Generic Effects" (2003)**
  The foundational work connecting algebraic theories to computational effects.
  [SpringerLink](https://link.springer.com/article/10.1023/A:1023064908962) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=16568227622307798680)

- **Plotkin & Pretnar, "Handlers of Algebraic Effects" (2009/2013)**
  Introduces effect handlers as a way to give semantics to algebraic effects.
  [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-642-00590-9_7) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=4536791881782624346)

### Modern Implementations

- **Leijen, "Type Directed Compilation of Row-typed Algebraic Effects" (2017)**
  Describes the implementation of algebraic effects in Koka.
  [ACM DL](https://dl.acm.org/doi/10.1145/3009837.3009872) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=11388528867398825209)

- **Bauer & Pretnar, "Programming with Algebraic Effects and Handlers" (2015)**
  Practical guide to programming with effects in the Eff language.
  [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S2352220814000194) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=3199828159824773009)

- **Hillerström & Lindley, "Liberating Effects with Rows and Handlers" (2016)**
  Combines row polymorphism with effect handlers for expressive effect typing.
  [ACM DL](https://dl.acm.org/doi/10.1145/2976022.2976033) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=5312148128218498295)

## Project Structure

```
chapter-12-effect-systems/
├── src/
│   ├── Syntax.hs      -- Types, effects, terms, handlers
│   ├── TypeCheck.hs   -- Effect tracking type checker
│   ├── Eval.hs        -- Evaluation with handler semantics
│   ├── Parser.hs      -- Parser for effect syntax
│   └── Pretty.hs      -- Pretty printer
├── app/
│   └── Main.hs        -- REPL
├── test/
│   └── Spec.hs        -- Test suite (61 tests)
├── exercises/
│   └── EXERCISES.md   -- Practice exercises
├── package.yaml       -- Package configuration
├── stack.yaml         -- Stack configuration
└── README.md          -- This file
```
