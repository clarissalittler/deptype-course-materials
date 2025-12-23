# Chapter 12: Effect Systems - Cheat Sheet

## Syntax at a Glance

### Effect-Annotated Types
```
T ! ε                -- Type T with effects ε
Int ! {}             -- Pure Int
String ! {IO}        -- String with IO effect
Bool ! {State, Exception}  -- Bool with State and Exception
```

### Effect Rows
```
ε ::= {}                   -- Empty (pure)
    | {E}                  -- Single effect
    | {E₁, E₂, ...}        -- Multiple effects
    | {E | ρ}              -- Effect E plus row variable ρ
    | ρ                    -- Row variable alone
```

### Function Types
```
A -> B ! ε           -- Takes A, returns B with effects ε
```

### Terms
```
perform E.op t       -- Perform effect operation
handle t with h      -- Handle effects
return t             -- Pure value in effectful context
Λρ. t                -- Effect abstraction
t [ε]                -- Effect application
```

## Built-in Effects

### State
```
State:
  get : Unit -> s      -- Read current state
  put : s -> Unit      -- Write new state
```

### Exception
```
Exception:
  throw : Unit -> Unit -- Raise an exception
```

### IO
```
IO:
  print : Nat -> Unit  -- Output a number
  read : Unit -> Nat   -- Input a number
```

### Choice
```
Choice:
  choose : Bool -> Bool  -- Nondeterministic choice
```

## Key Typing Rules

### Effect Tracking
```
Γ ⊢ t : T ! ε
```
Means: term t has type T and may perform effects ε

### Lambda (Pure Creation)
```
   Γ, x:A ⊢ t : B ! ε
  ─────────────────────── (Lam)
  Γ ⊢ λx:A. t : A -> B!ε ! {}
```
Creating a lambda is always pure!

### Application (Effect Union)
```
   Γ ⊢ t₁ : A -> B!ε₁ ! ε₂    Γ ⊢ t₂ : A ! ε₃
  ───────────────────────────────────────────── (App)
          Γ ⊢ t₁ t₂ : B ! ε₁ ∪ ε₂ ∪ ε₃
```
Effects accumulate: evaluating function + argument + body

### Perform (Introduce Effect)
```
   op : A -> B ∈ E
  ────────────────────────────────── (Perform)
  Γ ⊢ perform E.op t : B ! {E}
```

### Handle (Remove Effect)
```
   Γ ⊢ t : A ! {E | ε}    handler h handles E
  ──────────────────────────────────────────── (Handle)
     Γ ⊢ handle t with h : B ! ε
```

## Effect Handlers

### Basic Structure
```
handler {
  Effect:
  return x -> body           -- Handle pure return
  op₁ p k -> body           -- Handle operation (p=param, k=continuation)
  op₂ p k -> body
  ...
}
```

### Continuation (k)
- Represents "rest of computation"
- Call `k v` to resume with value v
- Not calling `k` aborts computation
- Can call `k` multiple times (nondeterminism)

## Common Effect Patterns

### State Handler
```
runState : S -> (Unit -> A ! {State S | ρ}) -> (A, S) ! ρ
runState s computation =
  handle (computation ()) with {
    State:
    return x -> (x, s)
    get () k -> k s
    put newS k -> runState newS (λ_. k ())
  }
```

### Exception Handler
```
tryCatch : (Unit -> A ! {Exception | ρ}) -> A -> A ! ρ
tryCatch computation default =
  handle (computation ()) with {
    Exception:
    return x -> x
    throw () k -> default  -- Don't call k!
  }
```

### IO Handler (Collect Output)
```
collectOutput : (Unit -> A ! {IO | ρ}) -> (A, [Nat]) ! ρ
collectOutput computation =
  handle (computation ()) with {
    IO:
    return x -> (x, [])
    print n k ->
      let (result, output) = k () in
      (result, n :: output)
    read () k -> k 0  -- Mock input
  }
```

### Choice Handler (All Results)
```
allChoices : (Unit -> A ! {Choice | ρ}) -> [A] ! ρ
allChoices computation =
  handle (computation ()) with {
    Choice:
    return x -> [x]
    choose b k -> k true ++ k false  -- Both branches!
  }
```

## Effect Polymorphism

### Row Variables
```
∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ
```
Works with ANY effect row!

### Row Extension
```
{E | ρ}              -- E plus whatever is in ρ
```

### Examples
```
# Pure version
map : (A -> B ! {}) -> List A -> List B ! {}

# Stateful version
map : (A -> B ! {State}) -> List A -> List B ! {State}

# Polymorphic (works for both!)
map : ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ
```

## Effect Composition

### Sequential Effects
```
do
  x <- perform State.get ()     -- {State}
  perform IO.print x             -- {State, IO}
  perform State.put (x + 1)      -- {State, IO}
-- Total: {State, IO}
```

### Nested Handlers
```
handle (
  handle computation with stateH
) with exceptionH
-- Order matters for semantics!
```

## Common Idioms

| Pattern | Effect Type | Handler Behavior |
|---------|------------|------------------|
| State | `{State S}` | Thread state through continuation |
| Exception | `{Exception}` | Don't call continuation (abort) |
| Nondeterminism | `{Choice}` | Call continuation multiple times |
| Logging | `{Logger}` | Accumulate results |
| Async | `{Async}` | Scheduler manages resumptions |

## Effect Laws

### Effect Identity
```
{} ∪ ε = ε
ε ∪ {} = ε
```

### Effect Commutativity
```
{E₁, E₂} = {E₂, E₁}
```

### Effect Idempotence
```
{E, E} = {E}
```

### Effect Associativity
```
(ε₁ ∪ ε₂) ∪ ε₃ = ε₁ ∪ (ε₂ ∪ ε₃)
```

## Comparison to Monads

| Monads | Algebraic Effects |
|--------|------------------|
| Values wrapped: `M a` | Types annotated: `T ! ε` |
| `return :: a -> M a` | `return :: a -> T ! {}` |
| `bind :: M a -> (a -> M b) -> M b` | Automatic sequencing |
| Transformers for combining | Row polymorphism |
| Fixed semantics | Handler-defined semantics |
| Effect hidden in M | Effect visible in type |

## Practical Tips

### ✓ Do
- Use effect polymorphism for reusable functions
- Handle effects at appropriate boundaries
- Think of handlers as interpreters
- Use row variables for extensibility
- Design effects by their operations

### ✗ Avoid
- Handling effects you don't have (harmless but confusing)
- Forgetting to handle effects (they propagate)
- Too many effects in one function
- Handler order confusion
- Leaking unhandled effects to main

## Quick Patterns

### Counter with State
```
counter : Unit -> Nat ! {State Nat}
counter = λ_.
  let n = perform State.get () in
  perform State.put (n + 1);
  n
```

### Retry with Exception
```
retry : (Unit -> A ! {Exception}) -> Nat -> A
retry f 0 = error "Max retries"
retry f n =
  handle (f ()) with {
    Exception:
    return x -> x
    throw () k -> retry f (n - 1)
  }
```

### Parallel Choices
```
both : (Unit -> A ! {Choice}) -> (A, A)
both f =
  handle (f ()) with {
    Choice:
    return x -> (x, x)
    choose b k -> (fst (k true), fst (k false))
  }
```

## Debugging Tips

### "Effect mismatch" Error
```
# Problem: Declared effects don't match actual
f : Unit -> Nat ! {}
f = λ_. perform State.get ()  -- ERROR: Missing {State}

# Fix: Add effect to type
f : Unit -> Nat ! {State}
f = λ_. perform State.get ()  -- OK
```

### "Unhandled effect" Warning
```
# Effects propagate upward
main : Unit -> Nat ! {}
main = counter ()  -- ERROR: {State} effect unhandled

# Fix: Handle it
main = runState 0 counter  -- OK
```

### Handler Not Working
```
# Check:
1. Correct effect name in handler
2. Handler wraps the computation
3. Operation names match exactly

# Wrong
handle ... with { state: get () k -> ... }

# Correct
handle ... with { State: get () k -> ... }
```

## REPL Commands

```bash
effect> :type λx : Unit. perform State.get ()
Unit -> s ! {State s}

effect> :effects
Available effects:
  State s: get, put
  Exception: throw
  IO: print, read
  Choice: choose

effect> :eval handle (perform State.get ()) with runState 0
0

effect> :trace
[Shows evaluation steps with effect handling]
```

## Effect Design Guidelines

### Designing an Effect

1. **Identify operations**: What can you do?
2. **Specify signatures**: Types for each operation
3. **Name the effect**: Clear, descriptive name
4. **Design handlers**: How to interpret operations

### Example: Logger Effect

```
1. Operations: log
2. Signature: log : String -> Unit
3. Name: Logger
4. Handlers:
   - Collect logs: Returns list of messages
   - Print logs: Output to console
   - Ignore logs: No-op
```

## Advanced Patterns

### Dependency Injection
```
# Define abstract effect
Database:
  query : String -> [Row]
  insert : Row -> Unit

# Production handler: Real database
# Test handler: In-memory mock
```

### Async/Await
```
Async:
  await : Promise a -> a
  spawn : (Unit -> a ! {Async}) -> Promise a

# Handler is scheduler
```

### Transactions
```
Transaction:
  begin : Unit -> Unit
  commit : Unit -> Unit
  rollback : Unit -> Unit

# Handler manages ACID properties
```

## Real-World Applications

- **Koka**: Full language with effect types
- **OCaml 5**: Algebraic effects for concurrency
- **Eff**: Research language
- **Unison**: Abilities (similar to effects)
- **Scala 3**: Contextual capabilities

## Quick Reference Card

```
Syntax:       T ! ε
Meaning:      Type T with effects ε
Pure:         T ! {}
Perform:      perform E.op t
Handle:       handle t with { E: return x -> ..., op p k -> ... }
Polymorphic:  ∀ρ. ... ! ρ
Row extend:   {E | ρ}

Remember: Effects are in the types, handlers give meaning!
```

## Common Effect Combinations

```
{State}                    -- Stateful computation
{IO}                       -- I/O operations
{Exception}                -- May throw
{State, IO}                -- Stateful I/O
{State, Exception}         -- Stateful with errors
{State, IO, Exception}     -- Full app
∀ρ. ... ! {State | ρ}      -- At least State
```

## Next Steps

After mastering effect systems:
- Chapter 13: Gradual Typing - Mix static and dynamic
- Study Koka for production effect system
- Explore effect handlers for concurrency
- Compare to monad transformers
