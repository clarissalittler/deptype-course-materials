# Chapter 12: Effect Systems - Frequently Asked Questions

## Conceptual Questions

### Q: What are algebraic effects?

**A:** Algebraic effects are a way to represent and handle computational side effects in a structured manner. They consist of:

1. **Effect operations**: The interface (e.g., `get`, `put` for State)
2. **Effect handlers**: The implementation/interpretation

Unlike monads, effects are:
- Declared by operations they support
- Given meaning by handlers
- Naturally composable via effect rows

### Q: Why "algebraic"?

**A:** The name comes from the algebraic structure of effects:

1. **Operations are algebraic**: Defined by signatures, not implementations
2. **Handlers give equations**: Define how operations compute
3. **Effects form an algebra**: Compose with laws

This is analogous to how algebras in mathematics are structures defined by operations and equations.

### Q: How are effects different from monads?

**A:** Key differences:

| Monads | Algebraic Effects |
|--------|------------------|
| Values wrapped: `M a` | Types annotated: `T ! ε` |
| Fixed semantics | Handler-defined semantics |
| Transformers for combining | Row polymorphism |
| Bind/return interface | Perform/handle interface |
| Effect hidden in M | Effect visible in type |

Example - State:
```
-- Monad approach
get :: State s s
put :: s -> State s ()

-- Effect approach
get : Unit -> s ! {State s}
put : s -> Unit ! {State s}
```

### Q: What is a continuation?

**A:** A continuation represents "the rest of the computation." When you perform an effect operation:

```
perform State.get () + 1
```

This creates continuation `k = λv. v + 1`. The handler receives `k` and can:
- Call `k v` to resume with value v
- Not call `k` to abort
- Call `k` multiple times for nondeterminism

### Q: Why use effect systems over exceptions?

**A:** Effect systems are more general:

1. **Resumable**: Can continue after handling
2. **Typed**: Effects in the type signature
3. **Composable**: Multiple effects work together
4. **User-defined**: Create your own effects

Exceptions are special case where you never resume.

## Technical Questions

### Q: How does effect typing work?

**A:** The typing judgment is `Γ ⊢ t : T ! ε`:
- t has type T
- May perform effects in ε

Key rules:
- Lambda creation is pure
- Application combines effects
- `perform E.op` adds E to effects
- `handle` removes handled effect

### Q: What is row polymorphism?

**A:** Row polymorphism lets functions be generic over effects:

```
map : ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ
```

The row variable `ρ` can be any effect row. This works with:
- Pure functions (ρ = {})
- State functions (ρ = {State})
- Any combination

### Q: How do handlers remove effects?

**A:** When you handle an effect:

```
handle t with {E: ...}
```

If t has type `A ! {E | ρ}`, the result has type `B ! ρ`.
The handled effect E is removed!

The handler "catches" all E operations and provides implementations.

### Q: Can I have multiple handlers?

**A:** Yes! Handlers compose:

```
handle (handle t with stateH) with exceptionH
```

Order can matter for semantics (which effect is interpreted first).

### Q: What's the difference between deep and shallow handlers?

**A:**
- **Deep**: Handler automatically re-handles effects in continuation
- **Shallow**: Handler only handles first occurrence

Most systems (including ours) use deep handlers.

### Q: How do I implement State correctly?

**A:** State handler threads state through continuations:

```
runState : S -> (Unit -> A ! {State S | ρ}) -> (A, S) ! ρ
runState s computation =
  handle (computation ()) with {
    State:
    return x -> (x, s)        -- Final state
    get () k -> k s           -- Provide current state
    put newS k ->             -- Update state
      runState newS (λ_. k ())
  }
```

Note: For recursive effects, the handler calls itself.

### Q: Can effects express async/await?

**A:** Yes! Define an Async effect:

```
Async:
  await : Promise a -> a
  spawn : (Unit -> a ! {Async}) -> Promise a
```

Handler manages execution:
- `await` suspends until promise resolves
- `spawn` creates concurrent computation
- Handler is the runtime scheduler

### Q: How do effects help with testing?

**A:** Effects let you swap implementations:

**Production**:
```
handle app with {
  DB: actual database
  HTTP: real network
}
```

**Testing**:
```
handle app with {
  DB: in-memory mock
  HTTP: fake responses
}
```

Same code, different handlers!

## Common Confusions

### Q: Is `{}` (pure) an effect?

**A:** `{}` is the empty effect row, meaning "no effects." It's the identity for effect composition:
- `{} ∪ E = E`
- `E ∪ {} = E`

Pure functions have effect `{}`.

### Q: Do effect rows have order?

**A:** No! Effect rows are sets:
```
{State, IO} = {IO, State}
```

Order doesn't matter for typing.

### Q: Can I catch effects I don't have?

**A:** Handling an effect that's not there is harmless but pointless:

```
handle (5) with stateHandler  -- No State effect, handler unused
```

The code works, but handler is dead code.

### Q: What if I don't handle an effect?

**A:** Unhandled effects remain in the type:

```
f : Unit -> Nat ! {State}
-- No handler, so State must be handled elsewhere

main : Unit -> Nat ! {}
main = λ_. handle (f ()) with stateHandler  -- Handle here
```

Eventually, main programs must handle all effects.

## Troubleshooting

### Q: "Effect mismatch" error

**A:** Common causes:

1. **Missing effect in type**:
   ```
   f : Unit -> Nat ! {}
   f = λ_. perform State.get ()  -- Error! Missing State
   ```

2. **Extra effect in type**:
   ```
   f : Unit -> Nat ! {State}
   f = λ_. 5  -- Warning: claims State but doesn't use it
   ```

Fix: Match declared effects to actual effects.

### Q: "Cannot unify row variables"

**A:** Row variable mismatch:
```
f : ∀ρ. A ! ρ -> A ! ρ
g : A ! {State} -> A ! {IO}  -- Different effects!
```

Fix: Ensure row variables match or use concrete effects.

### Q: Handler not intercepting effects

**A:** Check:
1. Correct effect label in handler
2. Handler wraps the effectful computation
3. Operation names match exactly

```
-- Wrong: effect name mismatch
handle ... with { state: get () k -> ... }  -- lowercase 'state'

-- Correct
handle ... with { State: get () k -> ... }  -- matches effect State
```

### Q: Continuation type error

**A:** Ensure k is called with correct type:

```
State.get : Unit -> Nat
-- So k expects Nat

get () k -> k "hello"  -- Error: String not Nat
get () k -> k 42       -- Correct: Nat
```

### Q: Effects not composing

**A:** Check row extension syntax:
```
-- This adds State to whatever ρ contains
{State | ρ}

-- Use in types
f : ∀ρ. A ! {State | ρ} -> B ! ρ
```

This says: "handles State, passes through other effects."
