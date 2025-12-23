# Chapter 12: Effect Systems - Quick Start

## TL;DR (30 seconds)

Effect systems track computational side effects (like state, I/O, exceptions) in the type system, making effects explicit and composable. This chapter teaches algebraic effects with handlers, where you define effects by their operations and give them meaning through handlers.

**Who**: Those who understand types and want to manage side effects precisely
**Time**: 2-3 weeks (or 1 intensive week)
**Payoff**: Explicit effect tracking, modular interpreters, testable side effects

## What You'll Build

- Type checker with effect tracking
- Effect handlers as interpreters
- Row polymorphism for effects
- Understanding of algebraic effects
- Comparison to monads

**Tangible Outcome**: Write programs where effects are explicit in types and swappable via handlers!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-12-effect-systems
stack build
stack exec effect-repl
```

You should see:
```
Welcome to the Effect Systems REPL!
effect>
```

### Step 2: Your First Effect (1 minute)

```
effect> :type λx : Unit. perform State.get ()
Unit -> s ! {State s}
```

Congrats! This is a stateful computation!

### Step 3: See Available Effects (1 minute)

```
effect> :effects
Available effects:
  State s: get, put
  Exception: throw
  IO: print, read
  Choice: choose
```

### Step 4: Use an Effect Handler (1 minute)

```
effect> :eval handle (perform State.get () + 1) with runState 0
1

effect> :eval handle (perform State.get () + 1) with runState 5
6
```

The handler provides the interpretation!

## Your First Success - Stateful Counter (10 minutes)

Follow this mini-tutorial to cement your understanding:

### 1. Define a Stateful Function

```
effect> :let counter = λ_. let n = perform State.get () in
                            perform State.put (n + 1);
                            n
counter : Unit -> Nat ! {State Nat}
```

### 2. What Does the Type Mean?

- `Unit -> Nat`: Takes unit, returns Nat
- `! {State Nat}`: May use State effect with Nat state

The effect is explicit in the type!

### 3. Run with a Handler

```
effect> :eval handle (counter ()) with runState 0
0

effect> :eval handle (counter (); counter ()) with runState 0
1
```

The handler interprets State operations!

### 4. Try Multiple Effects

```
effect> :let logAndCount = λ_.
          perform IO.print (perform State.get ());
          perform State.put (perform State.get () + 1)
logAndCount : Unit -> Unit ! {State Nat, IO}

effect> :eval handle (
          handle (logAndCount ()) with runState 0
        ) with collectIO
Prints: [0], Result: ((), 1)
```

**Achievement Unlocked**: You just composed two effects!

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - gentle introduction to effects and handlers
2. Follow `LESSON_PLAN.md` - structured 14-18 hour course
3. Use `REPL_GUIDE.md` as reference when stuck
4. Try the first 5 exercises in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Focus on handler semantics and continuations
3. Work through exercises 1-10 (2-3 hours)
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all the examples
2. Write custom effect handlers
3. Experiment with handler order
4. Compare to Haskell's monad transformers

## When to Skip This Chapter

**Skip if**:
- You're already comfortable with algebraic effects
- You've used Koka or Eff extensively
- You just want gradual typing (jump to Chapter 13)

**Don't skip if**:
- This is your first time with effect systems
- You want to understand effect handlers
- You're interested in modular side effects

## Quick Reference

```bash
# Build
cd chapter-12-effect-systems && stack build

# Run REPL
stack exec effect-repl

# Essential REPL Commands
:help                    # Show help
:type <expr>             # Check type with effects
:effects                 # List available effects
:eval <expr>             # Evaluate expression
:trace                   # Show evaluation steps
:quit                    # Exit

# Effect Syntax
T ! {}                   # Pure (no effects)
T ! {State}              # Uses State
T ! {State, IO}          # Uses State and IO
∀ρ. T ! ρ                # Effect-polymorphic

# Performing Effects
perform State.get ()     # Read state
perform State.put 5      # Write state
perform IO.print 42      # Print output
perform Exception.throw () # Throw exception

# Handlers
handle <expr> with {
  Effect:
  return x -> ...        # Handle pure value
  op p k -> ...          # Handle operation (k = continuation)
}
```

## Core Concepts in 2 Minutes

### 1. Effect Annotations
`T ! ε` = type T with effects ε

**Example**: `Int ! {State}` means "Int value from stateful computation"

### 2. Effect Tracking
Effects propagate through function calls:

```
f : A -> B ! {State}
g : B -> C ! {IO}
g (f x) : C ! {State, IO}  -- Both effects!
```

### 3. Effect Operations
Effects are defined by what you can do:

```
State:
  get : Unit -> s
  put : s -> Unit
```

### 4. Effect Handlers
Handlers give meaning to operations:

```
handle <computation> with {
  State:
  return x -> (x, finalState)
  get () k -> k currentState
  put newS k -> <continue with newS>
}
```

The handler interprets the effect!

### 5. Continuations
In handler `op p k`:
- `p` is the parameter
- `k` is "the rest of the computation"
- Call `k v` to resume with value `v`

## Success Criteria

You're ready for Chapter 13 when you can:
- [ ] Read effect-annotated types
- [ ] Understand effect rows and polymorphism
- [ ] Write basic effect handlers
- [ ] Explain what a continuation is
- [ ] Complete exercises 1-8

**Minimum**: Understand effect tracking and basic handlers
**Ideal**: Complete all exercises and write custom effects

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

### Q: How are effects different from exceptions?
**A**: Effects are more general:
- Exceptions: One-way (can't resume)
- Effects: Resumable (handler can continue)
- Effects: User-defined
- Effects: Composable

Exceptions are a special case where you don't call the continuation.

### Q: What's a continuation?
**A**: The "rest of the computation." When you `perform State.get ()`, execution pauses and creates a continuation representing "what happens next."

```
perform State.get () + 1
-- Continuation: k = λv. v + 1
```

### Q: How does this relate to monads?
**A**: Similar goals, different approaches:

| Monads | Effects |
|--------|---------|
| Wrap values: `M a` | Annotate types: `T ! ε` |
| Fixed semantics | Handler-defined |
| Transformers | Row polymorphism |

Effects make side effects more explicit and modular.

### Q: Can I use this in real code?
**A**: Yes! See:
- **Koka**: Full language with effects
- **OCaml 5**: Algebraic effects for concurrency
- **Eff**: Research language
- **Unison**: Abilities (similar)

## First Exercises to Try

After the quick start, try these from `exercises/EXERCISES.md`:

1. **Exercise 1**: Determine effects of expressions
2. **Exercise 2**: Write simple effect handlers
3. **Exercise 3**: Use effect polymorphism
4. **Exercise 4**: Compose multiple effects
5. **Exercise 5**: Design a custom effect

## What Makes This Chapter Special

Unlike monads, algebraic effects let you:
- **See effects in types**: `T ! {State, IO}` is explicit
- **Swap implementations**: Different handlers, same code
- **Compose naturally**: Row polymorphism
- **Define custom effects**: User-extensible
- **Resume or abort**: Full control via continuations

## Real-World Applications

Effect systems are used for:
- **Concurrency**: OCaml 5's fibers
- **Async/await**: Effect-based implementation
- **Testing**: Mock effects with test handlers
- **Dependency injection**: Abstract over implementations
- **Transactions**: Rollback semantics

## The "Aha!" Moment

Most students have their breakthrough when they realize:

> "Handlers are just interpreters for my effects!"

When you write a handler, you're defining what an effect MEANS. The same effect can have multiple interpretations:

```
# Production: Real IO
handle app with realIO

# Testing: Mock IO
handle app with mockIO

# Logging: Collect operations
handle app with traceIO
```

## Effect Design Pattern

```
1. Define operations    (what can you do?)
2. Write effect type    (signatures)
3. Implement handlers   (interpretations)
4. Use polymorphically  (∀ρ. ... ! ρ)
```

Example - Logger:
```
1. Operations: log, warn, error
2. Types: String -> Unit
3. Handlers: collect, print, ignore
4. Use in any effectful context
```

## Your Journey

```
Monads → Effect Systems → Algebraic Effects
  ↑           ↑                    ↑
Explicit   Modular           User-Defined
```

Effect systems make side effects:
- **Explicit**: In the type signature
- **Modular**: Swappable handlers
- **Compositional**: Row polymorphism

Good luck! You're learning a cutting-edge approach to managing computational effects!
