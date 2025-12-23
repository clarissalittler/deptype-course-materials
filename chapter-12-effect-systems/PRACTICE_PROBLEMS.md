# Chapter 12: Effect Systems - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce algebraic effect concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Effect Typing ⭐
What effects do these expressions have?

a) `λx. x + 1`
b) `λx. perform State.get ()`
c) `λx. perform IO.print x`
d) `λx. perform State.get () + perform IO.read ()`

### Problem 1.2: Effect Rows ⭐
Are these effect rows equal?

a) `{State}` and `{State}`
b) `{State, IO}` and `{IO, State}`
c) `{State, State}` and `{State}`
d) `{}` and `{State}`

### Problem 1.3: Pure or Effectful? ⭐
For each, determine if it's pure (`! {}`):

a) Creating a lambda: `λx. perform State.get ()`
b) Calling that lambda: `(λx. perform State.get ()) ()`
c) `5 + 3`
d) `if true then perform IO.print 1 else perform IO.print 2`

### Problem 1.4: Reading Types ⭐
What does each type tell you?

a) `f : Unit -> Nat ! {}`
b) `g : Unit -> Nat ! {State}`
c) `h : Unit -> Nat ! {State, IO}`
d) `i : ∀ρ. Unit -> Nat ! ρ`

### Problem 1.5: Handler Basics ⭐
What does this handler do?

```
handle (perform State.get () + 1) with {
  State:
  return x -> x
  get () k -> k 0
  put n k -> k ()
}
```

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Effect Propagation ⭐⭐
Determine the effect for each expression:

a)
```
λx. let y = perform State.get () in
    let z = perform IO.read () in
    y + z
```

b)
```
λf. λx. f (perform State.get ())
where f : Nat -> Nat ! {IO}
```

c)
```
if perform State.get () > 0
then perform IO.print 1
else perform IO.print 2
```

### Problem 2.2: Write Handlers ⭐⭐
Implement handlers for:

a) **countGets**: Count how many times `get` is called
```
countGets : (Unit -> A ! {State s | ρ}) -> (A, Nat) ! ρ
```

b) **ignoreExceptions**: Catch exceptions and return default value
```
ignoreExceptions : (Unit -> A ! {Exception | ρ}) -> A -> A ! ρ
```

c) **traceIO**: Collect all print operations
```
traceIO : (Unit -> A ! {IO | ρ}) -> (A, [Nat]) ! ρ
```

### Problem 2.3: Effect Polymorphism ⭐⭐
Write polymorphic effect types for:

a) **twice**: Apply a function twice
```
twice f x = f (f x)
```

b) **mapList**: Map a function over a list
```
mapList f [] = []
mapList f (x:xs) = f x : mapList f xs
```

c) **sequence**: Run a list of effectful computations
```
sequence [] = []
sequence (c:cs) = let x = c () in x : sequence cs
```

### Problem 2.4: Handler Composition ⭐⭐
Given:
```
stateH : Handles {State}
exceptionH : Handles {Exception}
```

What's the final effect type of:

a) `handle (f ()) with stateH`
   where `f : Unit -> A ! {State, IO}`

b) `handle (handle (g ()) with stateH) with exceptionH`
   where `g : Unit -> A ! {State, Exception}`

c) Which order handles State first: `stateH` then `exceptionH`, or vice versa?

### Problem 2.5: Continuation Usage ⭐⭐
For each handler, explain when/how the continuation is called:

a) Exception handler (abort on throw)
b) State handler (thread state)
c) Choice handler (both branches)
d) Logger handler (accumulate logs)

### Problem 2.6: Effect Design ⭐⭐
Design effects for:

a) **Random numbers**: Operations and their types
b) **Database**: Query, insert, update operations
c) **File system**: Read, write, delete operations

For each:
- List operations
- Give type signatures
- Describe one possible handler

### Problem 2.7: Type Inference ⭐⭐
Infer the most general effect type:

a)
```
λf. λg. λx. g (f x)
```

b)
```
λb. λt. λe. if b then t () else e ()
```

c)
```
λxs. case xs of
  [] -> ()
  (x:xs) -> perform IO.print x; iter xs
```

### Problem 2.8: Row Variable Usage ⭐⭐
Complete these types with appropriate row variables:

a)
```
needsState : ∀ρ. ??? -> Nat ! ???
needsState = λ_. perform State.get ()
```

b)
```
addIO : ∀ρ. (Unit -> A ! ρ) -> Unit -> A ! ???
addIO f = λ_. perform IO.print 0; f ()
```

c)
```
keepEffects : ∀ρ. (Unit -> A ! ρ) -> Unit -> A ! ???
keepEffects f = λ_. f ()
```

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Advanced State ⭐⭐⭐
Implement a state handler that:
- Maintains state of type `S`
- Starts with initial state
- Returns final state with result
- Properly threads state through continuations

```
runStateWith : S -> (Unit -> A ! {State S | ρ}) -> (A, S) ! ρ
```

Test with a function that uses get and put multiple times.

### Problem 3.2: Nondeterminism ⭐⭐⭐
Implement these choice handlers:

a) **allResults**: Return all possible results
```
allResults : (Unit -> A ! {Choice | ρ}) -> [A] ! ρ
```

b) **firstResult**: Return first successful result (use Exception for failure)
```
firstResult : (Unit -> A ! {Choice, Exception | ρ}) -> Maybe A ! ρ
```

c) **countChoices**: Count how many nondeterministic choices are made
```
countChoices : (Unit -> A ! {Choice | ρ}) -> (A, Nat) ! ρ
```

### Problem 3.3: Effect Interaction ⭐⭐⭐
Consider State and Exception together:

a) If exception is thrown, should state changes be rolled back?
b) Implement two handlers showing different semantics:
   - `stateBeforeException`: State changes persist
   - `exceptionBeforeState`: State changes rollback

c) Explain why handler order matters

### Problem 3.4: Async/Await ⭐⭐⭐
Design and implement an Async effect:

```
Async:
  await : Promise a -> a
  async : (Unit -> a ! {Async}) -> Promise a
```

a) What should the handler maintain (internal state)?
b) How does `await` suspend computation?
c) How does `async` create a new promise?
d) Implement a simple scheduler handler

### Problem 3.5: Effect Subsumption ⭐⭐⭐
Prove or disprove these subtyping relationships:

a) `A ! {}` <: `A ! {State}`
b) `A ! {State}` <: `A ! {}`
c) `A ! {State}` <: `A ! {State, IO}`
d) `∀ρ. A ! ρ` <: `A ! {State}`

Explain the variance of effects in function types.

---

## Debugging Exercises (30 minutes)

### Debug 1: Effect Mismatch ⭐
Fix the type error:

```
f : Unit -> Nat ! {}
f = λ_. perform State.get ()  -- ERROR!
```

### Debug 2: Unhandled Effects ⭐⭐
Why doesn't this work?

```
main : Unit -> Nat ! {}
main = λ_.
  let x = perform State.get () in
  x + 1
```

### Debug 3: Handler Not Matching ⭐⭐
This handler doesn't work. Why?

```
handle (perform State.get ()) with {
  state:  -- Wrong case!
  return x -> x
  get () k -> k 0
}
```

### Debug 4: Continuation Type Error ⭐⭐
This handler has a type error:

```
handle (perform State.get ()) with {
  State:
  return x -> x
  get () k -> k "hello"  -- ERROR: String not Nat
  put n k -> k ()
}
```

What's wrong and how to fix?

### Debug 5: Effect Row Issues ⭐⭐
Why doesn't this type check?

```
f : ∀ρ. A ! ρ -> A ! ρ
f x = perform State.get (); x
```

---

## Code Review Exercises (30 minutes)

### Review 1: State Handler ⭐⭐
Review this state handler:

```
runState : S -> (Unit -> A ! {State S}) -> A
runState s f =
  handle (f ()) with {
    State:
    return x -> x
    get () k -> k s
    put newS k -> k ()  -- Ignores new state!
  }
```

Questions:
- What's wrong with this implementation?
- Does it properly thread state?
- How to fix it?

### Review 2: Exception Handler ⭐⭐
Compare two exception handlers:

**Version A**:
```
tryA f =
  handle (f ()) with {
    Exception:
    return x -> Just x
    throw () k -> Nothing  -- Don't call k
  }
```

**Version B**:
```
tryB f =
  handle (f ()) with {
    Exception:
    return x -> Just x
    throw () k -> Just (k ())  -- Call k!
  }
```

Which is correct? Why?

### Review 3: Effect Polymorphism ⭐⭐
A student wrote:

```
mapList : (A -> B) -> List A -> List B
mapList f [] = []
mapList f (x:xs) = f x : mapList f xs
```

Suggest improvements for:
- Effect polymorphism
- Handling effectful functions

### Review 4: Handler Design ⭐⭐⭐
Review this logger design:

```
Logger:
  log : String -> Unit
  warn : String -> Unit
  error : String -> Unit

handler {
  Logger:
  return x -> (x, [])
  log msg k -> let (r, logs) = k () in (r, msg : logs)
  warn msg k -> let (r, logs) = k () in (r, "WARN: " ++ msg : logs)
  error msg k -> let (r, logs) = k () in (r, "ERROR: " ++ msg : logs)
}
```

Questions:
- Is this design clear?
- Could it be simplified?
- What's missing?

---

## Design Problems (45 minutes)

### Design 1: Resource Management ⭐⭐⭐
Design an effect for file handles:

```
File:
  open : FilePath -> Handle
  read : Handle -> String
  write : Handle -> String -> Unit
  close : Handle -> Unit
```

a) How do you ensure files are closed?
b) How do you prevent reading closed files?
c) Design a handler that tracks open handles
d) Implement `withFile` combinator

### Design 2: Concurrency ⭐⭐⭐
Design effects for cooperative concurrency:

```
Fork:
  fork : (Unit -> Unit ! {Fork}) -> Unit
  yield : Unit -> Unit
```

a) What should the handler maintain?
b) How do you schedule between tasks?
c) Implement a round-robin scheduler
d) Handle tasks that complete

### Design 3: Rollback Semantics ⭐⭐⭐
Design a transaction effect:

```
Transaction:
  read : Key -> Value
  write : Key -> Value -> Unit
  abort : Unit -> Unit
```

Handler should:
- Track all writes
- On abort: discard changes
- On success: commit changes
- Support nested transactions

### Design 4: Testing Framework ⭐⭐⭐
Design effects for testing:

```
Test:
  assert : Bool -> Unit
  skip : String -> Unit
  log : String -> Unit
```

Handler should:
- Collect all assertions
- Track passes/failures
- Support skipped tests
- Return test results

---

## Solutions

### Warm-Up Solutions

**1.1**:
```
a) ! {}  (pure)
b) ! {State}
c) ! {IO}
d) ! {State, IO}
```

**1.2**:
```
a) Yes (identical)
b) Yes (order doesn't matter)
c) Yes (idempotent)
d) No (different effects)
```

**1.3**:
```
a) Pure (creating lambda)
b) Effectful ! {State} (calling it)
c) Pure
d) Effectful ! {IO}
```

**1.4**:
```
a) Pure function returning Nat
b) Stateful function returning Nat
c) Uses both State and IO
d) Effect-polymorphic (works with any effects)
```

**1.5**: Returns 1 (gets 0, adds 1)

### Standard Solutions

**2.1**:
```
a) ! {State, IO}
b) ! {State, IO}  (State from get, IO from f)
c) ! {State, IO}
```

**2.2**:
```
a) countGets s f =
     handle (f ()) with {
       State:
       return x -> (x, 0)
       get () k ->
         let (r, count) = k s in
         (r, count + 1)
       put newS k -> k ()
     }

b) ignoreExceptions f default =
     handle (f ()) with {
       Exception:
       return x -> x
       throw () k -> default
     }

c) traceIO f =
     handle (f ()) with {
       IO:
       return x -> (x, [])
       print n k ->
         let (r, trace) = k () in
         (r, n : trace)
       read () k -> k 0
     }
```

**2.3**:
```
a) twice : ∀ρ. (A -> A ! ρ) -> A -> A ! ρ

b) mapList : ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ

c) sequence : ∀ρ. List (Unit -> A ! ρ) -> List A ! ρ
```

**2.4**:
```
a) A ! {IO}  (State handled, IO remains)
b) A ! {}  (both handled)
c) Inner handler (stateH) handles State first
```

**2.5**:
```
a) Exception: Never called (abort)
b) State: Always called (thread state)
c) Choice: Called multiple times (nondeterminism)
d) Logger: Called once (accumulate)
```

**2.6**:
```
a) Random:
     next : Unit -> Nat
   Handler: Use seed, generate pseudo-random

b) Database:
     query : String -> [Row]
     insert : Row -> Unit
     update : Row -> Unit
   Handler: Connect to DB, execute SQL

c) FileSystem:
     read : FilePath -> String
     write : FilePath -> String -> Unit
     delete : FilePath -> Unit
   Handler: OS file operations
```

**2.7**:
```
a) ∀ρ. (A -> B ! ρ) -> (B -> C ! ρ) -> A -> C ! ρ

b) ∀ρ. Bool -> (Unit -> A ! ρ) -> (Unit -> A ! ρ) -> A ! ρ

c) [Nat] -> Unit ! {IO}
```

**2.8**:
```
a) Unit -> Nat ! {State | ρ}

b) (Unit -> A ! ρ) -> Unit -> A ! {IO | ρ}

c) (Unit -> A ! ρ) -> Unit -> A ! ρ
```

### Challenge Solutions

**3.1**:
```
runStateWith s f =
  handle (f ()) with {
    State:
    return x -> (x, s)
    get () k -> k s
    put newS k -> runStateWith newS (λ_. k ())
  }
```

**3.2**:
```
a) allResults f =
     handle (f ()) with {
       Choice:
       return x -> [x]
       choose b k -> k true ++ k false
     }

b) firstResult f =
     handle (f ()) with {
       Choice, Exception:
       return x -> Just x
       choose b k ->
         case k true of
           Just r -> Just r
           Nothing -> k false
       throw () k -> Nothing
     }

c) countChoices f =
     handle (f ()) with {
       Choice:
       return x -> (x, 0)
       choose b k ->
         let (r, count) = k true in
         (r, count + 1)
     }
```

**3.3**:
```
a) Depends on handler order
b) Different semantics based on which is outer handler
c) Outer handler "sees" inner effects first
```

**3.4**: Requires a task queue and scheduler state. Complex implementation.

**3.5**:
```
a) No: can't add effects
b) No: can't remove effects
c) No: can't add effects
d) Yes: instantiate ρ = {State}

Effects are invariant in result position!
```

### Debugging Solutions

**Debug 1**: Change to `f : Unit -> Nat ! {State}`

**Debug 2**: Handle the State effect or change main type to `! {State}`

**Debug 3**: Effect name should be `State` not `state` (case-sensitive)

**Debug 4**: `get` returns `Nat` (or generic `s`), not `String`. Should be `k 0` or some Nat value.

**Debug 5**: `f` claims to work with any effect but then uses `{State}`. Should be `∀ρ. A ! {State | ρ} -> A ! {State | ρ}`.

### Code Review Solutions

**Review 1**: `put` handler ignores new state. Should call `runState newS (λ_. k ())` recursively.

**Review 2**: Version A is correct (don't resume after exception). Version B incorrectly resumes.

**Review 3**: Should be `∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ` for effect polymorphism.

**Review 4**: Seems reasonable. Could add severity levels. Missing: timestamp, structured logging.

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 5 hard, 5 debug, 4 review, 4 design

**Note**: These problems complement the main exercises. Focus on understanding effects as annotations and handlers as interpreters!
