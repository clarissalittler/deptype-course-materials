# Chapter 12: Effect Systems - Lesson Plan

**Estimated Total Time**: 14-18 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus (Chapter 2)
- [ ] Polymorphism (Chapter 6)
- [ ] Basic understanding of side effects
- [ ] Familiarity with continuations is helpful but not required

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain what effect systems are and why they matter
2. Read and write effect-annotated types
3. Understand effect rows and polymorphism
4. Write effect handlers to interpret operations
5. Connect algebraic effects to monads
6. Design custom effects for specific domains

---

## Lesson 1: The Problem of Side Effects (2-3 hours)

### Learning Goals
- Understand why tracking effects matters
- See how types can describe effects
- Learn the core intuition

### Activities

1. **Read** README.md sections: Overview, What Are Effects?

2. **The effects problem**:
   - `add : Int -> Int -> Int` -- obviously pure
   - `readFile : Path -> String` -- but what about I/O?
   - `getRandomNumber : Unit -> Int` -- state/nondeterminism?
   - Simple types don't distinguish pure from effectful!

3. **The effect system solution**:
   - `add : Int -> Int -> Int ! {}`  -- pure (empty effects)
   - `readFile : Path -> String ! {IO}` -- has IO effect
   - Type tells you WHAT effects a function may perform

4. **Key notation**:
   ```
   T ! ε       -- Type T with effects ε
   T ! {}      -- Pure (no effects)
   T ! {State} -- Uses state effect
   T ! {State, IO} -- Uses multiple effects
   ```

5. **Experiment** with the REPL:
   ```
   stack exec effect-repl
   effect> :type λx : Unit. perform State.get ()
   effect> :effects
   ```

### Self-Check Questions
- [ ] What are computational effects?
- [ ] Why can't simple types express effects?
- [ ] What does `T ! {State}` mean?

---

## Lesson 2: Effect Rows and Operations (2-3 hours)

### Learning Goals
- Understand effect row syntax
- Learn about effect operations
- See how effects compose

### Activities

1. **Read** README.md sections: Effect Rows, Built-in Effects

2. **Effect row syntax**:
   ```
   {}              -- Empty (pure)
   {State}         -- Single effect
   {State, IO}     -- Multiple effects
   {E | ρ}         -- Effect E plus row variable ρ
   ρ               -- Just a row variable
   ```

3. **Effect operations**:
   ```
   State:
     get : Unit -> Nat
     put : Nat -> Unit

   Exception:
     throw : Unit -> Unit

   IO:
     print : Nat -> Unit
     read : Unit -> Nat
   ```

4. **Performing operations**:
   ```
   perform State.get ()     -- Returns current state
   perform State.put 5      -- Sets state to 5
   perform Exception.throw ()  -- Raises exception
   ```

5. **Practice**: What effects do these have?
   - `λx. x + 1`
   - `λx. perform State.get ()`
   - `λx. perform IO.print x; perform State.put x`

### Self-Check Questions
- [ ] What is an effect row?
- [ ] How do you perform an effect operation?
- [ ] What's the difference between `{}` and `{State}`?

---

## Lesson 3: Effect Tracking Rules (2-3 hours)

### Learning Goals
- Understand how effects propagate
- Learn the typing rules for effects
- See effect union in action

### Activities

1. **Read** README.md sections: Type System, Effect Tracking Rule

2. **The typing judgment**:
   ```
   Γ ⊢ t : T ! ε
   ```
   Means: term t has type T and may perform effects ε

3. **Lambda rule**:
   ```
      Γ, x:A ⊢ t : B ! ε
     ─────────────────────── (Lam)
     Γ ⊢ λx:A. t : A -> B!ε ! {}
   ```
   Creating a lambda is pure; effects happen when called.

4. **Application rule**:
   ```
      Γ ⊢ t₁ : A -> B!ε₁ ! ε₂    Γ ⊢ t₂ : A ! ε₃
     ───────────────────────────────────────────── (App)
             Γ ⊢ t₁ t₂ : B ! ε₁ ∪ ε₂ ∪ ε₃
   ```
   Effects accumulate: evaluating t₁ + evaluating t₂ + function body.

5. **Perform rule**:
   ```
      op : A -> B ∈ E
     ────────────────────────────────── (Perform)
     Γ ⊢ perform E.op t : B ! {E}
   ```
   Performing an operation introduces that effect.

### Self-Check Questions
- [ ] How do effects combine in application?
- [ ] Why is creating a lambda pure?
- [ ] What effect does `perform State.get ()` have?

---

## Lesson 4: Effect Handlers (2-3 hours)

### Learning Goals
- Understand what handlers do
- Learn handler syntax
- See handlers as effect interpreters

### Activities

1. **Read** README.md sections: Handlers, Simple Handler

2. **What handlers do**:
   - Catch effect operations
   - Provide implementations
   - Transform computations

3. **Handler syntax**:
   ```
   handle computation with {
     Effect:
     return x -> body           -- Handle pure return
     op₁ p k -> body            -- Handle op₁ (p=param, k=continuation)
     op₂ p k -> body            -- Handle op₂
   }
   ```

4. **Example: State handler**:
   ```
   handle (perform State.get ()) with {
     State:
     return x -> x
     get () k -> k 0    -- Continue with state 0
     put n k -> k ()    -- Ignore, continue
   }
   -- Result: 0
   ```

5. **The continuation**:
   - `k` represents "the rest of the computation"
   - Calling `k v` resumes with value v
   - Not calling `k` aborts the computation

### Self-Check Questions
- [ ] What is an effect handler?
- [ ] What does the continuation `k` represent?
- [ ] What happens if a handler doesn't call `k`?

---

## Lesson 5: Effect Polymorphism (2-3 hours)

### Learning Goals
- Understand row polymorphism for effects
- Write polymorphic effect functions
- See the power of effect abstraction

### Activities

1. **Read** README.md sections: Effect Polymorphism

2. **Row variables**:
   ```
   ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ
   ```
   Works with ANY effect row.

3. **Why polymorphism?**:
   ```
   map_pure : (A -> B ! {}) -> List A -> List B ! {}
   map_state : (A -> B ! {State}) -> List A -> List B ! {State}
   map : ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ  -- One function!
   ```

4. **Row extension**:
   ```
   {E | ρ}   -- Effect E plus whatever is in ρ
   ```
   Allows adding effects to a polymorphic row.

5. **Practice**: What's the type of:
   ```
   λf. λx. f x; f x   -- Calls f twice
   ```

### Self-Check Questions
- [ ] What is a row variable?
- [ ] Why is effect polymorphism useful?
- [ ] What does `{State | ρ}` mean?

---

## Lesson 6: Algebraic Effects Theory (2-3 hours)

### Learning Goals
- Understand why effects are "algebraic"
- Learn continuation-based semantics
- Compare to monads

### Activities

1. **Read** README.md sections: Algebraic Effects Theory

2. **Why "algebraic"?**:
   - Operations are defined by signatures
   - Handlers give semantics via equations
   - Effects compose algebraically

3. **Continuation semantics**:
   ```
   perform State.get ()
   -- Suspends computation
   -- Creates continuation k = λresult. <rest>
   -- Handler receives: get, (), k
   -- Handler can resume: k 42
   ```

4. **Compared to monads**:
   | Monads | Algebraic Effects |
   |--------|------------------|
   | Values wrapped in M a | Types annotated with effects |
   | do notation | Direct syntax |
   | Transformers for combining | Row polymorphism |
   | Fixed semantics | Handler-defined semantics |

5. **Deep vs shallow handlers**:
   - Deep: Re-handle effects in continuation
   - Shallow: Handle only first occurrence

### Self-Check Questions
- [ ] What makes effects "algebraic"?
- [ ] How do handlers use continuations?
- [ ] How do algebraic effects compare to monads?

---

## Lesson 7: Building Custom Effects (2-3 hours)

### Learning Goals
- Design new effects
- Write handlers for custom effects
- Apply effects to real problems

### Activities

1. **Review** examples from README and exercises

2. **Designing an effect**:
   ```
   Logger:
     log : String -> Unit
   ```
   What are its operations? What types?

3. **Write a handler**:
   ```
   handle computation with {
     Logger:
     return x -> (x, [])         -- Return value + logs
     log msg k ->
       let (result, logs) = k () in
       (result, msg :: logs)     -- Accumulate logs
   }
   ```

4. **Common patterns**:
   - State: Thread state through continuation
   - Exception: Don't call continuation
   - Nondeterminism: Call continuation multiple times
   - Logging: Accumulate in result

5. **Real applications**:
   - Async/await as effects
   - Testing with mock effects
   - Dependency injection

### Self-Check Questions
- [ ] How do you design a new effect?
- [ ] What makes a good handler?
- [ ] When would you use algebraic effects?

---

## Lesson 8: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Effect row understanding
   - Writing handlers
   - Effect polymorphism
   - Custom effects

2. **Run all tests**:
   ```bash
   stack test
   ```
   All 61 tests should pass.

3. **Challenge problems**:
   - Implement async/await effect
   - Add generators/coroutines
   - Implement exception handling

4. **Self-assessment**: Can you...
   - [ ] Read effect-annotated types?
   - [ ] Write effect handlers?
   - [ ] Use effect polymorphism?
   - [ ] Design custom effects?

---

## Progress Tracker

### Lesson 1: Side Effects
- [ ] Understood the problem
- [ ] Learned effect notation
- [ ] Experimented with REPL

### Lesson 2: Effect Rows
- [ ] Know row syntax
- [ ] Understand operations
- [ ] Can compose effects

### Lesson 3: Typing Rules
- [ ] Understand propagation
- [ ] Know the key rules
- [ ] Can trace effects

### Lesson 4: Handlers
- [ ] Understand handler purpose
- [ ] Know handler syntax
- [ ] Grasp continuations

### Lesson 5: Polymorphism
- [ ] Understand row variables
- [ ] Can write polymorphic functions
- [ ] See the benefits

### Lesson 6: Theory
- [ ] Know why "algebraic"
- [ ] Understand continuation semantics
- [ ] Can compare to monads

### Lesson 7: Custom Effects
- [ ] Can design effects
- [ ] Can write handlers
- [ ] See applications

### Lesson 8: Exercises
- [ ] Completed exercises
- [ ] All tests pass
- [ ] Can apply concepts

---

## Key Takeaways

1. **Effects in types**: `T ! ε` tracks what effects may occur
2. **Effect rows**: Sets of effects that compose
3. **Handlers**: Interpret effect operations
4. **Continuations**: "The rest of the computation"
5. **Polymorphism**: Abstract over effects with row variables

## Next Steps

After mastering this chapter:
- **Chapter 13 (Gradual Typing)**: Mix static and dynamic typing
- **Research**: Koka, OCaml 5 effects, capability systems
- **Practice**: Implement effects for real problems
