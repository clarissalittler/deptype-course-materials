# Chapter 17: Abstract Machines - Lesson Plan

**Estimated Total Time**: 12-16 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Lambda calculus basics (Chapter 1)
- [ ] Evaluation strategies: call-by-value vs call-by-name
- [ ] Basic Haskell pattern matching and algebraic data types
- [ ] Recursion and recursive data structures

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain why abstract machines are needed (vs substitution semantics)
2. Describe the components of CEK, SECD, and Krivine machines
3. Trace the execution of terms through each machine
4. Implement a simple abstract machine in Haskell
5. Compare evaluation strategies: call-by-value vs call-by-name
6. Understand the connection to real interpreters and VMs

---

## Lesson 1: From Substitution to Machines (2-3 hours)

### Learning Goals
- Understand why substitution-based evaluation is inefficient
- Learn the concept of environments as delayed substitution
- Understand closures as "lambda + environment"

### Activities

1. **Read** README.md sections: Overview, The Key Insight
2. **Think about** the efficiency problem:
   - How many times is the term traversed in `(λx. x + x + x) (1 + 2)`?
   - What if the argument is a large term?

3. **Explore** `src/Syntax.hs`:
   ```bash
   stack exec abstract-machines-repl
   :parse (\\x. x + 1) 5
   ```

4. **Key concepts to understand**:
   - Environment: `{x ↦ 5, y ↦ true}`
   - Closure: `⟨λx. x + 1, {y ↦ 42}⟩`
   - Why closures capture the environment at definition time

5. **Practice**: Draw the environment at each step of:
   ```
   let y = 10 in (λx. x + y) 5
   ```

### Self-Check Questions
- [ ] Why is substitution expensive for large terms?
- [ ] What does a closure capture and why?
- [ ] When is the environment extended?

---

## Lesson 2: The CEK Machine (3-4 hours)

### Learning Goals
- Understand the three components: Control, Environment, Kontinuation
- Learn how continuations represent "what to do next"
- Trace CEK machine execution by hand

### Activities

1. **Read** README.md section: CEK Machine
2. **Study** `src/CEK.hs`:
   - Find the `State` data type
   - Find the `Frame` data type (continuation frames)
   - Understand the `step` function

3. **Trace through manually** (paper and pencil!):
   ```
   (λx. x) 5
   ```
   Starting state: `Eval (App (Lam "x" (Var "x")) (Lit 5)), {}, []`

4. **Experiment** with the REPL:
   ```
   am> :trace (\\x. x) 5
   am> :trace (\\x. x + x) 3
   am> :trace (\\f. \\x. f x) (\\y. y + 1) 5
   ```

5. **Key insight**: The continuation is a *stack* of frames
   - `[FApp1 t env, FAdd2 v]` means:
     - First: finish evaluating the function application
     - Then: add v to the result

6. **Exercise**: What does this continuation mean?
   ```haskell
   [FApp2 (VClosure "x" body env), FAdd1 (Lit 10) env']
   ```

### Self-Check Questions
- [ ] What are the two possible states in CEK (Eval vs Apply)?
- [ ] When is a new frame pushed onto the continuation?
- [ ] When is a frame popped?
- [ ] How is function application handled (which component evaluates first)?

---

## Lesson 3: The SECD Machine (2-3 hours)

### Learning Goals
- Understand compilation to instructions
- Learn the stack-based execution model
- Compare interpreted (CEK) vs compiled (SECD) approaches

### Activities

1. **Read** README.md section: SECD Machine
2. **Study** `src/SECD.hs`:
   - Find the instruction set (`Instr` data type)
   - Find the `compile` function
   - Find the `exec` function

3. **Compile by hand**:
   ```
   (λx. x + 1) 5
   ```
   Expected:
   ```
   [IClosure [IAccess 0, IConst 1, IAdd, IReturn], IConst 5, IApply]
   ```

4. **Execute the compiled code** step by step:
   - Track: Stack, Environment, Control, Dump

5. **Experiment** with the REPL:
   ```
   am> :secd (\\x. x + 1) 5
   am> :compile (\\x. x + 1)
   ```

6. **Compare** CEK trace vs SECD execution for the same term

### Self-Check Questions
- [ ] Why does SECD use de Bruijn indices?
- [ ] What is the Dump used for?
- [ ] How does `IApply` work?
- [ ] What's the difference between `IClosure` and a lambda value?

---

## Lesson 4: The Krivine Machine (2-3 hours)

### Learning Goals
- Understand call-by-name (lazy) evaluation
- Learn how thunks delay computation
- Compare eager vs lazy evaluation

### Activities

1. **Read** README.md section: Krivine Machine
2. **Study** `src/Krivine.hs`:
   - Note how arguments are NOT evaluated before function calls
   - Understand `Thunk` = unevaluated closure

3. **Key difference from CEK**:
   ```
   CEK (call-by-value):
     (λx. 42) (loop forever)  →  loops forever

   Krivine (call-by-name):
     (λx. 42) (loop forever)  →  42
   ```

4. **Trace by hand**:
   ```
   (λx. λy. x) 5 (error "never evaluated")
   ```

5. **Experiment** with the REPL:
   ```
   am> :krivine (\\x. 42) (1 + 2)
   am> :krivine (\\x. x + x) 3   -- Note: 3 evaluated twice!
   ```

6. **Think about**: Why might you NOT want call-by-name?
   - Hint: `(λx. x + x) (expensive computation)`

### Self-Check Questions
- [ ] What is a thunk?
- [ ] Why does Krivine not have continuation frames like CEK?
- [ ] What happens if a variable is used twice in call-by-name?
- [ ] How would you add memoization (call-by-need)?

---

## Lesson 5: Comparison and Extensions (2-3 hours)

### Learning Goals
- Compare all three machines
- Understand trade-offs in machine design
- Connect to real implementations

### Activities

1. **Create a comparison table**:

   | Aspect | CEK | SECD | Krivine |
   |--------|-----|------|---------|
   | Strategy | ? | ? | ? |
   | Compilation | ? | ? | ? |
   | Environment | ? | ? | ? |

2. **Study** the README comparison table
3. **Research**: Which machines influenced which real systems?
   - CEK → ?
   - SECD → ?
   - Krivine → ?

4. **Extend one machine** (pick one from exercises):
   - Add pairs to CEK
   - Add exceptions to CEK
   - Add memoization to Krivine

5. **Run the test suite**:
   ```bash
   stack test
   ```
   All 35+ tests should pass.

### Self-Check Questions
- [ ] When would you choose CEK over SECD?
- [ ] What's the advantage of compilation (SECD)?
- [ ] How does GHC's STG machine relate to Krivine?

---

## Lesson 6: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Exercise 1: CEK traces
   - Exercise 2: SECD compilation
   - Exercise 3: Krivine semantics
   - Exercise 4: Add pairs to CEK

2. **Challenge problems**:
   - Implement tail-call optimization
   - Add first-class continuations (call/cc)
   - Build a step debugger

3. **Self-assessment**: Can you...
   - [ ] Trace CEK execution without looking at code?
   - [ ] Compile a term to SECD instructions by hand?
   - [ ] Explain why Krivine doesn't evaluate arguments?
   - [ ] Add a new construct to one of the machines?

---

## Progress Tracker

### Lesson 1: From Substitution to Machines
- [ ] Understood substitution inefficiency
- [ ] Grasped environment concept
- [ ] Understand closures

### Lesson 2: The CEK Machine
- [ ] Can identify C, E, K components
- [ ] Traced execution by hand
- [ ] Used REPL :trace command

### Lesson 3: The SECD Machine
- [ ] Understand instruction set
- [ ] Can compile terms by hand
- [ ] Traced stack-based execution

### Lesson 4: The Krivine Machine
- [ ] Understand call-by-name
- [ ] Know what thunks are
- [ ] Can contrast with CEK

### Lesson 5: Comparison and Extensions
- [ ] Completed comparison table
- [ ] Connected to real systems
- [ ] Extended one machine

### Lesson 6: Exercises and Mastery
- [ ] Completed core exercises
- [ ] All tests pass
- [ ] Can explain concepts to others

---

## Key Takeaways

After completing this chapter, remember:

1. **Environments replace substitution**: Store bindings, look up on demand
2. **Closures = lambda + environment**: Capture scope at definition time
3. **Continuations = "what's next"**: Reified evaluation context
4. **Compilation separates concerns**: Parse once, execute many times
5. **Evaluation strategy matters**: Eager vs lazy, different use cases

## Next Steps

After mastering this chapter:
- **Chapter 18 (NbE)**: Normalization using semantic interpretation
- **Chapter 19 (Bidirectional)**: Efficient type checking with modes
- **Chapter 20 (Denotational)**: Mathematical meaning of programs
