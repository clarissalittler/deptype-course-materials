# Chapter 12: Effect Systems - Self-Assessment Quiz

Test your understanding of algebraic effect systems. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What does an effect system track?
a) Memory usage
b) Computational side effects in types
c) Execution time
d) Type errors

### Q2. What does `T ! {}` mean?
a) Error type
b) Pure computation returning T
c) Empty result
d) T with all effects

### Q3. What does `T ! {State}` mean?
a) T is state-dependent
b) T with state effect
c) T without state
d) State-only type

### Q4. What is an effect row?
a) A type of array
b) A collection of effects
c) A matrix operation
d) A row in a table

### Q5. What is `perform` used for?
a) Type checking
b) Executing an effect operation
c) Defining functions
d) Creating handlers

### Q6. What does a handler do?
a) Handles errors only
b) Interprets effect operations
c) Compiles code
d) Optimizes performance

### Q7. What is the continuation in a handler?
a) The next line of code
b) The rest of the computation after the operation
c) The previous computation
d) The loop counter

### Q8. What does effect polymorphism allow?
a) Different types at runtime
b) Functions that work with any effect row
c) Multiple return values
d) Dynamic typing

### Q9. What happens if a handler doesn't call the continuation?
a) Error
b) Computation continues
c) Computation aborts
d) Infinite loop

### Q10. Which language implements algebraic effects?
a) Python
b) JavaScript
c) Koka
d) Java

---

## Section 2: Effect Rows and Operations (10 questions)

### Q11. What's the effect row syntax for "no effects"?
a) `{}`
b) `[]`
c) `null`
d) `void`

### Q12. What's the type of `perform State.get ()`?
a) `Unit`
b) `Nat ! {State}`
c) `State`
d) `Nat`

### Q13. For State effect, what does `put` do?
a) Gets current state
b) Sets new state
c) Deletes state
d) Copies state

### Q14. What does `{E | ρ}` mean?
a) E or ρ
b) Effect E plus row variable ρ
c) E implies ρ
d) E without ρ

### Q15. What's the effect of `λx. x + 1`?
a) `{}`
b) `{State}`
c) `{Nat}`
d) Unknown

### Q16. How do effects combine in sequencing?
a) They cancel out
b) Union of effects
c) Intersection
d) Only the last effect

### Q17. What effect does creating a lambda have?
a) All effects of body
b) No effects (`{}`)
c) Depends on argument
d) Unknown

### Q18. What's the Exception effect operation for raising errors?
a) `raise`
b) `throw`
c) `error`
d) `exception`

### Q19. If `t₁` has effect `{A}` and `t₂` has effect `{B}`, what's `t₁; t₂`'s effect?
a) `{A}`
b) `{B}`
c) `{A, B}`
d) `{}`

### Q20. What is `ρ` in effect types?
a) A specific effect
b) A row variable (effect polymorphism)
c) A Greek letter
d) An error indicator

---

## Section 3: Typing Rules (10 questions)

### Q21. What judgment form does effect typing use?
a) `Γ ⊢ t : T`
b) `Γ ⊢ t : T ! ε`
c) `Γ ⊢ ε : T`
d) `Γ ! ε ⊢ t : T`

### Q22. In application `f x`, how are effects computed?
a) Only f's effects
b) Only x's effects
c) Union of all effects
d) No effects

### Q23. What's the type of `λx : Nat. perform State.get ()`?
a) `Nat -> Nat ! {}`
b) `Nat -> Nat ! {State}`
c) `Nat ! {State} -> Nat`
d) `(Nat, Nat) ! {State}`

### Q24. When is a function type pure (! {})?
a) Never
b) When it doesn't perform effects
c) When creating the lambda
d) Only for identity

### Q25. What's the effect of `if c then t₁ else t₂`?
a) Effect of c only
b) Effect of t₁ only
c) Effect of t₂ only
d) Union of all effects

### Q26. For `∀ρ. T`, what can ρ be instantiated to?
a) Any type
b) Any effect row
c) Only `{}`
d) Nothing

### Q27. What's the effect of `return t` in effectful context?
a) All effects
b) Same as t's effects
c) `{}`
d) Depends on handler

### Q28. How does `perform E.op t` affect the effect row?
a) Removes E
b) Adds E to the effect row
c) Changes E
d) No change

### Q29. What's needed to call a function `A -> B ! {State}`?
a) Any argument
b) Argument of type A, State effect must be handled
c) Argument of type B
d) Nothing special

### Q30. Is `{State} <: {State, IO}` (subeffecting)?
a) Yes
b) No
c) Sometimes
d) Not applicable

---

## Section 4: Handlers (10 questions)

### Q31. What parts does a handler have?
a) Just return clause
b) Return clause and operation clauses
c) Only operation clauses
d) Type annotations

### Q32. In handler clause `op p k -> body`, what is `p`?
a) The handler
b) The operation parameter
c) The result
d) Previous state

### Q33. In handler clause `op p k -> body`, what is `k`?
a) A constant
b) The continuation
c) The key
d) The kind

### Q34. To resume a computation in a handler, you:
a) Return a value
b) Call the continuation k
c) Throw an exception
d) Do nothing

### Q35. What does `handle t with h` do?
a) Type checks t
b) Runs t with handler h interpreting effects
c) Compiles t
d) Prints t

### Q36. For exception handling, how do you abort computation?
a) Call k with error
b) Don't call the continuation
c) Return null
d) Throw again

### Q37. What effect does `handle t with h` have?
a) Same as t
b) t's effects minus handled effect
c) No effects
d) Adds effects

### Q38. Can handlers call continuations multiple times?
a) No, never
b) Yes (enables nondeterminism)
c) Only once
d) Depends on language

### Q39. What's a "deep" handler?
a) Handles nested effects
b) Automatically re-handles effects in continuation
c) Deep in the stack
d) Slow handler

### Q40. What's the result type of a handler's return clause?
a) Must match input type
b) Determines overall handler result type
c) Always Unit
d) Doesn't matter

---

## Section 5: Applications (5 questions)

### Q41. How do algebraic effects compare to monads?
a) Same thing
b) Effects use handlers, monads use bind
c) Monads are simpler
d) Effects can't handle state

### Q42. What's the advantage of effect polymorphism?
a) Faster code
b) Reusable functions regardless of effects
c) Better error messages
d) No compilation needed

### Q43. For implementing state, the handler typically:
a) Uses global variables
b) Threads state through continuation calls
c) Ignores state
d) Creates new state each time

### Q44. How can effects express async/await?
a) They can't
b) Async as effect with suspend/resume operations
c) Using threads
d) Callbacks only

### Q45. What's the benefit of effects for testing?
a) Faster tests
b) Mock effects with test handlers
c) No benefits
d) Automatic test generation

---

## Answer Key

### Section 1: Core Concepts
1. b) Computational side effects in types
2. b) Pure computation returning T
3. b) T with state effect
4. b) A collection of effects
5. b) Executing an effect operation
6. b) Interprets effect operations
7. b) The rest of the computation after the operation
8. b) Functions that work with any effect row
9. c) Computation aborts
10. c) Koka

### Section 2: Effect Rows and Operations
11. a) `{}`
12. b) `Nat ! {State}`
13. b) Sets new state
14. b) Effect E plus row variable ρ
15. a) `{}`
16. b) Union of effects
17. b) No effects (`{}`)
18. b) `throw`
19. c) `{A, B}`
20. b) A row variable

### Section 3: Typing Rules
21. b) `Γ ⊢ t : T ! ε`
22. c) Union of all effects
23. b) `Nat -> Nat ! {State}`
24. c) When creating the lambda
25. d) Union of all effects
26. b) Any effect row
27. b) Same as t's effects
28. b) Adds E to the effect row
29. b) Argument of type A, State effect must be handled
30. a) Yes (can add effects in supertype)

### Section 4: Handlers
31. b) Return clause and operation clauses
32. b) The operation parameter
33. b) The continuation
34. b) Call the continuation k
35. b) Runs t with handler h interpreting effects
36. b) Don't call the continuation
37. b) t's effects minus handled effect
38. b) Yes (enables nondeterminism)
39. b) Automatically re-handles effects in continuation
40. b) Determines overall handler result type

### Section 5: Applications
41. b) Effects use handlers, monads use bind
42. b) Reusable functions regardless of effects
43. b) Threads state through continuation calls
44. b) Async as effect with suspend/resume operations
45. b) Mock effects with test handlers

---

## Scoring Guide

- **41-45 correct**: Excellent! You've mastered effect systems.
- **33-40 correct**: Good understanding. Review handlers and polymorphism.
- **22-32 correct**: Decent start. Re-work the tutorial examples.
- **Below 22**: Please review the chapter materials carefully.
