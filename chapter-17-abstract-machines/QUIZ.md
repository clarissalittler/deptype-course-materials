# Chapter 17: Abstract Machines - Self-Assessment Quiz

Test your understanding of abstract machines. Try to answer without looking at the solutions!

---

## Section 1: Fundamentals (10 questions)

### Q1. Why do abstract machines use environments instead of substitution?
a) Substitution is incorrect
b) Environments are easier to implement
c) Substitution is expensive (copying terms)
d) Environments support more language features

### Q2. What is a closure?
a) A function that takes no arguments
b) A function paired with its defining environment
c) A function that always returns the same value
d) A function that captures no free variables

### Q3. In the CEK machine, what does "K" stand for?
a) Konstant
b) Kontinuation
c) Kernel
d) Key

### Q4. What is a continuation?
a) A loop construct
b) The next instruction to execute
c) A representation of "what to do next" with the result
d) A way to exit a function early

### Q5. When does CEK create a closure?
a) When evaluating a variable
b) When evaluating a lambda
c) When evaluating an application
d) When applying a continuation

### Q6. In CEK, what are the two types of states?
a) Running and Stopped
b) Eval and Apply
c) Push and Pop
d) Call and Return

### Q7. What does the SECD machine do that CEK doesn't?
a) Support recursion
b) Compile terms to instructions first
c) Handle arithmetic
d) Use environments

### Q8. What is the purpose of the "Dump" in SECD?
a) Garbage collection
b) Error handling
c) Saving state for function returns
d) Storing compiled code

### Q9. What evaluation strategy does the Krivine machine implement?
a) Call-by-value
b) Call-by-name
c) Call-by-reference
d) Call-by-need

### Q10. What is a thunk in the Krivine machine?
a) An evaluated value
b) An unevaluated closure (term + environment)
c) A type of continuation
d) An error condition

---

## Section 2: CEK Machine (10 questions)

### Q11. In CEK, how is `(λx. x) 5` initially represented?
a) `Eval (App (Lam "x" (Var "x")) (Lit 5)), {}, []`
b) `Apply (Lam "x" (Var "x")), VInt 5`
c) `Eval (Var "x"), {x ↦ 5}, []`
d) `Apply [], VInt 5`

### Q12. When evaluating `f t` in CEK, what happens first?
a) t is evaluated
b) f is evaluated
c) Both are evaluated in parallel
d) The application is performed

### Q13. What does `FApp1 t env` in the continuation mean?
a) "Apply result to t"
b) "After getting the function, evaluate t in env"
c) "t is the first argument"
d) "Evaluate t first"

### Q14. What does `FApp2 v` in the continuation mean?
a) "Apply v to the next value"
b) "After getting the argument, apply v"
c) "v is the second part of application"
d) "Store v for later"

### Q15. After evaluating a lambda `λx.t` in environment `ρ`, what value is produced?
a) The lambda itself
b) `VClosure x t ρ`
c) `VLam x t`
d) The result of evaluating `t`

### Q16. When applying `VClosure x t ρ` to value `v`, what's the next state?
a) `Eval t, ρ, []`
b) `Eval t, ρ[x ↦ v], []`
c) `Apply [], v`
d) `Eval t, {x ↦ v}, []`

### Q17. What is the result of CEK on `(λx. λy. x) 1 2`?
a) 1
b) 2
c) A function
d) Error

### Q18. In CEK, what happens when continuation is empty and we have a value?
a) Error: missing continuation
b) Machine terminates with that value
c) Restart evaluation
d) Apply identity function

### Q19. How many frames are pushed for evaluating `f (g x)`?
a) 1
b) 2
c) 3
d) 4

### Q20. What's the purpose of storing `env` in frames like `FApp1 t env`?
a) Garbage collection
b) To evaluate t in the correct scope
c) Debugging
d) It's not necessary

---

## Section 3: SECD Machine (10 questions)

### Q21. What does `IAccess 0` do?
a) Access the first element of the stack
b) Access the first element of the environment
c) Access instruction 0
d) Access the first argument

### Q22. What's in a compiled closure created by `IClosure code`?
a) Just the code
b) The code and current environment
c) The code, environment, and stack
d) Just the environment

### Q23. How is `λx. x` compiled (x has de Bruijn index 0)?
a) `[IAccess 0]`
b) `[IClosure [IAccess 0]]`
c) `[IClosure [IAccess 0, IReturn]]`
d) `[ILam, IAccess 0]`

### Q24. How is application `t1 t2` compiled?
a) `compile t1 ++ [IApply] ++ compile t2`
b) `compile t2 ++ compile t1 ++ [IApply]`
c) `compile t1 ++ compile t2 ++ [IApply]`
d) `[IApply] ++ compile t1 ++ compile t2`

### Q25. What does `IApply` do?
a) Pops function and argument, starts executing function body
b) Pops two numbers and adds them
c) Applies the top of stack to the environment
d) Jumps to a code address

### Q26. When does the Dump get used?
a) Never in normal execution
b) When `IApply` is executed (save state)
c) When `IReturn` is executed (restore state)
d) Both b and c

### Q27. After `IApply`, what happens to the environment?
a) It's cleared
b) It's extended with the argument
c) It becomes the closure's environment extended with the argument
d) It's unchanged

### Q28. What does `IReturn` do?
a) Exits the program
b) Restores state from Dump and pushes result
c) Returns to the previous closure
d) Clears the stack

### Q29. Why does SECD use de Bruijn indices?
a) They're more readable
b) They're required by the theory
c) They allow O(1) variable lookup in the environment list
d) They simplify compilation

### Q30. Is SECD call-by-value or call-by-name?
a) Call-by-value
b) Call-by-name
c) Neither
d) Both

---

## Section 4: Krivine Machine (10 questions)

### Q31. In Krivine, when is an argument evaluated?
a) Before the function is called
b) When the corresponding variable is looked up
c) After the function returns
d) Never

### Q32. What does the Krivine stack contain?
a) Values
b) Thunks (unevaluated closures)
c) Continuations
d) Instructions

### Q33. For `(λx. 42) expensive`, what does Krivine do?
a) Evaluates expensive, then returns 42
b) Returns 42 without evaluating expensive
c) Errors because argument is unused
d) Returns expensive

### Q34. In Krivine, what happens when evaluating `t1 t2`?
a) Evaluate t2 to a value, then t1
b) Evaluate t1, push t2 as thunk
c) Push both as thunks
d) Compile to instructions

### Q35. What's the rule for lambda in Krivine with non-empty stack?
a) Create a closure
b) Error
c) Pop thunk, bind to variable, continue with body
d) Push body onto stack

### Q36. In `(λx. x + x) 3`, how many times is 3 evaluated in Krivine?
a) 0
b) 1
c) 2
d) 3

### Q37. What's call-by-need and how does it relate to Krivine?
a) Same thing
b) Krivine with memoization (evaluate thunks once)
c) Krivine with strict arguments
d) A different machine entirely

### Q38. What does Krivine do when evaluating a variable?
a) Look up value in environment
b) Look up thunk, continue with thunk's term and environment
c) Error if not found
d) Return the variable name

### Q39. For `(λx. λy. x) a b`, in what order are a and b evaluated?
a) a then b
b) b then a
c) Only a (b is never evaluated)
d) Neither (result is a thunk)

### Q40. Why doesn't Krivine have explicit continuation frames?
a) It uses the call stack instead
b) Arguments on the stack serve as implicit continuations
c) It doesn't need them for call-by-name
d) Both b and c

---

## Answer Key

### Section 1: Fundamentals
1. c) Substitution is expensive
2. b) Function + defining environment
3. b) Kontinuation
4. c) Representation of "what to do next"
5. b) When evaluating a lambda
6. b) Eval and Apply
7. b) Compile terms first
8. c) Saving state for returns
9. b) Call-by-name
10. b) Unevaluated closure

### Section 2: CEK Machine
11. a) `Eval (App ...), {}, []`
12. b) f is evaluated first
13. b) "After getting function, evaluate t in env"
14. b) "After getting argument, apply v"
15. b) `VClosure x t ρ`
16. b) `Eval t, ρ[x ↦ v], []`
17. a) 1
18. b) Machine terminates
19. c) 3 (one for outer app, one for inner app, one for variable g)
20. b) To evaluate t in correct scope

### Section 3: SECD Machine
21. b) Access first element of environment
22. b) Code and current environment
23. c) `[IClosure [IAccess 0, IReturn]]`
24. c) `compile t1 ++ compile t2 ++ [IApply]`
25. a) Pops function and argument, executes body
26. d) Both b and c
27. c) Closure's env extended with argument
28. b) Restores from Dump, pushes result
29. c) O(1) lookup
30. a) Call-by-value

### Section 4: Krivine Machine
31. b) When variable is looked up
32. b) Thunks
33. b) Returns 42 without evaluating expensive
34. b) Evaluate t1, push t2 as thunk
35. c) Pop thunk, bind to variable
36. c) 2 (x looked up twice)
37. b) Krivine with memoization
38. b) Look up thunk, continue with its term/env
39. c) Only a (b never evaluated)
40. d) Both b and c

---

## Scoring Guide

- **36-40 correct**: Excellent! You've mastered abstract machines.
- **28-35 correct**: Good understanding. Review the machines you struggled with.
- **20-27 correct**: Decent start. Re-read the tutorial and trace more examples.
- **Below 20**: Please review the chapter materials before proceeding.

---

## Targeted Review

If you missed questions in:
- **Section 1**: Review README.md Overview and "The Key Insight"
- **Section 2**: Study CEK.hs and trace examples by hand
- **Section 3**: Study SECD.hs, focus on compilation and execution
- **Section 4**: Study Krivine.hs, compare with CEK
