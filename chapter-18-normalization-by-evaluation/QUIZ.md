# Chapter 18: Normalization by Evaluation - Self-Assessment Quiz

Test your understanding of NbE. Try to answer without looking at the solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What is the purpose of normalization?
a) To make programs run faster
b) To convert terms to canonical form for comparison
c) To remove all variables
d) To type check programs

### Q2. NbE works by composing which two functions?
a) parse and print
b) compile and execute
c) eval and quote
d) check and infer

### Q3. What is a closure in NbE?
a) A function that has been fully applied
b) A term paired with its defining environment
c) A lambda with no free variables
d) The result of normalization

### Q4. What is a neutral value?
a) A value that has been normalized
b) A value stuck on a free variable
c) A function that ignores its argument
d) A constant value

### Q5. In NbE, when does beta reduction happen?
a) During parsing
b) During eval (when applying a closure)
c) During quote
d) Never

### Q6. Why do we use the host language (Haskell) for evaluation?
a) Haskell is faster
b) Haskell does beta reduction for us
c) Haskell has better syntax
d) It's required by the theory

### Q7. What does `applyClosure (Closure env body) arg` do?
a) Returns `body` unchanged
b) Evaluates `body` with `arg : env`
c) Substitutes `arg` into `body`
d) Returns `arg`

### Q8. What type of value does `eval` return?
a) Term
b) Val (semantic value)
c) Nf (normal form)
d) String

### Q9. What type of value does `quote` return?
a) Term
b) Val
c) Nf (normal form)
d) Closure

### Q10. How do you normalize a term `t`?
a) `eval t`
b) `quote t`
c) `quote (eval [] t)` or similar
d) `eval (quote t)`

---

## Section 2: Evaluation (10 questions)

### Q11. What is `eval [] (TLam "x" (TVar 0))`?
a) `TVar 0`
b) `VLam "x" (Closure [] (TVar 0))`
c) `VNe (NVar 0)`
d) Error: unbound variable

### Q12. What is `eval [VInt 5] (TVar 0)`?
a) `VInt 0`
b) `VInt 5`
c) `VNe (NVar 0)`
d) Error

### Q13. When evaluating `TApp t1 t2`, what order are things evaluated?
a) t2 first, then t1
b) t1 first, then t2, then apply
c) They're evaluated together
d) Neither is evaluated

### Q14. What does `vApp (VNe (NVar 0)) (VInt 5)` return?
a) `VInt 5`
b) `VNe (NVar 0)`
c) `VNe (NApp (NVar 0) (VInt 5))`
d) Error

### Q15. In `vApp (VLam x closure) arg`, what happens?
a) Returns the closure
b) Returns the arg
c) Applies closure to arg (beta reduction)
d) Builds a neutral

### Q16. Given `eval env (TApp (TLam "x" (TVar 0)) t)`, what's the result?
a) A closure
b) `eval (eval env t : env) (TVar 0)` = `eval env t`
c) A neutral application
d) Depends on t

### Q17. What environment is used when applying a closure?
a) Empty environment
b) Current environment
c) Closure's captured environment extended with argument
d) Just the argument

### Q18. Can `eval` produce a neutral value from a closed term?
a) Yes, always
b) No, never (closed terms have no free variables)
c) Only for non-terminating terms
d) Only for ill-typed terms

### Q19. What is `eval [] (TApp (TVar 0) (TInt 5))`?
a) `VInt 5`
b) `VNe (NApp (NVar 0) (VInt 5))`
c) Error: unbound variable
d) A closure

### Q20. Does `eval` always terminate?
a) Yes, for all terms
b) Yes, for normalizing terms
c) No, it may loop
d) Only for typed terms

---

## Section 3: Quotation (10 questions)

### Q21. What is the purpose of `quote`?
a) To convert terms to strings
b) To convert semantic values back to syntax
c) To evaluate terms
d) To type check values

### Q22. How does `quote` handle `VLam x closure`?
a) Returns the closure's body
b) Creates fresh var, applies closure, quotes result
c) Returns `NfLam x (quote closure.body)`
d) Ignores the lambda

### Q23. What is a "level" in NbE?
a) Type of a term
b) Nesting depth in the syntax
c) Counter for fresh variable generation
d) Index into environment

### Q24. How is a fresh variable created at level `lvl`?
a) `VNe (NVar lvl)`
b) `TVar lvl`
c) `NfNe (NeVar lvl)`
d) `Closure [] (TVar lvl)`

### Q25. When quoting at level `l`, and we encounter `NVar k`, what index do we use?
a) `k`
b) `l`
c) `l - k - 1`
d) `k - l`

### Q26. What is `quote 0 (VNe (NVar 0))`?
a) `NfNe (NeVar 0)`
b) `NfNe (NeVar 1)`
c) `NfLam "x" ...`
d) Error

### Q27. What happens when quoting a Pi type `VPi x A closure`?
a) Same as quoting a lambda
b) Quote A, then create fresh var for quoting B
c) Return the closure unchanged
d) Error: Pi is not a value

### Q28. What is "eta expansion" in NbE?
a) Expanding variables
b) Turning `f` into `λx. f x` for neutral `f`
c) Removing lambdas
d) Converting indices to levels

### Q29. Why might eta expansion be useful?
a) It makes terms smaller
b) It helps compare functions extensionally
c) It's required for type checking
d) It improves performance

### Q30. If `f` is a neutral of function type, what is `quote l f` with eta?
a) Just the neutral
b) `NfLam x (quote (l+1) (vApp f (VNe (NVar l))))`
c) `NfNe (NeVar 0)`
d) Error

---

## Section 4: De Bruijn Representation (5 questions)

### Q31. In `λ. λ. 0`, what does `0` refer to?
a) First lambda (outermost)
b) Second lambda (innermost)
c) Free variable
d) The term itself

### Q32. In levels, at depth 2, variable bound by outer lambda has level:
a) 0
b) 1
c) 2
d) -1

### Q33. Convert level 0 to index at depth 3:
a) 0
b) 1
c) 2
d) 3

### Q34. Why are levels used instead of indices in the semantic domain?
a) Levels are more readable
b) Fresh variable creation is just incrementing
c) Levels work with closures
d) Both b and c

### Q35. The environment in NbE stores values at positions corresponding to:
a) Levels
b) Indices
c) Names
d) Types

---

## Section 5: Applications (5 questions)

### Q36. To check if two types are equal, we:
a) Compare terms syntactically
b) Normalize both and compare
c) Evaluate one and quote the other
d) Use unification

### Q37. In dependent type checking, NbE is used to:
a) Parse types
b) Compute types with terms substituted
c) Generate error messages
d) Optimize code

### Q38. What is `normalize ((λx. x) y)` where `y` is free?
a) `λx. x`
b) `y`
c) `(λx. x) y`
d) Error

### Q39. Which statement about NbE is TRUE?
a) NbE only works for simply-typed languages
b) NbE requires substitution under binders
c) NbE handles open terms via neutrals
d) NbE is slower than reduction

### Q40. NbE is related to which proof technique?
a) Induction
b) Logical relations
c) Coinduction
d) Resolution

---

## Answer Key

### Section 1: Core Concepts
1. b) Canonical form for comparison
2. c) eval and quote
3. b) Term + environment
4. b) Stuck on free variable
5. b) During eval
6. b) Haskell does beta for us
7. b) Evaluates body with arg : env
8. b) Val
9. c) Nf
10. c) quote (eval [] t)

### Section 2: Evaluation
11. b) VLam with closure
12. b) VInt 5
13. b) t1, then t2, then apply
14. c) VNe (NApp ...)
15. c) Beta reduction
16. b) eval env t
17. c) Closure's env + arg
18. b) No, closed = no neutrals
19. c) Error: unbound
20. b) For normalizing terms

### Section 3: Quotation
21. b) Values back to syntax
22. b) Fresh var, apply, quote
23. c) Fresh variable counter
24. a) VNe (NVar lvl)
25. c) l - k - 1
26. a) NfNe (NeVar 0) (at level 0, index is 0 - 0 - 1 = -1? Actually 0)
27. b) Quote A, fresh var for B
28. b) f → λx. f x
29. b) Extensional comparison
30. b) Lambda wrapping

### Section 4: De Bruijn
31. b) Innermost lambda
32. a) 0
33. c) 2 (= 3 - 0 - 1)
34. d) Both b and c
35. b) Indices

### Section 5: Applications
36. b) Normalize and compare
37. b) Compute types with substitution
38. b) y
39. c) Handles open terms via neutrals
40. b) Logical relations

---

## Scoring Guide

- **36-40 correct**: Excellent! You've mastered NbE.
- **28-35 correct**: Good understanding. Review quotation and levels.
- **20-27 correct**: Decent start. Re-trace the examples in the tutorial.
- **Below 20**: Please review the chapter materials carefully.

---

## Targeted Review

If you missed questions in:
- **Section 1**: Review README Overview and Core Idea
- **Section 2**: Study `eval` in NbE.hs, trace examples
- **Section 3**: Study `quote`, understand fresh variable trick
- **Section 4**: Review levels vs indices section
- **Section 5**: Study type checking integration
