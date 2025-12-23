# Chapter 10: Linear Types - Self-Assessment Quiz

Test your understanding of linear types. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What does "linear" mean in linear types?
a) Types form a line
b) Values must be used exactly once
c) Functions are linear transformations
d) Types have linear complexity

### Q2. What are the two multiplicities?
a) One and Many
b) Linear (1) and Unrestricted (ω)
c) Single and Double
d) Static and Dynamic

### Q3. What does `A -o B` mean?
a) A implies B
b) A or B
c) Linear function from A to B
d) Unrestricted function from A to B

### Q4. What can you do with a linear variable?
a) Use it any number of times
b) Use it exactly once
c) Use it at least once
d) Never use it

### Q5. What can you do with an unrestricted variable?
a) Use it exactly once
b) Use it at most once
c) Use it any number of times (including zero)
d) Use it exactly twice

### Q6. Why can't you duplicate a linear variable?
a) It's inefficient
b) It would violate the "exactly once" rule
c) The syntax doesn't allow it
d) It causes runtime errors

### Q7. Why can't you discard a linear variable?
a) It wastes memory
b) It would violate the "exactly once" rule
c) It's not implemented
d) It causes type errors elsewhere

### Q8. What is `!A` (bang A)?
a) Not A
b) Unrestricted version of A
c) Linear version of A
d) Empty type

### Q9. What's the main benefit of linear types?
a) Faster execution
b) Smaller code
c) Compile-time resource management guarantees
d) Simpler syntax

### Q10. Which language uses ideas from linear types?
a) Python
b) JavaScript
c) Rust (ownership)
d) Java

---

## Section 2: Typing Rules (10 questions)

### Q11. Is `λ(x :1 Nat). x` well-typed?
a) Yes (x used once)
b) No (x should be unrestricted)
c) No (missing type annotation)
d) Depends on context

### Q12. Is `λ(x :1 Nat). (x, x)` well-typed?
a) Yes
b) No (x used twice)
c) No (pairs not allowed)
d) No (wrong type annotation)

### Q13. Is `λ(x :1 Nat). 0` well-typed?
a) Yes (we can ignore x)
b) No (x not used)
c) No (0 is not Nat)
d) No (missing return type)

### Q14. Is `λ(x :ω Nat). (x, x)` well-typed?
a) Yes (unrestricted can be duplicated)
b) No (still can't duplicate)
c) No (wrong syntax)
d) No (pairs require linear)

### Q15. Is `λ(x :ω Nat). 0` well-typed?
a) Yes (unrestricted can be ignored)
b) No (must use x)
c) No (0 is invalid)
d) No (missing annotation)

### Q16. What type does `λ(x :1 Nat). x` have?
a) Nat
b) Nat -> Nat
c) Nat -o Nat
d) !Nat -o Nat

### Q17. For `let (x, y) = p in t`, what must happen to x and y?
a) Both must be used exactly once
b) Both can be used any number of times
c) At least one must be used
d) Exactly one must be used

### Q18. When can you introduce `!t`?
a) Always
b) When t uses only unrestricted variables
c) When t is a value
d) When t has type Nat

### Q19. What does `let !x = t₁ in t₂` give you?
a) x is linear in t₂
b) x is unrestricted in t₂
c) x is not available in t₂
d) Depends on t₁

### Q20. In `f x` where f : A -o B, how many times is x used?
a) Zero times
b) Exactly once
c) At most once
d) Unknown

---

## Section 3: Context Splitting (10 questions)

### Q21. In `(t₁, t₂)`, how are linear variables distributed?
a) All go to t₁
b) All go to t₂
c) Split between t₁ and t₂
d) Copied to both

### Q22. Can the same linear variable appear in both t₁ and t₂ of `(t₁, t₂)`?
a) Yes, always
b) Yes, if it's used once total
c) No, never
d) Only in special cases

### Q23. For `λ(x :1 A). λ(y :1 B). (x, y)`, is this valid?
a) Yes (x and y each used once)
b) No (can't have two linear variables)
c) No (pairs are invalid)
d) No (wrong syntax)

### Q24. For `λ(x :1 A). λ(y :1 B). (y, y)`, is this valid?
a) Yes
b) No (y used twice)
c) No (x not used)
d) Both b and c

### Q25. How is context splitting for application `f e` done?
a) f gets all variables, e gets none
b) e gets all variables, f gets none
c) Variables split between f and e
d) Variables duplicated to both

### Q26. In `f e` where f : A -o B, how many times is f used?
a) Zero
b) Once (applied to e)
c) Depends on e
d) Twice

### Q27. For conditionals `if c then t else e`, how is context used?
a) Context split three ways
b) c gets some, t and e share the rest
c) Same context for t and e (only one executes)
d) All three get full copy

### Q28. Can unrestricted variables be shared across subterms?
a) No, must be split
b) Yes, they can be used multiple times
c) Only in special cases
d) Only if explicitly marked

### Q29. What's the context after `let (x, y) = e in ...`?
a) Empty
b) x and y both linear
c) x and y both unrestricted
d) Depends on e

### Q30. Is `λ(x :1 A * B). let (a, b) = x in (b, a)` valid?
a) Yes (x, a, b each used once)
b) No (x used in let)
c) No (a and b wrong order)
d) No (can't destructure linear)

---

## Section 4: Bang Type (5 questions)

### Q31. What's the type of `!5`?
a) Nat
b) !Nat
c) 5
d) Int

### Q32. Is `λ(x :1 Nat). !x` valid?
a) Yes
b) No (can't bang a linear variable)
c) No (syntax error)
d) Depends on context

### Q33. What does `let !x = e in (x, x)` achieve?
a) Makes e linear
b) Makes e unrestricted so x can be used twice
c) Creates a pair of e
d) Nothing, it's invalid

### Q34. Is `!!5` valid?
a) Yes, type is !!Nat
b) No, can't double-bang
c) Yes, type is !Nat
d) No, syntax error

### Q35. For `let !x = !5 in x + x`, what's the type?
a) !Nat
b) Nat
c) Nat * Nat
d) Error

---

## Section 5: Applications (5 questions)

### Q36. In Rust, what's analogous to linear types?
a) Generics
b) Traits
c) Ownership and move semantics
d) Macros

### Q37. For file handles, why should they be linear?
a) For speed
b) To ensure exactly one close
c) For security
d) For compatibility

### Q38. What do session types use linear types for?
a) Speed
b) Memory safety
c) Protocol compliance (each message sent once)
d) Type inference

### Q39. With linear memory: `free : Ptr -o ()`, what's prevented?
a) Memory allocation
b) Double-free and memory leaks
c) Null pointers
d) Buffer overflow

### Q40. Can linear types alone prevent all resource bugs?
a) Yes, completely
b) No, they prevent use-count bugs specifically
c) Only memory bugs
d) Only file bugs

---

## Answer Key

### Section 1: Core Concepts
1. b) Used exactly once
2. b) Linear (1) and Unrestricted (ω)
3. c) Linear function
4. b) Exactly once
5. c) Any number of times
6. b) Violates "exactly once"
7. b) Violates "exactly once"
8. b) Unrestricted version
9. c) Compile-time resource guarantees
10. c) Rust

### Section 2: Typing Rules
11. a) Yes
12. b) No (x used twice)
13. b) No (x not used)
14. a) Yes
15. a) Yes
16. c) Nat -o Nat
17. a) Both exactly once
18. b) Only unrestricted variables
19. b) x is unrestricted
20. b) Exactly once

### Section 3: Context Splitting
21. c) Split between
22. c) No, never
23. a) Yes
24. d) Both b and c
25. c) Split between
26. b) Once
27. c) Same context, one executes
28. b) Yes, can share
29. b) x and y both linear
30. a) Yes

### Section 4: Bang Type
31. b) !Nat
32. b) No
33. b) Makes unrestricted
34. a) Yes, !!Nat
35. b) Nat

### Section 5: Applications
36. c) Ownership
37. b) Exactly one close
38. c) Protocol compliance
39. b) Double-free and leaks
40. b) Use-count bugs specifically

---

## Scoring Guide

- **36-40 correct**: Excellent! You've mastered linear types.
- **28-35 correct**: Good understanding. Review bang and context splitting.
- **20-27 correct**: Decent start. Re-work the tutorial examples.
- **Below 20**: Please review the chapter materials carefully.
