# Chapter 11: Refinement Types - Self-Assessment Quiz

Test your understanding of refinement types. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What is a refinement type?
a) A type with runtime checks
b) A type with a predicate constraining values
c) A type that refines errors
d) A polymorphic type

### Q2. How do you read `{x: Nat | x > 0}`?
a) x is a natural number or greater than 0
b) Natural numbers greater than 0
c) x assigns Nat where x > 0
d) Nat excluding 0 through runtime check

### Q3. What values inhabit `{x: Nat | x == 5}`?
a) All natural numbers
b) Only 5
c) 0 through 5
d) Nothing (empty type)

### Q4. What values inhabit `{x: Nat | false}`?
a) All natural numbers
b) Only 0
c) No values (empty/uninhabited type)
d) Negative numbers

### Q5. What is the relationship between refinement types and simple types?
a) Refinements replace simple types
b) Refinements extend simple types with predicates
c) They are completely different
d) Simple types have predicates too

### Q6. What is `{x: Nat | true}` equivalent to?
a) The empty type
b) Just `Nat` (no restriction)
c) Just 0
d) An error type

### Q7. Why can't simple types express "positive number"?
a) No syntax for it
b) Types don't constrain values beyond structure
c) Positive isn't a valid type
d) Performance reasons

### Q8. What does refinement subtyping depend on?
a) Runtime values
b) Predicate implication
c) User annotations
d) Memory layout

### Q9. What is path sensitivity?
a) File path handling
b) Using branch conditions to refine types
c) Network path optimization
d) Critical path analysis

### Q10. Which is more specific: `{x: Nat | x > 10}` or `{x: Nat | x > 5}`?
a) `{x: Nat | x > 10}` (fewer values)
b) `{x: Nat | x > 5}` (more values)
c) They're equally specific
d) Can't compare them

---

## Section 2: Predicates and Refinements (10 questions)

### Q11. Which is a valid predicate?
a) `λx. x > 0`
b) `x > 0`
c) `type x = Nat`
d) `{x: Nat}`

### Q12. What does `x > 5 && x < 10` mean?
a) x is 5 or 10
b) x is between 5 and 10 (exclusive)
c) x is outside 5 to 10
d) Syntax error

### Q13. What is `x > 0 => x >= 1` for natural numbers?
a) Always true
b) Always false
c) Sometimes true
d) Syntax error

### Q14. Which type represents even numbers?
a) `{x: Nat | x % 2 == 0}`
b) `{x: Nat | even x}`
c) Both a and b (if modulo/even are in the predicate language)
d) Can't express evenness

### Q15. What is `{x: Nat | x > 0 || x <= 0}`?
a) Empty type
b) Same as Nat (tautology)
c) Positive numbers only
d) Error

### Q16. For `{x: Nat | x >= n}`, what does `n` refer to?
a) A global constant
b) A variable in scope
c) A type parameter
d) Nothing (invalid)

### Q17. What is `!true` in predicate logic?
a) true
b) false
c) not a predicate
d) error

### Q18. Which values satisfy `{x: Nat | x > 0 && x < 0}`?
a) All naturals
b) 0
c) None (contradiction)
d) Negative numbers

### Q19. What is the type of `5` as a refined natural?
a) Nat
b) `{x: Nat | x == 5}`
c) Both are valid types for 5
d) 5

### Q20. Can predicates mention function calls?
a) Yes, any function
b) Only pure functions
c) Depends on the predicate language design
d) Never

---

## Section 3: Subtyping (10 questions)

### Q21. Is `{x: Nat | x > 10}` a subtype of `{x: Nat | x > 5}`?
a) Yes (x > 10 implies x > 5)
b) No (different predicates)
c) Only at runtime
d) Depends on x

### Q22. Is `{x: Nat | x > 5}` a subtype of `{x: Nat | x > 10}`?
a) Yes
b) No (x = 6 satisfies first but not second)
c) Sometimes
d) They're equal

### Q23. Is `{x: Nat | x == 7}` a subtype of `{x: Nat | x > 0}`?
a) Yes (7 is positive)
b) No (different predicates)
c) Only for 7
d) Error

### Q24. What's the subtyping relationship between refinements?
a) Stronger predicate = supertype
b) Stronger predicate = subtype
c) No relationship
d) Alphabetical

### Q25. Is `Nat` a subtype of `{x: Nat | x >= 0}`?
a) Yes (equivalent types)
b) No (refinement is more specific)
c) Nat isn't refined
d) Only with explicit cast

### Q26. For `{x: T | φ} <: {x: T | ψ}`, what must hold?
a) `φ ⟹ ψ` (φ implies ψ)
b) `ψ ⟹ φ` (ψ implies φ)
c) `φ == ψ`
d) Nothing

### Q27. Is `{x: Nat | x > 0 && x < 10}` a subtype of `{x: Nat | x < 100}`?
a) Yes
b) No
c) Can't determine
d) Depends on runtime

### Q28. What's the most specific refinement of Nat?
a) `{x: Nat | true}`
b) `{x: Nat | false}`
c) Singleton types like `{x: Nat | x == 5}`
d) `Nat` itself

### Q29. Is `{x: Nat | x > 5}` a subtype of `Nat`?
a) Yes (Nat has no constraint, trivially satisfied)
b) No (Nat isn't refined)
c) Can't compare
d) Equal

### Q30. If A <: B and B <: C, is A <: C?
a) Yes (transitivity)
b) No
c) Only for refinements
d) Only for base types

---

## Section 4: Path Sensitivity (5 questions)

### Q31. In `if x > 5 then t else e`, what's known in `t`?
a) x > 5
b) x <= 5
c) Nothing
d) x == 5

### Q32. In `if x > 5 then t else e`, what's known in `e`?
a) x > 5
b) x <= 5
c) Nothing
d) x == 5

### Q33. What is "path sensitivity"?
a) Tracking conditions through branches
b) File system paths
c) Performance optimization
d) Memory paths

### Q34. After `if iszero x then ... else pred x`, why is pred safe?
a) Runtime check
b) x > 0 is known in else branch
c) pred always works
d) It's not safe

### Q35. Do path conditions accumulate in nested ifs?
a) Yes (inner branches know outer conditions)
b) No (each branch is independent)
c) Only for two levels
d) Only in then branches

---

## Section 5: Dependent Functions (5 questions)

### Q36. What does `(x: T₁) -> T₂` mean when x appears in T₂?
a) Error
b) T₂ can depend on x's value
c) T₂ ignores x
d) x is unused

### Q37. What's a valid type for safe division?
a) `Nat -> Nat -> Nat`
b) `Nat -> {d: Nat | d > 0} -> Nat`
c) Both work equally well
d) Division can't be typed

### Q38. For `index : Vec a n -> {i: Nat | i < n} -> a`, why is it safe?
a) Runtime bounds check
b) Type ensures i < n statically
c) Vectors can't be indexed
d) It's not safe

### Q39. What's the type of `replicate 5 'a'`?
a) `Vec Char 5`
b) `[Char]`
c) `Char`
d) Can't determine

### Q40. Can dependent function return types vary by argument?
a) No, types are fixed
b) Yes, that's the point of dependent types
c) Only for Nat arguments
d) Only at runtime

---

## Answer Key

### Section 1: Core Concepts
1. b) Type with predicate constraining values
2. b) Natural numbers greater than 0
3. b) Only 5
4. c) No values (empty type)
5. b) Refinements extend simple types
6. b) Just `Nat`
7. b) Types don't constrain values beyond structure
8. b) Predicate implication
9. b) Using branch conditions to refine types
10. a) `{x: Nat | x > 10}` (fewer values)

### Section 2: Predicates and Refinements
11. b) `x > 0`
12. b) x is between 5 and 10 (exclusive)
13. a) Always true
14. c) Both a and b
15. b) Same as Nat (tautology)
16. b) A variable in scope
17. b) false
18. c) None (contradiction)
19. c) Both are valid types for 5
20. c) Depends on predicate language design

### Section 3: Subtyping
21. a) Yes
22. b) No
23. a) Yes
24. b) Stronger predicate = subtype
25. a) Yes (equivalent)
26. a) φ implies ψ
27. a) Yes
28. c) Singleton types
29. a) Yes
30. a) Yes (transitivity)

### Section 4: Path Sensitivity
31. a) x > 5
32. b) x <= 5
33. a) Tracking conditions through branches
34. b) x > 0 is known in else branch
35. a) Yes

### Section 5: Dependent Functions
36. b) T₂ can depend on x's value
37. b) With refinement on divisor
38. b) Type ensures i < n statically
39. a) `Vec Char 5`
40. b) Yes, that's the point

---

## Scoring Guide

- **36-40 correct**: Excellent! You've mastered refinement types.
- **28-35 correct**: Good understanding. Review subtyping and path sensitivity.
- **20-27 correct**: Decent start. Re-work the tutorial examples.
- **Below 20**: Please review the chapter materials carefully.
