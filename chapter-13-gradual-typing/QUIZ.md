# Chapter 13: Gradual Typing - Self-Assessment Quiz

Test your understanding of gradual typing. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What is gradual typing?
a) Typing that gets faster over time
b) Mixing static and dynamic typing in one language
c) A gradual increase in type checking
d) Type checking only functions

### Q2. What does the type `?` represent?
a) An error type
b) A question mark literal
c) Dynamic/unknown type
d) The empty type

### Q3. What relation replaces equality in gradual typing?
a) Subtyping
b) Consistency
c) Equivalence
d) Ordering

### Q4. Is `Nat ~ ?` (Nat consistent with dynamic)?
a) Yes
b) No
c) Sometimes
d) Only at runtime

### Q5. Is `Nat ~ Bool`?
a) Yes
b) No
c) Through `?`
d) Depends on context

### Q6. Is consistency transitive?
a) Yes
b) No
c) Only for base types
d) Only with `?`

### Q7. What is a cast?
a) Type conversion at runtime
b) A type annotation
c) An error message
d) A function call

### Q8. What does `<T₁ => T₂>^l t` mean?
a) t has type T₁ or T₂
b) Cast t from T₁ to T₂ with blame label l
c) l is between T₁ and T₂
d) Convert T₁ to T₂

### Q9. What is blame tracking?
a) Error messages
b) Identifying the source of runtime type errors
c) Logging
d) Debugging

### Q10. What is the blame theorem?
a) All programs have blame
b) Well-typed code can't be blamed
c) Blame is always on the caller
d) Dynamic code is always blamed

---

## Section 2: Consistency Relation (10 questions)

### Q11. What makes consistency different from equality?
a) It's reflexive
b) It's symmetric
c) It's NOT transitive
d) All of the above

### Q12. Is `? ~ ?`?
a) Yes
b) No
c) Undefined
d) Only once

### Q13. Is `(Nat -> Bool) ~ (? -> ?)`?
a) Yes (componentwise consistency)
b) No
c) Only if Nat ~ Bool
d) Error

### Q14. Is `(Nat -> Nat) ~ (Bool -> Bool)`?
a) Yes
b) No (Nat ≁ Bool)
c) Through ?
d) Sometimes

### Q15. Is `(? -> Nat) ~ (Bool -> ?)`?
a) Yes
b) No
c) Only partially
d) Error

### Q16. For `T₁ -> T₂ ~ S₁ -> S₂`, what's needed?
a) T₁ = S₁ and T₂ = S₂
b) T₁ ~ S₁ and T₂ ~ S₂
c) T₁ ~ S₂ and T₂ ~ S₁
d) Any of the above

### Q17. If `A ~ ?` and `? ~ B`, is `A ~ B`?
a) Always yes
b) Not necessarily (consistency isn't transitive)
c) Always no
d) Only for base types

### Q18. What's the consistency of `Unit ~ ?`?
a) Yes
b) No
c) Undefined
d) Error

### Q19. Is `? -> ? ~ Nat`?
a) Yes
b) No (function not consistent with base type)
c) Through another cast
d) Sometimes

### Q20. Which types are consistent with every type?
a) Nat
b) Only ?
c) All types
d) None

---

## Section 3: Cast Calculus (10 questions)

### Q21. What does `<T => T> v` reduce to?
a) blame
b) v (identity cast)
c) <T => ?>
d) Error

### Q22. What are ground types?
a) All types
b) Base types and ? -> ?
c) Only ?
d) Function types

### Q23. Why does `? -> ?` exist as a ground type?
a) All functions share one runtime tag
b) For efficiency
c) It's the default
d) No reason

### Q24. What happens with `<? => Nat> (<Bool => ?> true)`?
a) Returns true
b) Returns 0
c) blame (ground type mismatch)
d) Loops forever

### Q25. How are function casts distributed?
a) `<A->B => C->D> f = λx. <B=>D>(f(<C=>A>x))`
b) f stays unchanged
c) Only outer type changes
d) Error

### Q26. What is cast insertion?
a) Adding explicit casts to surface language
b) Removing casts
c) Optimizing casts
d) Type checking

### Q27. When is a cast inserted?
a) When types are equal
b) When types are consistent but not equal
c) Always
d) Never

### Q28. What's `<Nat => ?>` called?
a) Projection
b) Injection
c) Reduction
d) Application

### Q29. What's `<? => Nat>` called?
a) Injection
b) Projection
c) Extension
d) Restriction

### Q30. Can `<Nat => Bool> 5` succeed?
a) Yes
b) No (inconsistent types)
c) At runtime
d) Sometimes

---

## Section 4: Blame (10 questions)

### Q31. What does a blame label identify?
a) The type error
b) The source location of the problematic cast
c) The value
d) The function

### Q32. What does positive blame mean?
a) Good code
b) Caller provided wrong type
c) Function is correct
d) No errors

### Q33. What does negative blame mean?
a) Bad code
b) Caller error
c) Function returned wrong type/misused input
d) No blame

### Q34. In `<Bool => Nat>^l true`, who gets blamed?
a) true
b) l (the cast location)
c) Nat
d) Bool

### Q35. Can a fully typed function be blamed?
a) Yes
b) No (blame theorem)
c) Sometimes
d) Only with ?

### Q36. Where does blame originate?
a) Typed code
b) Dynamic code (? boundaries)
c) Everywhere
d) Nowhere

### Q37. What happens when blame is raised?
a) Error message with label
b) Returns default value
c) Continues
d) Tries again

### Q38. In function cast `<A->B => C->D>^l`, what's blame on argument?
a) l
b) l̄ (opposite/negated)
c) No blame
d) Both

### Q39. Why track blame?
a) Debugging
b) Know which code is buggy
c) Error messages
d) All of the above

### Q40. What's `blame^l : T`?
a) A type
b) A term representing runtime type error
c) A label
d) A cast

---

## Section 5: Gradual Guarantees (5 questions)

### Q41. What is type precision?
a) Accuracy of types
b) Ordering where ? is least precise
c) Type size
d) Type complexity

### Q42. What's the static gradual guarantee?
a) Programs run faster
b) Making types more precise preserves typeability
c) All programs type check
d) Types never change

### Q43. What's the dynamic gradual guarantee?
a) Programs are dynamic
b) More precise types don't change behavior (up to blame)
c) Errors are dynamic
d) Types are optional

### Q44. If program P type checks with ?, and we replace ? with T, does P' type check?
a) Always (static gradual guarantee)
b) Never
c) Only if T is compatible
d) Randomly

### Q45. What's the goal of gradual typing?
a) Remove all types
b) Seamlessly mix typed and untyped code
c) Make everything dynamic
d) Eliminate runtime errors

---

## Answer Key

### Section 1: Core Concepts
1. b) Mixing static and dynamic typing
2. c) Dynamic/unknown type
3. b) Consistency
4. a) Yes
5. b) No
6. b) No
7. a) Type conversion at runtime
8. b) Cast t from T₁ to T₂ with blame label l
9. b) Identifying the source of runtime type errors
10. b) Well-typed code can't be blamed

### Section 2: Consistency Relation
11. c) It's NOT transitive
12. a) Yes
13. a) Yes
14. b) No
15. a) Yes
16. b) T₁ ~ S₁ and T₂ ~ S₂
17. b) Not necessarily
18. a) Yes
19. b) No
20. b) Only ?

### Section 3: Cast Calculus
21. b) v (identity cast)
22. b) Base types and ? -> ?
23. a) All functions share one runtime tag
24. c) blame
25. a) Distribution with argument contravariant
26. a) Adding explicit casts
27. b) When types are consistent but not equal
28. b) Injection
29. b) Projection
30. b) No

### Section 4: Blame
31. b) The source location
32. b) Caller provided wrong type
33. c) Function returned wrong type
34. b) l
35. b) No
36. b) Dynamic code
37. a) Error message with label
38. b) l̄ (opposite)
39. d) All of the above
40. b) A term representing runtime type error

### Section 5: Gradual Guarantees
41. b) Ordering where ? is least precise
42. b) Making types more precise preserves typeability
43. b) More precise types don't change behavior
44. a) Always
45. b) Seamlessly mix typed and untyped code

---

## Scoring Guide

- **41-45 correct**: Excellent! You've mastered gradual typing.
- **33-40 correct**: Good understanding. Review blame and guarantees.
- **22-32 correct**: Decent start. Re-work the cast calculus section.
- **Below 22**: Please review the chapter materials carefully.
