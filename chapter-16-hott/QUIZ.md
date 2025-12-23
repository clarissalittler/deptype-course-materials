# Chapter 16: Homotopy Type Theory - Self-Assessment Quiz

Test your understanding of Homotopy Type Theory. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. In HoTT, what does a type represent?
a) A set
b) A space
c) A number
d) A function

### Q2. What does a term a : A represent in HoTT?
a) A subset
b) A point in the space A
c) A function
d) An error

### Q3. What does the identity type `Id A a b` represent?
a) Boolean equality
b) The type of paths from a to b
c) A comparison function
d) Type equality

### Q4. Can there be multiple paths between two points?
a) No, paths are unique
b) Yes, there can be many paths
c) Only in special cases
d) Never in type theory

### Q5. What is refl in HoTT?
a) A reflection function
b) The constant/trivial path at a point
c) A proof of falsity
d) Type reflection

### Q6. What is the type of `refl a`?
a) A
b) Bool
c) `Id A a a`
d) Unit

### Q7. What is the J eliminator?
a) A jumping function
b) Path induction: reduce path problems to refl
c) A judgment
d) A Java function

### Q8. What is the computation rule for J?
a) J always loops
b) `J C base a a refl = base a`
c) J never reduces
d) `J = refl`

### Q9. What does "paths between paths" mean?
a) Error
b) 2-dimensional paths (homotopies)
c) Impossible
d) Same as paths

### Q10. What structure do paths form?
a) Ring
b) Group
c) Groupoid (paths with composition and inverse)
d) Field

---

## Section 2: Path Operations (10 questions)

### Q11. What does `sym : Id A a b → Id A b a` do?
a) Creates a symbol
b) Reverses a path
c) Duplicates a path
d) Deletes a path

### Q12. What is `sym refl`?
a) Error
b) refl
c) Empty path
d) sym

### Q13. What does `trans : Id A a b → Id A b c → Id A a c` do?
a) Translates
b) Composes two paths
c) Transforms types
d) Transposes

### Q14. What is `trans refl p`?
a) refl
b) p
c) Error
d) trans p

### Q15. What does `ap f : Id A a b → Id B (f a) (f b)` do?
a) Applies function to values
b) Maps a path through a function
c) Creates a function
d) Approximates

### Q16. What is `ap f refl`?
a) f
b) refl
c) ap
d) Error

### Q17. What does transport do?
a) Moves data along a path
b) Ships packages
c) Creates transport
d) Nothing

### Q18. What is `transport P refl x`?
a) P
b) refl
c) x (unchanged)
d) Error

### Q19. Which is NOT a groupoid law for paths?
a) `trans refl p = p`
b) `trans p (sym p) = refl`
c) `trans p q = trans q p` (commutativity)
d) `trans (trans p q) r = trans p (trans q r)`

### Q20. What type does `trans p (sym p)` have?
a) Error
b) `Id A a a` (same start and end)
c) `Id A a b`
d) Unit

---

## Section 3: J Eliminator (10 questions)

### Q21. What is J's motive C?
a) A constant
b) A type family depending on endpoints and path
c) A term
d) J itself

### Q22. Why does J only need a base case for refl?
a) Optimization
b) All paths are essentially like refl (contractibility)
c) Other paths don't exist
d) Error handling

### Q23. How do you derive sym using J?
a) Can't derive it
b) Use motive `C = λx y p. Id A y x`
c) Use motive `C = λx y p. Nat`
d) Primitive operation

### Q24. What does the base case of J prove?
a) Nothing
b) The property holds for all refl paths
c) The property fails
d) Termination

### Q25. Can J define transport?
a) No
b) Yes, with appropriate motive
c) Only sometimes
d) Only for Bool

### Q26. What happens when J is applied to non-refl paths?
a) Error
b) Still produces a valid proof, but doesn't compute to base
c) Returns refl
d) Loops

### Q27. Is J the only elimination principle for paths?
a) Yes
b) No, there's also pattern matching
c) Cubical type theory has others
d) Only for identity types

### Q28. What is "based path induction"?
a) Another name for J
b) A variant of J where one endpoint is fixed
c) Induction on bases
d) Based on nothing

### Q29. Does J give definitional equality for all paths?
a) Yes, always
b) No, only for refl (propositional for others)
c) Never
d) Only in Agda

### Q30. What is uniqueness of identity proofs (UIP)?
a) Each path is unique
b) All paths between same points are equal
c) Required in HoTT
d) A programming pattern

---

## Section 4: Higher Structure (10 questions)

### Q31. What are 2-paths?
a) Two paths
b) Paths between paths
c) Twice as long
d) Error

### Q32. What is an ∞-groupoid?
a) Infinite group
b) Structure with paths at all dimensions
c) Infinitely large type
d) Error

### Q33. Are the groupoid laws paths themselves?
a) No, they're boolean
b) Yes, they're paths between paths
c) Only sometimes
d) Never

### Q34. What is an h-level?
a) Height level
b) Classification of types by path complexity
c) Horizontal level
d) Happy level

### Q35. What h-level are sets?
a) -2
b) -1
c) 0
d) 1

### Q36. What h-level are propositions?
a) -2
b) -1
c) 0
d) 1

### Q37. What is a contractible type?
a) A type that shrinks
b) A type with unique element up to path (h-level -2)
c) An empty type
d) A small type

### Q38. Is Unit contractible?
a) No
b) Yes
c) Sometimes
d) Depends

### Q39. What are higher inductive types?
a) Types with path constructors
b) Higher-order functions
c) Induced types
d) Error

### Q40. What is the circle S¹ as a HIT?
a) Just a point
b) A point with a loop path
c) Two points
d) Can't be defined

---

## Section 5: Univalence (5 questions)

### Q41. What does univalence say?
a) All types are equal
b) Equivalent types are equal
c) Types are values
d) Nothing

### Q42. What notation is used for univalence?
a) A = B
b) (A ≃ B) ≃ (A = B)
c) A → B
d) A + B

### Q43. What does univalence imply?
a) Nothing useful
b) Function extensionality
c) Type erasure
d) Faster code

### Q44. Is univalence provable in vanilla type theory?
a) Yes
b) No, it's an axiom
c) Sometimes
d) Only in Coq

### Q45. What is cubical type theory's advantage?
a) Faster
b) Makes univalence compute
c) Simpler
d) No advantage

---

## Answer Key

### Section 1: Core Concepts
1. b) A space
2. b) A point in the space A
3. b) The type of paths from a to b
4. b) Yes, there can be many paths
5. b) The constant/trivial path at a point
6. c) `Id A a a`
7. b) Path induction
8. b) `J C base a a refl = base a`
9. b) 2-dimensional paths (homotopies)
10. c) Groupoid

### Section 2: Path Operations
11. b) Reverses a path
12. b) refl
13. b) Composes two paths
14. b) p
15. b) Maps a path through a function
16. b) refl
17. a) Moves data along a path
18. c) x (unchanged)
19. c) Commutativity (paths aren't commutative)
20. b) `Id A a a`

### Section 3: J Eliminator
21. b) A type family depending on endpoints and path
22. b) All paths are essentially like refl
23. b) Use motive `C = λx y p. Id A y x`
24. b) The property holds for all refl paths
25. b) Yes, with appropriate motive
26. b) Still produces valid proof, doesn't compute
27. c) Cubical type theory has others
28. b) A variant where one endpoint is fixed
29. b) No, only for refl
30. b) All paths between same points are equal

### Section 4: Higher Structure
31. b) Paths between paths
32. b) Structure with paths at all dimensions
33. b) Yes, they're paths between paths
34. b) Classification of types by path complexity
35. c) 0
36. b) -1
37. b) Unique element up to path
38. b) Yes
39. a) Types with path constructors
40. b) A point with a loop path

### Section 5: Univalence
41. b) Equivalent types are equal
42. b) (A ≃ B) ≃ (A = B)
43. b) Function extensionality
44. b) No, it's an axiom
45. b) Makes univalence compute

---

## Scoring Guide

- **41-45 correct**: Excellent! You've grasped HoTT deeply.
- **33-40 correct**: Good understanding. Review J and higher structure.
- **22-32 correct**: Decent start. Re-work path operations.
- **Below 22**: Please review the chapter materials carefully.
