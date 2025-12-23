# Chapter 15: Recursive Types (μ Types) - Self-Assessment Quiz

Test your understanding of recursive types. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What does μα.T mean?
a) Multiply α by T
b) A recursive type where α refers to the whole type
c) The smallest α in T
d) Type equality

### Q2. In μα. Unit + (Nat × α), what does α represent?
a) Unit
b) Nat
c) The list type itself
d) A number

### Q3. What is the purpose of recursive types?
a) Faster execution
b) Allowing types to refer to themselves
c) Type inference
d) Memory management

### Q4. Why can't we define lists in simply typed lambda calculus?
a) No recursion
b) No self-referential types
c) No sum types
d) Too slow

### Q5. What are the two semantics for recursive types?
a) Static and dynamic
b) Iso-recursive and equi-recursive
c) Strong and weak
d) Fast and slow

### Q6. In iso-recursive types, what's the relationship between μα.T and T[μα.T/α]?
a) Equal
b) Isomorphic but not equal
c) Unrelated
d) Subtype

### Q7. What operations mediate the isomorphism?
a) cons and nil
b) fold and unfold
c) left and right
d) in and out

### Q8. What does T[μα.T/α] mean?
a) T divided by α
b) Substitute μα.T for α in T
c) T minus α
d) Compare T and α

### Q9. What happens when you unfold a fold?
a) Error
b) They cancel out
c) Loops forever
d) Type error

### Q10. Which languages use iso-recursive types?
a) JavaScript
b) OCaml, Haskell, Rust
c) Python
d) None

---

## Section 2: Fold and Unfold (10 questions)

### Q11. What's the type of fold?
a) `μα.T → T`
b) `T[μα.T/α] → μα.T`
c) `T → μα.T`
d) `α → μα.T`

### Q12. What's the type of unfold?
a) `μα.T → T[μα.T/α]`
b) `T → μα.T`
c) `μα.T → T`
d) `α → T`

### Q13. Why is fold needed?
a) Performance
b) To wrap a value into the recursive type
c) For pattern matching
d) Type inference

### Q14. Why is unfold needed?
a) To unwrap and examine a recursive value
b) Performance
c) For type errors
d) Memory

### Q15. What's `unfold [μα. Nat] (fold [μα. Nat] 5)`?
a) μα. Nat
b) 5
c) Error
d) fold 5

### Q16. Is `fold [NatList] (inl unit)` valid?
a) Yes, it's nil
b) No, missing unfold
c) No, wrong type
d) Only sometimes

### Q17. What type does `fold [μα. A + B]` expect as input?
a) A + B
b) A + (μα. A + B)
c) The substituted type: A + B where α is replaced by μα. A + B
d) Just A

### Q18. For `NatList = μα. Unit + (Nat × α)`, what's the unfolded type?
a) `Unit + Nat`
b) `Unit + (Nat × NatList)`
c) `NatList × NatList`
d) `Unit`

### Q19. Can you nest folds?
a) No
b) Yes (e.g., for nested structures)
c) Only once
d) Only for lists

### Q20. In evaluation, what is `unfold (fold v)` when v is a value?
a) fold v
b) v
c) unfold v
d) Error

---

## Section 3: Data Structures (10 questions)

### Q21. What's the type for natural number lists?
a) `μα. Nat × α`
b) `μα. Unit + (Nat × α)`
c) `μα. Nat + α`
d) `Nat → Nat`

### Q22. What represents the empty list?
a) `fold (inr unit)`
b) `fold (inl unit)`
c) `nil`
d) Just `unit`

### Q23. What represents cons?
a) `fold (inl <n, l>)`
b) `fold (inr <n, l>)`
c) `inr <n, l>`
d) `<n, l>`

### Q24. For binary trees `μα. Nat + (α × α)`, what's a leaf?
a) `fold (inr n)`
b) `fold (inl n)`
c) `inl n`
d) Just n

### Q25. For binary trees, what's a branch?
a) `fold (inl <l, r>)`
b) `fold (inr <l, r>)`
c) `inr <l, r>`
d) `<l, r>`

### Q26. What's the type for infinite streams of Nat?
a) `μα. Nat + α`
b) `μα. Nat × α`
c) `μα. Unit + (Nat × α)`
d) `Nat → Nat`

### Q27. Why don't streams have a Unit case?
a) Optimization
b) They're always infinite (no empty case)
c) Type error
d) Not needed

### Q28. What's `head` for streams?
a) `λs. unfold s`
b) `λs. fst (unfold s)`
c) `λs. snd (unfold s)`
d) `λs. fold s`

### Q29. What's `tail` for streams?
a) `λs. fst (unfold s)`
b) `λs. snd (unfold s)`
c) `λs. unfold s`
d) `λs. fold s`

### Q30. Can you pattern match directly on a μ type value?
a) Yes
b) No, must unfold first
c) Only for lists
d) Only in equi-recursive

---

## Section 4: Self-Application and Termination (10 questions)

### Q31. Why can't STLC type `λx. x x`?
a) Syntax error
b) Would need T = T → S (impossible)
c) x is undefined
d) Too complex

### Q32. What type enables self-application?
a) `μα. Nat`
b) `μα. α → T`
c) `Nat → Nat`
d) `Unit`

### Q33. For `SelfApp = μα. α → Nat`, what's `unfold [SelfApp] x`?
a) `Nat`
b) `SelfApp → Nat`
c) `SelfApp`
d) `α → Nat`

### Q34. What is the omega combinator?
a) `λx. x`
b) `λx. (unfold x) x`
c) `λx. fold x`
d) `λx. x x` (untyped)

### Q35. Does `omega (fold omega)` terminate?
a) Yes, returns 0
b) No, loops forever
c) Type error
d) Returns omega

### Q36. What property does adding μ types break?
a) Type safety
b) Strong normalization (all programs terminate)
c) Subject reduction
d) Type preservation

### Q37. Can you write a typed Y combinator with μ types?
a) No
b) Yes
c) Only for some types
d) Only without fold

### Q38. What is general recursion?
a) Loops
b) Ability to write recursive functions without primitive recursion
c) For loops
d) While loops

### Q39. Does termination checking work with μ types?
a) Always
b) Never
c) Must be done carefully (structural recursion)
d) Only for lists

### Q40. Are all μ type values finite?
a) Yes
b) No (streams are infinite)
c) Only lists
d) Only trees

---

## Section 5: Advanced Topics (5 questions)

### Q41. What's the difference between iso and equi-recursive?
a) Speed
b) Iso needs explicit fold/unfold, equi treats types as equal
c) Memory usage
d) Syntax only

### Q42. What are positive occurrences?
a) Numbers > 0
b) Occurrences of α in covariant positions
c) Valid types
d) Recursive calls

### Q43. Why do positive occurrences matter?
a) Performance
b) Negative occurrences can cause logical inconsistency
c) Type inference
d) Memory

### Q44. What's the connection between μ and fixed points?
a) None
b) μα.T is the least fixed point of the type operator F(α) = T
c) They're opposites
d) Only in math

### Q45. Can you encode mutual recursion with μ?
a) No
b) Yes, with products or sums
c) Only for two types
d) Only for lists

---

## Answer Key

### Section 1: Core Concepts
1. b) A recursive type where α refers to the whole type
2. c) The list type itself
3. b) Allowing types to refer to themselves
4. b) No self-referential types
5. b) Iso-recursive and equi-recursive
6. b) Isomorphic but not equal
7. b) fold and unfold
8. b) Substitute μα.T for α in T
9. b) They cancel out
10. b) OCaml, Haskell, Rust

### Section 2: Fold and Unfold
11. b) `T[μα.T/α] → μα.T`
12. a) `μα.T → T[μα.T/α]`
13. b) To wrap a value into the recursive type
14. a) To unwrap and examine a recursive value
15. b) 5
16. a) Yes, it's nil
17. c) The substituted type
18. b) `Unit + (Nat × NatList)`
19. b) Yes
20. b) v

### Section 3: Data Structures
21. b) `μα. Unit + (Nat × α)`
22. b) `fold (inl unit)`
23. b) `fold (inr <n, l>)`
24. b) `fold (inl n)`
25. b) `fold (inr <l, r>)`
26. b) `μα. Nat × α`
27. b) They're always infinite
28. b) `λs. fst (unfold s)`
29. b) `λs. snd (unfold s)`
30. b) No, must unfold first

### Section 4: Self-Application and Termination
31. b) Would need T = T → S
32. b) `μα. α → T`
33. b) `SelfApp → Nat`
34. b) `λx. (unfold x) x`
35. b) No, loops forever
36. b) Strong normalization
37. b) Yes
38. b) Ability to write recursive functions
39. c) Must be done carefully
40. b) No (streams are infinite)

### Section 5: Advanced Topics
41. b) Iso needs explicit fold/unfold
42. b) Occurrences in covariant positions
43. b) Negative occurrences can cause inconsistency
44. b) μα.T is the least fixed point
45. b) Yes, with products or sums

---

## Scoring Guide

- **41-45 correct**: Excellent! You've mastered recursive types.
- **33-40 correct**: Good understanding. Review self-application and streams.
- **22-32 correct**: Decent start. Re-work the fold/unfold examples.
- **Below 22**: Please review the chapter materials carefully.
