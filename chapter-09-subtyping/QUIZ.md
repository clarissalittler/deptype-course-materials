# Chapter 9: Subtyping - Self-Assessment Quiz

Test your understanding of subtyping concepts. Try to answer without looking at the solutions!

---

## Section 1: Basic Subtyping (10 questions)

### Q1. What does `S <: T` mean?
a) S equals T
b) S is a supertype of T
c) S is a subtype of T (S can be used where T is expected)
d) S and T are incompatible

### Q2. Which of the following is TRUE?
a) `Top <: Bool`
b) `Bool <: Bot`
c) `Bot <: Nat`
d) `Nat <: Bool`

### Q3. Every type is a subtype of which type?
a) `Bool`
b) `Bot`
c) `Top`
d) `Nat`

### Q4. Which type is a subtype of every other type?
a) `Top`
b) `Bot`
c) `Bool`
d) None

### Q5. Does `Bool <: Bool` hold?
a) Yes, by reflexivity
b) No, a type can't be its own subtype
c) Only if Bool = Bool
d) Depends on context

### Q6. If `A <: B` and `B <: C`, what can we conclude?
a) `C <: A`
b) `A <: C` (by transitivity)
c) Nothing
d) `B = A`

### Q7. Can there be a value of type `Bot`?
a) Yes, the empty record `{}`
b) Yes, any value works
c) No, Bot is uninhabited (in a sound system)
d) No, but you can create one with `undefined`

### Q8. What is `Top` useful for?
a) Maximum type safety
b) Accepting any value (losing type information)
c) Creating type errors
d) Replacing all other types

### Q9. Which subtyping relationship is WRONG?
a) `Bot <: Top`
b) `Nat <: Top`
c) `Top <: Nat`
d) `Bot <: Nat`

### Q10. In the subtype lattice, which is at the "top"?
a) `Bot`
b) `Top`
c) `Bool`
d) The record with most fields

---

## Section 2: Record Subtyping (10 questions)

### Q11. Which record subtyping holds?
a) `{x: Nat} <: {x: Nat, y: Bool}`
b) `{x: Nat, y: Bool} <: {x: Nat}`
c) Neither
d) Both

### Q12. Why is `{x: Nat, y: Bool} <: {x: Nat}` true?
a) Fewer fields = subtype
b) More fields = subtype (width subtyping)
c) Same fields = subtype
d) It's not true

### Q13. Does `{x: Bot} <: {x: Nat}` hold?
a) No, Bot is special
b) Yes, by depth subtyping (Bot <: Nat)
c) Only if Nat <: Bot
d) Depends on x

### Q14. What is the subtype relationship between these?
`{a: Nat, b: Bool, c: Top}` and `{a: Nat, b: Bool}`

a) First <: Second
b) Second <: First
c) Neither
d) Both (they're equal)

### Q15. Does `{x: Nat, y: Nat} <: {y: Nat, x: Nat}` hold?
a) No, order matters
b) Yes, field order doesn't matter (permutation)
c) Only if x = y
d) Depends on implementation

### Q16. For `{x: {a: Nat, b: Bool}} <: {x: {a: Nat}}`:
a) True (depth + width in nested record)
b) False
c) Invalid syntax
d) Depends on a

### Q17. Which record is a subtype of `{name: Top}`?
a) `{name: Nat}`
b) `{name: Nat, age: Bool}`
c) `{age: Nat}`
d) Both a and b

### Q18. What's the intuition for width subtyping?
a) Smaller records are more specific
b) Bigger records have all the capabilities of smaller ones
c) Fields must match exactly
d) Width doesn't affect subtyping

### Q19. Does `{} <: {x: Nat}` hold?
a) Yes, empty record is subtype of everything
b) No, empty record lacks required field x
c) Yes, by width subtyping
d) Depends on x

### Q20. If `{x: A} <: {x: B}`, what can we conclude?
a) `A = B`
b) `A <: B` (depth subtyping)
c) `B <: A`
d) Nothing

---

## Section 3: Function Subtyping (10 questions)

### Q21. Functions are:
a) Covariant in both argument and result
b) Contravariant in both argument and result
c) Contravariant in argument, covariant in result
d) Covariant in argument, contravariant in result

### Q22. Does `(Top -> Bool) <: (Bool -> Bool)` hold?
a) No
b) Yes (contravariant argument: Bool <: Top)
c) Only if Top = Bool
d) Depends on the function body

### Q23. Does `(Bool -> Bool) <: (Top -> Bool)` hold?
a) Yes
b) No (would need Top <: Bool for argument)
c) Only at runtime
d) Depends on Bool

### Q24. Does `(Nat -> Bot) <: (Nat -> Bool)` hold?
a) No
b) Yes (covariant result: Bot <: Bool)
c) Only if Bool = Bot
d) Invalid

### Q25. For function `f : Animal -> String`, can we use it as `Dog -> String`?
a) Yes, because Dog <: Animal
b) No, wrong direction
c) Only if Animal = Dog
d) Depends on String

### Q26. For function `g : Dog -> String`, can we use it as `Animal -> String`?
a) Yes
b) No (caller might pass Cat, g can't handle it)
c) Only with a cast
d) Depends on runtime

### Q27. What is `(Top -> Bot) <: (Nat -> Bool)`?
a) False
b) True (Nat <: Top and Bot <: Bool)
c) Invalid
d) Depends on context

### Q28. In `(A -> B) -> C`, what's the variance of A?
a) Covariant (+)
b) Contravariant (-)
c) Covariant (- × - = +)
d) Invariant

### Q29. Why is function argument contravariant?
a) It's just a rule
b) The function receives (not provides) the argument
c) Because callers provide the argument
d) Both b and c

### Q30. Does `((Top -> Nat) -> Bool) <: ((Bot -> Nat) -> Bool)` hold?
a) Yes
b) No
c) Invalid
d) Depends on Bool

---

## Section 4: Subsumption and Ascription (5 questions)

### Q31. The subsumption rule allows:
a) Downcasting
b) Upcasting (using subtype where supertype expected)
c) Both
d) Neither

### Q32. What is `true as Top`?
a) Type error
b) A Bool value typed as Top
c) Converts true to Top
d) Invalid syntax

### Q33. Can we write `true as Nat`?
a) Yes
b) No (Bool is not a subtype of Nat)
c) Only at runtime
d) Depends on Nat

### Q34. Where is subsumption applied in type checking?
a) Only in ascription
b) Only in application
c) Application, ascription, and conditionals
d) Everywhere

### Q35. `({x = 0, y = true} as {x: Nat})` has type:
a) `{x: Nat, y: Bool}`
b) `{x: Nat}`
c) `Top`
d) Type error

---

## Section 5: Join and Meet (5 questions)

### Q36. What is `Nat ⊔ Bool`?
a) `Nat`
b) `Bool`
c) `Top`
d) `Bot`

### Q37. What is `{x: Nat, y: Bool} ⊔ {x: Nat, z: Top}`?
a) `{x: Nat, y: Bool, z: Top}`
b) `{x: Nat}`
c) `{}`
d) `Top`

### Q38. Join is used for:
a) Function arguments
b) If-then-else branches
c) Record fields
d) All of the above

### Q39. What is `(Nat -> Bool) ⊔ (Bool -> Nat)`?
a) `(Nat -> Nat)`
b) `(Bot -> Top)`
c) `Top`
d) `(Bool -> Bool)`

### Q40. What is `Bot ⊔ Nat`?
a) `Bot`
b) `Nat`
c) `Top`
d) Error

---

## Answer Key

### Section 1: Basic Subtyping
1. c) S is a subtype of T
2. c) Bot <: Nat
3. c) Top
4. b) Bot
5. a) Yes, by reflexivity
6. b) A <: C (by transitivity)
7. c) No, Bot is uninhabited
8. b) Accepting any value
9. c) Top <: Nat
10. b) Top

### Section 2: Record Subtyping
11. b) {x: Nat, y: Bool} <: {x: Nat}
12. b) More fields = subtype
13. b) Yes, by depth subtyping
14. a) First <: Second
15. b) Yes, field order doesn't matter
16. a) True
17. d) Both a and b
18. b) Bigger records have all capabilities
19. b) No, lacks required field
20. b) A <: B

### Section 3: Function Subtyping
21. c) Contravariant arg, covariant result
22. b) Yes
23. b) No
24. b) Yes
25. a) Yes
26. b) No
27. b) True
28. c) Covariant (- × - = +)
29. d) Both b and c
30. a) Yes (Bot <: Top, so Top -> Nat <: Bot -> Nat)

### Section 4: Subsumption and Ascription
31. b) Upcasting
32. b) A Bool value typed as Top
33. b) No
34. c) Application, ascription, conditionals
35. b) {x: Nat}

### Section 5: Join and Meet
36. c) Top
37. b) {x: Nat}
38. b) If-then-else branches
39. b) (Bot -> Top)
40. b) Nat

---

## Scoring Guide

- **36-40 correct**: Excellent! You've mastered subtyping.
- **28-35 correct**: Good understanding. Review the topics you missed.
- **20-27 correct**: Decent start. Re-read the tutorial for weak areas.
- **Below 20**: Please review the chapter materials before proceeding.

---

## Targeted Review

If you missed questions in:
- **Section 1**: Review README.md "Overview" and "Types" sections
- **Section 2**: Review "Record Subtyping" and work through TUTORIAL.md Part 2
- **Section 3**: Focus on "Function Subtyping" and TUTORIAL.md Part 3
- **Section 4**: Study "Typing Rules with Subsumption" in README.md
- **Section 5**: Review "Join and Meet" section and TUTORIAL.md Part 5
