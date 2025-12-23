# Chapter 14: Row Types & Extensible Records - Self-Assessment Quiz

Test your understanding of row types. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What is a row type?
a) A type for database rows
b) A mapping from labels to types, possibly with a tail variable
c) An array type
d) A matrix type

### Q2. What does `{x: Nat | ρ}` mean?
a) x is Nat or ρ
b) Record with at least field x: Nat, plus unknown fields ρ
c) x and ρ are both Nat
d) x exclusive or ρ

### Q3. What is row polymorphism?
a) Polymorphism over numbers
b) Ability to write functions that work with records having "at least" certain fields
c) Polymorphism over rows in a table
d) Multiple rows of types

### Q4. What problem does row polymorphism solve?
a) Performance
b) Closed record types can't express "at least these fields"
c) Memory management
d) Parsing

### Q5. What is `∀ρ. T` in row polymorphism?
a) For all types ρ
b) Polymorphic over row variable ρ
c) T contains ρ
d) ρ equals T

### Q6. What is the empty row?
a) {}
b) ()
c) null
d) void

### Q7. How do you read `<l: T | ρ>`?
a) l implies T with ρ
b) Polymorphic variant with at least case l: T
c) l is less than T given ρ
d) Array of l

### Q8. What's the dual of extensible records?
a) Functions
b) Polymorphic variants
c) Arrays
d) Strings

### Q9. What language feature is row polymorphism similar to?
a) Inheritance
b) Structural typing / duck typing
c) Dynamic typing
d) Pattern matching

### Q10. Can row labels appear in any order?
a) No, must be alphabetical
b) Yes, order doesn't matter
c) Only for base types
d) Depends on implementation

---

## Section 2: Record Operations (10 questions)

### Q11. What does `r.l` do?
a) Multiplies r and l
b) Projects (accesses) field l from record r
c) Compares r and l
d) Creates a new record

### Q12. What is `{l = t | r}` syntax for?
a) Pattern matching
b) Record extension (adding field l with value t)
c) Record deletion
d) Type annotation

### Q13. What does `r \ l` do?
a) Divides r by l
b) Record restriction (removes field l)
c) Checks if l is in r
d) Clones r

### Q14. For `{l = t | r}`, what constraint exists?
a) t must be a number
b) l must not already be in r
c) r must be empty
d) No constraint

### Q15. How do you update a field in a row-polymorphic way?
a) Direct assignment
b) Remove then add: `{l = newVal | r \ l}`
c) Mutation
d) Can't be done

### Q16. What's the type of `{x = 5 | {y = true}}`?
a) `{x: Nat}`
b) `{x: Nat, y: Bool}`
c) `{y: Bool}`
d) `Nat`

### Q17. What's `{x = 1, y = 2} \ x`?
a) `{x = 1}`
b) `{y = 2}`
c) `1`
d) Error

### Q18. Can you extend a record with a field that already exists?
a) Yes, overwrites
b) No, type error
c) Creates duplicate
d) Depends on value

### Q19. For `{name: String | ρ}`, what's the type of `ρ`?
a) String
b) A row (sequence of label-type pairs)
c) Record
d) Any

### Q20. What's the result of `{x = 1}.x`?
a) `{x = 1}`
b) `1`
c) `x`
d) Error

---

## Section 3: Row Polymorphism (10 questions)

### Q21. What type does `λr. r.name` have?
a) `String`
b) `{name: String} -> String`
c) `∀ρ. {name: String | ρ} -> String`
d) `∀ρ. {ρ} -> String`

### Q22. Can `getName : ∀ρ. {name: String | ρ} -> String` accept `{name = "A", age = 5}`?
a) Yes
b) No, types don't match
c) Only with cast
d) Runtime error

### Q23. What does `∀ρ. {x: Nat | ρ} -> {x: Nat | ρ}` mean?
a) Changes x
b) Takes record with at least x, returns record with same structure
c) Only works on {x: Nat}
d) Error type

### Q24. How do you instantiate a row-polymorphic function?
a) Can't
b) `f [(y: Bool)]` or implicitly through unification
c) `f <y: Bool>`
d) `f [y: Bool]`

### Q25. What's `addZ : ∀ρ. Nat -> {ρ} -> {z: Nat | ρ}` useful for?
a) Nothing
b) Adding z field to any record
c) Removing z field
d) Type checking

### Q26. Can row polymorphism express `{x: Nat} | {y: Bool}`?
a) Yes, directly
b) No, rows are about "at least", not "either"
c) Only with variants
d) With special syntax

### Q27. Is `{x: Nat, y: Bool | ρ}` the same as `{y: Bool, x: Nat | ρ}`?
a) No, order matters
b) Yes, order doesn't matter
c) Depends on ρ
d) Only in some systems

### Q28. What's lacking in `Elm`'s extensible records compared to full row polymorphism?
a) Everything
b) Record restriction
c) Field access
d) Record creation

### Q29. For `f : ∀ρ. {x: Nat | ρ} -> Nat`, can f access fields other than x?
a) Yes, through ρ
b) No, only x is known
c) Yes, through reflection
d) Depends on implementation

### Q30. What happens when you unify `{x: Nat | α}` with `{x: Nat, y: Bool}`?
a) Error
b) α is solved to (y: Bool)
c) α is solved to ()
d) Infinite loop

---

## Section 4: Polymorphic Variants (10 questions)

### Q31. What is a polymorphic variant?
a) A variable that changes type
b) An open sum type
c) A polymorphic function
d) A variant of polymorphism

### Q32. What does `<ok: Nat | error: String | ρ>` mean?
a) ok and error are alternates
b) Variant with at least ok: Nat and error: String cases
c) ok implies error
d) Three separate types

### Q33. How do you create a variant value?
a) `ok(42)`
b) `<ok = 42>`
c) `Ok 42`
d) `variant ok 42`

### Q34. What's the type of `<ok = 42>`?
a) `Nat`
b) `<ok: Nat>`
c) `<ok: Nat | ρ>` (open)
d) `Ok`

### Q35. In case analysis, what handles remaining cases?
a) default
b) `<other = x>` pattern
c) else
d) Nothing needed

### Q36. Can variants have more cases than the handler covers?
a) No, must be exhaustive
b) Yes, with open variants
c) Only at runtime
d) Never

### Q37. What's the dual relationship?
a) Records have "at least" fields, variants have "at least" cases
b) Records are sums, variants are products
c) No relationship
d) They're the same

### Q38. How does OCaml write polymorphic variants?
a) `<ok: int>`
b) `[> \`ok of int]`
c) `Ok<int>`
d) `variant<ok, int>`

### Q39. Can you extend variants like records?
a) Yes, add new cases
b) No, variants are fixed
c) Only closed variants
d) With special syntax

### Q40. What's `<l = t> : T` syntax for?
a) Type assertion
b) Variant injection with type annotation
c) Comparison
d) Pattern matching

---

## Section 5: Applications (5 questions)

### Q41. How does PureScript use row types?
a) Only for records
b) For records AND effects
c) Only for effects
d) Doesn't use them

### Q42. Why is row polymorphism better than subtyping for records?
a) Faster
b) Full type inference
c) Simpler
d) More features

### Q43. What's the connection to duck typing?
a) None
b) Row polymorphism is static duck typing
c) Both are dynamic
d) Opposite concepts

### Q44. What are "lack constraints"?
a) Missing types
b) Constraints that a label is NOT in a row
c) Error messages
d) Performance limits

### Q45. How are effect rows (Chapter 12) related?
a) Same machinery (label-to-type mapping)
b) Completely different
c) Only syntactically similar
d) One implements the other

---

## Answer Key

### Section 1: Core Concepts
1. b) Mapping from labels to types
2. b) Record with at least x, plus unknown ρ
3. b) Functions for "at least" certain fields
4. b) Closed records can't express "at least"
5. b) Polymorphic over row variable
6. b) ()
7. b) Variant with at least case l: T
8. b) Polymorphic variants
9. b) Structural typing / duck typing
10. b) Yes, order doesn't matter

### Section 2: Record Operations
11. b) Projects field l
12. b) Record extension
13. b) Record restriction
14. b) l must not already be in r
15. b) Remove then add
16. b) `{x: Nat, y: Bool}`
17. b) `{y = 2}`
18. b) No, type error
19. b) A row
20. b) `1`

### Section 3: Row Polymorphism
21. c) `∀ρ. {name: String | ρ} -> String`
22. a) Yes
23. b) Takes/returns record with same structure
24. b) `f [(y: Bool)]` or implicitly
25. b) Adding z field to any record
26. b) No, rows are "at least"
27. b) Yes, order doesn't matter
28. b) Record restriction
29. b) No, only x is known
30. b) α solved to (y: Bool)

### Section 4: Polymorphic Variants
31. b) An open sum type
32. b) Variant with at least those cases
33. b) `<ok = 42>`
34. c) `<ok: Nat | ρ>` (open)
35. b) `<other = x>` pattern
36. b) Yes, with open variants
37. a) Both have "at least" semantics
38. b) `[> \`ok of int]`
39. a) Yes, add new cases
40. b) Variant injection with type

### Section 5: Applications
41. b) Records AND effects
42. b) Full type inference
43. b) Static duck typing
44. b) Label NOT in row
45. a) Same machinery

---

## Scoring Guide

- **41-45 correct**: Excellent! You've mastered row types.
- **33-40 correct**: Good understanding. Review variants and unification.
- **22-32 correct**: Decent start. Re-work the tutorial examples.
- **Below 22**: Please review the chapter materials carefully.
