# Chapter 3: STLC with Algebraic Data Types - Self-Check Quiz

## Instructions

Test your understanding of ADTs in STLC. Try to answer without looking at materials, then check answers at the end.

**Scoring Guide**:
- 24-27 correct: Excellent! Ready for Chapter 4
- 20-23 correct: Good! Review missed topics
- 16-19 correct: Decent! More practice needed
- Below 16: Review chapter and tutorial

---

## Section 1: Product Types (Questions 1-4)

### Question 1
What is the type of `(true, 0)`?

A) `Bool × Nat`
B) `Nat × Bool`
C) `Bool + Nat`
D) `(Bool, Nat)`

### Question 2
What does `fst (false, succ 0)` evaluate to?

A) `false`
B) `succ 0`
C) `1`
D) Type error

### Question 3
What is the type of `λp:Nat×Bool. snd p`?

A) `Nat × Bool → Bool`
B) `Nat × Bool → Nat`
C) `Bool → Nat`
D) `Nat → Bool`

### Question 4
Can you nest product types like `((true, 0), false)`?

A) No, pairs can only contain base types
B) No, this is a syntax error
C) Yes, type is `(Bool × Nat) × Bool`
D) Yes, but only with records

---

## Section 2: Sum Types (Questions 5-8)

### Question 5
Why do we need type annotations on `inl` and `inr`?

A) For syntax highlighting
B) To specify the type of the "other" alternative
C) To make the code more readable
D) They're optional

### Question 6
What is the type of `inl[Nat] true`?

A) `Bool`
B) `Bool × Nat`
C) `Bool + Nat`
D) `Nat + Bool`

### Question 7
In a case expression, what must be true about the types of both branches?

A) They can be any types
B) They must be the same type
C) One must be Bool
D) They must be base types

### Question 8
What does this evaluate to?
```
case (inr[Bool] 0) of
  inl b => b
| inr n => iszero n
```

A) `0`
B) `false`
C) `true`
D) Type error

---

## Section 3: Option Type Pattern (Questions 9-11)

### Question 9
How is `Option τ` typically encoded?

A) `τ + τ`
B) `Unit + τ`
C) `Bool + τ`
D) `τ × Unit`

### Question 10
What is the type of `none` in `Option Nat`?

A) `Unit`
B) `Nat`
C) `Unit + Nat`
D) `Option Nat` (not valid - needs annotation)

### Question 11
What problem does Option solve compared to null in other languages?

A) It's faster
B) It uses less memory
C) It makes absence explicit in the type system
D) It allows any value to be null

---

## Section 4: Records (Questions 12-14)

### Question 12
What is the type of `{x=0, y=true}`?

A) `{x:Nat, y:Bool}`
B) `{0:Nat, true:Bool}`
C) `Nat × Bool`
D) `{Bool, Nat}`

### Question 13
How do you access the `x` field of a record `r`?

A) `r[x]`
B) `r.x`
C) `fst r`
D) `get r x`

### Question 14
What's the key difference between `(0, true)` and `{x=0, y=true}`?

A) No difference - they're the same
B) Records have named fields, pairs use positions
C) Records are faster
D) Pairs can only have two elements

---

## Section 5: Variants (Questions 15-17)

### Question 15
What is the syntax for creating a variant value?

A) `<circle=5>`
B) `<circle=5> as Shape`
C) `variant circle 5`
D) `{circle: 5}`

### Question 16
How are variants different from sums?

A) Variants are faster
B) Variants use named tags instead of inl/inr
C) Variants can only have two alternatives
D) Variants don't require pattern matching

### Question 17
What must be true for a variant case expression to type check?

A) All alternatives must have the same type
B) All branches must return the same type
C) Must use all possible tags
D) Both B and C

---

## Section 6: Lists (Questions 18-21)

### Question 18
What is the type of `[]`?

A) `List`
B) `List Unit`
C) `List τ` for any τ
D) Cannot determine without context

### Question 19
What is the type of `0 :: 1 :: []`?

A) `Nat`
B) `List Nat`
C) `Nat × Nat`
D) `List (Nat × Nat)`

### Question 20
What are the two constructors for lists?

A) `fst` and `snd`
B) `inl` and `inr`
C) `[]` and `::`
D) `nil` and `cons`

### Question 21
To pattern match on a list, what cases must you handle?

A) Only empty list
B) Only non-empty list
C) Both empty (`[]`) and non-empty (`x::xs`)
D) All possible lengths

---

## Section 7: Pattern Matching (Questions 22-24)

### Question 22
What does the wildcard pattern `_` mean?

A) Match anything but don't bind a variable
B) Match nothing
C) Type error
D) Match only unit values

### Question 23
Is this pattern match exhaustive?
```
match opt with
  inl u => ...
```

A) Yes
B) No, missing `inr` case
C) Depends on the type of opt
D) Pattern matching doesn't require exhaustiveness

### Question 24
Can you nest patterns like `(x, y)::rest`?

A) No, patterns must be flat
B) Yes, this matches a list whose head is a pair
C) Only if you use records
D) Syntax error

---

## Section 8: Type Safety (Questions 25-27)

### Question 25
Do ADTs affect the Progress theorem?

A) No, Progress still holds with new value forms
B) Yes, ADTs break Progress
C) Progress doesn't apply to ADTs
D) Only for recursive ADTs

### Question 26
Do ADTs affect strong normalization?

A) Yes, ADTs allow infinite loops
B) No, all well-typed terms still terminate
C) Only sums affect termination
D) Only products affect termination

### Question 27
Are ADTs enough to make STLC Turing-complete?

A) Yes, we can now write any program
B) No, we still need general recursion
C) Yes, through nested lists
D) Only with variants

---

## Answers

<details>
<summary>Click to reveal answers (try the quiz first!)</summary>

### Section 1: Product Types

**Q1: A** - `Bool × Nat`
- First element is Bool, second is Nat
- Product type notation: `τ₁ × τ₂`

**Q2: A** - `false`
- `fst` extracts the first component of a pair
- `fst (v₁, v₂)` → `v₁`

**Q3: A** - `Nat × Bool → Bool`
- Takes a pair of Nat and Bool
- `snd` returns the Bool (second component)

**Q4: C** - Yes, type is `(Bool × Nat) × Bool`
- Products can be nested
- Pair of (a pair and a boolean)

### Section 2: Sum Types

**Q5: B** - To specify the type of the "other" alternative
- `inl[τ₂]` needs to know what τ₂ is
- Type checker can't infer the unused alternative

**Q6: C** - `Bool + Nat`
- `inl[Nat]` puts Bool on the left
- Result type: `Bool + Nat`

**Q7: B** - They must be the same type
- Both branches must return the same type τ
- Otherwise, what type does the whole case expression have?

**Q8: C** - `true`
- `inr[Bool] 0` is a sum with Nat on the right
- Takes the right branch: `iszero 0` → `true`

### Section 3: Option Type

**Q9: B** - `Unit + τ`
- Left alternative (Unit) represents "none"
- Right alternative (τ) represents "some value"

**Q10: C** - `Unit + Nat`
- `none = inl[Nat] ()`
- Type is `Unit + Nat` (which is `Option Nat`)

**Q11: C** - It makes absence explicit in the type system
- With null, any value might be null
- With Option, the type tells you "this might not exist"
- Compiler enforces checking both cases

### Section 4: Records

**Q12: A** - `{x:Nat, y:Bool}`
- Record type lists field names and their types
- Fields `x` and `y` with types Nat and Bool

**Q13: B** - `r.x`
- Dot notation for projection
- `t.l` accesses field `l` of record `t`

**Q14: B** - Records have named fields, pairs use positions
- `(0, true)` - access with fst/snd (position-based)
- `{x=0, y=true}` - access with .x/.y (name-based)
- Much more readable!

### Section 5: Variants

**Q15: B** - `<circle=5> as Shape`
- Need the tag name: `circle`
- Need the type annotation: `as Shape`
- Contains the value: `5`

**Q16: B** - Variants use named tags instead of inl/inr
- `inl[Nat] true` vs `<left=true> as Either Bool Nat`
- Named tags are more readable
- Can have more than two alternatives

**Q17: D** - Both B and C
- All branches must return the same type (B)
- Must handle all possible tags for exhaustiveness (C)

### Section 6: Lists

**Q18: D** - Cannot determine without context
- `[]` is polymorphic - it could be `List Nat`, `List Bool`, etc.
- Needs type annotation or context to determine element type

**Q19: B** - `List Nat`
- `0 :: 1 :: []` is a list containing 0 and 1
- Element type is Nat, so `List Nat`

**Q20: C** - `[]` and `::`
- `[]` creates empty list
- `::` (cons) prepends element to list

**Q21: C** - Both empty (`[]`) and non-empty (`x::xs`)
- Lists have two constructors
- Must handle both for exhaustive pattern match

### Section 7: Pattern Matching

**Q22: A** - Match anything but don't bind a variable
- Use when you don't need the value
- Example: `(_, y)` ignores first component

**Q23: B** - No, missing `inr` case
- Sum types have two constructors: inl and inr
- Must handle both for exhaustiveness

**Q24: B** - Yes, this matches a list whose head is a pair
- Patterns can be nested
- Matches lists like `(0, true) :: (1, false) :: []`

### Section 8: Type Safety

**Q25: A** - No, Progress still holds with new value forms
- We extend the definition of "value" to include pairs, sums, etc.
- We add reduction rules for the new constructs
- Every well-typed ADT term is either a value or can step

**Q26: B** - No, all well-typed terms still terminate
- ADTs don't add general recursion
- Products/sums/records/variants combine finite terms
- Lists are finite (no infinite lists without fix)
- Strong normalization still holds

**Q27: B** - No, we still need general recursion
- ADTs add data structures
- But we can't write infinite loops or general recursion
- Need fixed-point operator (Chapter 5) for Turing-completeness

</details>

---

## Score Interpretation

Count your correct answers:

**24-27 correct (89-100%)**: Excellent! You have mastered ADTs. You understand products, sums, pattern matching, and common patterns. Ready for Chapter 4!

**20-23 correct (74-88%)**: Good! You understand most concepts. Review the questions you missed. Pay special attention to:
- Pattern matching exhaustiveness
- The difference between products/sums and records/variants
- Type safety properties

**16-19 correct (59-73%)**: Decent foundation, but some gaps. Focus review on:
- Sum types and case analysis (if you missed Q5-Q8)
- Pattern matching (if you missed Q22-Q24)
- Records vs variants (if you missed Q12-Q17)
- Type safety (if you missed Q25-Q27)

**Below 16 (< 59%)**: Don't worry! ADTs build on Chapter 2, so review both. Recommendations:
- Re-read TUTORIAL.md sections you struggled with
- Focus on worked examples step-by-step
- Use the REPL to experiment with:
  - Creating pairs and extracting with fst/snd
  - Using inl/inr and case expressions
  - Building and pattern matching lists
- Core topics to master:
  1. Product types (pairs, fst, snd)
  2. Sum types (inl, inr, case)
  3. Pattern matching (all cases must be covered)
  4. Option pattern (Unit + τ)
- Retake the quiz after review

---

## What to Review Based on Your Mistakes

**Missed Q1-Q4?** → Review:
- TUTORIAL.md: Part 1 (Product Types)
- README.md: "Product Types" section
- CHEAT_SHEET.md: Product operations
- Practice creating pairs and using fst/snd in REPL

**Missed Q5-Q8?** → Review:
- TUTORIAL.md: Part 2 (Sum Types and Case Analysis)
- README.md: "Sum Types" section
- COMMON_MISTAKES.md: "Sum Type Mistakes"
- Practice case expressions - make sure both branches type check!

**Missed Q9-Q11?** → Review:
- TUTORIAL.md: Part 3 (Option Type Pattern)
- README.md: "Option Type" example
- This is crucial for real-world programming!
- Understand why Option is safer than null

**Missed Q12-Q14?** → Review:
- TUTORIAL.md: Part 4 (Records)
- README.md: "Record Types" section
- Compare with product types - understand named vs positional

**Missed Q15-Q17?** → Review:
- TUTORIAL.md: Part 5 (Variants and State Machines)
- README.md: "Variant Types" section
- Build a state machine example
- Compare with sum types - understand named vs inl/inr

**Missed Q18-Q21?** → Review:
- TUTORIAL.md: Part 6 (Lists and Recursive Data)
- README.md: "List Types" section
- Do exercises/EXERCISES.md: Exercise 1
- Practice recursive functions on lists

**Missed Q22-Q24?** → Review:
- TUTORIAL.md: Part 7 (Advanced Pattern Matching)
- README.md: "Pattern Matching Semantics"
- COMMON_MISTAKES.md: "Non-Exhaustive Patterns"
- This is critical for writing safe code!

**Missed Q25-Q27?** → Review:
- TUTORIAL.md: Part 8 (Type Safety Proofs)
- README.md: "Metatheory" section
- Understand why ADTs preserve type safety
- See that we still can't write infinite loops

---

## Next Steps

- **Scored well?** Move on to Chapter 4: Hindley-Milner Type Inference
  - Learn how to write code WITHOUT type annotations
  - Understand algorithm W
  - See how ML and Haskell work

- **Need review?** Revisit relevant sections, then retake quiz
  - Focus especially on pattern matching
  - Make sure you understand Option/Either patterns
  - These patterns appear everywhere in real code!

- **Want more practice?** Complete all exercises in exercises/EXERCISES.md
  - Exercise 1: List operations
  - Exercise 2: Binary trees
  - Exercise 3: Option operations
  - Exercise 4: Expression evaluator
  - These solidify your understanding!

- **Feeling stuck?** That's normal! ADTs are a big step up in expressiveness.
  - Take a break
  - Work through TUTORIAL examples in the REPL
  - Try the exercises with simpler test cases first

Remember: ADTs are the foundation of modern type systems. Languages like Rust, Swift, Kotlin, TypeScript, Haskell, OCaml, and F# all use these concepts extensively. Master them here, and you'll recognize them everywhere!
