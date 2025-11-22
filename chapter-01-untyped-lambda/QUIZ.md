# Chapter 1: Untyped Lambda Calculus - Self-Check Quiz

## Instructions

This quiz tests your understanding of Chapter 1 concepts. Try to answer each question without looking at the materials, then check your answers at the end.

**Scoring Guide**:
- 20-23 correct: Excellent! Ready for Chapter 2
- 16-19 correct: Good! Review any missed topics
- 12-15 correct: Decent! Spend more time with weak areas
- Below 12: Review the chapter and tutorial before continuing

---

## Section 1: Basic Syntax (Questions 1-3)

### Question 1
What are the free variables in the following term?
```
λx. x y z
```

A) {x, y, z}
B) {y, z}
C) {x}
D) {z}

### Question 2
Which of the following are valid lambda terms? (Select all that apply)

A) `λx. λy. x y z`
B) `λ. x`
C) `x y z`
D) `(λx. x x) λy. y`
E) `λx y. x`

### Question 3
How is the term `f g h` parsed according to lambda calculus conventions?

A) `f (g h)`
B) `(f g) h`
C) `f g h` (cannot be parsed - ambiguous)
D) `((f) (g)) (h)`

---

## Section 2: Substitution and Alpha-Conversion (Questions 4-6)

### Question 4
What is the result of `[x ↦ a](λy. x y)`?

A) `λy. a y`
B) `λy. x y`
C) `λa. a y`
D) `λy. a a`

### Question 5
What is the CORRECT result of `[y ↦ x](λx. y)`?

A) `λx. x` (wrong - variable capture!)
B) `λz. x` (correct - after α-conversion)
C) `λx. y` (wrong - didn't substitute)
D) `λy. x` (wrong - changed the parameter incorrectly)

### Question 6
When performing substitution `[x ↦ s](λx. t)`, what happens?

A) Replace all occurrences of x in t with s
B) The term remains unchanged (x is shadowed)
C) Rename x to a fresh variable first
D) Throw an error - invalid substitution

---

## Section 3: Beta-Reduction (Questions 7-9)

### Question 7
What does `(λx. x x) y` reduce to?

A) `x x`
B) `y y`
C) `y x`
D) `λx. y y`

### Question 8
Evaluate `(λx. λy. x) a b` step by step. What is the final result?

A) `a`
B) `b`
C) `a b`
D) `λy. a b`

### Question 9
Which of the following terms is in normal form (cannot be reduced further)?

A) `(λx. x) y`
B) `λx. (λy. y) x`
C) `λx. x y`
D) `x (λy. y)`

---

## Section 4: Evaluation Strategies (Questions 10-11)

### Question 10
Consider the term: `(λx. λy. y) ((λz. z z) (λz. z z)) v`

Under which evaluation strategy does this term terminate?

A) Call-by-value only
B) Normal-order only
C) Both call-by-value and normal-order
D) Neither - it loops forever under both strategies

### Question 11
Which evaluation strategy is "complete" (finds normal form if it exists)?

A) Call-by-value
B) Call-by-name
C) Normal-order
D) All strategies are equally complete

---

## Section 5: Church Booleans (Questions 12-13)

### Question 12
Given Church booleans:
```
true  = λt. λf. t
false = λt. λf. f
```

What does `true a b` reduce to?

A) `true`
B) `a`
C) `b`
D) `a b`

### Question 13
What is the correct implementation of `and` for Church booleans?

A) `λp. λq. p q p`
B) `λp. λq. p q false`
C) `λp. λq. p false q`
D) `λp. λq. p true q`

---

## Section 6: Church Numerals (Questions 14-16)

### Question 14
What number does `λf. λx. f (f (f x))` represent?

A) 1
B) 2
C) 3
D) 4

### Question 15
What is the Church encoding for 0?

A) `λf. λx. x`
B) `λf. λx. f x`
C) `λx. x`
D) `false`

### Question 16
Given `plus = λm. λn. λf. λx. m f (n f x)`, what does `plus 1 2` reduce to?

A) `λf. λx. f x`
B) `λf. λx. f (f x)`
C) `λf. λx. f (f (f x))`
D) `3` (the JavaScript number)

---

## Section 7: Lists and Pairs (Questions 17-18)

### Question 17
Given:
```
pair = λx. λy. λf. f x y
fst  = λp. p (λx. λy. x)
snd  = λp. p (λx. λy. y)
```

What does `fst (pair a b)` reduce to?

A) `a`
B) `b`
C) `pair`
D) `λf. f a b`

### Question 18
For Church-encoded lists where:
```
nil  = λc. λn. n
cons = λh. λt. λc. λn. c h (t c n)
```

What does a list represent?

A) A linked data structure
B) An array
C) A fold (reduce) function
D) A map function

---

## Section 8: Y Combinator (Questions 19-20)

### Question 19
What is the key property of the Y combinator?

A) `Y f = f`
B) `Y f = f (Y f)`
C) `Y f = Y (Y f)`
D) `Y f = λx. f x`

### Question 20
Why doesn't the Y combinator work with call-by-value evaluation?

A) It has a syntax error
B) It immediately expands infinitely
C) It requires named recursion
D) Call-by-value doesn't support recursion

---

## Section 9: Theory (Questions 21-23)

### Question 21
What does the Church-Rosser theorem (confluence) guarantee?

A) All terms have a normal form
B) If a term has a normal form, it's unique
C) Evaluation always terminates
D) All reduction orders give the same number of steps

### Question 22
Which of the following terms does NOT have a normal form?

A) `λx. x x`
B) `(λx. x x) (λx. x x)`
C) `λx. (λy. y) x`
D) `(λx. λy. x) a b`

### Question 23
What does it mean that lambda calculus is Turing-complete?

A) It can compute anything a Turing machine can
B) It always terminates
C) It has built-in types
D) It requires Church encodings

---

## Answers

<details>
<summary>Click to reveal answers (try the quiz first!)</summary>

### Section 1: Basic Syntax

**Q1: B** - {y, z}
- x is bound by λx
- y and z are free (not bound by any λ)

**Q2: A, C, D**
- A: Valid ✓
- B: Invalid - λ must have a parameter
- C: Valid ✓ (just applications of variables)
- D: Valid ✓ (missing parentheses around second lambda, should be `(λx. x x) (λy. y)`, but as written it's `(λx. x x) λy. y` which parses as application of `(λx. x x)` to `λy. y` due to precedence)
- E: Invalid - λ takes one parameter at a time (should be `λx. λy. x`)

**Q3: B** - `(f g) h`
- Application associates to the left

### Section 2: Substitution

**Q4: A** - `λy. a y`
- Substitute a for x
- y is a different variable (bound by λy)
- x is free in the body, so replace it

**Q5: B** - `λz. x`
- Direct substitution would give `λx. x` (WRONG - variable capture!)
- Must α-convert first: `λx. y` → `λz. y`
- Then substitute: `[y ↦ x](λz. y)` = `λz. x`

**Q6: B** - The term remains unchanged
- The λx shadows the outer x
- No substitution happens in the body

### Section 3: Beta-Reduction

**Q7: B** - `y y`
- `[x ↦ y](x x)` = `y y`

**Q8: A** - `a`
- `(λx. λy. x) a` → `λy. a`
- `(λy. a) b` → `a`
- The constant function returns first argument

**Q9: C** - `λx. x y`
- A: Has redex `(λx. x) y`
- B: Has redex `(λy. y) x` inside
- C: No redex ✓
- D: Has redex `(λy. y)` if we reduce under application (though some strategies wouldn't reduce this)

### Section 4: Evaluation Strategies

**Q10: B** - Normal-order only
- Call-by-value tries to evaluate `(λz. z z) (λz. z z)` first → infinite loop
- Normal-order applies outer function first, discards the infinite term, returns `v`

**Q11: C** - Normal-order
- Normal-order is complete (finds normal form if it exists)
- Call-by-value can fail to find normal forms that exist

### Section 5: Church Booleans

**Q12: B** - `a`
- `true a b` = `(λt. λf. t) a b` → `(λf. a) b` → `a`

**Q13: B** - `λp. λq. p q false`
- If p is true: return q
- If p is false: return false
- This implements AND correctly

### Section 6: Church Numerals

**Q14: C** - 3
- `λf. λx. f (f (f x))` applies f three times

**Q15: A** - `λf. λx. x`
- Apply f zero times, just return x

**Q16: C** - `λf. λx. f (f (f x))`
- 1 + 2 = 3
- This is the Church numeral for 3

### Section 7: Lists and Pairs

**Q17: A** - `a`
- `fst (pair a b)` = `(λp. p (λx. λy. x)) (λf. f a b)`
- → `(λf. f a b) (λx. λy. x)`
- → `(λx. λy. x) a b`
- → `a`

**Q18: C** - A fold (reduce) function
- Church-encoded lists ARE their own fold function
- `cons h t` when given combining function c and nil value n returns `c h (t c n)`

### Section 8: Y Combinator

**Q19: B** - `Y f = f (Y f)`
- This is the fixed-point property
- Allows recursion: f receives "itself" as an argument

**Q20: B** - It immediately expands infinitely
- Y combinator: `(λx. f (x x)) (λx. f (x x))`
- With CBV, tries to evaluate `(λx. f (x x)) (λx. f (x x))` before applying
- This reduces to itself → infinite loop
- Need Z combinator for CBV

### Section 9: Theory

**Q21: B** - If a term has a normal form, it's unique
- Confluence means different reduction paths converge
- Normal forms are unique (up to α-equivalence)

**Q22: B** - `(λx. x x) (λx. x x)`
- This is Ω (omega) - the classic infinite loop
- Reduces to itself forever

**Q23: A** - It can compute anything a Turing machine can
- Lambda calculus and Turing machines have equivalent computational power
- Both are universal models of computation

</details>

---

## Score Interpretation

Count your correct answers:

**20-23 correct (87-100%)**: Excellent! You have a solid grasp of lambda calculus fundamentals. You're ready to move on to Chapter 2.

**16-19 correct (70-86%)**: Good! You understand most concepts. Review the questions you missed and make sure you understand why.

**12-15 correct (52-69%)**: Decent foundation, but some gaps. Review:
- Substitution and variable capture (if you missed Q4-Q6)
- Church encodings (if you missed Q12-Q18)
- Evaluation strategies (if you missed Q10-Q11)

**Below 12 (< 52%)**: Don't worry! Lambda calculus is genuinely challenging. Recommendations:
- Re-read TUTORIAL.md sections you struggled with
- Try working through examples step-by-step on paper
- Use the REPL to experiment (`stack run`)
- Focus on these core topics:
  1. Substitution (MOST important - get this right!)
  2. Beta-reduction (how to evaluate)
  3. Church encodings (understanding data as functions)
- Retake the quiz after review

---

## What to Review Based on Your Mistakes

**Missed Q1-Q3?** → Review:
- TUTORIAL.md: Part 1 (Basic Syntax)
- TUTORIAL.md: Part 2 (Free and Bound Variables)
- CHEAT_SHEET.md: Syntax and FV sections

**Missed Q4-Q6?** → Review:
- TUTORIAL.md: Part 3 (Substitution and Alpha-Conversion)
- COMMON_MISTAKES.md: Variable Capture section
- Practice more substitution examples

**Missed Q7-Q9?** → Review:
- TUTORIAL.md: Part 4 (Beta-Reduction)
- Work through examples step-by-step
- Use REPL's `:step` command

**Missed Q10-Q11?** → Review:
- TUTORIAL.md: Part 5 (Evaluation Strategies)
- README.md: "Evaluation Strategies" section
- Try examples with different strategies in REPL

**Missed Q12-Q13?** → Review:
- TUTORIAL.md: Part 6 (Church Booleans)
- Do exercises/EXERCISES.md: Exercise 1
- Trace boolean operations step-by-step

**Missed Q14-Q16?** → Review:
- TUTORIAL.md: Part 7 (Church Numerals)
- Do exercises/EXERCISES.md: Exercise 2
- Focus on understanding "apply f n times"

**Missed Q17-Q18?** → Review:
- TUTORIAL.md: Part 8 (Pairs and Lists)
- Do exercises/EXERCISES.md: Exercise 5
- Understand lists as fold functions

**Missed Q19-Q20?** → Review:
- TUTORIAL.md: Part 9 (Y Combinator)
- README.md: "Fixed-Point Combinator" section
- This is advanced - it's okay to struggle here!

**Missed Q21-Q23?** → Review:
- TUTORIAL.md: Part 10 (Theoretical Properties)
- README.md: "Theoretical Properties" section
- These are more conceptual - less critical for practice

---

## Next Steps

- **Scored well?** Move on to Chapter 2: Simply Typed Lambda Calculus
- **Need review?** Revisit relevant sections, then retake quiz
- **Want more practice?** Complete all exercises in exercises/EXERCISES.md
- **Feeling stuck?** That's normal! Lambda calculus is challenging. Take a break, then try again

Remember: Understanding lambda calculus deeply is more important than speed. Take your time!
