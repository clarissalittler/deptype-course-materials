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

*Why other answers are wrong:*
- A) {x, y, z}: x is NOT free — it's bound by the λx
- C) {x}: Wrong on two counts — x is bound AND y, z are missing
- D) {z}: Forgot about y, which is also free

> **Key insight**: Look for variables NOT under a λ that binds them.

**Q2: A, C, D**
- A: Valid ✓
- B: Invalid - λ must have a parameter name
- C: Valid ✓ (just applications of variables)
- D: Valid ✓ (parses as `(λx. x x) (λy. y)`)
- E: Invalid - should be `λx. λy. x` (one parameter per λ)

*Why B and E are invalid:*
- B) `λ. x`: Lambda needs a parameter. "What variable are you binding?"
- E) `λx y. x`: Shorthand some languages allow, but pure λ-calculus requires nested lambdas.

**Q3: B** - `(f g) h`
- Application associates to the left

*Why other answers are wrong:*
- A) `f (g h)`: Right-associative — opposite of the convention
- C) "Cannot be parsed": Left-associativity makes it unambiguous
- D) Extra parens, same meaning — but not the "canonical" parse

> **Mnemonic**: "Left to right, like reading" — f applied to g, then that result applied to h.

### Section 2: Substitution

**Q4: A** - `λy. a y`
- Substitute a for x in the body
- y is bound by λy, so only x changes

*Why other answers are wrong:*
- B) `λy. x y`: Didn't do the substitution at all
- C) `λa. a y`: Changed the wrong variable (the parameter, not the body)
- D) `λy. a a`: Substituted for both x AND y — y is a different variable!

**Q5: B** - `λz. x` (after α-conversion)
- Direct substitution gives `λx. x` — WRONG (variable capture!)
- Must rename first: `λx. y` → `λz. y`, then substitute

*Why other answers are wrong:*
- A) `λx. x`: Variable capture! The free x got "captured" by λx
- C) `λx. y`: Didn't substitute at all
- D) `λy. x`: Changed the parameter incorrectly

> **Critical concept**: Always rename bound variables if they conflict with what you're substituting.

**Q6: B** - The term remains unchanged
- The inner λx shadows the outer x — no substitution happens

*Why other answers are wrong:*
- A) Would cause capture — the inner binding protects its x
- C) Renaming isn't needed when the variable is shadowed
- D) Not an error — it's valid, just a no-op

### Section 3: Beta-Reduction

**Q7: B** - `y y`
- `[x ↦ y](x x)` = `y y` — replace both x's with y

*Why other answers are wrong:*
- A) `x x`: Didn't substitute at all
- C) `y x`: Only substituted one x
- D) `λx. y y`: Added a λ that wasn't there

**Q8: A** - `a`
- Step 1: `(λx. λy. x) a` → `λy. a` (substitute a for x)
- Step 2: `(λy. a) b` → `a` (substitute b for y, but y isn't in body!)

*Why other answers are wrong:*
- B) `b`: Returned second argument — that would be `(λx. λy. y) a b`
- C) `a b`: Stopped reduction too early
- D) `λy. a b`: Mixed up the structure

> **Key pattern**: This is the K combinator — always returns first argument, ignores second.

**Q9: C** - `λx. x y`
- A: Has redex `(λx. x) y` — can reduce!
- B: Has redex `(λy. y) x` inside the lambda body
- C: No redex — `x y` is just application, no λ being applied ✓
- D: Contains `(λy. y)` which could reduce (depending on strategy)

> **Definition check**: A redex is `(λvar. body) arg` — a lambda immediately applied to an argument.

### Section 4: Evaluation Strategies

**Q10: B** - Normal-order only
- The term `(λz. z z) (λz. z z)` is Ω — it loops forever!
- **Call-by-value**: Must evaluate argument first → loops on Ω → never terminates
- **Normal-order**: Applies outer function first → `(λx. λy. y) Ω v` → `(λy. y) v` → `v`

*Why other answers are wrong:*
- A) Call-by-value only: CBV loops on the Ω argument
- C) Both: CBV definitely fails here
- D) Neither: Normal-order succeeds!

> **Insight**: Normal-order can "skip" evaluating arguments that aren't used.

**Q11: C** - Normal-order
- **Normal-order is complete**: If a normal form exists, normal-order finds it
- **Call-by-value is incomplete**: May loop even when a normal form exists (like Q10!)

*Why other answers are wrong:*
- A) Call-by-value: Not complete — can fail on terms like Q10
- B) Call-by-name: Similar to normal-order but doesn't reduce under λ
- D) Not equally complete — normal-order has theoretical guarantees others lack

### Section 5: Church Booleans

**Q12: B** - `a`
- Step by step: `true a b` = `(λt. λf. t) a b`
- Apply a: `(λf. a) b`
- Apply b: `a`
- **Church true selects its FIRST argument**

*Why other answers are wrong:*
- A) `true`: That's the function, not the result of applying it
- C) `b`: That's what `false a b` returns (selects second)
- D) `a b`: Didn't finish reduction

> **Pattern**: `true` = "pick first", `false` = "pick second"

**Q13: B** - `λp. λq. p q false`
- **If p is true**: `true q false` → `q` (first argument)
- **If p is false**: `false q false` → `false` (second argument)

*Why other answers are wrong:*
- A) `λp. λq. p q p`: This is also AND, but returns p not false when p is false (works, but less standard)
- C) `λp. λq. p false q`: This is OR! If p is true → false, if p is false → q
- D) `λp. λq. p true q`: If p is true → true, if p is false → q — that's also wrong

> **Verification**: AND should return false if EITHER argument is false.

### Section 6: Church Numerals

**Q14: C** - 3
- Count the f's: `f (f (f x))` — three applications of f
- **Church numeral n = "apply f n times to x"**

*Why other answers are wrong:*
- A) 1: That would be `λf. λx. f x` (one f)
- B) 2: That would be `λf. λx. f (f x)` (two f's)
- D) 4: That would have four f's

> **Quick check**: Count nested f applications, that's your number.

**Q15: A** - `λf. λx. x`
- Zero applications of f — just return x unchanged

*Why other answers are wrong:*
- B) `λf. λx. f x`: That's 1 (one application of f)
- C) `λx. x`: Missing the f parameter — invalid Church numeral
- D) `false`: While `false` and `0` look similar (`λt. λf. f` vs `λf. λx. x`), they have different "intended" arguments

**Q16: C** - `λf. λx. f (f (f x))`
- 1 = `λf. λx. f x`, 2 = `λf. λx. f (f x)`
- Plus adds the f applications: 1 + 2 = 3 applications

*Why other answers are wrong:*
- A) `λf. λx. f x`: That's 1
- B) `λf. λx. f (f x)`: That's 2
- D) `3` (JavaScript number): λ-calculus has no primitive numbers!

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
- This is the **fixed-point property**
- `Y f` reduces to `f (Y f)` which is `f (f (Y f))` which is `f (f (f ...)))`
- Gives f a way to "call itself"

*Why other answers are wrong:*
- A) `Y f = f`: Y doesn't just return f — it creates infinite expansion
- C) `Y f = Y (Y f)`: Y isn't applied to itself
- D) `Y f = λx. f x`: This is just η-expansion, not the fixed-point property

> **Key insight**: `Y f = f (Y f)` means f "gets itself" as the first argument, enabling recursion.

**Q20: B** - It immediately expands infinitely under call-by-value
- Y = `(λx. f (x x)) (λx. f (x x))`
- CBV must evaluate argument `(λx. f (x x))` before substituting
- But when you apply it to itself: `(λx. f (x x)) (λx. f (x x))` → `f ((λx. f (x x)) (λx. f (x x)))`
- The argument is the same term! → loops forever

*Why other answers are wrong:*
- A) Syntax error: The syntax is valid
- C) Requires named recursion: Y is specifically for ANONYMOUS recursion
- D) CBV supports recursion — but needs Z combinator (has extra λ delay)

> **Solution**: Z combinator = `λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))` — the extra λy delays evaluation.

### Section 9: Theory

**Q21: B** - If a term has a normal form, it's unique
- **Church-Rosser theorem** = confluence
- Multiple reduction paths always converge to the same result
- Normal forms are unique (up to α-equivalence)

*Why other answers are wrong:*
- A) All terms have normal form: False! Ω has no normal form
- C) Evaluation always terminates: False! Ω never terminates
- D) Same number of steps: Different paths can have different lengths

> **Important**: Confluence says the DESTINATION is unique, not the PATH.

**Q22: B** - `(λx. x x) (λx. x x)`
- This is **Ω (omega)** — the canonical non-terminating term
- Reduces to itself: `(λx. x x) (λx. x x)` → `(λx. x x) (λx. x x)` → ...

*Why other answers are wrong:*
- A) `λx. x x`: This is ω (lowercase) — it HAS a normal form (itself — it's a value!)
- C) `λx. (λy. y) x`: This reduces to `λx. x` — terminates
- D) `(λx. λy. x) a b`: This reduces to `a` — terminates

> **Key distinction**: ω = `λx. x x` is a value; Ω = `ω ω` is what loops.

**Q23: A** - It can compute anything a Turing machine can
- **Church-Turing thesis**: λ-calculus = Turing machines in computational power
- Any computable function can be expressed in λ-calculus

*Why other answers are wrong:*
- B) Always terminates: False! We just saw Ω doesn't terminate
- C) Has built-in types: False! This is UNTYPED λ-calculus
- D) Requires Church encodings: Church encodings are ONE way to compute, not the only way

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
