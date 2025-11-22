# Chapter 2: Simply Typed Lambda Calculus - Self-Check Quiz

## Instructions

Test your understanding of STLC. Try to answer without looking at materials, then check answers at the end.

**Scoring Guide**:
- 18-20 correct: Excellent! Ready for Chapter 3
- 14-17 correct: Good! Review missed topics
- 10-13 correct: Decent! More practice needed
- Below 10: Review chapter and tutorial

---

## Section 1: Type Syntax (Questions 1-3)

### Question 1
How is the type `Nat → Bool → Nat` parsed?

A) `(Nat → Bool) → Nat`
B) `Nat → (Bool → Nat)`
C) Ambiguous - needs parentheses
D) `Nat → Bool` and `Nat` (not a function type)

### Question 2
What is the type of `λx:Bool. λy:Nat. x`?

A) `Bool → Nat → Bool`
B) `Nat → Bool → Nat`
C) `Bool → (Nat → Bool)`
D) `(Bool → Nat) → Bool`

### Question 3
Which term is syntactically valid in STLC?

A) `λx. x` (no type annotation)
B) `λx:Bool. x`
C) `λx:Bool:Nat. x`
D) `λ:Bool. x`

---

## Section 2: Typing Contexts (Questions 4-5)

### Question 4
Under context `Γ = x:Bool, y:Nat`, what is the type of `y`?

A) `Bool`
B) `Nat`
C) `Bool → Nat`
D) Cannot determine

### Question 5
What does the judgment `x:Nat ⊢ λy:Bool. x : Bool → Nat` mean?

A) Under empty context, `λy:Bool. x` has type `Bool → Nat`
B) Under context with `x:Nat`, `λy:Bool. x` has type `Bool → Nat`
C) The variable `x` has type `Nat` and type `Bool → Nat`
D) Type error - `x` has wrong type

---

## Section 3: Typing Rules - Abstraction and Application (Questions 6-9)

### Question 6
To type check `λx:τ₁. t` under context `Γ`, what context do we use for checking `t`?

A) `Γ`
B) `Γ, x:τ₁`
C) `x:τ₁`
D) `∅` (empty context)

### Question 7
Does `(λx:Bool. x) 0` type check?

A) Yes, type is `Bool`
B) Yes, type is `Nat`
C) No, type error - argument type mismatch
D) No, syntax error

### Question 8
What is the type of `(λx:Nat. succ x) 0`?

A) `Nat`
B) `Nat → Nat`
C) `Bool`
D) Doesn't type check

### Question 9
What is the type of `λf:Nat→Bool. λx:Nat. f x`?

A) `Nat → Bool`
B) `(Nat → Bool) → Nat → Bool`
C) `Nat → (Bool → Nat) → Bool`
D) Doesn't type check

---

## Section 4: Booleans and Conditionals (Questions 10-12)

### Question 10
Does `if true then 0 else false` type check?

A) Yes, type is `Nat`
B) Yes, type is `Bool`
C) No, branches have different types
D) No, condition must be `Nat`

### Question 11
What is the type of `if iszero 0 then succ 0 else 0`?

A) `Bool`
B) `Nat`
C) `Bool → Nat`
D) Doesn't type check

### Question 12
What must be true for `if t₁ then t₂ else t₃` to type check?

A) `t₁ : Bool`, `t₂` and `t₃` have any types
B) `t₁ : Nat`, `t₂ : Bool`, `t₃ : Bool`
C) `t₁ : Bool`, `t₂` and `t₃` have the same type
D) All three have type `Bool`

---

## Section 5: Metatheory (Questions 13-16)

### Question 13
What does the Progress theorem guarantee?

A) All programs terminate
B) Well-typed programs never get stuck
C) Types are preserved during evaluation
D) Programs run faster

### Question 14
What does the Preservation theorem guarantee?

A) All programs terminate
B) Programs don't change during evaluation
C) Types are preserved during evaluation
D) Programs never get stuck

### Question 15
What does "strong normalization" mean for STLC?

A) All programs terminate
B) All programs have a normal form
C) All well-typed programs terminate
D) Evaluation is efficient

### Question 16
Why can't we write the Y combinator in STLC?

A) It's not useful
B) `λx. x x` doesn't type check
C) We need more complex types
D) Syntax doesn't allow it

---

## Section 6: Evaluation (Questions 17-18)

### Question 17
What does `(λx:Bool. if x then 0 else 1) true` evaluate to?

A) `true`
B) `false`
C) `0`
D) `1`

### Question 18
Which of the following is a value in STLC?

A) `(λx:Nat. x) 0`
B) `λx:Nat. succ x`
C) `if true then 0 else 1`
D) `iszero 0`

---

## Section 7: Expressiveness (Questions 19-20)

### Question 19
Which of these terms from Chapter 1 CANNOT be typed in STLC?

A) `λx. x` (identity)
B) `λx. λy. x` (constant function)
C) `λx. x x` (self-application)
D) `λf. λx. f x` (application)

### Question 20
What is the main limitation of STLC compared to untyped lambda calculus?

A) Can't write any functions
B) Can't write general recursive functions
C) Can't use conditionals
D) Can't use natural numbers

---

## Answers

<details>
<summary>Click to reveal answers</summary>

### Section 1: Type Syntax

**Q1: B** - `Nat → (Bool → Nat)`
- Function types associate to the right
- This represents curried functions

**Q2: C** - `Bool → (Nat → Bool)`
- First λ takes Bool
- Returns a function from Nat to Bool (which returns the Bool argument)

**Q3: B** - `λx:Bool. x`
- STLC requires type annotations on lambda parameters
- A is untyped LC, C has double annotation, D has no parameter

### Section 2: Typing Contexts

**Q4: B** - `Nat`
- Context maps `y` to `Nat`
- T-Var rule looks up `y` in context

**Q5: B** - Under context with `x:Nat`, `λy:Bool. x` has type `Bool → Nat`
- The left side of `⊢` is the typing context
- The right side is the term and its type

### Section 3: Typing Rules

**Q6: B** - `Γ, x:τ₁`
- T-Abs extends context with parameter binding
- This is how we track variable types

**Q7: C** - No, type error - argument type mismatch
- Function expects `Bool`
- Argument is `0 : Nat`
- Type error!

**Q8: A** - `Nat`
- Function type: `Nat → Nat`
- Argument type: `Nat`
- Result type: `Nat`

**Q9: B** - `(Nat → Bool) → Nat → Bool`
- Takes function from Nat to Bool
- Returns function from Nat to Bool
- This is a higher-order function

### Section 4: Booleans and Conditionals

**Q10: C** - No, branches have different types
- Then branch: `Nat`
- Else branch: `Bool`
- T-If requires same type!

**Q11: B** - `Nat`
- Condition: `iszero 0 : Bool` ✓
- Then: `succ 0 : Nat`
- Else: `0 : Nat`
- Both branches `Nat`, so result is `Nat`

**Q12: C** - `t₁ : Bool`, `t₂` and `t₃` have the same type
- Condition must be Bool
- Both branches must have same type (any type)
- Result has that type

### Section 5: Metatheory

**Q13: B** - Well-typed programs never get stuck
- Progress: value or can step
- Prevents undefined states

**Q14: C** - Types are preserved during evaluation
- If `t : τ` and `t → t'`, then `t' : τ`
- Type doesn't change!

**Q15: C** - All well-typed programs terminate
- Strong normalization: no infinite loops
- Trade-off for safety

**Q16: B** - `λx. x x` doesn't type check
- Would need `x : τ` and `x : τ → σ` simultaneously
- Impossible in STLC

### Section 6: Evaluation

**Q17: C** - `0`
- Substitute `true` for `x`
- `if true then 0 else 1`
- Reduces to `0`

**Q18: B** - `λx:Nat. succ x`
- Lambda abstractions are values
- A, C, D all have redexes

### Section 7: Expressiveness

**Q19: C** - `λx. x x`
- Self-application doesn't type check
- All others can be typed (with appropriate annotations)

**Q20: B** - Can't write general recursive functions
- Y combinator doesn't type check
- Need explicit `fix` construct
- Trade-off for termination guarantee

</details>

---

## Score Interpretation

**18-20 correct (90-100%)**: Excellent! You understand STLC deeply. Ready for Chapter 3.

**14-17 correct (70-89%)**: Good grasp of concepts. Review:
- Type derivations (if missed Q6-Q9)
- Metatheory (if missed Q13-Q16)

**10-13 correct (50-69%)**: Basic understanding, but gaps. Focus on:
- How typing rules work
- Building complete derivations
- Progress and Preservation theorems

**Below 10 (<50%)**: Need more review. Recommendations:
- Re-read TUTORIAL.md
- Work through examples step-by-step
- Use REPL to check your work
- Complete exercises
- Retake quiz after review

---

## What to Review Based on Mistakes

**Missed Q1-Q3?** → Review type syntax, function types, associativity

**Missed Q4-Q5?** → Review typing contexts and judgments

**Missed Q6-Q9?** → Review T-Abs and T-App rules, practice derivations

**Missed Q10-Q12?** → Review conditionals, T-If rule

**Missed Q13-Q16?** → Review metatheory, Progress, Preservation

**Missed Q17-Q18?** → Review evaluation rules, what are values

**Missed Q19-Q20?** → Review expressiveness trade-offs, comparison with Chapter 1

---

## Next Steps

- **Scored well?** Move to Chapter 3: STLC with ADTs
- **Need review?** Focus on weak areas, retake quiz
- **Want practice?** Complete exercises/EXERCISES.md
- **Confused?** Use REPL, work through TUTORIAL.md examples

Remember: Understanding type systems is crucial for modern programming!
