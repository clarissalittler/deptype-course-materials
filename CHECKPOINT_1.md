# Checkpoint 1: Foundations (After Chapters 1-2)

## Purpose
Verify understanding of lambda calculus and basic type systems before proceeding to more advanced topics.

## Time Estimate
60-90 minutes

---

## Part A: Lambda Calculus (30 minutes)

### Concept Review Questions

1. **Explain the difference between alpha, beta, and eta conversion**. Give an example of each.

2. **What is the Church-Rosser property** and why does it matter?

3. **Explain substitution** and why name capture is a problem:
   ```
   (\x. \y. x) y   [substitute what for x?]
   ```

### Practical Problems

4. **Reduce to normal form**:
   ```
   a) (\x. x x) (\y. y)
   b) (\f. \x. f (f x)) (\z. z) (\a. a)
   c) (\x. \y. \z. x z (y z)) (\a. \b. a) (\c. \d. c)
   ```

5. **Implement Church numeral operations**:
   ```
   a) Write pred (predecessor) in lambda calculus
   b) Test: pred 3 should give 2
   ```

---

## Part B: Simply Typed Lambda Calculus (30 minutes)

### Concept Review Questions

6. **What do Progress and Preservation guarantee**?

7. **Give an example** of a term that:
   - Type checks: `____________`
   - Doesn't type check: `____________`
   - Why doesn't the second one type check?

8. **Explain the difference** between:
   ```
   Nat -> Nat -> Nat
   (Nat -> Nat) -> Nat
   ```

### Practical Problems

9. **Type check these terms** (or explain why they fail):
   ```
   a) \x:Nat. if (iszero x) then zero else (succ x)
   b) \f:Bool->Nat. \x:Bool. succ (f x)
   c) \x:Nat. \y:Bool. if y then x else true
   ```

10. **Implement in STLC**:
    ```
    a) max : Nat -> Nat -> Nat
    b) and : Bool -> Bool -> Bool
    ```

---

## Part C: Integration Questions (20 minutes)

11. **Compare**: How is typing in STLC different from evaluation in untyped LC?

12. **True or False** (explain):
    - [ ] Every typeable term in STLC reduces to a normal form
    - [ ] Every term in untyped LC reduces to a normal form
    - [ ] Every term in STLC is typeable
    - [ ] Type checking catches all runtime errors

13. **Design question**: Why do we need BOTH typing rules AND evaluation rules?

---

## Self-Assessment Rubric

### Score yourself (1-5 for each part):

**Part A (Lambda Calculus)**:
- 5: Can fluently reduce terms, explain concepts, implement Church encodings
- 4: Can reduce most terms, explain core concepts
- 3: Can reduce simple terms, understand basics
- 2: Struggle with reductions, concepts unclear
- 1: Don't understand lambda calculus

**Part B (STLC)**:
- 5: Can type check complex terms, explain metatheory, implement operations
- 4: Can type check most terms, understand type safety
- 3: Can type check simple terms
- 2: Confusion about typing rules
- 1: Don't understand typing

**Part C (Integration)**:
- 5: Clear understanding of relationship between chapters
- 4: Good grasp of connections
- 3: See some connections
- 2: Chapters feel disconnected
- 1: Don't see how they relate

### Interpretation:

**12-15 total**: ✅ Ready for Chapter 3!
**9-11 total**: ⚠️  Review weak areas, then proceed
**Below 9**: ❌ Review chapters 1-2 before continuing

---

## Recommended Next Steps

**Score 12-15**:
→ Move to Chapter 3 (ADTs) or Chapter 4 (Type Inference)

**Score 9-11**:
→ Review specific weak areas
→ Complete more exercises from chapters 1-2
→ Then proceed

**Score < 9**:
→ Re-read chapters 1-2
→ Work through tutorials
→ Complete exercises
→ Retake checkpoint

---

## Answer Key (Self-Check)

1. **Conversions**:
   - Alpha: λx.x = λy.y (renaming)
   - Beta: (λx.x)y → y (evaluation)
   - Eta: λx.f x = f (when x not in f)

2. **Church-Rosser**: Reduction order doesn't matter for final result

3. **Substitution**: Need alpha-conversion first to avoid capture

4. **Reductions**:
   - a) λy.y
   - b) λa.a
   - c) λa.λd.a

6. **Progress**: Well-typed terms don't get stuck
   **Preservation**: Reduction preserves types

7. Examples:
   - Type checks: `\x:Nat. succ x`
   - Doesn't: `\x:Bool. succ x` (succ requires Nat)

11. **Typing** rejects terms before execution; **evaluation** runs terms

12. **T/F**:
   - True (strong normalization)
   - False (e.g., Ω = (λx.x x)(λx.x x))
   - False (e.g., `\x:Bool. succ x` doesn't type)
   - True (in STLC, yes!)

---

**Good luck! This checkpoint ensures you have the foundation for more advanced topics.**
