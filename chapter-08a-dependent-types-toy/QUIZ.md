# Chapter 8: Full Dependent Types - Self-Check Quiz

## Instructions

This quiz tests your understanding of Chapter 8 concepts: universe hierarchy, propositional equality, inductive families, eliminators, and the complete Curry-Howard correspondence.

Try to answer each question without looking at the materials, then check your answers at the end.

**Scoring Guide**:
- 22-25 correct: Excellent! Ready for real proof assistants
- 18-21 correct: Very good! Review any missed topics
- 14-17 correct: Good progress! Spend more time with weak areas
- Below 14: Review the chapter, tutorial, and common mistakes

**Time Estimate**: 45-60 minutes

---

## Section 1: Universe Hierarchy (Questions 1-5)

### Question 1
What is the type of `Type 0`?

A) `Type 0` (Type-in-Type)
B) `Type 1`
C) `Type`
D) Cannot have a type (primitive)

### Question 2
Why is `Type : Type` inconsistent?

A) It leads to infinite loops
B) It enables Girard's paradox (can prove False)
C) It makes type checking too slow
D) It's not inconsistent - it's just a design choice

### Question 3
What is the level of `Nat → Bool`?

A) `Type 0`
B) `Type 1`
C) `Type 2`
D) Cannot be determined

### Question 4
What is the level of `Π(A:Type 0). A → A`?

A) `Type 0`
B) `Type 1`
C) `Type 2`
D) `Type 3`

### Question 5
What is predicativity?

A) The ability to predict program behavior
B) The restriction that `Π(x:A). B` lives in `Type (max i j)` where `A : Type i`, `B : Type j`
C) The ability to prove propositions
D) A form of type inference

---

## Section 2: Propositional Equality (Questions 6-10)

### Question 6
What is the type of `Eq`?

A) `Eq : Type → Type → Type`
B) `Eq : Π(A:Type). A → A → Type`
C) `Eq : Π(A:Type i). A → A → Type i`
D) `Eq : Π(A B:Type). A → B → Type`

### Question 7
What is the type of `refl`?

A) `refl : Π(A:Type). Eq A A A`
B) `refl : Π(A:Type). Π(x:A). Eq A x x`
C) `refl : Π(A:Type). Π(x y:A). Eq A x y`
D) `refl : Π(x:A). Eq A x x`

### Question 8
When can you use `refl` to prove `Eq A x y`?

A) Always - refl works for any equality
B) Only when x and y are the same variable
C) When x and y are definitionally equal (reduce to the same normal form)
D) Never - you need the J eliminator

### Question 9
Can you prove `Eq Nat (n + 0) n` using just `refl`?

A) Yes: `refl n`
B) Yes: `refl (n + 0)`
C) No - requires induction
D) It's unprovable

### Question 10
What does the J eliminator compute rule state?

A) `J A x C p x (refl x) ~> refl x`
B) `J A x C p x (refl x) ~> p`
C) `J A x C p y eq ~> eq`
D) `J A x C p y eq ~> C y eq`

---

## Section 3: The J Eliminator (Questions 11-13)

### Question 11
What is the intuition behind the J eliminator?

A) It proves equality is reflexive
B) To prove a property for all equalities `x = y`, it suffices to prove it for `x = x`
C) It allows pattern matching on equality proofs
D) It computes the normal form of terms

### Question 12
How do you derive symmetry of equality using J?

A) Use J with motive `C z eq = Eq A z x` and base case `refl x`
B) Use J with motive `C z eq = Eq A x z` and base case `refl y`
C) You can't - symmetry must be a primitive constructor
D) Apply J twice

### Question 13
Which properties of equality can be derived from J and refl alone?

A) Only reflexivity
B) Reflexivity and symmetry only
C) Reflexivity, symmetry, and transitivity
D) All equality properties (including congruence)

---

## Section 4: Inductive Families (Questions 14-17)

### Question 14
What's the difference between parameters and indices in inductive types?

A) Parameters can vary across constructors; indices are uniform
B) Parameters are uniform across constructors; indices can vary
C) They are the same thing
D) Parameters are types; indices are values

### Question 15
What is the type of `Nil` in the Vec type?

A) `Nil : Vec n A` for any n
B) `Nil : Π(A:Type). Vec 0 A`
C) `Nil : Π(n:Nat). Vec n A`
D) `Nil : Vec zero`

### Question 16
Why can `head : Vec (succ n) A → A` omit the `Nil` case in pattern matching?

A) Because Nil is an empty constructor
B) Because the type system knows `Nil : Vec 0 A` doesn't match `Vec (succ n) A`
C) Because it's optional to handle all cases
D) It's a bug - the Nil case should be there

### Question 17
How many inhabitants does `Fin 0` have?

A) 0 (empty type)
B) 1
C) Infinity
D) Undefined

---

## Section 5: Eliminators (Questions 18-20)

### Question 18
What is the type of `natElim`?

A) `natElim : Π(P:Nat → Type). P zero → P (succ zero) → Π(n:Nat). P n`
B) `natElim : Π(P:Nat → Type). P zero → (Π(k:Nat). P k → P (succ k)) → Π(n:Nat). P n`
C) `natElim : Nat → Nat → Nat`
D) `natElim : (Nat → Nat) → Nat → Nat`

### Question 19
What does `natElim P z s zero` reduce to?

A) `zero`
B) `z`
C) `s zero`
D) `P zero`

### Question 20
Why do eliminators guarantee termination?

A) They use a timeout mechanism
B) They only allow structural recursion on subterms
C) They are primitive operations
D) They don't guarantee termination

---

## Section 6: Curry-Howard Correspondence (Questions 21-25)

### Question 21
What type corresponds to the logical proposition P ∧ Q?

A) `P → Q`
B) `Π(x:P). Q`
C) `Σ(x:P). Q` or `Pair P Q`
D) `Either P Q`

### Question 22
What type corresponds to ¬P (negation of P)?

A) `Not P`
B) `P → Empty`
C) `Empty → P`
D) `Σ(x:P). Empty`

### Question 23
What type corresponds to ∀x. P(x)?

A) `Σ(x:A). P x`
B) `Π(x:A). P x`
C) `A → P`
D) `P → A`

### Question 24
What type corresponds to ∃x. P(x)?

A) `Π(x:A). P x`
B) `A → P`
C) `Σ(x:A). P x`
D) `Either A P`

### Question 25
What does it mean to "prove" a proposition in type theory?

A) Write a truth table
B) Construct a term of the corresponding type
C) Use a proof assistant
D) Apply logical rules

---

## Answers

### Section 1: Universe Hierarchy

1. **B** - `Type 0 : Type 1`
   - Each universe lives in the next one up

2. **B** - It enables Girard's paradox
   - With Type : Type, we can encode paradoxes and prove False

3. **A** - `Type 0`
   - Both Nat and Bool are in Type 0, so Nat → Bool is also in Type 0

4. **B** - `Type 1`
   - We quantify over Type 0, which lives in Type 1
   - The function body is Type 0
   - max(1, 0) = 1

5. **B** - The max level restriction for Pi types
   - In predicative systems, Π(x:A). B lives in Type (max i j)
   - Cannot quantify over all types to create a type at the same level

### Section 2: Propositional Equality

6. **C** - `Eq : Π(A:Type i). A → A → Type i`
   - Equality is universe-polymorphic
   - Takes a type and two elements, returns a type at the same level

7. **B** - `refl : Π(A:Type). Π(x:A). Eq A x x`
   - Reflexivity: every term equals itself

8. **C** - When definitionally equal
   - refl only works when both sides reduce to the same normal form
   - For other cases, need to prove equality

9. **C** - No, requires induction
   - n + 0 doesn't reduce to n without proof
   - Need to prove by induction on n

10. **B** - `J A x C p x (refl x) ~> p`
    - The computation rule: when the proof is refl, we get the base case

### Section 3: The J Eliminator

11. **B** - Prove for x = x, get all equalities
    - Since all equalities come from refl, proving for refl suffices

12. **A** - Motive `C z eq = Eq A z x`, base case `refl x`
    - To go from `x = y` to `y = x`, use J to "flip" the equality

13. **D** - All equality properties
    - J and refl are sufficient to derive symmetry, transitivity, congruence, etc.

### Section 4: Inductive Families

14. **B** - Parameters uniform; indices vary
    - Parameters (like A in Vec A n) are the same for all constructors
    - Indices (like n in Vec A n) can differ

15. **B** - `Nil : Π(A:Type). Vec 0 A`
    - Nil is the empty vector, always has length 0

16. **B** - Type system knows the mismatch
    - Nil : Vec 0 A, but we need Vec (succ n) A
    - 0 ≠ succ n, so this case is impossible

17. **A** - 0 (empty type)
    - No natural numbers are less than 0
    - Both constructors require succ in the index

### Section 5: Eliminators

18. **B** - Standard natElim type
    - Takes a motive, base case, step function, and a natural number
    - Returns a value of type P n

19. **B** - `z`
    - Base case of the elimination

20. **B** - Structural recursion only
    - Can only recurse on structurally smaller subterms
    - Guarantees termination

### Section 6: Curry-Howard Correspondence

21. **C** - `Σ(x:P). Q` or `Pair P Q`
    - Conjunction: proof requires both a proof of P and a proof of Q

22. **B** - `P → Empty`
    - Negation: show that P leads to a contradiction

23. **B** - `Π(x:A). P x`
    - Universal quantification: a dependent function giving P x for each x

24. **C** - `Σ(x:A). P x`
    - Existential quantification: a witness x and proof of P x

25. **B** - Construct a term of the corresponding type
    - Proofs are programs, propositions are types
    - Type checking is proof checking

---

## Score Interpretation

**22-25 correct (88-100%)**:
Excellent! You have a strong grasp of dependent type theory fundamentals. You're ready to:
- Start using Coq, Agda, Lean, or Idris
- Work through Software Foundations
- Prove real theorems
- Build verified programs

**18-21 correct (72-84%)**:
Very good! You understand the core concepts. Review:
- J eliminator and equality proofs (if you missed those)
- Inductive families and indices
- Universe level computation
Then you're ready for proof assistants!

**14-17 correct (56-68%)**:
Good foundation, but some gaps. Focus on:
- Universe hierarchy and why it matters
- The J eliminator (most challenging part)
- Difference between parameters and indices
- Curry-Howard correspondence
Work through the tutorial examples again.

**Below 14 (< 56%)**:
This material is genuinely hard! Don't be discouraged. Try:
1. Re-read the tutorial slowly
2. Work through each example by hand
3. Review common mistakes
4. Use the REPL to experiment
5. Take breaks - this material needs time to digest
6. Focus on one topic at a time (start with universes)

---

## Topics to Review Based on Mistakes

**If you struggled with Questions 1-5**: Review universe hierarchy
- Why Type : Type is broken
- How to compute universe levels
- The Pi-type level rule
- Predicativity

**If you struggled with Questions 6-10**: Review propositional equality
- Definitional vs. propositional equality
- When to use refl
- What proofs you need vs. what's automatic
- The Eq type constructor

**If you struggled with Questions 11-13**: Review the J eliminator
- This is the hardest topic - it's okay to struggle!
- Work through the symmetry derivation step by step
- Understand why J is sufficient
- Practice with concrete examples

**If you struggled with Questions 14-17**: Review inductive families
- Parameters vs. indices (crucial distinction!)
- How Vec encodes length in the type
- Why some pattern match cases are impossible
- How Fin prevents out-of-bounds errors

**If you struggled with Questions 18-20**: Review eliminators
- Eliminators as induction principles
- Connection to mathematical induction
- Reduction rules
- Why they guarantee termination

**If you struggled with Questions 21-25**: Review Curry-Howard
- Propositions as types
- Proofs as programs
- Mapping logical connectives to type constructors
- Example proofs as functional programs

---

## Next Steps

After completing this quiz:

1. **Review any topics you struggled with** using the tutorial
2. **Check common mistakes** in COMMON_MISTAKES.md
3. **Work through exercises** to solidify understanding
4. **Use the REPL** to experiment with concepts
5. **Try a real proof assistant** - you're ready!

Remember: dependent type theory is the culmination of this entire course. It's supposed to be challenging. Take your time, work through examples, and don't hesitate to review materials multiple times.

**Congratulations on completing the Chapter 8 quiz!** 🎓
