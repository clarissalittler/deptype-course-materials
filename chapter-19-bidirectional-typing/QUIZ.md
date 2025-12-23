# Chapter 19: Bidirectional Type Checking - Self-Assessment Quiz

Test your understanding of bidirectional typing. Try to answer without looking at solutions!

---

## Section 1: Core Concepts (10 questions)

### Q1. What does `Γ ⊢ e ⇒ A` mean?
a) Term e has type A in context Γ
b) Synthesize/infer type A for e in context Γ
c) Check e against type A in context Γ
d) Γ is a subtype of A

### Q2. What does `Γ ⊢ e ⇐ A` mean?
a) Synthesize type A for e
b) Term e has type A
c) Check that e has type A in context Γ
d) Infer Γ from e

### Q3. Which mode is used for variables?
a) Checking (⇐)
b) Inference (⇒)
c) Either
d) Neither

### Q4. Which mode is used for unannotated lambdas?
a) Checking (⇐)
b) Inference (⇒)
c) Either
d) Neither

### Q5. What is the key insight of bidirectional typing?
a) All types can be inferred
b) Introduction forms check, elimination forms infer
c) Annotations are never needed
d) Types flow bottom-up only

### Q6. Why can't we infer the type of `λx. x`?
a) It's syntactically invalid
b) Multiple types are possible (Bool→Bool, Nat→Nat, etc.)
c) The body is too complex
d) We can infer it

### Q7. What does subsumption do?
a) Converts checking to inference
b) Allows inference to satisfy checking when types match
c) Adds subtyping
d) Removes annotations

### Q8. In `f x`, which mode is used for `x`?
a) Inference
b) Checking (against domain of f's type)
c) Neither
d) Both

### Q9. What makes a construct an "introduction form"?
a) It uses a value
b) It constructs a value of a type
c) It can always be inferred
d) It requires an annotation

### Q10. What makes a construct an "elimination form"?
a) It removes values
b) It uses/destructs a value
c) It requires checking
d) It produces errors

---

## Section 2: Mode Classification (10 questions)

### Q11. Annotated lambda `λ(x:A). e`:
a) Check
b) Infer
c) Either
d) Neither

### Q12. Pair construction `(e₁, e₂)`:
a) Check
b) Infer
c) Either
d) Neither

### Q13. First projection `fst e`:
a) Check
b) Infer
c) Either
d) Neither

### Q14. Type annotation `(e : A)`:
a) Check
b) Infer
c) Either
d) Neither

### Q15. Sum injection `inl e`:
a) Check
b) Infer
c) Either
d) Neither

### Q16. Case analysis `case e of ...`:
a) Check
b) Infer
c) Either
d) Neither

### Q17. Type abstraction `Λα. e`:
a) Check
b) Infer
c) Either
d) Neither

### Q18. Type application `e [A]`:
a) Check
b) Infer
c) Either
d) Neither

### Q19. Boolean literal `true`:
a) Check
b) Infer
c) Either
d) Neither

### Q20. If-then-else:
a) Check
b) Infer
c) Infer for condition, depends for branches
d) Check always

---

## Section 3: Rules and Derivations (10 questions)

### Q21. The inference rule for application is:
a) `Γ ⊢ f ⇒ A → B, Γ ⊢ x ⇒ A ⊢ f x ⇒ B`
b) `Γ ⊢ f ⇒ A → B, Γ ⊢ x ⇐ A ⊢ f x ⇒ B`
c) `Γ ⊢ f ⇐ A → B, Γ ⊢ x ⇐ A ⊢ f x ⇐ B`
d) `Γ ⊢ f ⇒ A → B, Γ ⊢ x ⇐ B ⊢ f x ⇒ A`

### Q22. The checking rule for lambda is:
a) `Γ ⊢ e ⇒ B, Γ ⊢ λx.e ⇐ A → B`
b) `Γ,x:A ⊢ e ⇐ B implies Γ ⊢ λx.e ⇐ A → B`
c) `Γ ⊢ λx.e ⇒ A → B`
d) `Γ ⊢ e ⇐ A, Γ ⊢ λx.e ⇐ A → B`

### Q23. What type does `(λ(x:Bool). x) true` infer to?
a) Bool → Bool
b) Bool
c) Cannot infer
d) ∀α. α

### Q24. Can `(λx. x)` alone be type-checked?
a) Yes, it infers ∀α. α → α
b) Yes, it infers Bool → Bool
c) No, but it can be checked against a type
d) No, it's invalid

### Q25. For `((λx.x, λy.y) : (Bool→Bool) × (Nat→Nat))`, how are the lambdas typed?
a) Both inferred independently
b) First checked as Bool→Bool, second as Nat→Nat
c) Both checked as the same type
d) Cannot be typed

### Q26. In the subsumption rule, what must hold?
a) Expected type is subtype of inferred
b) Inferred type equals expected type
c) Expected type is supertype of inferred
d) Any relationship works

### Q27. What's the result of `{x:Bool} ⊢ x ⇒ ?`?
a) Cannot infer
b) Bool
c) ∀α.α
d) Error

### Q28. To check `e ⇐ A → B` when e is not a lambda:
a) Error immediately
b) Use subsumption: infer e, compare types
c) Convert e to a lambda
d) Change modes

### Q29. What type does `(e : A)` synthesize?
a) The type of e
b) A (after checking e ⇐ A)
c) Cannot synthesize
d) Depends on context

### Q30. For `Λα. λx. x ⇐ ∀α. α → α`, what's checked for the body?
a) λx. x ⇐ α → α
b) λx. x ⇒ α → α
c) λx. x ⇐ ∀α. α → α
d) x ⇐ α

---

## Section 4: Implementation (5 questions)

### Q31. The infer function returns:
a) `Either TypeError ()`
b) `Either TypeError Type`
c) `Type`
d) `Bool`

### Q32. The check function returns:
a) `Either TypeError ()`
b) `Either TypeError Type`
c) `Type`
d) `Bool`

### Q33. What should `check ctx (Pair e1 e2) (TyProd a b)` do?
a) `check ctx e1 a >> check ctx e2 b`
b) `infer ctx e1 >> infer ctx e2`
c) Return `TyProd a b`
d) Error

### Q34. What's the fallback case in the check function?
a) Error
b) Subsumption: infer and compare
c) Return unit
d) Call check again

### Q35. How do you handle `check ctx (Lam x e) (TyArr a b)`?
a) `check (extend x a ctx) e b`
b) `infer ctx (Lam x e)`
c) `check ctx e (TyArr a b)`
d) Error if not annotated

---

## Section 5: Advanced Topics (5 questions)

### Q36. With subtyping, subsumption becomes:
a) Inferred = expected
b) Inferred <: expected
c) Expected <: inferred
d) No change

### Q37. For higher-rank polymorphism, we:
a) Synthesize polytypes
b) Synthesize monotypes, check polytypes
c) Never allow forall
d) Require full inference

### Q38. In dependent types, bidirectional typing helps because:
a) Types don't contain terms
b) Type equality is simple
c) Mode annotations guide when to reduce types
d) Annotations are never needed

### Q39. Local type inference means:
a) Types are inferred globally
b) Annotations on binders suffice
c) No annotations ever
d) Complex constraint solving

### Q40. The "annotation trick" is:
a) Remove annotations when possible
b) Add (e : A) to make inference work
c) Annotate every variable
d) Use subsumption

---

## Answer Key

### Section 1: Core Concepts
1. b) Synthesize type
2. c) Check against type
3. b) Inference
4. a) Checking
5. b) Intro check, elim infer
6. b) Multiple types possible
7. b) Inference satisfies checking
8. b) Checking
9. b) Constructs a value
10. b) Uses/destructs a value

### Section 2: Mode Classification
11. b) Infer
12. a) Check
13. b) Infer
14. b) Infer
15. a) Check
16. b) Infer
17. a) Check
18. b) Infer
19. b) Infer
20. c) Infer condition, depends for branches

### Section 3: Rules and Derivations
21. b) f⇒, x⇐
22. b) Γ,x:A ⊢ e ⇐ B
23. b) Bool
24. c) No, but can check
25. b) Each checked separately
26. b) Equals
27. b) Bool
28. b) Subsumption
29. b) A
30. a) λx. x ⇐ α → α

### Section 4: Implementation
31. b) Either TypeError Type
32. a) Either TypeError ()
33. a) check both
34. b) Subsumption
35. a) Extend and check

### Section 5: Advanced
36. b) Inferred <: expected
37. b) Mono synth, poly check
38. c) Mode guides reduction
39. b) Annotations on binders
40. b) Add annotation

---

## Scoring Guide

- **36-40 correct**: Excellent! You've mastered bidirectional typing.
- **28-35 correct**: Good understanding. Review modes you missed.
- **20-27 correct**: Decent start. Re-trace derivation examples.
- **Below 20**: Please review the chapter carefully.

---

## Targeted Review

- **Section 1**: Review README Overview
- **Section 2**: Study the mode table in README
- **Section 3**: Work through derivation examples
- **Section 4**: Study TypeCheck.hs implementation
- **Section 5**: Read the Extensions section
