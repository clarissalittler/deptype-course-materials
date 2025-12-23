# Chapter 20: Denotational Semantics - Self-Assessment Quiz

Test your understanding of denotational semantics. Try to answer without looking!

---

## Section 1: Fundamentals (10 questions)

### Q1. What does `[[e]]` represent?
a) The syntax of e
b) The type of e
c) The denotation (mathematical meaning) of e
d) The evaluation of e

### Q2. Which question does denotational semantics answer?
a) How does the program run?
b) What can we prove about the program?
c) What does the program mean mathematically?
d) How fast is the program?

### Q3. What is compositionality?
a) Programs are made of parts
b) The meaning of a whole is determined by meanings of parts
c) All functions can be composed
d) Types compose with types

### Q4. What is ⊥ (bottom)?
a) The zero element
b) The undefined/non-terminating value
c) The empty set
d) The base type

### Q5. In a flat domain, what is comparable to everything?
a) All values
b) Only ⊥
c) Only the maximum element
d) Nothing

### Q6. What does `d₁ ⊑ d₂` mean?
a) d₁ equals d₂
b) d₁ approximates d₂ (has less information)
c) d₁ is greater than d₂
d) d₁ evaluates to d₂

### Q7. What is a domain (CPO)?
a) A type
b) A set with order, bottom, and suprema for chains
c) A set of functions
d) A programming language

### Q8. Why can't we use regular mathematics for recursion?
a) Math doesn't have functions
b) We need to handle non-termination (⊥)
c) Math is too slow
d) Recursion isn't mathematical

### Q9. What makes a function continuous?
a) It has no discontinuities
b) It's monotone and preserves suprema of chains
c) It's defined everywhere
d) It maps ⊥ to ⊥

### Q10. Why must semantic functions be continuous?
a) For efficiency
b) To ensure fixed points exist
c) To match operational semantics
d) Both b and c

---

## Section 2: Domains (10 questions)

### Q11. Draw the flat domain for Bool. What's at the bottom?
a) true
b) false
c) ⊥
d) Both true and false

### Q12. In the flat domain for Nat, is `1 ⊑ 2`?
a) Yes
b) No (they're incomparable)
c) Only if 1 < 2
d) Only if 2 < 1

### Q13. What is the least element in [A → B]?
a) The identity function
b) λx. ⊥ (undefined everywhere)
c) λx. x
d) There is no least element

### Q14. For functions, what does `f ⊑ g` mean?
a) f is faster than g
b) f(x) ⊑ g(x) for all x
c) f has fewer arguments
d) f and g are equal

### Q15. Is `λx. if x=⊥ then 0 else x` continuous?
a) Yes
b) No (not monotone: ⊥ ⊑ 1 but 0 ⋢ 1)
c) Depends on the domain
d) It's not well-defined

### Q16. What is a chain in a domain?
a) A sequence of functions
b) An increasing sequence: d₀ ⊑ d₁ ⊑ d₂ ⊑ ...
c) A decreasing sequence
d) Any sequence

### Q17. What is ⊔{d₀, d₁, d₂, ...}?
a) The minimum of the chain
b) The supremum (least upper bound) of the chain
c) The first element
d) The last element

### Q18. A function preserves suprema means:
a) f(⊔ chain) = ⊔ {f(d) | d in chain}
b) f(⊔) = ⊔
c) f preserves order
d) f is monotone

### Q19. What is [[loop]] where loop = loop?
a) An infinite loop
b) Error
c) ⊥
d) Undefined in math

### Q20. Is ⊥ comparable to itself?
a) No, ⊥ is special
b) Yes, ⊥ ⊑ ⊥ (reflexivity)
c) Only in flat domains
d) Depends on the type

---

## Section 3: Fixed Points (10 questions)

### Q21. Kleene's theorem states that fix f equals:
a) f(⊥)
b) f(f(⊥))
c) ⊔ₙ fⁿ(⊥) (supremum of the chain)
d) The largest fixed point

### Q22. The Kleene chain for f is:
a) ⊥, f, f², f³, ...
b) ⊥, f(⊥), f(f(⊥)), f(f(f(⊥))), ...
c) 0, 1, 2, 3, ...
d) f, f, f, f, ...

### Q23. Why is fix f the LEAST fixed point?
a) It's computed from ⊥
b) ⊥ is below everything, so the chain starts lowest
c) Any other fixed point g has fⁿ(⊥) ⊑ g for all n
d) All of the above

### Q24. For factorial F, what is F⁰(⊥)?
a) factorial
b) ⊥ (undefined everywhere)
c) λn. n
d) λn. 1

### Q25. For factorial F, what is F¹(⊥)(0)?
a) ⊥
b) 1
c) 0
d) Error

### Q26. For factorial F, what is F¹(⊥)(1)?
a) 1
b) ⊥ (because F¹(⊥) uses F⁰(⊥))
c) 0
d) Error

### Q27. Which fⁿ(⊥) first defines factorial on input 3?
a) f³
b) f⁴ (need 4 iterations: 0,1,2,3)
c) f²
d) f¹

### Q28. If f(d) = d, what is fix f?
a) d
b) ⊥
c) f(⊥) (the least such d)
d) Cannot determine

### Q29. What is fix (λf. λn. n)?
a) ⊥
b) λn. n
c) The identity function
d) Both b and c

### Q30. Is fix always defined?
a) Yes, for continuous f on CPOs
b) No, it may not exist
c) Only for monotone f
d) Only for total functions

---

## Section 4: Denotation Function (5 questions)

### Q31. [[x]]ρ =
a) x
b) ρ(x) (look up in environment)
c) ⊥
d) Error

### Q32. [[λx. e]]ρ =
a) e
b) λd. [[e]]ρ
c) λd. [[e]]ρ[x↦d]
d) [[e]]

### Q33. [[e₁ e₂]]ρ =
a) [[e₁]]([[e₂]])
b) [[e₁]]ρ ([[e₂]]ρ)
c) e₁ e₂
d) ρ(e₁ e₂)

### Q34. [[fix e]]ρ =
a) [[e]]ρ
b) fix([[e]]ρ)
c) ⊔ [[e]]ρ
d) [[e]]

### Q35. [[(λx. x) true]]ρ =
a) λx. x
b) true
c) ⊥
d) x

---

## Section 5: Properties (5 questions)

### Q36. Adequacy theorem says:
a) [[e]] is always defined
b) e →* v implies [[e]] = [[v]]
c) [[e]] = [[e']] implies e = e'
d) All programs terminate

### Q37. Full abstraction says:
a) [[e]] ≠ [[e']] implies e ≇ e' (different)
b) e ≃ e' implies [[e]] = [[e']]
c) Both a and b
d) Neither

### Q38. Standard denotational semantics for PCF is:
a) Fully abstract
b) Not fully abstract (has extra elements)
c) Undecidable
d) Incorrect

### Q39. Compositionality helps with:
a) Faster execution
b) Modular reasoning about programs
c) Type checking
d) Garbage collection

### Q40. The main advantage of denotational semantics is:
a) Fast execution
b) Mathematical foundation for reasoning
c) Simple implementation
d) No need for types

---

## Answer Key

### Section 1: Fundamentals
1. c) Mathematical meaning
2. c) What does it mean?
3. b) Meaning of whole from parts
4. b) Undefined/non-terminating
5. b) Only ⊥
6. b) Approximates
7. b) Set with order, bottom, suprema
8. b) Handle non-termination
9. b) Monotone + preserves suprema
10. d) Both b and c

### Section 2: Domains
11. c) ⊥
12. b) No, incomparable
13. b) λx. ⊥
14. b) f(x) ⊑ g(x) for all x
15. b) No
16. b) Increasing sequence
17. b) Supremum
18. a) f(⊔ chain) = ⊔ f(chain)
19. c) ⊥
20. b) Yes, reflexivity

### Section 3: Fixed Points
21. c) Supremum of chain
22. b) ⊥, f(⊥), f(f(⊥)), ...
23. d) All of the above
24. b) ⊥ everywhere
25. b) 1
26. b) ⊥
27. b) f⁴
28. c) f(⊥)
29. d) Both b and c
30. a) Yes, for continuous f

### Section 4: Denotation Function
31. b) ρ(x)
32. c) λd. [[e]]ρ[x↦d]
33. b) [[e₁]]ρ ([[e₂]]ρ)
34. b) fix([[e]]ρ)
35. b) true

### Section 5: Properties
36. b) e →* v implies [[e]] = [[v]]
37. c) Both
38. b) Not fully abstract
39. b) Modular reasoning
40. b) Mathematical foundation

---

## Scoring Guide

- **36-40 correct**: Excellent! You've mastered denotational semantics.
- **28-35 correct**: Good understanding. Review domains and fixed points.
- **20-27 correct**: Decent start. Re-work the tutorial examples.
- **Below 20**: Please review the chapter materials carefully.

---

## Targeted Review

- **Section 1**: Review README Overview
- **Section 2**: Study Domain.hs and draw domain diagrams
- **Section 3**: Work through fixed point iterations by hand
- **Section 4**: Study Denotation.hs
- **Section 5**: Review Key Properties section
