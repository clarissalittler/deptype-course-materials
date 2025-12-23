# Chapter 20: Denotational Semantics - Lesson Plan

**Estimated Total Time**: 14-18 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Lambda calculus basics (Chapter 1)
- [ ] Recursion and fixed points
- [ ] Basic set theory (partially ordered sets)
- [ ] Haskell's lazy evaluation

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain what denotational semantics is and why it matters
2. Define and work with domains (CPOs)
3. Understand the approximation ordering and bottom element
4. Compute fixed points using the Kleene chain
5. Write denotation functions for simple languages
6. Connect denotational and operational semantics

---

## Lesson 1: The Big Picture (2-3 hours)

### Learning Goals
- Understand what "meaning" means for programs
- See how denotational semantics differs from operational
- Grasp the compositionality principle

### Activities

1. **Read** README.md sections: Overview, The Central Idea

2. **Three kinds of semantics**:
   - **Operational**: How does it run? (reduction rules)
   - **Denotational**: What does it mean? (math objects)
   - **Axiomatic**: What can we prove? (logic)

3. **The key notation**:
   ```
   [[e]] = the denotation of term e
   ```
   The semantic brackets `[[·]]` map syntax to math.

4. **Compositionality**:
   ```
   [[e₁ e₂]] = [[e₁]]([[e₂]])
   ```
   Meaning of whole = combination of meanings of parts.

5. **Think about**: Why might we want a mathematical meaning?
   - Proving equivalences
   - Compiler correctness
   - Language design

### Self-Check Questions
- [ ] What question does denotational semantics answer?
- [ ] What does `[[·]]` mean?
- [ ] Why is compositionality important?

---

## Lesson 2: Domains and Approximation (3-4 hours)

### Learning Goals
- Understand partial orders and approximation
- Learn what bottom (⊥) represents
- Understand flat domains

### Activities

1. **Read** README.md section: Domain Theory

2. **What is a domain (CPO)?**
   - A set with a partial order ⊑ (approximation)
   - A least element ⊥ (bottom, undefined)
   - Suprema exist for all chains

3. **The approximation ordering**:
   ```
   ⊥ ⊑ v for all v     -- bottom approximates everything
   v ⊑ v                 -- reflexivity
   v ⊑ v' ⊑ v'' ⟹ v ⊑ v''  -- transitivity
   ```

4. **Flat domains** (for base types):
   ```
       0   1   2   3   ...
        \  |  /   /
         \ | /   /
          \|/   /
           ⊥
   ```
   All defined values are incomparable; only ⊥ is below.

5. **Study** `src/Domain.hs`:
   - Find the `Dom` type
   - Find the `approx` function
   - Understand `DBottom`

6. **Practice**: Draw the domain for Bool with ⊥.

### Self-Check Questions
- [ ] What does ⊥ represent?
- [ ] In a flat domain, what is comparable?
- [ ] Why is ⊥ needed for recursion?

---

## Lesson 3: Functions and Continuity (2-3 hours)

### Learning Goals
- Understand function domains
- Learn what continuity means
- See why continuity is required

### Activities

1. **Function domains**:
   ```
   [A → B] = {f : A → B | f is continuous}
   ```
   Ordered pointwise: `f ⊑ g iff ∀x. f(x) ⊑ g(x)`

2. **Continuity** (informal):
   A function is continuous if:
   - It preserves approximation: `x ⊑ y ⟹ f(x) ⊑ f(y)` (monotone)
   - It preserves limits of chains: `f(⊔ chain) = ⊔ (f(chain))`

3. **Why continuity?**
   - Ensures fixed points exist
   - Matches computational behavior
   - Excludes "non-computable" functions

4. **Example**: The "strict" identity
   ```
   id_strict(⊥) = ⊥     -- continuous
   id_strict(x) = x

   id_bad(⊥) = 0        -- NOT continuous!
   id_bad(x) = x
   ```

5. **Study** the `DFun` case in `Domain.hs`

### Self-Check Questions
- [ ] What is the least function in [A → B]?
- [ ] Why must semantic functions be continuous?
- [ ] Is `λx. if x=⊥ then 0 else x` continuous?

---

## Lesson 4: Fixed Points (3-4 hours)

### Learning Goals
- Understand Kleene's fixed point theorem
- Compute fixed points by iteration
- See how recursion is modeled

### Activities

1. **Read** README.md section: The Fixed Point Theorem

2. **Kleene's theorem**:
   If f : D → D is continuous, then:
   ```
   fix f = ⊔ₙ fⁿ(⊥) = ⊔ {⊥, f(⊥), f(f(⊥)), ...}
   ```
   The least fixed point is the supremum of the Kleene chain.

3. **Work through factorial**:
   ```
   F = λf. λn. if n=0 then 1 else n * f(n-1)

   F⁰(⊥) = ⊥                            -- undefined everywhere
   F¹(⊥) = λn. if n=0 then 1 else ⊥     -- defined on 0
   F²(⊥) = λn. if n≤1 then ... else ⊥   -- defined on 0,1
   ...
   fix F = factorial                     -- defined everywhere
   ```

4. **Study** `src/Domain.hs`:
   - Find the `fix` function
   - Find `fixN` (approximations)

5. **Experiment** with the REPL:
   ```
   stack exec denotational-repl
   den> fix (\(f : Nat -> Nat). \(x : Nat). x)
   den> :fact 5
   ```

6. **Practice**: Compute the first 3 approximations for:
   ```
   F = λf. λn. if n=0 then 0 else suc(f(n-1))
   ```

### Self-Check Questions
- [ ] What is the Kleene chain?
- [ ] Why does the chain have a supremum?
- [ ] What's the difference between `fix f` and `f(fix f)`?

---

## Lesson 5: The Denotation Function (2-3 hours)

### Learning Goals
- Implement [[·]] for a simple language
- Handle all term forms
- Connect to environments

### Activities

1. **Read** README.md section: Denotation Equations

2. **The key equations**:
   ```
   [[x]]ρ = ρ(x)
   [[λx.e]]ρ = λd. [[e]]ρ[x↦d]
   [[e₁ e₂]]ρ = [[e₁]]ρ ([[e₂]]ρ)
   [[fix e]]ρ = fix([[e]]ρ)
   ```

3. **Study** `src/Denotation.hs`:
   - Find the `denote` function
   - Trace through each case

4. **Hand-compute**:
   ```
   [[(\x. x) true]]{}
   = [[λx.x]]{}([[true]]{})
   = (λd. [[x]]{x↦d})(true)
   = (λd. d)(true)
   = true
   ```

5. **Run tests**:
   ```bash
   stack test
   ```

### Self-Check Questions
- [ ] What role does the environment ρ play?
- [ ] How is application handled?
- [ ] How does fix connect to Kleene iteration?

---

## Lesson 6: Adequacy and Extensions (2-3 hours)

### Learning Goals
- Understand adequacy theorem
- See how to extend to new features
- Connect to operational semantics

### Activities

1. **Read** README.md sections: Key Properties, Comparison

2. **Adequacy theorem**:
   ```
   e →* v ⟹ [[e]] = [[v]]
   ```
   Operational evaluation preserves denotational meaning.

3. **Full abstraction** (desired but hard):
   ```
   e ≃ e' (observationally) ⟹ [[e]] = [[e']]
   ```

4. **Extensions**: How would you add:
   - Products: `[[⟨e₁,e₂⟩]] = ([[e₁]], [[e₂]])`
   - Sums: Use disjoint union
   - State: Use state transformers

5. **Complete exercises** from `exercises/EXERCISES.md`

6. **Self-assessment**: Can you...
   - [ ] Define a domain for a new type?
   - [ ] Write denotation equations?
   - [ ] Compute fixed point approximations?
   - [ ] Explain adequacy?

---

## Progress Tracker

### Lesson 1: The Big Picture
- [ ] Understood three kinds of semantics
- [ ] Grasped compositionality
- [ ] Saw denotational intuition

### Lesson 2: Domains
- [ ] Understood approximation ordering
- [ ] Know what ⊥ means
- [ ] Can draw flat domains

### Lesson 3: Continuity
- [ ] Understand function domains
- [ ] Know what continuous means
- [ ] See why it's needed

### Lesson 4: Fixed Points
- [ ] Understand Kleene's theorem
- [ ] Can iterate approximations
- [ ] See how recursion works

### Lesson 5: Denotation Function
- [ ] Traced through cases
- [ ] Hand-computed examples
- [ ] Tests pass

### Lesson 6: Adequacy
- [ ] Understand the theorem
- [ ] Know what full abstraction means
- [ ] Completed exercises

---

## Key Takeaways

After completing this chapter, remember:

1. **[[e]] maps syntax to math**: Programs denote domain elements
2. **⊥ = undefined**: The least element, represents non-termination
3. **fix f = ⊔ fⁿ(⊥)**: Recursion as least fixed point of Kleene chain
4. **Compositionality**: Meaning of parts determines meaning of whole
5. **Adequacy**: Evaluation preserves denotation

## Next Steps

After mastering this chapter:
- **Game semantics**: Full abstraction for PCF
- **Logical relations**: Proving properties of programs
- **Effect semantics**: Monads, state, exceptions
- **Realizability**: Connection to computability theory
