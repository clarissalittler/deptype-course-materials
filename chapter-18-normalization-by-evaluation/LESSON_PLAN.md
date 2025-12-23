# Chapter 18: Normalization by Evaluation - Lesson Plan

**Estimated Total Time**: 14-18 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Lambda calculus and beta reduction
- [ ] Basic Haskell: algebraic data types, pattern matching, recursion
- [ ] Higher-order functions and closures
- [ ] De Bruijn indices (helpful, but we'll review)

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain the eval-quote paradigm for normalization
2. Distinguish between semantic values and syntactic terms
3. Implement NbE for a simply-typed lambda calculus
4. Understand closures and their role in NbE
5. Work with de Bruijn indices and levels
6. Apply NbE to type checking (definitional equality)

---

## Lesson 1: The Big Picture (2-3 hours)

### Learning Goals
- Understand why normalization is needed
- Learn the eval → Val → quote pattern
- See the difference between NbE and reduction

### Activities

1. **Read** README.md sections: Overview, The Core Idea, Why Not Just Reduce?

2. **Think about** the problem:
   - In dependent types, types contain terms
   - To check `f : (x : A) → B(x)` and apply `f` to `e : A`, we need `B(e)`
   - What if `B` is complex? We need to *normalize* it.

3. **Draw the diagram**:
   ```
   Term ──eval──► Val ──quote──► Nf
   ```

4. **Key insight**: Haskell does beta reduction for us!
   - Haskell function: `\x -> x + x`
   - Apply to 3: Haskell computes 6
   - We didn't write reduction rules!

5. **Experiment** with the REPL:
   ```
   stack exec nbe-repl
   nbe> (\x. x) true
   nbe> (\x. \y. x) true false
   ```

### Self-Check Questions
- [ ] What's the difference between a term and a value?
- [ ] Why can't we just compare terms syntactically for equality?
- [ ] How does NbE differ from reduction-based normalization?

---

## Lesson 2: The Semantic Domain (3-4 hours)

### Learning Goals
- Understand the Val type and its constructors
- Learn what closures are and how they work
- Understand neutral values

### Activities

1. **Read** README.md sections: Semantic Domain, Closures, Neutral Values

2. **Study** `src/Semantic.hs`:
   - Find the `Val` data type
   - Find the `Closure` type
   - Find the `Neutral` type

3. **Understand closures**:
   ```haskell
   -- A closure is a term + environment
   data Closure = Closure Env Term

   -- To apply it, extend env and evaluate
   applyClosure (Closure env body) arg = eval (arg : env) body
   ```

4. **Understand neutrals**:
   A neutral value is "stuck" because it depends on a free variable:
   ```
   x         -- neutral variable
   x 5       -- neutral application
   f (x + 1) -- neutral (if f is neutral)
   ```

5. **Draw examples**: For `λx. λy. x`:
   - After `eval []`: `VLam "x" (Closure [] (λy. x))`
   - After applying to `5`: `VLam "y" (Closure [5] x)`
   - After applying to `10`: `5`

6. **Practice**: What's the Val for:
   - `λf. f f`?
   - After applying to `λx. x`?

### Self-Check Questions
- [ ] What does a closure contain?
- [ ] When is a value neutral?
- [ ] Can a neutral contain a closure?

---

## Lesson 3: Evaluation (2-3 hours)

### Learning Goals
- Understand the eval function
- See how Haskell's evaluation handles beta
- Trace evaluation by hand

### Activities

1. **Read** README.md section: Evaluation

2. **Study** `src/NbE.hs`:
   - Find the `eval` function
   - Find the `vApp` function (value application)

3. **Key rules**:
   ```haskell
   eval env (TVar i)   = env !! i
   eval env (TLam x t) = VLam x (Closure env t)
   eval env (TApp t u) = vApp (eval env t) (eval env u)
   ```

4. **The magic is in vApp**:
   ```haskell
   vApp (VLam _ closure) arg = applyClosure closure arg
   vApp (VNe neutral) arg    = VNe (NApp neutral arg)
   ```

   - If we have a lambda, apply the closure (beta reduction!)
   - If we're stuck on a neutral, build bigger neutral

5. **Trace** `eval [] ((\f. \x. f x) (\y. y))`
   Step by step, showing all intermediate values.

6. **Experiment**:
   ```
   nbe> :eval (\f. \x. f x) (\y. y)
   nbe> :eval (\x. x x) (\x. x x)  -- What happens?
   ```

### Self-Check Questions
- [ ] When does eval create a closure vs. reduce?
- [ ] What's the environment used for?
- [ ] How does vApp handle stuck applications?

---

## Lesson 4: Quotation and Normal Forms (3-4 hours)

### Learning Goals
- Understand the quote function
- Learn the fresh variable trick
- Understand de Bruijn levels

### Activities

1. **Read** README.md sections: Quotation, Normal Forms, De Bruijn Levels vs. Indices

2. **Study** `src/NbE.hs`:
   - Find the `quote` function
   - Find the `Nf` (normal form) type in `Syntax.hs`

3. **The key trick for quoting lambdas**:
   ```haskell
   quote lvl (VLam x closure) =
     let freshVar = VNe (NVar lvl)     -- Create fresh variable
         body = applyClosure closure freshVar  -- Apply to it
     in NfLam x (quote (lvl + 1) body)  -- Quote recursively
   ```

   We "peek inside" the closure by applying it to a fresh variable!

4. **Understand levels vs indices**:
   - Index: counts inward from binding site
   - Level: counts outward from root

   ```
   λ. λ. 0 1   -- indices: inner var is 0, outer is 1
   λ. λ. x y   -- levels at depth 2: x is 0, y is 1
   ```

   Convert: `index = depth - level - 1`

5. **Why levels?** Fresh variable = just increment the level!

6. **Trace** `quote 0 (VLam "x" (Closure [] (TVar 0)))`
   - Create fresh var at level 0
   - Apply closure: `eval [VNe (NVar 0)] (TVar 0)` = `VNe (NVar 0)`
   - Quote that at level 1: `NfNe (NeVar 0)`
   - Result: `NfLam "x" (NfNe (NeVar 0))` = `λx. x`

### Self-Check Questions
- [ ] Why do we need fresh variables to quote lambdas?
- [ ] What's the difference between levels and indices?
- [ ] How is a neutral value quoted?

---

## Lesson 5: Putting It Together (2-3 hours)

### Learning Goals
- Implement full normalization
- Use NbE for equality checking
- Understand eta expansion

### Activities

1. **Normalization is just composition**:
   ```haskell
   normalize :: Term -> Nf
   normalize t = quote 0 (eval [] t)
   ```

2. **Equality check**:
   ```haskell
   equal :: Term -> Term -> Bool
   equal t1 t2 = normalize t1 == normalize t2
   ```

3. **Study** `src/TypeCheck.hs`:
   - Find where equality is checked
   - See how NbE integrates with type checking

4. **Understand eta expansion**:
   ```
   f : A → B   (f is neutral)
   quote(f) = λx. f x   (not just f!)
   ```

   Why? Quoting opens the value with a fresh variable.

5. **Test the implementation**:
   ```bash
   stack test
   ```
   All tests should pass.

6. **Experiment with equality**:
   ```
   nbe> :equal (\x. x) (\y. y)
   true
   nbe> :equal (\x. \y. x) (\a. \b. a)
   true
   ```

### Self-Check Questions
- [ ] How do you normalize a term?
- [ ] Why is eta expansion sometimes desirable?
- [ ] How does NbE help with type checking?

---

## Lesson 6: Extensions and Exercises (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Exercise 1: Trace NbE on examples
   - Exercise 2: Add booleans
   - Exercise 3: Add pairs/Sigma types

2. **Challenge problems**:
   - Universe levels
   - Typed NbE (where evaluation is type-directed)
   - Adding an inductive type

3. **Run all tests**:
   ```bash
   stack test
   ```

4. **Self-assessment**: Can you...
   - [ ] Implement eval for a new term form?
   - [ ] Implement quote for a new value form?
   - [ ] Trace NbE on paper?
   - [ ] Explain why NbE works?

---

## Progress Tracker

### Lesson 1: The Big Picture
- [ ] Understood normalization need
- [ ] Grasped eval-quote paradigm
- [ ] Experimented with REPL

### Lesson 2: The Semantic Domain
- [ ] Understood Val type
- [ ] Grasped closures
- [ ] Understood neutrals

### Lesson 3: Evaluation
- [ ] Studied eval function
- [ ] Understood vApp
- [ ] Traced examples

### Lesson 4: Quotation
- [ ] Understood quote function
- [ ] Grasped fresh variable trick
- [ ] Understood levels vs indices

### Lesson 5: Integration
- [ ] Implemented normalization
- [ ] Used equality checking
- [ ] Understood eta expansion

### Lesson 6: Extensions
- [ ] Completed exercises
- [ ] All tests pass
- [ ] Can extend the system

---

## Key Takeaways

After completing this chapter, remember:

1. **NbE = quote ∘ eval**: Simple composition gives normalization
2. **Closures delay substitution**: Environment + body, not substituted body
3. **Neutrals preserve structure**: Can't reduce, so remember the shape
4. **Fresh variables open closures**: The key trick for quotation
5. **Levels simplify freshness**: Just increment a counter

## Next Steps

After mastering this chapter:
- **Chapter 19 (Bidirectional)**: Uses NbE for type equality
- **Chapter 20 (Denotational)**: Mathematical perspective on meaning
- **Research**: Typed NbE, universe polymorphism, cubical NbE
