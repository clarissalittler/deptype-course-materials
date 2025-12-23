# Chapter 11: Refinement Types - Lesson Plan

**Estimated Total Time**: 14-18 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus (Chapter 2)
- [ ] Subtyping (Chapter 9)
- [ ] Basic predicate logic
- [ ] Function types and application

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain what refinement types are and why they matter
2. Write refinement type annotations with predicates
3. Understand subtyping via predicate implication
4. Apply path sensitivity in conditionals
5. Design APIs with refinement-based safety guarantees
6. Connect refinement types to dependent types and verification

---

## Lesson 1: The Problem of Imprecise Types (2-3 hours)

### Learning Goals
- Understand why simple types are insufficient
- See how refinements add precision
- Learn the core intuition

### Activities

1. **Read** README.md sections: Overview, What Are Refinement Types?

2. **The precision problem**:
   - `div : Nat -> Nat -> Nat` -- What if second arg is 0?
   - `head : List a -> a` -- What if list is empty?
   - `sqrt : Nat -> Nat` -- What if negative (for signed types)?
   - Simple types can't capture "non-zero" or "non-empty"

3. **The refinement solution**:
   - `{x: T | φ(x)}` describes values of T satisfying predicate φ
   - `div : Nat -> {d: Nat | d > 0} -> Nat` -- Requires non-zero!
   - Type system enforces the constraint statically

4. **Key notation**:
   ```
   {x: Nat | x > 0}       -- Positive naturals
   {x: Nat | x < n}       -- Bounded naturals
   (x: T1) -> T2          -- Dependent function (T2 can mention x)
   ```

5. **Experiment** with the REPL:
   ```
   stack exec refinement-repl
   refinement> :type λx : {n : Nat | n > 0}. x
   refinement> :check 5 > 0
   ```

### Self-Check Questions
- [ ] What problem do refinement types solve?
- [ ] How is `{x: Nat | x > 0}` different from `Nat`?
- [ ] Can you express "even number" as a refinement?

---

## Lesson 2: Predicates and Refinements (2-3 hours)

### Learning Goals
- Understand predicate syntax
- Learn how refinements constrain types
- See the relationship to sets

### Activities

1. **Read** README.md sections: Syntax (Types, Predicates)

2. **Predicate syntax**:
   ```
   φ ::= true | false           -- Constants
       | x                      -- Boolean variable
       | !φ | φ && ψ | φ || ψ   -- Boolean connectives
       | φ => ψ                 -- Implication
       | a₁ op a₂               -- Comparisons (==, <, >, etc.)

   a ::= x | n | a₁ + a₂ | a₁ - a₂   -- Arithmetic
   ```

3. **Types as sets**:
   - `Nat` = {0, 1, 2, 3, ...}
   - `{x: Nat | x > 0}` = {1, 2, 3, ...}
   - `{x: Nat | x < 10}` = {0, 1, 2, ..., 9}
   - `{x: Nat | x > 5 && x < 10}` = {6, 7, 8, 9}

4. **Trivial and impossible refinements**:
   ```
   {x: Nat | true}     -- Same as Nat (no constraint)
   {x: Nat | false}    -- Empty type (impossible to inhabit)
   {x: Nat | x >= 0}   -- Same as Nat (always true for Nat)
   ```

5. **Practice**: Write refinement types for:
   - Numbers between 1 and 100
   - Numbers divisible by 2
   - Numbers equal to a specific value

### Self-Check Questions
- [ ] What predicates can you use in refinements?
- [ ] How do you read `{x: Nat | x > 0 && x < 100}`?
- [ ] What values inhabit `{x: Nat | x == 5}`?

---

## Lesson 3: Subtyping and Implication (2-3 hours)

### Learning Goals
- Understand refinement subtyping
- Connect subtyping to predicate implication
- Learn when refinements are compatible

### Activities

1. **Read** README.md sections: Subtyping Rules

2. **The key rule**:
   ```
      Γ ⊢ T₁ <: T₂    ∀x. φ(x) ⟹ ψ(x)
     ──────────────────────────────────── (S-Refine)
         Γ ⊢ {x: T₁ | φ} <: {x: T₂ | ψ}
   ```
   Stronger predicate (more specific) is subtype of weaker one.

3. **Examples**:
   ```
   {x: Nat | x > 5} <: {x: Nat | x > 0}   -- 5 > implies > 0 ✓
   {x: Nat | x > 0} <: {x: Nat | x > 5}   -- NOT true! ✗
   {x: Nat | x == 7} <: {x: Nat | x > 0}  -- 7 is positive ✓
   ```

4. **Intuition**:
   - More specific = fewer values = subtype
   - Less specific = more values = supertype
   - `{x: Nat | x == 5}` has exactly one value (5)
   - `{x: Nat | x > 0}` has infinitely many values

5. **Study** `src/TypeCheck.hs`:
   - Find `isSubtype` function
   - See how `implies` is used
   - Understand the validity checking

### Self-Check Questions
- [ ] Why is `{x: Nat | x > 10}` a subtype of `{x: Nat | x > 5}`?
- [ ] What does predicate implication mean for subtyping?
- [ ] Is `{x: Nat | x > 0}` a subtype of `Nat`? Why?

---

## Lesson 4: Path Sensitivity (2-3 hours)

### Learning Goals
- Understand path-sensitive type checking
- Learn how conditionals affect types
- See the power of flow-sensitive analysis

### Activities

1. **Read** README.md sections: Path Sensitivity

2. **The idea**:
   When entering a branch, we know the condition is true/false:
   ```
      Γ, φ ⊢ t₂ : T₂    Γ, ¬φ ⊢ t₃ : T₃
     ────────────────────────────────────
       Γ ⊢ if t₁ then t₂ else t₃ : T
   ```

3. **Example**:
   ```
   λx : Nat. if iszero x
             then 0
             else pred x  -- Here we KNOW x > 0!
   ```
   In else branch, path condition includes `¬(x == 0)`, so `x > 0`.

4. **Path conditions accumulate**:
   ```haskell
   data Context = Context
     { ctxTypes :: Map Var Type
     , ctxPath  :: [Pred]       -- Accumulated conditions
     }
   ```

5. **Nested conditionals**:
   ```
   if x > 5 then
     if x < 10 then
       -- Here: x > 5 && x < 10
     else
       -- Here: x > 5 && x >= 10
   else
     -- Here: x <= 5
   ```

### Self-Check Questions
- [ ] What is path sensitivity?
- [ ] Why can we call `pred` safely in an else branch after `iszero`?
- [ ] How do path conditions help with refinement checking?

---

## Lesson 5: Dependent Function Types (2-3 hours)

### Learning Goals
- Understand function types that mention arguments
- Learn when return types depend on inputs
- See the connection to full dependent types

### Activities

1. **Read** README.md sections: Dependent Function Types

2. **The syntax**:
   ```
   (x: T₁) -> T₂    -- x is bound in T₂
   ```
   The result type can mention the argument!

3. **Examples**:
   ```
   div : (n: Nat, d: {d: Nat | d > 0}) -> Nat

   replicate : (n: Nat) -> a -> {arr: Vec a | length arr == n}

   head : {xs: List a | length xs > 0} -> a
   ```

4. **Difference from simple functions**:
   - `Nat -> Nat -> Nat` -- result type is just `Nat`
   - `(n: Nat) -> Vec a n` -- result type mentions `n`!

5. **Why useful**:
   - Capture relationships between inputs and outputs
   - Express array bounds
   - Ensure protocol compliance

### Self-Check Questions
- [ ] What makes a function type "dependent"?
- [ ] Write a type for `tail` that requires non-empty list
- [ ] Can the return type change based on input value?

---

## Lesson 6: Predicate Validity (2-3 hours)

### Learning Goals
- Understand how to check predicate implication
- Learn about SMT solvers
- See the tradeoffs in decidability

### Activities

1. **Read** README.md sections: Predicate Validity

2. **The challenge**:
   Given `φ ⟹ ψ`, how do we check if this is true?
   - Ground evaluation: If no variables, just evaluate
   - Syntactic rules: `p ⟹ p` is always true
   - SMT solvers: Full logical reasoning

3. **Our simple approach**:
   ```haskell
   implies :: Pred -> Pred -> Bool
   implies p q
     | p == q = True              -- Reflexivity
     | isGround p && isGround q = evalPred p `implies'` evalPred q
     | otherwise = conservative   -- Be safe
   ```

4. **SMT solvers**:
   - Z3, CVC5, etc. can check complex arithmetic
   - LiquidHaskell uses Z3 for refinement checking
   - Decidable for linear arithmetic

5. **Tradeoffs**:
   - Simple: Fast but incomplete
   - SMT: Complete for decidable theories but slower
   - Undecidable: General arithmetic

### Self-Check Questions
- [ ] What is an SMT solver?
- [ ] Why is full arithmetic undecidable?
- [ ] What does "conservative" mean for validity checking?

---

## Lesson 7: Practical Applications (2-3 hours)

### Learning Goals
- See real-world uses of refinement types
- Understand LiquidHaskell
- Design safe APIs

### Activities

1. **Read** README.md sections: Examples, Connections

2. **Array bounds checking**:
   ```
   get : (arr: Array n a, i: {i: Nat | i < n}) -> a
   ```
   Statically prevents out-of-bounds access!

3. **Non-null guarantees**:
   ```
   type NonNull a = {x: Maybe a | x != Nothing}
   fromJust : NonNull a -> a   -- Always safe
   ```

4. **Protocol verification**:
   ```
   -- File must be open to read, closed after done
   read : {f: File | isOpen f} -> (String, File)
   close : {f: File | isOpen f} -> {f: File | !isOpen f}
   ```

5. **LiquidHaskell** (research direction):
   - Adds refinement types to Haskell
   - Uses SMT solving for verification
   - Practical for real code

### Self-Check Questions
- [ ] How do refinement types prevent array bounds errors?
- [ ] What guarantees does `NonNull` provide?
- [ ] How are refinement types related to contracts?

---

## Lesson 8: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Basic refinement types
   - Subtyping relationships
   - Path sensitivity
   - Dependent functions

2. **Run all tests**:
   ```bash
   stack test
   ```
   All 82 tests should pass.

3. **Challenge problems**:
   - Integrate an SMT solver
   - Implement liquid type inference
   - Add support for user-defined predicates

4. **Self-assessment**: Can you...
   - [ ] Write refinement type annotations?
   - [ ] Determine subtyping via implication?
   - [ ] Use path sensitivity effectively?
   - [ ] Design safe APIs with refinements?

---

## Progress Tracker

### Lesson 1: The Problem
- [ ] Understood precision issues
- [ ] Grasped refinement intuition
- [ ] Experimented with REPL

### Lesson 2: Predicates
- [ ] Know predicate syntax
- [ ] Understand types as sets
- [ ] Can write refinement types

### Lesson 3: Subtyping
- [ ] Understand implication rule
- [ ] Can determine subtypes
- [ ] Know specific vs general

### Lesson 4: Path Sensitivity
- [ ] Understand flow sensitivity
- [ ] Can track path conditions
- [ ] See benefit for safety

### Lesson 5: Dependent Functions
- [ ] Know dependent syntax
- [ ] Can express relationships
- [ ] See connection to full dependent types

### Lesson 6: Validity
- [ ] Understand checking approaches
- [ ] Know about SMT solvers
- [ ] Aware of decidability issues

### Lesson 7: Applications
- [ ] See practical uses
- [ ] Know LiquidHaskell
- [ ] Can design safe APIs

### Lesson 8: Exercises
- [ ] Completed exercises
- [ ] All tests pass
- [ ] Can apply concepts

---

## Key Takeaways

1. **Refinements add precision**: `{x: T | φ}` constrains values
2. **Subtyping via implication**: Stronger predicate = subtype
3. **Path sensitivity**: Branches give us information
4. **Dependent functions**: Return types can mention arguments
5. **Practical value**: Prevent bugs statically

## Next Steps

After mastering this chapter:
- **Chapter 12 (Effect Systems)**: Track computational effects
- **Research**: Liquid types, verification tools
- **Practice**: Annotate existing code with refinements
