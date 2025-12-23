# Chapter 22 Exercises: Constraint-Based Type Inference

## Exercise 1: Constraint Generation (⭐)

**Goal:** Understand how constraints are generated from terms.

For each term below, write out:
1. The generated constraints
2. The inferred type (before solving)
3. The final type (after solving)

### Part A
```haskell
λx. λy. x
```

### Part B
```haskell
λf. f 0
```

### Part C
```haskell
λx. if x then 0 else succ 0
```

### Part D
```haskell
λx. (x, x)
```

---

## Exercise 2: Unification (⭐⭐)

**Goal:** Practice Robinson's unification algorithm.

For each pair of types, determine:
1. Whether they unify
2. If yes, the most general unifier (MGU)
3. If no, why not

### Part A
```
t0 → t1  ≡  Bool → Nat
```

### Part B
```
t0 → t0  ≡  Bool → Nat
```

### Part C
```
t0 → t1  ≡  t1 → t0
```

### Part D
```
t0  ≡  List t0
```

### Part E
```
(t0 → t1) → t2  ≡  (Bool → t3) → Nat
```

---

## Exercise 3: Let-Polymorphism (⭐⭐)

**Goal:** Understand the difference between let and lambda binding.

### Part A
Explain why this type checks:
```haskell
let id = λx. x in (id true, id 0)
```

### Part B
Explain why this does NOT type check:
```haskell
(λid. (id true, id 0)) (λx. x)
```

### Part C
What constraints are generated for each version?

### Part D
Modify the lambda version to make it type check.

---

## Exercise 4: Constraint Solving (⭐⭐)

**Goal:** Practice the constraint solving algorithm.

Given the constraint set:
```
{
  t0 ≡ t1 → t2,
  t1 ≡ Bool,
  t2 ≡ t3 → Nat,
  t3 ≡ Bool
}
```

### Part A
Solve the constraints step by step, showing the substitution after each step.

### Part B
What is the final substitution σ?

### Part C
If we had an additional constraint `t0 ≡ Nat → t4`, would the constraints still be solvable? Why or why not?

---

## Exercise 5: Occurs Check (⭐⭐)

**Goal:** Understand the occurs check and infinite types.

### Part A
Why does `λx. x x` fail to type check?

### Part B
What constraint is generated?

### Part C
Why would allowing `α ≡ α → β` create an infinite type?

### Part D
Show the infinite expansion that would result.

---

## Exercise 6: Implementing Constraint Generation (⭐⭐⭐)

**Goal:** Extend constraint generation with new features.

### Part A: Pairs
Modify `generateConstraints` to handle pairs `(e₁, e₂)` and projections `fst e`, `snd e`.

**Hint:** Use fresh type variables for unknown component types.

### Part B: Lists
Add constraint generation for:
- Empty list `[]`
- Cons `e₁ :: e₂`
- List operations: `head`, `tail`, `isnil`

### Part C: Fixed Point
Add constraint generation for a fixed-point operator:
```haskell
fix : (α → α) → α
```

---

## Exercise 7: Error Messages (⭐⭐⭐)

**Goal:** Improve error reporting using constraint information.

### Part A
For the term `if 0 then true else false`, write a function that:
1. Generates constraints
2. Detects the error during solving
3. Produces a helpful error message explaining where `Nat` and `Bool` are expected

### Part B
For the term `λx. x x`, explain:
1. Where the occurs check fails
2. Why this represents a type error
3. How to report this clearly to the user

---

## Exercise 8: Constraint Simplification (⭐⭐⭐)

**Goal:** Optimize constraint solving by simplifying constraints.

### Part A
Implement a function `simplify :: ConstraintSet -> ConstraintSet` that:
1. Removes trivial constraints like `Bool ≡ Bool`
2. Combines duplicate constraints
3. Applies obvious substitutions early

### Part B
Test your simplification on:
```
{
  t0 ≡ Bool,
  Bool ≡ Bool,
  t1 ≡ t0,
  t0 ≡ Bool,
  t2 ≡ t1 → Nat
}
```

---

## Exercise 9: Bidirectional Constraints (⭐⭐⭐⭐)

**Goal:** Combine constraint generation with bidirectional type checking.

### Part A
Modify the constraint generation to support **checking mode**:
```
Γ ⊢ e ⇐ τ | C    (check that e has type τ)
Γ ⊢ e ⇒ τ | C    (infer type τ for e)
```

### Part B
Add a rule for checking lambda against function type:
```
Γ, x:τ₁ ⊢ e ⇐ τ₂ | C
─────────────────────────
Γ ⊢ λx. e ⇐ τ₁ → τ₂ | C
```

### Part C
Why is this more efficient than pure inference?

---

## Exercise 10: Subtyping Constraints (⭐⭐⭐⭐)

**Goal:** Extend to constraint-based subtyping (see Chapter 9).

### Part A
Add a new constraint type:
```haskell
data Constraint
  = Equal Type Type
  | Subtype Type Type    -- τ₁ <: τ₂
```

### Part B
Implement a solver that handles both equality and subtyping constraints:
```haskell
solveSubtyping :: ConstraintSet -> Either Error Subst
```

### Part C
Add constraint generation for record width subtyping:
```
{x:τ₁, y:τ₂} <: {x:τ₁}
```

---

## Exercise 11: Type Classes (⭐⭐⭐⭐⭐)

**Goal:** Use constraints for type class resolution (Haskell-style).

### Part A
Add instance constraints:
```haskell
data Constraint
  = Equal Type Type
  | InstanceOf TypeClass Type    -- Show τ, Eq τ, etc.
```

### Part B
Implement constraint generation for:
```haskell
show :: Show α => α → String
(==) :: Eq α => α → α → Bool
```

### Part C
Show how to resolve instance constraints using a constraint solver.

---

## Exercise 12: Effects and Regions (⭐⭐⭐⭐⭐)

**Goal:** Track effects using constraints.

### Part A
Add effect constraints:
```haskell
data Constraint
  = Equal Type Type
  | HasEffect Term Effect    -- e has effect IO, State, etc.
```

### Part B
Generate constraints for:
```haskell
print : String → IO ()
pure : α → IO α
bind : IO α → (α → IO β) → IO β
```

### Part C
Ensure purity: reject programs that perform IO in pure contexts.

---

## Exercise 13: Constraint-Based Inference vs Algorithm W (⭐⭐)

**Goal:** Compare the two approaches.

### Part A
List 3 advantages of constraint-based inference over Algorithm W.

### Part B
List 2 disadvantages.

### Part C
Give an example where constraint-based inference makes debugging easier.

---

## Exercise 14: SMT Integration (⭐⭐⭐⭐⭐)

**Goal:** Connect constraints to SMT solvers (advanced).

### Part A
Design a constraint language for refinement types:
```haskell
data Refinement
  = IntGE Int          -- x ≥ n
  | IntLE Int          -- x ≤ n
  | And Refinement Refinement
  | Or Refinement Refinement

data Constraint
  = Equal Type Type
  | Refines Var Type Refinement    -- {x:τ | φ}
```

### Part B
Show how to encode constraints as SMT-LIB:
```smt
(declare-const x Int)
(assert (>= x 0))
(check-sat)
```

### Part C
Give an example of a program that type checks with refinements but would fail without them.

---

## Challenge Exercises

### Challenge 1: Constraint Graph Visualization (⭐⭐⭐⭐)
Build a tool that:
1. Generates constraints from a term
2. Visualizes the constraint graph
3. Shows the solving process step-by-step

### Challenge 2: Polymorphic Recursion (⭐⭐⭐⭐⭐)
Extend constraint generation to support polymorphic recursion:
```haskell
-- length is used at multiple types within itself
length : ∀α. List α → Nat
length [] = 0
length (x::xs) = 1 + length xs
```

### Challenge 3: Higher-Rank Types (⭐⭐⭐⭐⭐)
Add constraint generation for System F-style explicit polymorphism:
```haskell
runST : (∀s. ST s α) → α
```

Hint: You need to track which type variables are bound where.

---

## Testing Your Solutions

Use the REPL to test:

```haskell
-- Check constraint generation
λ> :constraints your-term

-- Check full solving process
λ> :solve your-term

-- Test unification
λ> :unify type1 type2

-- See the final type
λ> :type your-term
```

## Submission

Implement your solutions in `exercises/Solutions.hs` and ensure all tests pass:

```bash
cd chapter-22-constraint-inference
stack test
```
