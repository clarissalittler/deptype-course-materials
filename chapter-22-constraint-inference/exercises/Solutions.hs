{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import Constraint
import Solve
import Infer
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- ============================================================================
-- Exercise 1: Constraint Generation
-- ============================================================================

{-
Part A: λx. λy. x

Constraint Generation:
  α fresh (for x)
  β fresh (for y)
  x:α, y:β ⊢ x ⇝ α | ∅
  x:α ⊢ λy. x ⇝ β → α | ∅
  ⊢ λx. λy. x ⇝ α → β → α | ∅

Constraints: ∅ (no constraints!)
Inferred type: t0 → t1 → t0
Final type: t0 → t1 → t0 (already in normal form)

Part B: λf. f 0

Constraint Generation:
  α fresh (for f)
  β fresh (for result)
  f:α ⊢ f ⇝ α | ∅
  f:α ⊢ 0 ⇝ Nat | ∅
  f:α ⊢ f 0 ⇝ β | {α ≡ Nat → β}
  ⊢ λf. f 0 ⇝ α → β | {α ≡ Nat → β}

Constraints: {α ≡ Nat → β}
Inferred type: α → β where α ≡ Nat → β
After solving: (Nat → β) → β  or simplified: (Nat → t1) → t1

Part C: λx. if x then 0 else succ 0

Constraint Generation:
  α fresh (for x)
  x:α ⊢ x ⇝ α | ∅
  x:α ⊢ 0 ⇝ Nat | ∅
  x:α ⊢ succ 0 ⇝ Nat | ∅
  x:α ⊢ if x then 0 else succ 0 ⇝ Nat | {α ≡ Bool, Nat ≡ Nat}
  ⊢ λx. if x then 0 else succ 0 ⇝ α → Nat | {α ≡ Bool}

Constraints: {α ≡ Bool}
Final type: Bool → Nat

Part D: λx. (x, x)

Constraint Generation:
  α fresh (for x)
  x:α ⊢ x ⇝ α | ∅
  x:α ⊢ (x, x) ⇝ α × α | ∅
  ⊢ λx. (x, x) ⇝ α → α × α | ∅

Constraints: ∅
Final type: t0 → t0 × t0
-}

ex1a, ex1b, ex1c, ex1d :: Term
ex1a = Lam "x" (Lam "y" (Var "x"))
ex1b = Lam "f" (App (Var "f") TmZero)
ex1c = Lam "x" (TmIf (Var "x") TmZero (TmSucc TmZero))
ex1d = Lam "x" (TmPair (Var "x") (Var "x"))

-- ============================================================================
-- Exercise 2: Unification
-- ============================================================================

{-
Part A: t0 → t1 ≡ Bool → Nat
  Unify t0 → t1 with Bool → Nat:
    Unify t0 with Bool: {t0 ↦ Bool}
    Unify t1 with Nat: {t1 ↦ Nat}
  MGU: {t0 ↦ Bool, t1 ↦ Nat}

Part B: t0 → t0 ≡ Bool → Nat
  Unify t0 → t0 with Bool → Nat:
    Unify t0 with Bool: {t0 ↦ Bool}
    Unify t0 with Nat (after substitution):
      Bool ≡ Nat → FAIL!
  Error: Cannot unify Bool and Nat

Part C: t0 → t1 ≡ t1 → t0
  Unify t0 → t1 with t1 → t0:
    Unify t0 with t1: {t0 ↦ t1}
    Unify t1 with t0 after subst:
      Unify t1 with t1: {}
  MGU: {t0 ↦ t1}
  Result type: t1 → t1 (identity!)

Part D: t0 ≡ List t0
  Occurs check: t0 occurs in List t0
  This would create infinite type: t0 = List t0 = List (List t0) = ...
  Error: Occurs check failure

Part E: (t0 → t1) → t2 ≡ (Bool → t3) → Nat
  Unify (t0 → t1) → t2 with (Bool → t3) → Nat:
    Unify t0 → t1 with Bool → t3:
      Unify t0 with Bool: {t0 ↦ Bool}
      Unify t1 with t3: {t1 ↦ t3}
    Unify t2 with Nat: {t2 ↦ Nat}
  MGU: {t0 ↦ Bool, t1 ↦ t3, t2 ↦ Nat}
-}

ex2a, ex2b, ex2c, ex2d, ex2e :: Either SolveError Subst
ex2a = unify (TyArr (TyVar "t0") (TyVar "t1")) (TyArr TyBool TyNat)
ex2b = unify (TyArr (TyVar "t0") (TyVar "t0")) (TyArr TyBool TyNat)
ex2c = unify (TyArr (TyVar "t0") (TyVar "t1")) (TyArr (TyVar "t1") (TyVar "t0"))
ex2d = unify (TyVar "t0") (TyList (TyVar "t0"))
ex2e = unify (TyArr (TyArr (TyVar "t0") (TyVar "t1")) (TyVar "t2"))
             (TyArr (TyArr TyBool (TyVar "t3")) TyNat)

-- ============================================================================
-- Exercise 3: Let-Polymorphism
-- ============================================================================

{-
Part A: Why this type checks:
  let id = λx. x in (id true, id 0)

The key is LET-POLYMORPHISM:
1. We infer id : α → α
2. We GENERALIZE: id : ∀α. α → α
3. At first use (id true), we INSTANTIATE with fresh β:
   id : β → β, then unify β ≡ Bool
4. At second use (id 0), we INSTANTIATE with fresh γ:
   id : γ → γ, then unify γ ≡ Nat
5. Final type: Bool × Nat

Each use gets its OWN type variable!

Part B: Why this does NOT type check:
  (λid. (id true, id 0)) (λx. x)

Here id is lambda-bound, NOT let-bound:
1. id gets a SINGLE monomorphic type α → α
2. From id true: α ≡ Bool
3. From id 0: α ≡ Nat
4. Constraint: Bool ≡ Nat → FAIL!

Lambda-bound variables are NOT generalized!

Part C: Constraints

Let version:
  Constraints for λx. x: ∅
  Type: ∀α. α → α (generalized!)

  At id true: instantiate to β → β, constraint {β ≡ Bool}
  At id 0: instantiate to γ → γ, constraint {γ ≡ Nat}

  All constraints: {β ≡ Bool, γ ≡ Nat} (solvable!)

Lambda version:
  id has type α → α (monomorphic!)

  From id true: {α ≡ Bool}
  From id 0: {α ≡ Nat}

  All constraints: {α ≡ Bool, α ≡ Nat} (unsolvable!)

Part D: Fix by using let:
  (λid. let id' = id in (id' true, id' 0)) (λx. x)

  Or just:
  let id = λx. x in (id true, id 0)
-}

ex3_works :: Term
ex3_works = Let "id" (Lam "x" (Var "x"))
                (TmPair (App (Var "id") TmTrue)
                       (App (Var "id") TmZero))

ex3_fails :: Term
ex3_fails = App (Lam "id" (TmPair (App (Var "id") TmTrue)
                                  (App (Var "id") TmZero)))
               (Lam "x" (Var "x"))

-- ============================================================================
-- Exercise 4: Constraint Solving
-- ============================================================================

{-
Given constraints:
{
  t0 ≡ t1 → t2,
  t1 ≡ Bool,
  t2 ≡ t3 → Nat,
  t3 ≡ Bool
}

Step-by-step solving:

Step 1: Solve t0 ≡ t1 → t2
  σ₁ = {t0 ↦ t1 → t2}
  Remaining: {t1 ≡ Bool, t2 ≡ t3 → Nat, t3 ≡ Bool}

Step 2: Apply σ₁ and solve t1 ≡ Bool
  σ₂ = {t1 ↦ Bool}
  σ = σ₂ ∘ σ₁ = {t0 ↦ Bool → t2, t1 ↦ Bool}
  Remaining: {t2 ≡ t3 → Nat, t3 ≡ Bool}

Step 3: Apply σ and solve t2 ≡ t3 → Nat
  σ₃ = {t2 ↦ t3 → Nat}
  σ = σ₃ ∘ σ = {t0 ↦ Bool → (t3 → Nat), t1 ↦ Bool, t2 ↦ t3 → Nat}
  Remaining: {t3 ≡ Bool}

Step 4: Apply σ and solve t3 ≡ Bool
  σ₄ = {t3 ↦ Bool}
  σ = σ₄ ∘ σ = {t0 ↦ Bool → (Bool → Nat), t1 ↦ Bool, t2 ↦ Bool → Nat, t3 ↦ Bool}

Final: {t0 ↦ Bool → Bool → Nat, t1 ↦ Bool, t2 ↦ Bool → Nat, t3 ↦ Bool}

Part C: Add constraint t0 ≡ Nat → t4

After step 1, we have t0 ↦ t1 → t2
New constraint: t1 → t2 ≡ Nat → t4
This gives: t1 ≡ Nat, t2 ≡ t4

But we also have t1 ≡ Bool from step 2!
So: Bool ≡ Nat → FAIL!

The constraints would NOT be solvable.
-}

ex4_constraints :: ConstraintSet
ex4_constraints =
  [ Equal (TyVar "t0") (TyArr (TyVar "t1") (TyVar "t2"))
  , Equal (TyVar "t1") TyBool
  , Equal (TyVar "t2") (TyArr (TyVar "t3") TyNat)
  , Equal (TyVar "t3") TyBool
  ]

ex4_solve :: Either SolveError Subst
ex4_solve = solve ex4_constraints

-- ============================================================================
-- Exercise 5: Occurs Check
-- ============================================================================

{-
Part A: Why λx. x x fails

The term tries to apply x to itself. For this to type check:
  x : α (some type)
  x x : applying x to x requires x : α → β for some β
  So: α ≡ α → β

Part B: Generated constraint

  α fresh (for x)
  β fresh (for result)
  x:α ⊢ x ⇝ α | ∅
  x:α ⊢ x ⇝ α | ∅
  x:α ⊢ x x ⇝ β | {α ≡ α → β}

Constraint: {α ≡ α → β}

Part C: Why this creates infinite type

If we allow α ≡ α → β, then:
  α = α → β         (substitute α into itself)
  α = (α → β) → β   (substitute again)
  α = ((α → β) → β) → β
  α = (((α → β) → β) → β) → β
  ... infinite!

Part D: Infinite expansion

  α = α → β
    = (α → β) → β
    = ((α → β) → β) → β
    = (((α → β) → β) → β) → β
    = ((((α → β) → β) → β) → β) → β
    ...

This is called a "recursive type" or "infinite type". Some languages
(like Haskell with -XRecursiveDo) allow them, but they make type
checking undecidable!
-}

ex5_selfapp :: Term
ex5_selfapp = Lam "x" (App (Var "x") (Var "x"))

-- This will fail with occurs check error
ex5_infer :: Either InferenceError Type
ex5_infer = infer ex5_selfapp

-- ============================================================================
-- Exercise 13: Comparison with Algorithm W
-- ============================================================================

{-
Part A: Advantages of Constraint-Based Inference

1. MODULARITY: Easy to add new constraints (subtyping, effects, etc.)
   - Algorithm W: everything interleaved, hard to extend
   - Constraints: just add new constraint types

2. DEBUGGING: Explicit constraint sets make debugging easier
   - Algorithm W: "type error" at specific location
   - Constraints: can show ALL conflicting constraints

3. ERROR MESSAGES: Can explain WHY constraints arise
   - Algorithm W: "cannot unify Bool and Nat"
   - Constraints: "from if condition (line 5), Bool required; from branch (line 6), Nat inferred"

Part B: Disadvantages

1. COMPLEXITY: Two-phase approach is more code
   - Algorithm W: single recursive function
   - Constraints: generation + solving + composition

2. PERFORMANCE: Can be slower due to constraint manipulation
   - Algorithm W: direct substitution
   - Constraints: build constraint set, then solve

Part C: Debugging Example

Consider: λx. if (succ x) then 0 else 1

Algorithm W error:
  "Type error: cannot unify Nat with Bool"
  (Where? Why? Not clear!)

Constraint-Based error:
  "Generated constraints:
     t0 ≡ Nat        (from: succ requires Nat argument)
     Nat ≡ Bool      (from: if condition requires Bool)

   Constraint Nat ≡ Bool failed:
     - Nat comes from: succ x at line 1, column 8
     - Bool required by: if condition at line 1, column 5

   Suggestion: Remove succ, or use iszero instead of if"

Much more helpful!
-}

-- Example showing better debugging
ex13_error_term :: Term
ex13_error_term = Lam "x" (TmIf (TmSucc (Var "x")) TmZero (TmSucc TmZero))

-- Try: generateConstraints ex13_error_term
-- You'll see the exact constraints that conflict!

-- ============================================================================
-- Helper Functions for Testing
-- ============================================================================

-- Run constraint generation
testGenerate :: Term -> Either ConstraintError (ConstraintSet, Type)
testGenerate = generateConstraints

-- Run full inference
testInfer :: Term -> Either InferenceError Type
testInfer = infer

-- Test unification
testUnify :: Type -> Type -> Either SolveError Subst
testUnify = unify

-- Pretty print results
prettyResult :: Either InferenceError Type -> String
prettyResult (Left err) = "Error: " ++ show err
prettyResult (Right ty) = "Type: " ++ show ty
