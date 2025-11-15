{-# LANGUAGE LambdaCase #-}

module Hints where

import Syntax
import TypeCheck
import Eval

{-
  CHAPTER 2 EXERCISE HINTS

  This file provides scaffolding and hints for the exercises.
  Try to implement solutions yourself before looking at Solutions.hs!
-}

-- =============================================================================
-- Exercise 1: Arithmetic Extensions
-- =============================================================================

{- Exercise 1a: Multiplication

   HINT: Think recursively!
   mult m n = if iszero m then 0 else add n (mult (pred m) n)

   This is similar to how you'd implement addition.

   COMMON PITFALL: Remember that STLC doesn't have general recursion,
   so we can't write true recursive functions without fix.
   For exercises, we'll use pseudo-recursion or work with small fixed examples.
-}

-- Type signature to implement:
-- multNat :: Term -> Term -> Term
-- multNat m n = undefined

{- Exercise 1b: Less Than

   HINT: Compare by repeatedly decrementing both numbers.
   lt m n works like this:
   - If m is zero and n is not zero: true
   - If both are zero: false
   - If n is zero but m is not: false
   - Otherwise: recursively check lt (pred m) (pred n)

   Think about the base cases carefully!
-}

-- ltNat :: Term -> Term -> Term
-- ltNat m n = undefined

{- Exercise 1c: Equality

   HINT: Two numbers are equal if:
   - Both are zero, OR
   - Neither is zero AND (pred m) equals (pred n)

   This is very similar to less-than but with different base cases.
-}

-- eqNat :: Term -> Term -> Term
-- eqNat m n = undefined

-- =============================================================================
-- Exercise 2: Product Types (Medium)
-- =============================================================================

{- Exercise 2: Product Types

   NOTE: The current syntax doesn't include product types.
   To properly implement this exercise, you would need to extend Syntax.hs:

   1. Add to Type:
      data Type = ... | TyProd Type Type

   2. Add to Term:
      data Term = ...
                | TmPair Term Term
                | TmFst Term
                | TmSnd Term

   3. Add typing rules in TypeCheck.hs:
      typeOf ctx (TmPair t1 t2) = do
        ty1 <- typeOf ctx t1
        ty2 <- typeOf ctx t2
        return (TyProd ty1 ty2)

      typeOf ctx (TmFst t) = do
        ty <- typeOf ctx t
        case ty of
          TyProd ty1 ty2 -> return ty1
          _ -> Left "fst requires pair type"

   4. Add evaluation rules in Eval.hs:
      step (TmFst (TmPair v1 v2)) | isValue v1 && isValue v2 = Just v1
      step (TmSnd (TmPair v1 v2)) | isValue v1 && isValue v2 = Just v2

   LEARNING OBJECTIVE: Understanding how to systematically extend a type system.
-}

-- =============================================================================
-- Exercise 3: Sum Types (Medium)
-- =============================================================================

{- Exercise 3: Sum Types

   NOTE: Similar to product types, sum types require syntax extension:

   1. Add to Type:
      data Type = ... | TySum Type Type

   2. Add to Term:
      data Term = ...
                | TmInl Type Term  -- left injection with type annotation
                | TmInr Type Term  -- right injection with type annotation
                | TmCase Term Var Term Var Term  -- case analysis

   3. Typing rules:
      Γ ⊢ t : τ₁
      ──────────────────── T-Inl
      Γ ⊢ inl[τ₂] t : τ₁ + τ₂

      (Similar for inr)

      Γ ⊢ t : τ₁ + τ₂    Γ, x:τ₁ ⊢ t₁ : τ    Γ, y:τ₂ ⊢ t₂ : τ
      ────────────────────────────────────────────────────────── T-Case
      Γ ⊢ case t of inl x => t₁ | inr y => t₂ : τ

   4. Evaluation:
      case (inl v) of inl x => t₁ | inr y => t₂  →  t₁[x := v]
      case (inr v) of inl x => t₁ | inr y => t₂  →  t₂[y := v]

   DESIGN QUESTION: Why do we need type annotations on inl/inr?
   Answer: Without them, we can't determine the full type τ₁ + τ₂
-}

-- =============================================================================
-- Exercise 4: Let Bindings (Medium)
-- =============================================================================

{- Exercise 4: Let as Syntactic Sugar

   HINT: This one you CAN implement with current syntax!

   The key insight: let bindings are just syntactic sugar for lambda application.

   let x = t₁ in t₂  ≡  (λx:τ. t₂) t₁

   where τ is the type of t₁.

   STEPS:
   1. Type check t₁ to get its type τ
   2. Create a lambda abstraction λx:τ. t₂
   3. Apply it to t₁

   Example:
   let x = 3 in x + 1
   becomes:
   (λx:Nat. x + 1) 3
-}

desugarLet :: Var -> Term -> Type -> Term -> Term
desugarLet x t1 ty t2 = undefined
  -- HINT: Use Lam and App constructors

{- Try implementing this example:
   let x = 2 in let y = 3 in add x y
-}

-- exampleLet :: Term
-- exampleLet = undefined

-- =============================================================================
-- Exercise 5: Fixed Point Combinator (Hard)
-- =============================================================================

{- Exercise 5: Typed Fixed Point

   NOTE: This requires syntax extension.

   The fix operator enables general recursion:

   fix : (τ → τ) → τ

   Typing rule:
      Γ ⊢ t : τ → τ
      ─────────────── T-Fix
      Γ ⊢ fix t : τ

   Evaluation rule:
      fix v  →  v (fix v)

   KEY INSIGHT: fix "unrolls" one step of recursion.

   Example - Factorial:
   factorial = fix (λf:Nat→Nat. λn:Nat.
                 if iszero n then 1
                 else mult n (f (pred n)))

   IMPORTANT: Unlike untyped lambda calculus, we need fix as a primitive.
   The Y combinator doesn't type check in STLC!

   WHY? Because Y = λf. (λx. f (x x)) (λx. f (x x))
   The self-application (x x) requires x to have type α → β AND type α
   simultaneously, which is impossible in STLC.
-}

-- =============================================================================
-- Exercise 6: Type Safety (Hard)
-- =============================================================================

{- Exercise 6a: Progress

   Progress Theorem: If ⊢ t : τ, then either:
   1. t is a value, OR
   2. There exists t' such that t → t'

   In other words: well-typed terms don't get "stuck".

   HINT: Implement by cases on the term structure.
   For each term form, check if it's a value or can step.
-}

data ProgressResult
  = IsValue        -- The term is already a value
  | CanStep Term   -- The term can step to this term
  | Stuck          -- The term is stuck (shouldn't happen for well-typed terms!)
  deriving (Eq, Show)

-- demonstrateProgress :: Term -> ProgressResult
-- demonstrateProgress t = undefined
  -- HINT: Check isValue first, then try step

{- Exercise 6b: Preservation

   Preservation Theorem: If Γ ⊢ t : τ and t → t', then Γ ⊢ t' : τ

   In other words: evaluation preserves types.

   HINT: Check that both t and t' have the same type.
-}

-- demonstratePreservation :: TypeContext -> Term -> Type -> Bool
-- demonstratePreservation ctx t ty = undefined
  -- HINT:
  -- 1. Check t has type ty
  -- 2. Step t to get t'
  -- 3. Check t' also has type ty

-- =============================================================================
-- Testing Your Solutions
-- =============================================================================

{- To test your implementations:

   1. Load this file in GHCi:
      $ stack ghci
      > :load exercises/Hints.hs

   2. Try evaluating your functions:
      > eval (multNat (natFromInt 3) (natFromInt 4))
      > eval exampleLet

   3. Type check them:
      > typeOf emptyCtx yourTerm

   4. Run the test suite:
      $ stack test
-}

-- =============================================================================
-- Helper Functions (provided)
-- =============================================================================

-- Convert Int to Term representation of Nat
natFromInt :: Int -> Term
natFromInt 0 = TmZero
natFromInt n = TmSucc (natFromInt (n - 1))

-- =============================================================================
-- Common Mistakes to Avoid
-- =============================================================================

{-
  1. FORGETTING TYPE ANNOTATIONS
     ✗ Lam "x" undefined (Var "x")
     ✓ Lam "x" TyNat (Var "x")

  2. CONFUSING EVALUATION AND TYPE CHECKING
     Evaluation: runs the program
     Type checking: verifies it's safe to run
     They are separate phases!

  3. NOT HANDLING ALL CASES
     When pattern matching, handle all constructors.
     The compiler will warn about incomplete patterns.

  4. VARIABLE CAPTURE
     Be careful with substitution!
     The substVar function handles this automatically.

  5. ASSUMING GENERAL RECURSION
     STLC doesn't have general recursion without fix.
     Direct recursive definitions won't work in the term language.
-}

-- =============================================================================
-- Further Reading
-- =============================================================================

{-
  Pierce, "Types and Programming Languages":
  - Chapter 11: Simple Extensions (products, sums, let, fix)
  - Chapter 8: Typing Rules
  - Chapter 9: Properties (Progress, Preservation)

  Harper, "Practical Foundations for Programming Languages":
  - Chapter 10: Product and Sum Types
  - Chapter 19: Fixed Points
-}
