{-# LANGUAGE OverloadedStrings #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Map as Map

-- ============================================================================
-- Exercise 1: Understanding μ Types (Conceptual)
-- ============================================================================

-- 1.1 Type Unfolding
-- NatList = μα. Unit + (Nat × α)
-- Unfolding once: Unit + (Nat × (μα. Unit + (Nat × α)))
-- This represents either:
--   - inl () : The empty list (Nil)
--   - inr (n, rest) : A cons cell with a nat n and the rest of the list

-- 1.2 Iso-recursive vs Equi-recursive
-- In this implementation, we use iso-recursive types:
-- - fold and unfold are explicit coercions
-- - μα.T is distinct from but isomorphic to T[μα.T/α]
-- - This makes type-checking decidable and implementation simpler

-- 1.3 Type Equivalence
-- T1 = μα. Nat → α and T2 = μβ. Nat → β should be equal (alpha-equivalence)
-- T3 = μα. Nat → (Nat → α) unfolds to Nat → (Nat → (μα. Nat → (Nat → α)))
-- T3 is NOT equal to T1; it takes two Nats instead of one

-- ============================================================================
-- Exercise 2: Encoding Data Structures
-- ============================================================================

-- 2.1 Binary Trees
-- Tree = μα. Nat + (α × α)

-- Define the Tree type
treeType :: Type
treeType = TyMu "α" (TySum TyNat (TyProd (TyVar "α") (TyVar "α")))

-- leaf : Nat → Tree
-- Creates a leaf node by injecting a Nat into the left of the sum
leaf :: Term
leaf = Lam "n" TyNat
       (TmFold treeType
         (TmInl (Var "n") (TySum TyNat (TyProd treeType treeType))))

-- node : Tree → Tree → Tree
-- Creates an internal node by injecting a pair into the right of the sum
node :: Term
node = Lam "l" treeType
       (Lam "r" treeType
         (TmFold treeType
           (TmInr (TmPair (Var "l") (Var "r"))
                  (TySum TyNat (TyProd treeType treeType)))))

-- Helper to create test trees
testTree1 :: Term
testTree1 = App leaf TmZero

testTree2 :: Term
testTree2 = App (App node testTree1) testTree1

-- sumTree : Tree → Nat
-- Sums all values in a tree using unfold to eliminate the recursive type
sumTree :: Term
sumTree = Lam "t" treeType
          (TmCase (TmUnfold treeType (Var "t"))
            "n" (Var "n")  -- leaf case: just return the nat
            "p" (TmLet "l" (TmFst (Var "p"))
                  (TmLet "r" (TmSnd (Var "p"))
                    -- Recursively sum left and right
                    -- In a real implementation we'd need a fixed-point combinator
                    -- For now this is conceptual
                    (Var "l"))))  -- Simplified

-- 2.2 Streams (Infinite Lists)
-- Stream = μα. Nat × α

streamType :: Type
streamType = TyMu "α" (TyProd TyNat (TyVar "α"))

-- constStream : Nat → Stream
-- Creates an infinite stream of the same value
-- Note: This requires general recursion (a fixed point)
-- We show the structure but it won't terminate without special evaluation
constStream :: Term
constStream = Lam "n" TyNat
              (TmFold streamType
                (TmPair (Var "n")
                  -- This should be (constStream n) but we can't express that
                  -- without a fix-point combinator
                  (Var "n")))  -- Placeholder

-- head : Stream → Nat
-- Get the first element of a stream
headStream :: Term
headStream = Lam "s" streamType
             (TmFst (TmUnfold streamType (Var "s")))

-- tail : Stream → Stream
-- Get the rest of the stream
tailStream :: Term
tailStream = Lam "s" streamType
             (TmSnd (TmUnfold streamType (Var "s")))

-- Question: Can we define a stream of ascending natural numbers?
-- Yes, but only with general recursion via a fixed-point combinator.
-- The stream would be: μα. fold (n, fold (succ n, fold (succ (succ n), ...)))

-- 2.3 Optional Values
-- Option doesn't really need recursion; this would work:
-- Option A = Unit + A
-- The μ is unnecessary here because there's no self-reference in the body.
-- Recursion is necessary when the type variable appears in the body.

-- ============================================================================
-- Exercise 3: The Lambda Calculus in Lambda Calculus
-- ============================================================================

-- 3.1 Untyped Terms
-- UTerm = μα. Nat + (α × α) + α
-- Actually, for lambda we need: μα. Nat + (α × α) + α
-- Where: Var n | App t1 t2 | Lam body

utermType :: Type
utermType = TyMu "α"
            (TySum TyNat
              (TySum (TyProd (TyVar "α") (TyVar "α"))
                     (TyVar "α")))

-- Helper to create Var
utermVar :: Term -> Term
utermVar n = TmFold utermType
             (TmInl n (TySum TyNat
                        (TySum (TyProd utermType utermType)
                               utermType)))

-- Helper to create App
utermApp :: Term -> Term -> Term
utermApp t1 t2 = TmFold utermType
                 (TmInr (TmInl (TmPair t1 t2)
                               (TySum (TyProd utermType utermType)
                                      utermType))
                        (TySum TyNat
                          (TySum (TyProd utermType utermType)
                                 utermType)))

-- Helper to create Lam
utermLam :: Term -> Term
utermLam body = TmFold utermType
                (TmInr (TmInr body
                             (TySum (TyProd utermType utermType)
                                    utermType))
                       (TySum TyNat
                         (TySum (TyProd utermType utermType)
                                utermType)))

-- 1. The identity function: λx. x (using de Bruijn index 0)
utermId :: Term
utermId = utermLam (utermVar TmZero)

-- 2. The self-application ω: λx. x x
utermOmega :: Term
utermOmega = utermLam (utermApp (utermVar TmZero) (utermVar TmZero))

-- 3. The diverging term Ω: (λx. x x)(λx. x x)
utermBigOmega :: Term
utermBigOmega = utermApp utermOmega utermOmega

-- 3.2 Typed Self-Application
-- SelfApp = μα. α → Nat

selfAppType :: Type
selfAppType = TyMu "α" (TyFun (TyVar "α") TyNat)

-- A well-typed version of λx. x x
-- omega : SelfApp
-- omega = λx:SelfApp. (unfold x) x
-- Then: fold omega : SelfApp
typedOmega :: Term
typedOmega = TmFold selfAppType
             (Lam "x" selfAppType
               (App (TmUnfold selfAppType (Var "x"))
                    (Var "x")))

-- This type-checks because:
-- - unfold : SelfApp → (SelfApp → Nat)
-- - x : SelfApp
-- - So (unfold x) x : Nat
-- The fold/unfold break the occurs check by introducing the indirection

-- ============================================================================
-- Exercise 4: Fixed Points and Recursion
-- ============================================================================

-- 4.1 General Recursion from μ Types
-- Fix A = μα. α → A

fixType :: Type -> Type
fixType a = TyMu "α" (TyFun (TyVar "α") a)

-- fix : (A → A) → A
-- For A = Nat, we have:
-- fix f = (λg. f (g g)) (λg. f (g g))
-- With types:
-- fix : (Nat → Nat) → Nat
fixNat :: Term
fixNat = Lam "f" (TyFun TyNat TyNat)
         (TmLet "g" (TmFold (fixType TyNat)
                      (Lam "x" (fixType TyNat)
                        (App (Var "f")
                          (App (TmUnfold (fixType TyNat) (Var "x"))
                               (Var "x")))))
           (App (TmUnfold (fixType TyNat) (Var "g"))
                (Var "g")))

-- Factorial using fix:
-- factorial = fix (λfac. λn. if (isZero n) then 1 else n * fac (pred n))
-- Simplified version showing the structure
factorial :: Term
factorial = App fixNat
            (Lam "fac" (TyFun TyNat TyNat)
              (Lam "n" TyNat
                (TmIf (TmIsZero (Var "n"))
                      (TmSucc TmZero)  -- 1
                      -- n * fac (pred n) - simplified
                      (App (Var "fac") (TmPred (Var "n"))))))

-- 4.2 Non-termination
-- Example: fix id where id : Nat → Nat
-- This creates an infinite loop: id (id (id ...))
-- The typed lambda calculus without μ types is strongly normalizing.
-- With μ types, we can write recursive functions that may not terminate,
-- because fold/unfold allow us to create circular definitions.

diverge :: Term
diverge = App fixNat (Lam "x" TyNat (Var "x"))

-- ============================================================================
-- Exercise 5: Type System Extensions
-- ============================================================================

-- 5.1 Positive and Negative Occurrences
-- In μα. α → α, the type variable α appears:
-- - Once on the left of → (negative)
-- - Once on the right of → (positive)
-- This is problematic because it can lead to logical inconsistencies.
-- Many systems require strictly positive occurrences only.

-- Example of why negative occurrences are bad:
-- Bad = μα. α → α
-- Then we can construct: bad : Bad → Bad
-- This looks innocent but can lead to paradoxes.

-- 5.2 Least vs Greatest Fixed Points
-- μα.T (least fixed point) - inductive types
--   - Finite data structures
--   - Can be eliminated by structural recursion
--   - Well-founded
--
-- να.T (greatest fixed point) - coinductive types
--   - Possibly infinite data structures
--   - Can be observed/deconstructed indefinitely
--   - May not be well-founded

-- List = μα. 1 + (Nat × α) contains only finite lists because:
-- - Every list is built by finitely many applications of fold
-- - Structural recursion on lists always terminates

-- Stream = να. Nat × α can contain infinite streams because:
-- - We can keep unfolding forever
-- - Observations (head, tail) are always productive

-- If we used ν for lists, we could have infinite lists
-- If we used μ for streams, we could only have finite "streams"

-- ============================================================================
-- Exercise 6: Implementation Challenges
-- ============================================================================

-- 6.1 Type Equality
-- T1 = μα. Nat × (Nat × α)  unfolds to: Nat × (Nat × (μα. Nat × (Nat × α)))
-- T2 = μβ. Nat × β          unfolds to: Nat × (μβ. Nat × β)
--
-- These are NOT equal in general. T1 has two Nats in each node, T2 has one.
--
-- For equi-recursive types, type equality requires checking if two recursive
-- types have the same infinite unfolding (regular tree equality).
-- This can be done by converting to finite automata and checking language equiv.

-- 6.2 Recursive Type Inference
-- Type inference for μ types is undecidable in general.
-- For: λx. x x
-- We need: x : τ where τ = τ → σ for some σ
-- This requires solving: τ = τ → σ
-- Which gives: τ = μα. α → σ
--
-- So we can infer recursive types, but:
-- - Requires constraint solving with recursive equations
-- - May need annotations to guide inference
-- - Not always a unique principal type

-- ============================================================================
-- Challenge Problems
-- ============================================================================

-- Challenge 1: Church-Encoded Lists with Types
-- Church encoding: List A = ∀R. (A → R → R) → R → R
-- μ encoding: List A = μα. Unit + (A × α)
--
-- Church encoding:
-- + Universal quantification gives parametricity
-- + No need for explicit fold/unfold
-- + Can be used in System F
-- - Less convenient for pattern matching
-- - Harder to reason about computationally
--
-- μ encoding:
-- + Direct representation of data structure
-- + Pattern matching is natural
-- + Clearer computational behavior
-- - Need explicit fold/unfold
-- - Requires μ types in the type system

-- Challenge 2: Nested Recursion
-- Bush = μα. Nat × List α where List β = μγ. Unit + (β × γ)
-- Fully expanded: Bush = μα. Nat × (μγ. Unit + (α × γ))

bushType :: Type
bushType = TyMu "α"
           (TyProd TyNat
             (TyMu "γ" (TySum TyUnit (TyProd (TyVar "α") (TyVar "γ")))))

-- Leaf constructor: leaf n = fold (n, fold (inl ()))
bushLeaf :: Term
bushLeaf = Lam "n" TyNat
           (TmFold bushType
             (TmPair (Var "n")
               (TmFold (TyMu "γ" (TySum TyUnit (TyProd bushType (TyVar "γ"))))
                 (TmInl TmUnit (TySum TyUnit (TyProd bushType
                   (TyMu "γ" (TySum TyUnit (TyProd bushType (TyVar "γ"))))))))))

-- Challenge 3: Mutual Recursion
-- Tree = Nat × Forest
-- Forest = List Tree
--
-- Encode as: TreeForest = μα. (Nat × List α) × List (Nat × List α)
-- Or more simply using a product:
-- TreeForest = μα. α₁ × α₂ where α₁ = Nat × α₂ and α₂ = List α₁
-- Encoded as: μα. (Nat × List α) × List (Nat × List α)

-- The key idea is to bundle mutually recursive types into a single product type
-- where each component can reference the whole μ-bound type.

mutualType :: Type
mutualType = TyMu "α"
             (TyProd
               -- Tree component: Nat × Forest
               (TyProd TyNat (TyMu "β" (TySum TyUnit (TyProd (TyVar "α") (TyVar "β")))))
               -- Forest component: List Tree (same as the list above)
               (TyMu "β" (TySum TyUnit (TyProd (TyVar "α") (TyVar "β")))))

-- ============================================================================
-- Test Suite
-- ============================================================================

-- Test type checking of various constructs
testLeaf :: Either TypeError Type
testLeaf = typeCheck leaf

testNode :: Either TypeError Type
testNode = typeCheck node

testTypedOmega :: Either TypeError Type
testTypedOmega = typeCheck typedOmega

testFixNat :: Either TypeError Type
testFixNat = typeCheck fixNat

testFactorial :: Either TypeError Type
testFactorial = typeCheck factorial

testUtermId :: Either TypeError Type
testUtermId = typeCheck utermId

-- Run all tests
runTests :: IO ()
runTests = do
  putStrLn "Chapter 15: Recursive Types - Solutions"
  putStrLn "==========================================="

  putStrLn "\nTest 1: leaf constructor"
  print testLeaf

  putStrLn "\nTest 2: node constructor"
  print testNode

  putStrLn "\nTest 3: typed omega (self-application)"
  print testTypedOmega

  putStrLn "\nTest 4: fixed-point combinator"
  print testFixNat

  putStrLn "\nTest 5: factorial"
  print testFactorial

  putStrLn "\nTest 6: untyped lambda term (identity)"
  print testUtermId

  putStrLn "\nAll tests complete!"
