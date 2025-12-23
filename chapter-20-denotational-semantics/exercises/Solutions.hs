{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import Domain
import Denotation
import qualified Data.Map.Strict as Map

-- ============================================================================
-- Exercise 1: Computing Denotations (Warm-up)
-- ============================================================================

-- Exercise 1a: [[λx. x]] ∅ (identity function)
--
-- Solution:
--   [[λx:A. x]] ∅
--   = λd ∈ [[A]]. [[x]][x↦d]    (by lambda rule)
--   = λd ∈ [[A]]. d              (by variable lookup)
--   = id_[[A]]                    (identity function on domain [[A]])
--
-- In our implementation:
ex1a :: Dom
ex1a = denoteClosed (Lam "x" TyNat (Var "x"))
-- Result: DFun (identity function)

-- Exercise 1b: [[(λx. suc x) 5]] ∅
--
-- Solution:
--   [[(λx:Nat. suc x) 5]] ∅
--   = [[λx:Nat. suc x]] ∅ ([[5]] ∅)           (by application rule)
--   = (λd. [[suc x]][x↦d]) ([[5]] ∅)          (by lambda rule)
--   = (λd. [[suc x]][x↦d]) (5)                (literal evaluates to 5)
--   = [[suc x]][x↦5]                          (apply function to 5)
--   = suc([[x]][x↦5])                         (by suc rule)
--   = suc(5)                                  (variable lookup)
--   = 6                                       (successor)
--
-- In our implementation:
ex1b :: Dom
ex1b = denoteClosed (App (Lam "x" TyNat (Suc (Var "x"))) (Suc (Suc (Suc (Suc (Suc Zero))))))
-- Result: DNat 6

-- Exercise 1c: [[let y = 3 in y + y]] ∅
--
-- Solution:
--   [[let y = 3 in y + y]] ∅
--   = [[y + y]][y↦[[3]]∅]                     (by let rule)
--   = [[y + y]][y↦3]                          (literal evaluates to 3)
--   = [[y]][y↦3] + [[y]][y↦3]                (by addition semantics)
--   = 3 + 3                                   (variable lookup)
--   = 6                                       (addition)
--
-- In our implementation (using NatRec for addition):
ex1c :: Dom
ex1c = denoteClosed (Let "y" (Suc (Suc (Suc Zero)))
                         (addTerm (Var "y") (Var "y")))
  where
    -- Addition using natrec: add m n = natrec m (λ_ acc. suc acc) n
    addTerm m n = NatRec m (Lam "_" TyNat (Lam "acc" TyNat (Suc (Var "acc")))) n
-- Result: DNat 6

-- Exercise 1d: [[if true then 0 else 1]] ∅
--
-- Solution:
--   [[if true then 0 else 1]] ∅
--   = cond([[true]]∅, [[0]]∅, [[1]]∅)         (by if rule)
--   = cond(true, 0, 1)                        (evaluate subterms)
--   = 0                                       (conditional selects then branch)
--
-- In our implementation:
ex1d :: Dom
ex1d = denoteClosed (If TmTrue Zero (Suc Zero))
-- Result: DNat 0

-- ============================================================================
-- Exercise 2: Flat Domain Drawing
-- ============================================================================

-- Flat domain structure:
--   - Single bottom element ⊥
--   - All defined values are incomparable (not ordered except with ⊥)
--
-- Exercise 2a: Bool = {⊥, true, false}
--
-- Hasse diagram:
--
--     true    false
--        \    /
--         \  /
--          ⊥
--
-- Ordering relation:
--   ⊥ ⊑ true
--   ⊥ ⊑ false
--   true ⊑ true
--   false ⊑ false
--   NOT: true ⊑ false or false ⊑ true
--
-- This is a flat domain: all defined values are maximal.

-- Exercise 2b: Nat = {⊥, 0, 1, 2, ...}
--
-- Hasse diagram:
--
--     0    1    2    3   ...
--      \   |   |    /
--       \  |   |   /
--        \ |   |  /
--         \|   | /
--          \ | |/
--           \||/
--            ⊥
--
-- Ordering relation:
--   ⊥ ⊑ n for all n
--   n ⊑ n for all n
--   NOT: n ⊑ m for distinct defined n, m
--
-- This is also a flat domain.

-- Exercise 2c: Color = {⊥, red, green, blue}
--
-- Hasse diagram:
--
--   red   green   blue
--     \    |     /
--      \   |    /
--       \  |   /
--        \ |  /
--         \| /
--          ⊥
--
-- Same structure as Bool but with three elements instead of two.

-- ============================================================================
-- Exercise 3: Function Domain Analysis
-- ============================================================================

-- Domain: Bool → Bool (continuous functions from Bool to Bool)
--
-- Exercise 3a: List all elements
--
-- A continuous function f : Bool → Bool is determined by:
--   f(⊥), f(true), f(false)
--
-- By continuity, we need: f(⊥) ⊑ f(true) and f(⊥) ⊑ f(false)
--
-- The 4 continuous functions are:
--
-- 1. ⊥_fun: the totally undefined function
--    ⊥_fun(⊥) = ⊥, ⊥_fun(true) = ⊥, ⊥_fun(false) = ⊥
--
-- 2. const_true: constantly true (lazy)
--    const_true(⊥) = true, const_true(true) = true, const_true(false) = true
--
-- 3. const_false: constantly false (lazy)
--    const_false(⊥) = false, const_false(true) = false, const_false(false) = false
--
-- 4. id: identity function (strict)
--    id(⊥) = ⊥, id(true) = true, id(false) = false
--
-- Wait, let me reconsider. For continuity, f(⊥) ⊑ f(b) for any b.
-- So f(⊥) can only be ⊥.
--
-- Actually, the four functions are:
-- 1. λx. ⊥ (strict bottom)
-- 2. λx. true (constant true)
-- 3. λx. false (constant false)
-- 4. λx. x (identity)

-- Exercise 3b: Draw the partial order
--
--      const_true    id    const_false
--           \        |         /
--            \       |        /
--             \      |       /
--              \     |      /
--               \    |     /
--                 ⊥_fun
--
-- Ordering:
--   ⊥_fun ⊑ f for all f (least element)
--   f ⊑ f for all f (reflexivity)
--   No other orderings (maximal elements are incomparable)

-- Exercise 3c: Least element
--
-- The least element is ⊥_fun = λx. ⊥ (the strict undefined function)
-- This is the function that returns ⊥ for all inputs.

-- Examples in our implementation:
ex3_bottom_fun :: Dom
ex3_bottom_fun = DFun (\_ -> DBottom)

ex3_const_true :: Dom
ex3_const_true = DFun (\_ -> DBool True)

ex3_const_false :: Dom
ex3_const_false = DFun (\_ -> DBool False)

ex3_id :: Dom
ex3_id = DFun $ \x -> x

-- ============================================================================
-- Exercise 4: Fixed Point Iteration
-- ============================================================================

-- Function: f = λg. λn. if iszero n then 1 else n * g(n-1)
--
-- This is the functional for factorial!

-- Exercise 4a: f⁰(⊥) - what is ⊥ in the function domain?
--
-- In the function domain Nat → Nat, ⊥ is the function that returns ⊥ for all inputs.
-- So: f⁰(⊥) = ⊥ = λn. ⊥
--
-- In our implementation:
ex4a :: Dom
ex4a = fixN 0 factF_dom
  where
    factF_dom = \g -> DFun $ \n -> case n of
      DNat 0 -> DNat 1
      DNat k -> case domApp g (DNat (k - 1)) of
        DNat m -> DNat (k * m)
        _ -> DBottom
      _ -> DBottom
-- Result: DBottom

-- Exercise 4b: f¹(⊥) - apply f to ⊥
--
-- f¹(⊥) = f(⊥) = f(λn. ⊥)
--       = λn. if iszero n then 1 else n * ⊥(n-1)
--       = λn. if iszero n then 1 else ⊥
--
-- This function:
--   - Returns 1 when n = 0
--   - Returns ⊥ for all n > 0
--
-- In our implementation:
ex4b :: Dom
ex4b = fixN 1 factF_dom
  where
    factF_dom = \g -> DFun $ \n -> case n of
      DNat 0 -> DNat 1
      DNat k -> case domApp g (DNat (k - 1)) of
        DNat m -> DNat (k * m)
        _ -> DBottom
      _ -> DBottom
-- Result: DFun that works for 0 only

-- Exercise 4c: f²(⊥)
--
-- f²(⊥) = f(f(⊥))
--       = f(λn. if iszero n then 1 else ⊥)
--       = λn. if iszero n then 1 else n * (f(⊥))(n-1)
--       = λn. if iszero n then 1 else n * (if iszero(n-1) then 1 else ⊥)
--
-- This function:
--   - Returns 1 when n = 0
--   - Returns 1 when n = 1 (since 1 * 1 = 1)
--   - Returns ⊥ for n > 1
--
-- In our implementation:
ex4c :: Dom
ex4c = fixN 2 factF_dom
  where
    factF_dom = \g -> DFun $ \n -> case n of
      DNat 0 -> DNat 1
      DNat k -> case domApp g (DNat (k - 1)) of
        DNat m -> DNat (k * m)
        _ -> DBottom
      _ -> DBottom
-- Result: DFun that works for 0 and 1

-- Exercise 4d: f³(⊥)
--
-- f³(⊥) = f(f²(⊥))
--
-- This function:
--   - Returns 1 when n = 0
--   - Returns 1 when n = 1
--   - Returns 2 when n = 2 (since 2 * 1 = 2)
--   - Returns ⊥ for n > 2
--
-- In our implementation:
ex4d :: Dom
ex4d = fixN 3 factF_dom
  where
    factF_dom = \g -> DFun $ \n -> case n of
      DNat 0 -> DNat 1
      DNat k -> case domApp g (DNat (k - 1)) of
        DNat m -> DNat (k * m)
        _ -> DBottom
      _ -> DBottom
-- Result: DFun that works for 0, 1, and 2

-- Pattern: f^n(⊥) computes factorial correctly for inputs 0..n-1
-- and returns ⊥ for inputs ≥ n.
--
-- The limit: fix(f) = ⊔ₙ f^n(⊥) computes factorial for ALL inputs!

-- ============================================================================
-- Exercise 5: Continuity
-- ============================================================================

-- A function f : D → E is continuous if for all directed sets S ⊆ D:
--   f(⊔S) = ⊔{f(s) | s ∈ S}

-- Exercise 5a: λn. n + 1 on flat Nat
--
-- Proof that it's continuous:
--   For any directed set S ⊆ Nat:
--   - If S = {⊥}, then ⊔S = ⊥ and f(⊔S) = f(⊥) = ⊥
--     Also, {f(s) | s ∈ S} = {⊥}, so ⊔{f(s)} = ⊥
--     Thus f(⊔S) = ⊔{f(s)}
--   - If S contains a defined value n, then ⊔S = n (flat domain!)
--     f(⊔S) = f(n) = n + 1
--     {f(s) | s ∈ S} = {⊥, n+1}, so ⊔{f(s)} = n + 1
--     Thus f(⊔S) = ⊔{f(s)}
--
-- Therefore λn. n + 1 is continuous.

-- Exercise 5b: λb. if b then 0 else 1 on flat Bool
--
-- This is continuous by similar reasoning.
-- The conditional is strict in the condition, so it preserves directed suprema.

-- Exercise 5c: Parallel OR
--
-- por(⊥, true) = true
-- por(true, ⊥) = true
-- por(false, false) = false
--
-- This is NOT continuous!
--
-- Counterexample:
--   Consider S = {⊥} (a directed set)
--   ⊔S = ⊥
--   por(⊔S, true) = por(⊥, true) = true
--
--   But {por(s, true) | s ∈ S} = {por(⊥, true)} = {true}
--   ⊔{por(s, true)} = true
--
-- Wait, this works. Let me think more carefully.
--
-- Actually, parallel OR is not continuous because it's not monotone in its first argument
-- when the second is true:
--   por(⊥, true) = true but we'd expect it to be ⊥ for a strict function.
--
-- The issue is that por doesn't respect the ordering in a way that makes it continuous.
-- It's detecting information from both arguments simultaneously, which violates
-- sequential computation.

-- ============================================================================
-- Exercise 6: Strict vs. Non-strict Semantics
-- ============================================================================

-- Exercise 6a: Give full semantic definitions

-- Strict conditional:
--   [[if c then t else e]]ρ =
--     if [[c]]ρ = ⊥ then ⊥
--     else if [[c]]ρ = true then [[t]]ρ
--     else [[e]]ρ
--
-- Non-strict conditional:
--   [[if c then t else e]]ρ =
--     if [[c]]ρ = true then [[t]]ρ
--     else if [[c]]ρ = false then [[e]]ρ
--     else ⊥

-- Exercise 6b: [[if ⊥ then 0 else Ω]] under each
--
-- Strict: [[if ⊥ then 0 else Ω]] = ⊥ (condition is ⊥, so whole thing is ⊥)
-- Non-strict: [[if ⊥ then 0 else Ω]] = ⊥ (condition is ⊥, neither branch is taken)
--
-- They agree in this case!
--
-- Better example: [[if true then 0 else Ω]]
-- Both: = 0 (only evaluate then branch)
--
-- Key difference: [[if false then Ω else 0]]
-- Strict: = 0 (condition is defined, evaluate else branch)
-- Non-strict: = 0 (same)
--
-- Actually for conditionals, strictness in the condition is standard.
-- The difference is in the branches:
--   - Lazy languages (Haskell): only evaluate chosen branch
--   - Strict languages (ML): might evaluate both, but semantically it's the same

-- Exercise 6c: Which does each language use?
--
-- Haskell: Lazy/non-strict - only evaluates chosen branch
-- Standard ML: Strict in values but conditionals are still lazy in branches
--
-- Both use the same denotational semantics for conditionals!
-- The difference is in function application and let bindings.

-- ============================================================================
-- Exercise 7: Adding Products
-- ============================================================================

-- Exercise 7a: Define [[A × B]]
--
-- The product domain is:
--   [[A × B]] = [[A]] × [[B]] = {(a, b) | a ∈ [[A]], b ∈ [[B]]} ∪ {⊥}
--
-- More precisely, it's the lifted product with ordering:
--   ⊥ ⊑ (a, b) for all a, b
--   (a₁, b₁) ⊑ (a₂, b₂) iff a₁ ⊑ a₂ and b₁ ⊑ b₂

-- Exercise 7b: Denotation of pair formation
--
-- [[(e1, e2)]]ρ = ([[e1]]ρ, [[e2]]ρ)
--
-- This is strict in both components:
--   If [[e1]]ρ = ⊥ or [[e2]]ρ = ⊥, then the pair is ⊥.

-- Exercise 7c: Denotations of projections
--
-- [[fst e]]ρ = π₁([[e]]ρ)
--   where π₁((a, b)) = a and π₁(⊥) = ⊥
--
-- [[snd e]]ρ = π₂([[e]]ρ)
--   where π₂((a, b)) = b and π₂(⊥) = ⊥

-- Exercise 7d: Evaluate specific cases
--
-- [[fst ⊥]] = π₁(⊥) = ⊥
--   (bottom pair gives bottom)
--
-- [[fst (⊥, 0)]] = π₁((⊥, 0)) = ⊥
--   (if first component is ⊥, projection gives ⊥)
--
-- This shows pairs are strict in their components!

-- ============================================================================
-- Exercise 8: Recursive Types
-- ============================================================================

-- Exercise 8a: Domain equation for List
--
-- List = 1 + (Nat × List)
--
-- Domain equation:
--   [[List]] = [[1]] + ([[Nat]] × [[List]])
--   [[List]] = {★} + (ℕ_⊥ × [[List]])
--
-- This is a recursive domain equation!

-- Exercise 8b: Use fixed points to show this has a solution
--
-- Define a functional F on domains:
--   F(D) = {★} + (ℕ_⊥ × D)
--
-- We want to find D such that D = F(D), i.e., a fixed point.
--
-- By domain theory, F is a continuous function on the space of domains,
-- so by the fixed point theorem:
--   [[List]] = fix(F) = ⊔ₙ Fⁿ(⊥_Domain)
--
-- The approximation chain:
--   D₀ = ⊥_Domain (empty domain)
--   D₁ = F(⊥) = {★} + (ℕ_⊥ × ⊥) = {nil}
--   D₂ = F(D₁) = {★} + (ℕ_⊥ × {nil}) = {nil, cons(n, nil) | n ∈ ℕ}
--   D₃ = F(D₂) = {nil, cons(n, nil), cons(n, cons(m, nil)) | n, m ∈ ℕ}
--   ...
--
-- The limit is all finite lists plus infinite lists and partial lists!

-- Exercise 8c: What does ⊥ : List represent?
--
-- ⊥ represents a completely undefined list - a computation that doesn't
-- terminate or provide any information about the list.

-- Exercise 8d: What does inl () : List represent?
--
-- inl () represents the empty list (nil).
-- The left injection corresponds to the "1" part of "1 + (Nat × List)".

-- ============================================================================
-- Examples: Semantic Domains and Denotation Functions
-- ============================================================================

-- Example 1: Simple arithmetic
arithExample :: Dom
arithExample = denoteClosed (Suc (Suc (Suc Zero)))
-- Result: DNat 3

-- Example 2: Function application
appExample :: Dom
appExample = denoteClosed (App (Lam "x" TyNat (Suc (Var "x"))) (Suc (Suc Zero)))
-- Result: DNat 3

-- Example 3: Conditional
condExample :: Dom
condExample = denoteClosed (If TmTrue (Suc Zero) Zero)
-- Result: DNat 1

-- Example 4: Let binding
letExample :: Dom
letExample = denoteClosed (Let "x" (Suc (Suc Zero)) (Suc (Var "x")))
-- Result: DNat 3

-- Example 5: Fixed point - factorial
-- Using the built-in factorial from Denotation module
factExample :: Dom
factExample = factorialDen 5
-- Result: DNat 120

-- Example 6: Fixed point - fibonacci
fibExample :: Dom
fibExample = fibonacciDen 10
-- Result: DNat 55

-- Example 7: Explicit bottom
bottomExample :: Dom
bottomExample = denoteClosed (Bottom TyNat)
-- Result: DBottom

-- Example 8: IsZero predicate
isZeroExample1 :: Dom
isZeroExample1 = denoteClosed (IsZero Zero)
-- Result: DBool True

isZeroExample2 :: Dom
isZeroExample2 = denoteClosed (IsZero (Suc Zero))
-- Result: DBool False

-- Example 9: Predecessor
predExample1 :: Dom
predExample1 = denoteClosed (Pred (Suc (Suc Zero)))
-- Result: DNat 1

predExample2 :: Dom
predExample2 = denoteClosed (Pred Zero)
-- Result: DNat 0 (pred of 0 is 0)

-- Example 10: Higher-order function
-- Identity function applied to itself
higherOrderExample :: Dom
higherOrderExample = denoteClosed
  (App (Lam "f" (TyArr TyNat TyNat) (Var "f"))
       (Lam "x" TyNat (Var "x")))
-- Result: DFun (identity function)

-- ============================================================================
-- Advanced Examples: Fixed Point Iteration
-- ============================================================================

-- Helper to create natural number literals
natLit :: Integer -> Term
natLit 0 = Zero
natLit n = Suc (natLit (n - 1))

-- Addition using fix
addFix :: Term
addFix = Fix (Lam "add" (TyArr TyNat (TyArr TyNat TyNat))
                 (Lam "m" TyNat
                    (Lam "n" TyNat
                       (If (IsZero (Var "m"))
                           (Var "n")
                           (Suc (App (App (Var "add") (Pred (Var "m"))) (Var "n")))))))

-- Test addition
testAdd :: Dom
testAdd = denoteClosed (App (App addFix (natLit 3)) (natLit 4))
-- Result: DNat 7

-- Multiplication using fix
multFix :: Term
multFix = Fix (Lam "mult" (TyArr TyNat (TyArr TyNat TyNat))
                  (Lam "m" TyNat
                     (Lam "n" TyNat
                        (If (IsZero (Var "m"))
                            Zero
                            (App (App addFix (Var "n"))
                                 (App (App (Var "mult") (Pred (Var "m"))) (Var "n")))))))

-- Test multiplication
testMult :: Dom
testMult = denoteClosed (App (App multFix (natLit 3)) (natLit 4))
-- Result: DNat 12

-- ============================================================================
-- Test Suite
-- ============================================================================

-- Run all examples
runExamples :: IO ()
runExamples = do
  putStrLn "Chapter 20: Denotational Semantics - Solutions"
  putStrLn "============================================="

  putStrLn "\nExercise 1: Computing Denotations"
  putStrLn "1a. [[λx. x]]: " >> print ex1a
  putStrLn "1b. [[(λx. suc x) 5]]: " >> print ex1b
  putStrLn "1c. [[let y = 3 in y + y]]: " >> print ex1c
  putStrLn "1d. [[if true then 0 else 1]]: " >> print ex1d

  putStrLn "\nExercise 4: Fixed Point Iteration"
  putStrLn "4a. f⁰(⊥): " >> print ex4a
  putStrLn "4b. f¹(⊥): " >> print ex4b
  putStrLn "4c. f²(⊥): " >> print ex4c
  putStrLn "4d. f³(⊥): " >> print ex4d

  putStrLn "\nExamples: Semantic Evaluation"
  putStrLn "Arithmetic: " >> print arithExample
  putStrLn "Application: " >> print appExample
  putStrLn "Conditional: " >> print condExample
  putStrLn "Let binding: " >> print letExample
  putStrLn "Factorial(5): " >> print factExample
  putStrLn "Fibonacci(10): " >> print fibExample
  putStrLn "Bottom: " >> print bottomExample
  putStrLn "IsZero(0): " >> print isZeroExample1
  putStrLn "IsZero(1): " >> print isZeroExample2
  putStrLn "Pred(2): " >> print predExample1
  putStrLn "Pred(0): " >> print predExample2

  putStrLn "\nAdvanced: Fixed Point Examples"
  putStrLn "Addition 3+4: " >> print testAdd
  putStrLn "Multiplication 3*4: " >> print testMult

  putStrLn "\nAll solutions demonstrated!"

-- ============================================================================
-- Summary of Key Insights
-- ============================================================================

-- Key insight 1: Denotational semantics maps syntax to mathematical objects
--   Terms → Domain elements
--   Types → Domains (CPOs)
--   Programs → Functions between domains

-- Key insight 2: Domains are CPOs (Complete Partial Orders)
--   - Have a least element ⊥ (undefined/non-terminating)
--   - Directed sets have suprema (limits)
--   - Model approximation: d₁ ⊑ d₂ means "d₁ is less defined than d₂"

-- Key insight 3: Fixed points model recursion
--   fix f = ⊔ₙ fⁿ(⊥)
--   The least fixed point is the supremum of the approximation chain
--   This gives meaning to recursive definitions

-- Key insight 4: Continuity is essential
--   Continuous functions preserve directed suprema
--   Ensures that limits of computations are well-behaved
--   Only continuous functions have fixed points in domain theory

-- Key insight 5: Haskell's laziness embodies domain theory
--   undefined corresponds to ⊥
--   Lazy evaluation corresponds to continuous functions
--   fix is built into the language

-- Key insight 6: Flat domains model base types
--   ⊥ and a set of maximal, incomparable elements
--   Nat, Bool, etc. are flat domains
--   Function spaces are NOT flat (have internal structure)
