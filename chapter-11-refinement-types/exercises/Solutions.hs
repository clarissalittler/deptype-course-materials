{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Set as Set

-- ============================================================================
-- Exercise 1: Understanding Refinements
-- ============================================================================

-- Exercise 1.1: {x: Nat | x == 0}
-- This type contains only the value 0.
-- It's the singleton type for zero.

natEqZero :: Type
natEqZero = TyRefine "x" (TyBase TyNat) (PComp OpEq (PAVar "x") (PALit 0))

-- Exercise 1.2: {x: Nat | x > 0}
-- This type contains all positive natural numbers (1, 2, 3, ...)
-- Also known as the "positive naturals" or Nat+

natGtZero :: Type
natGtZero = TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 0))

-- Exercise 1.3: {x: Nat | x >= 0 && x < 10}
-- This type contains naturals in the range [0, 10): 0, 1, 2, ..., 9
-- A bounded natural type (digits)

natBounded :: Type
natBounded = TyRefine "x" (TyBase TyNat)
  (PAnd (PComp OpGe (PAVar "x") (PALit 0))
        (PComp OpLt (PAVar "x") (PALit 10)))

-- Exercise 1.4: {x: Bool | x == true}
-- This type contains only the value true.
-- It's the singleton type for true (also called "Top" in logic)

boolTrue :: Type
boolTrue = TyRefine "x" (TyBase TyBool) (PComp OpEq (PAVar "x") (PALit 1))

-- Exercise 1.5: {x: Nat | x > 5 && x < 3}
-- This type is EMPTY - no value can be both greater than 5 and less than 3.
-- This is an uninhabited type (like Empty/Bottom)

natEmpty :: Type
natEmpty = TyRefine "x" (TyBase TyNat)
  (PAnd (PComp OpGt (PAVar "x") (PALit 5))
        (PComp OpLt (PAVar "x") (PALit 3)))

-- ============================================================================
-- Exercise 2: Subtyping Relationships
-- ============================================================================

-- Exercise 2.1: {x: Nat | x > 5} <: {x: Nat | x > 0}
-- YES - this is valid!
-- Reason: If x > 5, then x > 0 (the predicate is stronger/more restrictive)
-- Subtyping for refinements: {x: T | φ} <: {x: T | ψ} iff φ => ψ

testSubtype1 :: Bool
testSubtype1 = isSubtype emptyContext natGtFive natGtZero
  where
    natGtFive = TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 5))

-- Exercise 2.2: {x: Nat | x > 0} <: {x: Nat | x > 5}
-- NO - this is NOT valid!
-- Reason: Not all x > 0 satisfy x > 5 (e.g., x = 3)
-- The implication does not hold: (x > 0) =/=> (x > 5)

testSubtype2 :: Bool
testSubtype2 = isSubtype emptyContext natGtZero natGtFive
  where
    natGtFive = TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 5))

-- Exercise 2.3: {x: Nat | x > 0} <: Nat
-- YES - this is valid!
-- Reason: We can always forget/drop refinements (subsumption)
-- A refined type is a subtype of its base type

testSubtype3 :: Bool
testSubtype3 = isSubtype emptyContext natGtZero (TyBase TyNat)

-- Exercise 2.4: Nat <: {x: Nat | x >= 0}
-- YES - this is valid!
-- Reason: All natural numbers are >= 0, so the predicate is trivially satisfied
-- This is a "trivial" refinement that adds no information

testSubtype4 :: Bool
testSubtype4 = isSubtype emptyContext (TyBase TyNat) natGeZero
  where
    natGeZero = TyRefine "x" (TyBase TyNat) (PComp OpGe (PAVar "x") (PALit 0))

-- Exercise 2.5: {x: Nat | x == 0} <: {x: Nat | x <= 0}
-- YES - this is valid!
-- Reason: If x == 0, then x <= 0
-- The singleton type for 0 is a subtype of "non-positive naturals"

testSubtype5 :: Bool
testSubtype5 = isSubtype emptyContext natEqZero natLeZero
  where
    natLeZero = TyRefine "x" (TyBase TyNat) (PComp OpLe (PAVar "x") (PALit 0))

-- ============================================================================
-- Exercise 3: Type Checking
-- ============================================================================

-- Exercise 3.1: λx : {n: Nat | n > 0}. pred x
-- This IS well-typed!
-- - Input: positive natural (n > 0)
-- - Output: Nat (predecessor of a positive nat)
-- Type: {n: Nat | n > 0} -> Nat

safePred :: Term
safePred = Lam "x" natGtZero (TmPred (Var "x"))

-- Exercise 3.2: λx : Nat. (x : {n: Nat | n >= 0})
-- This IS well-typed!
-- - Input: any Nat
-- - Ascription checks that x satisfies n >= 0, which is trivially true
-- Type: Nat -> {n: Nat | n >= 0}

trivialRefine :: Term
trivialRefine = Lam "x" (TyBase TyNat)
  (TmAscribe (Var "x")
    (TyRefine "n" (TyBase TyNat) (PComp OpGe (PAVar "n") (PALit 0))))

-- Exercise 3.3: λx : {n: Nat | n > 0}. if iszero x then 0 else x
-- This is ILL-TYPED as written!
-- Reason: If x : {n: Nat | n > 0}, then x > 0, so iszero x is always false
-- The "then" branch is dead code, but more importantly:
-- - In the "then" branch, we'd return 0 with type {n: Nat | n == 0}
-- - In the "else" branch, we'd return x with type {n: Nat | n > 0}
-- - These don't have a common supertype easily
--
-- However, with path sensitivity, this COULD type check:
-- - In then branch: x : {n: Nat | n > 0 && n == 0} (contradiction!)
-- - The then branch is unreachable, so we can give it any type

pathSensitiveExample :: Term
pathSensitiveExample = Lam "x" natGtZero
  (TmIf (TmIsZero (Var "x"))
    TmZero
    (Var "x"))

-- Exercise 3.4: let x = 5 in (x : {n: Nat | n > 0})
-- This IS well-typed!
-- - x is bound to literal 5
-- - We can refine x to have type {n: Nat | n == 5}
-- - {n: Nat | n == 5} <: {n: Nat | n > 0} because 5 > 0
-- Type: {n: Nat | n > 0}

literalRefinement :: Term
literalRefinement = TmLet "x"
  (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))))
  (TmAscribe (Var "x") natGtZero)

-- ============================================================================
-- Exercise 4: Path Sensitivity
-- ============================================================================

-- Path-sensitive typing for if-then-else:
--
-- λx : Nat.
--   if iszero x
--   then (0 : {n: Nat | n == 0})
--   else (x : {n: Nat | n > 0})
--
-- Path sensitivity helps by:
--
-- In the THEN branch:
-- - Path condition: iszero x == true, i.e., x == 0
-- - We know: x : {n: Nat | n == 0}
-- - So we can safely ascribe 0 : {n: Nat | n == 0}
--
-- In the ELSE branch:
-- - Path condition: iszero x == false, i.e., x != 0, i.e., x > 0 (for Nat)
-- - We know: x : {n: Nat | n > 0}
-- - So we can safely ascribe x : {n: Nat | n > 0}
--
-- Result type: Join of both branches
-- - Both branches produce Nat (after dropping refinements)
-- - Or we could use: {n: Nat | n >= 0} as the join

pathSensitiveIf :: Term
pathSensitiveIf = Lam "x" (TyBase TyNat)
  (TmIf (TmIsZero (Var "x"))
    (TmAscribe TmZero natEqZero)
    (TmAscribe (Var "x") natGtZero))

-- ============================================================================
-- Exercise 5: Implement Positive Division
-- ============================================================================

-- Division that's safe because denominator is positive:
-- div : (n: Nat, d: {x: Nat | x > 0}) -> Nat
--
-- The refinement prevents division by zero at compile time!
-- We can't call div with 0 as the second argument.

-- Type for safe division
divType :: Type
divType = TyFun "n" (TyBase TyNat)
  (TyFun "d" natGtZero (TyBase TyNat))

-- Implementation (simplified - we don't have actual division in the language)
-- We'd need to add a TmDiv constructor to implement this properly
-- For now, this is a conceptual example showing the type

safeDiv :: Term
safeDiv = Lam "n" (TyBase TyNat)
  (Lam "d" natGtZero
    -- In a real implementation, this would perform division
    -- For now, just return the numerator
    (Var "n"))

-- Example usage:
-- safeDiv 10 5        -- OK: 5 > 0
-- safeDiv 10 0        -- TYPE ERROR: can't prove 0 > 0
-- safeDiv 10 (succ 0) -- OK: succ 0 = 1 > 0

exampleDivGood :: Term
exampleDivGood = App (App safeDiv (TmSucc (TmSucc TmZero)))
  (TmSucc TmZero)  -- 1 > 0

-- ============================================================================
-- Exercise 6: Array Bounds Checking
-- ============================================================================

-- Array types with length refinements:
-- type Array n a = {a: Array a | length a == n}
--
-- get : (i: Nat, a: Array n a, {_: Unit | i < n}) -> a
-- set : (i: Nat, a: Array n a, {_: Unit | i < n}, v: a) -> Array n a
--
-- How refinements help:
-- 1. The array type tracks its length in the type
-- 2. The get/set operations require a proof that i < n
-- 3. Out-of-bounds access becomes a TYPE ERROR, not a runtime error!
--
-- Example:
--   let arr = makeArray 10 in    -- arr : Array 10 a
--   get 5 arr                     -- OK: can prove 5 < 10
--   get 15 arr                    -- TYPE ERROR: can't prove 15 < 10

-- Since we don't have arrays in our language, here's a conceptual definition:

-- Type for an array of length n
-- arrayType :: Int -> Type
-- arrayType n = TyRefine "a" (TyBase (TyArray TyNat))
--   (PComp OpEq (PAVar "length_a") (PALit n))

-- Type for bounds-checked get
-- getType : forall n. (i: Nat, a: Array n, {_: Unit | i < n}) -> Nat
-- This would require dependent types to properly express

-- The key insight is that refinements allow static bounds checking!

-- ============================================================================
-- Exercise 7: Extend the Predicate Language
-- ============================================================================

-- To add full multiplication to predicates:
--
-- 1. Extend PArith:
--    data PArith = ... | PAMulFull PArith PArith
--
-- 2. Update substitution - already works compositionally
--
-- 3. Update validity checker - THIS IS THE PROBLEM!
--
-- Trade-offs:
--
-- PROS of full multiplication:
-- - Can express more properties (e.g., "x is even" = ∃k. x = 2*k)
-- - More natural for expressing array/matrix operations
-- - Can reason about polynomial equations
--
-- CONS of full multiplication:
-- - Makes validity UNDECIDABLE (by reduction to Diophantine equations)
-- - Type checking may not terminate
-- - Need SMT solver or incomplete heuristics
-- - Performance degradation
--
-- Current design (PAMul Int PArith) keeps us in linear arithmetic,
-- which is decidable via SMT solvers or Fourier-Motzkin elimination

-- Example of what we could express with full multiplication:
-- {x: Nat | ∃k. x = 2 * k}  -- even numbers
-- {x: Nat | x * x < 100}     -- numbers whose square is less than 100

-- ============================================================================
-- Exercise 8: Implement Predicate Simplification
-- ============================================================================

-- Simplification rules for predicates
simplify :: Pred -> Pred
simplify = \case
  -- Logical simplifications
  PAnd PTrue p -> simplify p
  PAnd p PTrue -> simplify p
  PAnd PFalse _ -> PFalse
  PAnd _ PFalse -> PFalse
  PAnd p1 p2 ->
    case (simplify p1, simplify p2) of
      (PTrue, p) -> p
      (p, PTrue) -> p
      (PFalse, _) -> PFalse
      (_, PFalse) -> PFalse
      (p1', p2') | p1' == p2' -> p1'  -- p && p = p (idempotence)
      (p1', p2') -> PAnd p1' p2'

  POr PTrue _ -> PTrue
  POr _ PTrue -> PTrue
  POr PFalse p -> simplify p
  POr p PFalse -> simplify p
  POr p1 p2 ->
    case (simplify p1, simplify p2) of
      (PTrue, _) -> PTrue
      (_, PTrue) -> PTrue
      (PFalse, p) -> p
      (p, PFalse) -> p
      (p1', p2') | p1' == p2' -> p1'  -- p || p = p (idempotence)
      (p1', p2') -> POr p1' p2'

  -- Double negation
  PNot (PNot p) -> simplify p
  PNot PTrue -> PFalse
  PNot PFalse -> PTrue
  PNot p -> PNot (simplify p)

  -- Implication
  PImpl PFalse _ -> PTrue  -- false implies anything
  PImpl _ PTrue -> PTrue   -- anything implies true
  PImpl PTrue p -> simplify p  -- true implies p = p
  PImpl p PFalse -> PNot (simplify p)  -- p implies false = not p
  PImpl p1 p2 -> PImpl (simplify p1) (simplify p2)

  -- Comparison simplifications
  PComp OpEq a1 a2
    | a1 == a2 -> PTrue  -- x == x is always true
    | otherwise -> PComp OpEq (simplifyArith a1) (simplifyArith a2)

  PComp OpNeq a1 a2
    | a1 == a2 -> PFalse  -- x != x is always false
    | otherwise -> PComp OpNeq (simplifyArith a1) (simplifyArith a2)

  PComp OpLt a1 a2
    | a1 == a2 -> PFalse  -- x < x is always false
    | otherwise -> PComp OpLt (simplifyArith a1) (simplifyArith a2)

  PComp OpLe a1 a2
    | a1 == a2 -> PTrue  -- x <= x is always true
    | otherwise -> PComp OpLe (simplifyArith a1) (simplifyArith a2)

  PComp OpGt a1 a2
    | a1 == a2 -> PFalse  -- x > x is always false
    | otherwise -> PComp OpGt (simplifyArith a1) (simplifyArith a2)

  PComp OpGe a1 a2
    | a1 == a2 -> PTrue  -- x >= x is always true
    | otherwise -> PComp OpGe (simplifyArith a1) (simplifyArith a2)

  -- Base cases
  p@PTrue -> p
  p@PFalse -> p
  p@(PVar _) -> p

-- Simplify arithmetic expressions
simplifyArith :: PArith -> PArith
simplifyArith = \case
  PAAdd (PALit 0) a -> simplifyArith a  -- 0 + a = a
  PAAdd a (PALit 0) -> simplifyArith a  -- a + 0 = a
  PAAdd (PALit n1) (PALit n2) -> PALit (n1 + n2)  -- constant folding
  PAAdd a1 a2 -> PAAdd (simplifyArith a1) (simplifyArith a2)

  PASub a (PALit 0) -> simplifyArith a  -- a - 0 = a
  PASub (PALit n1) (PALit n2) -> PALit (n1 - n2)  -- constant folding
  PASub a1 a2 | a1 == a2 -> PALit 0  -- a - a = 0
  PASub a1 a2 -> PASub (simplifyArith a1) (simplifyArith a2)

  PAMul 0 _ -> PALit 0  -- 0 * a = 0
  PAMul 1 a -> simplifyArith a  -- 1 * a = a
  PAMul n (PALit m) -> PALit (n * m)  -- constant folding
  PAMul n a -> PAMul n (simplifyArith a)

  a@(PALit _) -> a
  a@(PAVar _) -> a

-- Test simplification
testSimplify1 :: Pred
testSimplify1 = simplify (PAnd PTrue (PComp OpEq (PAVar "x") (PALit 5)))
-- Result: PComp OpEq (PAVar "x") (PALit 5)

testSimplify2 :: Pred
testSimplify2 = simplify (PNot (PNot (PVar "x")))
-- Result: PVar "x"

testSimplify3 :: Pred
testSimplify3 = simplify (PComp OpEq (PAVar "x") (PAVar "x"))
-- Result: PTrue

-- ============================================================================
-- Example Programs and Tests
-- ============================================================================

-- Example 1: Absolute value that returns a non-negative number
-- abs : Nat -> {n: Nat | n >= 0}
absValue :: Term
absValue = Lam "x" (TyBase TyNat)
  (TmAscribe (Var "x")
    (TyRefine "n" (TyBase TyNat) (PComp OpGe (PAVar "n") (PALit 0))))

-- Example 2: Maximum of two naturals (always >= both inputs)
-- max : (x: Nat, y: Nat) -> {n: Nat | n >= x && n >= y}
maxType :: Type
maxType = TyFun "x" (TyBase TyNat)
  (TyFun "y" (TyBase TyNat)
    (TyRefine "n" (TyBase TyNat)
      (PAnd (PComp OpGe (PAVar "n") (PAVar "x"))
            (PComp OpGe (PAVar "n") (PAVar "y")))))

-- Example 3: Increment always produces a positive natural
-- incr : Nat -> {n: Nat | n > 0}
increment :: Term
increment = Lam "x" (TyBase TyNat)
  (TmAscribe (TmSucc (Var "x")) natGtZero)

-- Example 4: Decrement of positive natural stays natural
-- decr : {x: Nat | x > 0} -> Nat
decrement :: Term
decrement = Lam "x" natGtZero
  (TmPred (Var "x"))

-- Example 5: Subtyping in action - using specific type in general context
-- id : Nat -> Nat
-- id 5 : {n: Nat | n == 5} can be used where Nat is expected
identityNat :: Term
identityNat = Lam "x" (TyBase TyNat) (Var "x")

-- Apply identity to a refined value
testSubtyping :: Term
testSubtyping = App identityNat
  (TmAscribe (TmSucc TmZero) natGtZero)

-- ============================================================================
-- Test Suite
-- ============================================================================

-- Run basic tests
testSolutions :: IO ()
testSolutions = do
  putStrLn "Testing Chapter 11 Solutions"
  putStrLn "============================="

  putStrLn "\n1. Subtyping tests:"
  putStrLn $ "   {x > 5} <: {x > 0}: " ++ show testSubtype1
  putStrLn $ "   {x > 0} <: {x > 5}: " ++ show testSubtype2
  putStrLn $ "   {x > 0} <: Nat: " ++ show testSubtype3

  putStrLn "\n2. Type checking safePred:"
  print $ typeCheck safePred

  putStrLn "\n3. Type checking increment:"
  print $ typeCheck increment

  putStrLn "\n4. Type checking decrement:"
  print $ typeCheck decrement

  putStrLn "\n5. Simplification tests:"
  putStrLn $ "   simplify (true && p): " ++ show testSimplify1
  putStrLn $ "   simplify (!!p): " ++ show testSimplify2
  putStrLn $ "   simplify (x == x): " ++ show testSimplify3

  putStrLn "\n6. Path-sensitive example:"
  print $ typeCheck pathSensitiveIf

  putStrLn "\nAll solutions implemented!"
