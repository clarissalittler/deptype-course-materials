{-# LANGUAGE OverloadedStrings #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Map as Map

-- ============================================================================
-- Exercise 1: Understanding Consistency
-- ============================================================================

-- Consistency (T₁ ~ T₂) is the key relation in gradual typing.
-- Two types are consistent if one could be a plausible guess for the other.

-- Exercise 1.1: Nat ~ ?
-- Answer: Yes, consistent. ? is consistent with any type.
ex1_1 :: Bool
ex1_1 = consistent TyNat TyDyn
-- Result: True

-- Exercise 1.2: ? ~ Bool
-- Answer: Yes, consistent. ? is consistent with any type.
ex1_2 :: Bool
ex1_2 = consistent TyDyn TyBool
-- Result: True

-- Exercise 1.3: Nat -> Bool ~ ? -> ?
-- Answer: Yes, consistent. Functions are consistent if their domains
-- and codomains are consistent: Nat ~ ? and Bool ~ ?
ex1_3 :: Bool
ex1_3 = consistent (TyFun TyNat TyBool) (TyFun TyDyn TyDyn)
-- Result: True

-- Exercise 1.4: Nat -> Bool ~ ? -> Nat
-- Answer: Yes, consistent. Nat ~ ? and Bool ~ Nat would fail for normal
-- equality, but Bool ~ Nat is checked, which is False... wait, this should
-- be Nat ~ Nat in the codomain. Let me recalculate:
-- Domain: Nat ~ ?, True
-- Codomain: Bool ~ Nat, False
-- So this is NOT consistent.
ex1_4 :: Bool
ex1_4 = consistent (TyFun TyNat TyBool) (TyFun TyDyn TyNat)
-- Result: False

-- Exercise 1.5: Nat -> Bool ~ Bool -> Nat
-- Answer: No, not consistent. While Nat and Bool are both base types,
-- they are different, so Nat ~ Bool is False.
ex1_5 :: Bool
ex1_5 = consistent (TyFun TyNat TyBool) (TyFun TyBool TyNat)
-- Result: False

-- Exercise 1.6: (? -> Nat) -> Bool ~ (Nat -> ?) -> ?
-- Answer: Let's check step by step:
-- Outer function domains: (? -> Nat) ~ (Nat -> ?)
--   Inner domains: ? ~ Nat, True
--   Inner codomains: Nat ~ ?, True
--   So: True
-- Outer function codomains: Bool ~ ?, True
-- Result: True
ex1_6 :: Bool
ex1_6 = consistent (TyFun (TyFun TyDyn TyNat) TyBool)
                   (TyFun (TyFun TyNat TyDyn) TyDyn)
-- Result: True

-- ============================================================================
-- Exercise 2: Type Checking
-- ============================================================================

-- Exercise 2.1: λx : ?. x
-- Type: ? -> ?
ex2_1 :: Term
ex2_1 = Lam "x" TyDyn (Var "x")

ex2_1_type :: Either TypeError Type
ex2_1_type = typeCheck ex2_1
-- Result: Right (TyFun TyDyn TyDyn)

-- Exercise 2.2: λx : ?. succ x
-- Type: ? -> Nat
-- The argument x has type ?, which is consistent with Nat (required by succ).
-- The result of succ is always Nat.
ex2_2 :: Term
ex2_2 = Lam "x" TyDyn (TmSucc (Var "x"))

ex2_2_type :: Either TypeError Type
ex2_2_type = typeCheck ex2_2
-- Result: Right (TyFun TyDyn TyNat)

-- Exercise 2.3: (λx : ?. x) true
-- Type: ?
-- The function has type ? -> ?, and true : Bool is consistent with ?.
-- The result type is ?.
ex2_3 :: Term
ex2_3 = App (Lam "x" TyDyn (Var "x")) TmTrue

ex2_3_type :: Either TypeError Type
ex2_3_type = typeCheck ex2_3
-- Result: Right TyDyn

-- Exercise 2.4: (λf : ?. f 0) (λx : Nat. x)
-- Type: ?
-- f : ?, and we apply it to 0 : Nat. Since f : ?, we treat this as
-- f : ? -> ?, so the result is ?.
ex2_4 :: Term
ex2_4 = App (Lam "f" TyDyn (App (Var "f") TmZero))
            (Lam "x" TyNat (Var "x"))

ex2_4_type :: Either TypeError Type
ex2_4_type = typeCheck ex2_4
-- Result: Right TyDyn

-- Exercise 2.5: λf : ? -> Nat. λx : ?. f x
-- Type: (? -> Nat) -> ? -> Nat
-- f has type ? -> Nat, x has type ?, which is consistent with ?.
-- The result is f x : Nat.
ex2_5 :: Term
ex2_5 = Lam "f" (TyFun TyDyn TyNat)
            (Lam "x" TyDyn (App (Var "f") (Var "x")))

ex2_5_type :: Either TypeError Type
ex2_5_type = typeCheck ex2_5
-- Result: Right (TyFun (TyFun TyDyn TyNat) (TyFun TyDyn TyNat))

-- ============================================================================
-- Exercise 3: Cast Insertion
-- ============================================================================

-- Exercise 3.1: (λx : ?. x) 0
-- With explicit casts: (λx : ?. x) (<Nat => ?>^l 0)
-- The argument 0 : Nat needs to be cast to ? to match the parameter type.
ex3_1 :: Term
ex3_1 = App (Lam "x" TyDyn (Var "x")) TmZero

ex3_1_with_casts :: Either TypeError Term
ex3_1_with_casts = insertCasts emptyContext ex3_1
-- Result: The insertCasts function will add a cast from Nat to ? for the argument.
-- Expected: App (Lam "x" TyDyn (Var "x")) (TmCast TmZero TyNat TyDyn "arg")

-- Exercise 3.2: (λf : ? -> Nat. f true) (λx : ?. 0)
-- The function λx : ?. 0 has type ? -> Nat
-- When applied to true : Bool, we need to cast Bool to ? to match.
-- Expected: (λf : ? -> Nat. f (<Bool => ?>^l true)) (λx : ?. 0)
ex3_2 :: Term
ex3_2 = App (Lam "f" (TyFun TyDyn TyNat)
                 (App (Var "f") TmTrue))
            (Lam "x" TyDyn TmZero)

ex3_2_with_casts :: Either TypeError Term
ex3_2_with_casts = insertCasts emptyContext ex3_2
-- Result: Cast will be inserted for the true argument to f.

-- Exercise 3.3: if (x : ?) then 0 else 1 (where x : ?)
-- The condition x : ? needs to be cast to Bool.
-- Expected: if (<? => Bool>^l x) then 0 else 1
ex3_3 :: Term
ex3_3 = TmIf (TmAscribe (Var "x") TyDyn) TmZero (TmSucc TmZero)

-- We need a context with x : ?
ex3_3_with_casts :: Either TypeError Term
ex3_3_with_casts = insertCasts (Map.fromList [("x", TyDyn)]) ex3_3
-- Result: Cast will be inserted to convert ? to Bool for the condition.

-- ============================================================================
-- Exercise 4: Blame Tracking
-- ============================================================================

-- Blame labels track where type errors originate at runtime.

-- Exercise 4.1: (λx : Nat. x) ((λy : ?. y) true)
-- Analysis:
-- - Inner application: (λy : ?. y) true
--   - λy : ?. y has type ? -> ?
--   - Applying to true : Bool requires cast <Bool => ?>^l1 true
--   - Result has type ?
-- - Outer application: (λx : Nat. x) (result : ?)
--   - Expects Nat, receives ?
--   - Requires cast <? => Nat>^l2 result
--   - If the cast fails (because the value is actually true : Bool),
--     blame is assigned to l2.
ex4_1 :: Term
ex4_1 = App (Lam "x" TyNat (Var "x"))
            (App (Lam "y" TyDyn (Var "y")) TmTrue)

ex4_1_blame :: String
ex4_1_blame = "Blame at outer application: casting ? to Nat fails because the value is Bool (true)"

-- Exercise 4.2: (λf : Nat -> Nat. f true) (λx : ?. x)
-- Analysis:
-- - The function λf : Nat -> Nat. f true expects f : Nat -> Nat
-- - The argument λx : ?. x has type ? -> ?
-- - We need to cast ? -> ? to Nat -> Nat: <? -> ? => Nat -> Nat>^l1
-- - Inside the body, we apply f to true : Bool
-- - This requires casting true to Nat: <Bool => Nat>^l2
-- - Blame is assigned to l2 for trying to cast Bool to Nat.
ex4_2 :: Term
ex4_2 = App (Lam "f" (TyFun TyNat TyNat) (App (Var "f") TmTrue))
            (Lam "x" TyDyn (Var "x"))

ex4_2_blame :: String
ex4_2_blame = "Blame at argument to f: casting Bool (true) to Nat fails"

-- Exercise 4.3: let f = (λx : ?. succ x) in f true
-- Analysis:
-- - f has type ? -> Nat
-- - Applying f to true requires casting Bool to ?: <Bool => ?>^l1
-- - Inside f, we apply succ to x : ?
-- - succ requires Nat, so we need <? => Nat>^l2 x
-- - At runtime, the cast tries to convert true (Bool) to Nat
-- - Blame is assigned to l2.
ex4_3 :: Term
ex4_3 = TmLet "f" (Lam "x" TyDyn (TmSucc (Var "x")))
              (App (Var "f") TmTrue)

ex4_3_blame :: String
ex4_3_blame = "Blame at succ application: casting ? (containing Bool) to Nat fails"

-- ============================================================================
-- Exercise 5: Ground Types
-- ============================================================================

-- Ground types are base types or ? -> ?.
-- They are used in the cast semantics to decompose casts.

-- Exercise 5.1: Why is ? -> ? a ground type but Nat -> Bool is not?
ex5_1_explanation :: String
ex5_1_explanation = unlines
  [ "Ground types are the 'canonical representatives' of each type constructor."
  , "For base types (Nat, Bool, Unit), they are their own ground types."
  , "For function types, the ground type is ? -> ? because it represents"
  , "the least precise function type - a function with unknown domain and codomain."
  , ""
  , "Nat -> Bool is NOT a ground type because it is more precise than ? -> ?."
  , "Ground types are used to mediate casts through the dynamic type ?."
  ]

-- Check ground types
ex5_1_tests :: [(Type, Bool)]
ex5_1_tests =
  [ (TyNat, isGround TyNat)                    -- True: base type
  , (TyBool, isGround TyBool)                  -- True: base type
  , (TyUnit, isGround TyUnit)                  -- True: base type
  , (TyFun TyDyn TyDyn, isGround (TyFun TyDyn TyDyn))  -- True: ? -> ?
  , (TyFun TyNat TyBool, isGround (TyFun TyNat TyBool)) -- False: not ground
  , (TyDyn, isGround TyDyn)                    -- False: ? is not ground
  ]

-- Exercise 5.2: How do casts decompose through ground types?
ex5_2_explanation :: String
ex5_2_explanation = unlines
  [ "Casts between non-ground types and ? decompose through ground types."
  , ""
  , "Example: Casting Nat -> Bool to ?"
  , "  <Nat -> Bool => ?> decomposes to:"
  , "  <Nat -> Bool => ? -> ?> ; <? -> ? => ?>"
  , ""
  , "Example: Casting ? to Nat -> Bool"
  , "  <? => Nat -> Bool> decomposes to:"
  , "  <? => ? -> ?> ; <? -> ? => Nat -> Bool>"
  , ""
  , "For function types, the cast further decomposes:"
  , "  <Nat -> Bool => ? -> ?> creates a wrapper that:"
  , "  - Casts arguments from ? to Nat (contravariant)"
  , "  - Casts results from Bool to ? (covariant)"
  ]

-- Exercise 5.3: What happens when casting Nat -> Bool to ??
ex5_3_example :: Term
ex5_3_example = TmCast (Lam "x" TyNat (TmIf (TmIsZero (Var "x")) TmTrue TmFalse))
                       (TyFun TyNat TyBool)
                       TyDyn
                       "ex5_3"

ex5_3_explanation :: String
ex5_3_explanation = unlines
  [ "When casting a function Nat -> Bool to ?, the cast decomposes as:"
  , ""
  , "1. First, cast Nat -> Bool to the ground type ? -> ?:"
  , "   This creates a wrapper function that:"
  , "   - Takes argument of type ?"
  , "   - Casts it to Nat (using <? => Nat>)"
  , "   - Applies the original function"
  , "   - Casts the result Bool to ? (using <Bool => ?>)"
  , ""
  , "2. Then, cast ? -> ? to ?:"
  , "   This is the injection of a function ground type into ?."
  , ""
  , "At runtime, when this cast function is applied:"
  , "  - The argument is cast from ? to Nat"
  , "  - If the cast fails, blame is assigned"
  , "  - The result Bool is cast to ?"
  ]

-- ============================================================================
-- Exercise 6: Meet and Join
-- ============================================================================

-- The meet (⊓) is the greatest lower bound - the most precise type
-- that is less precise than both inputs.
-- The join (⊔) is the least upper bound - the least precise type
-- that is more precise than both inputs.

-- Exercise 6.1: Nat ⊓ ?
ex6_1 :: Maybe Type
ex6_1 = meet TyNat TyDyn
-- Result: Just TyNat
-- Explanation: Nat is more precise than ?, so the meet is Nat.

-- Exercise 6.2: ? ⊓ ?
ex6_2 :: Maybe Type
ex6_2 = meet TyDyn TyDyn
-- Result: Just TyDyn
-- Explanation: Both are ?, so the meet is ?.

-- Exercise 6.3: (Nat -> Bool) ⊓ (? -> ?)
ex6_3 :: Maybe Type
ex6_3 = meet (TyFun TyNat TyBool) (TyFun TyDyn TyDyn)
-- Result: Just (TyFun TyNat TyBool)
-- Explanation:
--   Domain: Nat ⊓ ? = Nat
--   Codomain: Bool ⊓ ? = Bool
--   Result: Nat -> Bool

-- Exercise 6.4: Nat ⊔ ?
ex6_4 :: Maybe Type
ex6_4 = join TyNat TyDyn
-- Result: Just TyDyn
-- Explanation: ? is less precise than Nat, so the join is ?.

-- Exercise 6.5: (Nat -> ?) ⊔ (? -> Bool)
ex6_5 :: Maybe Type
ex6_5 = join (TyFun TyNat TyDyn) (TyFun TyDyn TyBool)
-- Result: Just (TyFun TyDyn TyDyn)
-- Explanation:
--   Domain: Nat ⊔ ? = ?
--   Codomain: ? ⊔ Bool = ?
--   Result: ? -> ?

-- ============================================================================
-- Examples: Consistency in Action
-- ============================================================================

-- Example 1: A gradually-typed identity function
gradualId :: Term
gradualId = Lam "x" TyDyn (Var "x")
-- Type: ? -> ?
-- Can be applied to any argument type

-- Example 2: A function that expects Nat but accepts ?
partiallyTyped :: Term
partiallyTyped = Lam "x" TyDyn (TmSucc (Var "x"))
-- Type: ? -> Nat
-- At runtime, if x is not a Nat, the cast to Nat will fail with blame

-- Example 3: Ascription and casting
withAscription :: Term
withAscription = TmAscribe (Lam "x" TyDyn (Var "x")) (TyFun TyNat TyNat)
-- The ascription asserts that the ? -> ? function has type Nat -> Nat
-- This will insert casts to ensure the function behaves as Nat -> Nat

-- ============================================================================
-- Examples: Blame in Action
-- ============================================================================

-- Example 4: A cast that will succeed
goodCast :: Term
goodCast = TmCast TmZero TyNat TyDyn "safe"
-- Casting 0 : Nat to ? always succeeds

-- Example 5: A cast that will fail at runtime
badCast :: Term
badCast = TmCast TmTrue TyBool TyNat "unsafe"
-- Casting true : Bool to Nat will fail with blame "unsafe"
-- This represents a type error caught at runtime

-- Example 6: Function cast
functionCast :: Term
functionCast = TmCast (Lam "x" TyNat (Var "x"))
                      (TyFun TyNat TyNat)
                      (TyFun TyDyn TyDyn)
                      "funcast"
-- Casting Nat -> Nat to ? -> ?
-- Creates a wrapper that casts arguments and results

-- ============================================================================
-- Examples: Gradual Typing Use Cases
-- ============================================================================

-- Example 7: Migrating from dynamic to static
-- Start with fully dynamic code:
fullyDynamic :: Term
fullyDynamic =
  Lam "f" TyDyn
    (Lam "x" TyDyn
      (App (Var "f") (Var "x")))
-- Type: ? -> ? -> ?

-- Add types incrementally:
partiallyStatic :: Term
partiallyStatic =
  Lam "f" (TyFun TyNat TyNat)
    (Lam "x" TyDyn
      (App (Var "f") (Var "x")))
-- Type: (Nat -> Nat) -> ? -> Nat
-- More precise: we know f is Nat -> Nat

-- Fully static:
fullyStatic :: Term
fullyStatic =
  Lam "f" (TyFun TyNat TyNat)
    (Lam "x" TyNat
      (App (Var "f") (Var "x")))
-- Type: (Nat -> Nat) -> Nat -> Nat
-- Fully typed, no runtime casts needed

-- ============================================================================
-- Test Suite
-- ============================================================================

testSolutions :: IO ()
testSolutions = do
  putStrLn "Testing Chapter 13: Gradual Typing Solutions"
  putStrLn "=============================================="

  putStrLn "\nExercise 1: Consistency Tests"
  putStrLn $ "  1.1 Nat ~ ? = " ++ show ex1_1
  putStrLn $ "  1.2 ? ~ Bool = " ++ show ex1_2
  putStrLn $ "  1.3 Nat -> Bool ~ ? -> ? = " ++ show ex1_3
  putStrLn $ "  1.4 Nat -> Bool ~ ? -> Nat = " ++ show ex1_4
  putStrLn $ "  1.5 Nat -> Bool ~ Bool -> Nat = " ++ show ex1_5
  putStrLn $ "  1.6 (? -> Nat) -> Bool ~ (Nat -> ?) -> ? = " ++ show ex1_6

  putStrLn "\nExercise 2: Type Checking"
  putStrLn $ "  2.1 λx:?. x has type: " ++ show ex2_1_type
  putStrLn $ "  2.2 λx:?. succ x has type: " ++ show ex2_2_type
  putStrLn $ "  2.3 (λx:?. x) true has type: " ++ show ex2_3_type
  putStrLn $ "  2.4 (λf:?. f 0) (λx:Nat. x) has type: " ++ show ex2_4_type
  putStrLn $ "  2.5 λf:?->Nat. λx:?. f x has type: " ++ show ex2_5_type

  putStrLn "\nExercise 5: Ground Type Tests"
  putStrLn "  Type -> IsGround?"
  mapM_ (\(ty, result) -> putStrLn $ "    " ++ show ty ++ " -> " ++ show result) ex5_1_tests

  putStrLn "\nExercise 6: Meet and Join"
  putStrLn $ "  6.1 Nat ⊓ ? = " ++ show ex6_1
  putStrLn $ "  6.2 ? ⊓ ? = " ++ show ex6_2
  putStrLn $ "  6.3 (Nat -> Bool) ⊓ (? -> ?) = " ++ show ex6_3
  putStrLn $ "  6.4 Nat ⊔ ? = " ++ show ex6_4
  putStrLn $ "  6.5 (Nat -> ?) ⊔ (? -> Bool) = " ++ show ex6_5

  putStrLn "\nAll solutions complete!"
