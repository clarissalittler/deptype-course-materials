{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Map.Strict as Map

-- ============================================================================
-- Exercise 1: Subtype Relationships
-- ============================================================================

-- This exercise explores the core subtyping rules:
-- - Width subtyping: {x, y, z} <: {x, y} (more fields is a subtype)
-- - Depth subtyping: If T <: U then {f: T} <: {f: U}
-- - Function subtyping: If S' <: S and T <: T' then (S -> T) <: (S' -> T')
--   (contravariant in argument, covariant in result)

-- Exercise 1.1: {x: Nat, y: Bool, z: Top} <: {x: Nat, y: Bool}
-- Answer: TRUE
-- Reason: Width subtyping - a record with more fields is a subtype of one
-- with fewer fields. The subtype has an extra field 'z'.
ex1_1 :: Bool
ex1_1 = isSubtype
  (TyRecord (Map.fromList [("x", TyNat), ("y", TyBool), ("z", TyTop)]))
  (TyRecord (Map.fromList [("x", TyNat), ("y", TyBool)]))
-- Result: True

-- Exercise 1.2: {x: Nat} <: {x: Nat, y: Bool}
-- Answer: FALSE
-- Reason: Subtyping goes the other way - fewer fields is NOT a subtype of
-- more fields. A value with only 'x' cannot be used where 'x' and 'y' are needed.
ex1_2 :: Bool
ex1_2 = isSubtype
  (TyRecord (Map.fromList [("x", TyNat)]))
  (TyRecord (Map.fromList [("x", TyNat), ("y", TyBool)]))
-- Result: False

-- Exercise 1.3: (Top -> Bool) <: (Nat -> Bool)
-- Answer: TRUE
-- Reason: Function subtyping is contravariant in argument type.
-- Since Nat <: Top, we have (Top -> Bool) <: (Nat -> Bool).
-- A function accepting Top can safely accept Nat (since Nat <: Top).
ex1_3 :: Bool
ex1_3 = isSubtype (TyArr TyTop TyBool) (TyArr TyNat TyBool)
-- Result: True

-- Exercise 1.4: (Nat -> Bool) <: (Top -> Bool)
-- Answer: FALSE
-- Reason: This would require Top <: Nat (contravariance), which is false.
-- A function expecting only Nat cannot safely accept arbitrary Top values.
ex1_4 :: Bool
ex1_4 = isSubtype (TyArr TyNat TyBool) (TyArr TyTop TyBool)
-- Result: False

-- Exercise 1.5: (Bool -> Bot) <: (Bool -> Nat)
-- Answer: TRUE
-- Reason: Function subtyping is covariant in result type.
-- Since Bot <: Nat, we have (Bool -> Bot) <: (Bool -> Nat).
ex1_5 :: Bool
ex1_5 = isSubtype (TyArr TyBool TyBot) (TyArr TyBool TyNat)
-- Result: True

-- Exercise 1.6: {f: Nat -> Bool} <: {f: Top -> Bool}
-- Answer: FALSE
-- Reason: This requires (Nat -> Bool) <: (Top -> Bool), which is false
-- (see exercise 1.4). Depth subtyping preserves the variance of the field type.
ex1_6 :: Bool
ex1_6 = isSubtype
  (TyRecord (Map.fromList [("f", TyArr TyNat TyBool)]))
  (TyRecord (Map.fromList [("f", TyArr TyTop TyBool)]))
-- Result: False

-- Exercise 1.7: {point: {x: Nat, y: Nat, z: Nat}} <: {point: {x: Nat, y: Nat}}
-- Answer: TRUE
-- Reason: Depth subtyping combined with width subtyping.
-- The nested record {x, y, z} <: {x, y} by width subtyping,
-- so the outer record satisfies depth subtyping.
ex1_7 :: Bool
ex1_7 = isSubtype
  (TyRecord (Map.fromList [("point", TyRecord (Map.fromList [("x", TyNat), ("y", TyNat), ("z", TyNat)]))]))
  (TyRecord (Map.fromList [("point", TyRecord (Map.fromList [("x", TyNat), ("y", TyNat)]))]))
-- Result: True

-- ============================================================================
-- Exercise 2: Maximum and Minimum Types
-- ============================================================================

-- For each expression, we find:
-- - Minimum type: the most specific type the expression has
-- - Maximum type: the most general type it can be ascribed to (via subsumption)

-- Exercise 2.1: λx:Nat. x
-- Minimum type: Nat -> Nat
-- Maximum type: Top (we can always upcast to Top)
-- But more usefully: Top -> Bot (most general function type)
ex2_1_min :: Type
ex2_1_min = TyArr TyNat TyNat

ex2_1_max :: Type
ex2_1_max = TyTop  -- Everything is a subtype of Top

-- A more useful maximum (most general function type):
ex2_1_max_function :: Type
ex2_1_max_function = TyArr TyBot TyTop
-- Because: (Nat -> Nat) <: (Bot -> Top)
-- - Bot <: Nat (contravariance)
-- - Nat <: Top (covariance)

-- Exercise 2.2: λx:Top. 0
-- Minimum type: Top -> Nat
-- Maximum type: Top (or Bot -> Top for functions)
ex2_2_min :: Type
ex2_2_min = TyArr TyTop TyNat

ex2_2_max :: Type
ex2_2_max = TyArr TyBot TyTop

-- Exercise 2.3: {name = true, age = succ 0}
-- Minimum type: {name: Bool, age: Nat}
-- Maximum type: Top (or {} - the empty record)
ex2_3_min :: Type
ex2_3_min = TyRecord (Map.fromList [("name", TyBool), ("age", TyNat)])

-- The empty record is the most general record type (fewest requirements)
ex2_3_max :: Type
ex2_3_max = TyRecord Map.empty

-- Exercise 2.4: λr:{x: Nat}. r.x
-- Minimum type: {x: Nat} -> Nat
-- Maximum type: Top (or more usefully, for functions: {x: Nat, ...} -> Top)
ex2_4_min :: Type
ex2_4_min = TyArr (TyRecord (Map.fromList [("x", TyNat)])) TyNat

-- More general: accept records with more fields, return Top
ex2_4_max :: Type
ex2_4_max = TyArr (TyRecord (Map.fromList [("x", TyBot)])) TyTop

-- ============================================================================
-- Exercise 3: Join and Meet
-- ============================================================================

-- Join (least upper bound): smallest type that both types are subtypes of
-- Meet (greatest lower bound): largest type that is a subtype of both

-- Exercise 3.1: Join and Meet of {x: Nat, y: Bool} and {x: Nat, z: Top}
-- Join: {x: Nat} (intersection of fields)
-- Meet: {x: Nat, y: Bool, z: Top} (union of fields)
ex3_1_join :: Maybe Type
ex3_1_join = join
  (TyRecord (Map.fromList [("x", TyNat), ("y", TyBool)]))
  (TyRecord (Map.fromList [("x", TyNat), ("z", TyTop)]))
-- Result: Just {x: Nat}

ex3_1_meet :: Maybe Type
ex3_1_meet = meet
  (TyRecord (Map.fromList [("x", TyNat), ("y", TyBool)]))
  (TyRecord (Map.fromList [("x", TyNat), ("z", TyTop)]))
-- Result: Just {x: Nat, y: Bool, z: Top}

-- Exercise 3.2: Join and Meet of (Nat -> Bool) and (Bool -> Bool)
-- Join: (Bot -> Bool) - most general type both are subtypes of
--   (Nat -> Bool) <: (Bot -> Bool) because Bot <: Nat
--   (Bool -> Bool) <: (Bot -> Bool) because Bot <: Bool
-- Meet: (Top -> Bool) - most specific supertype of both
--   Actually, meet of Nat and Bool is Bot, so: (Bot -> Bool)
--   Wait, this is more subtle. Let me reconsider.
--   For contravariant: join of args becomes meet
--   For covariant: meet of results becomes meet
ex3_2_join :: Maybe Type
ex3_2_join = join (TyArr TyNat TyBool) (TyArr TyBool TyBool)
-- Result: Just (Bot -> Bool) from the implementation

ex3_2_meet :: Maybe Type
ex3_2_meet = meet (TyArr TyNat TyBool) (TyArr TyBool TyBool)
-- Result: Just (Top -> Bool) from the implementation

-- Exercise 3.3: Join and Meet of {a: Top} and {a: Bot}
-- Join: {a: Top} (depth subtyping with join of Top and Bot = Top)
-- Meet: {a: Bot} (depth subtyping with meet of Top and Bot = Bot)
ex3_3_join :: Maybe Type
ex3_3_join = join
  (TyRecord (Map.fromList [("a", TyTop)]))
  (TyRecord (Map.fromList [("a", TyBot)]))
-- Result: Just {a: Top}

ex3_3_meet :: Maybe Type
ex3_3_meet = meet
  (TyRecord (Map.fromList [("a", TyTop)]))
  (TyRecord (Map.fromList [("a", TyBot)]))
-- Result: Just {a: Bot}

-- Exercise 3.4: Join and Meet of (Top -> Bot) and (Bot -> Top)
-- Join: (Bot -> Top)
--   Meet(Top, Bot) = Bot for argument (contravariant)
--   Join(Bot, Top) = Top for result (covariant)
-- Meet: (Top -> Bot)
--   Join(Top, Bot) = Top for argument (contravariant)
--   Meet(Bot, Top) = Bot for result (covariant)
ex3_4_join :: Maybe Type
ex3_4_join = join (TyArr TyTop TyBot) (TyArr TyBot TyTop)
-- Result: Just (Bot -> Top)

ex3_4_meet :: Maybe Type
ex3_4_meet = meet (TyArr TyTop TyBot) (TyArr TyBot TyTop)
-- Result: Just (Top -> Bot)

-- ============================================================================
-- Exercise 4: Subtyping Derivations
-- ============================================================================

-- We demonstrate formal derivations by checking these judgments

-- Exercise 4.1: {x: Bot, y: Bool} <: {x: Nat}
-- Derivation:
--   Bot <: Nat (by S-Bot)
--   ─────────────────────────── (S-RcdDepth on x, S-RcdWidth drops y)
--   {x: Bot, y: Bool} <: {x: Nat}
ex4_1 :: Bool
ex4_1 = isSubtype
  (TyRecord (Map.fromList [("x", TyBot), ("y", TyBool)]))
  (TyRecord (Map.fromList [("x", TyNat)]))
-- Result: True

-- Exercise 4.2: (Top -> {a: Nat, b: Bool}) <: (Bool -> {a: Nat})
-- Derivation:
--   Bool <: Top (by S-Top)    {a: Nat, b: Bool} <: {a: Nat} (by S-RcdWidth)
--   ──────────────────────────────────────────────────────────────────────── (S-Arrow)
--   (Top -> {a: Nat, b: Bool}) <: (Bool -> {a: Nat})
ex4_2 :: Bool
ex4_2 = isSubtype
  (TyArr TyTop (TyRecord (Map.fromList [("a", TyNat), ("b", TyBool)])))
  (TyArr TyBool (TyRecord (Map.fromList [("a", TyNat)])))
-- Result: True

-- Exercise 4.3: {f: Top -> Bot} <: {f: Nat -> Bool}
-- Derivation:
--   Nat <: Top (by S-Top)    Bot <: Bool (by S-Bot)
--   ──────────────────────────────────────────────── (S-Arrow)
--   (Top -> Bot) <: (Nat -> Bool)
--   ──────────────────────────────────────────────── (S-RcdDepth)
--   {f: Top -> Bot} <: {f: Nat -> Bool}
ex4_3 :: Bool
ex4_3 = isSubtype
  (TyRecord (Map.fromList [("f", TyArr TyTop TyBot)]))
  (TyRecord (Map.fromList [("f", TyArr TyNat TyBool)]))
-- Result: True

-- ============================================================================
-- Exercise 6: Covariant and Contravariant Positions
-- ============================================================================

-- We analyze variance by counting the number of times we're on the left
-- of an arrow:
-- - Even number (0, 2, 4, ...): covariant (+)
-- - Odd number (1, 3, 5, ...): contravariant (-)
-- - Mixed: invariant (±)

-- Exercise 6.1: X -> Bool
-- X is on the left of an arrow (1 time) → contravariant (-)
variance_6_1 :: String
variance_6_1 = "contravariant (-)"

-- Exercise 6.2: Bool -> X
-- X is on the right of an arrow (0 times on left) → covariant (+)
variance_6_2 :: String
variance_6_2 = "covariant (+)"

-- Exercise 6.3: (X -> Bool) -> Nat
-- X is on the left of first arrow, then that whole type is on the left of second arrow
-- Left count: 1 + 1 = 2 → covariant (+)
variance_6_3 :: String
variance_6_3 = "covariant (+)"

-- Exercise 6.4: (Bool -> X) -> Nat
-- X is on the right of first arrow (0), then that whole type is on left of second (1)
-- Left count: 0 + 1 = 1 → contravariant (-)
variance_6_4 :: String
variance_6_4 = "contravariant (-)"

-- Exercise 6.5: {field: X -> X}
-- First X: contravariant (left of arrow) (-)
-- Second X: covariant (right of arrow) (+)
-- Result: invariant (±) because X appears in both positions
variance_6_5 :: String
variance_6_5 = "invariant (±)"

-- Exercise 6.6: (X -> X) -> (X -> X)
-- First X -> X on the left of outer arrow:
--   First X: 1 flip → contravariant
--   Second X: 1 flip → contravariant
-- Second X -> X on the right of outer arrow:
--   Third X: 0 flips → contravariant (inherits from being in function)
--   Fourth X: 0 flips → covariant
-- Actually, let me recalculate:
-- - Position 1 (arg of arg of result function): 1 flip = contravariant
-- - Position 2 (result of arg of result function): 1 flip = contravariant
-- - Position 3 (arg of result function): 0 flips + inside function = contravariant
-- - Position 4 (result of result function): 0 flips = covariant
-- Since X appears in both covariant and contravariant positions → invariant (±)
variance_6_6 :: String
variance_6_6 = "invariant (±)"

-- ============================================================================
-- Exercise 10: Object-Oriented Encoding
-- ============================================================================

-- We encode object-oriented programming using records and subtyping

-- Point type: a simple 2D point
type PointType = Type
point :: PointType
point = TyRecord (Map.fromList [("x", TyNat), ("y", TyNat)])

-- ColoredPoint type: a point with an additional color field
type ColoredPointType = Type
coloredPoint :: ColoredPointType
coloredPoint = TyRecord (Map.fromList
  [("x", TyNat), ("y", TyNat), ("color", TyBool)])

-- Verify subtyping relationship: ColoredPoint <: Point
-- This is width subtyping - more fields is a subtype
coloredPointIsPoint :: Bool
coloredPointIsPoint = isSubtype coloredPoint point
-- Result: True

-- A function that works on any Point
-- distance : {x: Nat, y: Nat} -> Nat
-- In a real implementation, this would compute sqrt(x^2 + y^2)
-- For simplicity, we just return x + y as a "Manhattan distance"
distance :: Term
distance = Lam "p" point
  (App (App (Var "add")  -- Hypothetical add function
            (TmProj (Var "p") "x"))
       (TmProj (Var "p") "y"))

-- Create a Point value
pointValue :: Term
pointValue = TmRecord (Map.fromList
  [("x", TmSucc (TmSucc TmZero))  -- x = 2
  ,("y", TmSucc (TmSucc (TmSucc TmZero)))])  -- y = 3

-- Create a ColoredPoint value
coloredPointValue :: Term
coloredPointValue = TmRecord (Map.fromList
  [("x", TmSucc TmZero)  -- x = 1
  ,("y", TmSucc (TmSucc TmZero))  -- y = 2
  ,("color", TmTrue)])  -- color = true

-- Demonstrate that distance works on both Point and ColoredPoint
-- This shows subsumption in action: ColoredPoint <: Point, so we can
-- pass coloredPointValue where Point is expected

-- Apply distance to a Point
testDistanceOnPoint :: Term
testDistanceOnPoint = App distance pointValue

-- Apply distance to a ColoredPoint (works via subsumption!)
testDistanceOnColoredPoint :: Term
testDistanceOnColoredPoint = App distance coloredPointValue

-- We can also upcast explicitly using ascription
upcastColoredPoint :: Term
upcastColoredPoint = TmAscribe coloredPointValue point

-- A function that only works on ColoredPoint
-- getColor : {x: Nat, y: Nat, color: Bool} -> Bool
getColor :: Term
getColor = Lam "cp" coloredPoint (TmProj (Var "cp") "color")

-- This would fail: App getColor pointValue
-- Because Point doesn't have a color field

-- ============================================================================
-- Test Suite
-- ============================================================================

-- Run tests to verify the solutions
testSolutions :: IO ()
testSolutions = do
  putStrLn "Testing Chapter 9: Subtyping Solutions"
  putStrLn "======================================="

  putStrLn "\nExercise 1: Subtype Relationships"
  putStrLn $ "1.1 (width subtyping): " ++ show ex1_1
  putStrLn $ "1.2 (reverse width - should be False): " ++ show ex1_2
  putStrLn $ "1.3 (function contravariance): " ++ show ex1_3
  putStrLn $ "1.4 (reverse contravariance - should be False): " ++ show ex1_4
  putStrLn $ "1.5 (function covariance): " ++ show ex1_5
  putStrLn $ "1.6 (depth with function - should be False): " ++ show ex1_6
  putStrLn $ "1.7 (nested width subtyping): " ++ show ex1_7

  putStrLn "\nExercise 2: Maximum and Minimum Types"
  putStrLn $ "2.1 min: " ++ showType ex2_1_min
  putStrLn $ "2.1 max (function): " ++ showType ex2_1_max_function
  putStrLn $ "2.2 min: " ++ showType ex2_2_min
  putStrLn $ "2.3 min: " ++ showType ex2_3_min
  putStrLn $ "2.4 min: " ++ showType ex2_4_min

  putStrLn "\nExercise 3: Join and Meet"
  putStrLn $ "3.1 join: " ++ show (fmap showType ex3_1_join)
  putStrLn $ "3.1 meet: " ++ show (fmap showType ex3_1_meet)
  putStrLn $ "3.2 join: " ++ show (fmap showType ex3_2_join)
  putStrLn $ "3.2 meet: " ++ show (fmap showType ex3_2_meet)
  putStrLn $ "3.3 join: " ++ show (fmap showType ex3_3_join)
  putStrLn $ "3.3 meet: " ++ show (fmap showType ex3_3_meet)

  putStrLn "\nExercise 4: Subtyping Derivations"
  putStrLn $ "4.1: " ++ show ex4_1
  putStrLn $ "4.2: " ++ show ex4_2
  putStrLn $ "4.3: " ++ show ex4_3

  putStrLn "\nExercise 6: Variance Analysis"
  putStrLn $ "6.1 (X -> Bool): " ++ variance_6_1
  putStrLn $ "6.2 (Bool -> X): " ++ variance_6_2
  putStrLn $ "6.3 ((X -> Bool) -> Nat): " ++ variance_6_3
  putStrLn $ "6.4 ((Bool -> X) -> Nat): " ++ variance_6_4
  putStrLn $ "6.5 ({field: X -> X}): " ++ variance_6_5
  putStrLn $ "6.6 ((X -> X) -> (X -> X)): " ++ variance_6_6

  putStrLn "\nExercise 10: Object-Oriented Encoding"
  putStrLn $ "ColoredPoint <: Point: " ++ show coloredPointIsPoint
  putStrLn $ "Point type: " ++ showType point
  putStrLn $ "ColoredPoint type: " ++ showType coloredPoint

  putStrLn "\nAll solutions demonstrated!"

-- Helper to show Types
showType :: Type -> String
showType = \case
  TyVar v -> v
  TyArr t1 t2 -> "(" ++ showType t1 ++ " -> " ++ showType t2 ++ ")"
  TyBool -> "Bool"
  TyNat -> "Nat"
  TyTop -> "Top"
  TyBot -> "Bot"
  TyRecord fields ->
    "{" ++ unwords [l ++ ": " ++ showType t | (l, t) <- Map.toList fields] ++ "}"
