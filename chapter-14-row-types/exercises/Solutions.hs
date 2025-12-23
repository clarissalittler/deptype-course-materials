{-# LANGUAGE OverloadedStrings #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Map as Map

-- ============================================================================
-- Exercise 1: Record Operations
-- ============================================================================

-- Exercise 1.1: {x = 0, y = true}.x
-- Evaluation: Project field x from the record
-- Result: 0
ex1_1 :: Term
ex1_1 = TmProj (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)])) "x"

ex1_1_type :: Either TypeError Type
ex1_1_type = typeCheck ex1_1
-- Result: Right TyNat

ex1_1_explanation :: String
ex1_1_explanation = unlines
  [ "Evaluating {x = 0, y = true}.x:"
  , "1. The record has type {x: Nat, y: Bool}"
  , "2. Projecting field x yields 0 : Nat"
  , "3. Final result: 0"
  ]

-- Exercise 1.2: {z = 1 | {x = 0, y = true}}.z
-- Evaluation: Extend record with field z, then project z
-- Result: 1
ex1_2 :: Term
ex1_2 = TmProj
          (TmExtend
            (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)]))
            "z"
            (TmSucc TmZero))
          "z"

ex1_2_type :: Either TypeError Type
ex1_2_type = typeCheck ex1_2
-- Result: Right TyNat

ex1_2_explanation :: String
ex1_2_explanation = unlines
  [ "Evaluating {z = 1 | {x = 0, y = true}}.z:"
  , "1. Start with {x = 0, y = true} : {x: Nat, y: Bool}"
  , "2. Extend with z = 1"
  , "3. Result type: {z: Nat, x: Nat, y: Bool}"
  , "4. Project field z yields 1 : Nat"
  , "5. Final result: 1"
  ]

-- Exercise 1.3: {x = 0, y = true} \ x
-- Evaluation: Remove field x from the record
-- Result: {y = true}
ex1_3 :: Term
ex1_3 = TmRestrict (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)])) "x"

ex1_3_type :: Either TypeError Type
ex1_3_type = typeCheck ex1_3
-- Result: Right (TyRecord (RowExtend "y" TyBool RowEmpty))

ex1_3_explanation :: String
ex1_3_explanation = unlines
  [ "Evaluating {x = 0, y = true} \\ x:"
  , "1. Start with {x = 0, y = true} : {x: Nat, y: Bool}"
  , "2. Restrict by removing field x"
  , "3. Result: {y = true} : {y: Bool}"
  ]

-- ============================================================================
-- Exercise 2: Row Polymorphism
-- ============================================================================

-- addId : ∀ρ. {| ρ} -> {id: Nat | ρ}
-- This function adds an "id" field to any record.

-- The type signature says:
-- - For any row ρ
-- - Given a record with row ρ
-- - Return a record with an "id" field of type Nat plus the original row ρ

addId :: Term
addId = TmRowAbs "rho"
          (Lam "r" (TyRecord (RowVar "rho"))
            (TmExtend (Var "r") "id" TmZero))

addId_type :: Either TypeError Type
addId_type = typeCheck addId
-- Result: Right (TyForallRow "rho"
--                (TyFun (TyRecord (RowVar "rho"))
--                       (TyRecord (RowExtend "id" TyNat (RowVar "rho")))))

-- Example usage: Add id to {name = "Alice", age = 30}
-- Note: We don't have strings, so we use booleans as stand-ins
addId_example :: Term
addId_example =
  TmRowApp
    (TmRowApp addId (RowExtend "name" TyBool (RowExtend "age" TyNat RowEmpty)))
    (RowExtend "name" TyBool (RowExtend "age" TyNat RowEmpty))

ex2_explanation :: String
ex2_explanation = unlines
  [ "Row polymorphism allows functions to work on records with unknown fields."
  , ""
  , "The type ∀ρ. {| ρ} -> {id: Nat | ρ} means:"
  , "- For ANY row ρ (any set of fields)"
  , "- Take a record with those fields"
  , "- Return a record with an 'id' field PLUS all the original fields"
  , ""
  , "This is polymorphic over the 'shape' of the record."
  , "It works for {}, {x: Nat}, {x: Nat, y: Bool}, etc."
  ]

-- More row polymorphic functions:

-- selectX : ∀ρ. {x: Nat | ρ} -> Nat
-- Select the x field from any record that has an x field
selectX :: Term
selectX = TmRowAbs "rho"
            (Lam "r" (TyRecord (RowExtend "x" TyNat (RowVar "rho")))
              (TmProj (Var "r") "x"))

selectX_type :: Either TypeError Type
selectX_type = typeCheck selectX
-- Result: Right (TyForallRow "rho"
--                (TyFun (TyRecord (RowExtend "x" TyNat (RowVar "rho")))
--                       TyNat))

-- renameX : ∀ρ. {x: Nat | ρ} -> {x': Nat | ρ}
-- Rename field x to x'
renameX :: Term
renameX = TmRowAbs "rho"
            (Lam "r" (TyRecord (RowExtend "x" TyNat (RowVar "rho")))
              (TmExtend
                (TmRestrict (Var "r") "x")
                "x'"
                (TmProj (Var "r") "x")))

-- ============================================================================
-- Exercise 3: Variant Types
-- ============================================================================

-- Option a = <None: Unit | Some: a>
-- This is like Maybe in Haskell

-- Define the Option type
optionType :: Type -> Type
optionType a = TyVariant (RowExtend "None" TyUnit (RowExtend "Some" a RowEmpty))

-- none : ∀a. Option a
none :: Type -> Term
none a = TmVariant "None" TmUnit (optionType a)

-- some : ∀a. a -> Option a
some :: Type -> Term -> Term
some a value = TmVariant "Some" value (optionType a)

-- Example: none : Option Nat
noneNat :: Term
noneNat = none TyNat

noneNat_type :: Either TypeError Type
noneNat_type = typeCheck noneNat
-- Result: Right (TyVariant (RowExtend "None" TyUnit (RowExtend "Some" TyNat RowEmpty)))

-- Example: some 5 : Option Nat
someNat :: Term
someNat = some TyNat (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))))

someNat_type :: Either TypeError Type
someNat_type = typeCheck someNat
-- Result: Right (TyVariant (RowExtend "None" TyUnit (RowExtend "Some" TyNat RowEmpty)))

-- Pattern matching on Option
-- unwrap : Option Nat -> Nat
-- Returns the value if Some, or 0 if None
unwrapOption :: Term
unwrapOption =
  Lam "opt" (optionType TyNat)
    (TmCase (Var "opt")
      [ ("None", "_", TmZero)
      , ("Some", "x", Var "x")
      ])

unwrapOption_type :: Either TypeError Type
unwrapOption_type = typeCheck unwrapOption
-- Result: Right (TyFun (TyVariant ...) TyNat)

ex3_explanation :: String
ex3_explanation = unlines
  [ "Variants are dual to records:"
  , "- Records: a value contains ALL labeled fields"
  , "- Variants: a value contains EXACTLY ONE labeled alternative"
  , ""
  , "Option a = <None: Unit | Some: a> means:"
  , "- A value is EITHER <None = ()> OR <Some = v> for some v : a"
  , "- We use case analysis to determine which variant we have"
  , ""
  , "This is like sum types or tagged unions in other languages."
  ]

-- ============================================================================
-- Exercise 4: Polymorphic Variants
-- ============================================================================

-- Exercise 4: Difference between closed and open variants

-- 4.1: <A: Nat, B: Bool>
-- This is a CLOSED variant - it has exactly these two alternatives.
closedVariant :: Type
closedVariant = TyVariant (RowExtend "A" TyNat (RowExtend "B" TyBool RowEmpty))

closedVariant_example :: Term
closedVariant_example = TmVariant "A" (TmSucc TmZero) closedVariant

-- 4.2: <A: Nat | ρ>
-- This is an OPEN variant - it has alternative A, plus whatever is in ρ.
openVariant :: RowVar -> Type
openVariant rho = TyVariant (RowExtend "A" TyNat (RowVar rho))

ex4_explanation :: String
ex4_explanation = unlines
  [ "Closed vs Open Variants:"
  , ""
  , "CLOSED: <A: Nat, B: Bool>"
  , "- Fixed, finite set of alternatives"
  , "- A value is EITHER <A = n> OR <B = b>, nothing else"
  , "- Case analysis must handle all cases"
  , "- Cannot be extended with new alternatives"
  , ""
  , "OPEN: <A: Nat | ρ>"
  , "- Has alternative A: Nat, plus whatever alternatives are in ρ"
  , "- ρ is a row variable - it can be instantiated with more alternatives"
  , "- Allows row polymorphism over variants"
  , "- Example: can instantiate ρ with (B: Bool | ()) to get <A: Nat, B: Bool>"
  , ""
  , "Open variants enable:"
  , "- Functions that handle some cases and pass through others"
  , "- Extensible error types"
  , "- Modular case analysis"
  ]

-- Example: A function that handles only the A case
handleA :: Term
handleA = TmRowAbs "rho"
            (Lam "v" (TyVariant (RowExtend "A" TyNat (RowVar "rho")))
              (TmCase (Var "v")
                [ ("A", "n", Var "n")
                -- Note: In a full system, we'd need to handle the ρ cases too
                ]))

-- ============================================================================
-- Exercise 5: Record Update
-- ============================================================================

-- Implement record update: r.l := v
-- This is syntactic sugar for: {l = v | r \ l}

-- updateField : ∀ρ. Label -> Type -> {l: T | ρ} -> T -> {l: T | ρ}
updateField :: Label -> Term -> Term -> Term
updateField l record newValue =
  TmExtend (TmRestrict record l) l newValue

-- Example: Update x field
-- {x = 0, y = true}.x := 5
ex5_example :: Term
ex5_example = updateField "x"
                (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)]))
                (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))))

ex5_type :: Either TypeError Type
ex5_type = typeCheck ex5_example
-- Result: Right (TyRecord (RowExtend "x" TyNat (RowExtend "y" TyBool RowEmpty)))

ex5_explanation :: String
ex5_explanation = unlines
  [ "Record update r.l := v is implemented as:"
  , "  {l = v | r \\ l}"
  , ""
  , "Steps:"
  , "1. r \\ l: Remove field l from record r"
  , "2. {l = v | ...}: Add field l with new value v"
  , ""
  , "Example: {x = 0, y = true}.x := 5"
  , "1. {x = 0, y = true} \\ x = {y = true}"
  , "2. {x = 5 | {y = true}} = {x = 5, y = true}"
  , ""
  , "Type preservation:"
  , "- If r : {l: T | ρ} and v : T"
  , "- Then r.l := v : {l: T | ρ}"
  ]

-- ============================================================================
-- Row Polymorphism Examples
-- ============================================================================

-- Example 1: Point record types
point2D :: Type
point2D = TyRecord (RowExtend "x" TyNat (RowExtend "y" TyNat RowEmpty))

point3D :: Type
point3D = TyRecord (RowExtend "x" TyNat
                      (RowExtend "y" TyNat
                        (RowExtend "z" TyNat RowEmpty)))

-- getX works on both 2D and 3D points!
getX :: Term
getX = TmRowAbs "rho"
         (Lam "p" (TyRecord (RowExtend "x" TyNat (RowVar "rho")))
           (TmProj (Var "p") "x"))

-- Example 2: Record concatenation
-- concat : ∀ρ₁ ρ₂. {| ρ₁} -> {| ρ₂} -> {| ρ₁, ρ₂}
-- Note: In a full system, we'd need to ensure ρ₁ and ρ₂ are disjoint

-- Example 3: Subtyping simulation
-- In row types, {x: Nat, y: Bool, z: Unit} can be used where
-- {x: Nat, y: Bool | ρ} is expected, by instantiating ρ with (z: Unit | ())

-- ============================================================================
-- Variant Polymorphism Examples
-- ============================================================================

-- Example 1: Error handling with extensible errors
errorType :: RowVar -> Type
errorType rho = TyVariant (RowExtend "DivByZero" TyUnit (RowVar rho))

-- handleDivByZero : ∀ρ. <DivByZero: Unit | ρ> -> ...
-- This function handles division by zero errors, passing through other errors

-- Example 2: State machine with extensible states
stateType :: RowVar -> Type
stateType rho = TyVariant
  (RowExtend "Running" TyUnit
    (RowExtend "Stopped" TyUnit
      (RowVar rho)))

-- ============================================================================
-- Advanced Row Operations
-- ============================================================================

-- Row extension is order-independent (up to permutation)
-- {x: Nat, y: Bool} ≡ {y: Bool, x: Nat}

-- Records support "width" subtyping through row polymorphism:
-- {x: Nat, y: Bool, z: Unit} <: {x: Nat, y: Bool | ρ}

-- Multiple extensions
multiExtend :: Term
multiExtend =
  TmExtend
    (TmExtend
      (TmExtend
        (TmRecord Map.empty)
        "x" TmZero)
      "y" TmTrue)
    "z" TmUnit

multiExtend_type :: Either TypeError Type
multiExtend_type = typeCheck multiExtend
-- Result: {x: Nat, y: Bool, z: Unit}

-- ============================================================================
-- Practical Examples
-- ============================================================================

-- Example: Database records with optional fields
-- userRecord : ∀ρ. {id: Nat, name: String | ρ}
-- Different tables can have different additional fields

-- Example: Configuration objects
-- config : {debug: Bool, port: Nat | ρ}
-- Can be extended with additional config options

-- Example: Event types in event-driven systems
-- event : <Click: Nat | MouseMove: Nat | KeyPress: Nat | ρ>
-- New event types can be added by instantiating ρ

-- ============================================================================
-- Comparison with Other Type Systems
-- ============================================================================

comparisonExplanation :: String
comparisonExplanation = unlines
  [ "Row Types vs Other Approaches:"
  , ""
  , "1. Row Types vs Structural Subtyping:"
  , "   - Row types: Explicit polymorphism via row variables"
  , "   - Subtyping: Implicit {x: Nat, y: Bool} <: {x: Nat}"
  , "   - Row types are more explicit and predictable"
  , ""
  , "2. Row Types vs Type Classes:"
  , "   - Row types: Polymorphism over record/variant structure"
  , "   - Type classes: Polymorphism over operations/methods"
  , "   - Both enable ad-hoc polymorphism"
  , ""
  , "3. Row Types vs Dependent Types:"
  , "   - Row types: Types indexed by record structure"
  , "   - Dependent types: Types indexed by values"
  , "   - Row types are a simpler, more focused approach"
  , ""
  , "4. Benefits of Row Types:"
  , "   - Extensible records without subtyping complexity"
  , "   - Precise types for record operations"
  , "   - Modular variant handling"
  , "   - Type inference friendly"
  ]

-- ============================================================================
-- Test Suite
-- ============================================================================

testSolutions :: IO ()
testSolutions = do
  putStrLn "Testing Chapter 14: Row Types Solutions"
  putStrLn "========================================"

  putStrLn "\nExercise 1: Record Operations"
  putStrLn $ "  1.1 {x = 0, y = true}.x has type: " ++ show ex1_1_type
  putStrLn $ "  1.2 {z = 1 | {x = 0, y = true}}.z has type: " ++ show ex1_2_type
  putStrLn $ "  1.3 {x = 0, y = true} \\ x has type: " ++ show ex1_3_type

  putStrLn "\nExercise 2: Row Polymorphism"
  putStrLn $ "  addId has type: " ++ show addId_type
  putStrLn $ "  selectX has type: " ++ show selectX_type

  putStrLn "\nExercise 3: Variant Types"
  putStrLn $ "  none : Option Nat has type: " ++ show noneNat_type
  putStrLn $ "  some 5 : Option Nat has type: " ++ show someNat_type
  putStrLn $ "  unwrapOption has type: " ++ show unwrapOption_type

  putStrLn "\nExercise 5: Record Update"
  putStrLn $ "  Update example has type: " ++ show ex5_type

  putStrLn $ "\n" ++ ex2_explanation
  putStrLn ex3_explanation
  putStrLn ex4_explanation
  putStrLn ex5_explanation
  putStrLn comparisonExplanation

  putStrLn "\nAll solutions complete!"
