{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import TypeCheck

-- ============================================================================
-- Exercise 1: Mode Classification
-- ============================================================================

-- Solutions provided in the EXERCISES.md file:
--
-- 1. `true` - INFERRED (=>)
--    Reason: Boolean literals have a known type (TyBool)
--
-- 2. `\x. x` - CHECKED (<=)
--    Reason: Unannotated lambda needs expected type to determine x's type
--
-- 3. `\(x : Bool). x` - INFERRED (=>)
--    Reason: Annotation on parameter provides input type, enabling inference
--
-- 4. `f x` - INFERRED (=>)
--    Reason: Application is elimination form, can infer from function type
--
-- 5. `(true, false)` - CHECKED (<=)
--    Reason: Pairs are introduction forms, need expected type for components
--
-- 6. `fst p` - INFERRED (=>)
--    Reason: Projection is elimination form, can extract from pair type
--
-- 7. `inl true` - CHECKED (<=)
--    Reason: Injection is introduction form, need full sum type
--
-- 8. `(\x. x : Bool -> Bool)` - INFERRED (=>)
--    Reason: Top-level annotation makes entire term inferrable

-- ============================================================================
-- Exercise 2: Derivation Trees
-- ============================================================================

-- Full bidirectional typing derivation for: ⊢ (\(x : Bool). x) true => Bool
--
-- The derivation tree (from bottom to top):
--
--                                    ─────────────────── (Var)
--                                    x:Bool ⊢ x => Bool
--                     ─────────────────────────────────────── (LamAnn)
--                     ⊢ (\(x:Bool). x) => Bool -> Bool
--                                                               ───────────────── (True)
--                                                               ⊢ true => Bool
--                                                            ───────────────────── (Sub)
--                                                               ⊢ true <= Bool
-- ─────────────────────────────────────────────────────────────────────────────────────── (App)
--                     ⊢ (\(x:Bool). x) true => Bool

-- ============================================================================
-- Exercise 3: Annotation Placement
-- ============================================================================

-- Exercise 3a: \x. \y. x
-- Minimal annotation: add parameter type to first lambda
ex3a :: Term
ex3a = LamAnn "x" TyBool (Lam "y" (Var "x"))
-- Type: Bool -> A -> Bool (for any A)
-- Alternative: (\x. \y. x : Bool -> Nat -> Bool)

-- Exercise 3b: \f. \x. f (f x)
-- Need to annotate both f and x since they interact
ex3b :: Term
ex3b = LamAnn "f" (TyArr TyNat TyNat) (LamAnn "x" TyNat (App (Var "f") (App (Var "f") (Var "x"))))
-- Type: (Nat -> Nat) -> Nat -> Nat

-- Exercise 3c: (inl true, inr zero)
-- Need full type annotation on the pair
ex3c :: Term
ex3c = Ann (Pair (Inl TmTrue) (Inr Zero))
           (TyProd (TySum TyBool TyNat) (TySum TyBool TyNat))
-- Type: (Bool + Nat, Bool + Nat)

-- Exercise 3d: \p. (snd p, fst p)
-- Need to annotate the pair parameter
ex3d :: Term
ex3d = LamAnn "p" (TyProd TyBool TyNat)
              (Pair (Snd (Var "p")) (Fst (Var "p")))
-- Type: (Bool, Nat) -> (Nat, Bool)

-- ============================================================================
-- Exercise 4: Unit Type Checking
-- ============================================================================

-- The unit type is both checkable and inferrable.
-- In the current implementation, TmUnit is inferrable (returns TyUnit).
--
-- For checking mode:
--   check ctx TmUnit TyUnit = success (it matches)
--   check ctx TmUnit otherTy = error (type mismatch)
--
-- This is already handled by the subsumption rule in the type checker:
--   (e, expected) -> do
--     inferred <- infer ctx e
--     unless (typeEq inferred expected) $ ...
--
-- So TmUnit works correctly in both modes!

-- Test cases for unit type
testUnit1 :: Either TypeError Type
testUnit1 = infer emptyCtx TmUnit
-- Expected: Right TyUnit

testUnit2 :: Either TypeError ()
testUnit2 = check emptyCtx TmUnit TyUnit
-- Expected: Right ()

testUnit3 :: Either TypeError ()
testUnit3 = check emptyCtx TmUnit TyBool
-- Expected: Left (TypeMismatch TyBool TyUnit)

-- ============================================================================
-- Exercise 8: Bidirectional Case Analysis
-- ============================================================================

-- Current implementation: Case infers the scrutinee and branches
-- This means branches must be inferrable.
--
-- To support checking mode for case expressions, we would modify:
--
-- checkCase :: Ctx -> Term -> Name -> Term -> Name -> Term -> Type -> TC ()
-- checkCase ctx scrut x1 e1 x2 e2 expectedTy = do
--   t <- infer ctx scrut
--   case t of
--     TySum a b -> do
--       check (extendCtx x1 a ctx) e1 expectedTy
--       check (extendCtx x2 b ctx) e2 expectedTy
--     _ -> throwError $ ExpectedSum t
--
-- This would make terms like this typeable:
--   case x of
--     inl a -> \y. a    -- unannotated lambda in branch
--     inr b -> \z. b
--
-- Previously, the unannotated lambdas couldn't be inferred, but with
-- checking mode and an expected type like (Nat -> Nat), they become checkable.

-- Example of a case that would benefit from checking mode
ex8_needsChecking :: Term
ex8_needsChecking =
  Ann (Case (Var "x")
            "a" (Lam "y" (Var "a"))  -- unannotated lambda
            "b" (Lam "z" (Var "b"))) -- unannotated lambda
      (TyArr TyNat TyNat)
-- This requires the outer annotation because the lambdas can't be inferred

-- ============================================================================
-- Examples: Inference vs Checking Mode
-- ============================================================================

-- Example 1: Identity function (inference mode)
-- The annotated lambda can be inferred
idBoolInfer :: Term
idBoolInfer = LamAnn "x" TyBool (Var "x")
-- Can infer: Bool -> Bool

testIdBoolInfer :: Either TypeError Type
testIdBoolInfer = infer emptyCtx idBoolInfer
-- Result: Right (TyArr TyBool TyBool)

-- Example 2: Identity function (checking mode)
-- The unannotated lambda must be checked against expected type
idBoolCheck :: Term
idBoolCheck = Lam "x" (Var "x")
-- Cannot infer, must check

testIdBoolCheck :: Either TypeError ()
testIdBoolCheck = check emptyCtx idBoolCheck (TyArr TyBool TyBool)
-- Result: Right ()

-- Example 3: Application (inference mode)
-- Apply identity to true
appExample :: Term
appExample = App (LamAnn "x" TyBool (Var "x")) TmTrue
-- Can infer the result type

testAppExample :: Either TypeError Type
testAppExample = infer emptyCtx appExample
-- Result: Right TyBool

-- Example 4: Pair (checking mode)
-- Pairs need expected type to know component types
pairExample :: Term
pairExample = Pair TmTrue Zero
-- Cannot infer, must check

testPairCheck :: Either TypeError ()
testPairCheck = check emptyCtx pairExample (TyProd TyBool TyNat)
-- Result: Right ()

-- Example 5: Projection (inference mode)
-- Can infer from the pair's type
fstExample :: Term
fstExample = Fst (Ann (Pair TmTrue Zero) (TyProd TyBool TyNat))
-- Can infer: Bool

testFstExample :: Either TypeError Type
testFstExample = infer emptyCtx fstExample
-- Result: Right TyBool

-- Example 6: Sum injection (checking mode)
-- Need full sum type to know the other branch
inlExample :: Term
inlExample = Inl TmTrue
-- Cannot infer, must check

testInlCheck :: Either TypeError ()
testInlCheck = check emptyCtx inlExample (TySum TyBool TyNat)
-- Result: Right ()

-- Example 7: Let binding (mixed mode)
-- Let can infer the bound term and use it in the body
letExample :: Term
letExample = Let "x" TmTrue (If (Var "x") Zero (Suc Zero))

testLetExample :: Either TypeError Type
testLetExample = infer emptyCtx letExample
-- Result: Right TyNat

-- Example 8: Nested checking and inference
-- Complex example showing mode switching
complexExample :: Term
complexExample =
  Let "id" (LamAnn "x" TyBool (Var "x"))
      (App (Var "id") TmTrue)  -- infer app, check argument

testComplexExample :: Either TypeError Type
testComplexExample = infer emptyCtx complexExample
-- Result: Right TyBool

-- ============================================================================
-- Advanced Examples: Showing Mode Switching
-- ============================================================================

-- Example: Annotation switches from checking to inference
-- Without annotation: checking mode needed
-- With annotation: inference mode enabled
switchModeExample1 :: Term
switchModeExample1 = Ann (Lam "x" (Var "x")) (TyArr TyNat TyNat)

testSwitchMode1 :: Either TypeError Type
testSwitchMode1 = infer emptyCtx switchModeExample1
-- Result: Right (TyArr TyNat TyNat)

-- Example: Higher-order function
-- Shows inference in function position, checking in argument position
higherOrderExample :: Term
higherOrderExample =
  Let "apply" (LamAnn "f" (TyArr TyBool TyBool)
                      (LamAnn "x" TyBool
                              (App (Var "f") (Var "x"))))
      (App (App (Var "apply")
                (LamAnn "b" TyBool (Var "b")))  -- infer this
           TmTrue)  -- check this against Bool

testHigherOrder :: Either TypeError Type
testHigherOrder = infer emptyCtx higherOrderExample
-- Result: Right TyBool

-- Example: Case expression with inferred branches
caseExample :: Term
caseExample =
  Case (Ann (Inl TmTrue) (TySum TyBool TyNat))
       "x" (If (Var "x") Zero (Suc Zero))  -- infer: Nat
       "y" (Var "y")                        -- infer: Nat

testCaseExample :: Either TypeError Type
testCaseExample = infer emptyCtx caseExample
-- Result: Right TyNat

-- ============================================================================
-- Test Values for Common Patterns
-- ============================================================================

-- Boolean values
testTrue :: Term
testTrue = TmTrue

testFalse :: Term
testFalse = TmFalse

-- Natural numbers
testZero :: Term
testZero = Zero

testOne :: Term
testOne = Suc Zero

testTwo :: Term
testTwo = Suc (Suc Zero)

-- Conditional (inference mode - all branches must be inferrable)
testIf :: Term
testIf = If TmTrue Zero (Suc Zero)

-- Unit value
testUnitVal :: Term
testUnitVal = TmUnit

-- Type annotations enable inference for otherwise non-inferrable terms
testAnnotation :: Term
testAnnotation = Ann (Pair TmTrue Zero) (TyProd TyBool TyNat)

-- ============================================================================
-- Helper Functions for Testing
-- ============================================================================

-- Run a type inference check
testInfer :: Term -> IO ()
testInfer t = case infer emptyCtx t of
  Left err -> putStrLn $ "Type error: " ++ show err
  Right ty -> putStrLn $ "Inferred type: " ++ show ty

-- Run a type checking check
testCheck :: Term -> Type -> IO ()
testCheck t ty = case check emptyCtx t ty of
  Left err -> putStrLn $ "Type error: " ++ show err
  Right () -> putStrLn $ "Successfully checked against " ++ show ty

-- ============================================================================
-- Summary of Key Insights
-- ============================================================================

-- Key insight 1: Introduction forms are checked
--   - Lambdas without annotations: Lam
--   - Pairs: Pair
--   - Injections: Inl, Inr
--   - Type abstractions: TyLam

-- Key insight 2: Elimination forms are inferred
--   - Variables: Var
--   - Applications: App
--   - Projections: Fst, Snd
--   - Case expressions: Case
--   - Type applications: TyApp

-- Key insight 3: Annotations switch modes
--   - Ann switches from checking to inference
--   - LamAnn makes lambdas inferrable

-- Key insight 4: Subsumption allows checking when inference succeeds
--   - If a term can be inferred, it can also be checked
--   - The inferred type must match the expected type
