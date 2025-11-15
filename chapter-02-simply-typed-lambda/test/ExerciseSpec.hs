{-# LANGUAGE LambdaCase #-}

module ExerciseSpec (spec) where

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import qualified Solutions as S
import Control.Monad (forM_)

-- Helper to evaluate to normal form
evalToNorm :: Term -> Term
evalToNorm = eval

-- Helper to convert Nat term to Int
natToInt :: Term -> Maybe Int
natToInt TmZero = Just 0
natToInt (TmSucc n) = (+ 1) <$> natToInt n
natToInt _ = Nothing

-- Helper to check if term is boolean value
isBool :: Term -> Maybe Bool
isBool TmTrue = Just True
isBool TmFalse = Just False
isBool _ = Nothing

spec :: Spec
spec = do
  describe "Exercise 1: Arithmetic Operations" $ do
    describe "1a. Addition" $ do
      it "3 + 4 = 7" $ do
        let result = evalToNorm $ S.addNat (S.natFromInt 3) (S.natFromInt 4)
        natToInt result `shouldBe` Just 7

      it "0 + 5 = 5" $ do
        let result = evalToNorm $ S.addNat TmZero (S.natFromInt 5)
        natToInt result `shouldBe` Just 5

      it "5 + 0 = 5" $ do
        let result = evalToNorm $ S.addNat (S.natFromInt 5) TmZero
        natToInt result `shouldBe` Just 5

    describe "1b. Multiplication" $ do
      it "3 * 4 = 12" $ do
        let result = evalToNorm $ S.multNat (S.natFromInt 3) (S.natFromInt 4)
        natToInt result `shouldBe` Just 12

      it "5 * 0 = 0" $ do
        let result = evalToNorm $ S.multNat (S.natFromInt 5) TmZero
        natToInt result `shouldBe` Just 0

      it "0 * 5 = 0" $ do
        let result = evalToNorm $ S.multNat TmZero (S.natFromInt 5)
        natToInt result `shouldBe` Just 0

    describe "1c. Less Than" $ do
      it "0 < 0 is false" $ do
        let result = evalToNorm $ S.ltNat TmZero TmZero
        isBool result `shouldBe` Just False

      it "3 < 5 is true" $ do
        let result = evalToNorm $ S.ltNat (S.natFromInt 3) (S.natFromInt 5)
        isBool result `shouldBe` Just True

      it "5 < 3 is false" $ do
        let result = evalToNorm $ S.ltNat (S.natFromInt 5) (S.natFromInt 3)
        isBool result `shouldBe` Just False

      it "5 < 5 is false" $ do
        let result = evalToNorm $ S.ltNat (S.natFromInt 5) (S.natFromInt 5)
        isBool result `shouldBe` Just False

    describe "1d. Equality" $ do
      it "0 == 0 is true" $ do
        let result = evalToNorm $ S.eqNat TmZero TmZero
        isBool result `shouldBe` Just True

      it "5 == 5 is true" $ do
        let result = evalToNorm $ S.eqNat (S.natFromInt 5) (S.natFromInt 5)
        isBool result `shouldBe` Just True

      it "3 == 5 is false" $ do
        let result = evalToNorm $ S.eqNat (S.natFromInt 3) (S.natFromInt 5)
        isBool result `shouldBe` Just False

  describe "Exercise 2: Boolean Operations" $ do
    it "2a. AND: true && true = true" $
      isBool (evalToNorm $ App (App S.boolAnd TmTrue) TmTrue) `shouldBe` Just True

    it "2a. AND: true && false = false" $
      isBool (evalToNorm $ App (App S.boolAnd TmTrue) TmFalse) `shouldBe` Just False

    it "2a. AND: false && true = false" $
      isBool (evalToNorm $ App (App S.boolAnd TmFalse) TmTrue) `shouldBe` Just False

    it "2b. OR: true || false = true" $
      isBool (evalToNorm $ App (App S.boolOr TmTrue) TmFalse) `shouldBe` Just True

    it "2b. OR: false || false = false" $
      isBool (evalToNorm $ App (App S.boolOr TmFalse) TmFalse) `shouldBe` Just False

    it "2c. NOT: not true = false" $
      isBool (evalToNorm $ App S.boolNot TmTrue) `shouldBe` Just False

    it "2c. NOT: not false = true" $
      isBool (evalToNorm $ App S.boolNot TmFalse) `shouldBe` Just True

    it "2d. XOR: true XOR false = true" $
      isBool (evalToNorm $ App (App S.boolXor TmTrue) TmFalse) `shouldBe` Just True

    it "2d. XOR: true XOR true = false" $
      isBool (evalToNorm $ App (App S.boolXor TmTrue) TmTrue) `shouldBe` Just False

  describe "Exercise 3: Higher-Order Functions" $ do
    it "3a. Composition" $ do
      let succFn = Lam "x" TyNat (TmSucc (Var "x"))
      let composed = App (App (App S.compose succFn) succFn) (S.natFromInt 3)
      natToInt (evalToNorm composed) `shouldBe` Just 5

    it "3b. Twice" $ do
      let succFn = Lam "x" TyNat (TmSucc (Var "x"))
      let result = App (App S.twice succFn) (S.natFromInt 3)
      natToInt (evalToNorm result) `shouldBe` Just 5

    it "3c. Const" $ do
      let result = App (App S.constFn (S.natFromInt 5)) (S.natFromInt 10)
      natToInt (evalToNorm result) `shouldBe` Just 5

    it "3d. Flip" $ do
      let subFn = Lam "x" TyNat $ Lam "y" TyNat $
                    TmIf (TmIsZero (Var "y")) (Var "x")
                         (TmSucc (Var "x"))  -- Simplified: just adds 1 instead of recursive sub
      -- flip f 3 2
      let result = App (App (App S.flipFn subFn) (S.natFromInt 2)) (S.natFromInt 3)
      natToInt (evalToNorm result) `shouldBe` Just 4  -- f 3 2 = succ 3 = 4

  describe "Exercise 4: Conditional Expressions" $ do
    it "4a. Max: max 3 5 = 5" $ do
      let result = App (App S.maxNat (S.natFromInt 3)) (S.natFromInt 5)
      natToInt (evalToNorm result) `shouldBe` Just 5

    it "4a. Max: max 5 3 = 5" $ do
      let result = App (App S.maxNat (S.natFromInt 5)) (S.natFromInt 3)
      natToInt (evalToNorm result) `shouldBe` Just 5

    it "4b. Min: min 3 5 = 3" $ do
      let result = App (App S.minNat (S.natFromInt 3)) (S.natFromInt 5)
      natToInt (evalToNorm result) `shouldBe` Just 3

    it "4b. Min: min 5 3 = 3" $ do
      let result = App (App S.minNat (S.natFromInt 5)) (S.natFromInt 3)
      natToInt (evalToNorm result) `shouldBe` Just 3

  describe "Exercise 5: Let Bindings" $ do
    it "5a. Simple let" $ do
      let term = S.desugarLet "x" (S.natFromInt 5) TyNat (TmSucc (Var "x"))
      natToInt (evalToNorm term) `shouldBe` Just 6

    it "5b. Example let" $ do
      let result = evalToNorm S.exampleLet
      natToInt result `shouldBe` Just 5

    it "5c. Multiple let bindings" $ do
      let result = evalToNorm S.exampleLetMultiple
      natToInt result `shouldBe` Just 12

  describe "Exercise 6: Type Safety" $ do
    describe "6a. Progress" $ do
      it "Values are values" $ do
        S.demonstrateProgress TmTrue `shouldBe` S.IsValue
        S.demonstrateProgress (S.natFromInt 5) `shouldBe` S.IsValue

      it "Non-values can step" $ do
        case S.demonstrateProgress (TmSucc (TmPred (S.natFromInt 5))) of
          S.CanStep _ -> return ()
          _ -> expectationFailure "Expected to be able to step"

    describe "6b. Preservation" $ do
      it "Types are preserved" $ do
        let t = TmSucc (TmPred (S.natFromInt 5))
        S.demonstratePreservation mempty t TyNat `shouldBe` True

      it "Boolean types preserved" $ do
        let t = TmIf TmTrue TmFalse TmTrue
        S.demonstratePreservation mempty t TyBool `shouldBe` True

    describe "6c. Well-typed examples" $ do
      it "All examples type check" $ do
        forM_ S.wellTypedExamples $ \(name, term, expectedTy) ->
          case typeOf mempty term of
            Right ty -> ty `shouldBe` expectedTy
            Left err -> expectationFailure $ name ++ " failed: " ++ show err

  describe "Exercise 7: Advanced Examples" $ do
    it "7a. Factorial-like function" $ do
      natToInt (evalToNorm $ App S.fact3 TmZero) `shouldBe` Just 1
      natToInt (evalToNorm $ App S.fact3 (S.natFromInt 1)) `shouldBe` Just 1
      natToInt (evalToNorm $ App S.fact3 (S.natFromInt 2)) `shouldBe` Just 2
      natToInt (evalToNorm $ App S.fact3 (S.natFromInt 3)) `shouldBe` Just 6

    it "7b. Sign function" $ do
      natToInt (evalToNorm $ App S.sign TmZero) `shouldBe` Just 0
      natToInt (evalToNorm $ App S.sign (S.natFromInt 5)) `shouldBe` Just 1

    it "7c. Bool to Nat" $ do
      natToInt (evalToNorm $ App S.boolToNat TmTrue) `shouldBe` Just 1
      natToInt (evalToNorm $ App S.boolToNat TmFalse) `shouldBe` Just 0

    it "7d. IsEven for small numbers" $ do
      isBool (evalToNorm $ App S.isEven2 TmZero) `shouldBe` Just True
      isBool (evalToNorm $ App S.isEven2 (S.natFromInt 1)) `shouldBe` Just False
      isBool (evalToNorm $ App S.isEven2 (S.natFromInt 2)) `shouldBe` Just True

  describe "Example Programs" $ do
    it "Example 1: 3 + 4 = 7" $
      natToInt (evalToNorm S.example1) `shouldBe` Just 7

    it "Example 2: 5 == 5" $
      isBool (evalToNorm S.example2) `shouldBe` Just True

    it "Example 3: 3 < 5" $
      isBool (evalToNorm S.example3) `shouldBe` Just True

    it "Example 5: twice succ 3 = 5" $
      natToInt (evalToNorm S.example5) `shouldBe` Just 5

    it "Example 6: true && false = false" $
      isBool (evalToNorm S.example6) `shouldBe` Just False

    it "Example 7: (succ . succ) 3 = 5" $
      natToInt (evalToNorm S.example7) `shouldBe` Just 5
