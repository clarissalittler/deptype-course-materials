{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Hspec

import qualified Data.Set as Set

import Syntax
import TypeCheck
import Eval
import Parser
import Pretty

main :: IO ()
main = hspec $ do
  describe "Syntax" $ do
    describe "freeVars" $ do
      it "finds free variable in Var" $
        freeVars (Var "x") `shouldBe` Set.singleton "x"

      it "removes bound variable in lambda" $
        freeVars (Lam "x" TyNat (Var "x")) `shouldBe` Set.empty

      it "finds free in lambda body" $
        freeVars (Lam "x" TyNat (Var "y")) `shouldBe` Set.singleton "y"

    describe "isGround" $ do
      it "Bool is ground" $
        isGround TyBool `shouldBe` True

      it "Nat is ground" $
        isGround TyNat `shouldBe` True

      it "? -> ? is ground" $
        isGround (TyFun TyDyn TyDyn) `shouldBe` True

      it "Nat -> Bool is not ground" $
        isGround (TyFun TyNat TyBool) `shouldBe` False

      it "? is not ground" $
        isGround TyDyn `shouldBe` False

  describe "Consistency" $ do
    describe "consistent" $ do
      it "? is consistent with anything" $ do
        consistent TyDyn TyBool `shouldBe` True
        consistent TyDyn TyNat `shouldBe` True
        consistent TyDyn (TyFun TyNat TyBool) `shouldBe` True

      it "anything is consistent with ?" $ do
        consistent TyBool TyDyn `shouldBe` True
        consistent TyNat TyDyn `shouldBe` True
        consistent (TyFun TyNat TyBool) TyDyn `shouldBe` True

      it "same base types are consistent" $ do
        consistent TyBool TyBool `shouldBe` True
        consistent TyNat TyNat `shouldBe` True

      it "different base types are not consistent" $
        consistent TyBool TyNat `shouldBe` False

      it "function types consistent componentwise" $ do
        consistent (TyFun TyNat TyBool) (TyFun TyNat TyBool) `shouldBe` True
        consistent (TyFun TyDyn TyBool) (TyFun TyNat TyBool) `shouldBe` True
        consistent (TyFun TyNat TyDyn) (TyFun TyNat TyBool) `shouldBe` True

      it "incompatible function types not consistent" $
        consistent (TyFun TyNat TyBool) (TyFun TyBool TyNat) `shouldBe` False

    describe "meet" $ do
      it "meet with ? is the other type" $ do
        meet TyDyn TyBool `shouldBe` Just TyBool
        meet TyNat TyDyn `shouldBe` Just TyNat

      it "meet of same type is that type" $
        meet TyBool TyBool `shouldBe` Just TyBool

      it "meet of different base types is Nothing" $
        meet TyBool TyNat `shouldBe` Nothing

  describe "TypeCheck" $ do
    describe "Basic typing" $ do
      it "types true as Bool" $
        typeCheck TmTrue `shouldBe` Right TyBool

      it "types zero as Nat" $
        typeCheck TmZero `shouldBe` Right TyNat

      it "types unit as Unit" $
        typeCheck TmUnit `shouldBe` Right TyUnit

    describe "Lambda and application" $ do
      it "types identity function" $
        typeCheck (Lam "x" TyNat (Var "x"))
          `shouldBe` Right (TyFun TyNat TyNat)

      it "types dynamic identity" $
        typeCheck (Lam "x" TyDyn (Var "x"))
          `shouldBe` Right (TyFun TyDyn TyDyn)

      it "types application with dynamic" $ do
        let term = App (Lam "x" TyDyn (Var "x")) TmZero
        typeCheck term `shouldBe` Right TyDyn

      it "types dynamic function application" $ do
        let term = App (Lam "f" TyDyn (App (Var "f") TmZero))
                       (Lam "x" TyNat (TmSucc (Var "x")))
        typeCheck term `shouldSatisfy` isRight

      it "rejects inconsistent types" $ do
        let term = App (Lam "x" TyBool (Var "x")) TmZero
        typeCheck term `shouldSatisfy` isLeft

    describe "Conditionals" $ do
      it "types if with consistent condition" $
        typeCheck (TmIf TmTrue TmZero (TmSucc TmZero))
          `shouldBe` Right TyNat

      it "accepts dynamic condition" $ do
        let term = Lam "x" TyDyn (TmIf (Var "x") TmZero TmZero)
        typeCheck term `shouldSatisfy` isRight

    describe "Let binding" $ do
      it "types let binding" $
        typeCheck (TmLet "x" TmZero (TmSucc (Var "x")))
          `shouldBe` Right TyNat

    describe "Ascription" $ do
      it "accepts consistent ascription" $
        typeCheck (TmAscribe TmZero TyNat)
          `shouldBe` Right TyNat

      it "accepts dynamic ascription" $
        typeCheck (TmAscribe TmZero TyDyn)
          `shouldBe` Right TyDyn

      it "rejects inconsistent ascription" $
        typeCheck (TmAscribe TmTrue TyNat)
          `shouldSatisfy` isLeft

  describe "Evaluation" $ do
    describe "isValue" $ do
      it "lambda is value" $
        isValue (Lam "x" TyNat (Var "x")) `shouldBe` True

      it "true is value" $
        isValue TmTrue `shouldBe` True

      it "zero is value" $
        isValue TmZero `shouldBe` True

    describe "eval" $ do
      it "evaluates identity application" $
        eval (App (Lam "x" TyNat (Var "x")) TmZero) `shouldBe` TmZero

      it "evaluates if true" $
        eval (TmIf TmTrue TmZero (TmSucc TmZero)) `shouldBe` TmZero

      it "evaluates let binding" $
        eval (TmLet "x" (TmSucc TmZero) (Var "x")) `shouldBe` TmSucc TmZero

      it "evaluates pred (succ 0)" $
        eval (TmPred (TmSucc TmZero)) `shouldBe` TmZero

  describe "Parser" $ do
    describe "parseTerm" $ do
      it "parses true" $
        parseTerm "true" `shouldBe` Right TmTrue

      it "parses false" $
        parseTerm "false" `shouldBe` Right TmFalse

      it "parses 0" $
        parseTerm "0" `shouldBe` Right TmZero

      it "parses lambda with dynamic type" $
        parseTerm "\\x : ?. x" `shouldBe`
          Right (Lam "x" TyDyn (Var "x"))

      it "parses ascription" $
        parseTerm "x : Nat" `shouldBe`
          Right (TmAscribe (Var "x") TyNat)

    describe "parseType" $ do
      it "parses ?" $
        parseType "?" `shouldBe` Right TyDyn

      it "parses Bool" $
        parseType "Bool" `shouldBe` Right TyBool

      it "parses function with dynamic" $
        parseType "? -> Nat" `shouldBe` Right (TyFun TyDyn TyNat)

  describe "Pretty" $ do
    describe "prettyTerm" $ do
      it "prints true" $
        prettyTerm TmTrue `shouldBe` "true"

      it "prints lambda" $
        prettyTerm (Lam "x" TyDyn (Var "x"))
          `shouldBe` "λx : ?. x"

    describe "prettyType" $ do
      it "prints dynamic type" $
        prettyType TyDyn `shouldBe` "?"

      it "prints function with dynamic" $
        prettyType (TyFun TyDyn TyNat) `shouldBe` "? -> Nat"

  describe "Cast Insertion" $ do
    it "inserts no casts for pure term" $ do
      let term = Lam "x" TyNat (Var "x")
      insertCasts emptyContext term `shouldBe` Right term

    it "inserts cast for dynamic application" $ do
      let term = App (Lam "x" TyDyn (Var "x")) TmZero
      case insertCasts emptyContext term of
        Right (App _ (TmCast _ TyNat TyDyn _)) -> return ()
        Right t -> expectationFailure $ "Expected cast, got: " ++ prettyTerm t
        Left err -> expectationFailure $ "Error: " ++ show err

-- Helpers
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False
