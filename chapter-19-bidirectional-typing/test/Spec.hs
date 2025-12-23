{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import Parser

main :: IO ()
main = hspec $ do
  describe "Bidirectional Type Checking" $ do
    describe "Inference (⇒)" $ do
      it "infers variable types" $ do
        let ctx = extendCtx "x" TyBool emptyCtx
        infer ctx (Var "x") `shouldBe` Right TyBool

      it "infers annotated lambda" $ do
        let term = LamAnn "x" TyBool (Var "x")
        infer emptyCtx term `shouldBe` Right (TyArr TyBool TyBool)

      it "infers application" $ do
        let f = LamAnn "x" TyNat (Var "x")
            term = App f Zero
        infer emptyCtx term `shouldBe` Right TyNat

      it "infers annotation" $ do
        let term = Ann (Lam "x" (Var "x")) (TyArr TyBool TyBool)
        infer emptyCtx term `shouldBe` Right (TyArr TyBool TyBool)

      it "infers true/false" $ do
        infer emptyCtx TmTrue `shouldBe` Right TyBool
        infer emptyCtx TmFalse `shouldBe` Right TyBool

      it "infers if-then-else" $ do
        let term = If TmTrue Zero (Suc Zero)
        infer emptyCtx term `shouldBe` Right TyNat

      it "infers natural numbers" $ do
        infer emptyCtx Zero `shouldBe` Right TyNat
        infer emptyCtx (Suc Zero) `shouldBe` Right TyNat

      it "infers fst/snd" $ do
        let pair = Ann (Pair TmTrue Zero) (TyProd TyBool TyNat)
        infer emptyCtx (Fst pair) `shouldBe` Right TyBool
        infer emptyCtx (Snd pair) `shouldBe` Right TyNat

      it "infers let binding" $ do
        let term = Let "x" TmTrue (If (Var "x") Zero (Suc Zero))
        infer emptyCtx term `shouldBe` Right TyNat

    describe "Checking (⇐)" $ do
      it "checks lambda against function type" $ do
        let term = Lam "x" (Var "x")
        check emptyCtx term (TyArr TyBool TyBool) `shouldBe` Right ()

      it "checks nested lambda" $ do
        let term = Lam "x" (Lam "y" (Var "x"))
        check emptyCtx term (TyArr TyBool (TyArr TyNat TyBool)) `shouldBe` Right ()

      it "checks pair against product type" $ do
        let term = Pair TmTrue Zero
        check emptyCtx term (TyProd TyBool TyNat) `shouldBe` Right ()

      it "checks inl against sum type" $ do
        let term = Inl TmTrue
        check emptyCtx term (TySum TyBool TyNat) `shouldBe` Right ()

      it "checks inr against sum type" $ do
        let term = Inr Zero
        check emptyCtx term (TySum TyBool TyNat) `shouldBe` Right ()

      it "fails on type mismatch" $ do
        let term = Lam "x" (Var "x")
        check emptyCtx term TyBool `shouldSatisfy` isLeft

    describe "Polymorphism" $ do
      it "infers type application" $ do
        let polyId = Ann (TyLam "a" (Lam "x" (Var "x")))
                         (TyForall "a" (TyArr (TyVar "a") (TyVar "a")))
            term = TyApp polyId TyBool
        infer emptyCtx term `shouldBe` Right (TyArr TyBool TyBool)

      it "checks type abstraction" $ do
        let term = TyLam "a" (Lam "x" (Var "x"))
            ty = TyForall "a" (TyArr (TyVar "a") (TyVar "a"))
        check emptyCtx term ty `shouldBe` Right ()

    describe "Error Cases" $ do
      it "rejects unbound variable" $ do
        infer emptyCtx (Var "x") `shouldBe` Left (UnboundVariable "x")

      it "rejects non-function application" $ do
        infer emptyCtx (App TmTrue TmFalse) `shouldBe` Left (ExpectedFunction TyBool)

      it "cannot infer unannotated lambda" $ do
        case infer emptyCtx (Lam "x" (Var "x")) of
          Left (CannotInfer _) -> return ()
          other -> expectationFailure $ "Expected CannotInfer, got: " ++ show other

  describe "Evaluation" $ do
    it "evaluates identity" $ do
      let term = App (LamAnn "x" TyBool (Var "x")) TmTrue
      evalClosed term `shouldBe` VBool True

    it "evaluates if-then-else" $ do
      evalClosed (If TmTrue Zero (Suc Zero)) `shouldBe` VNat 0
      evalClosed (If TmFalse Zero (Suc Zero)) `shouldBe` VNat 1

    it "evaluates pairs" $ do
      let pair = Pair TmTrue (Suc Zero)
      evalClosed (Fst pair) `shouldBe` VBool True
      evalClosed (Snd pair) `shouldBe` VNat 1

    it "evaluates case" $ do
      let term = Case (Inl TmTrue) "x" (If (Var "x") Zero (Suc Zero)) "y" (Var "y")
      evalClosed term `shouldBe` VNat 0

  describe "Parser" $ do
    it "parses lambda" $ do
      parseTerm "\\x. x" `shouldBe` Right (Lam "x" (Var "x"))

    it "parses annotated lambda" $ do
      parseTerm "\\(x : Bool). x" `shouldBe` Right (LamAnn "x" TyBool (Var "x"))

    it "parses annotation" $ do
      parseTerm "(\\x. x : Bool -> Bool)"
        `shouldBe` Right (Ann (Lam "x" (Var "x")) (TyArr TyBool TyBool))

    it "parses type application" $ do
      parseTerm "f [Bool]" `shouldBe` Right (TyApp (Var "f") TyBool)

    it "parses forall type" $ do
      parseType "forall a. a -> a"
        `shouldBe` Right (TyForall "a" (TyArr (TyVar "a") (TyVar "a")))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False
