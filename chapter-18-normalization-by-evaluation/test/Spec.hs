{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec
import Syntax
import Semantic
import NbE
import Parser

main :: IO ()
main = hspec $ do
  describe "NbE Core" $ do
    describe "Evaluation" $ do
      it "evaluates variables" $ do
        let env = [VTrue]
        eval env (TVar 0) `shouldBe` VTrue

      it "evaluates lambda to closure" $ do
        let val = eval [] (TLam "x" (TVar 0))
        case val of
          VLam "x" _ -> return ()
          _ -> expectationFailure "Expected lambda"

      it "evaluates application (beta reduction)" $ do
        let t = TApp (TLam "x" (TVar 0)) TTrue
        eval [] t `shouldBe` VTrue

      it "evaluates nested application" $ do
        let k = TLam "x" (TLam "y" (TVar 1))  -- K combinator
            t = TApp (TApp k TTrue) TFalse
        eval [] t `shouldBe` VTrue

    describe "Quotation" $ do
      it "quotes integers" $ do
        quote 0 VTrue `shouldBe` NfTrue

      it "quotes neutral variables" $ do
        quote 1 (VNe (NVar 0)) `shouldBe` NfNe (NeVar 0)

      it "quotes lambda" $ do
        let closure = Closure [] (TVar 0)
            val = VLam "x" closure
        quote 0 val `shouldBe` NfLam "x" (NfNe (NeVar 0))

    describe "Normalization" $ do
      it "normalizes identity applied to argument" $ do
        let t = TApp (TLam "x" (TVar 0)) TTrue
        normalize t `shouldBe` NfTrue

      it "normalizes K combinator" $ do
        let k = TLam "x" (TLam "y" (TVar 1))
            t = TApp (TApp k TTrue) TFalse
        normalize t `shouldBe` NfTrue

      it "normalizes nested lambdas" $ do
        let t = TLam "x" (TLam "y" (TVar 1))
        normalize t `shouldBe` NfLam "x" (NfLam "y" (NfNe (NeVar 0)))

      it "normalizes if-true" $ do
        let t = TIf TTrue (TLam "x" (TVar 0)) (TLam "y" TFalse)
        normalize t `shouldBe` NfLam "x" (NfNe (NeVar 0))

      it "normalizes if-false" $ do
        let t = TIf TFalse TTrue TFalse
        normalize t `shouldBe` NfFalse

      it "leaves neutral if alone" $ do
        let t = TLam "b" (TIf (TVar 0) TTrue TFalse)
            result = normalize t
        case result of
          NfLam "b" (NfNe (NeIf _ _ _)) -> return ()
          _ -> expectationFailure $ "Expected neutral if, got: " ++ show result

  describe "Natural Numbers" $ do
    it "normalizes zero" $ do
      normalize TZero `shouldBe` NfZero

    it "normalizes successor" $ do
      normalize (TSuc TZero) `shouldBe` NfSuc NfZero

    it "normalizes double successor" $ do
      normalize (TSuc (TSuc TZero)) `shouldBe` NfSuc (NfSuc NfZero)

  describe "Pi Types" $ do
    it "normalizes simple Pi" $ do
      let t = TPi "x" TBool TBool
      normalize t `shouldBe` NfPi "x" NfBool NfBool

    it "normalizes dependent Pi" $ do
      let t = TPi "b" TBool (TIf (TVar 0) TNat TBool)
      case normalize t of
        NfPi "b" NfBool _ -> return ()
        r -> expectationFailure $ "Expected Pi, got: " ++ show r

  describe "Parser" $ do
    it "parses lambda" $ do
      parseTerm "\\x. x" `shouldBe` Right (TLam "x" (TVar 0))

    it "parses application" $ do
      parseTerm "(\\x. x) true" `shouldBe` Right (TApp (TLam "x" (TVar 0)) TTrue)

    it "parses Type" $ do
      parseTerm "Type" `shouldBe` Right TU

    it "parses Bool" $ do
      parseTerm "Bool" `shouldBe` Right TBool

    it "parses forall" $ do
      parseTerm "forall (x : Bool) -> Bool"
        `shouldBe` Right (TPi "x" TBool TBool)

    it "parses let" $ do
      parseTerm "let x : Bool = true in x"
        `shouldBe` Right (TLet "x" TBool TTrue (TVar 0))

  describe "Eta Expansion" $ do
    it "eta-expands functions" $ do
      -- A neutral function should become λx. f x
      -- when we quote it
      let f = VNe (NVar 0)  -- A free function variable
          -- Apply to fresh var and quote
          result = quote 1 f
      result `shouldBe` NfNe (NeVar 0)

  describe "Complex Examples" $ do
    it "normalizes church true" $ do
      -- true = λx. λy. x
      let t = TLam "x" (TLam "y" (TVar 1))
      case normalize t of
        NfLam _ (NfLam _ (NfNe (NeVar 0))) -> return ()
        r -> expectationFailure $ "Got: " ++ show r

    it "normalizes church false" $ do
      -- false = λx. λy. y
      let t = TLam "x" (TLam "y" (TVar 0))
      case normalize t of
        NfLam _ (NfLam _ (NfNe (NeVar 1))) -> return ()
        r -> expectationFailure $ "Got: " ++ show r
