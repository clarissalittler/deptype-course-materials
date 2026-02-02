{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import TypeCheck

main :: IO ()
main = hspec $ do
  describe "Universe and Pi/Sigma" $ do
    it "Type 0 has type Type 1" $
      typeOf emptyCtx (Universe 0) `shouldBe` Right (Universe 1)

    it "Pi lives in a universe" $ do
      typeOf emptyCtx (Pi "x" Nat Nat) `shouldBe` Right (Universe 0)

    it "Sigma lives in a universe" $ do
      typeOf emptyCtx (Sigma "x" Nat Nat) `shouldBe` Right (Universe 0)

  describe "Bidirectional core" $ do
    it "lambda checks against Pi" $ do
      let term = Lam "x" Nat (Var "x")
      typeCheck emptyCtx term (Pi "x" Nat Nat) `shouldBe` Right ()

    it "lambda does not infer" $ do
      let term = Lam "x" Nat (Var "x")
      typeOf emptyCtx term `shouldSatisfy` isCannotInfer

    it "application infers when function type is known" $ do
      let ctx = extendCtx "id" (Pi "x" Nat Nat) emptyCtx
      typeOf ctx (App (Var "id") Zero) `shouldBe` Right Nat

    it "pair checks against Sigma with dependency" $ do
      let ty = Sigma "x" Nat (Eq Nat (Var "x") (Var "x"))
      let term = Pair Zero (Refl Zero)
      typeCheck emptyCtx term ty `shouldBe` Right ()

    it "pair does not infer" $ do
      let term = Pair Zero Zero
      typeOf emptyCtx term `shouldSatisfy` isCannotInfer

  describe "Equality types" $ do
    it "Eq Nat 0 0 is a type" $
      typeOf emptyCtx (Eq Nat Zero Zero) `shouldBe` Right (Universe 0)

    it "refl 0 has type Eq Nat 0 0" $
      typeOf emptyCtx (Refl Zero) `shouldBe` Right (Eq Nat Zero Zero)

  describe "Unsupported constructs" $ do
    it "natElim is not supported" $ do
      let p = Lam "n" Nat Nat
      let z = Zero
      let s = Lam "k" Nat (Lam "rec" Nat (Succ (Var "rec")))
      typeOf emptyCtx (NatElim p z s Zero) `shouldSatisfy` isNotSupported

    it "match is not supported" $ do
      typeOf emptyCtx (Match Zero []) `shouldSatisfy` isNotSupported

-- Helpers
isCannotInfer :: Either TypeError Term -> Bool
isCannotInfer (Left (CannotInfer _)) = True
isCannotInfer _ = False

isNotSupported :: Either TypeError Term -> Bool
isNotSupported (Left (NotSupported _)) = True
isNotSupported _ = False
