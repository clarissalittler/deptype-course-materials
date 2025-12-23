{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec
import Syntax
import Domain
import Denotation
import Parser
import Pretty

main :: IO ()
main = hspec $ do
  describe "Denotational Semantics" $ do
    describe "Basic Values" $ do
      it "denotes true" $ do
        denoteClosed TmTrue `shouldBe` DBool True

      it "denotes false" $ do
        denoteClosed TmFalse `shouldBe` DBool False

      it "denotes zero" $ do
        denoteClosed Zero `shouldBe` DNat 0

      it "denotes successor" $ do
        denoteClosed (Suc Zero) `shouldBe` DNat 1
        denoteClosed (Suc (Suc Zero)) `shouldBe` DNat 2

      it "denotes unit" $ do
        denoteClosed TmUnit `shouldBe` DUnit

    describe "Conditional" $ do
      it "evaluates then branch on true" $ do
        let term = If TmTrue Zero (Suc Zero)
        denoteClosed term `shouldBe` DNat 0

      it "evaluates else branch on false" $ do
        let term = If TmFalse Zero (Suc Zero)
        denoteClosed term `shouldBe` DNat 1

    describe "Functions" $ do
      it "applies identity function" $ do
        let term = App (Lam "x" TyNat (Var "x")) (Suc Zero)
        denoteClosed term `shouldBe` DNat 1

      it "applies constant function" $ do
        let term = App (App (Lam "x" TyNat (Lam "y" TyNat (Var "x"))) Zero) (Suc Zero)
        denoteClosed term `shouldBe` DNat 0

    describe "Let Binding" $ do
      it "binds and uses variable" $ do
        let term = Let "x" (Suc Zero) (Suc (Var "x"))
        denoteClosed term `shouldBe` DNat 2

    describe "Predecessor" $ do
      it "pred 0 = 0" $ do
        denoteClosed (Pred Zero) `shouldBe` DNat 0

      it "pred (suc n) = n" $ do
        denoteClosed (Pred (Suc (Suc Zero))) `shouldBe` DNat 1

    describe "IsZero" $ do
      it "iszero 0 = true" $ do
        denoteClosed (IsZero Zero) `shouldBe` DBool True

      it "iszero (suc n) = false" $ do
        denoteClosed (IsZero (Suc Zero)) `shouldBe` DBool False

    describe "NatRec (Primitive Recursion)" $ do
      it "natrec z s 0 = z" $ do
        let term = NatRec Zero (Lam "n" TyNat (Lam "r" TyNat (Suc (Var "r")))) Zero
        denoteClosed term `shouldBe` DNat 0

      it "natrec computes double" $ do
        -- double n = natrec 0 (\_ r. suc (suc r)) n
        let double n = NatRec Zero
              (Lam "_" TyNat (Lam "r" TyNat (Suc (Suc (Var "r")))))
              n
        denoteClosed (double (Suc (Suc Zero))) `shouldBe` DNat 4

    describe "Fixed Point" $ do
      it "fix creates a function value" $ do
        -- The type of fix f is a function, so we just check it evaluates
        let term = Fix (Lam "f" (TyArr TyNat TyNat) (Lam "x" TyNat (Var "x")))
        case denoteClosed term of
          DFun _ -> True `shouldBe` True
          _ -> expectationFailure "Expected function"

    describe "Fixed Point Approximation (Domain module)" $ do
      it "shows chain of approximations" $ do
        -- For the function f(x) = 0, the chain is:
        -- f^0(⊥) = ⊥, f^1(⊥) = 0, f^2(⊥) = 0, ...
        let f _ = DNat 0
        fixN 0 f `shouldBe` DBottom
        fixN 1 f `shouldBe` DNat 0
        fixN 2 f `shouldBe` DNat 0

  describe "Domain Operations" $ do
    it "bottom approximates everything" $ do
      approx DBottom (DNat 0) `shouldBe` True
      approx DBottom (DBool True) `shouldBe` True

    it "values only approximate themselves" $ do
      approx (DNat 1) (DNat 1) `shouldBe` True
      approx (DNat 1) (DNat 2) `shouldBe` False

  describe "Parser" $ do
    it "parses numbers" $ do
      parseTerm "5" `shouldBe` Right (Suc (Suc (Suc (Suc (Suc Zero)))))

    it "parses lambda" $ do
      parseTerm "\\(x : Nat). x" `shouldBe` Right (Lam "x" TyNat (Var "x"))

    it "parses fix" $ do
      parseTerm "fix f" `shouldBe` Right (Fix (Var "f"))

    it "parses application" $ do
      parseTerm "f x y" `shouldBe` Right (App (App (Var "f") (Var "x")) (Var "y"))

    it "parses if-then-else" $ do
      parseTerm "if true then 0 else 1"
        `shouldBe` Right (If TmTrue Zero (Suc Zero))

    it "parses let" $ do
      parseTerm "let x = 1 in suc x"
        `shouldBe` Right (Let "x" (Suc Zero) (Suc (Var "x")))

    it "parses type" $ do
      parseType "Nat -> Bool -> Nat"
        `shouldBe` Right (TyArr TyNat (TyArr TyBool TyNat))

  describe "Pretty Printing" $ do
    it "pretty prints domains" $ do
      prettyDom (DNat 42) `shouldBe` "42"
      prettyDom (DBool True) `shouldBe` "true"
      prettyDom DBottom `shouldBe` "⊥"
