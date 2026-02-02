{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import Parser
import Pretty

main :: IO ()
main = hspec $ do
  describe "Dependent Type System - Basic" $ do
    it "Type has type Type" $ do
      typeOf emptyCtx Type `shouldBe` Right Type

    it "types variables from context" $ do
      let ctx = extendCtx "x" Nat emptyCtx
      typeOf ctx (Var "x") `shouldBe` Right Nat

    it "types lambda with simple type" $ do
      -- λ(x:Nat). x : Nat → Nat
      let term = Lam "x" Nat (Var "x")
      typeOf emptyCtx term `shouldBe` Right (Pi "x" Nat Nat)

    it "types application" $ do
      -- (λ(x:Nat). x) 0 : Nat
      let term = App (Lam "x" Nat (Var "x")) Zero
      typeOf emptyCtx term `shouldBe` Right Nat

  describe "Dependent Function Types (Pi)" $ do
    it "simple function type is a Pi type" $ do
      -- Nat → Nat is sugar for Π(x:Nat). Nat
      let piType = Pi "x" Nat Nat
      typeOf emptyCtx piType `shouldBe` Right Type

    it "dependent function type" $ do
      -- Π(n:Nat). Vec n where Vec is a type family
      -- For testing, we'll use Π(n:Nat). Nat (simpler)
      let depFun = Pi "n" Nat Nat
      typeOf emptyCtx depFun `shouldBe` Right Type

    it "types identity function polymorphically" $ do
      -- λ(A:Type). λ(x:A). x : Π(A:Type). A → A
      let polyId = Lam "A" Type (Lam "x" (Var "A") (Var "x"))
      let expected = Pi "A" Type (Pi "x" (Var "A") (Var "A"))
      typeOf emptyCtx polyId `shouldBe` Right expected

    it "applies polymorphic identity to Nat" $ do
      -- (λ(A:Type). λ(x:A). x) Nat : Nat → Nat
      let polyId = Lam "A" Type (Lam "x" (Var "A") (Var "x"))
      let applied = App polyId Nat
      typeOf emptyCtx applied `shouldBe` Right (Pi "x" Nat Nat)

    it "applies polymorphic identity twice" $ do
      -- ((λ(A:Type). λ(x:A). x) Nat) 0 : Nat
      let polyId = Lam "A" Type (Lam "x" (Var "A") (Var "x"))
      let term = App (App polyId Nat) Zero
      typeOf emptyCtx term `shouldBe` Right Nat

  describe "Dependent Pair Types (Sigma)" $ do
    it "sigma type is well-typed" $ do
      -- Σ(x:Nat). Nat : Type
      let sigmaType = Sigma "x" Nat Nat
      typeOf emptyCtx sigmaType `shouldBe` Right Type

    it "pair has sigma type" $ do
      -- (0, 1) : Σ(x:Nat). Nat
      let pair = Pair Zero (Succ Zero)
      typeOf emptyCtx pair `shouldSatisfy` isRight

    it "first projection of pair" $ do
      -- fst (0, 1) evaluates to 0
      let pair = Pair Zero (Succ Zero)
      eval (Fst pair) `shouldBe` Zero

    it "second projection of pair" $ do
      -- snd (0, 1) evaluates to 1
      let pair = Pair Zero (Succ Zero)
      eval (Snd pair) `shouldBe` Succ Zero

    it "types first projection" $ do
      -- Given p : Σ(x:Nat). Nat, fst p : Nat
      let ctx = extendCtx "p" (Sigma "x" Nat Nat) emptyCtx
      typeOf ctx (Fst (Var "p")) `shouldBe` Right Nat

    it "types second projection" $ do
      -- Given p : Σ(x:Nat). Nat, snd p : Nat
      let ctx = extendCtx "p" (Sigma "x" Nat Nat) emptyCtx
      typeOf ctx (Snd (Var "p")) `shouldBe` Right Nat

  describe "Evaluation" $ do
    it "evaluates beta reduction" $ do
      -- (λ(x:Nat). x) 0 ⟶ 0
      let term = App (Lam "x" Nat (Var "x")) Zero
      eval term `shouldBe` Zero

    it "evaluates nested applications" $ do
      -- (λ(x:Nat). λ(y:Nat). x) 0 1 ⟶ 0
      let term = App (App (Lam "x" Nat (Lam "y" Nat (Var "x"))) Zero) (Succ Zero)
      eval term `shouldBe` Zero

    it "evaluates pair projections" $ do
      -- fst (0, 1) ⟶ 0
      -- snd (0, 1) ⟶ 1
      let pair = Pair Zero (Succ Zero)
      eval (Fst pair) `shouldBe` Zero
      eval (Snd pair) `shouldBe` Succ Zero

    it "evaluates if-then-else" $ do
      eval (If TmTrue Zero (Succ Zero)) `shouldBe` Zero
      eval (If TmFalse Zero (Succ Zero)) `shouldBe` Succ Zero

  describe "Type Normalization" $ do
    it "normalizes application in types" $ do
      -- (λ(A:Type). A) Nat ≡ Nat
      let ty = App (Lam "A" Type (Var "A")) Nat
      normalize ty `shouldBe` Nat

    it "normalizes nested type applications" $ do
      -- (λ(A:Type). λ(B:Type). A) Nat Bool ≡ Nat
      let ty = App (App (Lam "A" Type (Lam "B" Type (Var "A"))) Nat) Bool
      normalize ty `shouldBe` Nat

  describe "Parser" $ do
    it "parses Type" $ do
      parseTerm "Type" `shouldBe` Right Type

    it "parses variables" $ do
      parseTerm "x" `shouldBe` Right (Var "x")

    it "parses lambda" $ do
      parseTerm "\\(x:Nat). x" `shouldBe` Right (Lam "x" Nat (Var "x"))

    it "parses application" $ do
      parseTerm "f x" `shouldBe` Right (App (Var "f") (Var "x"))

    it "parses Pi type with symbol" $ do
      parseTerm "Pi(x:Nat). Nat" `shouldBe` Right (Pi "x" Nat Nat)

    it "parses Pi type with binder arrow sugar" $ do
      parseTerm "Pi(x:Nat). Nat" `shouldBe` Right (Pi "x" Nat Nat)

    it "parses non-dependent arrow sugar" $ do
      parseTerm "Nat -> Nat" `shouldBe` Right (Pi "_" Nat Nat)

    it "parses Sigma type" $ do
      parseTerm "Sigma(x:Nat). Nat" `shouldBe` Right (Sigma "x" Nat Nat)

    it "parses pairs" $ do
      parseTerm "(zero, succ zero)" `shouldBe` Right (Pair Zero (Succ Zero))

    it "parses numeric literal 0" $ do
      parseTerm "0" `shouldBe` Right Zero

    it "parses projections" $ do
      parseTerm "fst p" `shouldBe` Right (Fst (Var "p"))
      parseTerm "snd p" `shouldBe` Right (Snd (Var "p"))

  describe "Pretty Printing" $ do
    it "pretty prints Type" $ do
      pretty Type `shouldBe` "Type"

    it "pretty prints lambda" $ do
      pretty (Lam "x" Nat (Var "x")) `shouldBe` "λ(x:Nat). x"

    it "pretty prints Pi type" $ do
      pretty (Pi "x" Nat Nat) `shouldBe` "Nat → Nat"

    it "pretty prints dependent Pi type" $ do
      pretty (Pi "x" Nat (Var "x")) `shouldBe` "Π(x:Nat). x"

    it "pretty prints Sigma type" $ do
      pretty (Sigma "x" Nat Nat) `shouldBe` "Σ(x:Nat). Nat"

    it "pretty prints pairs" $ do
      pretty (Pair Zero (Succ Zero)) `shouldBe` "(0, 1)"

  describe "Advanced Examples" $ do
    it "const function" $ do
      -- λ(A:Type). λ(B:Type). λ(x:A). λ(y:B). x
      let constFun = Lam "A" Type
                       (Lam "B" Type
                         (Lam "x" (Var "A")
                           (Lam "y" (Var "B") (Var "x"))))
      typeOf emptyCtx constFun `shouldSatisfy` isRight

    it "applies const function" $ do
      -- const Nat Bool 0 true ⟶ 0
      let constFun = Lam "A" Type
                       (Lam "B" Type
                         (Lam "x" (Var "A")
                           (Lam "y" (Var "B") (Var "x"))))
      let term = App (App (App (App constFun Nat) Bool) Zero) TmTrue
      eval term `shouldBe` Zero

    it "swap function for pairs" $ do
      -- λ(p:Σ(x:Nat). Nat). (snd p, fst p)
      let swapFun = Lam "p" (Sigma "x" Nat Nat)
                      (Pair (Snd (Var "p")) (Fst (Var "p")))
      typeOf emptyCtx swapFun `shouldSatisfy` isRight

-- Helper functions
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False
