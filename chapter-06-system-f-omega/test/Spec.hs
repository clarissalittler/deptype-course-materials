{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import Parser
import Pretty
import qualified Data.Map.Strict as Map
import qualified ExerciseSpec

main :: IO ()
main = hspec $ do
  describe "Chapter 6 Exercises" ExerciseSpec.spec

  describe "Kinding System" $ do
    it "kinds base types as *" $ do
      kinding Map.empty TyBool `shouldBe` Right KStar
      kinding Map.empty TyNat `shouldBe` Right KStar

    it "kinds function types as *" $ do
      kinding Map.empty (TyArr TyBool TyNat) `shouldBe` Right KStar

    it "kinds type variables from context" $ do
      let kctx = Map.fromList [("A", KStar), ("F", KArr KStar KStar)]
      kinding kctx (TyVar "A") `shouldBe` Right KStar
      kinding kctx (TyVar "F") `shouldBe` Right (KArr KStar KStar)

    it "kinds type operators" $ do
      -- λA::*. A has kind * → *
      let tyOp = TyLam "A" KStar (TyVar "A")
      kinding Map.empty tyOp `shouldBe` Right (KArr KStar KStar)

    it "kinds nested type operators" $ do
      -- λF::* → *. λA::*. F A has kind (* → *) → * → *
      let tyOp = TyLam "F" (KArr KStar KStar)
                   (TyLam "A" KStar
                     (TyApp (TyVar "F") (TyVar "A")))
      kinding Map.empty tyOp `shouldBe`
        Right (KArr (KArr KStar KStar) (KArr KStar KStar))

    it "kinds type application" $ do
      -- (λA::*. A) Bool :: *
      let tyOp = TyLam "A" KStar (TyVar "A")
      let tyApp = TyApp tyOp TyBool
      kinding Map.empty tyApp `shouldBe` Right KStar

    it "rejects ill-kinded type application" $ do
      -- Cannot apply * to * (Bool Bool is ill-kinded)
      let tyApp = TyApp TyBool TyBool
      kinding Map.empty tyApp `shouldSatisfy` isLeft

    it "kinds forall with proper kind" $ do
      -- ∀A::*. A → A has kind *
      let ty = TyForall "A" KStar (TyArr (TyVar "A") (TyVar "A"))
      kinding Map.empty ty `shouldBe` Right KStar

  describe "Type System - System F-omega" $ do
    it "types polymorphic identity with kind annotation" $ do
      -- ΛA::*. λx:A. x : ∀A::*. A → A
      let polyId = TyAbs "A" KStar (Lam "x" (TyVar "A") (Var "x"))
      let expected = TyForall "A" KStar (TyArr (TyVar "A") (TyVar "A"))
      typeOf Map.empty Map.empty polyId `shouldBe` Right expected

    it "types identity with type operator" $ do
      -- ΛF::* → *. ΛA::*. λx:F A. x : ∀F::* → *. ∀A::*. F A → F A
      let term = TyAbs "F" (KArr KStar KStar)
                   (TyAbs "A" KStar
                     (Lam "x" (TyApp (TyVar "F") (TyVar "A")) (Var "x")))
      let expected = TyForall "F" (KArr KStar KStar)
                       (TyForall "A" KStar
                         (TyArr (TyApp (TyVar "F") (TyVar "A"))
                                (TyApp (TyVar "F") (TyVar "A"))))
      typeOf Map.empty Map.empty term `shouldBe` Right expected

    it "types const function with kind annotations" $ do
      -- ΛA::*. ΛB::*. λx:A. λy:B. x
      let polyConst = TyAbs "A" KStar
                        (TyAbs "B" KStar
                          (Lam "x" (TyVar "A")
                            (Lam "y" (TyVar "B") (Var "x"))))
      let expected = TyForall "A" KStar
                       (TyForall "B" KStar
                         (TyArr (TyVar "A") (TyArr (TyVar "B") (TyVar "A"))))
      typeOf Map.empty Map.empty polyConst `shouldBe` Right expected

    it "types type application with higher-kinded type" $ do
      -- Define List type operator: λA::*. ...some implementation
      -- For testing, we'll use a simpler example
      let kctx = Map.singleton "List" (KArr KStar KStar)
      let ty = TyApp (TyVar "List") TyBool  -- List Bool
      kinding kctx ty `shouldBe` Right KStar

  describe "Type-Level Evaluation" $ do
    it "normalizes type-level beta reduction" $ do
      -- (λA::*. A) Bool → Bool
      let tyOp = TyLam "A" KStar (TyVar "A")
      let tyApp = TyApp tyOp TyBool
      normalizeType tyApp `shouldBe` TyBool

    it "normalizes nested type applications" $ do
      -- (λA::*. λB::*. A → B) Bool Nat → Bool → Nat
      let tyOp = TyLam "A" KStar (TyLam "B" KStar (TyArr (TyVar "A") (TyVar "B")))
      let tyApp = TyApp (TyApp tyOp TyBool) TyNat
      normalizeType tyApp `shouldBe` TyArr TyBool TyNat

    it "normalizes type operators in types" $ do
      -- ∀A::*. (λB::*. B → B) A → A  normalizes to  ∀A::*. (A → A) → A
      let tyOp = TyLam "B" KStar (TyArr (TyVar "B") (TyVar "B"))
      let ty = TyForall "A" KStar
                 (TyArr (TyApp tyOp (TyVar "A")) (TyVar "A"))
      let expected = TyForall "A" KStar
                       (TyArr (TyArr (TyVar "A") (TyVar "A")) (TyVar "A"))
      normalizeType ty `shouldBe` expected

  describe "Evaluation - Terms" $ do
    it "evaluates polymorphic identity" $ do
      let polyId = TyAbs "A" KStar (Lam "x" (TyVar "A") (Var "x"))
      let term = App (TyAppTerm polyId TyBool) TmTrue
      eval term `shouldBe` TmTrue

    it "evaluates with type operators" $ do
      let polyId = TyAbs "A" KStar (Lam "x" (TyVar "A") (Var "x"))
      let term = App (TyAppTerm polyId TyNat) (TmSucc TmZero)
      eval term `shouldBe` TmSucc TmZero

  describe "Parser" $ do
    it "parses kinds" $ do
      parseKind "*" `shouldBe` Right KStar
      parseKind "* -> *" `shouldBe` Right (KArr KStar KStar)
      parseKind "* -> * -> *" `shouldBe` Right (KArr KStar (KArr KStar KStar))

    it "parses type operators" $ do
      parseType "/\\A::*. A" `shouldBe`
        Right (TyLam "A" KStar (TyVar "A"))

    it "parses type application" $ do
      parseType "F A" `shouldBe`
        Right (TyApp (TyVar "F") (TyVar "A"))

    it "parses forall with kind annotations" $ do
      parseType "forall A::*. A -> A" `shouldBe`
        Right (TyForall "A" KStar (TyArr (TyVar "A") (TyVar "A")))

    it "parses kinded type abstractions" $ do
      parseTerm "/\\A::*. \\(x:A). x" `shouldBe`
        Right (TyAbs "A" KStar (Lam "x" (TyVar "A") (Var "x")))

  describe "Pretty Printing" $ do
    it "pretty prints kinds" $ do
      prettyKind KStar `shouldBe` "*"
      prettyKind (KArr KStar KStar) `shouldBe` "* → *"

    it "pretty prints type operators" $ do
      let tyOp = TyLam "A" KStar (TyVar "A")
      prettyType tyOp `shouldBe` "λA::*. A"

    it "pretty prints type application" $ do
      let tyApp = TyApp (TyVar "F") (TyVar "A")
      prettyType tyApp `shouldBe` "F A"

    it "pretty prints kinded forall" $ do
      let ty = TyForall "A" KStar (TyArr (TyVar "A") (TyVar "A"))
      prettyType ty `shouldBe` "∀A::*. A → A"

  describe "Higher-Kinded Examples" $ do
    it "types functor-like abstraction" $ do
      -- ΛF::* → *. ΛA::*. ΛB::*. λf:A → B. λx:F A. ... (we can't implement map without more structure)
      -- But we can type the beginning
      let term = TyAbs "F" (KArr KStar KStar)
                   (TyAbs "A" KStar
                     (TyAbs "B" KStar
                       (Lam "f" (TyArr (TyVar "A") (TyVar "B"))
                         (Var "f"))))
      typeOf Map.empty Map.empty term `shouldSatisfy` isRight

-- Helper functions
isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False
