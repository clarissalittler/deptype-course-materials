{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import Parser
import Pretty
import qualified ExerciseSpec

main :: IO ()
main = hspec $ do
  describe "Chapter 5 Exercises" ExerciseSpec.spec
  describe "System F - Type System" $ do
    it "types polymorphic identity" $ do
      -- ΛA. λx:A. x : ∀A. A → A
      let polyId = TyAbs "A" (Lam "x" (TyVar "A") (Var "x"))
      typeCheck polyId `shouldBe` Right (TyForall "A" (TyArr (TyVar "A") (TyVar "A")))

    it "types identity on Bool" $ do
      -- (ΛA. λx:A. x) [Bool] true : Bool
      let polyId = TyAbs "A" (Lam "x" (TyVar "A") (Var "x"))
      let term = App (TyApp polyId TyBool) TmTrue
      typeCheck term `shouldBe` Right TyBool

    it "types identity on Nat" $ do
      let polyId = TyAbs "A" (Lam "x" (TyVar "A") (Var "x"))
      let term = App (TyApp polyId TyNat) TmZero
      typeCheck term `shouldBe` Right TyNat

    it "types const function" $ do
      -- ΛA. ΛB. λx:A. λy:B. x : ∀A. ∀B. A → B → A
      let polyConst = TyAbs "A" (TyAbs "B"
                        (Lam "x" (TyVar "A")
                          (Lam "y" (TyVar "B") (Var "x"))))
      typeCheck polyConst `shouldBe`
        Right (TyForall "A" (TyForall "B"
                (TyArr (TyVar "A") (TyArr (TyVar "B") (TyVar "A")))))

  describe "System F - Evaluation" $ do
    it "evaluates polymorphic identity" $ do
      let polyId = TyAbs "A" (Lam "x" (TyVar "A") (Var "x"))
      let term = App (TyApp polyId TyBool) TmTrue
      eval term `shouldBe` TmTrue

    it "evaluates nested type applications" $ do
      let polyId = TyAbs "A" (Lam "x" (TyVar "A") (Var "x"))
      let term = App (TyApp polyId TyNat) (TmSucc TmZero)
      eval term `shouldBe` TmSucc TmZero

    it "evaluates const with type applications" $ do
      let polyConst = TyAbs "A" (TyAbs "B"
                        (Lam "x" (TyVar "A")
                          (Lam "y" (TyVar "B") (Var "x"))))
      let term = App (App (TyApp (TyApp polyConst TyBool) TyNat) TmTrue) TmZero
      eval term `shouldBe` TmTrue

  describe "Church Encodings in System F" $ do
    it "types Church booleans" $ do
      -- CBool = ∀A. A → A → A
      -- true = ΛA. λt:A. λf:A. t
      let churchBoolTy = TyForall "A" (TyArr (TyVar "A")
                          (TyArr (TyVar "A") (TyVar "A")))
      let churchTrue = TyAbs "A" (Lam "t" (TyVar "A")
                        (Lam "f" (TyVar "A") (Var "t")))
      typeCheck churchTrue `shouldBe` Right churchBoolTy

    it "evaluates Church boolean application" $ do
      let churchTrue = TyAbs "A" (Lam "t" (TyVar "A")
                        (Lam "f" (TyVar "A") (Var "t")))
      let churchFalse = TyAbs "A" (Lam "t" (TyVar "A")
                         (Lam "f" (TyVar "A") (Var "f")))
      -- true [Nat] 0 (succ 0) → 0
      let term = App (App (TyApp churchTrue TyNat) TmZero) (TmSucc TmZero)
      eval term `shouldBe` TmZero

  describe "Parser" $ do
    it "parses type abstraction" $ do
      parseTerm "/\\A. \\x:A. x" `shouldBe`
        Right (TyAbs "A" (Lam "x" (TyVar "A") (Var "x")))

    it "parses type application" $ do
      parseTerm "(/\\A. \\x:A. x) [Bool]" `shouldBe`
        Right (TyApp (TyAbs "A" (Lam "x" (TyVar "A") (Var "x"))) TyBool)

    it "parses forall types" $ do
      parseType "forall A. A -> A" `shouldBe`
        Right (TyForall "A" (TyArr (TyVar "A") (TyVar "A")))

    it "parses nested foralls" $ do
      parseType "forall A. forall B. A -> B -> A" `shouldBe`
        Right (TyForall "A" (TyForall "B"
                (TyArr (TyVar "A") (TyArr (TyVar "B") (TyVar "A")))))

  describe "Pretty Printing" $ do
    it "pretty prints forall types" $ do
      prettyType (TyForall "A" (TyArr (TyVar "A") (TyVar "A"))) `shouldBe`
        "∀A. A -> A"

    it "pretty prints type abstraction" $ do
      pretty (TyAbs "A" (Lam "x" (TyVar "A") (Var "x"))) `shouldBe`
        "ΛA. λx:A. x"

  describe "Type Safety" $ do
    it "rejects unbound type variables" $ do
      let badTerm = Lam "x" (TyVar "A") (Var "x")  -- A not bound!
      case typeCheck badTerm of
        Left (UnboundTypeVariable "A") -> return ()
        other -> expectationFailure $ "Expected unbound type var, got: " ++ show other

    it "rejects type application to non-forall" $ do
      let badTerm = TyApp TmTrue TyBool
      case typeCheck badTerm of
        Left (NotAForall TyBool) -> return ()
        other -> expectationFailure $ "Expected not-a-forall, got: " ++ show other
