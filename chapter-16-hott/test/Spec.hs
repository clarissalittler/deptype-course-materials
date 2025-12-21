{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec

import Syntax
import Parser
import TypeCheck
import Eval
import Pretty

main :: IO ()
main = hspec $ do
  describe "Syntax" $ do
    describe "Type equality" $ do
      it "base types are equal" $ do
        TyBool `shouldBe` TyBool
        TyNat `shouldBe` TyNat
        TyUnit `shouldBe` TyUnit

      it "function types compare structurally" $ do
        TyFun TyNat TyBool `shouldBe` TyFun TyNat TyBool
        TyFun TyNat TyBool `shouldNotBe` TyFun TyBool TyNat

      it "identity types compare with endpoints" $ do
        TyId TyNat TmZero TmZero `shouldBe` TyId TyNat TmZero TmZero
        TyId TyNat TmZero (TmSucc TmZero) `shouldNotBe` TyId TyNat TmZero TmZero

    describe "Substitution" $ do
      it "substitutes in identity type endpoints" $ do
        let ty = TyId TyNat (Var "x") (Var "x")
        substType "x" TmZero ty `shouldBe` TyId TyNat TmZero TmZero

  describe "TypeCheck" $ do
    describe "Identity types" $ do
      it "types refl correctly" $ do
        let term = TmRefl TyNat TmZero
        typeCheck term `shouldBe` Right (TyId TyNat TmZero TmZero)

      it "refl requires matching type" $ do
        let term = TmRefl TyBool TmZero
        typeCheck term `shouldSatisfy` isLeft

      it "types sym correctly" $ do
        let path = TmRefl TyNat TmZero
        let term = TmSym path
        typeCheck term `shouldBe` Right (TyId TyNat TmZero TmZero)

      it "sym reverses endpoints" $ do
        -- We need a non-trivial path to see the reversal
        -- For now, just check the type structure
        let idTy = TyId TyNat TmZero (TmSucc TmZero)
        let lam = Lam "p" idTy (TmSym (Var "p"))
        case typeCheck lam of
          Right (TyFun _ (TyId _ a b)) -> do
            a `shouldBe` TmSucc TmZero
            b `shouldBe` TmZero
          other -> expectationFailure $ "Expected function type, got: " ++ show other

      it "types trans correctly" $ do
        let p = TmRefl TyNat TmZero
        let q = TmRefl TyNat TmZero
        let term = TmTrans p q
        typeCheck term `shouldBe` Right (TyId TyNat TmZero TmZero)

      it "trans requires matching midpoint" $ do
        let idTy1 = TyId TyNat TmZero (TmSucc TmZero)
        let idTy2 = TyId TyNat (TmSucc (TmSucc TmZero)) TmZero
        let lam = Lam "p" idTy1 (Lam "q" idTy2 (TmTrans (Var "p") (Var "q")))
        typeCheck lam `shouldSatisfy` isLeft

      it "types ap correctly" $ do
        let f = Lam "x" TyNat (TmSucc (Var "x"))
        let p = TmRefl TyNat TmZero
        let term = TmAp f p
        case typeCheck term of
          Right (TyId TyNat (App _ a) (App _ b)) -> do
            a `shouldBe` TmZero
            b `shouldBe` TmZero
          other -> expectationFailure $ "Expected identity type, got: " ++ show other

      it "types J eliminator" $ do
        let base = Lam "x" TyNat (Var "x")
        let a = TmZero
        let b = TmZero
        let p = TmRefl TyNat TmZero
        let term = TmJ TyNat base a b p
        typeCheck term `shouldBe` Right TyNat

      it "types transport" $ do
        let p = TmRefl TyNat TmZero
        let t = TmTrue
        let term = TmTransport TyBool p t
        typeCheck term `shouldBe` Right TyBool

    describe "Void type" $ do
      it "absurd has any type" $ do
        let voidTerm = Var "v"
        let ctx = emptyContext
        let lam = Lam "v" TyVoid (TmAbsurd TyNat (Var "v"))
        typeCheck lam `shouldBe` Right (TyFun TyVoid TyNat)

  describe "Eval" $ do
    describe "Path operations" $ do
      it "refl is a value" $ do
        isValue (TmRefl TyNat TmZero) `shouldBe` True

      it "sym refl = refl" $ do
        let term = TmSym (TmRefl TyNat TmZero)
        eval term `shouldBe` TmRefl TyNat TmZero

      it "trans refl refl = refl" $ do
        let term = TmTrans (TmRefl TyNat TmZero) (TmRefl TyNat TmZero)
        eval term `shouldBe` TmRefl TyNat TmZero

      it "ap f refl = refl (f a)" $ do
        let f = Lam "x" TyNat (TmSucc (Var "x"))
        let term = TmAp f (TmRefl TyNat TmZero)
        -- ap f refl evaluates to refl (f a), but with f = λx. succ x,
        -- the result is refl (succ 0), not refl (App f 0)
        case eval term of
          TmRefl _ (TmSucc TmZero) -> return ()
          TmRefl _ (App _ arg) -> arg `shouldBe` TmZero
          other -> expectationFailure $ "Expected refl, got: " ++ show other

      it "transport refl t = t" $ do
        let term = TmTransport TyNat (TmRefl TyNat TmZero) (TmSucc TmZero)
        eval term `shouldBe` TmSucc TmZero

      it "J base a a refl = base a" $ do
        let base = Lam "x" TyNat (TmSucc (Var "x"))
        let term = TmJ TyNat base TmZero TmZero (TmRefl TyNat TmZero)
        eval term `shouldBe` TmSucc TmZero

  describe "Parser" $ do
    describe "Types" $ do
      it "parses identity type" $ do
        parseType "Id Nat x y" `shouldBe`
          Right (TyId TyNat (Var "x") (Var "y"))

      it "parses Void" $ do
        parseType "Void" `shouldBe` Right TyVoid

      it "parses Type universe" $ do
        parseType "Type" `shouldBe` Right TyUniverse

    describe "Terms" $ do
      it "parses refl" $ do
        parseTerm "refl [Nat] 0" `shouldBe`
          Right (TmRefl TyNat TmZero)

      it "parses sym" $ do
        parseTerm "sym x" `shouldBe` Right (TmSym (Var "x"))

      it "parses trans" $ do
        parseTerm "trans p q" `shouldBe`
          Right (TmTrans (Var "p") (Var "q"))

      it "parses ap" $ do
        parseTerm "ap f p" `shouldBe`
          Right (TmAp (Var "f") (Var "p"))

      it "parses transport" $ do
        parseTerm "transport [Nat] p x" `shouldBe`
          Right (TmTransport TyNat (Var "p") (Var "x"))

      it "parses J" $ do
        parseTerm "J [Nat] base a b p" `shouldBe`
          Right (TmJ TyNat (Var "base") (Var "a") (Var "b") (Var "p"))

      it "parses absurd" $ do
        parseTerm "absurd [Nat] v" `shouldBe`
          Right (TmAbsurd TyNat (Var "v"))

  describe "Pretty" $ do
    describe "Types" $ do
      it "pretty prints identity type" $ do
        prettyType (TyId TyNat TmZero (TmSucc TmZero))
          `shouldBe` "Id Nat 0 (succ 0)"

      it "pretty prints Void" $ do
        prettyType TyVoid `shouldBe` "Void"

    describe "Terms" $ do
      it "pretty prints refl" $ do
        prettyTerm (TmRefl TyNat TmZero)
          `shouldBe` "refl [Nat] 0"

      it "pretty prints sym" $ do
        prettyTerm (TmSym (Var "p"))
          `shouldBe` "sym p"

      it "pretty prints transport" $ do
        prettyTerm (TmTransport TyNat (Var "p") (Var "x"))
          `shouldBe` "transport [Nat] p x"

  describe "Integration" $ do
    describe "Path algebra" $ do
      it "reflexivity paths are trivial" $ do
        let refl0 = TmRefl TyNat TmZero
        let refl1 = TmRefl TyNat (TmSucc TmZero)
        isValue (eval refl0) `shouldBe` True
        isValue (eval refl1) `shouldBe` True

      it "path operations compose" $ do
        let p = TmRefl TyNat TmZero
        -- sym (sym p) should evaluate like p
        let doubleSym = TmSym (TmSym p)
        eval doubleSym `shouldBe` TmRefl TyNat TmZero

      it "transport is identity on refl paths" $ do
        let value = TmPair TmTrue (TmSucc TmZero)
        let path = TmRefl TyNat TmZero
        let transported = TmTransport (TyProd TyBool TyNat) path value
        eval transported `shouldBe` value

    describe "Function application to paths" $ do
      it "ap preserves identity" $ do
        let idFn = Lam "x" TyNat (Var "x")
        let path = TmRefl TyNat (TmSucc TmZero)
        let result = eval (TmAp idFn path)
        case result of
          TmRefl _ _ -> return ()
          other -> expectationFailure $ "Expected refl, got: " ++ show other

      it "ap composes with function composition" $ do
        let f = Lam "x" TyNat (TmSucc (Var "x"))
        let g = Lam "x" TyNat (TmSucc (Var "x"))
        let path = TmRefl TyNat TmZero
        -- ap f (ap g refl) should be refl
        let composed = TmAp f (TmAp g path)
        case eval composed of
          TmRefl _ _ -> return ()
          other -> expectationFailure $ "Expected refl, got: " ++ show other

-- Helper functions
isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False
