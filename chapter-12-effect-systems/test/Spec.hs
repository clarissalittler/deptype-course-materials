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

      it "handles let binding" $
        freeVars (TmLet "x" (Var "a") (App (Var "x") (Var "b")))
          `shouldBe` Set.fromList ["a", "b"]

      it "handles perform" $
        freeVars (TmPerform "State" "get" TmUnit) `shouldBe` Set.empty

    describe "freeEffectVars" $ do
      it "finds effect variable in function type" $
        freeEffectVars (TyFun TyNat TyNat (EffVar "ρ"))
          `shouldBe` Set.singleton "ρ"

      it "removes bound effect variable in forall" $
        freeEffectVars (TyForallEff "ρ" (TyFun TyNat TyNat (EffVar "ρ")))
          `shouldBe` Set.empty

  describe "Effect Rows" $ do
    describe "rowContains" $ do
      it "empty row contains nothing" $
        rowContains "State" EffEmpty `shouldBe` False

      it "finds effect in singleton row" $
        rowContains "State" (EffLabel "State" EffEmpty) `shouldBe` True

      it "finds effect in multi-effect row" $
        rowContains "State" (EffLabel "IO" (EffLabel "State" EffEmpty))
          `shouldBe` True

      it "doesn't find absent effect" $
        rowContains "State" (EffLabel "IO" EffEmpty) `shouldBe` False

    describe "rowUnion" $ do
      it "union with empty is identity" $
        rowUnion EffEmpty (EffLabel "State" EffEmpty)
          `shouldBe` EffLabel "State" EffEmpty

      it "unions two rows" $
        let r1 = EffLabel "State" EffEmpty
            r2 = EffLabel "IO" EffEmpty
        in rowContains "State" (rowUnion r1 r2) &&
           rowContains "IO" (rowUnion r1 r2)
          `shouldBe` True

    describe "rowRemove" $ do
      it "removes effect from row" $
        rowRemove "State" (EffLabel "State" (EffLabel "IO" EffEmpty))
          `shouldBe` EffLabel "IO" EffEmpty

      it "removing from empty is empty" $
        rowRemove "State" EffEmpty `shouldBe` EffEmpty

  describe "TypeCheck" $ do
    describe "Basic typing" $ do
      it "types true as Bool" $
        typeCheck TmTrue `shouldBe` Right (TypeAndEffect TyBool EffEmpty)

      it "types zero as Nat" $
        typeCheck TmZero `shouldBe` Right (TypeAndEffect TyNat EffEmpty)

      it "types unit as Unit" $
        typeCheck TmUnit `shouldBe` Right (TypeAndEffect TyUnit EffEmpty)

    describe "Lambda and application" $ do
      it "types pure identity function" $
        typeCheck (Lam "x" TyNat (Var "x"))
          `shouldBe` Right (TypeAndEffect (TyFun TyNat TyNat EffEmpty) EffEmpty)

      it "types application" $
        typeCheck (App (Lam "x" TyNat (Var "x")) TmZero)
          `shouldBe` Right (TypeAndEffect TyNat EffEmpty)

      it "rejects unbound variable" $
        typeCheck (Var "x") `shouldBe` Left (UnboundVariable "x")

    describe "Effect operations" $ do
      it "types State.get with State effect" $ do
        let result = typeCheck (TmPerform "State" "get" TmUnit)
        case result of
          Right (TypeAndEffect TyNat eff) ->
            rowContains "State" eff `shouldBe` True
          _ -> expectationFailure "Expected Nat ! {State}"

      it "types State.put with State effect" $ do
        let result = typeCheck (TmPerform "State" "put" TmZero)
        case result of
          Right (TypeAndEffect TyUnit eff) ->
            rowContains "State" eff `shouldBe` True
          _ -> expectationFailure "Expected Unit ! {State}"

      it "rejects unknown effect" $
        typeCheck (TmPerform "Unknown" "op" TmUnit)
          `shouldBe` Left (UnboundOperation "Unknown" "op")

    describe "Let binding" $ do
      it "types let with effect propagation" $
        typeCheck (TmLet "x" TmZero (Var "x"))
          `shouldBe` Right (TypeAndEffect TyNat EffEmpty)

    describe "Effect polymorphism" $ do
      it "types effect abstraction" $
        typeCheck (TmEffAbs "ρ" (Lam "x" TyNat (Var "x")))
          `shouldSatisfy` isRight

  describe "Evaluation" $ do
    describe "isValue" $ do
      it "lambda is value" $
        isValue (Lam "x" TyNat (Var "x")) `shouldBe` True

      it "true is value" $
        isValue TmTrue `shouldBe` True

      it "zero is value" $
        isValue TmZero `shouldBe` True

      it "application is not value" $
        isValue (App (Var "f") (Var "x")) `shouldBe` False

    describe "eval" $ do
      it "evaluates identity application" $
        eval (App (Lam "x" TyNat (Var "x")) TmZero) `shouldBe` TmZero

      it "evaluates if true" $
        eval (TmIf TmTrue TmZero (TmSucc TmZero)) `shouldBe` TmZero

      it "evaluates if false" $
        eval (TmIf TmFalse TmZero (TmSucc TmZero)) `shouldBe` TmSucc TmZero

      it "evaluates pred (succ 0)" $
        eval (TmPred (TmSucc TmZero)) `shouldBe` TmZero

      it "evaluates let binding" $
        eval (TmLet "x" (TmSucc TmZero) (Var "x")) `shouldBe` TmSucc TmZero

  describe "Parser" $ do
    describe "parseTerm" $ do
      it "parses true" $
        parseTerm "true" `shouldBe` Right TmTrue

      it "parses false" $
        parseTerm "false" `shouldBe` Right TmFalse

      it "parses 0" $
        parseTerm "0" `shouldBe` Right TmZero

      it "parses lambda" $
        parseTerm "\\x : Nat. x" `shouldBe`
          Right (Lam "x" TyNat (Var "x"))

      it "parses perform" $
        parseTerm "perform State.get ()" `shouldBe`
          Right (TmPerform "State" "get" TmUnit)

      it "parses return" $
        parseTerm "return 0" `shouldBe` Right (TmReturn TmZero)

    describe "parseType" $ do
      it "parses Bool" $
        parseType "Bool" `shouldBe` Right TyBool

      it "parses Nat" $
        parseType "Nat" `shouldBe` Right TyNat

      it "parses function type" $
        parseType "Nat -> Bool" `shouldBe`
          Right (TyFun TyNat TyBool EffEmpty)

      it "parses effectful function type" $
        parseType "Nat -> Bool ! {State}" `shouldBe`
          Right (TyFun TyNat TyBool (EffLabel "State" EffEmpty))

    describe "parseEffectRow" $ do
      it "parses empty row" $
        parseEffectRow "{}" `shouldBe` Right EffEmpty

      it "parses singleton row" $
        parseEffectRow "{State}" `shouldBe`
          Right (EffLabel "State" EffEmpty)

      it "parses multi-effect row" $
        parseEffectRow "{State, IO}" `shouldBe`
          Right (EffLabel "State" (EffLabel "IO" EffEmpty))

      it "parses row with variable" $
        parseEffectRow "{State | ρ}" `shouldBe`
          Right (EffLabel "State" (EffVar "ρ"))

  describe "Pretty" $ do
    describe "prettyTerm" $ do
      it "prints true" $
        prettyTerm TmTrue `shouldBe` "true"

      it "prints natural numbers" $
        prettyTerm (TmSucc (TmSucc TmZero)) `shouldBe` "2"

      it "prints lambda" $
        prettyTerm (Lam "x" TyNat (Var "x"))
          `shouldBe` "λx : Nat. x"

      it "prints perform" $
        prettyTerm (TmPerform "State" "get" TmUnit)
          `shouldBe` "perform State.get ()"

    describe "prettyType" $ do
      it "prints base types" $
        prettyType TyNat `shouldBe` "Nat"

      it "prints pure function" $
        prettyType (TyFun TyNat TyBool EffEmpty)
          `shouldBe` "Nat -> Bool"

      it "prints effectful function" $
        prettyType (TyFun TyNat TyBool (EffLabel "State" EffEmpty))
          `shouldBe` "Nat -> Bool ! {State}"

    describe "prettyEffectRow" $ do
      it "prints empty row" $
        prettyEffectRow EffEmpty `shouldBe` "{}"

      it "prints singleton row" $
        prettyEffectRow (EffLabel "State" EffEmpty) `shouldBe` "{State}"

      it "prints row with variable" $
        prettyEffectRow (EffLabel "State" (EffVar "ρ")) `shouldBe` "{State | ρ}"

  describe "Integration" $ do
    it "type checks stateful function" $ do
      let term = Lam "x" TyUnit (TmPerform "State" "get" TmUnit)
      case typeCheck term of
        Right (TypeAndEffect (TyFun TyUnit TyNat eff) _) ->
          rowContains "State" eff `shouldBe` True
        _ -> expectationFailure "Expected Unit -> Nat ! {State}"

    it "pure function has no effects" $ do
      let term = Lam "x" TyNat (TmSucc (Var "x"))
      typeCheck term `shouldBe`
        Right (TypeAndEffect (TyFun TyNat TyNat EffEmpty) EffEmpty)

-- Helper
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False
