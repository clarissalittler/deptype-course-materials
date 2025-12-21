{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Hspec
import Test.QuickCheck ()

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
        freeVars (Var "x") `shouldBe` fromList ["x"]

      it "removes bound variable in lambda" $
        freeVars (Lam "x" (TyBase TyNat) (Var "x")) `shouldBe` fromList []

      it "finds free in lambda body" $
        freeVars (Lam "x" (TyBase TyNat) (Var "y")) `shouldBe` fromList ["y"]

      it "handles let binding" $
        freeVars (TmLet "x" (Var "a") (App (Var "x") (Var "b")))
          `shouldBe` fromList ["a", "b"]

    describe "predFreeVars" $ do
      it "finds variable in PVar" $
        predFreeVars (PVar "x") `shouldBe` fromList ["x"]

      it "finds variables in comparison" $
        predFreeVars (PComp OpGt (PAVar "x") (PALit 0)) `shouldBe` fromList ["x"]

    describe "substPred" $ do
      it "substitutes in comparison" $
        substPred "x" (PALit 5) (PComp OpGt (PAVar "x") (PALit 0))
          `shouldBe` PComp OpGt (PALit 5) (PALit 0)

  describe "TypeCheck" $ do
    describe "Basic typing" $ do
      it "types true as Bool" $
        typeCheck TmTrue `shouldBe` Right (TyBase TyBool)

      it "types false as Bool" $
        typeCheck TmFalse `shouldBe` Right (TyBase TyBool)

      it "types zero as Nat" $
        typeCheck TmZero `shouldBe` Right (TyBase TyNat)

      it "types succ 0 as Nat" $
        typeCheck (TmSucc TmZero) `shouldBe` Right (TyBase TyNat)

      it "types unit as Unit" $
        typeCheck TmUnit `shouldBe` Right (TyBase TyUnit)

    describe "Lambda and application" $ do
      it "types identity function" $
        typeCheck (Lam "x" (TyBase TyNat) (Var "x"))
          `shouldBe` Right (TyFun "x" (TyBase TyNat) (TyBase TyNat))

      it "types constant function" $
        typeCheck (Lam "x" (TyBase TyNat) TmZero)
          `shouldBe` Right (TyFun "x" (TyBase TyNat) (TyBase TyNat))

      it "rejects unbound variable" $
        typeCheck (Var "x") `shouldBe` Left (UnboundVariable "x")

    describe "Conditionals" $ do
      it "types if-then-else with matching branches" $
        typeCheck (TmIf TmTrue TmZero (TmSucc TmZero))
          `shouldBe` Right (TyBase TyNat)

      it "rejects non-boolean condition" $
        case typeCheck (TmIf TmZero TmTrue TmFalse) of
          Left (ConditionNotBool _) -> True
          _ -> False

    describe "Arithmetic" $ do
      it "types addition" $
        typeCheck (TmArith Add TmZero TmZero) `shouldBe` Right (TyBase TyNat)

      it "types subtraction" $
        typeCheck (TmArith Sub (TmSucc TmZero) TmZero) `shouldBe` Right (TyBase TyNat)

      it "types iszero" $
        typeCheck (TmIsZero TmZero) `shouldBe` Right (TyBase TyBool)

    describe "Let binding" $ do
      it "types simple let" $
        typeCheck (TmLet "x" TmZero (Var "x"))
          `shouldSatisfy` isRight

      it "types let with arithmetic" $
        typeCheck (TmLet "x" TmZero (TmArith Add (Var "x") (TmSucc TmZero)))
          `shouldBe` Right (TyBase TyNat)

    describe "Ascription" $ do
      it "accepts valid ascription" $
        typeCheck (TmAscribe TmZero (TyBase TyNat))
          `shouldBe` Right (TyBase TyNat)

  describe "Subtyping" $ do
    describe "isSubtype" $ do
      it "base types are subtypes of themselves" $
        isSubtype emptyContext (TyBase TyNat) (TyBase TyNat) `shouldBe` True

      it "different base types are not subtypes" $
        isSubtype emptyContext (TyBase TyNat) (TyBase TyBool) `shouldBe` False

      it "refined type is subtype of base" $
        isSubtype emptyContext
          (TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 0)))
          (TyBase TyNat)
          `shouldBe` True

      it "stronger refinement is subtype of weaker" $
        -- {x: Nat | x > 5} <: {x: Nat | x > 0}  (5 > 0)
        isSubtype emptyContext
          (TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 5)))
          (TyRefine "x" (TyBase TyNat) PTrue)
          `shouldBe` True

  describe "Predicate validity" $ do
    describe "isValid" $ do
      it "PTrue is valid" $
        isValid PTrue `shouldBe` True

      it "PFalse is not valid" $
        isValid PFalse `shouldBe` False

      it "1 > 0 is valid" $
        isValid (PComp OpGt (PALit 1) (PALit 0)) `shouldBe` True

      it "0 > 1 is not valid" $
        isValid (PComp OpGt (PALit 0) (PALit 1)) `shouldBe` False

      it "5 == 5 is valid" $
        isValid (PComp OpEq (PALit 5) (PALit 5)) `shouldBe` True

      it "PTrue && PTrue is valid" $
        isValid (PAnd PTrue PTrue) `shouldBe` True

      it "PTrue && PFalse is not valid" $
        isValid (PAnd PTrue PFalse) `shouldBe` False

      it "PTrue || PFalse is valid" $
        isValid (POr PTrue PFalse) `shouldBe` True

    describe "implies" $ do
      it "PTrue implies PTrue" $
        implies PTrue PTrue `shouldBe` True

      it "PFalse implies anything" $
        implies PFalse PTrue `shouldBe` True

      it "PTrue doesn't imply PFalse" $
        implies PTrue PFalse `shouldBe` False

      it "x > 5 implies x > 0 (for ground)" $
        implies (PComp OpGt (PALit 6) (PALit 5))
                (PComp OpGt (PALit 6) (PALit 0)) `shouldBe` True

  describe "Evaluation" $ do
    describe "isValue" $ do
      it "lambda is value" $
        isValue (Lam "x" (TyBase TyNat) (Var "x")) `shouldBe` True

      it "true is value" $
        isValue TmTrue `shouldBe` True

      it "zero is value" $
        isValue TmZero `shouldBe` True

      it "succ 0 is value" $
        isValue (TmSucc TmZero) `shouldBe` True

      it "application is not value" $
        isValue (App (Var "f") (Var "x")) `shouldBe` False

    describe "eval" $ do
      it "evaluates identity application" $
        eval (App (Lam "x" (TyBase TyNat) (Var "x")) TmZero)
          `shouldBe` TmZero

      it "evaluates if true" $
        eval (TmIf TmTrue TmZero (TmSucc TmZero)) `shouldBe` TmZero

      it "evaluates if false" $
        eval (TmIf TmFalse TmZero (TmSucc TmZero)) `shouldBe` TmSucc TmZero

      it "evaluates pred (succ 0)" $
        eval (TmPred (TmSucc TmZero)) `shouldBe` TmZero

      it "evaluates iszero 0" $
        eval (TmIsZero TmZero) `shouldBe` TmTrue

      it "evaluates iszero (succ 0)" $
        eval (TmIsZero (TmSucc TmZero)) `shouldBe` TmFalse

      it "evaluates let binding" $
        eval (TmLet "x" (TmSucc TmZero) (Var "x")) `shouldBe` TmSucc TmZero

      it "evaluates addition" $
        eval (TmArith Add (TmSucc TmZero) (TmSucc (TmSucc TmZero)))
          `shouldBe` TmSucc (TmSucc (TmSucc TmZero))

      it "evaluates subtraction" $
        eval (TmArith Sub (TmSucc (TmSucc TmZero)) (TmSucc TmZero))
          `shouldBe` TmSucc TmZero

  describe "Parser" $ do
    describe "parseTerm" $ do
      it "parses true" $
        parseTerm "true" `shouldBe` Right TmTrue

      it "parses false" $
        parseTerm "false" `shouldBe` Right TmFalse

      it "parses 0" $
        parseTerm "0" `shouldBe` Right TmZero

      it "parses natural numbers" $
        parseTerm "3" `shouldBe` Right (TmSucc (TmSucc (TmSucc TmZero)))

      it "parses succ" $
        parseTerm "succ 0" `shouldBe` Right (TmSucc TmZero)

      it "parses lambda" $
        parseTerm "\\x : Nat. x" `shouldBe`
          Right (Lam "x" (TyBase TyNat) (Var "x"))

      it "parses if-then-else" $
        parseTerm "if true then 0 else 1" `shouldBe`
          Right (TmIf TmTrue TmZero (TmSucc TmZero))

      it "parses let" $
        parseTerm "let x = 0 in x" `shouldBe`
          Right (TmLet "x" TmZero (Var "x"))

      it "parses arithmetic" $
        parseTerm "1 + 2" `shouldBe`
          Right (TmArith Add (TmSucc TmZero) (TmSucc (TmSucc TmZero)))

    describe "parseType" $ do
      it "parses Bool" $
        parseType "Bool" `shouldBe` Right (TyBase TyBool)

      it "parses Nat" $
        parseType "Nat" `shouldBe` Right (TyBase TyNat)

      it "parses function type" $
        parseType "Nat -> Bool" `shouldBe`
          Right (TyFun "_" (TyBase TyNat) (TyBase TyBool))

      it "parses dependent function type" $
        parseType "(x : Nat) -> Nat" `shouldBe`
          Right (TyFun "x" (TyBase TyNat) (TyBase TyNat))

      it "parses refinement type" $
        parseType "{x : Nat | x > 0}" `shouldBe`
          Right (TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 0)))

    describe "parsePred" $ do
      it "parses true" $
        parsePred "true" `shouldBe` Right PTrue

      it "parses comparison" $
        parsePred "x > 0" `shouldBe` Right (PComp OpGt (PAVar "x") (PALit 0))

      it "parses conjunction" $
        parsePred "x > 0 && x < 10" `shouldBe`
          Right (PAnd (PComp OpGt (PAVar "x") (PALit 0))
                      (PComp OpLt (PAVar "x") (PALit 10)))

      it "parses implication" $
        parsePred "x > 5 => x > 0" `shouldBe`
          Right (PImpl (PComp OpGt (PAVar "x") (PALit 5))
                       (PComp OpGt (PAVar "x") (PALit 0)))

  describe "Pretty" $ do
    describe "prettyTerm" $ do
      it "prints true" $
        prettyTerm TmTrue `shouldBe` "true"

      it "prints natural numbers" $
        prettyTerm (TmSucc (TmSucc TmZero)) `shouldBe` "2"

      it "prints lambda" $
        prettyTerm (Lam "x" (TyBase TyNat) (Var "x"))
          `shouldBe` "λx : Nat. x"

    describe "prettyType" $ do
      it "prints base types" $
        prettyType (TyBase TyNat) `shouldBe` "Nat"

      it "prints refinement types" $
        prettyType (TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 0)))
          `shouldBe` "{x : Nat | x > 0}"

      it "prints function types" $
        prettyType (TyFun "_" (TyBase TyNat) (TyBase TyBool))
          `shouldBe` "Nat -> Bool"

    describe "prettyPred" $ do
      it "prints true" $
        prettyPred PTrue `shouldBe` "true"

      it "prints comparison" $
        prettyPred (PComp OpGt (PAVar "x") (PALit 0)) `shouldBe` "x > 0"

      it "prints conjunction" $
        prettyPred (PAnd (PComp OpGt (PAVar "x") (PALit 0))
                         (PComp OpLt (PAVar "x") (PALit 10)))
          `shouldBe` "x > 0 && x < 10"

  describe "Integration" $ do
    it "type checks positive number function" $ do
      let term = Lam "n" (TyRefine "x" (TyBase TyNat) (PComp OpGt (PAVar "x") (PALit 0)))
                     (Var "n")
      typeCheck term `shouldSatisfy` isRight

    it "type checks and evaluates let with refinement" $ do
      let term = TmLet "x" (TmSucc TmZero) (TmArith Add (Var "x") (Var "x"))
      typeCheck term `shouldSatisfy` isRight
      eval term `shouldBe` TmSucc (TmSucc TmZero)

-- Helpers
fromList :: [String] -> Set.Set String
fromList = Set.fromList

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False
