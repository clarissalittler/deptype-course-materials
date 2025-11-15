{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import Parser
import Pretty
import qualified Data.Set as Set
import qualified ExerciseSpec

main :: IO ()
main = hspec $ do
  ExerciseSpec.spec
  describe "Syntax" $ do
    it "computes free variables correctly" $ do
      freeVars (Var "x") `shouldBe` Set.fromList ["x"]
      freeVars (Lam "x" TyBool (Var "x")) `shouldBe` Set.empty
      freeVars (Lam "x" TyBool (Var "y")) `shouldBe` Set.fromList ["y"]
      freeVars TmTrue `shouldBe` Set.empty
      freeVars (TmSucc TmZero) `shouldBe` Set.empty

  describe "Type system" $ do
    it "types boolean literals correctly" $ do
      typeCheck TmTrue `shouldBe` Right TyBool
      typeCheck TmFalse `shouldBe` Right TyBool

    it "types natural number literals correctly" $ do
      typeCheck TmZero `shouldBe` Right TyNat
      typeCheck (TmSucc TmZero) `shouldBe` Right TyNat
      typeCheck (TmSucc (TmSucc TmZero)) `shouldBe` Right TyNat

    it "types lambda abstractions correctly" $ do
      -- λx:Bool. x has type Bool -> Bool
      let identity = Lam "x" TyBool (Var "x")
      typeCheck identity `shouldBe` Right (TyArr TyBool TyBool)

      -- λx:Nat. λy:Bool. x has type Nat -> Bool -> Nat
      let const' = Lam "x" TyNat (Lam "y" TyBool (Var "x"))
      typeCheck const' `shouldBe` Right (TyArr TyNat (TyArr TyBool TyNat))

    it "types applications correctly" $ do
      -- (λx:Bool. x) true : Bool
      let term = App (Lam "x" TyBool (Var "x")) TmTrue
      typeCheck term `shouldBe` Right TyBool

    it "rejects ill-typed applications" $ do
      -- (λx:Bool. x) 0 is ill-typed
      let term = App (Lam "x" TyBool (Var "x")) TmZero
      case typeCheck term of
        Left (ArgumentTypeMismatch _ _) -> return ()
        _ -> expectationFailure "Should reject argument type mismatch"

    it "types if-then-else correctly" $ do
      -- if true then false else true : Bool
      let term = TmIf TmTrue TmFalse TmTrue
      typeCheck term `shouldBe` Right TyBool

      -- if iszero 0 then 0 else succ 0 : Nat
      let term' = TmIf (TmIsZero TmZero) TmZero (TmSucc TmZero)
      typeCheck term' `shouldBe` Right TyNat

    it "rejects if with non-boolean condition" $ do
      let term = TmIf TmZero TmTrue TmFalse
      case typeCheck term of
        Left (ConditionNotBool _) -> return ()
        _ -> expectationFailure "Should reject non-boolean condition"

    it "rejects if with mismatched branches" $ do
      let term = TmIf TmTrue TmZero TmFalse
      case typeCheck term of
        Left (TypeMismatch _ _) -> return ()
        _ -> expectationFailure "Should reject mismatched branch types"

    it "types numeric operations correctly" $ do
      typeCheck (TmSucc TmZero) `shouldBe` Right TyNat
      typeCheck (TmPred TmZero) `shouldBe` Right TyNat
      typeCheck (TmIsZero TmZero) `shouldBe` Right TyBool

    it "rejects numeric operations on non-naturals" $ do
      case typeCheck (TmSucc TmTrue) of
        Left (NotANat _) -> return ()
        _ -> expectationFailure "Should reject succ on non-Nat"

  describe "Evaluation" $ do
    it "identifies values correctly" $ do
      isValue (Lam "x" TyBool (Var "x")) `shouldBe` True
      isValue TmTrue `shouldBe` True
      isValue TmFalse `shouldBe` True
      isValue TmZero `shouldBe` True
      isValue (TmSucc TmZero) `shouldBe` True
      isValue (Var "x") `shouldBe` False
      isValue (App (Var "f") (Var "x")) `shouldBe` False

    it "evaluates identity function" $ do
      let term = App (Lam "x" TyBool (Var "x")) TmTrue
      eval term `shouldBe` TmTrue

    it "evaluates if-then-else" $ do
      eval (TmIf TmTrue TmFalse TmTrue) `shouldBe` TmFalse
      eval (TmIf TmFalse TmFalse TmTrue) `shouldBe` TmTrue

    it "evaluates nested conditionals" $ do
      -- if (if true then false else true) then true else false
      -- → if false then true else false → false
      let term = TmIf (TmIf TmTrue TmFalse TmTrue) TmTrue TmFalse
      eval term `shouldBe` TmFalse

    it "evaluates numeric operations" $ do
      eval (TmPred (TmSucc TmZero)) `shouldBe` TmZero
      eval (TmPred TmZero) `shouldBe` TmZero
      eval (TmIsZero TmZero) `shouldBe` TmTrue
      eval (TmIsZero (TmSucc TmZero)) `shouldBe` TmFalse

    it "evaluates complex numeric expressions" $ do
      -- iszero (pred (succ 0)) → iszero 0 → true
      let term = TmIsZero (TmPred (TmSucc TmZero))
      eval term `shouldBe` TmTrue

      -- if iszero 0 then succ 0 else 0 → if true then succ 0 else 0 → succ 0
      let term' = TmIf (TmIsZero TmZero) (TmSucc TmZero) TmZero
      eval term' `shouldBe` TmSucc TmZero

    it "evaluates function application" $ do
      -- (λx:Nat. succ x) 0 → succ 0
      let term = App (Lam "x" TyNat (TmSucc (Var "x"))) TmZero
      eval term `shouldBe` TmSucc TmZero

      -- (λx:Bool. if x then 0 else succ 0) false → if false then 0 else succ 0 → succ 0
      let term' = App (Lam "x" TyBool (TmIf (Var "x") TmZero (TmSucc TmZero))) TmFalse
      eval term' `shouldBe` TmSucc TmZero

  describe "Parser" $ do
    it "parses types correctly" $ do
      parseType "Bool" `shouldBe` Right TyBool
      parseType "Nat" `shouldBe` Right TyNat
      parseType "Bool -> Nat" `shouldBe` Right (TyArr TyBool TyNat)
      parseType "Nat -> Nat -> Bool" `shouldBe`
        Right (TyArr TyNat (TyArr TyNat TyBool))

    it "parses boolean literals" $ do
      parseTerm "true" `shouldBe` Right TmTrue
      parseTerm "false" `shouldBe` Right TmFalse

    it "parses natural numbers" $ do
      parseTerm "0" `shouldBe` Right TmZero
      parseTerm "succ 0" `shouldBe` Right (TmSucc TmZero)
      parseTerm "pred 0" `shouldBe` Right (TmPred TmZero)
      parseTerm "iszero 0" `shouldBe` Right (TmIsZero TmZero)

    it "parses lambda abstractions" $ do
      parseTerm "\\x:Bool. x" `shouldBe` Right (Lam "x" TyBool (Var "x"))
      parseTerm "λx:Nat. succ x" `shouldBe`
        Right (Lam "x" TyNat (TmSucc (Var "x")))

    it "parses applications" $ do
      parseTerm "(\\x:Bool. x) true" `shouldBe`
        Right (App (Lam "x" TyBool (Var "x")) TmTrue)

    it "parses if-then-else" $ do
      parseTerm "if true then false else true" `shouldBe`
        Right (TmIf TmTrue TmFalse TmTrue)

  describe "Pretty printing" $ do
    it "pretty prints types" $ do
      prettyType TyBool `shouldBe` "Bool"
      prettyType TyNat `shouldBe` "Nat"
      prettyType (TyArr TyBool TyNat) `shouldBe` "Bool -> Nat"

    it "pretty prints terms" $ do
      pretty TmTrue `shouldBe` "true"
      pretty TmFalse `shouldBe` "false"
      pretty TmZero `shouldBe` "0"
      pretty (Lam "x" TyBool (Var "x")) `shouldBe` "λx:Bool. x"

  describe "Type safety" $ do
    it "ensures well-typed terms don't get stuck" $ do
      -- If a term is well-typed and not a value, it can take a step
      let term = App (Lam "x" TyBool (Var "x")) TmTrue
      case typeCheck term of
        Right _ -> do
          if not (isValue term)
            then step term `shouldSatisfy` (/= Nothing)
            else return ()
        Left _ -> expectationFailure "Term should be well-typed"
