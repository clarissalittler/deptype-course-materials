{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Test.QuickCheck
import qualified Data.Map.Strict as Map

import Syntax
import TypeCheck
import Eval
import Parser
import Pretty

main :: IO ()
main = hspec $ do
  subtypingSpec
  typeCheckSpec
  evalSpec
  parserSpec
  prettySpec

-- =============================================================================
-- Subtyping Tests
-- =============================================================================

subtypingSpec :: Spec
subtypingSpec = describe "Subtyping" $ do

  describe "Reflexivity" $ do
    it "Bool <: Bool" $
      TyBool <: TyBool `shouldBe` True

    it "Nat <: Nat" $
      TyNat <: TyNat `shouldBe` True

    it "Top <: Top" $
      TyTop <: TyTop `shouldBe` True

    it "Bot <: Bot" $
      TyBot <: TyBot `shouldBe` True

  describe "Top and Bot" $ do
    it "Bool <: Top" $
      TyBool <: TyTop `shouldBe` True

    it "Nat <: Top" $
      TyNat <: TyTop `shouldBe` True

    it "Bot <: Bool" $
      TyBot <: TyBool `shouldBe` True

    it "Bot <: Nat" $
      TyBot <: TyNat `shouldBe` True

    it "Bot <: Top" $
      TyBot <: TyTop `shouldBe` True

    it "Top </: Bool" $
      TyTop <: TyBool `shouldBe` False

    it "Bool </: Bot" $
      TyBool <: TyBot `shouldBe` False

  describe "Function subtyping" $ do
    -- Contravariant in argument, covariant in result
    it "(Top -> Bool) <: (Bool -> Bool)" $
      TyArr TyTop TyBool <: TyArr TyBool TyBool `shouldBe` True

    it "(Bool -> Bool) </: (Top -> Bool)" $
      TyArr TyBool TyBool <: TyArr TyTop TyBool `shouldBe` False

    it "(Bool -> Bot) <: (Bool -> Bool)" $
      TyArr TyBool TyBot <: TyArr TyBool TyBool `shouldBe` True

    it "(Bool -> Bool) </: (Bool -> Bot)" $
      TyArr TyBool TyBool <: TyArr TyBool TyBot `shouldBe` False

    it "(Top -> Bot) <: (Bool -> Nat)" $
      TyArr TyTop TyBot <: TyArr TyBool TyNat `shouldBe` True

  describe "Record width subtyping" $ do
    it "{x: Nat, y: Bool} <: {x: Nat}" $
      let r1 = TyRecord $ Map.fromList [("x", TyNat), ("y", TyBool)]
          r2 = TyRecord $ Map.fromList [("x", TyNat)]
      in r1 <: r2 `shouldBe` True

    it "{x: Nat} </: {x: Nat, y: Bool}" $
      let r1 = TyRecord $ Map.fromList [("x", TyNat)]
          r2 = TyRecord $ Map.fromList [("x", TyNat), ("y", TyBool)]
      in r1 <: r2 `shouldBe` False

    it "{a: Nat, b: Bool, c: Top} <: {a: Nat}" $
      let r1 = TyRecord $ Map.fromList [("a", TyNat), ("b", TyBool), ("c", TyTop)]
          r2 = TyRecord $ Map.fromList [("a", TyNat)]
      in r1 <: r2 `shouldBe` True

  describe "Record depth subtyping" $ do
    it "{x: Bot} <: {x: Nat}" $
      let r1 = TyRecord $ Map.fromList [("x", TyBot)]
          r2 = TyRecord $ Map.fromList [("x", TyNat)]
      in r1 <: r2 `shouldBe` True

    it "{x: Nat} <: {x: Top}" $
      let r1 = TyRecord $ Map.fromList [("x", TyNat)]
          r2 = TyRecord $ Map.fromList [("x", TyTop)]
      in r1 <: r2 `shouldBe` True

    it "{x: Top} </: {x: Nat}" $
      let r1 = TyRecord $ Map.fromList [("x", TyTop)]
          r2 = TyRecord $ Map.fromList [("x", TyNat)]
      in r1 <: r2 `shouldBe` False

  describe "Combined width and depth" $ do
    it "{x: Bot, y: Bool} <: {x: Nat}" $
      let r1 = TyRecord $ Map.fromList [("x", TyBot), ("y", TyBool)]
          r2 = TyRecord $ Map.fromList [("x", TyNat)]
      in r1 <: r2 `shouldBe` True

-- =============================================================================
-- Type Checking Tests
-- =============================================================================

typeCheckSpec :: Spec
typeCheckSpec = describe "Type Checking" $ do

  describe "Basic terms" $ do
    it "true : Bool" $
      typeCheck TmTrue `shouldBe` Right TyBool

    it "false : Bool" $
      typeCheck TmFalse `shouldBe` Right TyBool

    it "0 : Nat" $
      typeCheck TmZero `shouldBe` Right TyNat

    it "succ 0 : Nat" $
      typeCheck (TmSucc TmZero) `shouldBe` Right TyNat

  describe "Lambda and application" $ do
    it "λx:Bool. x : Bool -> Bool" $
      typeCheck (Lam "x" TyBool (Var "x")) `shouldBe` Right (TyArr TyBool TyBool)

    it "(λx:Bool. x) true : Bool" $
      typeCheck (App (Lam "x" TyBool (Var "x")) TmTrue) `shouldBe` Right TyBool

  describe "Subsumption" $ do
    it "(λx:Top. x) true : Top" $
      -- true : Bool, Bool <: Top, so this typechecks
      typeCheck (App (Lam "x" TyTop (Var "x")) TmTrue) `shouldBe` Right TyTop

    it "(λx:Top. x) 0 : Top" $
      typeCheck (App (Lam "x" TyTop (Var "x")) TmZero) `shouldBe` Right TyTop

  describe "Records" $ do
    it "{x = 0} : {x: Nat}" $
      typeCheck (TmRecord $ Map.fromList [("x", TmZero)])
        `shouldBe` Right (TyRecord $ Map.fromList [("x", TyNat)])

    it "{x = 0, y = true} : {x: Nat, y: Bool}" $
      typeCheck (TmRecord $ Map.fromList [("x", TmZero), ("y", TmTrue)])
        `shouldBe` Right (TyRecord $ Map.fromList [("x", TyNat), ("y", TyBool)])

  describe "Projection" $ do
    it "{x = 0}.x : Nat" $
      typeCheck (TmProj (TmRecord $ Map.fromList [("x", TmZero)]) "x")
        `shouldBe` Right TyNat

    it "{x = 0, y = true}.y : Bool" $
      typeCheck (TmProj (TmRecord $ Map.fromList [("x", TmZero), ("y", TmTrue)]) "y")
        `shouldBe` Right TyBool

  describe "Record subsumption" $ do
    it "(λr:{x: Nat}. r.x) {x = 0, y = true} : Nat" $
      -- {x: Nat, y: Bool} <: {x: Nat}, so this works
      let f = Lam "r" (TyRecord $ Map.fromList [("x", TyNat)]) (TmProj (Var "r") "x")
          arg = TmRecord $ Map.fromList [("x", TmZero), ("y", TmTrue)]
      in typeCheck (App f arg) `shouldBe` Right TyNat

  describe "Ascription" $ do
    it "true as Bool : Bool" $
      typeCheck (TmAscribe TmTrue TyBool) `shouldBe` Right TyBool

    it "true as Top : Top" $
      typeCheck (TmAscribe TmTrue TyTop) `shouldBe` Right TyTop

    it "0 as Top : Top" $
      typeCheck (TmAscribe TmZero TyTop) `shouldBe` Right TyTop

    it "true as Nat fails" $
      case typeCheck (TmAscribe TmTrue TyNat) of
        Left _ -> True `shouldBe` True
        Right _ -> expectationFailure "Should have failed"

  describe "If-then-else with join" $ do
    it "if true then 0 else succ 0 : Nat" $
      typeCheck (TmIf TmTrue TmZero (TmSucc TmZero)) `shouldBe` Right TyNat

    it "if true then {x=0,y=true} else {x=succ 0} : {x: Nat}" $
      -- Join of {x:Nat,y:Bool} and {x:Nat} is {x:Nat}
      let r1 = TmRecord $ Map.fromList [("x", TmZero), ("y", TmTrue)]
          r2 = TmRecord $ Map.fromList [("x", TmSucc TmZero)]
      in typeCheck (TmIf TmTrue r1 r2)
           `shouldBe` Right (TyRecord $ Map.fromList [("x", TyNat)])

-- =============================================================================
-- Evaluation Tests
-- =============================================================================

evalSpec :: Spec
evalSpec = describe "Evaluation" $ do

  describe "Basic values" $ do
    it "true evaluates to true" $
      eval TmTrue `shouldBe` TmTrue

    it "0 evaluates to 0" $
      eval TmZero `shouldBe` TmZero

  describe "Application" $ do
    it "(λx:Bool. x) true → true" $
      eval (App (Lam "x" TyBool (Var "x")) TmTrue) `shouldBe` TmTrue

  describe "Conditionals" $ do
    it "if true then 0 else succ 0 → 0" $
      eval (TmIf TmTrue TmZero (TmSucc TmZero)) `shouldBe` TmZero

    it "if false then 0 else succ 0 → succ 0" $
      eval (TmIf TmFalse TmZero (TmSucc TmZero)) `shouldBe` TmSucc TmZero

  describe "Arithmetic" $ do
    it "pred (succ 0) → 0" $
      eval (TmPred (TmSucc TmZero)) `shouldBe` TmZero

    it "iszero 0 → true" $
      eval (TmIsZero TmZero) `shouldBe` TmTrue

    it "iszero (succ 0) → false" $
      eval (TmIsZero (TmSucc TmZero)) `shouldBe` TmFalse

  describe "Records" $ do
    it "{x = 0}.x → 0" $
      eval (TmProj (TmRecord $ Map.fromList [("x", TmZero)]) "x")
        `shouldBe` TmZero

    it "{x = succ 0, y = true}.x → succ 0" $
      eval (TmProj (TmRecord $ Map.fromList [("x", TmSucc TmZero), ("y", TmTrue)]) "x")
        `shouldBe` TmSucc TmZero

  describe "Ascription" $ do
    it "(true as Top) → true" $
      eval (TmAscribe TmTrue TyTop) `shouldBe` TmTrue

-- =============================================================================
-- Parser Tests
-- =============================================================================

parserSpec :: Spec
parserSpec = describe "Parser" $ do

  describe "Types" $ do
    it "parses Bool" $
      parseType "Bool" `shouldBe` Right TyBool

    it "parses Nat" $
      parseType "Nat" `shouldBe` Right TyNat

    it "parses Top" $
      parseType "Top" `shouldBe` Right TyTop

    it "parses Bot" $
      parseType "Bot" `shouldBe` Right TyBot

    it "parses Bool -> Nat" $
      parseType "Bool -> Nat" `shouldBe` Right (TyArr TyBool TyNat)

    it "parses {x: Nat}" $
      parseType "{x: Nat}" `shouldBe` Right (TyRecord $ Map.fromList [("x", TyNat)])

  describe "Terms" $ do
    it "parses true" $
      parseTerm "true" `shouldBe` Right TmTrue

    it "parses false" $
      parseTerm "false" `shouldBe` Right TmFalse

    it "parses 0" $
      parseTerm "0" `shouldBe` Right TmZero

    it "parses lambda" $
      parseTerm "\\x:Bool. x" `shouldBe` Right (Lam "x" TyBool (Var "x"))

    it "parses application" $
      parseTerm "(\\x:Bool. x) true"
        `shouldBe` Right (App (Lam "x" TyBool (Var "x")) TmTrue)

    it "parses record" $
      parseTerm "{x = 0}"
        `shouldBe` Right (TmRecord $ Map.fromList [("x", TmZero)])

    it "parses projection" $
      parseTerm "{x = 0}.x"
        `shouldBe` Right (TmProj (TmRecord $ Map.fromList [("x", TmZero)]) "x")

    it "parses ascription" $
      parseTerm "true as Top"
        `shouldBe` Right (TmAscribe TmTrue TyTop)

-- =============================================================================
-- Pretty Printer Tests
-- =============================================================================

prettySpec :: Spec
prettySpec = describe "Pretty Printer" $ do

  describe "Types" $ do
    it "prints Bool" $
      prettyType TyBool `shouldBe` "Bool"

    it "prints Top" $
      prettyType TyTop `shouldBe` "Top"

    it "prints function type" $
      prettyType (TyArr TyBool TyNat) `shouldBe` "Bool -> Nat"

  describe "Terms" $ do
    it "prints true" $
      prettyTerm TmTrue `shouldBe` "true"

    it "prints lambda" $
      prettyTerm (Lam "x" TyBool (Var "x")) `shouldBe` "λx:Bool. x"

    it "prints record" $
      prettyTerm (TmRecord $ Map.fromList [("x", TmZero)])
        `shouldBe` "{x = 0}"

    it "prints natural numbers" $
      prettyTerm (TmSucc (TmSucc TmZero)) `shouldBe` "2"
