{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec

import Syntax
import TypeCheck
import Eval
import Parser

main :: IO ()
main = hspec $ do
  linearitySpec
  typeCheckSpec
  evalSpec
  parserSpec

-- =============================================================================
-- Linearity Tests
-- =============================================================================

linearitySpec :: Spec
linearitySpec = describe "Linearity Checking" $ do

  describe "Linear variable usage" $ do
    it "linear variable used once is OK" $
      -- λx :1 Nat. x
      typeCheck (Lam "x" One TyNat (Var "x"))
        `shouldBe` Right (TyFun One TyNat TyNat)

    it "linear variable not used is error" $
      -- λx :1 Nat. 0
      case typeCheck (Lam "x" One TyNat TmZero) of
        Left (LinearVariableUnused "x") -> True `shouldBe` True
        _ -> expectationFailure "Expected LinearVariableUnused"

    it "linear variable used twice is error" $
      -- λx :1 Nat. (x, x)  -- illegal!
      case typeCheck (Lam "x" One TyNat (TmPair (Var "x") (Var "x"))) of
        Left (LinearVariableUsedTwice "x") -> True `shouldBe` True
        _ -> expectationFailure "Expected LinearVariableUsedTwice"

    it "linear variable used in only one branch is error" $
      -- λx :1 Nat. if true then x else 0
      case typeCheck (Lam "x" One TyNat (TmIf TmTrue (Var "x") TmZero)) of
        Left (LinearVariableUsedInBranch "x") -> True `shouldBe` True
        _ -> expectationFailure "Expected LinearVariableUsedInBranch"

    it "linear variable passed to unrestricted function is error" $
      -- λy :1 Nat. (λx :ω Nat. x) y
      let term = Lam "y" One TyNat (App (Lam "x" Many TyNat (Var "x")) (Var "y"))
      in case typeCheck term of
           Left (LinearVariableUsedTwice "y") -> True `shouldBe` True
           _ -> expectationFailure "Expected LinearVariableUsedTwice"

  describe "Unrestricted variable usage" $ do
    it "unrestricted variable used once is OK" $
      typeCheck (Lam "x" Many TyNat (Var "x"))
        `shouldBe` Right (TyFun Many TyNat TyNat)

    it "unrestricted variable not used is OK" $
      typeCheck (Lam "x" Many TyNat TmZero)
        `shouldBe` Right (TyFun Many TyNat TyNat)

    it "unrestricted variable used twice is OK" $
      typeCheck (Lam "x" Many TyNat (TmPair (Var "x") (Var "x")))
        `shouldBe` Right (TyFun Many TyNat (TyPair TyNat TyNat))

  describe "Pairs and let-pair" $ do
    it "let-pair uses both components linearly" $
      -- let (x, y) = (0, true) in x
      let term = TmLetPair "x" "y" (TmPair TmZero TmTrue) (Var "x")
      in case typeCheck term of
           Left (LinearVariableUnused "y") -> True `shouldBe` True
           _ -> expectationFailure "Expected y to be unused error"

    it "let-pair with both used is OK" $
      -- let (x, y) = (0, true) in (x, y)
      let term = TmLetPair "x" "y" (TmPair TmZero TmTrue) (TmPair (Var "x") (Var "y"))
      in typeCheck term `shouldBe` Right (TyPair TyNat TyBool)

-- =============================================================================
-- Type Checking Tests
-- =============================================================================

typeCheckSpec :: Spec
typeCheckSpec = describe "Type Checking" $ do

  describe "Basic terms" $ do
    it "true : Bool" $
      typeCheck TmTrue `shouldBe` Right TyBool

    it "0 : Nat" $
      typeCheck TmZero `shouldBe` Right TyNat

    it "() : ()" $
      typeCheck TmUnit `shouldBe` Right TyUnit

  describe "Linear functions" $ do
    it "linear identity has linear type" $
      typeCheck (Lam "x" One TyBool (Var "x"))
        `shouldBe` Right (TyFun One TyBool TyBool)

    it "linear function application" $
      let f = Lam "x" One TyNat (Var "x")
          app = App f TmZero
      in typeCheck app `shouldBe` Right TyNat

  describe "Unrestricted functions" $ do
    it "unrestricted identity" $
      typeCheck (Lam "x" Many TyBool (Var "x"))
        `shouldBe` Right (TyFun Many TyBool TyBool)

    it "K combinator (discards argument)" $
      -- λx :w Nat. λy :1 Bool. x
      let k = Lam "x" Many TyNat (Lam "y" One TyBool (Var "y"))
      in typeCheck k `shouldBe` Right (TyFun Many TyNat (TyFun One TyBool TyBool))

  describe "Pairs" $ do
    it "pair of values" $
      typeCheck (TmPair TmZero TmTrue)
        `shouldBe` Right (TyPair TyNat TyBool)

    it "nested pairs" $
      typeCheck (TmPair (TmPair TmZero TmZero) TmTrue)
        `shouldBe` Right (TyPair (TyPair TyNat TyNat) TyBool)

  describe "Bang types" $ do
    it "bang of value" $
      typeCheck (TmBang TmZero) `shouldBe` Right (TyBang TyNat)

    it "bang allows unrestricted variables" $
      typeCheck (Lam "u" Many TyNat (TmBang (Var "u")))
        `shouldBe` Right (TyFun Many TyNat (TyBang TyNat))

    it "let-bang makes variable unrestricted" $
      -- let !x = !0 in (x, x)
      let term = TmLetBang "x" (TmBang TmZero) (TmPair (Var "x") (Var "x"))
      in typeCheck term `shouldBe` Right (TyPair TyNat TyNat)

  describe "Conditionals" $ do
    it "if-then-else with same types" $
      typeCheck (TmIf TmTrue TmZero (TmSucc TmZero))
        `shouldBe` Right TyNat

-- =============================================================================
-- Evaluation Tests
-- =============================================================================

evalSpec :: Spec
evalSpec = describe "Evaluation" $ do

  describe "Values" $ do
    it "true is value" $
      isValue TmTrue `shouldBe` True

    it "lambda is value" $
      isValue (Lam "x" One TyNat (Var "x")) `shouldBe` True

    it "pair of values is value" $
      isValue (TmPair TmZero TmTrue) `shouldBe` True

  describe "Application" $ do
    it "linear function application" $
      eval (App (Lam "x" One TyNat (Var "x")) TmZero)
        `shouldBe` TmZero

    it "unrestricted function application" $
      eval (App (Lam "x" Many TyNat (TmPair (Var "x") (Var "x"))) TmZero)
        `shouldBe` TmPair TmZero TmZero

  describe "Let" $ do
    it "preserves multiplicity while stepping" $
      evalStep (TmLet "x" Many (TmPred (TmSucc TmZero)) (Var "x"))
        `shouldBe` Just (TmLet "x" Many TmZero (Var "x"))

  describe "Let-pair" $ do
    it "let-pair elimination" $
      eval (TmLetPair "x" "y" (TmPair TmZero TmTrue) (Var "x"))
        `shouldBe` TmZero

    it "let-pair with swap" $
      eval (TmLetPair "x" "y" (TmPair TmZero TmTrue) (TmPair (Var "y") (Var "x")))
        `shouldBe` TmPair TmTrue TmZero

  describe "Bang" $ do
    it "let-bang elimination" $
      eval (TmLetBang "x" (TmBang TmZero) (Var "x"))
        `shouldBe` TmZero

    it "let-bang allows duplication" $
      eval (TmLetBang "x" (TmBang TmZero) (TmPair (Var "x") (Var "x")))
        `shouldBe` TmPair TmZero TmZero

  describe "Conditionals" $ do
    it "if true" $
      eval (TmIf TmTrue TmZero (TmSucc TmZero)) `shouldBe` TmZero

    it "if false" $
      eval (TmIf TmFalse TmZero (TmSucc TmZero)) `shouldBe` TmSucc TmZero

  describe "Arithmetic" $ do
    it "pred (succ 0)" $
      eval (TmPred (TmSucc TmZero)) `shouldBe` TmZero

    it "iszero 0" $
      eval (TmIsZero TmZero) `shouldBe` TmTrue

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

    it "parses linear function" $
      parseType "Nat -o Bool" `shouldBe` Right (TyFun One TyNat TyBool)

    it "parses unrestricted function" $
      parseType "Nat -> Bool" `shouldBe` Right (TyFun Many TyNat TyBool)

    it "parses pair type" $
      parseType "Nat * Bool" `shouldBe` Right (TyPair TyNat TyBool)

    it "parses bang type" $
      parseType "!Nat" `shouldBe` Right (TyBang TyNat)

  describe "Terms" $ do
    it "parses true" $
      parseTerm "true" `shouldBe` Right TmTrue

    it "parses 0" $
      parseTerm "0" `shouldBe` Right TmZero

    it "parses numeric literals" $
      parseTerm "2" `shouldBe` Right (TmSucc (TmSucc TmZero))

    it "parses unit" $
      parseTerm "()" `shouldBe` Right TmUnit

    it "parses pair" $
      parseTerm "(0, true)" `shouldBe` Right (TmPair TmZero TmTrue)

    it "parses bang" $
      parseTerm "!0" `shouldBe` Right (TmBang TmZero)

    it "parses omega multiplicity" $
      parseTerm "\\x:ω Nat. x" `shouldBe` Right (Lam "x" Many TyNat (Var "x"))

    it "parses linear lambda" $
      parseTerm "\\x :1 Nat. x"
        `shouldBe` Right (Lam "x" One TyNat (Var "x"))
