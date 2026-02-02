{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import qualified Data.Map.Strict as Map

import Syntax hiding (Spec)
import TypeCheck
import Eval
import Parser
import Pretty

main :: IO ()
main = hspec $ do
  typeCheckSpec
  evalSpec
  parserSpec
  prettySpec
  moduleSpec
  signatureSpec

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

    it "parses record" $
      parseTerm "{x = 0}"
        `shouldBe` Right (TmRecord $ Map.fromList [("x", TmZero)])

-- =============================================================================
-- Pretty Printer Tests
-- =============================================================================

prettySpec :: Spec
prettySpec = describe "Pretty Printer" $ do

  describe "Types" $ do
    it "prints Bool" $
      prettyType TyBool `shouldBe` "Bool"

    it "prints function type" $
      prettyType (TyArr TyBool TyNat) `shouldBe` "Bool -> Nat"

  describe "Terms" $ do
    it "prints true" $
      prettyTerm TmTrue `shouldBe` "true"

    it "prints lambda" $
      prettyTerm (Lam "x" TyBool (Var "x")) `shouldBe` "λx:Bool. x"

    it "prints natural numbers" $
      prettyTerm (TmSucc (TmSucc TmZero)) `shouldBe` "2"

-- =============================================================================
-- Module Tests
-- =============================================================================

moduleSpec :: Spec
moduleSpec = describe "Modules" $ do

  describe "Simple structures" $ do
    it "struct with value" $ do
      let m = Struct [ValDecl "x" TyNat TmZero]
          expected = Sig [ValSpec "x" TyNat]
      typeCheckMod emptyContext m `shouldBe` Right expected

    it "struct with type" $ do
      let m = Struct [TypeDecl "t" (Just TyNat)]
          expected = Sig [TypeSpec "t" (Just TyNat)]
      typeCheckMod emptyContext m `shouldBe` Right expected

    it "struct with value and type" $ do
      let m = Struct [TypeDecl "t" (Just TyNat), ValDecl "x" (TyNamed "t") TmZero]
      case typeCheckMod emptyContext m of
        Right _ -> True `shouldBe` True
        Left err -> expectationFailure $ "Should type check: " ++ err

  describe "Module variables" $ do
    it "module variable lookup" $ do
      let sig = Sig [ValSpec "x" TyNat]
          ctx = extendMod "M" sig emptyContext
      typeCheckMod ctx (ModVar "M") `shouldBe` Right sig

  describe "Nested modules" $ do
    it "struct with nested module" $ do
      let inner = Struct [ValDecl "x" TyNat TmZero]
          outer = Struct [ModDecl "N" inner]
      case typeCheckMod emptyContext outer of
        Right _ -> True `shouldBe` True
        Left err -> expectationFailure $ "Should type check: " ++ err

-- =============================================================================
-- Signature Matching Tests
-- =============================================================================

signatureSpec :: Spec
signatureSpec = describe "Signature Matching" $ do

  describe "Value specifications" $ do
    it "exact match succeeds" $ do
      let impl = Sig [ValSpec "x" TyNat]
          req = Sig [ValSpec "x" TyNat]
      matchSignature impl req `shouldBe` Right ()

    it "missing value fails" $ do
      let impl = Sig []
          req = Sig [ValSpec "x" TyNat]
      case matchSignature impl req of
        Left _ -> True `shouldBe` True
        Right _ -> expectationFailure "Should fail"

    it "type mismatch fails" $ do
      let impl = Sig [ValSpec "x" TyBool]
          req = Sig [ValSpec "x" TyNat]
      case matchSignature impl req of
        Left _ -> True `shouldBe` True
        Right _ -> expectationFailure "Should fail"

  describe "Type specifications" $ do
    it "abstract type matches any type" $ do
      let impl = Sig [TypeSpec "t" (Just TyNat)]
          req = Sig [TypeSpec "t" Nothing]
      matchSignature impl req `shouldBe` Right ()

    it "manifest type must match exactly" $ do
      let impl = Sig [TypeSpec "t" (Just TyNat)]
          req = Sig [TypeSpec "t" (Just TyNat)]
      matchSignature impl req `shouldBe` Right ()

  describe "Width subtyping" $ do
    it "more specifications than required" $ do
      let impl = Sig [ValSpec "x" TyNat, ValSpec "y" TyBool]
          req = Sig [ValSpec "x" TyNat]
      matchSignature impl req `shouldBe` Right ()

  describe "Sealing" $ do
    it "sealing hides extra components" $ do
      let m = Struct [ValDecl "x" TyNat TmZero, ValDecl "y" TyBool TmTrue]
          sig = Sig [ValSpec "x" TyNat]
          sealed = Seal m sig
      typeCheckMod emptyContext sealed `shouldBe` Right sig
