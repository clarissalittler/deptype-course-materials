{-# LANGUAGE LambdaCase #-}

module ExerciseSpec (spec) where

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import qualified Solutions as S

-- Helper to check if type checking succeeds
typeCheckSucceeds :: Term -> Expectation
typeCheckSucceeds t = case typeCheck t of
  Right _ -> return ()
  Left err -> expectationFailure $ "Type checking failed: " ++ show err

-- Helper to check if type checking fails
typeCheckFails :: Term -> Expectation
typeCheckFails t = case typeCheck t of
  Left _ -> return ()
  Right ty -> expectationFailure $ "Expected type error, but got type: " ++ show ty

-- Helper to check inferred type
hasType :: Term -> Type -> Expectation
hasType t expected = case typeCheck t of
  Right ty -> ty `shouldBe` expected
  Left err -> expectationFailure $ "Type checking failed: " ++ show err

-- Helper to evaluate to normal form
evalToNorm :: Term -> Term
evalToNorm = eval

-- Helper to convert Nat term to Int
natToInt :: Term -> Maybe Int
natToInt TmZero = Just 0
natToInt (TmSucc n) = (+ 1) <$> natToInt n
natToInt _ = Nothing

-- Helper to create Nat from Int
natFromInt :: Int -> Term
natFromInt 0 = TmZero
natFromInt n = TmSucc (natFromInt (n - 1))

spec :: Spec
spec = do
  describe "Exercise 1: Church Encodings" $ do
    describe "1a. Option Type" $ do
      it "none type checks" $ do
        typeCheckSucceeds S.none

      it "none has correct type" $ do
        S.none `hasType` TyForall "A" (S.optionType (TyVar "A"))

      it "some type checks" $ do
        typeCheckSucceeds S.some

      it "some has correct type" $ do
        S.some `hasType` TyForall "A" (TyArr (TyVar "A") (S.optionType (TyVar "A")))

      it "matchOption type checks" $ do
        typeCheckSucceeds S.matchOption

      it "matchOption none returns default" $ do
        -- matchOption [Nat] [Nat] (none [Nat]) 42 (λx. succ x)
        let noneNat = TyApp S.none TyNat
        let defaultVal = natFromInt 42
        let someFn = Lam "x" TyNat (TmSucc (Var "x"))
        let result = evalToNorm $
              App (App (App (TyApp (TyApp S.matchOption TyNat) TyNat) noneNat)
                        defaultVal)
                  someFn
        result `shouldBe` defaultVal

      it "matchOption some applies function" $ do
        -- matchOption [Nat] [Nat] (some [Nat] 5) 42 (λx. succ x) = 6
        let someVal = App (TyApp S.some TyNat) (natFromInt 5)
        let defaultVal = natFromInt 42
        let someFn = Lam "x" TyNat (TmSucc (Var "x"))
        let result = evalToNorm $
              App (App (App (TyApp (TyApp S.matchOption TyNat) TyNat) someVal)
                        defaultVal)
                  someFn
        natToInt result `shouldBe` Just 6

    describe "1b. Either Type" $ do
      it "left type checks" $ do
        typeCheckSucceeds S.eitherLeft

      it "left has correct type" $ do
        S.eitherLeft `hasType`
          TyForall "A" (TyForall "B"
            (TyArr (TyVar "A") (S.eitherType (TyVar "A") (TyVar "B"))))

      it "right type checks" $ do
        typeCheckSucceeds S.eitherRight

      it "right has correct type" $ do
        S.eitherRight `hasType`
          TyForall "A" (TyForall "B"
            (TyArr (TyVar "B") (S.eitherType (TyVar "A") (TyVar "B"))))

      it "matchEither type checks" $ do
        typeCheckSucceeds S.matchEither

      it "matchEither left applies left function" $ do
        -- matchEither [Nat] [Bool] [Nat] (left [Nat] [Bool] 5) (λx. succ x) (λy. 0) = 6
        let leftVal = App (TyApp (TyApp S.eitherLeft TyNat) TyBool) (natFromInt 5)
        let leftFn = Lam "x" TyNat (TmSucc (Var "x"))
        let rightFn = Lam "y" TyBool TmZero
        let result = evalToNorm $
              App (App (App (TyApp (TyApp (TyApp S.matchEither TyNat) TyBool) TyNat)
                            leftVal)
                        leftFn)
                  rightFn
        natToInt result `shouldBe` Just 6

      it "matchEither right applies right function" $ do
        -- matchEither [Nat] [Bool] [Bool] (right [Nat] [Bool] true) (λx. false) (λy. y) = true
        let rightVal = App (TyApp (TyApp S.eitherRight TyNat) TyBool) TmTrue
        let leftFn = Lam "x" TyNat TmFalse
        let rightFn = Lam "y" TyBool (Var "y")
        let result = evalToNorm $
              App (App (App (TyApp (TyApp (TyApp S.matchEither TyNat) TyBool) TyBool)
                            rightVal)
                        leftFn)
                  rightFn
        result `shouldBe` TmTrue

  describe "Exercise 2: Polymorphic Data Structures" $ do
    describe "2a. Binary Trees" $ do
      it "leaf type checks" $ do
        typeCheckSucceeds S.treeLeaf

      it "leaf has correct type" $ do
        S.treeLeaf `hasType` TyForall "A" (S.treeType (TyVar "A"))

      it "node type checks" $ do
        typeCheckSucceeds S.treeNode

      it "node has correct type" $ do
        S.treeNode `hasType`
          TyForall "A"
            (TyArr (TyVar "A")
              (TyArr (S.treeType (TyVar "A"))
                (TyArr (S.treeType (TyVar "A"))
                  (S.treeType (TyVar "A")))))

      it "treeMap type checks" $ do
        typeCheckSucceeds S.treeMap

      it "treeMap has correct type" $ do
        S.treeMap `hasType`
          TyForall "A" (TyForall "B"
            (TyArr (TyArr (TyVar "A") (TyVar "B"))
              (TyArr (S.treeType (TyVar "A"))
                (S.treeType (TyVar "B")))))

      it "treeMap over leaf" $ do
        let succFn = Lam "x" TyNat (TmSucc (Var "x"))
        let leaf = TyApp S.treeLeaf TyNat
        let result = App (App (TyApp (TyApp S.treeMap TyNat) TyNat) succFn) leaf
        typeCheckSucceeds result

      it "treeFold type checks" $ do
        typeCheckSucceeds S.treeFold

      it "treeFold has correct type" $ do
        S.treeFold `hasType`
          TyForall "A" (TyForall "B"
            (TyArr (TyVar "B")
              (TyArr (TyArr (TyVar "A")
                      (TyArr (TyVar "B")
                        (TyArr (TyVar "B") (TyVar "B"))))
                (TyArr (S.treeType (TyVar "A"))
                  (TyVar "B")))))

      it "treeFold over leaf returns zero" $ do
        -- treeFold [Nat] [Nat] 42 (λx λl λr. x) (leaf [Nat]) = 42
        let leaf = TyApp S.treeLeaf TyNat
        let zero = natFromInt 42
        let combiner = Lam "x" TyNat (Lam "l" TyNat (Lam "r" TyNat (Var "x")))
        let result = evalToNorm $
              App (App (App (TyApp (TyApp S.treeFold TyNat) TyNat) zero) combiner) leaf
        result `shouldBe` zero

      it "treeHeight type checks" $ do
        typeCheckSucceeds S.treeHeight

      it "treeHeight has correct type" $ do
        S.treeHeight `hasType` TyForall "A" (TyArr (S.treeType (TyVar "A")) TyNat)

      it "treeHeight of leaf is zero" $ do
        let leaf = TyApp S.treeLeaf TyNat
        let result = evalToNorm $ App (TyApp S.treeHeight TyNat) leaf
        natToInt result `shouldBe` Just 0

  describe "Exercise 3: Church Numerals Extended" $ do
    it "cnatZero type checks" $ do
      typeCheckSucceeds S.cnatZero

    it "cnatZero has correct type" $ do
      S.cnatZero `hasType` S.cnatType

    it "cnatOne type checks" $ do
      typeCheckSucceeds S.cnatOne

    it "cnatSucc type checks" $ do
      typeCheckSucceeds S.cnatSucc

    it "cnatAdd type checks" $ do
      typeCheckSucceeds S.cnatAdd

    it "cnatAdd has correct type" $ do
      S.cnatAdd `hasType` TyArr S.cnatType (TyArr S.cnatType S.cnatType)

    it "cnatMult type checks" $ do
      typeCheckSucceeds S.cnatMult

    it "cnatMult has correct type" $ do
      S.cnatMult `hasType` TyArr S.cnatType (TyArr S.cnatType S.cnatType)

    describe "3a. Exponentiation" $ do
      it "cnatExp type checks" $ do
        typeCheckSucceeds S.cnatExp

      it "cnatExp has correct type" $ do
        S.cnatExp `hasType` TyArr S.cnatType (TyArr S.cnatType S.cnatType)

    describe "3b. Factorial" $ do
      it "cnatFactorial type checks" $ do
        typeCheckSucceeds S.cnatFactorial

      it "cnatFactorial has correct type" $ do
        S.cnatFactorial `hasType` TyArr S.cnatType S.cnatType

    describe "3c. Division" $ do
      it "cnatDiv type checks" $ do
        typeCheckSucceeds S.cnatDiv

      it "cnatDiv has correct type" $ do
        S.cnatDiv `hasType` TyArr S.cnatType (TyArr S.cnatType S.cnatType)

  describe "Exercise 4: Existential Types" $ do
    describe "4a. Encode Existentials" $ do
      it "existentialPack type checks for Nat" $ do
        let packNat = S.existentialPack TyNat
        typeCheckSucceeds packNat

      it "existentialUnpack type checks for Nat" $ do
        let unpackNat = S.existentialUnpack TyNat
        typeCheckSucceeds unpackNat

    describe "4b. Abstract Counter" $ do
      it "makeCounter type checks" $ do
        typeCheckSucceeds S.makeCounter

  describe "Exercise 6: Impredicativity" $ do
    describe "6a. Self-Application" $ do
      it "polyId type checks" $ do
        typeCheckSucceeds S.polyId

      it "polyId has correct type" $ do
        S.polyId `hasType` TyForall "A" (TyArr (TyVar "A") (TyVar "A"))

      it "selfApply type checks (impredicativity!)" $ do
        typeCheckSucceeds S.selfApply

      it "selfApply has correct type" $ do
        S.selfApply `hasType` TyForall "A" (TyArr (TyVar "A") (TyVar "A"))

      it "selfApply evaluates to identity" $ do
        let result = evalToNorm S.selfApply
        -- Result should still be the identity function
        typeCheckSucceeds result

    describe "6c. Nested Polymorphism" $ do
      it "twice type checks" $ do
        typeCheckSucceeds S.twice

      it "twice has correct type" $ do
        S.twice `hasType`
          TyForall "A"
            (TyArr (TyArr (TyVar "A") (TyVar "A"))
              (TyArr (TyVar "A") (TyVar "A")))

      it "polyTwice type checks" $ do
        typeCheckSucceeds S.polyTwice

      it "polyTwice has correct type" $ do
        S.polyTwice `hasType`
          TyArr (TyForall "A" (TyArr (TyVar "A") (TyVar "A")))
            (TyForall "B" (TyArr (TyVar "B") (TyVar "B")))

  describe "Example Programs" $ do
    it "Example 1: some [Nat] 5 type checks" $ do
      typeCheckSucceeds S.example1

    it "Example 1: has Option Nat type" $ do
      S.example1 `hasType` S.optionType TyNat

    it "Example 2: matchOption type checks" $ do
      typeCheckSucceeds S.example2

    it "Example 2: has Bool type" $ do
      S.example2 `hasType` TyBool

    it "Example 2: evaluates to true" $ do
      evalToNorm S.example2 `shouldBe` TmTrue

    it "Example 3: left [Nat] [Bool] 0 type checks" $ do
      typeCheckSucceeds S.example3

    it "Example 3: has Either Nat Bool type" $ do
      S.example3 `hasType` S.eitherType TyNat TyBool

    it "Example 4: tree construction type checks" $ do
      typeCheckSucceeds S.example4

    it "Example 4: has Tree Nat type" $ do
      S.example4 `hasType` S.treeType TyNat

    it "Example 5: treeMap type checks" $ do
      typeCheckSucceeds S.example5

    it "Example 5: has Tree Nat type" $ do
      S.example5 `hasType` S.treeType TyNat

    it "Example 6: Church numeral addition type checks" $ do
      typeCheckSucceeds S.example6

    it "Example 6: has CNat type" $ do
      S.example6 `hasType` S.cnatType

    it "Example 7: self-application type checks" $ do
      typeCheckSucceeds S.example7

    it "Example 7: has polymorphic identity type" $ do
      S.example7 `hasType` TyForall "A" (TyArr (TyVar "A") (TyVar "A"))

    it "Example 8: polyTwice id type checks" $ do
      typeCheckSucceeds S.example8

    it "Example 8: has polymorphic identity type" $ do
      S.example8 `hasType` TyForall "B" (TyArr (TyVar "B") (TyVar "B"))

  describe "Theoretical Exercises" $ do
    it "Parametricity explanation is non-empty" $ do
      S.parametricityExplanation `shouldSatisfy` (not . null)

    it "System F limitations explanation is non-empty" $ do
      S.systemFLimitationsExplanation `shouldSatisfy` (not . null)

    it "Free theorems examples is non-empty" $ do
      S.freeTheoremsExamples `shouldSatisfy` (not . null)
