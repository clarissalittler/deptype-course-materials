{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Data.Text (Text)
import qualified Data.Set

import Syntax
import Parser
import TypeCheck
import Eval
import Pretty

main :: IO ()
main = hspec $ do
  describe "Syntax" $ do
    describe "Type substitution" $ do
      it "substitutes type variable in simple type" $ do
        substTyVar "a" TyNat (TyVar "a") `shouldBe` TyNat

      it "does not substitute different variable" $ do
        substTyVar "a" TyNat (TyVar "b") `shouldBe` TyVar "b"

      it "substitutes in function type" $ do
        substTyVar "a" TyNat (TyFun (TyVar "a") (TyVar "a"))
          `shouldBe` TyFun TyNat TyNat

      it "substitutes in product type" $ do
        substTyVar "a" TyBool (TyProd (TyVar "a") TyNat)
          `shouldBe` TyProd TyBool TyNat

      it "does not substitute bound variable in mu" $ do
        substTyVar "a" TyNat (TyMu "a" (TyVar "a"))
          `shouldBe` TyMu "a" (TyVar "a")

      it "substitutes free variable in mu body" $ do
        substTyVar "b" TyNat (TyMu "a" (TyFun (TyVar "a") (TyVar "b")))
          `shouldBe` TyMu "a" (TyFun (TyVar "a") TyNat)

    describe "Free type variables" $ do
      it "finds variable in TyVar" $ do
        freeTyVars (TyVar "a") `shouldBe` fromList ["a"]

      it "finds no variables in base types" $ do
        freeTyVars TyBool `shouldBe` fromList []
        freeTyVars TyNat `shouldBe` fromList []

      it "binds variable in mu" $ do
        freeTyVars (TyMu "a" (TyVar "a")) `shouldBe` fromList []

      it "finds free but not bound in mu" $ do
        freeTyVars (TyMu "a" (TyFun (TyVar "a") (TyVar "b")))
          `shouldBe` fromList ["b"]

  describe "TypeCheck" $ do
    describe "Recursive types" $ do
      it "types fold correctly" $ do
        let natList = TyMu "a" (TySum TyUnit (TyProd TyNat (TyVar "a")))
        let nil = TmFold natList (TmInl TmUnit (TySum TyUnit (TyProd TyNat natList)))
        typeCheck nil `shouldBe` Right natList

      it "types unfold correctly" $ do
        let natList = TyMu "a" (TySum TyUnit (TyProd TyNat (TyVar "a")))
        let nil = TmFold natList (TmInl TmUnit (TySum TyUnit (TyProd TyNat natList)))
        let unfolded = TmUnfold natList nil
        typeCheck unfolded `shouldBe` Right (TySum TyUnit (TyProd TyNat natList))

      it "rejects fold with wrong inner type" $ do
        let natList = TyMu "a" (TySum TyUnit (TyProd TyNat (TyVar "a")))
        let wrong = TmFold natList TmTrue
        typeCheck wrong `shouldSatisfy` isLeft

      it "rejects unfold on non-recursive type" $ do
        let wrong = TmUnfold TyNat TmZero
        typeCheck wrong `shouldSatisfy` isLeft

      it "rejects fold with non-recursive type annotation" $ do
        let wrong = TmFold TyNat TmZero
        typeCheck wrong `shouldSatisfy` isLeft

    describe "unfoldType" $ do
      it "unfolds mu type one step" $ do
        let natList = TyMu "a" (TySum TyUnit (TyProd TyNat (TyVar "a")))
        unfoldType natList `shouldBe` TySum TyUnit (TyProd TyNat natList)

      it "leaves non-recursive types unchanged" $ do
        unfoldType TyNat `shouldBe` TyNat
        unfoldType (TyFun TyNat TyBool) `shouldBe` TyFun TyNat TyBool

  describe "Eval" $ do
    describe "fold/unfold" $ do
      it "unfold . fold = id on values" $ do
        let natList = TyMu "a" (TySum TyUnit (TyProd TyNat (TyVar "a")))
        let inner = TmInl TmUnit (TySum TyUnit (TyProd TyNat natList))
        let folded = TmFold natList inner
        let unfolded = TmUnfold natList folded
        eval unfolded `shouldBe` inner

      it "evaluates inside fold" $ do
        let ty = TyMu "a" (TySum TyUnit (TyVar "a"))
        let term = TmFold ty (TmInl (TmIf TmTrue TmUnit TmUnit) (TySum TyUnit ty))
        isValue (eval term) `shouldBe` True

    describe "isValue" $ do
      it "fold of value is value" $ do
        let ty = TyMu "a" TyUnit
        isValue (TmFold ty TmUnit) `shouldBe` True

      it "fold of non-value is not value" $ do
        let ty = TyMu "a" TyNat
        isValue (TmFold ty (TmSucc TmZero)) `shouldBe` True
        isValue (TmFold ty (TmPred TmZero)) `shouldBe` False

  describe "Parser" $ do
    describe "Types" $ do
      it "parses mu type" $ do
        parseType "mu a. a" `shouldBe` Right (TyMu "a" (TyVar "a"))

      it "parses mu with function body" $ do
        parseType "mu a. a -> a"
          `shouldBe` Right (TyMu "a" (TyFun (TyVar "a") (TyVar "a")))

      it "parses nested mu" $ do
        parseType "mu a. mu b. a + b"
          `shouldBe` Right (TyMu "a" (TyMu "b" (TySum (TyVar "a") (TyVar "b"))))

      it "parses list type" $ do
        parseType "mu a. Unit + (Nat * a)"
          `shouldBe` Right (TyMu "a" (TySum TyUnit (TyProd TyNat (TyVar "a"))))

    describe "Terms" $ do
      it "parses fold" $ do
        let ty = TyMu "a" TyUnit
        parseTerm "fold [mu a. Unit] unit"
          `shouldBe` Right (TmFold ty TmUnit)

      it "parses unfold" $ do
        let ty = TyMu "a" TyUnit
        parseTerm "unfold [mu a. Unit] x"
          `shouldBe` Right (TmUnfold ty (Var "x"))

      it "parses fold with complex type" $ do
        let ty = TyMu "a" (TySum TyUnit (TyVar "a"))
        parseTerm "fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a))"
          `shouldSatisfy` isRight

  describe "Pretty" $ do
    describe "Types" $ do
      it "pretty prints mu type" $ do
        prettyType (TyMu "a" (TyVar "a")) `shouldBe` "μa. a"

      it "pretty prints mu with function" $ do
        prettyType (TyMu "a" (TyFun (TyVar "a") TyNat))
          `shouldBe` "μa. a -> Nat"

    describe "Terms" $ do
      it "pretty prints fold" $ do
        prettyTerm (TmFold (TyMu "a" TyUnit) TmUnit)
          `shouldBe` "fold [μa. Unit] unit"

      it "pretty prints unfold" $ do
        prettyTerm (TmUnfold (TyMu "a" TyNat) (Var "x"))
          `shouldBe` "unfold [μa. Nat] x"

  describe "Integration" $ do
    describe "Natural number lists" $ do
      let natList = TyMu "a" (TySum TyUnit (TyProd TyNat (TyVar "a")))
      let innerTy = TySum TyUnit (TyProd TyNat natList)

      it "nil has correct type" $ do
        let nil = TmFold natList (TmInl TmUnit innerTy)
        typeCheck nil `shouldBe` Right natList

      it "cons has correct type" $ do
        let nil = TmFold natList (TmInl TmUnit innerTy)
        let consExpr = TmFold natList (TmInr (TmPair TmZero nil) innerTy)
        typeCheck consExpr `shouldBe` Right natList

      it "can access head of list" $ do
        let nil = TmFold natList (TmInl TmUnit innerTy)
        let list1 = TmFold natList (TmInr (TmPair (TmSucc TmZero) nil) innerTy)
        let getHead = TmCase (TmUnfold natList list1)
                        "n" TmZero
                        "p" (TmFst (Var "p"))
        eval getHead `shouldBe` TmSucc TmZero

    describe "Infinite types" $ do
      it "types omega combinator body" $ do
        -- ω = λx. unfold x (fold x)
        -- Type: μa. a -> T
        let selfApp = TyMu "a" (TyFun (TyVar "a") TyNat)
        let omega = Lam "x" selfApp
                      (App (TmUnfold selfApp (Var "x"))
                           (Var "x"))
        typeCheck omega `shouldBe` Right (TyFun selfApp TyNat)

-- Helper functions
isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

fromList :: Ord a => [a] -> Data.Set.Set a
fromList = Data.Set.fromList
