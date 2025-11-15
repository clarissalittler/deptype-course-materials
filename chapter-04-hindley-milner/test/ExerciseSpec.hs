{-# LANGUAGE LambdaCase #-}

module ExerciseSpec (spec) where

import Test.Hspec
import Syntax
import Infer
import Eval
import qualified Solutions as S
import Control.Monad (unless)

-- Helper to check if type inference succeeds
inferSucceeds :: Term -> Expectation
inferSucceeds t = case infer t of
  Right _ -> return ()
  Left err -> expectationFailure $ "Type inference failed: " ++ show err

-- Helper to check if type inference fails
inferFails :: Term -> Expectation
inferFails t = case infer t of
  Left _ -> return ()
  Right ty -> expectationFailure $ "Expected type error, but got type: " ++ show ty

-- Helper to check inferred type
hasType :: Term -> Type -> Expectation
hasType t expected = case infer t of
  Right ty -> ty `shouldBe` expected
  Left err -> expectationFailure $ "Type inference failed: " ++ show err

-- Helper to check if type contains certain structure (for polymorphic types)
hasTypeStructure :: Term -> (Type -> Bool) -> String -> Expectation
hasTypeStructure t predicate desc = case infer t of
  Right ty -> unless (predicate ty) $
    expectationFailure $ "Type " ++ show ty ++ " doesn't match expected structure: " ++ desc
  Left err -> expectationFailure $ "Type inference failed: " ++ show err

-- Helper to evaluate to normal form
evalToNorm :: Term -> Term
evalToNorm = eval

-- Helper to convert Nat term to Int
natToInt :: Term -> Maybe Int
natToInt TmZero = Just 0
natToInt (TmSucc n) = (+ 1) <$> natToInt n
natToInt _ = Nothing

-- Helper to check if function type
isFunctionType :: Type -> Bool
isFunctionType (TyArr _ _) = True
isFunctionType _ = False

spec :: Spec
spec = do
  describe "Exercise 1: Type Inference Practice" $ do
    describe "1a. Composition" $ do
      it "type checks successfully" $ do
        inferSucceeds S.compose

      it "has function type with three arrows" $ do
        hasTypeStructure S.compose
          (\case
            TyArr _ (TyArr _ (TyArr _ _)) -> True
            _ -> False)
          "function with three arrows"

    describe "1b. S Combinator" $ do
      it "type checks successfully" $ do
        inferSucceeds S.sCombinator

      it "has function type with three arrows" $ do
        hasTypeStructure S.sCombinator
          (\case
            TyArr _ (TyArr _ (TyArr _ _)) -> True
            _ -> False)
          "function with three arrows"

    describe "1c. Twice" $ do
      it "type checks successfully" $ do
        inferSucceeds S.twice

      it "has function type with two arrows" $ do
        hasTypeStructure S.twice
          (\case
            TyArr _ (TyArr _ _) -> True
            _ -> False)
          "function with two arrows"

    describe "1d. Flip" $ do
      it "type checks successfully" $ do
        inferSucceeds S.flipFn

      it "has function type with three arrows" $ do
        hasTypeStructure S.flipFn
          (\case
            TyArr _ (TyArr _ (TyArr _ _)) -> True
            _ -> False)
          "function with three arrows"

  describe "Exercise 2: Polymorphic List Operations" $ do
    describe "2a. Map" $ do
      it "type checks successfully" $ do
        inferSucceeds S.mapList

      it "has function type" $ do
        hasTypeStructure S.mapList isFunctionType "function type"

      it "maps succ over list correctly" $ do
        let succFn = Lam "x" (TmSucc (Var "x"))
        let list = TmCons TmZero (TmCons (TmSucc TmZero) TmNil)
        let result = evalToNorm $ App (App S.mapList succFn) list
        -- Result should be [1, 2]
        case result of
          TmCons h1 (TmCons h2 TmNil) -> do
            natToInt h1 `shouldBe` Just 1
            natToInt h2 `shouldBe` Just 2
          _ -> expectationFailure "Expected cons list with 2 elements"

    describe "2b. Filter" $ do
      it "type checks successfully" $ do
        inferSucceeds S.filterList

      it "has function type" $ do
        hasTypeStructure S.filterList isFunctionType "function type"

    describe "2c. Length" $ do
      it "type checks successfully" $ do
        inferSucceeds S.lengthList

      it "computes length correctly" $ do
        let list = TmCons TmZero (TmCons TmZero (TmCons TmZero TmNil))
        let result = evalToNorm $ App S.lengthList list
        natToInt result `shouldBe` Just 3

      it "length of empty list is 0" $ do
        let result = evalToNorm $ App S.lengthList TmNil
        natToInt result `shouldBe` Just 0

    describe "2d. FoldL" $ do
      it "type checks successfully" $ do
        inferSucceeds S.foldlList

      it "has function type" $ do
        hasTypeStructure S.foldlList isFunctionType "function type"

    describe "2e. FoldR" $ do
      it "type checks successfully" $ do
        inferSucceeds S.foldrList

      it "has function type" $ do
        hasTypeStructure S.foldrList isFunctionType "function type"

  describe "Exercise 3: Let-Polymorphism vs Lambda" $ do
    describe "3a. Polymorphic Let" $ do
      it "type checks successfully (polymorphic let works)" $ do
        inferSucceeds S.letPolymorphic

      it "evaluates correctly" $ do
        let result = evalToNorm S.letPolymorphic
        case result of
          TmPair TmZero TmTrue -> return ()
          _ -> expectationFailure "Expected (0, true)"

    describe "3b. Monomorphic Lambda" $ do
      it "fails to type check (lambda is monomorphic)" $ do
        inferFails S.lambdaMonomorphic

  describe "Exercise 5: Polymorphic Trees" $ do
    describe "5a. Tree Map" $ do
      it "type checks successfully" $ do
        inferSucceeds S.treeMap

      it "has function type" $ do
        hasTypeStructure S.treeMap isFunctionType "function type"

      it "type checks with tree" $ do
        let succFn = Lam "x" (TmSucc (Var "x"))
        inferSucceeds $ App (App S.treeMap succFn) S.mkLeaf

    describe "5b. Tree Fold" $ do
      it "type checks successfully" $ do
        inferSucceeds S.treeFold

      it "has function type" $ do
        hasTypeStructure S.treeFold isFunctionType "function type"

    describe "5c. Tree Height" $ do
      it "type checks successfully" $ do
        inferSucceeds S.treeHeight

      it "height of leaf is 0" $ do
        let result = evalToNorm $ App S.treeHeight S.mkLeaf
        natToInt result `shouldBe` Just 0

      it "height of any tree is 0 (simplified)" $ do
        let tree = S.mkNode TmZero S.mkLeaf S.mkLeaf
        let result = evalToNorm $ App S.treeHeight tree
        natToInt result `shouldBe` Just 0

  describe "Example Programs" $ do
    it "Example 1: composition evaluates correctly" $ do
      let result = evalToNorm S.example1
      natToInt result `shouldBe` Just 5

    it "Example 2: twice evaluates correctly" $ do
      let result = evalToNorm S.example2
      natToInt result `shouldBe` Just 5

    it "Example 3: map over list type checks" $ do
      inferSucceeds S.example3

    it "Example 4: length of list evaluates to 3" $ do
      let result = evalToNorm S.example4
      natToInt result `shouldBe` Just 3

    it "Example 5: polymorphic let type checks" $ do
      inferSucceeds S.example5

    it "Example 5: polymorphic let evaluates correctly" $ do
      let result = evalToNorm S.example5
      case result of
        TmPair TmZero TmTrue -> return ()
        _ -> expectationFailure "Expected (0, true)"

    it "Example 6: simple tree type checks" $ do
      inferSucceeds S.example6

    it "Example 7: tree height type checks" $ do
      inferSucceeds S.example7

    it "Example 7: tree height of leaf is 0" $ do
      let result = evalToNorm S.example7
      natToInt result `shouldBe` Just 0
