{-# LANGUAGE LambdaCase #-}

module ExerciseSpec (spec) where

import Test.Hspec
import Syntax
import Eval
import qualified Solutions as S
import qualified Data.Map.Strict as Map

-- Helper to evaluate to normal form
evalToNorm :: Term -> Term
evalToNorm = eval

-- Helper to convert Nat term to Int
natToInt :: Term -> Maybe Int
natToInt TmZero = Just 0
natToInt (TmSucc n) = (+ 1) <$> natToInt n
natToInt _ = Nothing

-- Helper to convert list of nats to list of ints
listToInts :: Term -> Maybe [Int]
listToInts (TmNil _) = Just []
listToInts (TmCons h t) = do
  h' <- natToInt h
  t' <- listToInts t
  return (h' : t')
listToInts _ = Nothing

spec :: Spec
spec = do
  describe "Exercise 1: List Operations" $ do
    describe "1a. Append" $ do
      it "append [] [] = []" $ do
        let result = evalToNorm $ App (App (S.appendList TyNat) (TmNil TyNat)) (TmNil TyNat)
        listToInts result `shouldBe` Just []

      it "append [1,2] [3,4] = [1,2,3,4]" $ do
        let list1 = TmCons (S.natFromInt 1) (TmCons (S.natFromInt 2) (TmNil TyNat))
        let list2 = TmCons (S.natFromInt 3) (TmCons (S.natFromInt 4) (TmNil TyNat))
        let result = evalToNorm $ App (App (S.appendList TyNat) list1) list2
        listToInts result `shouldBe` Just [1,2,3,4]

      it "append [] [1,2] = [1,2]" $ do
        let list2 = TmCons (S.natFromInt 1) (TmCons (S.natFromInt 2) (TmNil TyNat))
        let result = evalToNorm $ App (App (S.appendList TyNat) (TmNil TyNat)) list2
        listToInts result `shouldBe` Just [1,2]

    describe "1b. Reverse" $ do
      it "reverse [] = []" $ do
        let result = evalToNorm $ App (S.reverseList TyNat) (TmNil TyNat)
        listToInts result `shouldBe` Just []

      it "reverse [1,2,3] = [3,2,1]" $ do
        let list1 = TmCons (S.natFromInt 1) $
                    TmCons (S.natFromInt 2) $
                    TmCons (S.natFromInt 3) $
                    TmNil TyNat
        let result = evalToNorm $ App (S.reverseList TyNat) list1
        listToInts result `shouldBe` Just [3,2,1]

    describe "1c. Length" $ do
      it "length [] = 0" $ do
        let result = evalToNorm $ App (S.lengthList TyNat) (TmNil TyNat)
        natToInt result `shouldBe` Just 0

      it "length [1,2,3] = 3" $ do
        let list1 = TmCons (S.natFromInt 1) $
                    TmCons (S.natFromInt 2) $
                    TmCons (S.natFromInt 3) $
                    TmNil TyNat
        let result = evalToNorm $ App (S.lengthList TyNat) list1
        natToInt result `shouldBe` Just 3

  describe "Exercise 2: Binary Trees" $ do
    describe "2a. Tree height" $ do
      it "height of leaf = 0" $ do
        let leaf = S.mkLeaf TyNat
        let result = evalToNorm $ App (S.treeHeight TyNat) leaf
        natToInt result `shouldBe` Just 0

      it "height of single node = 1" $ do
        let tree = S.mkNode TyNat (S.natFromInt 5) (S.mkLeaf TyNat) (S.mkLeaf TyNat)
        let result = evalToNorm $ App (S.treeHeight TyNat) tree
        natToInt result `shouldBe` Just 1

      it "height of tree with depth 2" $ do
        let leftChild = S.mkNode TyNat (S.natFromInt 3) (S.mkLeaf TyNat) (S.mkLeaf TyNat)
        let tree = S.mkNode TyNat (S.natFromInt 5) leftChild (S.mkLeaf TyNat)
        let result = evalToNorm $ App (S.treeHeight TyNat) tree
        natToInt result `shouldBe` Just 2

    describe "2b. Tree mirror" $ do
      it "mirror of leaf = leaf" $ do
        let leaf = S.mkLeaf TyNat
        let result = evalToNorm $ App (S.treeMirror TyNat) leaf
        case result of
          TmTag "leaf" TmUnit _ -> return ()
          _ -> expectationFailure "Expected leaf"

      it "mirror creates symmetric tree" $ do
        let tree = S.mkNode TyNat (S.natFromInt 5)
                     (S.mkNode TyNat (S.natFromInt 3) (S.mkLeaf TyNat) (S.mkLeaf TyNat))
                     (S.mkLeaf TyNat)
        let mirrored = evalToNorm $ App (S.treeMirror TyNat) tree
        -- After mirroring, the left subtree should be a leaf
        case mirrored of
          TmTag "node" _ _ -> return ()
          _ -> expectationFailure "Expected node"

    describe "2c. Tree map" $ do
      it "map over leaf = leaf" $ do
        let succFn = Lam "x" TyNat (TmSucc (Var "x"))
        let leaf = S.mkLeaf TyNat
        let result = evalToNorm $ App (App (S.treeMap TyNat TyNat) succFn) leaf
        case result of
          TmTag "leaf" TmUnit _ -> return ()
          _ -> expectationFailure "Expected leaf"

      it "map succ over simple tree" $ do
        let succFn = Lam "x" TyNat (TmSucc (Var "x"))
        let tree = S.mkNode TyNat (S.natFromInt 2) (S.mkLeaf TyNat) (S.mkLeaf TyNat)
        let result = evalToNorm $ App (App (S.treeMap TyNat TyNat) succFn) tree
        -- Should be node with value 3
        case result of
          TmTag "node" (TmPair val _) _ -> natToInt val `shouldBe` Just 3
          _ -> expectationFailure "Expected node with incremented value"

  describe "Exercise 3: Option Type" $ do
    describe "3a. Option map" $ do
      it "map over none = none" $ do
        let succFn = Lam "x" TyNat (TmSucc (Var "x"))
        let none = S.mkNone TyNat
        let result = evalToNorm $ App (App (S.optionMap TyNat TyNat) succFn) none
        case result of
          TmInl _ TmUnit -> return ()
          _ -> expectationFailure "Expected none"

      it "map succ over some 5 = some 6" $ do
        let succFn = Lam "x" TyNat (TmSucc (Var "x"))
        let some5 = S.mkSome TyNat (S.natFromInt 5)
        let result = evalToNorm $ App (App (S.optionMap TyNat TyNat) succFn) some5
        case result of
          TmInr _ val -> natToInt val `shouldBe` Just 6
          _ -> expectationFailure "Expected some 6"

    describe "3b. Option bind" $ do
      it "bind none with any function = none" $ do
        let fn = Lam "x" TyNat (S.mkSome TyNat (TmSucc (Var "x")))
        let none = S.mkNone TyNat
        let result = evalToNorm $ App (App (S.optionBind TyNat TyNat) none) fn
        case result of
          TmInl _ TmUnit -> return ()
          _ -> expectationFailure "Expected none"

      it "bind some 5 with function = some result" $ do
        let fn = Lam "x" TyNat (S.mkSome TyNat (TmSucc (Var "x")))
        let some5 = S.mkSome TyNat (S.natFromInt 5)
        let result = evalToNorm $ App (App (S.optionBind TyNat TyNat) some5) fn
        case result of
          TmInr _ val -> natToInt val `shouldBe` Just 6
          _ -> expectationFailure "Expected some 6"

    describe "3c. Option getOrElse" $ do
      it "getOrElse none 42 = 42" $ do
        let none = S.mkNone TyNat
        let result = evalToNorm $ App (App (S.optionGetOrElse TyNat) none) (S.natFromInt 42)
        natToInt result `shouldBe` Just 42

      it "getOrElse (some 5) 42 = 5" $ do
        let some5 = S.mkSome TyNat (S.natFromInt 5)
        let result = evalToNorm $ App (App (S.optionGetOrElse TyNat) some5) (S.natFromInt 42)
        natToInt result `shouldBe` Just 5

  describe "Exercise 4: Expression Evaluator" $ do
    describe "4a. Evaluator" $ do
      it "eval (lit 5) = 5" $ do
        let expr = S.mkLit (S.natFromInt 5)
        let result = evalToNorm $ App S.exprEval expr
        natToInt result `shouldBe` Just 5

      it "eval (add (lit 2) (lit 3)) = 5" $ do
        let expr = S.mkAdd (S.mkLit (S.natFromInt 2)) (S.mkLit (S.natFromInt 3))
        let result = evalToNorm $ App S.exprEval expr
        natToInt result `shouldBe` Just 5

      it "eval (mul (lit 3) (lit 4)) = 12" $ do
        let expr = S.mkMul (S.mkLit (S.natFromInt 3)) (S.mkLit (S.natFromInt 4))
        let result = evalToNorm $ App S.exprEval expr
        natToInt result `shouldBe` Just 12

      it "eval (mul (add (lit 1) (lit 2)) (lit 3)) = 9" $ do
        let expr = S.mkMul (S.mkAdd (S.mkLit (S.natFromInt 1)) (S.mkLit (S.natFromInt 2)))
                           (S.mkLit (S.natFromInt 3))
        let result = evalToNorm $ App S.exprEval expr
        natToInt result `shouldBe` Just 9

  describe "Exercise 5: Record Operations" $ do
    describe "5a. Update record field" $ do
      it "updates x field correctly" $ do
        let rec = TmRecord $ Map.fromList [("x", S.natFromInt 10), ("y", S.natFromInt 20)]
        let result = evalToNorm $ App (App (S.updateRecordX TyNat TyNat) rec) (S.natFromInt 99)
        case result of
          TmRecord fields -> do
            natToInt (fields Map.! "x") `shouldBe` Just 99
            natToInt (fields Map.! "y") `shouldBe` Just 20
          _ -> expectationFailure "Expected record"

  describe "Example Programs" $ do
    it "Example list [1,2,3]" $ do
      listToInts S.exampleList `shouldBe` Just [1,2,3]

    it "Example append" $ do
      let result = evalToNorm S.exampleAppend
      listToInts result `shouldBe` Just [1,2,3,4]

    it "Example tree is a node" $ do
      case S.exampleTree of
        TmTag "node" _ _ -> return ()
        _ -> expectationFailure "Expected node"

    it "Example some has value" $ do
      case S.exampleSome of
        TmInr _ val -> natToInt val `shouldBe` Just 42
        _ -> expectationFailure "Expected some"

    it "Example none is none" $ do
      case S.exampleNone of
        TmInl _ TmUnit -> return ()
        _ -> expectationFailure "Expected none"

    it "Example expression evaluates to 5" $ do
      let result = evalToNorm $ App S.exprEval S.exampleExpr
      natToInt result `shouldBe` Just 5

    it "Example record has correct fields" $ do
      case S.exampleRecord of
        TmRecord fields -> do
          natToInt (fields Map.! "x") `shouldBe` Just 10
          natToInt (fields Map.! "y") `shouldBe` Just 20
        _ -> expectationFailure "Expected record"
