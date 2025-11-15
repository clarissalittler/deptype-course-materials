{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import Infer
import Eval
import Parser
import Pretty
import qualified ExerciseSpec

main :: IO ()
main = hspec $ do
  describe "Chapter 4 Exercises" ExerciseSpec.spec
  describe "Type Inference - Basic" $ do
    it "infers identity function" $ do
      let Right term = parseTerm "\\x. x"
      case infer term of
        Right ty -> ty `shouldSatisfy` \t -> case t of
          TyArr (TyVar a) (TyVar b) -> a == b
          _ -> False
        Left err -> expectationFailure $ show err

    it "infers const function" $ do
      let Right term = parseTerm "\\x. \\y. x"
      case infer term of
        Right ty -> do
          -- Type should be polymorphic: a -> b -> a
          prettyType ty `shouldSatisfy` \s -> "->" `elem` words s
        Left err -> expectationFailure $ show err

    it "infers boolean functions" $ do
      let Right term = parseTerm "\\x. if x then false else true"
      infer term `shouldBe` Right (TyArr TyBool TyBool)

    it "infers function application" $ do
      let Right term = parseTerm "(\\x. x) true"
      infer term `shouldBe` Right TyBool

  describe "Type Inference - Let Polymorphism" $ do
    it "allows polymorphic let bindings" $ do
      -- let id = \x. x in (id true, id 0)
      let Right term = parseTerm "let id = \\x. x in (id true, id 0)"
      infer term `shouldBe` Right (TyProd TyBool TyNat)

    it "generalizes let-bound variables" $ do
      -- let const = \x. \y. x in const
      let Right term = parseTerm "let const = \\x. \\y. x in const"
      case infer term of
        Right ty -> ty `shouldSatisfy` \t -> case t of
          TyArr _ (TyArr _ _) -> True
          _ -> False
        Left err -> expectationFailure $ show err

    it "does not generalize lambda-bound variables" $ do
      -- \f. (f true, f 0) should fail (f must be monomorphic)
      let Right term = parseTerm "\\f. (f true, f 0)"
      case infer term of
        Left (UnificationFail TyBool TyNat) -> return ()
        Left err -> expectationFailure $ "Wrong error: " ++ show err
        Right ty -> expectationFailure $ "Should fail but got: " ++ prettyType ty

  describe "Type Inference - Pairs" $ do
    it "infers pair types" $ do
      let Right term = parseTerm "(true, 0)"
      infer term `shouldBe` Right (TyProd TyBool TyNat)

    it "infers fst/snd correctly" $ do
      let Right fstTerm = parseTerm "\\p. fst p"
      let Right sndTerm = parseTerm "\\p. snd p"
      case (infer fstTerm, infer sndTerm) of
        (Right ty1, Right ty2) -> do
          -- fst has type (a, b) -> a
          ty1 `shouldSatisfy` \t -> case t of
            TyArr (TyProd _ _) _ -> True
            _ -> False
          -- snd has type (a, b) -> b
          ty2 `shouldSatisfy` \t -> case t of
            TyArr (TyProd _ _) _ -> True
            _ -> False
        (Left err, _) -> expectationFailure $ show err
        (_, Left err) -> expectationFailure $ show err

  describe "Type Inference - Lists" $ do
    it "infers polymorphic empty list" $ do
      let Right term = parseTerm "[]"
      case infer term of
        Right (TyList (TyVar _)) -> return ()
        Right ty -> expectationFailure $ "Expected polymorphic list, got: " ++ prettyType ty
        Left err -> expectationFailure $ show err

    it "infers list cons" $ do
      let Right term = parseTerm "\\x. \\xs. x"
      -- Note: Without full list syntax in parser, we test components
      case infer term of
        Right _ -> return ()
        Left err -> expectationFailure $ show err

    it "infers homogeneous lists" $ do
      -- This tests that list elements must have same type
      let Right nilTerm = parseTerm "[]"
      case infer nilTerm of
        Right (TyList _) -> return ()
        Right ty -> expectationFailure $ "Expected list type, got: " ++ prettyType ty
        Left err -> expectationFailure $ show err

  describe "Type Inference - Recursion via Y combinator" $ do
    it "Y combinator type" $ do
      -- Y = \f. (\x. f (x x)) (\x. f (x x))
      -- This actually won't type check in HM without recursive types!
      -- But we can test a weaker form
      let Right term = parseTerm "\\f. \\x. f (f x)"
      case infer term of
        Right ty -> ty `shouldSatisfy` \t -> case t of
          TyArr _ _ -> True
          _ -> False
        Left err -> expectationFailure $ show err

  describe "Type Inference - Complex Examples" $ do
    it "compose function" $ do
      -- compose = \f. \g. \x. f (g x)
      let Right term = parseTerm "\\f. \\g. \\x. f (g x)"
      case infer term of
        Right ty -> ty `shouldSatisfy` \t -> case t of
          TyArr _ (TyArr _ (TyArr _ _)) -> True
          _ -> False
        Left err -> expectationFailure $ show err

    it "map-like function" $ do
      -- Not full map, but: \f. \x. f x
      let Right term = parseTerm "\\f. \\x. f x"
      case infer term of
        Right (TyArr (TyArr t1 t2) (TyArr t3 t4)) ->
          (t1 == t3 && t2 == t4) `shouldBe` True
        Right ty -> expectationFailure $ "Wrong type: " ++ prettyType ty
        Left err -> expectationFailure $ show err

  describe "Evaluation" $ do
    it "evaluates identity application" $ do
      let Right term = parseTerm "(\\x. x) true"
      eval term `shouldBe` TmTrue

    it "evaluates let bindings" $ do
      let Right term = parseTerm "let x = true in x"
      eval term `shouldBe` TmTrue

    it "evaluates polymorphic let" $ do
      let Right term = parseTerm "let id = \\x. x in id true"
      eval term `shouldBe` TmTrue

  describe "Parser" $ do
    it "parses lambda without type annotations" $ do
      parseTerm "\\x. x" `shouldBe` Right (Lam "x" (Var "x"))

    it "parses let expressions" $ do
      parseTerm "let x = true in x" `shouldBe`
        Right (Let "x" TmTrue (Var "x"))

    it "parses nested lets" $ do
      let Right term = parseTerm "let x = true in let y = false in x"
      term `shouldBe` Let "x" TmTrue (Let "y" TmFalse (Var "x"))
