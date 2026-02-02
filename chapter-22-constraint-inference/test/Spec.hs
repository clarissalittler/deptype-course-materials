{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import Constraint
import Solve
import Infer
import Eval
import Parser
import Pretty
import Data.Text (Text)

main :: IO ()
main = hspec $ do
  describe "Constraint Generation" $ do
    it "generates no constraints for identity" $ do
      term <- parseTermOrFail "\\x. x"
      case generateConstraints term of
        Right ([], _) -> return ()
        Right (cs, _) -> expectationFailure $ "Expected no constraints, got: " ++ show cs
        Left err -> expectationFailure $ show err

    it "generates Nat constraint for succ" $ do
      term <- parseTermOrFail "\\x. succ x"
      case generateConstraints term of
        Right (cs, _) -> cs `shouldSatisfy` (not . null)
        Left err -> expectationFailure $ show err

    it "generates function constraint for application" $ do
      term <- parseTermOrFail "\\f. \\x. f x"
      case generateConstraints term of
        Right (cs, _) -> cs `shouldSatisfy` (not . null)
        Left err -> expectationFailure $ show err

    it "generates constraints for if expression" $ do
      term <- parseTermOrFail "\\x. \\y. if x then y else 0"
      case generateConstraints term of
        Right (cs, _) -> cs `shouldSatisfy` (\l -> length l >= 2)
        Left err -> expectationFailure $ show err

  describe "Constraint Solving" $ do
    it "solves trivial constraints" $ do
      let c = [Equal TyBool TyBool]
      solve c `shouldBe` Right emptySubst

    it "solves simple substitution" $ do
      let c = [Equal (TyVar "t0") TyNat]
      case solve c of
        Right subst -> applySubst subst (TyVar "t0") `shouldBe` TyNat
        Left err -> expectationFailure $ show err

    it "solves function constraints" $ do
      let c = [Equal (TyVar "t0") (TyArr TyBool TyNat)]
      case solve c of
        Right subst -> applySubst subst (TyVar "t0") `shouldBe` TyArr TyBool TyNat
        Left err -> expectationFailure $ show err

    it "fails on occurs check" $ do
      let c = [Equal (TyVar "t0") (TyArr (TyVar "t0") TyNat)]
      case solve c of
        Left (OccursCheck "t0" _) -> return ()
        Left err -> expectationFailure $ "Wrong error: " ++ show err
        Right _ -> expectationFailure "Should fail occurs check"

    it "fails on inconsistent types" $ do
      let c = [Equal TyBool TyNat]
      case solve c of
        Left (UnificationFail TyBool TyNat) -> return ()
        Left err -> expectationFailure $ "Wrong error: " ++ show err
        Right _ -> expectationFailure "Should fail to unify Bool and Nat"

  describe "Unification" $ do
    it "unifies identical types" $ do
      unify TyBool TyBool `shouldBe` Right emptySubst

    it "unifies type variable with type" $ do
      case unify (TyVar "t0") TyNat of
        Right subst -> applySubst subst (TyVar "t0") `shouldBe` TyNat
        Left err -> expectationFailure $ show err

    it "unifies function types" $ do
      case unify (TyArr (TyVar "t0") (TyVar "t1")) (TyArr TyBool TyNat) of
        Right subst -> do
          applySubst subst (TyVar "t0") `shouldBe` TyBool
          applySubst subst (TyVar "t1") `shouldBe` TyNat
        Left err -> expectationFailure $ show err

    it "unifies product types" $ do
      case unify (TyProd (TyVar "t0") (TyVar "t1")) (TyProd TyBool TyNat) of
        Right subst -> do
          applySubst subst (TyVar "t0") `shouldBe` TyBool
          applySubst subst (TyVar "t1") `shouldBe` TyNat
        Left err -> expectationFailure $ show err

    it "fails occurs check" $ do
      case unify (TyVar "t0") (TyArr (TyVar "t0") TyNat) of
        Left (OccursCheck "t0" _) -> return ()
        Left err -> expectationFailure $ "Wrong error: " ++ show err
        Right _ -> expectationFailure "Should fail occurs check"

  describe "Type Inference - Basic" $ do
    it "infers identity function" $ do
      term <- parseTermOrFail "\\x. x"
      case infer term of
        Right ty -> ty `shouldSatisfy` \t -> case t of
          TyArr (TyVar a) (TyVar b) -> a == b
          _ -> False
        Left err -> expectationFailure $ show err

    it "infers const function" $ do
      term <- parseTermOrFail "\\x. \\y. x"
      case infer term of
        Right ty -> do
          prettyType ty `shouldSatisfy` \s -> "->" `elem` words s
        Left err -> expectationFailure $ show err

    it "infers boolean functions" $ do
      term <- parseTermOrFail "\\x. if x then false else true"
      infer term `shouldBe` Right (TyArr TyBool TyBool)

    it "infers function application" $ do
      term <- parseTermOrFail "(\\x. x) true"
      infer term `shouldBe` Right TyBool

  describe "Type Inference - Let Polymorphism" $ do
    it "allows polymorphic let bindings" $ do
      term <- parseTermOrFail "let id = \\x. x in (id true, id 0)"
      infer term `shouldBe` Right (TyProd TyBool TyNat)

    it "generalizes let-bound variables" $ do
      term <- parseTermOrFail "let const = \\x. \\y. x in const"
      case infer term of
        Right ty -> ty `shouldSatisfy` \t -> case t of
          TyArr _ (TyArr _ _) -> True
          _ -> False
        Left err -> expectationFailure $ show err

    it "does not generalize lambda-bound variables" $ do
      term <- parseTermOrFail "\\f. (f true, f 0)"
      case infer term of
        Left (SolveErr (UnificationFail TyBool TyNat)) -> return ()
        Left err -> expectationFailure $ "Wrong error: " ++ show err
        Right ty -> expectationFailure $ "Should fail but got: " ++ prettyType ty

  describe "Type Inference - Pairs" $ do
    it "infers pair types" $ do
      term <- parseTermOrFail "(true, 0)"
      infer term `shouldBe` Right (TyProd TyBool TyNat)

    it "infers fst/snd correctly" $ do
      fstTerm <- parseTermOrFail "\\p. fst p"
      sndTerm <- parseTermOrFail "\\p. snd p"
      case (infer fstTerm, infer sndTerm) of
        (Right ty1, Right ty2) -> do
          ty1 `shouldSatisfy` \t -> case t of
            TyArr (TyProd _ _) _ -> True
            _ -> False
          ty2 `shouldSatisfy` \t -> case t of
            TyArr (TyProd _ _) _ -> True
            _ -> False
        (Left err, _) -> expectationFailure $ show err
        (_, Left err) -> expectationFailure $ show err

  describe "Type Inference - Lists" $ do
    it "infers polymorphic empty list" $ do
      term <- parseTermOrFail "[]"
      case infer term of
        Right (TyList (TyVar _)) -> return ()
        Right ty -> expectationFailure $ "Expected polymorphic list, got: " ++ prettyType ty
        Left err -> expectationFailure $ show err

    it "infers homogeneous lists" $ do
      nilTerm <- parseTermOrFail "[]"
      case infer nilTerm of
        Right (TyList _) -> return ()
        Right ty -> expectationFailure $ "Expected list type, got: " ++ prettyType ty
        Left err -> expectationFailure $ show err

  describe "Type Inference - Complex Examples" $ do
    it "compose function" $ do
      term <- parseTermOrFail "\\f. \\g. \\x. f (g x)"
      case infer term of
        Right ty -> ty `shouldSatisfy` \t -> case t of
          TyArr _ (TyArr _ (TyArr _ _)) -> True
          _ -> False
        Left err -> expectationFailure $ show err

    it "map-like function" $ do
      term <- parseTermOrFail "\\f. \\x. f x"
      case infer term of
        Right (TyArr (TyArr t1 t2) (TyArr t3 t4)) ->
          (t1 == t3 && t2 == t4) `shouldBe` True
        Right ty -> expectationFailure $ "Wrong type: " ++ prettyType ty
        Left err -> expectationFailure $ show err

  describe "Full Inference Process" $ do
    it "shows constraints for simple term" $ do
      term <- parseTermOrFail "\\x. succ x"
      case inferType term of
        Right (cs, _, ty) -> do
          cs `shouldSatisfy` (not . null)
          ty `shouldBe` TyArr TyNat TyNat
        Left err -> expectationFailure $ show err

    it "shows constraints for complex term" $ do
      term <- parseTermOrFail "\\f. \\g. \\x. f (g x)"
      case inferType term of
        Right (cs, _subst, ty) -> do
          cs `shouldSatisfy` (not . null)
          ty `shouldSatisfy` \t -> case t of
            TyArr _ (TyArr _ (TyArr _ _)) -> True
            _ -> False
        Left err -> expectationFailure $ show err

  describe "Evaluation" $ do
    it "evaluates identity application" $ do
      term <- parseTermOrFail "(\\x. x) true"
      eval term `shouldBe` TmTrue

    it "evaluates let bindings" $ do
      term <- parseTermOrFail "let x = true in x"
      eval term `shouldBe` TmTrue

    it "evaluates polymorphic let" $ do
      term <- parseTermOrFail "let id = \\x. x in id true"
      eval term `shouldBe` TmTrue

  describe "Parser" $ do
    it "parses variables" $ do
      parseTerm "x" `shouldBe` Right (Var "x")

    it "parses lambda" $ do
      parseTerm "\\x. x" `shouldBe` Right (Lam "x" (Var "x"))

    it "parses application" $ do
      parseTerm "f x" `shouldBe` Right (App (Var "f") (Var "x"))

    it "parses let" $ do
      parseTerm "let x = true in x" `shouldBe`
        Right (Let "x" TmTrue (Var "x"))

  describe "Pretty Printing" $ do
    it "pretty prints types" $ do
      prettyType (TyArr TyBool TyNat) `shouldBe` "Bool -> Nat"
      prettyType (TyProd TyBool TyNat) `shouldBe` "Bool * Nat"

    it "pretty prints constraints" $ do
      let c = Equal (TyVar "t0") TyBool
      prettyConstraint c `shouldSatisfy` \s -> "t0" `elem` words s

    it "pretty prints terms" $ do
      pretty (Lam "x" (Var "x")) `shouldBe` "λx. x"
      pretty (App (Var "f") (Var "x")) `shouldBe` "f x"

-- | Parse a term or fail the test with a readable error.
parseTermOrFail :: Text -> IO Term
parseTermOrFail input =
  case parseTerm input of
    Left err -> expectationFailure err >> fail "parseTerm failed"
    Right t -> return t
