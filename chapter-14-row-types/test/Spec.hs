{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map as Map

import Syntax
import TypeCheck
import Eval
import Parser
import Pretty

main :: IO ()
main = hspec $ do
  describe "Syntax" $ do
    describe "freeVars" $ do
      it "finds vars in record" $
        freeVars (TmRecord (Map.fromList [("x", Var "a"), ("y", Var "b")]))
          `shouldBe` Set.fromList ["a", "b"]

      it "finds vars in variant" $
        freeVars (TmVariant "left" (Var "x") (TyVariant RowEmpty))
          `shouldBe` Set.singleton "x"

      it "binds vars in case" $
        freeVars (TmCase (Var "v") [("l", "x", Var "x")])
          `shouldBe` Set.singleton "v"

      it "finds vars in extension" $
        freeVars (TmExtend (Var "r") "x" (Var "y"))
          `shouldBe` Set.fromList ["r", "y"]

    describe "freeRowVars" $ do
      it "finds row var in record type" $
        freeRowVars (TyRecord (RowExtend "x" TyNat (RowVar "ρ")))
          `shouldBe` Set.singleton "ρ"

      it "finds row var in variant type" $
        freeRowVars (TyVariant (RowExtend "l" TyBool (RowVar "ρ")))
          `shouldBe` Set.singleton "ρ"

      it "binds row var in forall" $
        freeRowVars (TyForallRow "ρ" (TyRecord (RowVar "ρ")))
          `shouldBe` Set.empty

      it "finds free but not bound" $
        freeRowVars (TyForallRow "ρ" (TyFun (TyRecord (RowVar "ρ")) (TyRecord (RowVar "σ"))))
          `shouldBe` Set.singleton "σ"

  describe "Row Operations" $ do
    describe "rowHas" $ do
      it "finds label in row" $
        rowHas "x" (RowExtend "x" TyNat RowEmpty) `shouldBe` True

      it "finds label in nested row" $
        rowHas "y" (RowExtend "x" TyNat (RowExtend "y" TyBool RowEmpty)) `shouldBe` True

      it "returns false for missing label" $
        rowHas "z" (RowExtend "x" TyNat RowEmpty) `shouldBe` False

      it "returns false for empty row" $
        rowHas "x" RowEmpty `shouldBe` False

    describe "rowGet" $ do
      it "retrieves type from row" $
        rowGet "x" (RowExtend "x" TyNat RowEmpty) `shouldBe` Just TyNat

      it "retrieves from nested row" $
        rowGet "y" (RowExtend "x" TyNat (RowExtend "y" TyBool RowEmpty))
          `shouldBe` Just TyBool

      it "returns Nothing for missing" $
        rowGet "z" (RowExtend "x" TyNat RowEmpty) `shouldBe` Nothing

  describe "TypeCheck" $ do
    describe "Records" $ do
      it "types empty record" $
        typeCheck (TmRecord Map.empty) `shouldBe` Right (TyRecord RowEmpty)

      it "types record with one field" $
        typeCheck (TmRecord (Map.fromList [("x", TmZero)]))
          `shouldSatisfy` isRight

      it "types record with multiple fields" $
        typeCheck (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue), ("z", TmUnit)]))
          `shouldSatisfy` isRight

      it "types projection" $
        typeCheck (TmProj (TmRecord (Map.fromList [("x", TmZero)])) "x")
          `shouldBe` Right TyNat

      it "types projection from multi-field record" $
        typeCheck (TmProj (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)])) "y")
          `shouldBe` Right TyBool

      it "rejects projection of missing field" $
        typeCheck (TmProj (TmRecord (Map.fromList [("x", TmZero)])) "y")
          `shouldBe` Left (MissingLabel "y")

      it "types record extension" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero)])
        typeCheck (TmExtend rec "y" TmTrue) `shouldSatisfy` isRight

      it "types record restriction" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)])
        typeCheck (TmRestrict rec "x") `shouldSatisfy` isRight

      it "rejects restricting missing field" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero)])
        typeCheck (TmRestrict rec "y") `shouldSatisfy` isLeft

    describe "Variants" $ do
      it "types variant injection" $ do
        let ty = TyVariant (RowExtend "left" TyNat (RowExtend "right" TyBool RowEmpty))
        let term = TmVariant "left" TmZero ty
        typeCheck term `shouldBe` Right ty

      it "rejects variant with wrong payload type" $ do
        let ty = TyVariant (RowExtend "left" TyNat RowEmpty)
        let term = TmVariant "left" TmTrue ty
        typeCheck term `shouldSatisfy` isLeft

      it "rejects variant with unknown label" $ do
        let ty = TyVariant (RowExtend "left" TyNat RowEmpty)
        let term = TmVariant "right" TmZero ty
        typeCheck term `shouldSatisfy` isLeft

      it "types case expression" $ do
        let ty = TyVariant (RowExtend "left" TyNat (RowExtend "right" TyBool RowEmpty))
        let v = TmVariant "left" TmZero ty
        let term = TmCase v [("left", "x", Var "x"), ("right", "y", TmZero)]
        typeCheck term `shouldBe` Right TyNat

      it "rejects case with mismatched branch types" $ do
        let ty = TyVariant (RowExtend "left" TyNat (RowExtend "right" TyBool RowEmpty))
        let v = TmVariant "left" TmZero ty
        let term = TmCase v [("left", "x", Var "x"), ("right", "y", TmTrue)]
        typeCheck term `shouldSatisfy` isLeft

    describe "Let bindings" $ do
      it "types let binding" $
        typeCheck (TmLet "x" TmZero (TmSucc (Var "x")))
          `shouldBe` Right TyNat

      it "types let with record" $ do
        let rec = TmRecord (Map.fromList [("a", TmZero)])
        typeCheck (TmLet "r" rec (TmProj (Var "r") "a"))
          `shouldBe` Right TyNat

  describe "Evaluation" $ do
    describe "Records" $ do
      it "evaluates record projection" $
        eval (TmProj (TmRecord (Map.fromList [("x", TmZero)])) "x")
          `shouldBe` TmZero

      it "evaluates projection from multi-field record" $
        eval (TmProj (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)])) "y")
          `shouldBe` TmTrue

      it "evaluates record extension" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero)])
        eval (TmProj (TmExtend rec "y" TmTrue) "y")
          `shouldBe` TmTrue

      it "preserves old field after extension" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero)])
        eval (TmProj (TmExtend rec "y" TmTrue) "x")
          `shouldBe` TmZero

      it "evaluates record restriction" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)])
        let restricted = eval (TmRestrict rec "x")
        -- After restriction, projecting x should fail (it's removed)
        -- But projecting y should still work
        eval (TmProj restricted "y") `shouldBe` TmTrue

      it "evaluates nested projections" $ do
        let inner = TmRecord (Map.fromList [("a", TmZero)])
        let outer = TmRecord (Map.fromList [("inner", inner)])
        eval (TmProj (TmProj outer "inner") "a")
          `shouldBe` TmZero

    describe "Variants" $ do
      it "evaluates case on left" $ do
        let ty = TyVariant (RowExtend "left" TyNat (RowExtend "right" TyBool RowEmpty))
        let v = TmVariant "left" (TmSucc TmZero) ty
        let term = TmCase v [("left", "x", Var "x"), ("right", "y", TmZero)]
        eval term `shouldBe` TmSucc TmZero

      it "evaluates case on right" $ do
        let ty = TyVariant (RowExtend "left" TyNat (RowExtend "right" TyBool RowEmpty))
        let v = TmVariant "right" TmTrue ty
        let term = TmCase v [("left", "x", TmZero), ("right", "y", TmSucc TmZero)]
        eval term `shouldBe` TmSucc TmZero

      it "substitutes bound variable in case" $ do
        let ty = TyVariant (RowExtend "val" TyNat RowEmpty)
        let v = TmVariant "val" (TmSucc (TmSucc TmZero)) ty
        let term = TmCase v [("val", "x", TmSucc (Var "x"))]
        eval term `shouldBe` TmSucc (TmSucc (TmSucc TmZero))

    describe "Let bindings" $ do
      it "evaluates let binding" $
        eval (TmLet "x" TmZero (TmSucc (Var "x")))
          `shouldBe` TmSucc TmZero

      it "evaluates nested let" $
        eval (TmLet "x" TmZero (TmLet "y" (TmSucc (Var "x")) (Var "y")))
          `shouldBe` TmSucc TmZero

  describe "Parser" $ do
    describe "Records" $ do
      it "parses empty record" $
        parseTerm "{}" `shouldBe` Right (TmRecord Map.empty)

      it "parses record with field" $
        parseTerm "{x = 0}" `shouldBe` Right (TmRecord (Map.fromList [("x", TmZero)]))

      it "parses record with multiple fields" $
        parseTerm "{x = 0, y = true}"
          `shouldBe` Right (TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)]))

      it "parses projection" $
        parseTerm "r.x" `shouldBe` Right (TmProj (Var "r") "x")

      it "parses projection on expression" $
        parseTerm "(r.x).y" `shouldSatisfy` isRight

      it "parses record type" $
        parseType "{x: Nat}" `shouldBe` Right (TyRecord (RowExtend "x" TyNat RowEmpty))

      it "parses multi-field record type" $
        parseType "{x: Nat, y: Bool}"
          `shouldSatisfy` isRight

    describe "Variants" $ do
      it "parses variant type" $
        parseType "<left: Nat, right: Bool>"
          `shouldSatisfy` isRight

      it "parses variant injection" $
        -- Syntax is: <label = term> : type (single label case)
        parseTerm "<left = 0> : <left: Nat>"
          `shouldSatisfy` isRight

    describe "Let bindings" $ do
      it "parses let" $
        parseTerm "let x = 0 in x"
          `shouldBe` Right (TmLet "x" TmZero (Var "x"))

      it "parses nested let" $
        parseTerm "let x = 0 in let y = x in y"
          `shouldSatisfy` isRight

  describe "Pretty" $ do
    describe "Records" $ do
      it "prints empty record" $
        prettyTerm (TmRecord Map.empty) `shouldBe` "{}"

      it "prints record with field" $
        prettyTerm (TmRecord (Map.fromList [("x", TmZero)]))
          `shouldBe` "{x = 0}"

      it "prints record type" $
        prettyType (TyRecord (RowExtend "x" TyNat RowEmpty))
          `shouldBe` "{x: Nat}"

      it "prints projection" $
        prettyTerm (TmProj (Var "r") "x")
          `shouldBe` "r.x"

    describe "Variants" $ do
      it "prints variant type" $
        prettyType (TyVariant (RowExtend "left" TyNat RowEmpty))
          `shouldBe` "<left: Nat>"

      it "prints variant injection" $
        prettyTerm (TmVariant "left" TmZero (TyVariant (RowExtend "left" TyNat RowEmpty)))
          `shouldBe` "<left = 0> : <left: Nat>"

  describe "Integration" $ do
    describe "Record operations" $ do
      it "extend then project new field" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero)])
        let extended = TmExtend rec "y" TmTrue
        eval (TmProj extended "y") `shouldBe` TmTrue

      it "extend then project old field" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero)])
        let extended = TmExtend rec "y" TmTrue
        eval (TmProj extended "x") `shouldBe` TmZero

      it "restrict then verify field removed" $ do
        let rec = TmRecord (Map.fromList [("x", TmZero), ("y", TmTrue)])
        let restricted = TmRestrict rec "x"
        typeCheck (TmProj restricted "y") `shouldBe` Right TyBool

    describe "Variant pattern matching" $ do
      it "handles option-like type" $ do
        let optTy = TyVariant (RowExtend "some" TyNat (RowExtend "none" TyUnit RowEmpty))
        let someVal = TmVariant "some" (TmSucc TmZero) optTy
        let unwrap = TmCase someVal
              [("some", "x", Var "x"), ("none", "_", TmZero)]
        eval unwrap `shouldBe` TmSucc TmZero

      it "handles either-like type" $ do
        let eitherTy = TyVariant (RowExtend "left" TyNat (RowExtend "right" TyBool RowEmpty))
        let leftVal = TmVariant "left" TmZero eitherTy
        let rightVal = TmVariant "right" TmTrue eitherTy
        let handler = [("left", "n", TmIsZero (Var "n")), ("right", "b", Var "b")]
        eval (TmCase leftVal handler) `shouldBe` TmTrue
        eval (TmCase rightVal handler) `shouldBe` TmTrue

    describe "Records with functions" $ do
      it "record of functions" $ do
        let inc = Lam "x" TyNat (TmSucc (Var "x"))
        let rec = TmRecord (Map.fromList [("inc", inc)])
        let applied = App (TmProj rec "inc") TmZero
        eval applied `shouldBe` TmSucc TmZero

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False
