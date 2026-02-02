{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import Parser
import Pretty
import qualified Data.Map.Strict as Map
import qualified ExerciseSpec

main :: IO ()
main = hspec $ do
  describe "Chapter 3 Exercises" ExerciseSpec.spec
  describe "Type System - Products" $ do
    it "types pairs correctly" $ do
      let pair = TmPair TmTrue TmZero
      typeCheck pair `shouldBe` Right (TyProd TyBool TyNat)

    it "types projections correctly" $ do
      let pair = TmPair TmTrue TmFalse
      typeCheck (TmFst pair) `shouldBe` Right TyBool
      typeCheck (TmSnd pair) `shouldBe` Right TyBool

  describe "Type System - Sums" $ do
    it "types left injection correctly" $ do
      let term = TmInl TyNat TmTrue
      typeCheck term `shouldBe` Right (TySum TyBool TyNat)

    it "types right injection correctly" $ do
      let term = TmInr TyBool TmZero
      typeCheck term `shouldBe` Right (TySum TyBool TyNat)

    it "types case expression correctly" $ do
      let term = TmCase (TmInl TyNat TmTrue) "x" (Var "x") "y" TmFalse
      typeCheck term `shouldBe` Right TyBool

  describe "Type System - Records" $ do
    it "types records correctly" $ do
      let record = TmRecord $ Map.fromList [("x", TmTrue), ("y", TmZero)]
      typeCheck record `shouldBe`
        Right (TyRecord $ Map.fromList [("x", TyBool), ("y", TyNat)])

    it "types record projection correctly" $ do
      let record = TmRecord $ Map.fromList [("x", TmTrue), ("y", TmZero)]
      typeCheck (TmProj record "x") `shouldBe` Right TyBool
      typeCheck (TmProj record "y") `shouldBe` Right TyNat

  describe "Type System - Lists" $ do
    it "types nil correctly" $ do
      typeCheck (TmNil TyNat) `shouldBe` Right (TyList TyNat)

    it "types cons correctly" $ do
      let list = TmCons TmZero (TmNil TyNat)
      typeCheck list `shouldBe` Right (TyList TyNat)

    it "rejects heterogeneous lists" $ do
      let badList = TmCons TmTrue (TmNil TyNat)
      case typeCheck badList of
        Left (TypeMismatch _ _) -> return ()
        _ -> expectationFailure "Should reject mismatched list element type"

  describe "Evaluation - Products" $ do
    it "evaluates fst correctly" $ do
      eval (TmFst (TmPair TmTrue TmFalse)) `shouldBe` TmTrue

    it "evaluates snd correctly" $ do
      eval (TmSnd (TmPair TmTrue TmFalse)) `shouldBe` TmFalse

    it "evaluates projections on nested pairs" $ do
      let nested = TmPair (TmPair TmTrue TmFalse) TmZero
      eval (TmFst (TmFst nested)) `shouldBe` TmTrue

  describe "Evaluation - Sums" $ do
    it "evaluates case on left injection" $ do
      let term = TmCase (TmInl TyNat TmTrue) "x" (Var "x") "y" TmFalse
      eval term `shouldBe` TmTrue

    it "evaluates case on right injection" $ do
      let term = TmCase (TmInr TyBool TmZero) "x" TmTrue "y" (Var "y")
      eval term `shouldBe` TmZero

  describe "Evaluation - Records" $ do
    it "evaluates record projection" $ do
      let record = TmRecord $ Map.fromList [("x", TmTrue), ("y", TmZero)]
      eval (TmProj record "x") `shouldBe` TmTrue
      eval (TmProj record "y") `shouldBe` TmZero

  describe "Evaluation - Lists" $ do
    it "evaluates isnil on empty list" $ do
      eval (TmIsNil (TmNil TyNat)) `shouldBe` TmTrue

    it "evaluates isnil on non-empty list" $ do
      let list = TmCons TmZero (TmNil TyNat)
      eval (TmIsNil list) `shouldBe` TmFalse

    it "evaluates head correctly" $ do
      let list = TmCons TmZero (TmNil TyNat)
      eval (TmHead list) `shouldBe` TmZero

    it "evaluates tail correctly" $ do
      let list = TmCons TmZero (TmCons (TmSucc TmZero) (TmNil TyNat))
      eval (TmTail list) `shouldBe` TmCons (TmSucc TmZero) (TmNil TyNat)

  describe "Pattern Matching" $ do
    it "matches variable pattern" $ do
      let term = TmMatch TmTrue [(PatVar "x", Var "x")]
      eval term `shouldBe` TmTrue

    it "matches wildcard pattern" $ do
      let term = TmMatch TmTrue [(PatWild, TmFalse)]
      eval term `shouldBe` TmFalse

    it "matches boolean patterns" $ do
      let term = TmMatch TmTrue [(PatFalse, TmZero), (PatTrue, TmSucc TmZero)]
      eval term `shouldBe` TmSucc TmZero

    it "matches pair patterns" $ do
      let pair = TmPair TmTrue TmZero
      let term = TmMatch pair [(PatPair (PatVar "x") (PatVar "y"), Var "x")]
      eval term `shouldBe` TmTrue

    it "matches with multiple patterns (first match wins)" $ do
      let term = TmMatch TmZero
            [(PatSucc PatWild, TmTrue)
            ,(PatZero, TmFalse)
            ]
      eval term `shouldBe` TmFalse

  describe "Parser" $ do
    it "parses pairs" $ do
      parseTerm "(true, 0)" `shouldBe` Right (TmPair TmTrue TmZero)

    it "parses records" $ do
      parseTerm "{x=true, y=0}" `shouldBe`
        Right (TmRecord $ Map.fromList [("x", TmTrue), ("y", TmZero)])

    it "parses list cons chains" $ do
      parseTerm "0::succ 0::[]:Nat" `shouldBe`
        Right (TmCons TmZero (TmCons (TmSucc TmZero) (TmNil TyNat)))

    it "parses match with cons patterns" $ do
      parseTerm "match 0::[]:Nat with h::t => h | [] => 0" `shouldBe`
        Right (TmMatch (TmCons TmZero (TmNil TyNat))
          [ (PatCons (PatVar "h") (PatVar "t"), Var "h")
          , (PatNil, TmZero)
          ])

    it "parses case with patterns" $ do
      parseTerm "case 0::[]:Nat of h::t => h | [] => 0" `shouldBe`
        Right (TmMatch (TmCons TmZero (TmNil TyNat))
          [ (PatCons (PatVar "h") (PatVar "t"), Var "h")
          , (PatNil, TmZero)
          ])

    it "parses variant patterns" $ do
      let variantTy = TyVariant (Map.fromList [("some", TyNat), ("none", TyUnit)])
      parseTerm "case <some=0> as <some:Nat, none:Unit> of <some=x> => x | <none=_> => 0"
        `shouldBe`
          Right (TmMatch (TmTag "some" TmZero variantTy)
            [ (PatVariant "some" (PatVar "x"), Var "x")
            , (PatVariant "none" PatWild, TmZero)
            ])

    it "parses succ and sum patterns" $ do
      parseTerm "match inl[Nat] true with inl x => x | inr y => false" `shouldBe`
        Right (TmMatch (TmInl TyNat TmTrue)
          [ (PatInl (PatVar "x"), Var "x")
          , (PatInr (PatVar "y"), TmFalse)
          ])

      parseTerm "match succ 0 with succ x => x | 0 => 0" `shouldBe`
        Right (TmMatch (TmSucc TmZero)
          [ (PatSucc (PatVar "x"), Var "x")
          , (PatZero, TmZero)
          ])

    it "rejects duplicate record labels" $ do
      case parseTerm "{x=true, x=false}" of
        Left _ -> return ()
        Right _ -> expectationFailure "Expected duplicate record labels to fail parsing"

    it "rejects duplicate record types" $ do
      case parseType "{x:Bool, x:Nat}" of
        Left _ -> return ()
        Right _ -> expectationFailure "Expected duplicate record type labels to fail parsing"

    it "rejects duplicate variant types" $ do
      case parseType "<a:Nat, a:Bool>" of
        Left _ -> return ()
        Right _ -> expectationFailure "Expected duplicate variant type labels to fail parsing"

    it "parses product types" $ do
      parseType "Bool * Nat" `shouldBe` Right (TyProd TyBool TyNat)

    it "parses list types" $ do
      parseType "List Nat" `shouldBe` Right (TyList TyNat)

  describe "Pretty Printing" $ do
    it "pretty prints pairs" $ do
      pretty (TmPair TmTrue TmZero) `shouldBe` "(true, 0)"

    it "pretty prints product types" $ do
      prettyType (TyProd TyBool TyNat) `shouldBe` "Bool * Nat"

    it "pretty prints list types" $ do
      prettyType (TyList TyNat) `shouldBe` "List Nat"

  describe "Complex Examples" $ do
    it "evaluates option type example" $ do
      -- Option Nat = Unit + Nat
      -- Some 5 = inr[Unit] 5
      -- None = inl[Nat] ()
      let some5 = TmInr TyUnit (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))))
      let none = TmInl TyNat TmUnit

      -- case some5 of inl _ => 0 | inr n => n
      let extract = TmCase some5 "u" TmZero "n" (Var "n")
      eval extract `shouldBe` TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero))))

      -- case none of inl _ => 0 | inr n => n
      let extractNone = TmCase none "u" TmZero "n" (Var "n")
      eval extractNone `shouldBe` TmZero

    it "works with higher-order functions on products" $ do
      -- swap : Bool * Nat -> Nat * Bool
      -- swap = λp:Bool*Nat. (snd p, fst p)
      let swapTy = TyArr (TyProd TyBool TyNat) (TyProd TyNat TyBool)
      let swap = Lam "p" (TyProd TyBool TyNat)
                   (TmPair (TmSnd (Var "p")) (TmFst (Var "p")))

      typeCheck swap `shouldBe` Right swapTy

      let result = eval (App swap (TmPair TmTrue TmZero))
      result `shouldBe` TmPair TmZero TmTrue
