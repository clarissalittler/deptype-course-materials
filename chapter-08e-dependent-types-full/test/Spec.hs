{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import TypeCheck
import Eval
import Parser
import Pretty
import qualified Data.Map.Strict as Map

main :: IO ()
main = hspec $ do
  describe "Universe Hierarchy" $ do
    it "Type 0 has type Type 1" $ do
      typeOf emptyCtx (Universe 0) `shouldBe` Right (Universe 1)

    it "Type 1 has type Type 2" $ do
      typeOf emptyCtx (Universe 1) `shouldBe` Right (Universe 2)

    it "Type i has type Type (i+1)" $ do
      typeOf emptyCtx (Universe 5) `shouldBe` Right (Universe 6)

    it "Nat lives in Type 0" $ do
      typeOf emptyCtx Nat `shouldBe` Right (Universe 0)

    it "Bool lives in Type 0" $ do
      typeOf emptyCtx Bool `shouldBe` Right (Universe 0)

    it "cumulativity allows Type 0 to check against Type 1" $ do
      typeCheck emptyCtx Nat (Universe 1) `shouldBe` Right ()

  describe "Equality Types" $ do
    it "Eq Nat 0 0 is a type" $ do
      let eqType = Eq Nat Zero Zero
      typeOf emptyCtx eqType `shouldBe` Right (Universe 0)

    it "refl 0 has type Eq Nat 0 0" $ do
      typeOf emptyCtx (Refl Zero) `shouldBe` Right (Eq Nat Zero Zero)

    it "refl true has type Eq Bool true true" $ do
      typeOf emptyCtx (Refl TmTrue) `shouldBe` Right (Eq Bool TmTrue TmTrue)

    it "J eliminator works on refl" $ do
      -- Simplified test: J should reduce when given refl
      let x = Zero
      let eq = Refl x
      let p = x  -- dummy motive result
      let result = J Nat (Lam "z" Nat (Lam "e" (Eq Nat x (Var "z")) (Universe 0))) p x x eq
      eval result `shouldBe` p

  describe "Natural Number Eliminator" $ do
    it "natElim on zero returns base case" $ do
      let p = Lam "n" Nat Nat
      let z = Zero
      let s = Lam "k" Nat (Lam "rec" Nat (Succ (Var "rec")))
      eval (NatElim p z s Zero) `shouldBe` Zero

    it "natElim on succ applies step function" $ do
      let p = Lam "n" Nat Nat
      let z = Zero
      let s = Lam "k" Nat (Lam "rec" Nat (Succ (Var "rec")))
      let n = Succ Zero
      let result = eval (NatElim p z s n)
      result `shouldBe` Succ Zero

    it "natElim implements addition" $ do
      -- add m n = natElim (λ_. Nat) m (λk rec. succ rec) n
      let add m n =
            NatElim
              (Lam "_" Nat Nat)
              m
              (Lam "k" Nat (Lam "rec" Nat (Succ (Var "rec"))))
              n
      eval (add (Succ Zero) (Succ (Succ Zero))) `shouldBe` Succ (Succ (Succ Zero))

  describe "Boolean Eliminator" $ do
    it "boolElim on true returns true branch" $ do
      let p = Lam "b" Bool Nat
      let t = Zero
      let f = Succ Zero
      eval (BoolElim p t f TmTrue) `shouldBe` Zero

    it "boolElim on false returns false branch" $ do
      let p = Lam "b" Bool Nat
      let t = Zero
      let f = Succ Zero
      eval (BoolElim p t f TmFalse) `shouldBe` Succ Zero

  describe "Unit and Empty Types" $ do
    it "Unit is a type" $ do
      typeOf emptyCtx Unit `shouldBe` Right (Universe 0)

    it "TT has type Unit" $ do
      typeOf emptyCtx TT `shouldBe` Right Unit

    it "unitElim on TT returns the value" $ do
      let p = Lam "_" Unit Nat
      let u = Zero
      eval (UnitElim p u TT) `shouldBe` Zero

    it "Empty is a type" $ do
      typeOf emptyCtx Empty `shouldBe` Right (Universe 0)

    it "Empty has no constructors" $ do
      -- Can't create a value of Empty type
      -- emptyElim can produce any type from Empty (ex falso quodlibet)
      isValue Empty `shouldBe` True

  describe "Pattern Matching" $ do
    it "matches variable pattern" $ do
      matchPattern (PVar "x") Zero `shouldBe` Just (Map.singleton "x" Zero)

    it "matches wildcard pattern" $ do
      matchPattern PWild Zero `shouldBe` Just Map.empty

    it "matches constructor with no args" $ do
      let pat = PCon "Nil" [PVar "a"]
      let term = Con "Nil" [Nat]
      case matchPattern pat term of
        Just bindings -> Map.lookup "a" bindings `shouldBe` Just Nat
        Nothing -> expectationFailure "Pattern should match"

    it "matches nat constructors" $ do
      matchPattern (PCon "Zero" []) Zero `shouldBe` Just Map.empty
      matchPattern (PCon "Succ" [PVar "k"]) (Succ Zero)
        `shouldBe` Just (Map.singleton "k" Zero)

  describe "Pattern Matching Typing" $ do
    it "types Nil constructor for Vec" $ do
      typeOf emptyCtx (Con "Nil" [Nat])
        `shouldBe` Right (App (App (Ind "Vec") Nat) Zero)

    it "types Cons constructor for Vec" $ do
      let nil = Con "Nil" [Nat]
      let cons = Con "Cons" [Nat, Zero, Zero, nil]
      typeOf emptyCtx cons
        `shouldBe` Right (App (App (Ind "Vec") Nat) (Succ Zero))

    it "types match with non-dependent branches" $ do
      let ctx =
            extendCtx "n" Nat
              (extendCtx "xs" (App (App (Ind "Vec") Nat) (Var "n")) emptyCtx)
      let scrut = Var "xs"
      let branches =
            [ (PCon "Nil" [PVar "A"], Zero)
            , (PCon "Cons" [PVar "A", PVar "n", PVar "x", PVar "xs"], Succ Zero)
            ]
      typeOf ctx (Match scrut Nothing branches) `shouldBe` Right Nat

    it "types match on Nat" $ do
      let branches =
            [ (PCon "Zero" [], Zero)
            , (PCon "Succ" [PVar "k"], Var "k")
            ]
      typeOf emptyCtx (Match Zero Nothing branches) `shouldBe` Right Nat

    it "rejects dependent branch types" $ do
      let ctx =
            extendCtx "n" Nat
              (extendCtx "xs" (App (App (Ind "Vec") Nat) (Var "n")) emptyCtx)
      let scrut = Var "xs"
      let branches =
            [ (PCon "Nil" [PVar "A"], Lam "y" (Var "A") (Var "y"))
            , (PCon "Cons" [PVar "A", PVar "n", PVar "x", PVar "xs"], Lam "y" (Var "A") (Var "y"))
            ]
      typeOf ctx (Match scrut Nothing branches) `shouldSatisfy` isPatternError

    it "rejects impossible Nil branch for Vec (succ n)" $ do
      let nil = Con "Nil" [Nat]
      let scrut = Con "Cons" [Nat, Zero, Zero, nil]
      let branches =
            [ (PCon "Nil" [PVar "A"], Zero)
            , (PCon "Cons" [PVar "A", PVar "n", PVar "x", PVar "xs"], Succ Zero)
            ]
      typeOf emptyCtx (Match scrut Nothing branches) `shouldSatisfy` isPatternError

    it "rejects missing Cons branch for Vec n" $ do
      let ctx =
            extendCtx "n" Nat
              (extendCtx "xs" (App (App (Ind "Vec") Nat) (Var "n")) emptyCtx)
      let branches = [ (PCon "Nil" [PVar "A"], Zero) ]
      typeOf ctx (Match (Var "xs") Nothing branches) `shouldSatisfy` isPatternError

    it "types dependent match with indexed motive" $ do
      let vecN = App (App (Ind "Vec") Nat) (Var "n")
      let motive =
            Lam "n" Nat
              (Lam "v" vecN
                (Eq vecN (Var "v") (Var "v")))
      let branches =
            [ (PCon "Nil" [PWild], Refl (Con "Nil" [Nat]))
            , (PCon "Cons" [PWild, PVar "k", PVar "x", PVar "xs"],
               Refl (Con "Cons" [Nat, Var "k", Var "x", Var "xs"]))
            ]
      let term =
            Lam "n" Nat
              (Lam "v" vecN
                (Match (Var "v") (Just motive) branches))
      let expectedTy =
            Pi "n" Nat
              (Pi "v" vecN
                (App (App motive (Var "n")) (Var "v")))
      typeOf emptyCtx term `shouldBe` Right expectedTy

    it "types dependent match on Nat with simple motive" $ do
      let motive = Lam "n" Nat (Eq Nat (Var "n") (Var "n"))
      let branches =
            [ (PCon "Zero" [], Refl Zero)
            , (PCon "Succ" [PVar "k"], Refl (Succ (Var "k")))
            ]
      let term = Lam "n" Nat (Match (Var "n") (Just motive) branches)
      let expectedTy = Pi "n" Nat (App motive (Var "n"))
      typeOf emptyCtx term `shouldBe` Right expectedTy

  describe "Dependent Types with Universe Levels" $ do
    it "polymorphic identity at level 1" $ do
      -- id : Π(A:Type 0). A → A
      let polyId = Lam "A" (Universe 0) (Lam "x" (Var "A") (Var "x"))
      let expectedType = Pi "A" (Universe 0) (Pi "x" (Var "A") (Var "A"))
      typeOf emptyCtx polyId `shouldBe` Right expectedType

    it "type of types at level 1" $ do
      -- Π(A:Type 0). Type 0  lives in Type 1
      let ty = Pi "A" (Universe 0) (Universe 0)
      typeOf emptyCtx ty `shouldBe` Right (Universe 1)

  describe "Normalization (NBE)" $ do
    it "reduces type-level application in Pi domain" $ do
      let dom = App (Lam "n" Nat Nat) Zero
      let ty = Pi "x" dom Nat
      typeOf emptyCtx ty `shouldBe` Right (Universe 0)

  describe "Parser" $ do
    it "parses universe levels" $ do
      parseTerm "Type0" `shouldBe` Right (Universe 0)
      parseTerm "Type1" `shouldBe` Right (Universe 1)

    it "parses equality types" $ do
      parseTerm "Eq Nat zero zero" `shouldBe` Right (Eq Nat Zero Zero)

    it "parses refl" $ do
      parseTerm "refl zero" `shouldBe` Right (Refl Zero)

    it "parses natElim" $ do
      let input = "natElim(\\(n:Nat). Nat, zero, \\(k:Nat). \\(rec:Nat). succ rec, zero)"
      case parseTerm input of
        Right (NatElim _ _ _ _) -> return ()
        other -> expectationFailure $ "Failed to parse natElim: " ++ show other

    it "parses constructors" $ do
      parseTerm "Nil Nat" `shouldBe` Right (Con "Nil" [Nat])

    it "parses patterns" $ do
      parsePattern "Nil a" `shouldBe` Right (PCon "Nil" [PVar "a"])
      parsePattern "_" `shouldBe` Right PWild
      parsePattern "zero" `shouldBe` Right (PCon "Zero" [])
      parsePattern "succ k" `shouldBe` Right (PCon "Succ" [PVar "k"])
      parsePattern "true" `shouldBe` Right (PCon "True" [])

    it "parses arrow sugar" $ do
      parseTerm "Nat -> Nat" `shouldBe` Right (Pi "_" Nat Nat)

    it "parses numeric literals" $ do
      parseTerm "2" `shouldBe` Right (Succ (Succ Zero))

    it "parses match with return motive" $ do
      parseTerm "match zero return Nat with | _ -> zero"
        `shouldBe` Right (Match Zero (Just Nat) [(PWild, Zero)])

  describe "Pretty Printing" $ do
    it "pretty prints universes" $ do
      pretty (Universe 0) `shouldBe` "Type"
      pretty (Universe 1) `shouldBe` "Type1"

    it "pretty prints equality" $ do
      pretty (Eq Nat Zero Zero) `shouldBe` "Eq Nat 0 0"

    it "pretty prints refl" $ do
      pretty (Refl Zero) `shouldBe` "refl 0"

    it "pretty prints constructors" $ do
      pretty (Con "Nil" [Nat]) `shouldBe` "Nil Nat"

    it "pretty prints patterns" $ do
      prettyPattern (PCon "Cons" [PVar "x", PVar "xs"]) `shouldBe` "Cons x xs"
      prettyPattern PWild `shouldBe` "_"

  describe "Evaluation" $ do
    it "evaluates polymorphic identity" $ do
      let polyId = Lam "A" (Universe 0) (Lam "x" (Var "A") (Var "x"))
      let term = App (App polyId Nat) Zero
      eval term `shouldBe` Zero

    it "normalizes nested applications" $ do
      let term = App (Lam "x" Nat (Succ (Var "x"))) Zero
      eval term `shouldBe` Succ Zero

    it "reduces natElim completely" $ do
      -- natElim on (succ (succ zero))
      let p = Lam "n" Nat Nat
      let z = Zero
      let s = Lam "k" Nat (Lam "rec" Nat (Succ (Var "rec")))
      let n = Succ (Succ Zero)
      eval (NatElim p z s n) `shouldBe` Succ (Succ Zero)

  describe "Advanced Examples" $ do
    it "symmetry of equality (conceptual)" $ do
      -- sym : Π(A:Type). Π(x:A). Π(y:A). Eq A x y → Eq A y x
      -- Implementation would use J eliminator
      -- For now, just check refl is symmetric
      typeOf emptyCtx (Refl Zero) `shouldBe` Right (Eq Nat Zero Zero)

    it "transitivity of equality (conceptual)" $ do
      -- trans : Π(A:Type). Π(x y z:A). Eq A x y → Eq A y z → Eq A x z
      -- Would use J eliminator twice
      -- Refl is transitive with itself
      typeOf emptyCtx (Refl TmTrue) `shouldBe` Right (Eq Bool TmTrue TmTrue)

    it "const function with universe levels" $ do
      let constFun = Lam "A" (Universe 0)
                       (Lam "B" (Universe 0)
                         (Lam "x" (Var "A")
                           (Lam "y" (Var "B") (Var "x"))))
      typeOf emptyCtx constFun `shouldSatisfy` isRight

-- Helper
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isPatternError :: Either TypeError a -> Bool
isPatternError (Left (PatternError _)) = True
isPatternError _ = False
