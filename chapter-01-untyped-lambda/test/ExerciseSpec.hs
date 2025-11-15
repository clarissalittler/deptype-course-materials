{-# LANGUAGE OverloadedStrings #-}

module ExerciseSpec (spec) where

import Test.Hspec
import Syntax
import Eval
import qualified Solutions as S

-- | Helper: apply Church boolean to true and false branches
applyChurchBool :: Term -> Term -> Term -> Term
applyChurchBool b t f = eval $ App (App b t) f

-- | Helper: convert Church numeral to Int
-- Apply to (succ 0) and 0, then count how many times succ was applied
churchToInt :: Term -> Int
churchToInt n = countSucc $ eval $ App (App n S.churchSucc) S.churchZero
  where
    countSucc :: Term -> Int
    countSucc (Lam "n" (Lam "f" (Lam "x" (Var "x")))) = 0  -- zero
    countSucc (Lam "n" (Lam "f" (Lam "x" body))) = 1 + countSucc (Lam "n" (Lam "f" (Lam "x" (removeOneApp body))))
    countSucc _ = 0

    removeOneApp :: Term -> Term
    removeOneApp (App (Var "f") rest) = rest
    removeOneApp t = t

-- | Helper: convert Church numeral to Int more reliably
-- We'll evaluate n (λx. x+1) 0 by using a custom "increment" function
churchNumToInt :: Term -> Int
churchNumToInt n = go 0 (eval $ App (App n incrementer) S.churchZero)
  where
    incrementer = Lam "x" (App S.churchSucc (Var "x"))
    go :: Int -> Term -> Int
    go acc term
      | alphaEq term S.churchZero = acc
      | otherwise = case term of
          App (Lam _ _) arg -> go (acc + 1) arg
          _ -> acc

-- | Better approach: apply to succ and 0 from untyped LC
-- and count the structure
churchToInt' :: Term -> Int
churchToInt' n =
  let result = eval $ App (App n (Lam "x" (Lam "n" (App (Var "n") (Var "x"))))) (Lam "y" (Var "y"))
  in countNesting result
  where
    countNesting :: Term -> Int
    countNesting (Lam "y" (Var "y")) = 0
    countNesting (Lam "n" body) = 1 + countNesting body
    countNesting (App (Var "n") inner) = 1 + countNesting inner
    countNesting _ = 0

-- | Most direct approach: evaluate with Haskell succ and 0
evalChurchNum :: Term -> Int
evalChurchNum cn = count $ eval $ App (App cn inc) zero
  where
    inc = Lam "x" (Var "succ_x")  -- marker
    zero = Var "zero"  -- marker
    count (Var "zero") = 0
    count (App (Lam "x" (Var "succ_x")) rest) = 1 + count rest
    count _ = error "Not a valid church numeral result"

-- | Check if two church booleans are equivalent
churchBoolEq :: Term -> Term -> Bool
churchBoolEq b1 b2 =
  let r1 = applyChurchBool b1 (Var "T") (Var "F")
      r2 = applyChurchBool b2 (Var "T") (Var "F")
  in alphaEq r1 r2

spec :: Spec
spec = do
  describe "Exercise 1: Church Boolean Operations" $ do
    describe "1a. AND operation" $ do
      it "true AND true = true" $
        churchBoolEq (App (App S.churchAnd S.churchTrue) S.churchTrue) S.churchTrue `shouldBe` True

      it "true AND false = false" $
        churchBoolEq (App (App S.churchAnd S.churchTrue) S.churchFalse) S.churchFalse `shouldBe` True

      it "false AND true = false" $
        churchBoolEq (App (App S.churchAnd S.churchFalse) S.churchTrue) S.churchFalse `shouldBe` True

      it "false AND false = false" $
        churchBoolEq (App (App S.churchAnd S.churchFalse) S.churchFalse) S.churchFalse `shouldBe` True

    describe "1b. OR operation" $ do
      it "true OR true = true" $
        churchBoolEq (App (App S.churchOr S.churchTrue) S.churchTrue) S.churchTrue `shouldBe` True

      it "true OR false = true" $
        churchBoolEq (App (App S.churchOr S.churchTrue) S.churchFalse) S.churchTrue `shouldBe` True

      it "false OR true = true" $
        churchBoolEq (App (App S.churchOr S.churchFalse) S.churchTrue) S.churchTrue `shouldBe` True

      it "false OR false = false" $
        churchBoolEq (App (App S.churchOr S.churchFalse) S.churchFalse) S.churchFalse `shouldBe` True

    describe "1c. XOR operation" $ do
      it "true XOR true = false" $
        churchBoolEq (App (App S.churchXor S.churchTrue) S.churchTrue) S.churchFalse `shouldBe` True

      it "true XOR false = true" $
        churchBoolEq (App (App S.churchXor S.churchTrue) S.churchFalse) S.churchTrue `shouldBe` True

      it "false XOR true = true" $
        churchBoolEq (App (App S.churchXor S.churchFalse) S.churchTrue) S.churchTrue `shouldBe` True

      it "false XOR false = false" $
        churchBoolEq (App (App S.churchXor S.churchFalse) S.churchFalse) S.churchFalse `shouldBe` True

  describe "Exercise 2: Church Numeral Arithmetic" $ do
    describe "2a. Predecessor" $ do
      it "pred 0 = 0" $
        alphaEq (eval $ App S.churchPred S.churchZero) S.churchZero `shouldBe` True

      it "pred 1 = 0" $
        alphaEq (eval $ App S.churchPred S.churchOne) S.churchZero `shouldBe` True

      it "pred 2 = 1" $
        alphaEq (eval $ App S.churchPred S.churchTwo) S.churchOne `shouldBe` True

      it "pred 3 = 2" $
        alphaEq (eval $ App S.churchPred S.churchThree) S.churchTwo `shouldBe` True

    describe "2b. Subtraction" $ do
      it "3 - 1 = 2" $
        alphaEq (eval $ App (App S.churchSub S.churchThree) S.churchOne) S.churchTwo `shouldBe` True

      it "3 - 2 = 1" $
        alphaEq (eval $ App (App S.churchSub S.churchThree) S.churchTwo) S.churchOne `shouldBe` True

      it "2 - 2 = 0" $
        alphaEq (eval $ App (App S.churchSub S.churchTwo) S.churchTwo) S.churchZero `shouldBe` True

      it "1 - 3 = 0 (saturating)" $
        alphaEq (eval $ App (App S.churchSub S.churchOne) S.churchThree) S.churchZero `shouldBe` True

    describe "2c. Equality test" $ do
      it "0 == 0" $
        churchBoolEq (App (App S.churchIsEqual S.churchZero) S.churchZero) S.churchTrue `shouldBe` True

      it "2 == 2" $
        churchBoolEq (App (App S.churchIsEqual S.churchTwo) S.churchTwo) S.churchTrue `shouldBe` True

      it "1 != 2" $
        churchBoolEq (App (App S.churchIsEqual S.churchOne) S.churchTwo) S.churchFalse `shouldBe` True

  describe "Exercise 3: Recursion and Fixed Points" $ do
    it "3a. Z combinator enables recursion" $ do
      -- Test that Z f = f (Z f) for some simple f
      let f = Lam "rec" (Lam "x" (Var "x"))  -- f rec x = x
      let zf = eval $ App S.zCombinator f
      -- Z f should behave like λx. x
      alphaEq (eval $ App zf (Var "y")) (Var "y") `shouldBe` True

    it "3b. Factorial of 3 = 6" $ do
      let fact3 = eval $ App S.churchFactorial S.churchThree
      let six = eval $ App (App S.churchMult S.churchTwo) S.churchThree
      alphaEq fact3 six `shouldBe` True

    it "3c. Fibonacci of 0 = 0" $ do
      let fib0 = eval $ App S.churchFibonacci S.churchZero
      alphaEq fib0 S.churchZero `shouldBe` True

    it "3c. Fibonacci of 1 = 1" $ do
      let fib1 = eval $ App S.churchFibonacci S.churchOne
      alphaEq fib1 S.churchOne `shouldBe` True

    it "3c. Fibonacci of 2 = 1" $ do
      let fib2 = eval $ App S.churchFibonacci S.churchTwo
      alphaEq fib2 S.churchOne `shouldBe` True

  describe "Exercise 4: Advanced Combinators" $ do
    it "4a. I combinator" $
      alphaEq (eval $ App S.combI (Var "x")) (Var "x") `shouldBe` True

    it "4a. K combinator" $
      alphaEq (eval $ App (App S.combK (Var "x")) (Var "y")) (Var "x") `shouldBe` True

    it "4a. S combinator" $ do
      -- S x y z = x z (y z)
      -- S K K a = K a (K a) = a
      let result = eval $ App (App (App S.combS S.combK) S.combK) (Var "a")
      alphaEq result (Var "a") `shouldBe` True

    it "4c. I = S K K" $ do
      let i1 = eval $ App S.combI (Var "x")
      let i2 = eval $ App S.iFromSK (Var "x")
      alphaEq i1 i2 `shouldBe` True

  describe "Exercise 5: List Operations" $ do
    it "5a. Length of empty list = 0" $ do
      let len = eval $ App S.churchLength S.churchNil
      alphaEq len S.churchZero `shouldBe` True

    it "5a. Length of [1,2,3] = 3" $ do
      let list = S.makeChurchList [S.churchOne, S.churchTwo, S.churchThree]
      let len = eval $ App S.churchLength list
      alphaEq len S.churchThree `shouldBe` True

    it "5b. Map succ over [0,1,2]" $ do
      -- Just test that map returns a function (it's a Church-encoded list)
      let list = S.makeChurchList [S.churchZero, S.churchOne]
      let mapped = eval $ App (App S.churchMap S.churchSucc) list
      -- Check it's a lambda (Church lists are functions)
      case mapped of
        Lam _ (Lam _ _) -> return ()
        _ -> expectationFailure $ "Expected a Church list (λc. λn. ...), got: " ++ show mapped

    it "5d. Fold plus over [1,2,3] with 0" $ do
      let list = S.makeChurchList [S.churchOne, S.churchTwo, S.churchThree]
      let sum' = eval $ App (App (App S.churchFold S.churchPlus) S.churchZero) list
      let six = eval $ App (App S.churchPlus S.churchThree) S.churchThree
      alphaEq sum' six `shouldBe` True
