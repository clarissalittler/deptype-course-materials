{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec
import Syntax
import Eval
import Parser
import Pretty
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified ExerciseSpec

main :: IO ()
main = hspec $ do
  ExerciseSpec.spec
  describe "Syntax" $ do
    it "computes free variables correctly" $ do
      freeVars (Var "x") `shouldBe` Set.fromList ["x"]
      freeVars (Lam "x" (Var "x")) `shouldBe` Set.empty
      freeVars (Lam "x" (Var "y")) `shouldBe` Set.fromList ["y"]
      freeVars (App (Var "x") (Var "y")) `shouldBe` Set.fromList ["x", "y"]

    it "performs capture-avoiding substitution" $ do
      -- [x ↦ y]x = y
      substVar "x" (Var "y") (Var "x") `shouldBe` Var "y"

      -- [x ↦ y]z = z
      substVar "x" (Var "y") (Var "z") `shouldBe` Var "z"

      -- [x ↦ y](λx. x) = λx. x (x is bound)
      substVar "x" (Var "y") (Lam "x" (Var "x")) `shouldBe` Lam "x" (Var "x")

      -- [x ↦ y](λz. x) = λz. y
      substVar "x" (Var "y") (Lam "z" (Var "x")) `shouldBe` Lam "z" (Var "y")

    it "avoids variable capture in substitution" $ do
      -- [x ↦ y](λy. x) should rename y to avoid capturing the free y in the substitution
      let result = substVar "x" (Var "y") (Lam "y" (Var "x"))
      case result of
        Lam y' body -> do
          y' `shouldNotBe` "y"  -- y should be renamed
          body `shouldBe` Var "y"  -- but the substitution should still happen
        _ -> expectationFailure "Expected a lambda"

  describe "Parser" $ do
    it "parses variables" $ do
      parseTerm "x" `shouldBe` Right (Var "x")
      parseTerm "foo" `shouldBe` Right (Var "foo")

    it "parses lambda abstractions" $ do
      parseTerm "\\x. x" `shouldBe` Right (Lam "x" (Var "x"))
      parseTerm "λx. x" `shouldBe` Right (Lam "x" (Var "x"))
      parseTerm "\\x -> x" `shouldBe` Right (Lam "x" (Var "x"))

    it "parses multiple lambda arguments" $ do
      parseTerm "\\x y. x" `shouldBe` Right (Lam "x" (Lam "y" (Var "x")))
      parseTerm "λx y z. z" `shouldBe` Right (Lam "x" (Lam "y" (Lam "z" (Var "z"))))

    it "parses applications" $ do
      parseTerm "f x" `shouldBe` Right (App (Var "f") (Var "x"))
      parseTerm "f x y" `shouldBe` Right (App (App (Var "f") (Var "x")) (Var "y"))

    it "parses complex terms" $ do
      parseTerm "(\\x. x) y" `shouldBe`
        Right (App (Lam "x" (Var "x")) (Var "y"))

    it "respects parentheses" $ do
      parseTerm "f (g x)" `shouldBe`
        Right (App (Var "f") (App (Var "g") (Var "x")))

  describe "Evaluation" $ do
    it "identifies values correctly" $ do
      isValue (Lam "x" (Var "x")) `shouldBe` True
      isValue (Var "x") `shouldBe` False
      isValue (App (Var "f") (Var "x")) `shouldBe` False

    it "performs beta reduction" $ do
      -- (λx. x) y → y
      let identity = Lam "x" (Var "x")
      let term = App identity (Var "y")
      eval term `shouldBe` Var "y"

    it "evaluates the identity function" $ do
      case parseTerm "(\\x. x) y" of
        Right term -> eval term `shouldBe` Var "y"
        Left err -> expectationFailure err

    it "evaluates constant function (K combinator)" $ do
      -- (λx. λy. x) a b → a
      case parseTerm "(\\x y. x) a b" of
        Right term -> eval term `shouldBe` Var "a"
        Left err -> expectationFailure err

    it "evaluates S combinator" $ do
      -- (λx. λy. λz. x z (y z)) f g x → f x (g x)
      case parseTerm "(\\x y z. x z (y z)) f g a" of
        Right term ->
          eval term `shouldBe` App (App (Var "f") (Var "a")) (App (Var "g") (Var "a"))
        Left err -> expectationFailure err

    it "evaluates nested applications" $ do
      case parseTerm "(\\x. x x) (\\y. y)" of
        Right term -> eval term `shouldBe` Lam "y" (Var "y")
        Left err -> expectationFailure err

  describe "Church encodings" $ do
    let church0 = "\\f x. x"
    let church1 = "\\f x. f x"
    let churchSucc = "\\n f x. f (n f x)"

    it "computes successor of Church numerals" $ do
      case parseTerm $ T.pack $ "(" ++ churchSucc ++ ") (" ++ church0 ++ ")" of
        Right term -> do
          let result = eval term
          case parseTerm church1 of
            Right expected -> result `shouldBe` expected
            Left err -> expectationFailure err
        Left err -> expectationFailure err

    it "defines Church booleans" $ do
      let true = "\\t f. t"
      let false = "\\t f. f"
      let ifThenElse = "\\p t f. p t f"

      case parseTerm $ T.pack $ "(" ++ ifThenElse ++ ") (" ++ true ++ ") a b" of
        Right term -> eval term `shouldBe` Var "a"
        Left err -> expectationFailure err

      case parseTerm $ T.pack $ "(" ++ ifThenElse ++ ") (" ++ false ++ ") a b" of
        Right term -> eval term `shouldBe` Var "b"
        Left err -> expectationFailure err

  describe "Pretty printing" $ do
    it "pretty prints variables" $ do
      pretty (Var "x") `shouldBe` "x"

    it "pretty prints lambdas" $ do
      pretty (Lam "x" (Var "x")) `shouldBe` "λx. x"

    it "pretty prints applications with correct associativity" $ do
      pretty (App (App (Var "f") (Var "x")) (Var "y")) `shouldBe` "f x y"

    it "adds parentheses where needed" $ do
      pretty (App (Var "f") (Lam "x" (Var "x"))) `shouldBe` "f (λx. x)"
      pretty (Lam "x" (App (Var "x") (Var "x"))) `shouldBe` "λx. x x"
