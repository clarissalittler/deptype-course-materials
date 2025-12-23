{-# LANGUAGE LambdaCase #-}
-- | Interactive REPL for denotational semantics

module Main where

import System.IO (hFlush, stdout)
import Control.Monad (forever, when)
import Data.List (isPrefixOf)

import Syntax
import Domain
import Denotation
import Parser
import Pretty

main :: IO ()
main = do
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║     Denotational Semantics Explorer - Chapter 20                  ║"
  putStrLn "╠═══════════════════════════════════════════════════════════════════╣"
  putStrLn "║  Commands:                                                        ║"
  putStrLn "║    <term>              - Compute denotation                       ║"
  putStrLn "║    :fix n <term>       - Show n iterations of fixed point         ║"
  putStrLn "║    :fact n             - Compute factorial(n)                     ║"
  putStrLn "║    :fib n              - Compute fibonacci(n)                     ║"
  putStrLn "║    :examples           - Show example terms                       ║"
  putStrLn "║    :theory             - Show domain theory concepts              ║"
  putStrLn "║    :help               - Show this help                           ║"
  putStrLn "║    :quit               - Exit                                     ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "Key insight: [[fix f]] = ⊔ₙ fⁿ(⊥), the least fixed point of f"
  putStrLn ""
  repl

repl :: IO ()
repl = forever $ do
  putStr "den> "
  hFlush stdout
  input <- getLine
  when (not $ null input) $ processInput input

processInput :: String -> IO ()
processInput input
  | ":quit" `isPrefixOf` input = do
      putStrLn "Goodbye!"
      error "quit"
  | ":help" `isPrefixOf` input = showHelp
  | ":examples" `isPrefixOf` input = showExamples
  | ":theory" `isPrefixOf` input = showTheory
  | ":fix " `isPrefixOf` input = showFixIterations (drop 5 input)
  | ":fact " `isPrefixOf` input = computeFactorial (drop 6 input)
  | ":fib " `isPrefixOf` input = computeFibonacci (drop 5 input)
  | ":" `isPrefixOf` input = putStrLn "Unknown command. Try :help"
  | otherwise = evaluateTerm input

-- | Evaluate a term and show its denotation
evaluateTerm :: String -> IO ()
evaluateTerm input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> do
    putStrLn $ "Term: " ++ prettyTerm term
    let d = denoteClosed term
    putStrLn $ "[[·]] = " ++ prettyDom d

-- | Show iterations of fixed point computation
showFixIterations :: String -> IO ()
showFixIterations input =
  let (nStr, rest) = break (== ' ') input
  in case (reads nStr :: [(Int, String)]) of
    [(n, "")] -> case parseTerm (dropWhile (== ' ') rest) of
      Left err -> putStrLn $ "Parse error: " ++ err
      Right term -> do
        putStrLn $ "Computing fixed point iterations for: " ++ prettyTerm term
        let d = denoteClosed term
        case d of
          DFun f -> do
            putStrLn "Chain: ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ ..."
            putStrLn ""
            mapM_ (showIteration f) [0..n]
          _ -> putStrLn "Error: expected function term"
    _ -> putStrLn "Usage: :fix N <function-term>"
  where
    showIteration f i = do
      let approxI = fixN i f
      putStrLn $ "f^" ++ show i ++ "(⊥) = " ++ prettyDom approxI

-- | Compute factorial
computeFactorial :: String -> IO ()
computeFactorial input =
  case reads input :: [(Integer, String)] of
    [(n, "")] -> do
      let result = factorialDen n
      putStrLn $ "[[fact]](" ++ show n ++ ") = " ++ prettyDom result
    _ -> putStrLn "Usage: :fact N"

-- | Compute fibonacci
computeFibonacci :: String -> IO ()
computeFibonacci input =
  case reads input :: [(Integer, String)] of
    [(n, "")] -> do
      let result = fibonacciDen n
      putStrLn $ "[[fib]](" ++ show n ++ ") = " ++ prettyDom result
    _ -> putStrLn "Usage: :fib N"

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║                    Denotational Semantics                         ║"
  putStrLn "╠═══════════════════════════════════════════════════════════════════╣"
  putStrLn "║                                                                   ║"
  putStrLn "║  The denotation [[e]] maps syntax to semantic domains.            ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Key equations:                                                   ║"
  putStrLn "║    [[x]]ρ = ρ(x)                           (variable lookup)      ║"
  putStrLn "║    [[λx. e]]ρ = λd. [[e]]ρ[x↦d]           (abstraction)           ║"
  putStrLn "║    [[e1 e2]]ρ = [[e1]]ρ([[e2]]ρ)          (application)           ║"
  putStrLn "║    [[fix f]]ρ = ⊔ₙ ([[f]]ρ)ⁿ(⊥)           (least fixed point)     ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Syntax:                                                          ║"
  putStrLn "║    \\(x : T). e    Lambda abstraction                             ║"
  putStrLn "║    e1 e2          Application                                     ║"
  putStrLn "║    fix e          Fixed point (for recursion)                     ║"
  putStrLn "║    if c then t else e                                             ║"
  putStrLn "║    let x = e1 in e2                                               ║"
  putStrLn "║    0, suc n       Natural numbers                                 ║"
  putStrLn "║    pred n, iszero n                                               ║"
  putStrLn "║    true, false, ()                                                ║"
  putStrLn "║    ⊥ T            Explicit bottom of type T                       ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Types: Bool, Nat, Unit, A -> B                                   ║"
  putStrLn "║                                                                   ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""

-- | Show domain theory concepts
showTheory :: IO ()
showTheory = do
  putStrLn ""
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║                       Domain Theory                               ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "DOMAINS (Complete Partial Orders)"
  putStrLn "  A domain D is a set with:"
  putStrLn "  • A partial order ⊑ (approximation)"
  putStrLn "  • A least element ⊥ (bottom = undefined)"
  putStrLn "  • Suprema (⊔) of all directed sets"
  putStrLn ""
  putStrLn "FLAT DOMAINS"
  putStrLn "  For base types like Nat:"
  putStrLn "        0   1   2   3   ..."
  putStrLn "         \\  |  /   /"
  putStrLn "          \\ | /   /"
  putStrLn "           \\|/   /"
  putStrLn "            ⊥"
  putStrLn "  All defined values are incomparable;"
  putStrLn "  only ⊥ is below everything."
  putStrLn ""
  putStrLn "FUNCTION DOMAINS [A → B]"
  putStrLn "  Consist of all Scott-continuous functions."
  putStrLn "  Continuous = preserves suprema of directed sets."
  putStrLn "  Ordered pointwise: f ⊑ g iff ∀x. f(x) ⊑ g(x)"
  putStrLn ""
  putStrLn "LEAST FIXED POINTS"
  putStrLn "  For a continuous f : D → D:"
  putStrLn "  fix f = ⊔ₙ fⁿ(⊥)"
  putStrLn ""
  putStrLn "  The chain: ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ f³(⊥) ⊑ ..."
  putStrLn "  converges to the least fixed point."
  putStrLn ""
  putStrLn "  This is why recursion works!"
  putStrLn "  Each iteration gives a better approximation."
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = do
  putStrLn ""
  putStrLn "Examples:"
  putStrLn ""
  putStrLn "-- Identity function"
  putStrLn "  (\\(x : Nat). x) 5"
  putStrLn "  [[·]] = 5"
  putStrLn ""
  putStrLn "-- Successor"
  putStrLn "  suc (suc 0)"
  putStrLn "  [[·]] = 2"
  putStrLn ""
  putStrLn "-- Conditional"
  putStrLn "  if iszero 0 then 42 else 0"
  putStrLn "  [[·]] = 42"
  putStrLn ""
  putStrLn "-- Let binding"
  putStrLn "  let x = 3 in suc x"
  putStrLn "  [[·]] = 4"
  putStrLn ""
  putStrLn "-- Factorial (uses fix internally)"
  putStrLn "  :fact 5"
  putStrLn "  [[fact]](5) = 120"
  putStrLn ""
  putStrLn "-- Fibonacci (uses fix internally)"
  putStrLn "  :fib 10"
  putStrLn "  [[fib]](10) = 55"
  putStrLn ""
  putStrLn "-- Fixed point iterations"
  putStrLn "  :fix 5 \\(f : Nat -> Nat). \\(x : Nat). if iszero x then 1 else x"
  putStrLn "  Shows how the fixed point is approximated"
  putStrLn ""
