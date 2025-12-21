{-# LANGUAGE OverloadedStrings #-}

module Main where

import Syntax
import TypeCheck
import Eval
import Parser
import Pretty

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.IO (hFlush, stdout)

main :: IO ()
main = do
  putStrLn "=== Refinement Types REPL ==="
  putStrLn "Commands:"
  putStrLn "  :type <term>   - Show the type of a term"
  putStrLn "  :eval <term>   - Evaluate a term"
  putStrLn "  :check <pred>  - Check if a predicate is valid"
  putStrLn "  :help          - Show this help"
  putStrLn "  :quit          - Exit"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  :type \\x : {n : Nat | n > 0}. x"
  putStrLn "  :eval succ (succ 0)"
  putStrLn "  :check 1 > 0"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "refinement> "
  hFlush stdout
  line <- TIO.getLine
  case T.words line of
    [] -> repl
    (":quit" : _) -> putStrLn "Goodbye!"
    (":q" : _) -> putStrLn "Goodbye!"
    (":help" : _) -> do
      showHelp
      repl
    (":type" : rest) -> do
      handleType (T.unwords rest)
      repl
    (":t" : rest) -> do
      handleType (T.unwords rest)
      repl
    (":eval" : rest) -> do
      handleEval (T.unwords rest)
      repl
    (":e" : rest) -> do
      handleEval (T.unwords rest)
      repl
    (":check" : rest) -> do
      handleCheck (T.unwords rest)
      repl
    (":c" : rest) -> do
      handleCheck (T.unwords rest)
      repl
    _ -> do
      -- Default: try to type check and evaluate
      handleDefault line
      repl

handleType :: Text -> IO ()
handleType input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term ->
      case typeCheck term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ prettyType ty

handleEval :: Text -> IO ()
handleEval input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term -> putStrLn $ prettyTerm (eval term)

handleCheck :: Text -> IO ()
handleCheck input =
  case parsePred input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right p ->
      if isValid p
        then putStrLn "Valid (always true)"
        else putStrLn "Not valid (may be false)"

handleDefault :: Text -> IO ()
handleDefault input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term ->
      case typeCheck term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> do
          let result = eval term
          putStrLn $ prettyTerm result ++ " : " ++ prettyType ty

showHelp :: IO ()
showHelp = do
  putStrLn "=== Refinement Types REPL ==="
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :type <term>   - Show the type of a term (or :t)"
  putStrLn "  :eval <term>   - Evaluate a term (or :e)"
  putStrLn "  :check <pred>  - Check if a predicate is valid (or :c)"
  putStrLn "  :help          - Show this help"
  putStrLn "  :quit          - Exit (or :q)"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit          - Base types"
  putStrLn "    {x : T | φ}              - Refinement type"
  putStrLn "    T1 -> T2                 - Function type"
  putStrLn "    (x : T1) -> T2           - Dependent function type"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    true, false              - Booleans"
  putStrLn "    0, 1, 2, ...             - Natural numbers"
  putStrLn "    succ t, pred t           - Successor, predecessor"
  putStrLn "    iszero t                 - Zero test"
  putStrLn "    t1 + t2, t1 - t2         - Arithmetic"
  putStrLn "    if t1 then t2 else t3    - Conditional"
  putStrLn "    \\x : T. t                - Lambda"
  putStrLn "    t1 t2                    - Application"
  putStrLn "    let x = t1 in t2         - Let binding"
  putStrLn "    t : T                    - Type ascription"
  putStrLn ""
  putStrLn "  Predicates:"
  putStrLn "    true, false              - Constants"
  putStrLn "    a1 == a2, a1 != a2       - Equality/inequality"
  putStrLn "    a1 < a2, a1 <= a2        - Comparison"
  putStrLn "    a1 > a2, a1 >= a2        - Comparison"
  putStrLn "    !p                       - Negation"
  putStrLn "    p1 && p2, p1 || p2       - Conjunction, disjunction"
  putStrLn "    p1 => p2                 - Implication"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  {x : Nat | x > 0}          - Positive naturals"
  putStrLn "  {x : Nat | x >= 0 && x < 10} - Naturals 0-9"
  putStrLn "  \\f : ({x:Nat|x>0} -> Nat). f 1"
