{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

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
  putStrLn "=== Gradual Typing REPL ==="
  putStrLn "Commands:"
  putStrLn "  :type <term>    - Show the type of a term"
  putStrLn "  :eval <term>    - Evaluate a term"
  putStrLn "  :casts <term>   - Show term with explicit casts"
  putStrLn "  :help           - Show this help"
  putStrLn "  :quit           - Exit"
  putStrLn ""
  putStrLn "The dynamic type is written as ?"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  :type \\x : ?. x"
  putStrLn "  :eval (\\x : ?. succ x) 0"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "gradual> "
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
    (":casts" : rest) -> do
      handleCasts (T.unwords rest)
      repl
    _ -> do
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

handleCasts :: Text -> IO ()
handleCasts input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term ->
      case insertCasts emptyContext term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right term' -> putStrLn $ prettyTerm term'

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
  putStrLn "=== Gradual Typing REPL ==="
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :type <term>    - Show the type of a term (or :t)"
  putStrLn "  :eval <term>    - Evaluate a term (or :e)"
  putStrLn "  :casts <term>   - Show term with explicit casts"
  putStrLn "  :help           - Show this help"
  putStrLn "  :quit           - Exit (or :q)"
  putStrLn ""
  putStrLn "Types:"
  putStrLn "  Bool, Nat, Unit  - Base types"
  putStrLn "  ?                - Dynamic type (consistent with everything)"
  putStrLn "  T1 -> T2         - Function type"
  putStrLn ""
  putStrLn "Terms:"
  putStrLn "  λx : T. t        - Lambda (also \\x : T. t)"
  putStrLn "  t1 t2            - Application"
  putStrLn "  t : T            - Type ascription"
  putStrLn "  <T1 => T2>^l t   - Explicit cast (for advanced use)"
  putStrLn ""
  putStrLn "Key concept: The dynamic type ? is consistent with any type."
  putStrLn "This allows mixing typed and untyped code!"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  \\x : ?. succ x     -- Dynamic input, treated as Nat at runtime"
  putStrLn "  (\\x : ?. x) true   -- Dynamic function applied to Bool"
