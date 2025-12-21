{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.IO (hFlush, stdout)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Syntax
import Parser
import TypeCheck
import Eval
import Pretty

main :: IO ()
main = do
  putStrLn "=== Linear Types REPL ==="
  putStrLn "Type expressions to evaluate them."
  putStrLn "Linear variables must be used exactly once!"
  putStrLn "Commands:"
  putStrLn "  :type <expr>  - Show the type of an expression"
  putStrLn "  :help         - Show this help"
  putStrLn "  :quit         - Exit the REPL"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "linear> "
  hFlush stdout
  line <- TIO.getLine
  if T.null (T.strip line)
    then repl
    else case T.words line of
      [":quit"] -> putStrLn "Goodbye!"
      [":help"] -> do
        showHelp
        repl
      (":type" : rest) -> do
        handleType (T.unwords rest)
        repl
      _ -> do
        handleEval line
        repl

showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "=== Linear Types REPL ==="
  putStrLn ""
  putStrLn "Expressions:"
  putStrLn "  λx :1 T. e    - Linear lambda (uses x exactly once)"
  putStrLn "  λx :w T. e    - Unrestricted lambda (uses x any number of times)"
  putStrLn "  \\x :1 T. e    - ASCII linear lambda"
  putStrLn "  e1 e2         - Application"
  putStrLn "  (e1, e2)      - Pair"
  putStrLn "  let (x, y) = e1 in e2  - Pair elimination"
  putStrLn "  !e            - Bang (makes unrestricted)"
  putStrLn "  let !x = e1 in e2      - Bang elimination"
  putStrLn "  let x :1 = e1 in e2    - Linear let"
  putStrLn "  let x :w = e1 in e2    - Unrestricted let"
  putStrLn ""
  putStrLn "Types:"
  putStrLn "  A -o B        - Linear function (uses argument once)"
  putStrLn "  A -> B        - Unrestricted function"
  putStrLn "  A * B         - Pair type"
  putStrLn "  !A            - Bang type (unrestricted A)"
  putStrLn "  Bool, Nat, () - Base types"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  (\\x :1 Nat. x)       - Linear identity"
  putStrLn "  (\\x :w Nat. (x, x))  - Duplicate (must be unrestricted)"
  putStrLn "  let (a, b) = (0, true) in a"
  putStrLn ""

handleEval :: Text -> IO ()
handleEval input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term ->
      case typeCheck term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> do
          let result = eval term
          putStrLn $ prettyTerm result ++ " : " ++ prettyType ty

handleType :: Text -> IO ()
handleType input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term ->
      case typeCheck term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ prettyType ty
