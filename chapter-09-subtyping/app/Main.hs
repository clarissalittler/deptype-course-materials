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
  putStrLn "=== STLC with Subtyping REPL ==="
  putStrLn "Type expressions to evaluate them."
  putStrLn "Commands:"
  putStrLn "  :type <expr>  - Show the type of an expression"
  putStrLn "  :subtype T1 T2 - Check if T1 <: T2"
  putStrLn "  :help         - Show this help"
  putStrLn "  :quit         - Exit the REPL"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "subtype> "
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
      (":subtype" : rest) -> do
        handleSubtype (T.unwords rest)
        repl
      _ -> do
        handleEval line
        repl

showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "=== STLC with Subtyping REPL ==="
  putStrLn ""
  putStrLn "Expressions:"
  putStrLn "  λx:T. e       - Lambda abstraction"
  putStrLn "  \\x:T. e       - Lambda (ASCII syntax)"
  putStrLn "  e1 e2         - Application"
  putStrLn "  true, false   - Booleans"
  putStrLn "  if e1 then e2 else e3"
  putStrLn "  0, succ e, pred e, iszero e"
  putStrLn "  {l1 = e1, l2 = e2, ...}  - Records"
  putStrLn "  e.l           - Projection"
  putStrLn "  e as T        - Type ascription"
  putStrLn ""
  putStrLn "Types:"
  putStrLn "  Bool, Nat     - Base types"
  putStrLn "  Top           - Supertype of all types"
  putStrLn "  Bot           - Subtype of all types"
  putStrLn "  T1 -> T2      - Function type"
  putStrLn "  {l1: T1, ...} - Record type"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  (\\x:Top. x) true"
  putStrLn "  {name = true, age = succ 0}"
  putStrLn "  {x = 0, y = succ 0}.x"
  putStrLn "  (\\r:{x: Nat}. r.x) {x = 0, y = succ 0}"
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

handleSubtype :: Text -> IO ()
handleSubtype input =
  -- Parse two types separated by space
  case parseSubtypeInput input of
    Left err -> putStrLn err
    Right (t1, t2) ->
      if isSubtype t1 t2
        then putStrLn $ prettyType t1 ++ " <: " ++ prettyType t2 ++ " ✓"
        else putStrLn $ prettyType t1 ++ " <: " ++ prettyType t2 ++ " ✗"

-- | Parse input for :subtype command
-- Expects two types, possibly with arrow syntax
-- We use a simple heuristic: split on the word "and" or multiple args
parseSubtypeInput :: Text -> Either String (Type, Type)
parseSubtypeInput input = do
  -- Try to parse as "T1 T2" by finding where to split
  -- This is tricky because types can contain spaces
  -- Use a simple approach: parse from both ends
  let parts = T.words input
  case parts of
    [t1, t2] -> do
      ty1 <- case parseType t1 of
        Left _ -> Left $ "Cannot parse first type: " ++ T.unpack t1
        Right ty -> Right ty
      ty2 <- case parseType t2 of
        Left _ -> Left $ "Cannot parse second type: " ++ T.unpack t2
        Right ty -> Right ty
      Right (ty1, ty2)
    _ -> Left "Usage: :subtype Type1 Type2"
