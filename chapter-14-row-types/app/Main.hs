{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

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
  putStrLn "=== Row Types REPL ==="
  putStrLn "Commands: :type, :eval, :help, :quit"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "row> "
  hFlush stdout
  line <- TIO.getLine
  case T.words line of
    [] -> repl
    (":quit":_) -> putStrLn "Goodbye!"
    (":q":_) -> putStrLn "Goodbye!"
    (":help":_) -> showHelp >> repl
    (":type":rest) -> handleType (T.unwords rest) >> repl
    (":t":rest) -> handleType (T.unwords rest) >> repl
    (":eval":rest) -> handleEval (T.unwords rest) >> repl
    (":e":rest) -> handleEval (T.unwords rest) >> repl
    _ -> handleDefault line >> repl

handleType :: Text -> IO ()
handleType input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ show err
  Right term -> case typeCheck term of
    Left err -> putStrLn $ "Type error: " ++ show err
    Right ty -> putStrLn $ prettyType ty

handleEval :: Text -> IO ()
handleEval input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ show err
  Right term -> putStrLn $ prettyTerm (eval term)

handleDefault :: Text -> IO ()
handleDefault input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ show err
  Right term -> case typeCheck term of
    Left err -> putStrLn $ "Type error: " ++ show err
    Right ty -> putStrLn $ prettyTerm (eval term) ++ " : " ++ prettyType ty

showHelp :: IO ()
showHelp = do
  putStrLn "Row Types - Extensible Records and Variants"
  putStrLn ""
  putStrLn "Records: {x = 1, y = true}"
  putStrLn "Projection: r.x"
  putStrLn "Extension: {z = 0 | r}"
  putStrLn "Variants: <Left = 0> : <Left: Nat, Right: Bool>"
  putStrLn "Case: case v of <Left = x> -> x | <Right = b> -> 0"
