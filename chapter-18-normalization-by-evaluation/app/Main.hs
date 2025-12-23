module Main where

import System.IO (hFlush, stdout)
import Control.Monad (unless)

import Syntax
import Parser
import Pretty
import NbE

main :: IO ()
main = do
  putStrLn "Normalization by Evaluation REPL"
  putStrLn "Commands:"
  putStrLn "  :norm <expr>  - Normalize expression"
  putStrLn "  :help         - Show this help"
  putStrLn "  :quit         - Exit"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "nbe> "
  hFlush stdout
  input <- getLine
  unless (input == ":quit" || input == ":q") $ do
    processInput input
    repl

processInput :: String -> IO ()
processInput input
  | null input = return ()
  | ":norm " `isPrefixOf` input = normalizeInput (drop 6 input)
  | ":help" `isPrefixOf` input = showHelp
  | otherwise = normalizeInput input  -- Default to normalize
  where
    isPrefixOf prefix str = take (length prefix) str == prefix

normalizeInput :: String -> IO ()
normalizeInput input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> do
    let nf = normalize term
    putStrLn $ "Normal form: " ++ prettyNf 0 nf

showHelp :: IO ()
showHelp = do
  putStrLn "Normalization by Evaluation REPL"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  \\x. e            Lambda abstraction"
  putStrLn "  e1 e2            Application"
  putStrLn "  forall (x:A)->B  Pi type"
  putStrLn "  let x:A = e in u Let binding"
  putStrLn "  Type             Universe"
  putStrLn "  Bool             Boolean type"
  putStrLn "  true, false      Boolean values"
  putStrLn "  if b then t else f"
  putStrLn "  Nat              Natural number type"
  putStrLn "  zero, suc n      Natural values"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  (\\x. x) true               -- normalizes to: true"
  putStrLn "  (\\x. \\y. x) true false    -- normalizes to: true"
  putStrLn "  if true then zero else (suc zero)"
