module Main (main) where

import System.IO (hFlush, stdout)
import Data.Text (Text, pack)
import Parser
import TypeCheck
import Eval
import Pretty

main :: IO ()
main = do
  putStrLn "Homotopy Type Theory REPL"
  putStrLn "Type expressions to evaluate, :t <expr> to type-check, or :q to quit"
  putStrLn "Examples:"
  putStrLn "  refl [Nat] 0                           -- reflexivity path"
  putStrLn "  sym (refl [Bool] true)                 -- path symmetry"
  putStrLn "  trans (refl [Nat] 0) (refl [Nat] 0)    -- path transitivity"
  putStrLn "  ap (\\x:Nat. succ x) (refl [Nat] 0)    -- apply function to path"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "hott> "
  hFlush stdout
  input <- getLine
  case input of
    ":q" -> putStrLn "Goodbye!"
    ':':'t':' ':rest -> do
      typeCheckInput (pack rest)
      repl
    _ -> do
      evalInput (pack input)
      repl

typeCheckInput :: Text -> IO ()
typeCheckInput input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right term ->
      case typeCheck term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ prettyType ty

evalInput :: Text -> IO ()
evalInput input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right term ->
      case typeCheck term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right _ -> putStrLn $ prettyTerm (eval term)
