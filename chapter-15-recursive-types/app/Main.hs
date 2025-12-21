module Main (main) where

import System.IO (hFlush, stdout)
import Data.Text (Text, pack)
import Syntax
import Parser
import TypeCheck
import Eval
import Pretty

main :: IO ()
main = do
  putStrLn "Recursive Types REPL"
  putStrLn "Type expressions to evaluate, :t <expr> to type-check, or :q to quit"
  putStrLn "Examples:"
  putStrLn "  fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a))"
  putStrLn "  let nil = fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a)))) in nil"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "recursive> "
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
