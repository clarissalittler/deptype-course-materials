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
  putStrLn "=== Effect Systems REPL ==="
  putStrLn "Commands:"
  putStrLn "  :type <term>    - Show the type of a term"
  putStrLn "  :eval <term>    - Evaluate a term"
  putStrLn "  :effects        - Show available effects"
  putStrLn "  :help           - Show this help"
  putStrLn "  :quit           - Exit"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  :type \\x : Nat. perform State.get ()"
  putStrLn "  :eval succ (succ 0)"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "effect> "
  hFlush stdout
  line <- TIO.getLine
  case T.words line of
    [] -> repl
    (":quit" : _) -> putStrLn "Goodbye!"
    (":q" : _) -> putStrLn "Goodbye!"
    (":help" : _) -> do
      showHelp
      repl
    (":effects" : _) -> do
      showEffects
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
        Right (TypeAndEffect ty eff) ->
          putStrLn $ prettyType ty ++
            (if isEmptyEff eff then "" else " ! " ++ prettyEffectRow eff)
  where
    isEmptyEff EffEmpty = True
    isEmptyEff _ = False

handleEval :: Text -> IO ()
handleEval input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term -> putStrLn $ prettyTerm (eval term)

handleDefault :: Text -> IO ()
handleDefault input =
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right term ->
      case typeCheck term of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right (TypeAndEffect ty eff) -> do
          let result = eval term
          putStrLn $ prettyTerm result ++ " : " ++ prettyType ty ++
            (if isEmptyEff eff then "" else " ! " ++ prettyEffectRow eff)
  where
    isEmptyEff EffEmpty = True
    isEmptyEff _ = False

showEffects :: IO ()
showEffects = do
  putStrLn "Available effects:"
  putStrLn ""
  putStrLn "  State:"
  putStrLn "    get : Unit -> Nat"
  putStrLn "    put : Nat -> Unit"
  putStrLn ""
  putStrLn "  Exception:"
  putStrLn "    throw : Unit -> Unit"
  putStrLn ""
  putStrLn "  IO:"
  putStrLn "    print : Nat -> Unit"
  putStrLn "    read : Unit -> Nat"
  putStrLn ""
  putStrLn "  Choice:"
  putStrLn "    choose : Bool -> Bool"

showHelp :: IO ()
showHelp = do
  putStrLn "=== Effect Systems REPL ==="
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :type <term>    - Show the type and effects of a term (or :t)"
  putStrLn "  :eval <term>    - Evaluate a term (or :e)"
  putStrLn "  :effects        - Show available effects"
  putStrLn "  :help           - Show this help"
  putStrLn "  :quit           - Exit (or :q)"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit           - Base types"
  putStrLn "    T1 -> T2                  - Pure function"
  putStrLn "    T1 -> T2 ! {E1, E2}       - Effectful function"
  putStrLn "    ∀ρ. T                     - Effect-polymorphic type"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    λx : T. t                 - Lambda"
  putStrLn "    perform Eff.op t          - Perform effect operation"
  putStrLn "    handle t with h           - Handle effects"
  putStrLn "    return t                  - Pure value"
  putStrLn "    Λρ. t                     - Effect abstraction"
  putStrLn "    t [{E}]                   - Effect application"
  putStrLn ""
  putStrLn "  Handlers:"
  putStrLn "    { Eff: return x -> body; op p k -> body }"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  perform State.get ()        - Get state"
  putStrLn "  perform State.put 5         - Put state"
  putStrLn "  handle (perform State.get ()) with { State: return x -> x; ... }"
