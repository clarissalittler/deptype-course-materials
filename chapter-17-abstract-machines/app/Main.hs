module Main where

import System.IO (hFlush, stdout)
import Control.Monad (unless)

import Syntax
import Parser
import Pretty
import qualified CEK
import qualified Krivine

main :: IO ()
main = do
  putStrLn "Abstract Machines REPL"
  putStrLn "Commands:"
  putStrLn "  :cek <expr>     - Evaluate with CEK machine"
  putStrLn "  :krivine <expr> - Evaluate with Krivine machine"
  putStrLn "  :trace <expr>   - Trace CEK execution"
  putStrLn "  :help           - Show this help"
  putStrLn "  :quit           - Exit"
  putStrLn ""
  repl

repl :: IO ()
repl = do
  putStr "am> "
  hFlush stdout
  input <- getLine
  unless (input == ":quit" || input == ":q") $ do
    processInput input
    repl

processInput :: String -> IO ()
processInput input
  | null input = return ()
  | ":cek " `isPrefixOf` input = evalCEK (drop 5 input)
  | ":krivine " `isPrefixOf` input = evalKrivine (drop 9 input)
  | ":trace " `isPrefixOf` input = traceCEK (drop 7 input)
  | ":help" `isPrefixOf` input = showHelp
  | otherwise = evalCEK input  -- Default to CEK
  where
    isPrefixOf prefix str = take (length prefix) str == prefix

evalCEK :: String -> IO ()
evalCEK input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> case CEK.run term of
    Just val -> putStrLn $ "Result: " ++ prettyValue val
    Nothing  -> putStrLn "Evaluation stuck or diverged"

evalKrivine :: String -> IO ()
evalKrivine input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> case Krivine.run term of
    Just val -> putStrLn $ "Result: " ++ prettyValue val
    Nothing  -> putStrLn "Evaluation stuck or diverged"

traceCEK :: String -> IO ()
traceCEK input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> do
    let states = CEK.trace term
    putStrLn $ "Trace (" ++ show (length states) ++ " steps):"
    mapM_ (putStrLn . ("  " ++) . prettyState) (take 20 states)
    if length states > 20
      then putStrLn $ "  ... (" ++ show (length states - 20) ++ " more steps)"
      else return ()

showHelp :: IO ()
showHelp = do
  putStrLn "Abstract Machines REPL"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  \\x. e       Lambda abstraction"
  putStrLn "  e1 e2       Application"
  putStrLn "  let x = e1 in e2"
  putStrLn "  if0 e then e1 else e2"
  putStrLn "  fix e       Fixed point"
  putStrLn "  n           Integer literal"
  putStrLn "  e1 + e2     Addition"
  putStrLn "  e1 - e2     Subtraction"
  putStrLn "  e1 * e2     Multiplication"
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  (\\x. x + 1) 5"
  putStrLn "  let double = \\x. x + x in double 21"
  putStrLn "  fix (\\f. \\n. if0 n then 1 else n * f (n - 1)) 5"
