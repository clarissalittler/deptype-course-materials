{-# LANGUAGE LambdaCase #-}
-- | Interactive REPL for bidirectional type checking

module Main where

import System.IO (hFlush, stdout)
import Control.Monad (forever, when)
import Data.List (isPrefixOf)

import Syntax
import TypeCheck
import Eval
import Parser
import Pretty

main :: IO ()
main = do
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║     Bidirectional Type Checker - Chapter 19                       ║"
  putStrLn "╠═══════════════════════════════════════════════════════════════════╣"
  putStrLn "║  Commands:                                                        ║"
  putStrLn "║    <term>              - Infer type and evaluate                  ║"
  putStrLn "║    :check <term> : <type>  - Check term against type              ║"
  putStrLn "║    :type <term>        - Only show inferred type                  ║"
  putStrLn "║    :parse <term>       - Show parsed AST                          ║"
  putStrLn "║    :examples           - Show example terms                       ║"
  putStrLn "║    :help               - Show this help                           ║"
  putStrLn "║    :quit               - Exit                                     ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "Key insight: Introduction forms are CHECKED (⇐), elimination forms are INFERRED (⇒)"
  putStrLn ""
  repl

repl :: IO ()
repl = forever $ do
  putStr "bidir> "
  hFlush stdout
  input <- getLine
  when (not $ null input) $ processInput input

processInput :: String -> IO ()
processInput input
  | ":quit" `isPrefixOf` input = do
      putStrLn "Goodbye!"
      error "quit"  -- Simple exit
  | ":help" `isPrefixOf` input = showHelp
  | ":examples" `isPrefixOf` input = showExamples
  | ":parse " `isPrefixOf` input = parseOnly (drop 7 input)
  | ":type " `isPrefixOf` input = typeOnly (drop 6 input)
  | ":check " `isPrefixOf` input = checkTerm (drop 7 input)
  | ":" `isPrefixOf` input = putStrLn "Unknown command. Try :help"
  | otherwise = inferAndEval input

-- | Parse and show AST
parseOnly :: String -> IO ()
parseOnly input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> do
    putStrLn $ "Parsed: " ++ show term
    putStrLn $ "Pretty: " ++ prettyTerm term

-- | Only infer type, don't evaluate
typeOnly :: String -> IO ()
typeOnly input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> case infer emptyCtx term of
    Left err -> putStrLn $ "Type error: " ++ showTypeError err
    Right ty -> putStrLn $ "Type: " ++ prettyType ty

-- | Check term against type
checkTerm :: String -> IO ()
checkTerm input =
  let (termPart, rest) = break (== ':') input
  in if null rest
     then putStrLn "Usage: :check <term> : <type>"
     else case parseTerm (trim termPart) of
       Left err -> putStrLn $ "Parse error in term: " ++ err
       Right term -> case parseType (trim $ drop 1 rest) of
         Left err -> putStrLn $ "Parse error in type: " ++ err
         Right ty -> case check emptyCtx term ty of
           Left err -> putStrLn $ "Check failed: " ++ showTypeError err
           Right () -> do
             putStrLn $ "✓ " ++ prettyTerm term ++ " ⇐ " ++ prettyType ty
             let val = evalClosed term
             putStrLn $ "Value: " ++ prettyVal val

-- | Infer type and evaluate
inferAndEval :: String -> IO ()
inferAndEval input = case parseTerm input of
  Left err -> putStrLn $ "Parse error: " ++ err
  Right term -> case infer emptyCtx term of
    Left err -> do
      putStrLn $ "Cannot infer: " ++ showTypeError err
      putStrLn "Hint: Use annotation (term : Type) or :check command"
    Right ty -> do
      putStrLn $ prettyTerm term ++ " ⇒ " ++ prettyType ty
      let val = evalClosed term
      putStrLn $ "Value: " ++ prettyVal val

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║                    Bidirectional Type Checking                    ║"
  putStrLn "╠═══════════════════════════════════════════════════════════════════╣"
  putStrLn "║                                                                   ║"
  putStrLn "║  Two judgment forms:                                              ║"
  putStrLn "║    Γ ⊢ e ⇒ A    \"infer type A for e\"    (synthesis)              ║"
  putStrLn "║    Γ ⊢ e ⇐ A    \"check e against A\"     (checking)               ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Key principle:                                                   ║"
  putStrLn "║    • Introduction forms are CHECKED                               ║"
  putStrLn "║    • Elimination forms are INFERRED                               ║"
  putStrLn "║    • Annotations switch from checking to inference                ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Syntax:                                                          ║"
  putStrLn "║    \\x. e          Unannotated lambda (needs checking)            ║"
  putStrLn "║    \\(x : T). e    Annotated lambda (can be inferred)             ║"
  putStrLn "║    (e : T)        Type annotation                                 ║"
  putStrLn "║    /\\a. e         Type abstraction                               ║"
  putStrLn "║    e [T]          Type application                                ║"
  putStrLn "║    (e1, e2)       Pair                                            ║"
  putStrLn "║    inl e, inr e   Sum injections                                  ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Types:                                                           ║"
  putStrLn "║    Bool, Nat, Unit                                                ║"
  putStrLn "║    A -> B          Function type                                  ║"
  putStrLn "║    (A, B)          Product type                                   ║"
  putStrLn "║    (A + B)         Sum type                                       ║"
  putStrLn "║    forall a. T     Universal type                                 ║"
  putStrLn "║                                                                   ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = do
  putStrLn ""
  putStrLn "Examples:"
  putStrLn ""
  putStrLn "-- Unannotated lambda (cannot be inferred)"
  putStrLn "  \\x. x"
  putStrLn "  → Error: Cannot infer type"
  putStrLn ""
  putStrLn "-- Annotated lambda (can be inferred)"
  putStrLn "  \\(x : Bool). x"
  putStrLn "  → Bool → Bool"
  putStrLn ""
  putStrLn "-- Type annotation switches modes"
  putStrLn "  (\\x. x : Bool -> Bool)"
  putStrLn "  → Bool → Bool"
  putStrLn ""
  putStrLn "-- Checking mode for lambda"
  putStrLn "  :check \\x. x : Bool -> Bool"
  putStrLn "  → ✓"
  putStrLn ""
  putStrLn "-- Application infers function, checks argument"
  putStrLn "  (\\(x : Bool). x) true"
  putStrLn "  → Bool"
  putStrLn ""
  putStrLn "-- Polymorphic identity"
  putStrLn "  (/\\a. \\(x : a). x : forall a. a -> a)"
  putStrLn "  → ∀a. a → a"
  putStrLn ""
  putStrLn "-- Type application"
  putStrLn "  (/\\a. \\(x : a). x : forall a. a -> a) [Bool]"
  putStrLn "  → Bool → Bool"
  putStrLn ""
  putStrLn "-- Pairs (need checking)"
  putStrLn "  :check (true, zero) : (Bool, Nat)"
  putStrLn "  → ✓"
  putStrLn ""
  putStrLn "-- Projection (infers)"
  putStrLn "  fst ((true, zero) : (Bool, Nat))"
  putStrLn "  → Bool"
  putStrLn ""

-- | Show type error in a readable way
showTypeError :: TypeError -> String
showTypeError = \case
  UnboundVariable x -> "Unbound variable: " ++ x
  UnboundTypeVariable a -> "Unbound type variable: " ++ a
  TypeMismatch expected actual ->
    "Type mismatch: expected " ++ prettyType expected ++
    ", got " ++ prettyType actual
  ExpectedFunction ty ->
    "Expected function type, got: " ++ prettyType ty
  ExpectedForall ty ->
    "Expected polymorphic type (∀), got: " ++ prettyType ty
  ExpectedBool ty ->
    "Expected Bool, got: " ++ prettyType ty
  ExpectedNat ty ->
    "Expected Nat, got: " ++ prettyType ty
  ExpectedProduct ty ->
    "Expected product type (×), got: " ++ prettyType ty
  ExpectedSum ty ->
    "Expected sum type (+), got: " ++ prettyType ty
  CannotInfer _ ->
    "Cannot infer type for this term (try adding annotation)"

-- | Trim whitespace
trim :: String -> String
trim = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse
