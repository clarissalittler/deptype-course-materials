{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module REPL (runREPL) where

import Syntax
import Parser
import Pretty
import TypeCheck
import Eval

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as T
import System.IO (hFlush, stdout)
import Control.Exception (catch, IOException)
import GHC.IO.Exception (IOErrorType(..))
import System.IO.Error (ioeGetErrorType)

-- | REPL State
data REPLState = REPLState
  { bindings :: Map String Term
  , typeBindings :: Map String Type
  , showSteps :: Bool
  , showTypes :: Bool
  , maxSteps :: Int
  }

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { bindings = Map.empty
  , typeBindings = Map.empty
  , showSteps = False
  , showTypes = True
  , maxSteps = 1000
  }

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "==========================================="
  putStrLn "Refinement Types REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Predicate refinements, subtyping,"
  putStrLn "          dependent function types, validity checking"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :check p           Check if predicate p is valid"
  putStrLn "  :subtype T1 T2     Check if T1 <: T2"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Type an expression to evaluate and type check it."
  putStrLn "Type :examples to see comprehensive examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "refinement> "
  hFlush stdout
  input <- getLine `catch` handleEOF
  case input of
    "" -> repl state
    (':':cmd) -> do
      state' <- handleCommand cmd state
      repl state'
    _ -> do
      state' <- handleInput input state
      repl state'
  where
    handleEOF :: IOException -> IO String
    handleEOF e =
      if ioeGetErrorType e == EOF
      then putStrLn "" >> return ":quit"
      else putStrLn ("\nIO error: " ++ show e) >> return ""

-- | Handle REPL commands
handleCommand :: String -> REPLState -> IO REPLState
handleCommand cmd state = case words cmd of
  ["help"] -> showHelp >> return state
  ["examples"] -> showExamples >> return state
  ["quit"] -> putStrLn "Goodbye!" >> error "quit"
  ["q"] -> putStrLn "Goodbye!" >> error "quit"
  ["env"] -> showEnv state >> return state
  ["reset"] -> putStrLn "Bindings reset." >> return initialState

  ("let" : x : "=" : rest) -> handleLetBinding x (unwords rest) state

  ("type" : rest) -> handleTypeOf (unwords rest) >> return state
  ("t" : rest) -> handleTypeOf (unwords rest) >> return state

  ("check" : rest) -> handleCheckPred (unwords rest) >> return state
  ("c" : rest) -> handleCheckPred (unwords rest) >> return state

  ("subtype" : rest) -> handleSubtype (unwords rest) >> return state

  ("step" : rest) -> handleStep (unwords rest) >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

  ("eval" : rest) -> handleEval (unwords rest) >> return state
  ("e" : rest) -> handleEval (unwords rest) >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn ("Parse error: " ++ show err) >> return state
    Right t -> do
      case typeCheck t of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right ty -> do
          let v = eval t
          putStrLn $ x ++ " : " ++ prettyType ty ++ " = " ++ prettyTerm v
          return state
            { bindings = Map.insert x v (bindings state)
            , typeBindings = Map.insert x ty (typeBindings state)
            }

-- | Handle :type command
handleTypeOf :: String -> IO ()
handleTypeOf input = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      case typeCheck t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ prettyType ty

-- | Handle :check command for predicate validity
handleCheckPred :: String -> IO ()
handleCheckPred input = do
  case parsePred (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right p ->
      if isValid p
        then putStrLn $ "  " ++ prettyPred p ++ " is VALID (always true)"
        else putStrLn $ "  " ++ prettyPred p ++ " is NOT VALID (may be false)"

-- | Handle :subtype command
handleSubtype :: String -> IO ()
handleSubtype input = do
  -- Try to parse two types separated by "and" or ";"
  case parseSubtypeArgs (T.pack input) of
    Left err -> putStrLn err
    Right (t1, t2) ->
      if isSubtype emptyContext t1 t2
        then putStrLn $ "  " ++ prettyType t1 ++ " <: " ++ prettyType t2 ++ "  ✓"
        else putStrLn $ "  " ++ prettyType t1 ++ " <: " ++ prettyType t2 ++ "  ✗"

-- | Parse two types for subtype command
parseSubtypeArgs :: T.Text -> Either String (Type, Type)
parseSubtypeArgs input = do
  let stripped = T.strip input
  case findSplit stripped of
    Nothing -> Left "Usage: :subtype Type1 and Type2"
    Just (s1, s2) -> do
      ty1 <- case parseType s1 of
        Left _ -> Left $ "Cannot parse first type: " ++ T.unpack s1
        Right ty -> Right ty
      ty2 <- case parseType s2 of
        Left _ -> Left $ "Cannot parse second type: " ++ T.unpack s2
        Right ty -> Right ty
      Right (ty1, ty2)

-- | Find a good split point for two types
findSplit :: T.Text -> Maybe (T.Text, T.Text)
findSplit input
  | " and " `T.isInfixOf` input =
      let parts = T.splitOn " and " input
      in case parts of
        [t1, t2] -> Just (T.strip t1, T.strip t2)
        _ -> Nothing
  | ";" `T.isInfixOf` input =
      let parts = T.splitOn ";" input
      in case parts of
        [t1, t2] -> Just (T.strip t1, T.strip t2)
        _ -> Nothing
  | otherwise = Nothing

-- | Handle :step command
handleStep :: String -> IO ()
handleStep input = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      case evalStep t of
        Nothing -> putStrLn "  (no reduction possible)"
        Just t' -> putStrLn $ "  ⟶  " ++ prettyTerm t'

-- | Handle :steps command
handleSteps :: String -> REPLState -> IO ()
handleSteps input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      let steps = generateEvalSteps t (maxSteps state)
      mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ s) (zip [0::Int ..] steps)

-- | Handle :eval command
handleEval :: String -> IO ()
handleEval input = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> putStrLn $ "  " ++ prettyTerm (eval t)

-- | Generate evaluation steps
generateEvalSteps :: Term -> Int -> [String]
generateEvalSteps t maxS = go t 0
  where
    go current n
      | n >= maxS = [prettyTerm current ++ " (max steps reached)"]
      | otherwise = case evalStep current of
          Nothing -> [prettyTerm current]
          Just next -> prettyTerm current : go next (n + 1)

-- | Handle term input
handleInput :: String -> REPLState -> IO REPLState
handleInput input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn ("Parse error: " ++ show err) >> return state
    Right t -> do
      case typeCheck t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> do
          when (showTypes state) $
            putStrLn $ "  : " ++ prettyType ty
          let result = eval t
          putStrLn $ "  " ++ prettyTerm result
      return state

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Bindings:"
  if Map.null (bindings state)
    then putStrLn "  (none)"
    else mapM_ showBinding (Map.toList $ bindings state)
  where
    showBinding (x, v) = case Map.lookup x (typeBindings state) of
      Just ty -> putStrLn $ "  " ++ x ++ " : " ++ prettyType ty ++ " = " ++ prettyTerm v
      Nothing -> putStrLn $ "  " ++ x ++ " = " ++ prettyTerm v

-- | Helper for when
when :: Bool -> IO () -> IO ()
when True action = action
when False _ = return ()

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "Refinement Types REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL (or :q)"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t (or :t)"
  putStrLn "  :check p           Check if predicate p is valid (or :c)"
  putStrLn "  :subtype T1 and T2 Check if T1 <: T2"
  putStrLn "  :eval t            Just evaluate, no type check (or :e)"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit            Base types"
  putStrLn "    {x : T | p}                Refinement type"
  putStrLn "    T1 -> T2                   Function type"
  putStrLn "    (x : T1) -> T2             Dependent function type"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    true, false                Booleans"
  putStrLn "    0, 1, 2, ...               Natural numbers"
  putStrLn "    succ t, pred t             Successor, predecessor"
  putStrLn "    t1 + t2, t1 - t2           Arithmetic"
  putStrLn "    iszero t                   Zero test"
  putStrLn "    if t1 then t2 else t3      Conditional"
  putStrLn "    \\x : T. t                  Lambda"
  putStrLn "    t1 t2                      Application"
  putStrLn "    let x = t1 in t2           Let binding"
  putStrLn "    t : T                      Type ascription"
  putStrLn ""
  putStrLn "  Predicates:"
  putStrLn "    true, false                Constants"
  putStrLn "    a1 == a2, a1 != a2         Equality/inequality"
  putStrLn "    a1 < a2, a1 <= a2          Less than"
  putStrLn "    a1 > a2, a1 >= a2          Greater than"
  putStrLn "    !p                         Negation"
  putStrLn "    p1 && p2, p1 || p2         Conjunction, disjunction"
  putStrLn "    p1 => p2                   Implication"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Refinement Types Examples"
  , "==========================================="
  , ""
  , "--- Basic Refinement Types ---"
  , ""
  , "1. Positive naturals:"
  , "   {x : Nat | x > 0}"
  , ""
  , "2. Naturals in range:"
  , "   {x : Nat | x >= 0 && x < 10}"
  , ""
  , "3. The singleton true:"
  , "   {x : Bool | x == true}"
  , ""
  , "--- Type Checking with Refinements ---"
  , ""
  , "4. Function on positive naturals:"
  , "   \\x : {n : Nat | n > 0}. x - 1"
  , "   : {n : Nat | n > 0} -> Nat"
  , ""
  , "5. Predecessor is safe on positive:"
  , "   \\x : {n : Nat | n > 0}. pred x"
  , "   : {n : Nat | n > 0} -> Nat"
  , ""
  , "6. Division-safe (non-zero denominator):"
  , "   -- div : Nat -> {d : Nat | d > 0} -> Nat"
  , ""
  , "--- Subtyping with Refinements ---"
  , ""
  , "7. More refined is subtype:"
  , "   :subtype {x : Nat | x > 5} and {x : Nat | x > 0}"
  , "   {x : Nat | x > 5} <: {x : Nat | x > 0}  ✓"
  , ""
  , "8. Not the other way:"
  , "   :subtype {x : Nat | x > 0} and {x : Nat | x > 5}"
  , "   {x : Nat | x > 0} <: {x : Nat | x > 5}  ✗"
  , ""
  , "--- Dependent Function Types ---"
  , ""
  , "9. Result type depends on input:"
  , "   (n : Nat) -> {x : Nat | x <= n}"
  , "   -- Returns a number no larger than input"
  , ""
  , "10. Safe indexing:"
  , "    -- nth : (n : Nat) -> Vec n a -> {i : Nat | i < n} -> a"
  , ""
  , "--- Predicate Validity ---"
  , ""
  , "11. Check if predicate is always true:"
  , "    :check 0 >= 0"
  , "    0 >= 0 is VALID"
  , ""
  , "12. Check if predicate may be false:"
  , "    :check x > 0"
  , "    x > 0 is NOT VALID (may be false)"
  , ""
  , "13. Tautology:"
  , "    :check x > 0 || x <= 0"
  , "    x > 0 || x <= 0 is VALID"
  , ""
  , "--- Practical Examples ---"
  , ""
  , "14. Safe array access (conceptual):"
  , "    -- type BoundedArray n = { arr : Array a, len : {l : Nat | l == n} }"
  , "    -- get : (n : Nat) -> BoundedArray n -> {i : Nat | i < n} -> a"
  , ""
  , "15. Non-empty list head:"
  , "    -- type NonEmpty a = {xs : List a | length xs > 0}"
  , "    -- head : NonEmpty a -> a  -- Always safe!"
  , ""
  , "16. Sorted list:"
  , "    -- type Sorted = {xs : List Nat | isSorted xs}"
  , "    -- merge : Sorted -> Sorted -> Sorted"
  , ""
  , "==========================================="
  , "Key Concepts"
  , "==========================================="
  , ""
  , "REFINEMENT TYPE {x : T | p}:"
  , "  - Base type T with predicate p"
  , "  - Values must satisfy p"
  , "  - Compile-time verification"
  , ""
  , "SUBTYPING:"
  , "  - {x : T | p1} <: {x : T | p2}  iff  p1 => p2"
  , "  - More refined = more specific = subtype"
  , ""
  , "DEPENDENT FUNCTIONS (x : T1) -> T2:"
  , "  - Return type T2 can mention parameter x"
  , "  - Enables precise specifications"
  , ""
  , "VALIDITY CHECKING:"
  , "  - SMT-based (in real systems)"
  , "  - Decidable for linear arithmetic"
  , "  - This REPL uses simple decision procedure"
  , ""
  , "==========================================="
  , "Real-World Systems"
  , "==========================================="
  , ""
  , "• Liquid Haskell - Refinement types for Haskell"
  , "• F* - Verification-oriented ML"
  , "• Dafny - Verified programming"
  , "• Ada SPARK - Safety-critical systems"
  , "• Rust (lifetimes) - Memory safety"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Create a refined type:"
  , "   :type \\x : {n : Nat | n > 0}. pred x"
  , ""
  , "2. Check subtyping:"
  , "   :subtype {x : Nat | x > 10} and {x : Nat | x > 0}"
  , ""
  , "3. Validate a predicate:"
  , "   :check x + 1 > x"
  ]
