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
  , typeBindings :: Map String (Type, Mult)
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
  putStrLn "Linear Types REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Linear functions (-o), bang types (!),"
  putStrLn "          multiplicities (1/w), usage tracking"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Linear variables must be used exactly once!"
  putStrLn "Type :examples to see comprehensive examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "linear> "
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
  ["env"] -> showEnv state >> return state
  ["reset"] -> putStrLn "Bindings reset." >> return initialState

  ("let" : x : "=" : rest) -> handleLetBinding x (unwords rest) state

  ("type" : rest) -> handleTypeOf (unwords rest) state >> return state

  ("step" : rest) -> handleStep (unwords rest) >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

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
          -- Bindings are unrestricted by default
          return state
            { bindings = Map.insert x v (bindings state)
            , typeBindings = Map.insert x (ty, Many) (typeBindings state)
            }

-- | Handle :type command
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input _state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      case typeCheck t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ prettyType ty

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
      -- Type check
      case typeCheck t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> do
          when (showTypes state) $
            putStrLn $ "  : " ++ prettyType ty

          -- Evaluate
          if showSteps state
            then do
              let steps = generateEvalSteps t (maxSteps state)
              mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ s) (zip [0::Int ..] steps)
            else do
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
      Just (ty, m) -> putStrLn $ "  " ++ x ++ " :" ++ prettyMult m ++ " " ++ prettyType ty ++ " = " ++ prettyTerm v
      Nothing -> putStrLn $ "  " ++ x ++ " = " ++ prettyTerm v

-- | Helper for when
when :: Bool -> IO () -> IO ()
when True action = action
when False _ = return ()

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "Linear Types REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, ()         Base types"
  putStrLn "    A -o B                Linear function (uses A exactly once)"
  putStrLn "    A -> B                Unrestricted function (uses A any times)"
  putStrLn "    A * B                 Pair type (tensor product)"
  putStrLn "    !A                    Bang type (makes A unrestricted)"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                     Variable"
  putStrLn "    \\x :1 T. t            Linear lambda (must use x once)"
  putStrLn "    \\x :w T. t            Unrestricted lambda (use x freely)"
  putStrLn "    t1 t2                 Application"
  putStrLn "    (t1, t2)              Pair"
  putStrLn "    let (x, y) = t1 in t2 Pair elimination"
  putStrLn "    !t                    Bang introduction"
  putStrLn "    let !x = t1 in t2     Bang elimination"
  putStrLn "    let x :1 = t1 in t2   Linear let binding"
  putStrLn "    let x :w = t1 in t2   Unrestricted let binding"
  putStrLn ""
  putStrLn "Key Concepts:"
  putStrLn "  - Linear (1): Must be used exactly once"
  putStrLn "  - Unrestricted (w): Can be used any number of times"
  putStrLn "  - Bang (!): Promotes linear to unrestricted"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Linear Types Examples"
  , "==========================================="
  , ""
  , "--- Linear vs Unrestricted Functions ---"
  , ""
  , "1. Linear identity (uses argument exactly once):"
  , "   \\x :1 Nat. x"
  , "   : Nat -o Nat"
  , ""
  , "2. Unrestricted identity (can use argument freely):"
  , "   \\x :w Nat. x"
  , "   : Nat -> Nat"
  , ""
  , "3. Linear function MUST use its argument:"
  , "   \\x :1 Nat. 0"
  , "   Type error: Linear variable 'x' unused"
  , ""
  , "4. Linear function CANNOT use argument twice:"
  , "   \\x :1 Nat. (x, x)"
  , "   Type error: Linear variable 'x' used twice"
  , ""
  , "--- Pairs (Tensor Product) ---"
  , ""
  , "5. Create a pair:"
  , "   (true, 0)"
  , "   : Bool * Nat"
  , ""
  , "6. Linear pair elimination (must use BOTH components):"
  , "   let (x, y) = (true, 0) in x"
  , "   Type error: Linear variable 'y' unused"
  , ""
  , "7. Correct pair elimination:"
  , "   let (x, y) = (true, succ 0) in if x then y else 0"
  , "   : Nat"
  , "   = 1"
  , ""
  , "--- Bang Types (!) ---"
  , ""
  , "8. Bang wraps a value for unrestricted use:"
  , "   !true"
  , "   : !Bool"
  , ""
  , "9. Bang elimination gives unrestricted access:"
  , "   let !x = !true in (x, x)"
  , "   : Bool * Bool"
  , "   = (true, true)"
  , ""
  , "10. Without bang, duplication fails:"
  , "    \\x :1 Bool. (x, x)"
  , "    Type error: Linear variable 'x' used twice"
  , ""
  , "11. With bang, duplication works:"
  , "    \\x :1 !Bool. let !y = x in (y, y)"
  , "    : !Bool -o Bool * Bool"
  , ""
  , "--- Function Composition ---"
  , ""
  , "12. Linear composition (each function used once):"
  , "    \\f :1 Nat -o Bool. \\g :1 Bool -o Nat. \\x :1 Nat. g (f x)"
  , "    : (Nat -o Bool) -o (Bool -o Nat) -o Nat -o Nat"
  , ""
  , "--- Swap Function ---"
  , ""
  , "13. Linear swap:"
  , "    \\p :1 Nat * Bool. let (x, y) = p in (y, x)"
  , "    : Nat * Bool -o Bool * Nat"
  , ""
  , "--- Discarding with Unrestricted ---"
  , ""
  , "14. Unrestricted values can be discarded:"
  , "    \\x :w Nat. 0"
  , "    : Nat -> Nat"
  , "    (x is not used, which is fine for unrestricted)"
  , ""
  , "15. Unrestricted values can be duplicated:"
  , "    \\x :w Nat. (x, x)"
  , "    : Nat -> Nat * Nat"
  , ""
  , "--- Real-World Analogy ---"
  , ""
  , "16. File handle (linear - must close exactly once):"
  , "    -- open : () -o Handle"
  , "    -- read : Handle -o String * Handle"
  , "    -- close : Handle -o ()"
  , ""
  , "    -- Correct: open, read, close"
  , "    -- Error: open, forget to close (resource leak)"
  , "    -- Error: close twice (use-after-free)"
  , ""
  , "==========================================="
  , "Key Concepts"
  , "==========================================="
  , ""
  , "LINEAR (1):"
  , "  - Must be used exactly once"
  , "  - Cannot be discarded or duplicated"
  , "  - Perfect for resources: files, locks, connections"
  , ""
  , "UNRESTRICTED (w):"
  , "  - Can be used any number of times (0, 1, many)"
  , "  - Traditional functional programming behavior"
  , ""
  , "BANG TYPE (!A):"
  , "  - Wraps a value to make it unrestricted"
  , "  - !A can be used any number of times"
  , "  - let !x = e1 in e2 extracts the value"
  , ""
  , "TENSOR PRODUCT (A * B):"
  , "  - Both components must be used"
  , "  - let (x, y) = p in ... eliminates pairs"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Linear identity:"
  , "   \\x :1 Nat. x"
  , ""
  , "2. Try to violate linearity:"
  , "   \\x :1 Nat. 0"
  , "   (Should fail: x unused)"
  , ""
  , "3. Use bang for duplication:"
  , "   \\x :1 !Nat. let !y = x in (y, y)"
  , ""
  , "4. Linear pair elimination:"
  , "   let (a, b) = (0, true) in (b, a)"
  ]
