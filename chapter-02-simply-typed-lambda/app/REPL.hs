{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module REPL
  ( runREPL
  , REPLState(..)
  , initialState
  ) where

import Syntax
import Parser
import Eval
import Pretty
import TypeCheck
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as T
import Data.Text (Text)
import System.IO (hFlush, stdout)
import Control.Monad (when, unless)
import Control.Exception (IOException)
import qualified Control.Exception

-- | REPL state tracks bindings, types, and settings
data REPLState = REPLState
  { termBindings :: Map String Term
  , typeBindings :: Map String Type   -- Track types of bound terms
  , stepMode :: Bool
  , showSteps :: Bool
  , showTypes :: Bool                 -- Show types during evaluation
  , typeCheckMode :: Bool             -- Type check before evaluation
  , maxSteps :: Int
  }

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { termBindings = Map.empty
  , typeBindings = Map.empty
  , stepMode = False
  , showSteps = False
  , showTypes = True
  , typeCheckMode = True
  , maxSteps = 1000
  }

-- | Run the REPL
runREPL :: IO ()
runREPL = do
  putStrLn "╔═══════════════════════════════════════════════════════════╗"
  putStrLn "║  Simply Typed Lambda Calculus REPL                        ║"
  putStrLn "║  Chapter 2: Type Systems Course                           ║"
  putStrLn "╚═══════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "Type ':help' for available commands"
  putStrLn "Type ':examples' to see example terms"
  putStrLn ""
  loop initialState

-- | Main REPL loop
loop :: REPLState -> IO ()
loop state = do
  putStr "λ> "
  hFlush stdout
  input <- getLine
  let inputText = T.strip $ T.pack input

  unless (T.null inputText) $ do
    case T.unpack inputText of
      ':':cmd -> handleCommand (T.pack cmd) state
      _ -> handleTerm inputText state

-- | Handle REPL commands
handleCommand :: Text -> REPLState -> IO ()
handleCommand cmd state = case T.words cmd of
  ["help"] -> showHelp >> loop state
  ["h"] -> showHelp >> loop state
  ["?"] -> showHelp >> loop state

  ["quit"] -> putStrLn "Goodbye!"
  ["q"] -> putStrLn "Goodbye!"
  ["exit"] -> putStrLn "Goodbye!"

  ["examples"] -> showExamples >> loop state
  ["ex"] -> showExamples >> loop state

  ["bindings"] -> showBindings state >> loop state
  ["b"] -> showBindings state >> loop state

  ["clear"] -> loop initialState
  ["c"] -> loop initialState

  ["step"] -> do
    putStrLn "Step mode enabled"
    loop state { stepMode = True }

  ["nostep"] -> do
    putStrLn "Step mode disabled"
    loop state { stepMode = False }

  ["trace"] -> do
    putStrLn "Evaluation trace enabled"
    loop state { showSteps = True }

  ["notrace"] -> do
    putStrLn "Evaluation trace disabled"
    loop state { showSteps = False }

  ["types"] -> do
    putStrLn "Type display enabled"
    loop state { showTypes = True }

  ["notypes"] -> do
    putStrLn "Type display disabled"
    loop state { showTypes = False }

  ["typecheck"] -> do
    putStrLn "Type checking enabled (recommended)"
    loop state { typeCheckMode = True }

  ["notypecheck"] -> do
    putStrLn "Type checking disabled (evaluation may fail!)"
    loop state { typeCheckMode = False }

  words' | "type" : rest <- words', not (null rest) ->
    handleTypeQuery (T.unwords rest) state

  words' | "let" : name : "=" : rest <- words', not (null rest) ->
    handleLet (T.unpack name) (T.unwords rest) state

  ["load", filename] -> handleLoad (T.unpack filename) state
  ["save", filename] -> handleSave (T.unpack filename) state

  _ -> do
    putStrLn $ "Unknown command: :" ++ T.unpack cmd
    putStrLn "Type ':help' for available commands"
    loop state

-- | Handle type queries
handleTypeQuery :: Text -> REPLState -> IO ()
handleTypeQuery input state = do
  case parseTerm input of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (termBindings state) (typeBindings state) term
          ctx = typeBindings state
      case typeOf ctx term' of
        Left err -> do
          putStrLn $ "Type error: " ++ prettyTypeError err
          loop state
        Right ty -> do
          putStrLn $ "  " ++ pretty term' ++ " : " ++ prettyType ty
          loop state

-- | Handle term evaluation
handleTerm :: Text -> REPLState -> IO ()
handleTerm input state = do
  case parseTerm input of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (termBindings state) (typeBindings state) term
          ctx = typeBindings state

      -- Type check if enabled
      when (typeCheckMode state) $ do
        case typeOf ctx term' of
          Left err -> do
            putStrLn $ "Type error: " ++ prettyTypeError err
            loop state
            return ()
          Right ty -> do
            when (showTypes state) $
              putStrLn $ "  : " ++ prettyType ty

      if stepMode state
        then handleStepMode term' state
        else handleEvalMode term' state

-- | Handle evaluation in step mode
handleStepMode :: Term -> REPLState -> IO ()
handleStepMode term state = do
  putStrLn $ "  " ++ pretty term
  stepLoop term state
  where
    stepLoop t st = do
      putStr "    "
      hFlush stdout
      c <- getLine
      case c of
        "" -> case step t of
          Nothing -> do
            putStrLn "  (normal form)"
            loop st
          Just t' -> do
            putStrLn $ "→ " ++ pretty t'
            when (showTypes st) $ showTermType t' st
            stepLoop t' st
        ":quit" -> loop st
        ":q" -> loop st
        _ -> do
          putStrLn "Press Enter to step, :quit to exit step mode"
          stepLoop t st

-- | Handle evaluation in normal mode
handleEvalMode :: Term -> REPLState -> IO ()
handleEvalMode term state = do
  if showSteps state
    then do
      let steps = take (maxSteps state) $ evalSteps term
      mapM_ (\t -> putStrLn $ "  " ++ pretty t) steps
      when (length steps >= maxSteps state) $
        putStrLn "  (stopped: max steps reached)"
    else do
      let result = eval term
      putStrLn $ "  " ++ pretty result
      when (showTypes state) $ showTermType result state
  loop state

-- | Show the type of a term
showTermType :: Term -> REPLState -> IO ()
showTermType term state = do
  let ctx = typeBindings state
  case typeOf ctx term of
    Left _ -> return ()
    Right ty -> putStrLn $ "  : " ++ prettyType ty

-- | Expand term bindings
expandBindings :: Map String Term -> Map String Type -> Term -> Term
expandBindings termEnv _typeEnv = go
  where
    go (Var x) = case Map.lookup x termEnv of
      Just t -> t
      Nothing -> Var x
    go (Lam x ty t) = Lam x ty (go t)
    go (App t1 t2) = App (go t1) (go t2)
    go (TmIf t1 t2 t3) = TmIf (go t1) (go t2) (go t3)
    go (TmSucc t) = TmSucc (go t)
    go (TmPred t) = TmPred (go t)
    go (TmIsZero t) = TmIsZero (go t)
    go t = t

-- | Pretty print type errors
prettyTypeError :: TypeError -> String
prettyTypeError (UnboundVariable x) =
  "Unbound variable: " ++ x
prettyTypeError (TypeMismatch expected actual) =
  "Type mismatch: expected " ++ prettyType expected ++
  " but got " ++ prettyType actual
prettyTypeError (NotAFunction ty) =
  "Not a function type: " ++ prettyType ty
prettyTypeError (ConditionNotBool ty) =
  "Condition must have type Bool, but has type: " ++ prettyType ty
prettyTypeError (ArgumentTypeMismatch paramTy argTy) =
  "Argument type mismatch: expected " ++ prettyType paramTy ++
  " but got " ++ prettyType argTy
prettyTypeError (NotANat ty) =
  "Expected Nat but got: " ++ prettyType ty

-- | Handle let binding
handleLet :: String -> Text -> REPLState -> IO ()
handleLet name termText state = do
  case parseTerm termText of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (termBindings state) (typeBindings state) term
          ctx = typeBindings state

      -- Type check the term
      case typeOf ctx term' of
        Left err -> do
          putStrLn $ "Type error: " ++ prettyTypeError err
          loop state
        Right ty -> do
          putStrLn $ "  " ++ name ++ " : " ++ prettyType ty
          putStrLn $ "  " ++ name ++ " = " ++ pretty term'
          loop state
            { termBindings = Map.insert name term' (termBindings state)
            , typeBindings = Map.insert name ty (typeBindings state)
            }

-- | Show current bindings
showBindings :: REPLState -> IO ()
showBindings state = do
  if Map.null (termBindings state)
    then putStrLn "No bindings defined"
    else do
      putStrLn "Current bindings:"
      mapM_ showBinding (Map.toList $ termBindings state)
  where
    showBinding (name, term) =
      case Map.lookup name (typeBindings state) of
        Just ty -> putStrLn $ "  " ++ name ++ " : " ++ prettyType ty ++ " = " ++ pretty term
        Nothing -> putStrLn $ "  " ++ name ++ " = " ++ pretty term

-- | Load bindings from file
handleLoad :: String -> REPLState -> IO ()
handleLoad filename state = do
  result <- try $ readFile filename
  case result of
    Left (e :: IOException) -> do
      putStrLn $ "Error loading file: " ++ show e
      loop state
    Right contents -> do
      let newState = processLines (lines contents) state
      putStrLn $ "Loaded " ++ show (Map.size (termBindings newState) - Map.size (termBindings state)) ++ " bindings"
      loop newState
  where
    try :: IO a -> IO (Either IOException a)
    try action = Control.Exception.catch (Right <$> action) (return . Left)

    processLines :: [String] -> REPLState -> REPLState
    processLines [] st = st
    processLines (l:ls) st = case words l of
      (name:"=":rest) -> case parseTerm (T.pack $ unwords rest) of
        Right term ->
          let ctx = typeBindings st
          in case typeOf ctx term of
            Right ty -> processLines ls st
              { termBindings = Map.insert name term (termBindings st)
              , typeBindings = Map.insert name ty (typeBindings st)
              }
            Left _ -> processLines ls st
        Left _ -> processLines ls st
      _ -> processLines ls st

-- | Save bindings to file
handleSave :: String -> REPLState -> IO ()
handleSave filename state = do
  let contents = unlines [ name ++ " = " ++ pretty term
                         | (name, term) <- Map.toList (termBindings state) ]
  result <- try $ writeFile filename contents
  case result of
    Left (e :: IOException) -> do
      putStrLn $ "Error saving file: " ++ show e
      loop state
    Right () -> do
      putStrLn $ "Saved " ++ show (Map.size $ termBindings state) ++ " bindings to " ++ filename
      loop state
  where
    try :: IO a -> IO (Either IOException a)
    try action = Control.Exception.catch (Right <$> action) (return . Left)

-- | Show help message
showHelp :: IO ()
showHelp = putStrLn $ unlines
  [ "Available commands:"
  , ""
  , "  :help, :h, :?           Show this help message"
  , "  :quit, :q, :exit        Exit the REPL"
  , "  :examples, :ex          Show example terms"
  , "  :bindings, :b           Show current bindings"
  , "  :clear, :c              Clear all bindings"
  , ""
  , "Evaluation modes:"
  , "  :step                   Enable step-by-step evaluation"
  , "  :nostep                 Disable step-by-step evaluation"
  , "  :trace                  Show all evaluation steps"
  , "  :notrace                Hide evaluation steps"
  , ""
  , "Type checking:"
  , "  :type term              Show the type of a term"
  , "  :types                  Show types during evaluation (default)"
  , "  :notypes                Hide types during evaluation"
  , "  :typecheck              Enable type checking (default)"
  , "  :notypecheck            Disable type checking (unsafe!)"
  , ""
  , "Bindings:"
  , "  :let name = term        Define a binding"
  , "  :load filename          Load bindings from file"
  , "  :save filename          Save bindings to file"
  , ""
  , "Term syntax:"
  , "  x                       Variable"
  , "  \\x:T. body              Lambda abstraction (λx:T. body)"
  , "  f x                     Application"
  , "  true, false             Booleans"
  , "  if t then t else t      Conditional"
  , "  0                       Zero"
  , "  succ t                  Successor"
  , "  pred t                  Predecessor"
  , "  iszero t                Zero test"
  , ""
  , "Type syntax:"
  , "  Bool                    Boolean type"
  , "  Nat                     Natural number type"
  , "  T -> T                  Function type"
  ]

-- | Show example terms
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "Example typed lambda terms:"
  , ""
  , "Identity function:"
  , "  \\x:Bool. x"
  , "  \\x:Nat. x"
  , ""
  , "Constant function:"
  , "  \\x:Bool. \\y:Bool. x"
  , ""
  , "Application:"
  , "  (\\x:Bool. x) true"
  , "  (\\x:Nat. succ x) 0"
  , ""
  , "Conditionals:"
  , "  if true then 0 else succ 0"
  , "  \\x:Bool. if x then false else true"
  , ""
  , "Natural numbers:"
  , "  succ (succ (succ 0))"
  , "  pred (succ 0)"
  , "  iszero 0"
  , "  iszero (succ 0)"
  , ""
  , "Higher-order functions:"
  , "  :let not = \\x:Bool. if x then false else true"
  , "  :let isZeroFn = \\x:Nat. iszero x"
  , "  :let twice = \\f:Nat->Nat. \\x:Nat. f (f x)"
  , "  twice (\\x:Nat. succ x) 0"
  , ""
  , "Composition:"
  , "  :let compose = \\f:Nat->Nat. \\g:Nat->Nat. \\x:Nat. f (g x)"
  , "  compose (\\x:Nat. succ x) (\\y:Nat. succ y) 0"
  , ""
  , "Type queries:"
  , "  :type \\x:Bool. x"
  , "  :type if true then 0 else succ 0"
  , "  :type \\f:Nat->Nat. \\x:Nat. f x"
  , ""
  , "Type errors (try these to see error messages):"
  , "  (\\x:Bool. x) 0           [Argument type mismatch]"
  , "  if 0 then true else false [Condition not Bool]"
  , "  succ true                  [Expected Nat]"
  ]
