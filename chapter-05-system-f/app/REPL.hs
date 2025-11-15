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
  , typeBindings :: Map String Type
  , stepMode :: Bool
  , showSteps :: Bool
  , showTypes :: Bool
  , typeCheckMode :: Bool
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
  putStrLn "║  System F (Explicit Polymorphism) REPL                    ║"
  putStrLn "║  Chapter 5: Type Systems Course                           ║"
  putStrLn "╚═══════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "✨ Explicit polymorphism with ΛA and [T] ✨"
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
      let term' = expandBindings (termBindings state) term
      case typeCheck term' of
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
      let term' = expandBindings (termBindings state) term

      -- Type check if enabled
      when (typeCheckMode state) $ do
        case typeCheck term' of
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
            when (showTypes st && typeCheckMode st) $ showTermType t' st
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
      let steps = take (maxSteps state) $ generateEvalSteps term
      mapM_ (\t -> putStrLn $ "  " ++ pretty t) steps
      when (length steps >= maxSteps state) $
        putStrLn "  (stopped: max steps reached)"
    else do
      let result = eval term
      putStrLn $ "  " ++ pretty result
      when (showTypes state && typeCheckMode state) $ showTermType result state
  loop state

-- | Generate all evaluation steps
generateEvalSteps :: Term -> [Term]
generateEvalSteps t = t : case step t of
  Nothing -> []
  Just t' -> generateEvalSteps t'

-- | Show the type of a term
showTermType :: Term -> REPLState -> IO ()
showTermType term _state = do
  case typeCheck term of
    Left _ -> return ()
    Right ty -> putStrLn $ "  : " ++ prettyType ty

-- | Expand term bindings
expandBindings :: Map String Term -> Term -> Term
expandBindings env = go
  where
    go (Var x) = case Map.lookup x env of
      Just t -> t
      Nothing -> Var x
    go (Lam x ty t) = Lam x ty (go t)
    go (App t1 t2) = App (go t1) (go t2)
    go (TyAbs a t) = TyAbs a (go t)
    go (TyApp t ty) = TyApp (go t) ty
    go (TmIf t1 t2 t3) = TmIf (go t1) (go t2) (go t3)
    go (TmSucc t) = TmSucc (go t)
    go (TmPred t) = TmPred (go t)
    go (TmIsZero t) = TmIsZero (go t)
    go t = t

-- | Pretty print type errors
prettyTypeError :: TypeError -> String
prettyTypeError (UnboundVariable x) =
  "Unbound variable: " ++ x
prettyTypeError (UnboundTypeVariable a) =
  "Unbound type variable: " ++ a
prettyTypeError (TypeMismatch expected actual) =
  "Type mismatch: expected " ++ prettyType expected ++
  " but got " ++ prettyType actual
prettyTypeError (NotAFunction ty) =
  "Not a function type: " ++ prettyType ty
prettyTypeError (ConditionNotBool ty) =
  "Condition must have type Bool, but has type: " ++ prettyType ty
prettyTypeError (NotANat ty) =
  "Expected Nat but got: " ++ prettyType ty
prettyTypeError (NotAForall ty) =
  "Expected universal type (∀A. T) but got: " ++ prettyType ty

-- | Handle let binding
handleLet :: String -> Text -> REPLState -> IO ()
handleLet name termText state = do
  case parseTerm termText of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (termBindings state) term

      -- Type check the term
      case typeCheck term' of
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
        Right term -> case typeCheck term of
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
  , "  \\x:T. body              Lambda abstraction"
  , "  f x                     Application"
  , "  /\\A. body               Type abstraction (ΛA. body)"
  , "  t [T]                   Type application"
  , "  true, false             Booleans"
  , "  if t then t else t      Conditional"
  , "  0, succ t, pred t       Natural numbers"
  , ""
  , "Type syntax:"
  , "  A, B, C                 Type variables (uppercase)"
  , "  Bool, Nat               Base types"
  , "  T1 -> T2                Function type"
  , "  forall A. T             Universal type (∀A. T)"
  , ""
  , "Key Features:"
  , "  • Explicit polymorphism - must use Λ and [T]"
  , "  • Parametric polymorphism - functions uniform across types"
  , "  • Church encodings with types"
  ]

-- | Show example terms
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "Example System F terms:"
  , ""
  , "=== Polymorphic Identity ==="
  , "  /\\A. \\x:A. x"
  , "  Type: ∀A. A -> A"
  , ""
  , "  (/\\A. \\x:A. x) [Bool] true"
  , "  Type: Bool"
  , "  Result: true"
  , ""
  , "=== Polymorphic Constant ==="
  , "  /\\A. /\\B. \\x:A. \\y:B. x"
  , "  Type: ∀A. ∀B. A -> B -> A"
  , ""
  , "=== Self Application ==="
  , "  (/\\A. \\x:A. x) [forall B. B -> B]"
  , "  Type: (∀B. B -> B) -> (∀B. B -> B)"
  , ""
  , "=== Polymorphic Composition ==="
  , "  :let compose = /\\A. /\\B. /\\C. \\f:B->C. \\g:A->B. \\x:A. f (g x)"
  , "  compose : ∀A. ∀B. ∀C. (B -> C) -> (A -> B) -> A -> C"
  , ""
  , "=== Twice Function ==="
  , "  :let twice = /\\A. \\f:A->A. \\x:A. f (f x)"
  , "  twice : ∀A. (A -> A) -> A -> A"
  , ""
  , "  twice [Nat] (\\x:Nat. succ x) 0"
  , "  Result: succ (succ 0)"
  , ""
  , "=== Church Booleans (Typed) ==="
  , "  :let CBool = forall A. A -> A -> A"
  , ""
  , "  :let ctrue = /\\A. \\t:A. \\f:A. t"
  , "  ctrue : ∀A. A -> A -> A"
  , ""
  , "  :let cfalse = /\\A. \\t:A. \\f:A. f"
  , "  cfalse : ∀A. A -> A -> A"
  , ""
  , "  :let cif = /\\A. \\b:CBool. \\t:A. \\f:A. b [A] t f"
  , "  cif : ∀A. (∀B. B -> B -> B) -> A -> A -> A"
  , ""
  , "  cif [Bool] ctrue true false"
  , "  Result: true"
  , ""
  , "=== Church Numerals (Typed) ==="
  , "  :let CNat = forall A. (A -> A) -> A -> A"
  , ""
  , "  :let czero = /\\A. \\f:A->A. \\x:A. x"
  , "  czero : ∀A. (A -> A) -> A -> A"
  , ""
  , "  :let cone = /\\A. \\f:A->A. \\x:A. f x"
  , "  cone : ∀A. (A -> A) -> A -> A"
  , ""
  , "  :let csucc = \\n:CNat. /\\A. \\f:A->A. \\x:A. f (n [A] f x)"
  , "  csucc : CNat -> CNat"
  , ""
  , "  :let cnat2nat = \\n:CNat. n [Nat] (\\x:Nat. succ x) 0"
  , "  cnat2nat : CNat -> Nat"
  , ""
  , "  cnat2nat (csucc cone)"
  , "  Result: succ (succ 0)"
  , ""
  , "=== Church Pairs (Typed) ==="
  , "  :let CPair = /\\A. /\\B. forall C. (A -> B -> C) -> C"
  , ""
  , "  :let cpair = /\\A. /\\B. \\x:A. \\y:B. /\\C. \\f:A->B->C. f x y"
  , "  cpair : ∀A. ∀B. A -> B -> (∀C. (A -> B -> C) -> C)"
  , ""
  , "  :let cfst = /\\A. /\\B. \\p:CPair A B. p [A] (\\x:A. \\y:B. x)"
  , "  cfst : ∀A. ∀B. CPair A B -> A"
  , ""
  , "  :let csnd = /\\A. /\\B. \\p:CPair A B. p [B] (\\x:A. \\y:B. y)"
  , "  csnd : ∀A. ∀B. CPair A B -> B"
  , ""
  , "=== Church Lists (Typed) ==="
  , "  :let CList = /\\A. forall B. B -> (A -> B -> B) -> B"
  , ""
  , "  :let cnil = /\\A. /\\B. \\n:B. \\c:A->B->B. n"
  , "  cnil : ∀A. (∀B. B -> (A -> B -> B) -> B)"
  , ""
  , "  :let ccons = /\\A. \\h:A. \\t:CList A. /\\B. \\n:B. \\c:A->B->B. c h (t [B] n c)"
  , "  ccons : ∀A. A -> CList A -> CList A"
  , ""
  , "=== Parametricity Examples ==="
  , "  # Any function of type ∀A. A -> A MUST be identity!"
  , "  /\\A. \\x:A. x"
  , ""
  , "  # Any function of type ∀A. ∀B. A -> B -> A MUST be constant!"
  , "  /\\A. /\\B. \\x:A. \\y:B. x"
  , ""
  , "Type queries:"
  , "  :type /\\A. \\x:A. x"
  , "  :type /\\A. /\\B. /\\C. \\f:B->C. \\g:A->B. \\x:A. f (g x)"
  , "  :type /\\A. \\f:A->A. \\x:A. f (f x)"
  , ""
  , "Try these to see type errors:"
  , "  (/\\A. \\x:A. x) true          [Missing type application!]"
  , "  (/\\A. \\x:A. x) [Bool]        [Missing term argument]"
  , "  (\\x:Bool. x) [Nat]            [Not a universal type]"
  ]
