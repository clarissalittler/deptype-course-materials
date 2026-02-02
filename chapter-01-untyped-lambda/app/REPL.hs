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
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as T
import Data.Text (Text)
import System.IO (hFlush, stdout)
import Control.Monad (when, unless)
import Control.Exception (IOException, catch)

-- | REPL state tracks bindings and settings
data REPLState = REPLState
  { bindings :: Map String Term
  , stepMode :: Bool           -- Step-by-step evaluation mode
  , showSteps :: Bool          -- Show all evaluation steps
  , maxSteps :: Int            -- Maximum evaluation steps
  , evalStrategy :: EvalStrategy
  }

data EvalStrategy = Normal | CallByValue | CallByName
  deriving (Show, Eq)

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { bindings = Map.empty
  , stepMode = False
  , showSteps = False
  , maxSteps = 1000
  , evalStrategy = CallByValue
  }

-- | Run the REPL
runREPL :: IO ()
runREPL = do
  putStrLn "╔═══════════════════════════════════════════════════════════╗"
  putStrLn "║  Untyped Lambda Calculus REPL                             ║"
  putStrLn "║  Chapter 1: Type Systems Course                           ║"
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

  ["clear"] -> loop initialState { evalStrategy = evalStrategy state }
  ["c"] -> loop initialState { evalStrategy = evalStrategy state }

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

  ["strategy", "normal"] -> do
    putStrLn "Evaluation strategy: Normal order"
    loop state { evalStrategy = Normal }

  ["strategy", "cbv"] -> do
    putStrLn "Evaluation strategy: Call-by-value"
    loop state { evalStrategy = CallByValue }

  ["strategy", "cbn"] -> do
    putStrLn "Evaluation strategy: Call-by-name"
    loop state { evalStrategy = CallByName }

  words' | "let" : name : "=" : rest <- words', not (null rest) ->
    handleLet (T.unpack name) (T.unwords rest) state

  ["load", filename] -> handleLoad (T.unpack filename) state
  ["save", filename] -> handleSave (T.unpack filename) state

  _ -> do
    putStrLn $ "Unknown command: :" ++ T.unpack cmd
    putStrLn "Type ':help' for available commands"
    loop state

-- | Handle term evaluation
handleTerm :: Text -> REPLState -> IO ()
handleTerm input state = do
  case parseTermEither input of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (bindings state) term
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
        "" -> case evalStep st t of
          Nothing -> do
            putStrLn "  (normal form)"
            loop st
          Just t' -> do
            putStrLn $ "→ " ++ pretty t'
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
      let steps = normalizeStepsWith (maxSteps state) (evalStep state) term
      mapM_ (\t -> putStrLn $ "  " ++ pretty t) steps
      when (length steps >= maxSteps state) $
        putStrLn "  (stopped: max steps reached)"
    else do
      let result = evalWith (evalStrategy state) (maxSteps state) term
      putStrLn $ "  " ++ pretty result
  loop state

-- | Expand bindings in a term
expandBindings :: Map String Term -> Term -> Term
expandBindings env = go
  where
    go (Var x) = case Map.lookup x env of
      Just t -> t
      Nothing -> Var x
    go (Lam x t) = Lam x (go t)
    go (App t1 t2) = App (go t1) (go t2)

-- | Single evaluation step based on strategy
evalStep :: REPLState -> Term -> Maybe Term
evalStep state = case evalStrategy state of
  Normal -> stepNormal
  CallByValue -> stepCallByValue
  CallByName -> stepCallByName

-- | Evaluate with strategy
evalWith :: EvalStrategy -> Int -> Term -> Term
evalWith strategy maxStepsLimit term = case strategy of
  Normal -> maybe term id (normalizeWith maxStepsLimit stepNormal term)
  CallByValue -> maybe term id (normalizeWith maxStepsLimit stepCallByValue term)
  CallByName -> maybe term id (normalizeWith maxStepsLimit stepCallByName term)

-- | Handle let binding
handleLet :: String -> Text -> REPLState -> IO ()
handleLet name termText state = do
  case parseTermEither termText of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (bindings state) term
      putStrLn $ "  " ++ name ++ " = " ++ pretty term'
      loop state { bindings = Map.insert name term' (bindings state) }

-- | Show current bindings
showBindings :: REPLState -> IO ()
showBindings state = do
  if Map.null (bindings state)
    then putStrLn "No bindings defined"
    else do
      putStrLn "Current bindings:"
      mapM_ showBinding (Map.toList $ bindings state)
  where
    showBinding (name, term) =
      putStrLn $ "  " ++ name ++ " = " ++ pretty term

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
      putStrLn $ "Loaded " ++ show (Map.size (bindings newState) - Map.size (bindings state)) ++ " bindings"
      loop newState
  where
    try :: IO a -> IO (Either IOException a)
    try action = Control.Exception.catch (Right <$> action) (return . Left)

    processLines :: [String] -> REPLState -> REPLState
    processLines [] st = st
    processLines (l:ls) st = case words l of
      (name:"=":rest) -> case parseTermEither (T.pack $ unwords rest) of
        Right term -> processLines ls st { bindings = Map.insert name term (bindings st) }
        Left _ -> processLines ls st
      _ -> processLines ls st

-- | Save bindings to file
handleSave :: String -> REPLState -> IO ()
handleSave filename state = do
  let contents = unlines [ name ++ " = " ++ pretty term
                         | (name, term) <- Map.toList (bindings state) ]
  result <- try $ writeFile filename contents
  case result of
    Left (e :: IOException) -> do
      putStrLn $ "Error saving file: " ++ show e
      loop state
    Right () -> do
      putStrLn $ "Saved " ++ show (Map.size $ bindings state) ++ " bindings to " ++ filename
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
  , "Evaluation strategies:"
  , "  :strategy normal        Use normal order reduction (default)"
  , "  :strategy cbv           Use call-by-value"
  , "  :strategy cbn           Use call-by-name"
  , ""
  , "Bindings:"
  , "  :let name = term        Define a binding"
  , "  :load filename          Load bindings from file"
  , "  :save filename          Save bindings to file"
  , ""
  , "Term syntax:"
  , "  x                       Variable"
  , "  \\x. body                Lambda abstraction (λx. body)"
  , "  \\x y z. body            Multiple arguments (λx. λy. λz. body)"
  , "  f x                     Application"
  , "  (t)                     Parentheses for grouping"
  ]

-- | Show example terms
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "Example lambda terms:"
  , ""
  , "Identity:"
  , "  \\x. x"
  , ""
  , "Constant:"
  , "  \\x y. x"
  , ""
  , "Application:"
  , "  (\\x. x) (\\y. y)"
  , ""
  , "Church Booleans:"
  , "  :let true = \\t f. t"
  , "  :let false = \\t f. f"
  , "  :let if = \\b t f. b t f"
  , "  if true (\\x. x) (\\y. y)"
  , ""
  , "Church Numerals:"
  , "  :let zero = \\f x. x"
  , "  :let one = \\f x. f x"
  , "  :let two = \\f x. f (f x)"
  , "  :let succ = \\n f x. f (n f x)"
  , "  succ one"
  , ""
  , "Church Pairs:"
  , "  :let pair = \\x y f. f x y"
  , "  :let fst = \\p. p (\\x y. x)"
  , "  :let snd = \\p. p (\\x y. y)"
  , "  fst (pair true false)"
  , ""
  , "Omega combinator (non-terminating):"
  , "  (\\x. x x) (\\x. x x)"
  , ""
  , "Y combinator (fixed-point):"
  , "  \\f. (\\x. f (x x)) (\\x. f (x x))"
  ]
