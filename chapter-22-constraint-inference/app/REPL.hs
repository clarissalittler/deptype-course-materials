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
import Infer
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Text as T
import Data.Text (Text)
import System.IO (hFlush, stdout)
import Control.Monad (when, unless)
import Control.Exception (IOException)
import qualified Control.Exception

-- | REPL state tracks bindings and settings
data REPLState = REPLState
  { termBindings :: Map String Term
  , typeBindings :: Map String TypeScheme
  , stepMode :: Bool
  , showSteps :: Bool
  , showTypes :: Bool
  , showConstraints :: Bool          -- Show generated constraints
  , showSolving :: Bool              -- Show solving steps
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
  , showConstraints = False
  , showSolving = False
  , maxSteps = 1000
  }

-- | Run the REPL
runREPL :: IO ()
runREPL = do
  putStrLn "╔═══════════════════════════════════════════════════════════╗"
  putStrLn "║  Constraint-Based Type Inference REPL                     ║"
  putStrLn "║  Chapter 22: Type Systems Course                          ║"
  putStrLn "╚═══════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "✨ Two-phase type inference: Constraints + Unification! ✨"
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

  ["constraints"] -> do
    putStrLn "Constraint display enabled"
    loop state { showConstraints = True }

  ["noconstraints"] -> do
    putStrLn "Constraint display disabled"
    loop state { showConstraints = False }

  ["solving"] -> do
    putStrLn "Solving steps display enabled"
    loop state { showSolving = True }

  ["nosolving"] -> do
    putStrLn "Solving steps display disabled"
    loop state { showSolving = False }

  words' | "type" : rest <- words', not (null rest) ->
    handleTypeQuery (T.unwords rest) state

  words' | "constraints" : rest <- words', not (null rest) ->
    handleConstraintsQuery (T.unwords rest) state

  words' | "solve" : rest <- words', not (null rest) ->
    handleSolveQuery (T.unwords rest) state

  words' | "unify" : ty1str : ty2str : _ <- words' ->
    handleUnifyQuery ty1str ty2str state

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
      case infer term' of
        Left err -> do
          putStrLn $ "Inference error: " ++ showInferenceError err
          loop state
        Right ty -> do
          putStrLn $ "  " ++ pretty term' ++ " : " ++ prettyType ty
          loop state

-- | Handle constraints query (show constraints without solving)
handleConstraintsQuery :: Text -> REPLState -> IO ()
handleConstraintsQuery input state = do
  case parseTerm input of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (termBindings state) term
      case generateConstraints term' of
        Left err -> do
          putStrLn $ "Error: " ++ show err
          loop state
        Right (constraints, ty) -> do
          putStrLn "Generated constraints:"
          if null constraints
            then putStrLn "  (no constraints)"
            else putStr $ prettyConstraints constraints
          putStrLn $ "Inferred type (before solving): " ++ prettyType ty
          loop state

-- | Handle solve query (show solving process)
handleSolveQuery :: Text -> REPLState -> IO ()
handleSolveQuery input state = do
  case parseTerm input of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (termBindings state) term
      case inferType term' of
        Left err -> do
          putStrLn $ "Inference error: " ++ showInferenceError err
          loop state
        Right (constraints, subst, ty) -> do
          putStrLn "Generated constraints:"
          if null constraints
            then putStrLn "  (no constraints)"
            else putStr $ prettyConstraints constraints
          putStrLn ""
          putStrLn "Solved with substitution:"
          putStrLn $ prettySubst subst
          putStrLn ""
          putStrLn $ "Final type: " ++ prettyType ty
          loop state

-- | Handle unify query (demonstrate unification)
handleUnifyQuery :: Text -> Text -> REPLState -> IO ()
handleUnifyQuery ty1str ty2str state = do
  case (parseType ty1str, parseType ty2str) of
    (Left err, _) -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    (_, Left err) -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    (Right ty1, Right ty2) -> do
      putStrLn $ "Unifying: " ++ prettyType ty1 ++ " ≡ " ++ prettyType ty2
      case unify ty1 ty2 of
        Left err -> do
          putStrLn $ "Unification failed: " ++ show err
          loop state
        Right subst -> do
          putStrLn "Most general unifier:"
          putStrLn $ prettySubst subst
          putStrLn ""
          putStrLn $ "  " ++ prettyType ty1 ++ " [σ] = " ++ prettyType (applySubst subst ty1)
          putStrLn $ "  " ++ prettyType ty2 ++ " [σ] = " ++ prettyType (applySubst subst ty2)
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

      -- Infer type
      case inferType term' of
        Left err -> do
          putStrLn $ "Inference error: " ++ showInferenceError err
          loop state
        Right (constraints, subst, ty) -> do
          -- Show constraints if enabled
          when (showConstraints state) $ do
            putStrLn "Constraints:"
            if null constraints
              then putStrLn "  (no constraints)"
              else putStr $ prettyConstraints constraints

          -- Show solving if enabled
          when (showSolving state) $ do
            putStrLn "Substitution:"
            putStrLn $ prettySubst subst

          -- Show type
          when (showTypes state) $
            putStrLn $ "  : " ++ prettyType ty

          -- Evaluate
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
        "" -> case eval1 t of
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
      let steps = take (maxSteps state) $ generateEvalSteps term
      mapM_ (\t -> putStrLn $ "  " ++ pretty t) steps
      when (length steps >= maxSteps state) $
        putStrLn "  (stopped: max steps reached)"
    else do
      let result = eval term
      putStrLn $ "  " ++ pretty result
  loop state

-- | Generate all evaluation steps
generateEvalSteps :: Term -> [Term]
generateEvalSteps t = t : case eval1 t of
  Nothing -> []
  Just t' -> generateEvalSteps t'

-- | Expand term bindings
expandBindings :: Map String Term -> Term -> Term
expandBindings env = go
  where
    go (Var x) = case Map.lookup x env of
      Just t -> t
      Nothing -> Var x
    go (Lam x t) = Lam x (go t)
    go (App t1 t2) = App (go t1) (go t2)
    go (Let x t1 t2) = Let x (go t1) (go t2)
    go (TmIf t1 t2 t3) = TmIf (go t1) (go t2) (go t3)
    go (TmSucc t) = TmSucc (go t)
    go (TmPred t) = TmPred (go t)
    go (TmIsZero t) = TmIsZero (go t)
    go (TmPair t1 t2) = TmPair (go t1) (go t2)
    go (TmFst t) = TmFst (go t)
    go (TmSnd t) = TmSnd (go t)
    go (TmCons t1 t2) = TmCons (go t1) (go t2)
    go (TmIsNil t) = TmIsNil (go t)
    go (TmHead t) = TmHead (go t)
    go (TmTail t) = TmTail (go t)
    go t = t

-- | Handle let binding
handleLet :: String -> Text -> REPLState -> IO ()
handleLet name termText state = do
  case parseTerm termText of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      loop state
    Right term -> do
      let term' = expandBindings (termBindings state) term

      -- Infer type
      case infer term' of
        Left err -> do
          putStrLn $ "Inference error: " ++ showInferenceError err
          loop state
        Right ty -> do
          -- Generalize to type scheme
          let scheme = TypeScheme [] ty  -- Simple generalization
          putStrLn $ "  " ++ name ++ " : " ++ prettyScheme scheme
          putStrLn $ "  " ++ name ++ " = " ++ pretty term'
          loop state
            { termBindings = Map.insert name term' (termBindings state)
            , typeBindings = Map.insert name scheme (typeBindings state)
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
        Just scheme -> putStrLn $ "  " ++ name ++ " : " ++ prettyScheme scheme ++ " = " ++ pretty term
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
        Right term -> case infer term of
          Right ty ->
            let scheme = TypeScheme [] ty
            in processLines ls st
              { termBindings = Map.insert name term (termBindings st)
              , typeBindings = Map.insert name scheme (typeBindings st)
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
  , "Type inference:"
  , "  :type term              Show the inferred type of a term"
  , "  :types                  Show types during evaluation (default)"
  , "  :notypes                Hide types during evaluation"
  , ""
  , "Constraint-based inference:"
  , "  :constraints term       Show generated constraints"
  , "  :constraints            Enable showing constraints (default: off)"
  , "  :noconstraints          Disable showing constraints"
  , "  :solve term             Show full solving process"
  , "  :solving                Enable showing solving steps (default: off)"
  , "  :nosolving              Disable showing solving steps"
  , "  :unify ty1 ty2          Demonstrate unification"
  , ""
  , "Bindings:"
  , "  :let name = term        Define a binding"
  , "  :load filename          Load bindings from file"
  , "  :save filename          Save bindings to file"
  , ""
  , "Term syntax (NO TYPE ANNOTATIONS!):"
  , "  x                       Variable"
  , "  \\x. body                Lambda abstraction (no type needed!)"
  , "  f x                     Application"
  , "  let x = t1 in t2        Let binding (polymorphic!)"
  , "  true, false             Booleans"
  , "  if t then t else t      Conditional"
  , "  0, succ t, pred t       Natural numbers"
  , "  (t1, t2)                Pair"
  , "  fst t, snd t            Projections"
  , "  [], t::ts               Lists"
  , "  head t, tail t, isnil t List operations"
  , ""
  , "Key Features:"
  , "  • Two-phase inference: constraint generation + solving"
  , "  • More extensible than Algorithm W"
  , "  • No type annotations needed - types are inferred!"
  , "  • Let-polymorphism: let-bound variables can be used at different types"
  ]

-- | Show example terms
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "Example terms demonstrating constraint-based inference:"
  , ""
  , "=== Inspecting Constraints ==="
  , "  :constraints \\x. x"
  , "  Shows: (no constraints) - identity has no restrictions!"
  , ""
  , "  :constraints \\x. succ x"
  , "  Shows: t1 ≡ Nat (parameter must be Nat)"
  , ""
  , "  :constraints \\f. \\x. f x"
  , "  Shows: t1 ≡ t2 -> t3 (f must be a function)"
  , ""
  , "=== Solving Process ==="
  , "  :solve \\x. succ x"
  , "  Shows full constraint generation and solving"
  , ""
  , "  :solve let id = \\x. x in (id 0, id true)"
  , "  Demonstrates let-polymorphism"
  , ""
  , "=== Unification ==="
  , "  :unify (t0 -> t1) (Bool -> t2)"
  , "  Shows: {t0 ↦ Bool, t1 ↦ t2}"
  , ""
  , "  :unify (t0 -> t0) (Bool -> Nat)"
  , "  Fails: Cannot unify Bool with Nat"
  , ""
  , "  :unify t0 (t0 -> Bool)"
  , "  Fails: Occurs check (infinite type)"
  , ""
  , "=== Complex Examples ==="
  , "  :solve \\f. \\g. \\x. f (g x)"
  , "  Compose function - see how constraints flow"
  , ""
  , "  :solve \\x. \\y. if x then y else 0"
  , "  Mixed constraints from if and types"
  , ""
  , "Try enabling constraint display:"
  , "  :constraints"
  , "  \\x. succ x"
  , "  (Shows constraints automatically)"
  ]
