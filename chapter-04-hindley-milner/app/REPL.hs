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
import qualified Data.Set as Set
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
  , inferMode :: Bool                -- Automatically infer types
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
  , inferMode = True
  , maxSteps = 1000
  }

-- | Run the REPL
runREPL :: IO ()
runREPL = do
  putStrLn "╔═══════════════════════════════════════════════════════════╗"
  putStrLn "║  Hindley-Milner Type Inference REPL                        ║"
  putStrLn "║  Chapter 4: Type Systems Course                           ║"
  putStrLn "╚═══════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "✨ Automatic type inference - no type annotations needed! ✨"
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

  ["infer"] -> do
    putStrLn "Type inference enabled"
    loop state { inferMode = True }

  ["noinfer"] -> do
    putStrLn "Type inference disabled"
    loop state { inferMode = False }

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
      case infer term' of
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

      -- Infer type if enabled
      when (inferMode state) $ do
        case infer term' of
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
            when (showTypes st && inferMode st) $ showTermType t' st
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
      when (showTypes state && inferMode state) $ showTermType result state
  loop state

-- | Generate all evaluation steps
generateEvalSteps :: Term -> [Term]
generateEvalSteps t = t : case step t of
  Nothing -> []
  Just t' -> generateEvalSteps t'

-- | Show the type of a term
showTermType :: Term -> REPLState -> IO ()
showTermType term _state = do
  case infer term of
    Left _ -> return ()
    Right ty -> putStrLn $ "  : " ++ prettyType ty

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

freeTyVarsScheme :: TypeScheme -> Set.Set TyVar
freeTyVarsScheme (TypeScheme vars ty) =
  freeTyVars ty Set.\\ Set.fromList vars

freeTyVarsEnv :: Map String TypeScheme -> Set.Set TyVar
freeTyVarsEnv env =
  Set.unions (map freeTyVarsScheme (Map.elems env))

generalizeEnv :: Map String TypeScheme -> Type -> TypeScheme
generalizeEnv env ty =
  let vars = Set.toList (freeTyVars ty Set.\\ freeTyVarsEnv env)
  in TypeScheme vars ty

-- | Pretty print type errors
prettyTypeError :: TypeError -> String
prettyTypeError (UnboundVariable x) =
  "Unbound variable: " ++ x
prettyTypeError (UnificationFail t1 t2) =
  "Cannot unify types: " ++ prettyType t1 ++ " and " ++ prettyType t2
prettyTypeError (OccursCheck a t) =
  "Occurs check failed: " ++ a ++ " occurs in " ++ prettyType t
prettyTypeError (TypeMismatch t1 t2) =
  "Type mismatch: " ++ prettyType t1 ++ " ≠ " ++ prettyType t2

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
          putStrLn $ "Type error: " ++ prettyTypeError err
          loop state
        Right ty -> do
          let scheme = generalizeEnv (typeBindings state) ty
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
            let scheme = generalizeEnv (typeBindings st) ty
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
  , "  :infer                  Enable automatic type inference (default)"
  , "  :noinfer                Disable automatic type inference"
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
  , "  • No type annotations needed - types are inferred!"
  , "  • Let-polymorphism: let-bound variables can be used at different types"
  , "  • Unification algorithm finds most general types"
  ]

-- | Show example terms
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "Example terms with automatic type inference:"
  , ""
  , "=== Identity Function ==="
  , "  \\x. x"
  , "  Type inferred: t0 -> t0 (polymorphic!)"
  , ""
  , "=== Constant Function ==="
  , "  \\x. \\y. x"
  , "  Type inferred: t0 -> t1 -> t0"
  , ""
  , "=== Compose ==="
  , "  \\f. \\g. \\x. f (g x)"
  , "  Type inferred: (t0 -> t1) -> (t2 -> t0) -> t2 -> t1"
  , ""
  , "=== Let-Polymorphism ==="
  , "  let id = \\x. x in (id 0, id true)"
  , "  Type inferred: Nat * Bool"
  , "  Note: id is used at BOTH Nat -> Nat AND Bool -> Bool!"
  , ""
  , "Compare with:"
  , "  (\\id. (id 0, id true)) (\\x. x)"
  , "  Type error! Cannot unify Nat and Bool"
  , "  (id would need a single monomorphic type)"
  , ""
  , "=== Higher-Order Functions ==="
  , "  :let twice = \\f. \\x. f (f x)"
  , "  twice : (t0 -> t0) -> t0 -> t0"
  , ""
  , "  :let compose = \\f. \\g. \\x. f (g x)"
  , "  compose : (t1 -> t2) -> (t0 -> t1) -> t0 -> t2"
  , ""
  , "=== Lists ==="
  , "  []"
  , "  Type inferred: List t0 (polymorphic empty list!)"
  , ""
  , "  0 :: []"
  , "  Type inferred: List Nat"
  , ""
  , "  :let map = \\f. \\l. if isnil l then [] else f (head l) :: map f (tail l)"
  , "  map : (t0 -> t1) -> List t0 -> List t1"
  , ""
  , "=== Pairs ==="
  , "  :let swap = \\p. (snd p, fst p)"
  , "  swap : (t0 * t1) -> (t1 * t0)"
  , ""
  , "  :let fst' = \\p. fst p"
  , "  fst' : (t0 * t1) -> t0"
  , ""
  , "=== Type Inference Examples ==="
  , "  :type \\x. succ x"
  , "  Nat -> Nat"
  , ""
  , "  :type \\x. \\y. if x then y else 0"
  , "  Bool -> Nat -> Nat"
  , ""
  , "  :type \\f. \\x. \\y. f x y"
  , "  (t0 -> t1 -> t2) -> t0 -> t1 -> t2"
  , ""
  , "=== Common Errors ==="
  , "  (\\x. x x) (\\x. x)"
  , "  Type error: Occurs check (infinite type!)"
  , ""
  , "  if 0 then true else false"
  , "  Type error: Cannot unify Nat and Bool"
  , ""
  , "=== Recursive Functions (not built-in) ==="
  , "  :let length = \\l. if isnil l then 0 else succ (length (tail l))"
  , "  Note: This requires a fixpoint operator or let-rec (not in this chapter)."
  , ""
  , "Try these to explore type inference:"
  , "  :type \\x. x"
  , "  :type \\f. \\g. \\x. f (g x)"
  , "  :type let id = \\x. x in id"
  , "  :type (\\x. x, \\y. succ y)"
  ]
