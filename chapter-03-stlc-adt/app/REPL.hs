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
  putStrLn "║  STLC with Algebraic Data Types REPL                      ║"
  putStrLn "║  Chapter 3: Type Systems Course                           ║"
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
      let steps = take (maxSteps state) $ generateEvalSteps term
      mapM_ (\t -> putStrLn $ "  " ++ pretty t) steps
      when (length steps >= maxSteps state) $
        putStrLn "  (stopped: max steps reached)"
    else do
      let result = eval term
      putStrLn $ "  " ++ pretty result
      when (showTypes state) $ showTermType result state
  loop state

-- | Generate all evaluation steps
generateEvalSteps :: Term -> [Term]
generateEvalSteps t = t : case step t of
  Nothing -> []
  Just t' -> generateEvalSteps t'

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
    go (TmPair t1 t2) = TmPair (go t1) (go t2)
    go (TmFst t) = TmFst (go t)
    go (TmSnd t) = TmSnd (go t)
    go (TmInl ty t) = TmInl ty (go t)
    go (TmInr ty t) = TmInr ty (go t)
    go (TmCase t x1 t1 x2 t2) = TmCase (go t) x1 (go t1) x2 (go t2)
    go (TmRecord fields) = TmRecord (Map.map go fields)
    go (TmProj t l) = TmProj (go t) l
    go (TmTag l t ty) = TmTag l (go t) ty
    go (TmCaseVariant t cases) = TmCaseVariant (go t) [(l, x, go ti) | (l, x, ti) <- cases]
    go (TmCons t1 t2) = TmCons (go t1) (go t2)
    go (TmIsNil t) = TmIsNil (go t)
    go (TmHead t) = TmHead (go t)
    go (TmTail t) = TmTail (go t)
    go (TmMatch t cases) = TmMatch (go t) [(p, go ti) | (p, ti) <- cases]
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
prettyTypeError (NotAProduct ty) =
  "Expected product type but got: " ++ prettyType ty
prettyTypeError (NotASum ty) =
  "Expected sum type but got: " ++ prettyType ty
prettyTypeError (NotARecord ty) =
  "Expected record type but got: " ++ prettyType ty
prettyTypeError (NotAList ty) =
  "Expected list type but got: " ++ prettyType ty
prettyTypeError (FieldNotFound l) =
  "Field not found: " ++ l
prettyTypeError (VariantLabelNotFound l) =
  "Variant label not found: " ++ l
prettyTypeError (PatternTypeMismatch pat ty) =
  "Pattern " ++ prettyPattern pat ++ " doesn't match type " ++ prettyType ty
prettyTypeError NonExhaustivePatterns =
  "Non-exhaustive pattern match"
prettyTypeError (DuplicateLabel l) =
  "Duplicate label: " ++ l
prettyTypeError (DuplicatePatternVar x) =
  "Duplicate pattern variable: " ++ x

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
  , "  \\x:T. body              Lambda abstraction"
  , "  f x                     Application"
  , "  true, false             Booleans"
  , "  if t then t else t      Conditional"
  , "  0, succ t, pred t       Natural numbers"
  , "  ()                      Unit value"
  , "  (t1, t2)                Pair"
  , "  fst t, snd t            Projections"
  , "  inl[T] t, inr[T] t      Sum injections"
  , "  case t of ...           Case analysis"
  , "  {l1=t1, l2=t2}          Record"
  , "  t.label                 Record projection"
  , "  <l=t> as T              Variant"
  , "  []:T                    Empty list"
  , "  t::ts                   List cons"
  , "  head t, tail t, isnil t List operations"
  , "  match t with ...        Pattern matching"
  , ""
  , "Type syntax:"
  , "  Bool, Nat, Unit         Base types"
  , "  T1 -> T2                Function type"
  , "  T1 * T2                 Product type"
  , "  T1 + T2                 Sum type"
  , "  {l1:T1, l2:T2}          Record type"
  , "  <l1:T1, l2:T2>          Variant type"
  , "  List T                  List type"
  ]

-- | Show example terms
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "Example terms with ADTs:"
  , ""
  , "=== Product Types (Pairs) ==="
  , "  (true, 0)"
  , "  (\\x:Bool. x, \\y:Nat. succ y)"
  , "  fst (true, false)"
  , "  snd (0, succ 0)"
  , ""
  , "  :let swap = \\p:Bool*Nat. (snd p, fst p)"
  , "  swap (true, 0)"
  , ""
  , "=== Sum Types ==="
  , "  inl[Nat] true"
  , "  inr[Bool] 0"
  , "  case inl[Nat] true of inl x => x | inr y => false"
  , ""
  , "  :let fromOption = \\x:Bool+Unit. case x of inl v => v | inr _ => false"
  , "  fromOption (inl[Unit] true)"
  , ""
  , "=== Records ==="
  , "  {name=true, age=0}"
  , "  {x=0, y=succ 0}.x"
  , ""
  , "  :let point = {x=0, y=0}"
  , "  point.x"
  , ""
  , "  :let getX = \\p:{x:Nat, y:Nat}. p.x"
  , "  getX {x=succ 0, y=0}"
  , ""
  , "=== Variants ==="
  , "  <some=5> as <some:Nat, none:Unit>"
  , "  <none=()> as <some:Nat, none:Unit>"
  , ""
  , "  :let fromMaybe = \\x:<some:Nat, none:Unit>. case x of <some=n> => n | <none=_> => 0"
  , "  fromMaybe (<some=5> as <some:Nat, none:Unit>)"
  , ""
  , "=== Lists ==="
  , "  []:Nat"
  , "  0::[]:Nat"
  , "  0::succ 0::[]:Nat"
  , "  head (0::[]:Nat)"
  , "  tail (0::succ 0::[]:Nat)"
  , "  isnil ([]:Nat)"
  , ""
  , "  :let length = \\l:List Nat. match l with [] => 0 | h::t => succ (length t)"
  , ""
  , "=== Pattern Matching ==="
  , "  match (true, 0) with (x, y) => x"
  , "  match (0, succ 0) with (0, y) => y | (x, _) => x"
  , ""
  , "=== Complex Examples ==="
  , "  :let map = \\f:Nat->Nat. \\l:List Nat. match l with [] => []:Nat | h::t => f h::map f t"
  , ""
  , "  :let filter = \\p:Nat->Bool. \\l:List Nat. match l with [] => []:Nat | h::t => if p h then h::filter p t else filter p t"
  , ""
  , "  :let foldr = \\f:Nat->Nat->Nat. \\z:Nat. \\l:List Nat. match l with [] => z | h::t => f h (foldr f z t)"
  , ""
  , "Type queries:"
  , "  :type (true, 0)"
  , "  :type \\p:Bool*Nat. fst p"
  , "  :type {x=0, y=0}"
  , "  :type <some=0> as <some:Nat, none:Unit>"
  , ""
  , "Try these to see type errors:"
  , "  fst true                        [Not a product type]"
  , "  {x=0}.y                         [Field not found]"
  , "  inl[Nat] 0                     [Type mismatch - inl expects first component]"
  ]
