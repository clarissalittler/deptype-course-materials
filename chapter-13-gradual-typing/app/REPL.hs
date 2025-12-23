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
import qualified Data.Text.IO as TIO
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
  putStrLn "Gradual Typing REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Dynamic type (?), consistency,"
  putStrLn "          runtime casts, blame tracking"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :consistent T1 T2  Check if T1 ~ T2"
  putStrLn "  :meet T1 T2        Compute meet (GLB) of T1 and T2"
  putStrLn "  :join T1 T2        Compute join (LUB) of T1 and T2"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :casts t           Show term with explicit casts"
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
  putStr "gradual> "
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

  ("consistent" : rest) -> handleConsistent (unwords rest) >> return state

  ("join" : rest) -> handleJoin (unwords rest) >> return state

  ("meet" : rest) -> handleMeet (unwords rest) >> return state

  ("step" : rest) -> handleStep (unwords rest) >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

  ("casts" : rest) -> handleCasts (unwords rest) state >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn ("Parse error: " ++ show err) >> return state
    Right t -> do
      let ctx = buildContext state
      case infer ctx t of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right ty -> do
          let v = eval t
          putStrLn $ x ++ " : " ++ prettyType ty ++ " = " ++ prettyTerm v
          return state
            { bindings = Map.insert x v (bindings state)
            , typeBindings = Map.insert x ty (typeBindings state)
            }

-- | Handle :type command
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      let ctx = buildContext state
      case infer ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ prettyType ty

-- | Handle :consistent command
handleConsistent :: String -> IO ()
handleConsistent input = do
  case parseTypeArgs (T.pack input) of
    Left err -> putStrLn err
    Right (t1, t2) ->
      if consistent t1 t2
        then putStrLn $ "  " ++ prettyType t1 ++ " ~ " ++ prettyType t2 ++ "  ✓"
        else putStrLn $ "  " ++ prettyType t1 ++ " ~ " ++ prettyType t2 ++ "  ✗"

-- | Handle :join command
handleJoin :: String -> IO ()
handleJoin input = do
  case parseTypeArgs (T.pack input) of
    Left err -> putStrLn err
    Right (t1, t2) ->
      case join t1 t2 of
        Just ty -> putStrLn $ "  " ++ prettyType t1 ++ " ⊔ " ++ prettyType t2 ++ " = " ++ prettyType ty
        Nothing -> putStrLn $ "  No join exists for " ++ prettyType t1 ++ " and " ++ prettyType t2

-- | Handle :meet command
handleMeet :: String -> IO ()
handleMeet input = do
  case parseTypeArgs (T.pack input) of
    Left err -> putStrLn err
    Right (t1, t2) ->
      case meet t1 t2 of
        Just ty -> putStrLn $ "  " ++ prettyType t1 ++ " ⊓ " ++ prettyType t2 ++ " = " ++ prettyType ty
        Nothing -> putStrLn $ "  No meet exists for " ++ prettyType t1 ++ " and " ++ prettyType t2

-- | Handle :casts command
handleCasts :: String -> REPLState -> IO ()
handleCasts input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      let ctx = buildContext state
      case insertCasts ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right t' -> putStrLn $ "  " ++ prettyTerm t'

-- | Parse two types for consistency/join/meet commands
parseTypeArgs :: T.Text -> Either String (Type, Type)
parseTypeArgs input = do
  let stripped = T.strip input
  case findSplit stripped of
    Nothing -> Left "Usage: :consistent Type1 Type2 (use 'and' or ';' to separate)"
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
  -- Try 'and' separator
  | " and " `T.isInfixOf` input =
      let parts = T.splitOn " and " input
      in case parts of
        [t1, t2] -> Just (T.strip t1, T.strip t2)
        _ -> Nothing
  -- Try ';' separator
  | ";" `T.isInfixOf` input =
      let parts = T.splitOn ";" input
      in case parts of
        [t1, t2] -> Just (T.strip t1, T.strip t2)
        _ -> Nothing
  -- Try space for simple types
  | otherwise =
      let ws = T.words input
      in case ws of
        [t1, t2] -> Just (t1, t2)
        -- For arrow types, try splitting at the last space before second type
        _ -> trySplitArrow input

-- | Try to split two arrow types
trySplitArrow :: T.Text -> Maybe (T.Text, T.Text)
trySplitArrow input =
  let arrows = T.count "->" input
  in if arrows >= 2
     then let ws = T.words input
              half = length ws `div` 2
              (p1, p2) = splitAt half ws
          in Just (T.unwords p1, T.unwords p2)
     else Nothing

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
      let ctx = buildContext state

      -- Type check and display type
      case infer ctx t of
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

-- | Build context from bindings
buildContext :: REPLState -> Context
buildContext state = typeBindings state

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
  putStrLn "Gradual Typing REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :consistent T1 T2  Check if T1 ~ T2 (consistency)"
  putStrLn "  :meet T1 T2        Compute meet (GLB) of T1 and T2"
  putStrLn "  :join T1 T2        Compute join (LUB) of T1 and T2"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :casts t           Show term with explicit casts"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit    Base types"
  putStrLn "    ?                  Dynamic type (consistent with everything!)"
  putStrLn "    T1 -> T2           Function type"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                  Variable"
  putStrLn "    \\x:T. t  or  λx:T. t   Lambda abstraction"
  putStrLn "    t1 t2              Application"
  putStrLn "    true, false        Boolean literals"
  putStrLn "    if t1 then t2 else t3  Conditional"
  putStrLn "    0, succ t, pred t  Natural numbers"
  putStrLn "    iszero t           Zero test"
  putStrLn "    ()                 Unit value"
  putStrLn "    let x = t1 in t2   Let binding"
  putStrLn "    t : T              Type ascription"
  putStrLn "    <T1 => T2>^l t     Explicit cast (inserted automatically)"
  putStrLn ""
  putStrLn "Key Concepts:"
  putStrLn "  • Consistency (~): Types are consistent if they could be equal"
  putStrLn "    - ? is consistent with any type"
  putStrLn "    - Bool ~ Bool, Nat ~ Nat, etc."
  putStrLn "    - Bool ~/~ Nat (inconsistent base types)"
  putStrLn "    - T1->T2 ~ S1->S2 if T1~S1 and T2~S2"
  putStrLn ""
  putStrLn "  • Casts: Runtime type conversions"
  putStrLn "    - Inserted automatically where types differ but are consistent"
  putStrLn "    - May fail at runtime (blame!)"
  putStrLn ""
  putStrLn "  • Blame: Runtime type errors tracked by labels"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Gradual Typing Examples"
  , "==========================================="
  , ""
  , "The dynamic type ? is the key to gradual typing!"
  , "It's consistent with any type, allowing you to mix"
  , "typed and untyped code seamlessly."
  , ""
  , "--- Basic Consistency ---"
  , ""
  , "1. Dynamic is consistent with everything:"
  , "   :consistent ? Bool"
  , "   ? ~ Bool  ✓"
  , ""
  , "   :consistent ? Nat"
  , "   ? ~ Nat  ✓"
  , ""
  , "   :consistent ? (Nat -> Bool)"
  , "   ? ~ (Nat -> Bool)  ✓"
  , ""
  , "2. Static types are only consistent with themselves:"
  , "   :consistent Bool Nat"
  , "   Bool ~ Nat  ✗"
  , ""
  , "   :consistent Bool Bool"
  , "   Bool ~ Bool  ✓"
  , ""
  , "--- Dynamic Functions ---"
  , ""
  , "3. A function accepting dynamic can take anything:"
  , "   :let dynId = \\x:?. x"
  , "   dynId : ? -> ?"
  , ""
  , "   dynId 5"
  , "   : ?"
  , "   = 5"
  , ""
  , "   dynId true"
  , "   : ?"
  , "   = true"
  , ""
  , "4. Using dynamic input as a specific type:"
  , "   :let addOne = \\x:?. succ x"
  , "   addOne : ? -> Nat"
  , ""
  , "   addOne 5"
  , "   : Nat"
  , "   = 6"
  , ""
  , "   This works! Runtime cast from ? to Nat succeeds."
  , ""
  , "5. Runtime type errors (blame):"
  , "   :let addOne = \\x:?. succ x"
  , "   addOne true"
  , "   : Nat"
  , "   = blame^... : Nat"
  , ""
  , "   This fails! Can't use Bool as Nat."
  , ""
  , "--- Mixing Static and Dynamic ---"
  , ""
  , "6. Calling static function with dynamic:"
  , "   :let staticSucc = \\x:Nat. succ x"
  , "   staticSucc : Nat -> Nat"
  , ""
  , "   :let dynArg = (5 : ?)"
  , "   staticSucc dynArg"
  , "   : Nat"
  , "   = 6"
  , ""
  , "7. Storing static value as dynamic:"
  , "   :let x = (true : ?)"
  , "   x : ? = true"
  , ""
  , "   :let y = (42 : ?)"
  , "   y : ? = 42"
  , ""
  , "--- Explicit Casts ---"
  , ""
  , "8. See where casts are inserted:"
  , "   :casts \\x:?. succ x"
  , "   λx : ?. succ <? => Nat>^... x"
  , ""
  , "   The cast converts ? to Nat before calling succ."
  , ""
  , "9. Casts for function types:"
  , "   :casts (\\f:?. f true) (\\x:Bool. x)"
  , ""
  , "   Shows casts for both the function and its argument."
  , ""
  , "--- Function Type Consistency ---"
  , ""
  , "10. Function types are consistent if parts are:"
  , "    :consistent (Bool -> Nat) and (Bool -> ?)"
  , "    (Bool -> Nat) ~ (Bool -> ?)  ✓"
  , ""
  , "11. But not if argument types differ statically:"
  , "    :consistent (Bool -> Nat) and (Nat -> Nat)"
  , "    (Bool -> Nat) ~ (Nat -> Nat)  ✗"
  , ""
  , "12. Dynamic in argument position:"
  , "    :consistent (? -> Nat) and (Bool -> Nat)"
  , "    (? -> Nat) ~ (Bool -> Nat)  ✓"
  , ""
  , "--- Meet and Join ---"
  , ""
  , "13. Meet (greatest lower bound):"
  , "    :meet Nat ?"
  , "    Nat ⊓ ? = Nat"
  , ""
  , "    :meet Bool ?"
  , "    Bool ⊓ ? = Bool"
  , ""
  , "14. Join (least upper bound):"
  , "    :join Nat ?"
  , "    Nat ⊔ ? = ?"
  , ""
  , "    :join Bool Nat"
  , "    No join exists"
  , ""
  , "--- Step-by-Step with Casts ---"
  , ""
  , "15. Watch cast evaluation:"
  , "    :steps (\\x:?. succ x) 5"
  , "    Shows how the cast from ? to Nat is checked and removed."
  , ""
  , "16. Cast failure:"
  , "    :steps (\\x:?. succ x) true"
  , "    Shows where blame occurs."
  , ""
  , "--- Practical Examples ---"
  , ""
  , "17. Gradually typing a function:"
  , "    Start with fully dynamic:"
  , "    :let process = \\x:?. x"
  , ""
  , "    Add some types:"
  , "    :let process2 = \\x:?. if x then 1 else 0"
  , "    (assumes x is Bool, returns Nat)"
  , ""
  , "    Fully typed:"
  , "    :let process3 = \\x:Bool. if x then 1 else 0"
  , ""
  , "18. Heterogeneous data with dynamic:"
  , "    :let first = (true : ?)"
  , "    :let second = (42 : ?)"
  , ""
  , "    Both have type ?, can be used interchangeably!"
  , ""
  , "19. Callback with unknown type:"
  , "    :let apply = \\f:?. \\x:?. f x"
  , "    apply : ? -> ? -> ?"
  , ""
  , "    apply (\\x:Nat. succ x) 5"
  , "    : ?"
  , "    = 6"
  , ""
  , "20. Type ascription for control:"
  , "    (5 : Nat) : ?"
  , "    : ?"
  , "    = 5"
  , ""
  , "    Cast from Nat to ? is safe (any static type can become dynamic)."
  , ""
  , "==========================================="
  , "Key Benefits of Gradual Typing"
  , "==========================================="
  , ""
  , "• **Migration**: Start with dynamic (?), add types incrementally"
  , "• **Interop**: Mix typed and untyped code"
  , "• **Flexibility**: Use ? where types are hard to express"
  , "• **Safety**: Static checking where possible, runtime checks where needed"
  , "• **Blame**: Pinpoint where runtime type errors originate"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Check what's consistent:"
  , "   :consistent ? (Bool -> Nat)"
  , "   :consistent (? -> Nat) and (Bool -> ?)"
  , ""
  , "2. See cast insertion:"
  , "   :casts \\x:?. \\y:?. if x then y else 0"
  , ""
  , "3. Build gradually typed functions:"
  , "   :let dyn = \\x:?. x"
  , "   :let partial = \\x:?. succ x"
  , "   :let static = \\x:Nat. succ x"
  , ""
  , "4. Experiment with blame:"
  , "   (\\x:?. succ x) true"
  , "   (\\x:?. if x then 0 else 1) 42"
  , ""
  , "5. Explore consistency:"
  , "   :meet Bool ?"
  , "   :join Nat ?"
  , "   :consistent (? -> ?) and (Nat -> Bool)"
  ]
