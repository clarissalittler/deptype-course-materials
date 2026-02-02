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
  putStrLn "STLC with Subtyping REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Top/Bot types, record subtyping,"
  putStrLn "          covariance/contravariance, join/meet"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :subtype T1 T2     Check if T1 <: T2"
  putStrLn "  :join T1 T2        Compute join (LUB) of T1 and T2"
  putStrLn "  :meet T1 T2        Compute meet (GLB) of T1 and T2"
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
  putStr "subtype> "
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

  ("subtype" : rest) -> handleSubtype (unwords rest) >> return state

  ("join" : rest) -> handleJoin (unwords rest) >> return state

  ("meet" : rest) -> handleMeet (unwords rest) >> return state

  ("step" : rest) -> handleStep (unwords rest) >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn ("Parse error: " ++ show err) >> return state
    Right t -> do
      let ctx = buildContext state
      case typeOf ctx t of
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
      case typeOf ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ prettyType ty

-- | Handle :subtype command
handleSubtype :: String -> IO ()
handleSubtype input = do
  -- Try to parse two types
  case parseSubtypeArgs (T.pack input) of
    Left err -> putStrLn err
    Right (t1, t2) ->
      if isSubtype t1 t2
        then putStrLn $ "  " ++ prettyType t1 ++ " <: " ++ prettyType t2 ++ "  ✓"
        else putStrLn $ "  " ++ prettyType t1 ++ " <: " ++ prettyType t2 ++ "  ✗"

-- | Handle :join command
handleJoin :: String -> IO ()
handleJoin input = do
  case parseSubtypeArgs (T.pack input) of
    Left err -> putStrLn err
    Right (t1, t2) ->
      case join t1 t2 of
        Just ty -> putStrLn $ "  " ++ prettyType t1 ++ " ⊔ " ++ prettyType t2 ++ " = " ++ prettyType ty
        Nothing -> putStrLn $ "  No join exists for " ++ prettyType t1 ++ " and " ++ prettyType t2

-- | Handle :meet command
handleMeet :: String -> IO ()
handleMeet input = do
  case parseSubtypeArgs (T.pack input) of
    Left err -> putStrLn err
    Right (t1, t2) ->
      case meet t1 t2 of
        Just ty -> putStrLn $ "  " ++ prettyType t1 ++ " ⊓ " ++ prettyType t2 ++ " = " ++ prettyType ty
        Nothing -> putStrLn $ "  No meet exists for " ++ prettyType t1 ++ " and " ++ prettyType t2

-- | Parse two types for subtype/join/meet commands
parseSubtypeArgs :: T.Text -> Either String (Type, Type)
parseSubtypeArgs input = do
  -- Simple approach: split on common separators
  let stripped = T.strip input
  -- Try to find a natural split point
  case findSplit stripped of
    Nothing -> Left "Usage: :subtype Type1 Type2 (use 'and' or ';' to separate complex types)"
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
  -- Count arrows and try to split evenly
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
      case typeOf ctx t of
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
buildContext :: REPLState -> TypeContext
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
  putStrLn "STLC with Subtyping REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :subtype T1 T2     Check if T1 <: T2"
  putStrLn "  :join T1 T2        Compute join (LUB) of T1 and T2"
  putStrLn "  :meet T1 T2        Compute meet (GLB) of T1 and T2"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat              Base types"
  putStrLn "    Top                    Supertype of everything"
  putStrLn "    Bot                    Subtype of everything"
  putStrLn "    T1 -> T2               Function type"
  putStrLn "    {l1: T1, l2: T2, ...}  Record type"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                      Variable"
  putStrLn "    \\x:T. t  or  λx:T. t   Lambda abstraction"
  putStrLn "    t1 t2                  Application"
  putStrLn "    true, false            Boolean literals"
  putStrLn "    if t1 then t2 else t3  Conditional"
  putStrLn "    0, succ t, pred t      Natural numbers"
  putStrLn "    iszero t               Zero test"
  putStrLn "    {l1 = t1, l2 = t2}     Record"
  putStrLn "    t.l                    Projection"
  putStrLn "    t as T                 Type ascription (upcast)"
  putStrLn ""
  putStrLn "Subtyping Rules:"
  putStrLn "  Bot <: T <: Top          (for all T)"
  putStrLn "  T1 -> T2 <: S1 -> S2     if S1 <: T1 and T2 <: S2"
  putStrLn "  {l1:T1,...,ln+1:Tn+1}    Width: more fields is subtype"
  putStrLn "    <: {l1:T1,...,ln:Tn}"
  putStrLn "  {li:Ti} <: {li:Si}       Depth: if Ti <: Si for all i"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "STLC with Subtyping Examples"
  , "==========================================="
  , ""
  , "--- Top and Bot Types ---"
  , ""
  , "1. Any value can be cast to Top:"
  , "   true as Top"
  , "   : Top"
  , ""
  , "2. Bot is the empty type (no inhabitants):"
  , "   :type \\x:Bot. x"
  , "   : Bot -> Bot"
  , ""
  , "3. Bot is subtype of everything:"
  , "   :subtype Bot Nat"
  , "   Bot <: Nat  ✓"
  , ""
  , "--- Function Subtyping (Variance) ---"
  , ""
  , "4. Contravariant in argument, covariant in result:"
  , "   :subtype (Top -> Nat) and (Nat -> Nat)"
  , "   (Top -> Nat) <: (Nat -> Nat)  ✓"
  , ""
  , "   (A function accepting Top can be used where Nat is expected)"
  , ""
  , "5. NOT the other way:"
  , "   :subtype (Nat -> Nat) and (Top -> Nat)"
  , "   (Nat -> Nat) <: (Top -> Nat)  ✗"
  , ""
  , "6. Covariant in return type:"
  , "   :subtype (Nat -> Bot) and (Nat -> Nat)"
  , "   (Nat -> Bot) <: (Nat -> Nat)  ✓"
  , ""
  , "--- Record Subtyping ---"
  , ""
  , "7. Width subtyping (more fields = subtype):"
  , "   :subtype {x: Nat, y: Nat} and {x: Nat}"
  , "   {x: Nat, y: Nat} <: {x: Nat}  ✓"
  , ""
  , "8. Depth subtyping (subtype fields):"
  , "   :subtype {x: Bot} and {x: Nat}"
  , "   {x: Bot} <: {x: Nat}  ✓"
  , ""
  , "9. Using records with subtyping:"
  , "   (\\r:{x: Nat}. r.x) {x = succ 0, y = true}"
  , "   : Nat"
  , "   = 1"
  , ""
  , "--- Join and Meet ---"
  , ""
  , "10. Join (least upper bound):"
  , "    :join Nat Bool"
  , "    Nat ⊔ Bool = Top"
  , ""
  , "11. Meet (greatest lower bound):"
  , "    :meet Nat Top"
  , "    Nat ⊓ Top = Nat"
  , ""
  , "12. Record join (intersection of fields):"
  , "    :join {x: Nat, y: Bool} and {x: Nat, z: Nat}"
  , "    {x: Nat, y: Bool} ⊔ {x: Nat, z: Nat} = {x: Nat}"
  , ""
  , "13. Record meet (union of fields):"
  , "    :meet {x: Nat} and {y: Bool}"
  , "    {x: Nat} ⊓ {y: Bool} = {x: Nat, y: Bool}"
  , ""
  , "--- Polymorphism via Top ---"
  , ""
  , "14. Top as a universal type:"
  , "    :let id = \\x:Top. x"
  , "    id true"
  , "    : Top"
  , ""
  , "15. But we lose type info with Top:"
  , "    :let applyToTop = \\f:Top -> Nat. f true"
  , "    applyToTop (\\x:Top. 0)"
  , "    : Nat"
  , "    = 0"
  , ""
  , "--- Ascription (Explicit Upcast) ---"
  , ""
  , "16. Upcast a record (hide fields):"
  , "    ({x = 0, y = true} as {x: Nat})"
  , "    : {x: Nat}"
  , ""
  , "17. Upcast to Top:"
  , "    (succ (succ 0)) as Top"
  , "    : Top"
  , ""
  , "--- Step-by-Step Evaluation ---"
  , ""
  , "18. Watch evaluation steps:"
  , "    :steps (\\x:Nat. succ x) (succ 0)"
  , "    0. (λx:Nat. succ x) 1"
  , "    1. succ 1"
  , "    2. 2"
  , ""
  , "19. Record projection steps:"
  , "    :steps {x = succ 0, y = true}.x"
  , "    0. {x = 1, y = true}.x"
  , "    1. 1"
  , ""
  , "==========================================="
  , "Key Concepts"
  , "==========================================="
  , ""
  , "• **Subtyping**: S <: T means S can be used where T is expected"
  , "• **Variance**: Functions are contravariant in argument,"
  , "               covariant in result"
  , "• **Width Subtyping**: More record fields = more specific = subtype"
  , "• **Depth Subtyping**: Subtype fields make subtype records"
  , "• **Top/Bot**: Universal supertype and empty subtype"
  , "• **Join (⊔)**: Least upper bound (most specific common supertype)"
  , "• **Meet (⊓)**: Greatest lower bound (most general common subtype)"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Check subtyping relations:"
  , "   :subtype {a: Nat, b: Bool} and {a: Nat}"
  , ""
  , "2. Compute joins and meets:"
  , "   :join Nat Bool"
  , "   :meet {x: Nat} and {y: Bool}"
  , ""
  , "3. Use functions with subtyping:"
  , "   (\\r:{x: Nat}. r.x) {x = 0, y = true, z = false}"
  , ""
  , "4. Explore contravariance:"
  , "   :let acceptTop = \\f:Top -> Nat. f true"
  , "   acceptTop (\\x:Top. 0)"
  ]
