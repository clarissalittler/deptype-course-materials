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
  putStrLn "Row Types REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Extensible records, row polymorphism,"
  putStrLn "          variants, record extension/restriction"
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
  putStrLn "Type an expression to evaluate and type check it."
  putStrLn "Type :examples to see comprehensive examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "row> "
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
      -- Type check and display type
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
  putStrLn "Row Types REPL Commands:"
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
  putStrLn "    Bool, Nat, Unit        Base types"
  putStrLn "    T1 -> T2               Function type"
  putStrLn "    {l1: T1, l2: T2, ...}  Record type (closed)"
  putStrLn "    {l: T | ρ}             Row extension"
  putStrLn "    <l1: T1 | l2: T2 | ...> Variant type"
  putStrLn "    ∀ρ. T                  Row polymorphism"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                      Variable"
  putStrLn "    \\x:T. t  or  λx:T. t   Lambda abstraction"
  putStrLn "    t1 t2                  Application"
  putStrLn "    true, false            Boolean literals"
  putStrLn "    if t1 then t2 else t3  Conditional"
  putStrLn "    0, succ t, pred t      Natural numbers"
  putStrLn "    iszero t               Zero test"
  putStrLn "    ()                     Unit value"
  putStrLn "    {l1 = t1, l2 = t2}     Record literal"
  putStrLn "    t.l                    Record projection"
  putStrLn "    {l = t | r}            Record extension"
  putStrLn "    r \\ l                  Record restriction (remove field)"
  putStrLn "    <l = t> : T            Variant injection"
  putStrLn "    case t of <l1 = x1> -> t1 | ...  Pattern matching"
  putStrLn "    Λρ. t                  Row abstraction"
  putStrLn "    t [ρ]                  Row application"
  putStrLn ""
  putStrLn "Row Types Concepts:"
  putStrLn "  • Records can be extended with new fields"
  putStrLn "  • Row variables (ρ) represent unknown fields"
  putStrLn "  • Row polymorphism allows functions to work on"
  putStrLn "    records with any additional fields"
  putStrLn "  • Variants are dual to records (sum vs product)"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Row Types Examples"
  , "==========================================="
  , ""
  , "--- Basic Records ---"
  , ""
  , "1. Simple record literal:"
  , "   {x = 0, y = true}"
  , "   : {x: Nat, y: Bool}"
  , ""
  , "2. Record projection:"
  , "   {x = succ 0, y = false}.x"
  , "   : Nat"
  , "   = 1"
  , ""
  , "3. Nested records:"
  , "   {point = {x = 0, y = 1}, visible = true}"
  , "   : {point: {x: Nat, y: Nat}, visible: Bool}"
  , ""
  , "--- Record Extension ---"
  , ""
  , "4. Extend a record with a new field:"
  , "   :let point = {x = 0, y = 1}"
  , "   {z = 2 | point}"
  , "   : {z: Nat, x: Nat, y: Nat}"
  , "   = {z = 2, x = 0, y = 1}"
  , ""
  , "5. Extension in action:"
  , "   {color = true | {x = 0}}"
  , "   : {color: Bool, x: Nat}"
  , ""
  , "--- Record Restriction ---"
  , ""
  , "6. Remove a field from a record:"
  , "   {x = 0, y = 1, z = 2} \\ y"
  , "   : {x: Nat, z: Nat}"
  , "   = {x = 0, z = 2}"
  , ""
  , "--- Row Polymorphism ---"
  , ""
  , "7. Function that works on any record with an 'x' field:"
  , "   :let getX = \\r:{x: Nat}. r.x"
  , "   getX {x = 5}"
  , "   : Nat"
  , "   = 5"
  , ""
  , "8. Same function works with extra fields:"
  , "   getX {x = 3, y = true, z = ()}"
  , "   : Nat"
  , "   = 3"
  , ""
  , "9. Row polymorphic function with extension:"
  , "   :let addZ = \\r:{x: Nat, y: Nat}. {z = 0 | r}"
  , "   addZ {x = 1, y = 2}"
  , "   : {z: Nat, x: Nat, y: Nat}"
  , ""
  , "--- Variants (Tagged Unions) ---"
  , ""
  , "10. Variant injection (must specify type):"
  , "    <Left = 0> : <Left: Nat, Right: Bool>"
  , "    : <Left: Nat, Right: Bool>"
  , ""
  , "11. Another variant tag:"
  , "    <Right = true> : <Left: Nat, Right: Bool>"
  , "    : <Left: Nat, Right: Bool>"
  , ""
  , "12. Case analysis on variants:"
  , "    :let either = <Left = 5> : <Left: Nat, Right: Nat>"
  , "    case either of <Left = x> -> succ x | <Right = y> -> pred y"
  , "    : Nat"
  , "    = 6"
  , ""
  , "--- Practical Examples ---"
  , ""
  , "13. Point operations:"
  , "    :let point2D = {x = 3, y = 4}"
  , "    :let getX = \\p:{x: Nat}. p.x"
  , "    :let getY = \\p:{y: Nat}. p.y"
  , "    {sum = succ (succ (succ (succ (succ (succ (succ 0))))))}"
  , "    : {sum: Nat}"
  , ""
  , "14. Optional values with variants:"
  , "    :let just = <Some = 42> : <Some: Nat, None: Unit>"
  , "    :let nothing = <None = ()> : <Some: Nat, None: Unit>"
  , "    case just of <Some = x> -> x | <None = u> -> 0"
  , "    : Nat"
  , "    = 42"
  , ""
  , "15. Extensible record update:"
  , "    :let updateX = \\r:{x: Nat}. \\n:Nat. {x = n | r \\ x}"
  , "    This creates a new record with x updated to n"
  , ""
  , "--- Generic Programming ---"
  , ""
  , "16. Selector that works on any record with a field:"
  , "    :let select = \\r:{name: Bool}. r.name"
  , "    select {name = true, age = 0}"
  , "    : Bool"
  , "    = true"
  , ""
  , "17. Combining records:"
  , "    {a = 0 | {b = true | {c = ()}}}"
  , "    : {a: Nat, b: Bool, c: Unit}"
  , "    = {a = 0, b = true, c = ()}"
  , ""
  , "--- Error Handling Patterns ---"
  , ""
  , "18. Result type with variants:"
  , "    :let ok = <Ok = 100> : <Ok: Nat, Err: Bool>"
  , "    :let err = <Err = false> : <Ok: Nat, Err: Bool>"
  , "    case ok of <Ok = v> -> v | <Err = e> -> 0"
  , "    : Nat"
  , "    = 100"
  , ""
  , "--- Boolean Logic with Records ---"
  , ""
  , "19. Using if with record fields:"
  , "    :let config = {debug = true, port = 8080}"
  , "    if config.debug then 1 else 0"
  , "    : Nat"
  , "    = 1"
  , ""
  , "--- Higher-Order Functions ---"
  , ""
  , "20. Map over optional values:"
  , "    :let maybe_map = \\f:Nat -> Nat. \\m:<Some: Nat, None: Unit>."
  , "                       case m of"
  , "                         <Some = x> -> <Some = f x> : <Some: Nat, None: Unit>"
  , "                       | <None = u> -> <None = ()> : <Some: Nat, None: Unit>"
  , "    :let inc = \\n:Nat. succ n"
  , "    maybe_map inc (<Some = 5> : <Some: Nat, None: Unit>)"
  , "    : <Some: Nat, None: Unit>"
  , ""
  , "--- Step-by-Step Evaluation ---"
  , ""
  , "21. Watch record projection evaluation:"
  , "    :steps {x = succ 0}.x"
  , "    0. {x = succ 0}.x"
  , "    1. {x = 1}.x"
  , "    2. 1"
  , ""
  , "22. Watch case evaluation:"
  , "    :steps case <Left = succ 0> : <Left: Nat, Right: Bool> of"
  , "             <Left = x> -> x | <Right = b> -> 0"
  , "    Shows step-by-step pattern matching"
  , ""
  , "==========================================="
  , "Key Concepts"
  , "==========================================="
  , ""
  , "• **Extensible Records**: Records can be extended with new fields"
  , "  using the syntax {l = t | r}"
  , ""
  , "• **Row Variables**: ρ represents unknown/polymorphic row of fields"
  , "  Enables writing functions that work on any record with certain fields"
  , ""
  , "• **Record Restriction**: Remove fields with r \\ l"
  , "  Useful for updating records immutably"
  , ""
  , "• **Variants**: Dual to records - tagged unions where exactly"
  , "  one alternative is present at runtime"
  , ""
  , "• **Row Polymorphism**: Functions polymorphic over record structure"
  , "  Type ∀ρ. {l: T | ρ} -> ... works on any record with at least field l"
  , ""
  , "• **Type Safety**: Cannot project missing fields, cannot match"
  , "  wrong variant tags - all checked at compile time"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Create and manipulate records:"
  , "   {name = true, age = 25}.name"
  , "   {z = () | {x = 0, y = 1}}"
  , ""
  , "2. Use variants for sum types:"
  , "   case <Some = 10> : <Some: Nat, None: Unit> of"
  , "     <Some = x> -> x | <None = u> -> 0"
  , ""
  , "3. Write row-polymorphic functions:"
  , "   :let getId = \\r:{id: Nat}. r.id"
  , "   getId {id = 123, name = true}"
  , ""
  , "4. Experiment with record extension and restriction:"
  , "   :let r = {a = 0, b = 1, c = 2}"
  , "   {d = 3 | r \\ b}"
  , ""
  , "5. Pattern match on complex variants:"
  , "   :let result = <Err = false> : <Ok: Nat, Err: Bool>"
  , "   case result of <Ok = v> -> v | <Err = e> -> 999"
  , ""
  ]
