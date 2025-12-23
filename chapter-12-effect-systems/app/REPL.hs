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
  , effectBindings :: Map String EffectRow
  , effectEnv :: EffectEnv
  , showSteps :: Bool
  , showTypes :: Bool
  , maxSteps :: Int
  }

-- | Initial REPL state with standard effects
initialState :: REPLState
initialState = REPLState
  { bindings = Map.empty
  , typeBindings = Map.empty
  , effectBindings = Map.empty
  , effectEnv = standardEffects
  , showSteps = False
  , showTypes = True
  , maxSteps = 1000
  }

-- | Standard effects available in the system
standardEffects :: EffectEnv
standardEffects = Map.fromList
  [ ("State", Effect "State"
      [ Operation "get" TyUnit TyNat
      , Operation "put" TyNat TyUnit
      ])
  , ("Exception", Effect "Exception"
      [ Operation "throw" TyUnit TyUnit
      ])
  , ("IO", Effect "IO"
      [ Operation "print" TyNat TyUnit
      , Operation "read" TyUnit TyNat
      ])
  , ("Choice", Effect "Choice"
      [ Operation "choose" TyBool TyBool
      ])
  ]

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "==========================================="
  putStrLn "Effect Systems REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Algebraic effects and handlers,"
  putStrLn "          effect rows, effect polymorphism"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type and effects of term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :effects           Show available effects"
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
  putStr "effect> "
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
  ["effects"] -> showEffects (effectEnv state) >> return state

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
      let ctx = buildContext state
      case infer ctx (effectEnv state) t of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right (TypeAndEffect ty eff) -> do
          let v = eval t
          putStrLn $ x ++ " : " ++ prettyType ty ++
            (if isEmptyRow eff then "" else " ! " ++ prettyEffectRow eff) ++
            " = " ++ prettyTerm v
          return state
            { bindings = Map.insert x v (bindings state)
            , typeBindings = Map.insert x ty (typeBindings state)
            , effectBindings = Map.insert x eff (effectBindings state)
            }

-- | Handle :type command
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      let ctx = buildContext state
      case infer ctx (effectEnv state) t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right (TypeAndEffect ty eff) ->
          putStrLn $ "  : " ++ prettyType ty ++
            (if isEmptyRow eff then "" else " ! " ++ prettyEffectRow eff)

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
      case infer ctx (effectEnv state) t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right (TypeAndEffect ty eff) -> do
          when (showTypes state) $
            putStrLn $ "  : " ++ prettyType ty ++
              (if isEmptyRow eff then "" else " ! " ++ prettyEffectRow eff)

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
      Just ty -> do
        let effStr = case Map.lookup x (effectBindings state) of
              Just eff | not (isEmptyRow eff) -> " ! " ++ prettyEffectRow eff
              _ -> ""
        putStrLn $ "  " ++ x ++ " : " ++ prettyType ty ++ effStr ++ " = " ++ prettyTerm v
      Nothing -> putStrLn $ "  " ++ x ++ " = " ++ prettyTerm v

-- | Show available effects
showEffects :: EffectEnv -> IO ()
showEffects env = do
  putStrLn "Available effects:"
  putStrLn ""
  mapM_ showEffect (Map.toList env)
  where
    showEffect (name, eff) = do
      putStrLn $ "  " ++ effectName eff ++ ":"
      mapM_ showOp (effectOps eff)
      putStrLn ""
    showOp op =
      putStrLn $ "    " ++ opName op ++ " : " ++
        prettyType (opParam op) ++ " -> " ++ prettyType (opReturn op)

-- | Helper for when
when :: Bool -> IO () -> IO ()
when True action = action
when False _ = return ()

-- | Check if effect row is empty
isEmptyRow :: EffectRow -> Bool
isEmptyRow EffEmpty = True
isEmptyRow _ = False

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "Effect Systems REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type and effects of term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :effects           Show available effects"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit                Base types"
  putStrLn "    T1 -> T2                       Pure function"
  putStrLn "    T1 -> T2 ! {E1, E2}            Effectful function"
  putStrLn "    ∀ρ. T                          Effect-polymorphic type"
  putStrLn ""
  putStrLn "  Effect Rows:"
  putStrLn "    {}                             No effects (pure)"
  putStrLn "    {State}                        Single effect"
  putStrLn "    {State, Exception}             Multiple effects"
  putStrLn "    {State | ρ}                    Open row (polymorphic)"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                              Variable"
  putStrLn "    λx:T. t                        Lambda abstraction"
  putStrLn "    t1 t2                          Application"
  putStrLn "    true, false                    Boolean literals"
  putStrLn "    if t1 then t2 else t3          Conditional"
  putStrLn "    0, succ t, pred t              Natural numbers"
  putStrLn "    iszero t                       Zero test"
  putStrLn "    ()                             Unit value"
  putStrLn "    let x = t1 in t2               Let binding"
  putStrLn "    perform Eff.op t               Perform effect operation"
  putStrLn "    handle t with h                Handle effects"
  putStrLn "    return t                       Return pure value"
  putStrLn "    Λρ. t                          Effect abstraction"
  putStrLn "    t [ε]                          Effect application"
  putStrLn ""
  putStrLn "  Handlers:"
  putStrLn "    { Eff: return x -> body; op p k -> body; ... }"
  putStrLn ""
  putStrLn "Effect System:"
  putStrLn "  - Effects are tracked in function types: A -> B ! {State, IO}"
  putStrLn "  - Handlers transform effectful computations to pure ones"
  putStrLn "  - Effect polymorphism allows code reuse across effects"
  putStrLn "  - Continuation-based semantics for composability"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Effect Systems Examples"
  , "==========================================="
  , ""
  , "--- Basic Effectful Operations ---"
  , ""
  , "1. Performing state operations:"
  , "   perform State.get ()"
  , "   : Nat ! {State}"
  , ""
  , "2. Putting a value into state:"
  , "   perform State.put 42"
  , "   : Unit ! {State}"
  , ""
  , "3. Throwing an exception:"
  , "   perform Exception.throw ()"
  , "   : Unit ! {Exception}"
  , ""
  , "4. IO operations:"
  , "   perform IO.print 5"
  , "   : Unit ! {IO}"
  , ""
  , "--- Effectful Functions ---"
  , ""
  , "5. A function that uses state:"
  , "   λx:Nat. perform State.put x"
  , "   : Nat -> Unit ! {State}"
  , ""
  , "6. A function that reads and increments state:"
  , "   λx:Unit. let s = perform State.get () in"
  , "           perform State.put (succ s)"
  , "   : Unit -> Unit ! {State}"
  , ""
  , "7. Multiple effects in sequence:"
  , "   λx:Nat. let u = perform State.put x in"
  , "          perform IO.print x"
  , "   : Nat -> Unit ! {State, IO}"
  , ""
  , "--- Effect Handlers ---"
  , ""
  , "8. State handler (simplified):"
  , "   handle (perform State.get ()) with"
  , "   { State:"
  , "     return x -> λs:Nat. x;"
  , "     get u k -> λs:Nat. k s s;"
  , "     put v k -> λs:Nat. k () v"
  , "   }"
  , ""
  , "   The handler transforms State operations into a function"
  , "   that takes the initial state and returns the result."
  , ""
  , "9. Exception handler (catch):"
  , "   handle (perform Exception.throw ()) with"
  , "   { Exception:"
  , "     return x -> x;"
  , "     throw u k -> 0"
  , "   }"
  , ""
  , "   The handler catches exceptions and returns a default value."
  , ""
  , "--- Effect Rows and Polymorphism ---"
  , ""
  , "10. Pure function (no effects):"
  , "    λx:Nat. succ x"
  , "    : Nat -> Nat"
  , "    (equivalent to: Nat -> Nat ! {})"
  , ""
  , "11. Effectful function type:"
  , "    Nat -> Nat ! {State}"
  , "    (reads: 'function from Nat to Nat with State effect')"
  , ""
  , "12. Multiple effects:"
  , "    Nat -> Nat ! {State, Exception}"
  , ""
  , "13. Open effect row (polymorphic):"
  , "    Nat -> Nat ! {State | ρ}"
  , "    (reads: 'at least State, possibly more effects ρ')"
  , ""
  , "--- Effect Polymorphism ---"
  , ""
  , "14. Effect-polymorphic identity:"
  , "    Λρ. λx:Nat. x"
  , "    : ∀ρ. Nat -> Nat ! {ρ}"
  , ""
  , "    This function works with any effect row."
  , ""
  , "15. Applying to specific effect row:"
  , "    (Λρ. λx:Nat. x) [{State}]"
  , "    : Nat -> Nat ! {State}"
  , ""
  , "--- Return and Pure Values ---"
  , ""
  , "16. Lifting a pure value:"
  , "    return 5"
  , "    : Nat"
  , ""
  , "17. Composing pure and effectful:"
  , "    let x = return 5 in"
  , "    perform State.put x"
  , "    : Unit ! {State}"
  , ""
  , "--- Practical Examples ---"
  , ""
  , "18. Counter function:"
  , "    λx:Unit."
  , "      let s = perform State.get () in"
  , "      let s' = succ s in"
  , "      perform State.put s'"
  , ""
  , "    This increments a counter stored in the state."
  , ""
  , "19. Safe division (with exceptions):"
  , "    λx:Nat. λy:Nat."
  , "      if iszero y"
  , "      then perform Exception.throw ()"
  , "      else return x"
  , ""
  , "20. Logging computation:"
  , "    λx:Nat."
  , "      let u1 = perform IO.print x in"
  , "      let r = succ x in"
  , "      let u2 = perform IO.print r in"
  , "      r"
  , ""
  , "--- Understanding Handlers ---"
  , ""
  , "A handler has two parts:"
  , "  1. return clause: handles pure values"
  , "  2. operation clauses: handle effect operations"
  , ""
  , "Each operation clause receives:"
  , "  - The argument to the operation"
  , "  - A continuation (what to do with the result)"
  , ""
  , "Example State handler structure:"
  , "  { State:"
  , "    return x -> ..."
  , "    get param continuation -> ..."
  , "    put param continuation -> ..."
  , "  }"
  , ""
  , "--- Choice Effect (Nondeterminism) ---"
  , ""
  , "21. Choosing between alternatives:"
  , "    perform Choice.choose true"
  , "    : Bool ! {Choice}"
  , ""
  , "22. Handler for Choice (collect all paths):"
  , "    handle (perform Choice.choose true) with"
  , "    { Choice:"
  , "      return x -> x;"
  , "      choose b k -> if b then k true else k false"
  , "    }"
  , ""
  , "==========================================="
  , "Key Concepts"
  , "==========================================="
  , ""
  , "• **Effects**: Computational behaviors like state, I/O, exceptions"
  , "• **Effect Rows**: Sets of effects a computation may use"
  , "• **Handlers**: Transform effectful computations by interpreting operations"
  , "• **Continuations**: Represent 'the rest of the computation'"
  , "• **Effect Polymorphism**: Code that works with any effects"
  , "• **Effect Safety**: Type system prevents unhandled effects"
  , ""
  , "Benefits of Effect Systems:"
  , "  ✓ Explicit tracking of computational effects in types"
  , "  ✓ Modular effect handling (no global interpreter)"
  , "  ✓ Effect polymorphism enables code reuse"
  , "  ✓ Safe composition of effectful operations"
  , "  ✓ Multiple interpretations of the same effect"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Explore basic effects:"
  , "   perform State.get ()"
  , "   perform IO.print 42"
  , ""
  , "2. Create effectful functions:"
  , "   λx:Nat. perform State.put (succ x)"
  , ""
  , "3. Examine effect types:"
  , "   :type λx:Nat. perform State.get ()"
  , ""
  , "4. See the standard effects:"
  , "   :effects"
  , ""
  , "5. Try composing effects:"
  , "   λx:Nat. let s = perform State.get () in"
  , "          perform IO.print s"
  , ""
  , "6. Experiment with handlers:"
  , "   handle (perform State.get ()) with"
  , "   { State: return x -> x; get u k -> k 0 0 }"
  , ""
  , "7. Build stateful computations:"
  , "   let inc = λu:Unit. let s = perform State.get () in"
  , "                      perform State.put (succ s) in"
  , "   inc"
  , ""
  ]
