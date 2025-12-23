{-# LANGUAGE LambdaCase #-}

module REPL (runREPL) where

import Syntax
import Parser
import Pretty
import qualified CEK
import qualified Krivine
import qualified SECD

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import System.IO (hFlush, stdout)
import Control.Exception (catch, IOException)
import GHC.IO.Exception (IOErrorType(..))
import System.IO.Error (ioeGetErrorType)

-- | REPL State
data REPLState = REPLState
  { bindings :: Map String Term
  , currentMachine :: Machine
  , maxSteps :: Int
  , showTrace :: Bool
  }

-- | Abstract machine to use
data Machine = CEKMachine | KrivineMachine | SECDMachine
  deriving (Eq, Show)

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { bindings = Map.empty
  , currentMachine = CEKMachine
  , maxSteps = 100
  , showTrace = False
  }

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "==========================================="
  putStrLn "Abstract Machines REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Three evaluation strategies:"
  putStrLn "  - CEK:     Call-by-value with continuations"
  putStrLn "  - Krivine: Call-by-name (lazy evaluation)"
  putStrLn "  - SECD:    Instruction-based virtual machine"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :cek               Use CEK machine (default)"
  putStrLn "  :krivine           Use Krivine machine"
  putStrLn "  :secd              Use SECD machine"
  putStrLn "  :compare t         Compare all three machines on term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Type an expression to evaluate it."
  putStrLn "Type :examples to see comprehensive examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  let prompt = case currentMachine state of
        CEKMachine     -> "cek> "
        KrivineMachine -> "krivine> "
        SECDMachine    -> "secd> "
  putStr prompt
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

  ["cek"] -> do
    putStrLn "Switched to CEK machine (call-by-value)"
    return state { currentMachine = CEKMachine }

  ["krivine"] -> do
    putStrLn "Switched to Krivine machine (call-by-name)"
    return state { currentMachine = KrivineMachine }

  ["secd"] -> do
    putStrLn "Switched to SECD machine (instruction-based)"
    return state { currentMachine = SECDMachine }

  ("let" : x : "=" : rest) -> handleLetBinding x (unwords rest) state

  ("compare" : rest) -> handleCompare (unwords rest) >> return state

  ("step" : rest) -> handleStep (unwords rest) state >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      case evalTerm (currentMachine state) t of
        Nothing -> putStrLn "Evaluation failed" >> return state
        Just v -> do
          putStrLn $ x ++ " = " ++ prettyValue v
          return state { bindings = Map.insert x t (bindings state) }

-- | Handle :compare command
handleCompare :: String -> IO ()
handleCompare input = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      putStrLn "Comparing evaluation strategies:"
      putStrLn ""

      -- CEK (call-by-value)
      putStr "  CEK (call-by-value):     "
      case CEK.run t of
        Just v -> putStrLn $ prettyValue v
        Nothing -> putStrLn "stuck/diverged"

      -- Krivine (call-by-name)
      putStr "  Krivine (call-by-name):  "
      case Krivine.run t of
        Just v -> putStrLn $ prettyValue v
        Nothing -> putStrLn "stuck/diverged"

      -- SECD (instruction-based)
      putStr "  SECD (instructions):     "
      case SECD.run t of
        Just v -> putStrLn $ prettyValue v
        Nothing -> putStrLn "stuck/diverged"

      -- Show trace lengths
      putStrLn ""
      putStrLn "Trace lengths:"
      putStrLn $ "  CEK:     " ++ show (length (CEK.trace t)) ++ " steps"
      putStrLn $ "  Krivine: " ++ show (length (Krivine.trace t)) ++ " steps"

-- | Handle :step command
handleStep :: String -> REPLState -> IO ()
handleStep input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      case currentMachine state of
        CEKMachine -> case CEK.step (CEK.inject t) of
          Nothing -> putStrLn "  (no step possible)"
          Just st -> putStrLn $ "  ⟶  " ++ prettyState st

        KrivineMachine -> case Krivine.step (Krivine.inject t) of
          Nothing -> putStrLn "  (no step possible)"
          Just st -> putStrLn $ "  ⟶  " ++ prettyKrivineState st

        SECDMachine -> case SECD.step (SECD.inject t) of
          Nothing -> putStrLn "  (no step possible)"
          Just st -> putStrLn $ "  ⟶  " ++ prettySECDState st

-- | Handle :steps command
handleSteps :: String -> REPLState -> IO ()
handleSteps input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let maxS = maxSteps state
      case currentMachine state of
        CEKMachine -> do
          let states = take maxS (CEK.trace t)
          putStrLn $ "CEK trace (" ++ show (length states) ++ " steps):"
          mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ prettyState s)
                (zip [0::Int ..] states)

        KrivineMachine -> do
          let states = take maxS (Krivine.trace t)
          putStrLn $ "Krivine trace (" ++ show (length states) ++ " steps):"
          mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ prettyKrivineState s)
                (zip [0::Int ..] states)

        SECDMachine -> do
          putStrLn "SECD execution:"
          putStrLn $ "  Compiled code: " ++ show (SECD.compile t)
          putStrLn ""
          let states = take maxS (traceSECD t)
          putStrLn $ "SECD trace (" ++ show (length states) ++ " steps):"
          mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ prettySECDState s)
                (zip [0::Int ..] states)

-- | Trace SECD execution
traceSECD :: Term -> [SECD.State]
traceSECD t = go (SECD.inject t)
  where
    go state = state : case SECD.step state of
      Nothing -> []
      Just state' -> go state'

-- | Handle term input
handleInput :: String -> REPLState -> IO REPLState
handleInput input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      case evalTerm (currentMachine state) t of
        Nothing -> putStrLn "Evaluation failed"
        Just v -> putStrLn $ "  " ++ prettyValue v
      return state

-- | Evaluate a term using the selected machine
evalTerm :: Machine -> Term -> Maybe Value
evalTerm CEKMachine t = CEK.run t
evalTerm KrivineMachine t = Krivine.run t
evalTerm SECDMachine t = SECD.run t

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Bindings:"
  if Map.null (bindings state)
    then putStrLn "  (none)"
    else mapM_ showBinding (Map.toList $ bindings state)
  putStrLn ""
  putStrLn $ "Current machine: " ++ case currentMachine state of
    CEKMachine -> "CEK (call-by-value)"
    KrivineMachine -> "Krivine (call-by-name)"
    SECDMachine -> "SECD (instruction-based)"
  where
    showBinding (x, t) = putStrLn $ "  " ++ x ++ " = " ++ prettyTerm t

-- | Pretty print Krivine state
prettyKrivineState :: Krivine.State -> String
prettyKrivineState (Krivine.State term _ stack) =
  "⟨" ++ prettyTerm term ++
  ", stack=" ++ show (length stack) ++ "⟩"

-- | Pretty print SECD state
prettySECDState :: SECD.State -> String
prettySECDState (SECD.State stack _ code _) =
  "⟨stack=" ++ show (length stack) ++
  ", code=" ++ show (length code) ++ " instrs⟩"

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "Abstract Machines REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :cek               Use CEK machine (call-by-value)"
  putStrLn "  :krivine           Use Krivine machine (call-by-name)"
  putStrLn "  :secd              Use SECD machine (instruction-based)"
  putStrLn "  :compare t         Compare all three machines on term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Terms:"
  putStrLn "    x                        Variable"
  putStrLn "    \\x. t  or  λx. t         Lambda abstraction"
  putStrLn "    t1 t2                    Application"
  putStrLn "    n                        Integer literal"
  putStrLn "    t1 + t2, t1 - t2, t1 * t2  Arithmetic"
  putStrLn "    if0 t then t1 else t2    Conditional"
  putStrLn "    let x = t1 in t2         Let binding"
  putStrLn "    fix t                    Fixed point (recursion)"
  putStrLn ""
  putStrLn "Abstract Machines:"
  putStrLn ""
  putStrLn "  CEK Machine (call-by-value):"
  putStrLn "    C - Control: current term being evaluated"
  putStrLn "    E - Environment: variable bindings"
  putStrLn "    K - Kontinuation: what to do next"
  putStrLn ""
  putStrLn "  Krivine Machine (call-by-name/lazy):"
  putStrLn "    Delays evaluation of arguments"
  putStrLn "    Uses thunks (unevaluated closures)"
  putStrLn "    Arguments evaluated when needed"
  putStrLn ""
  putStrLn "  SECD Machine (instruction-based):"
  putStrLn "    S - Stack: intermediate results"
  putStrLn "    E - Environment: variable bindings"
  putStrLn "    C - Control: instructions to execute"
  putStrLn "    D - Dump: saved contexts for returns"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Abstract Machines Examples"
  , "==========================================="
  , ""
  , "--- Basic Evaluation ---"
  , ""
  , "1. Simple arithmetic:"
  , "   3 + 4 * 2"
  , "   = 11"
  , ""
  , "2. Lambda application:"
  , "   (\\x. x + 1) 5"
  , "   = 6"
  , ""
  , "3. Let binding:"
  , "   let double = \\x. x + x in double 21"
  , "   = 42"
  , ""
  , "--- Comparing Machines ---"
  , ""
  , "4. See all three machines in action:"
  , "   :compare (\\x. x * 2) (3 + 4)"
  , ""
  , "   Output:"
  , "   CEK (call-by-value):     14"
  , "   Krivine (call-by-name):  14"
  , "   SECD (instructions):     14"
  , ""
  , "--- Call-by-Value vs Call-by-Name ---"
  , ""
  , "5. Unused argument (demonstrates laziness):"
  , "   :compare (\\x. 5) (1 + 2 + 3)"
  , ""
  , "   Both produce 5, but:"
  , "   - CEK evaluates (1+2+3) first (strict)"
  , "   - Krivine never evaluates it (lazy)"
  , ""
  , "6. Check with step counts:"
  , "   :cek"
  , "   :steps (\\x. 5) (1 + 2 + 3)"
  , "   "
  , "   :krivine"
  , "   :steps (\\x. 5) (1 + 2 + 3)"
  , ""
  , "--- Recursion with Fix ---"
  , ""
  , "7. Factorial function:"
  , "   :let fact = fix (\\f. \\n. if0 n then 1 else n * f (n - 1))"
  , "   fact 5"
  , "   = 120"
  , ""
  , "8. Sum from 1 to n:"
  , "   :let sum = fix (\\f. \\n. if0 n then 0 else n + f (n - 1))"
  , "   sum 10"
  , "   = 55"
  , ""
  , "9. Fibonacci:"
  , "   :let fib = fix (\\f. \\n. if0 n then 0 else if0 (n - 1) then 1 else f (n - 1) + f (n - 2))"
  , "   fib 7"
  , "   = 13"
  , ""
  , "--- Step-by-Step Evaluation ---"
  , ""
  , "10. Watch CEK machine evaluate:"
  , "    :cek"
  , "    :steps (\\x. x + 1) 5"
  , ""
  , "    Shows each CEK state transition"
  , ""
  , "11. Watch Krivine machine (lazy):"
  , "    :krivine"
  , "    :steps (\\x. x + x) (2 + 3)"
  , ""
  , "    Notice: argument evaluated when used"
  , ""
  , "12. SECD compilation and execution:"
  , "    :secd"
  , "    :steps (\\x. x * 2) 7"
  , ""
  , "    Shows compiled instructions and stack operations"
  , ""
  , "--- Higher-Order Functions ---"
  , ""
  , "13. Function composition:"
  , "    :let compose = \\f. \\g. \\x. f (g x)"
  , "    :let inc = \\x. x + 1"
  , "    :let double = \\x. x * 2"
  , "    compose inc double 5"
  , "    = 11"
  , ""
  , "14. Twice combinator:"
  , "    :let twice = \\f. \\x. f (f x)"
  , "    twice (\\x. x + 1) 0"
  , "    = 2"
  , ""
  , "15. Church numerals style:"
  , "    :let apply3 = \\f. \\x. f (f (f x))"
  , "    apply3 (\\x. x * 2) 1"
  , "    = 8"
  , ""
  , "--- Comparing Evaluation Orders ---"
  , ""
  , "16. Demonstrating evaluation difference:"
  , "    :let const = \\x. \\y. x"
  , "    :compare const 5 (1 + 2 + 3 + 4)"
  , ""
  , "    CEK:     Evaluates 1+2+3+4 (call-by-value)"
  , "    Krivine: Skips evaluation (call-by-name)"
  , "    Both return: 5"
  , ""
  , "17. Multiple uses of argument:"
  , "    :let usetwice = \\f. \\x. f x + f x"
  , "    :compare usetwice (\\y. y * 2) 3"
  , ""
  , "    Both evaluate to 12, but with different strategies"
  , ""
  , "--- SECD Instruction View ---"
  , ""
  , "18. See compiled instructions:"
  , "    :secd"
  , "    :steps \\x. \\y. x + y"
  , ""
  , "    Shows how lambda is compiled to IClosure"
  , ""
  , "19. Application compilation:"
  , "    :secd"
  , "    :steps (\\x. x + 1) 5"
  , ""
  , "    Shows: IConst, IClosure, IApply sequence"
  , ""
  , "--- Complex Recursion ---"
  , ""
  , "20. Mutual recursion simulation:"
  , "    :let ack = fix (\\f. \\m. \\n. if0 m then (n + 1) else if0 n then f (m - 1) 1 else f (m - 1) (f m (n - 1)))"
  , "    ack 2 2"
  , "    = 7"
  , ""
  , "==========================================="
  , "Key Concepts"
  , "==========================================="
  , ""
  , "CEK Machine:"
  , "  • Control-Environment-Kontinuation"
  , "  • Call-by-value (strict evaluation)"
  , "  • Explicit continuation (evaluation context)"
  , "  • Efficient for eager languages"
  , ""
  , "Krivine Machine:"
  , "  • Call-by-name (lazy evaluation)"
  , "  • Uses thunks (delayed computations)"
  , "  • Only evaluates when needed"
  , "  • May duplicate work (without memoization)"
  , ""
  , "SECD Machine:"
  , "  • Stack-Environment-Control-Dump"
  , "  • Compiles to instructions first"
  , "  • Like a real virtual machine"
  , "  • Historic (1964), influenced real VMs"
  , ""
  , "Evaluation Strategies:"
  , "  • Call-by-value: Evaluate args before function"
  , "  • Call-by-name: Pass unevaluated args"
  , "  • Call-by-need: Lazy + memoization (Haskell)"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Compare evaluation strategies:"
  , "   :compare (\\x. 5) (1 + 2 + 3 + 4 + 5)"
  , ""
  , "2. Trace execution step-by-step:"
  , "   :cek"
  , "   :steps (\\f. \\x. f (f x)) (\\y. y + 1) 0"
  , ""
  , "3. Switch machines and compare:"
  , "   :krivine"
  , "   (\\x. x + x) (2 * 3)"
  , "   :cek"
  , "   (\\x. x + x) (2 * 3)"
  , ""
  , "4. Explore recursion:"
  , "   :let power = fix (\\f. \\base. \\exp. if0 exp then 1 else base * f base (exp - 1))"
  , "   power 2 10"
  , ""
  , "5. SECD instructions:"
  , "   :secd"
  , "   :steps (\\x. \\y. x + y) 3 4"
  ]
