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
  putStrLn "Recursive Types REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: iso-recursive types (μα.T),"
  putStrLn "          fold/unfold operations,"
  putStrLn "          lists, trees, and other inductive types"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :unfold T          Unfold recursive type T one step"
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
  putStr "recursive> "
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

  ("unfold" : rest) -> handleUnfoldType (unwords rest) >> return state

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

-- | Handle :unfold command
handleUnfoldType :: String -> IO ()
handleUnfoldType input = do
  case parseType (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right ty -> do
      let unfolded = unfoldType ty
      putStrLn $ "  " ++ prettyType ty ++ " ⟶ " ++ prettyType unfolded

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
  putStrLn "Recursive Types REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :unfold T          Unfold recursive type T one step"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit        Base types"
  putStrLn "    T1 -> T2               Function type"
  putStrLn "    T1 * T2                Product type"
  putStrLn "    T1 + T2                Sum type"
  putStrLn "    mu α. T                Recursive type"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                      Variable"
  putStrLn "    \\x:T. t  or  λx:T. t   Lambda abstraction"
  putStrLn "    t1 t2                  Application"
  putStrLn "    true, false            Boolean literals"
  putStrLn "    if t1 then t2 else t3  Conditional"
  putStrLn "    0, succ t, pred t      Natural numbers"
  putStrLn "    iszero t               Zero test"
  putStrLn "    unit                   Unit value"
  putStrLn "    <t1, t2>               Pair"
  putStrLn "    fst t, snd t           Projections"
  putStrLn "    inl t as T             Left injection"
  putStrLn "    inr t as T             Right injection"
  putStrLn "    case t of ...          Case analysis"
  putStrLn "    fold [T] t             Fold into recursive type"
  putStrLn "    unfold [T] t           Unfold recursive type"
  putStrLn ""
  putStrLn "Recursive Type Examples:"
  putStrLn "  List = μa. Unit + (Nat * a)"
  putStrLn "  Nat  = μa. Unit + a"
  putStrLn "  Tree = μa. Nat + (a * a)"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Recursive Types Examples"
  , "==========================================="
  , ""
  , "--- Basic Recursive Types ---"
  , ""
  , "1. Natural numbers as recursive type:"
  , "   NatRec = μa. Unit + a"
  , "   "
  , "   Zero:  fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a))"
  , "   : μa. Unit + a"
  , ""
  , "2. Successor (fold of right injection):"
  , "   let zero = fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a)) in"
  , "   fold [mu a. Unit + a] (inr zero as Unit + (mu a. Unit + a))"
  , "   : μa. Unit + a"
  , ""
  , "3. Unfold to inspect:"
  , "   let zero = fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a)) in"
  , "   unfold [mu a. Unit + a] zero"
  , "   : Unit + (μa. Unit + a)"
  , "   = inl unit as Unit + (μa. Unit + a)"
  , ""
  , "--- Lists as Recursive Types ---"
  , ""
  , "4. Empty list (nil):"
  , "   List = μa. Unit + (Nat * a)"
  , "   "
  , "   fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a))))"
  , "   : μa. Unit + (Nat * a)"
  , ""
  , "5. Single element list:"
  , "   let nil = fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a)))) in"
  , "   fold [mu a. Unit + (Nat * a)] (inr <succ 0, nil> as Unit + (Nat * (mu a. Unit + (Nat * a))))"
  , "   : μa. Unit + (Nat * a)"
  , ""
  , "6. Two element list:"
  , "   let nil = fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a)))) in"
  , "   let cons1 = fold [mu a. Unit + (Nat * a)] (inr <succ 0, nil> as Unit + (Nat * (mu a. Unit + (Nat * a)))) in"
  , "   fold [mu a. Unit + (Nat * a)] (inr <succ (succ 0), cons1> as Unit + (Nat * (mu a. Unit + (Nat * a))))"
  , "   : μa. Unit + (Nat * a)"
  , ""
  , "--- Fold and Unfold Operations ---"
  , ""
  , "7. Fold creates a recursive value:"
  , "   fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a))"
  , "   : μa. Unit + a"
  , "   "
  , "   The type annotation [mu a. Unit + a] specifies the recursive type"
  , ""
  , "8. Unfold unwraps one layer:"
  , "   :type fold [mu a. Bool + a] (inl true as Bool + (mu a. Bool + a))"
  , "   : μa. Bool + a"
  , "   "
  , "   :type unfold [mu a. Bool + a] (fold [mu a. Bool + a] (inl true as Bool + (mu a. Bool + a)))"
  , "   : Bool + (μa. Bool + a)"
  , ""
  , "9. Unfold a type with :unfold command:"
  , "   :unfold mu a. Unit + (Nat * a)"
  , "   μa. Unit + (Nat * a) ⟶ Unit + (Nat * (μa. Unit + (Nat * a)))"
  , ""
  , "--- Binary Trees ---"
  , ""
  , "10. Binary tree type:"
  , "    Tree = μa. Unit + (Nat * (a * a))"
  , "    "
  , "    Empty leaf:"
  , "    fold [mu a. Unit + (Nat * (a * a))] (inl unit as Unit + (Nat * ((mu a. Unit + (Nat * (a * a))) * (mu a. Unit + (Nat * (a * a))))))"
  , "    : μa. Unit + (Nat * (a * a))"
  , ""
  , "11. Tree with one node:"
  , "    let leaf = fold [mu a. Unit + (Nat * (a * a))] (inl unit as Unit + (Nat * ((mu a. Unit + (Nat * (a * a))) * (mu a. Unit + (Nat * (a * a)))))) in"
  , "    fold [mu a. Unit + (Nat * (a * a))] (inr <succ 0, <leaf, leaf>> as Unit + (Nat * ((mu a. Unit + (Nat * (a * a))) * (mu a. Unit + (Nat * (a * a))))))"
  , "    : μa. Unit + (Nat * (a * a))"
  , ""
  , "--- Functions on Recursive Types ---"
  , ""
  , "12. IsNil function for lists:"
  , "    \\xs:(mu a. Unit + (Nat * a))."
  , "      case (unfold [mu a. Unit + (Nat * a)] xs) of"
  , "        inl u => true"
  , "      | inr p => false"
  , "    : (μa. Unit + (Nat * a)) -> Bool"
  , ""
  , "13. Head function for lists (unsafe - assumes non-empty):"
  , "    \\xs:(mu a. Unit + (Nat * a))."
  , "      case (unfold [mu a. Unit + (Nat * a)] xs) of"
  , "        inl u => 0"
  , "      | inr p => fst p"
  , "    : (μa. Unit + (Nat * a)) -> Nat"
  , ""
  , "14. Tail function for lists:"
  , "    \\xs:(mu a. Unit + (Nat * a))."
  , "      case (unfold [mu a. Unit + (Nat * a)] xs) of"
  , "        inl u => fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a))))"
  , "      | inr p => snd p"
  , "    : (μa. Unit + (Nat * a)) -> (μa. Unit + (Nat * a))"
  , ""
  , "--- Step-by-Step Evaluation ---"
  , ""
  , "15. Watch fold/unfold cancel out:"
  , "    :steps unfold [mu a. Unit + a] (fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a)))"
  , "    0. unfold [μa. Unit + a] (fold [μa. Unit + a] (inl unit as Unit + (μa. Unit + a)))"
  , "    1. inl unit as Unit + (μa. Unit + a)"
  , ""
  , "16. Evaluate isNil on empty list:"
  , "    let nil = fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a)))) in"
  , "    :steps case (unfold [mu a. Unit + (Nat * a)] nil) of inl u => true | inr p => false"
  , ""
  , "--- Type Checking ---"
  , ""
  , "17. Check the type of nil:"
  , "    :type fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a))))"
  , "    : μa. Unit + (Nat * a)"
  , ""
  , "18. Check the type after unfold:"
  , "    let nil = fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a)))) in"
  , "    :type unfold [mu a. Unit + (Nat * a)] nil"
  , "    : Unit + (Nat * (μa. Unit + (Nat * a)))"
  , ""
  , "19. Unfold a type to see its expansion:"
  , "    :unfold mu a. Nat + a"
  , "    μa. Nat + a ⟶ Nat + (μa. Nat + a)"
  , ""
  , "==========================================="
  , "Key Concepts"
  , "==========================================="
  , ""
  , "• **Recursive Types (μα.T)**: Types that refer to themselves"
  , "• **Iso-recursive**: fold/unfold required (explicit conversion)"
  , "• **Equi-recursive**: fold/unfold automatic (implicit conversion)"
  , "• **fold [μα.T] t**: Wrap term t to create recursive type"
  , "  - t must have type T[μα.T/α] (type with μα.T substituted for α)"
  , "  - Result has type μα.T"
  , "• **unfold [μα.T] t**: Unwrap one layer of recursive type"
  , "  - t must have type μα.T"
  , "  - Result has type T[μα.T/α]"
  , "• **Lists**: μa. Unit + (Element * a)"
  , "  - nil: fold (inl unit)"
  , "  - cons: fold (inr <element, rest>)"
  , "• **Natural Numbers**: μa. Unit + a"
  , "  - zero: fold (inl unit)"
  , "  - succ n: fold (inr n)"
  , "• **Binary Trees**: μa. Unit + (Value * (a * a))"
  , "  - leaf: fold (inl unit)"
  , "  - node: fold (inr <value, <left, right>>)"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Create a simple list:"
  , "   let nil = fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a)))) in nil"
  , ""
  , "2. Create recursive naturals:"
  , "   fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a))"
  , ""
  , "3. Unfold to inspect:"
  , "   let zero = fold [mu a. Unit + a] (inl unit as Unit + (mu a. Unit + a)) in"
  , "   unfold [mu a. Unit + a] zero"
  , ""
  , "4. Try the isNil function:"
  , "   let nil = fold [mu a. Unit + (Nat * a)] (inl unit as Unit + (Nat * (mu a. Unit + (Nat * a)))) in"
  , "   let isNil = \\xs:(mu a. Unit + (Nat * a)). case (unfold [mu a. Unit + (Nat * a)] xs) of inl u => true | inr p => false in"
  , "   isNil nil"
  , ""
  , "5. Explore type unfolding:"
  , "   :unfold mu a. Bool + (Nat * a)"
  ]
