{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module REPL (runREPL) where

import Syntax
import Parser
import Pretty
import NbE
import TypeCheck
import Semantic

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import System.IO (hFlush, stdout)
import Control.Exception (catch, IOException)
import GHC.IO.Exception (IOErrorType(..))
import System.IO.Error (ioeGetErrorType)

-- | REPL State
data REPLState = REPLState
  { bindings :: Map String Term
  , typeBindings :: Map String Val
  , valueBindings :: Map String Val
  , showSteps :: Bool
  , showTypes :: Bool
  , showVals :: Bool
  , maxSteps :: Int
  , ctx :: Ctx
  }

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { bindings = Map.empty
  , typeBindings = Map.empty
  , valueBindings = Map.empty
  , showSteps = False
  , showTypes = True
  , showVals = False
  , maxSteps = 1000
  , ctx = emptyCtx
  }

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "==========================================="
  putStrLn "Normalization by Evaluation (NbE) REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Semantic evaluation, quotation,"
  putStrLn "          dependent types, HOAS closures"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Infer the type of term t"
  putStrLn "  :normalize t       Normalize term (default)"
  putStrLn "  :nf t              Alias for :normalize"
  putStrLn "  :eval t            Show semantic value (eval phase)"
  putStrLn "  :quote t           Show quotation of evaluated term"
  putStrLn "  :step t            Show one normalization step"
  putStrLn "  :steps t           Show all normalization steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Type an expression to normalize it."
  putStrLn "Type :examples to see comprehensive examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "nbe> "
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
  ["q"] -> putStrLn "Goodbye!" >> error "quit"
  ["env"] -> showEnv state >> return state
  ["reset"] -> putStrLn "Bindings reset." >> return initialState

  ("let" : x : "=" : rest) -> handleLetBinding x (unwords rest) state

  ("type" : rest) -> handleTypeOf (unwords rest) state >> return state

  ("normalize" : rest) -> handleNormalize (unwords rest) >> return state
  ("nf" : rest) -> handleNormalize (unwords rest) >> return state

  ("eval" : rest) -> handleEval (unwords rest) >> return state

  ("quote" : rest) -> handleQuote (unwords rest) >> return state

  ("step" : rest) -> handleStep (unwords rest) >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      case infer (ctx state) t of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right ty -> do
          let val = eval emptyEnv t
              nf = normalize t
          putStrLn $ x ++ " : " ++ prettyNf 0 (quote 0 ty) ++ " = " ++ prettyNf 0 nf
          return state
            { bindings = Map.insert x t (bindings state)
            , typeBindings = Map.insert x ty (typeBindings state)
            , valueBindings = Map.insert x val (valueBindings state)
            }

-- | Handle :type command
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      case infer (ctx state) t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> do
          let tyNf = quote 0 ty
          putStrLn $ "  : " ++ prettyNf 0 tyNf

-- | Handle :normalize command
handleNormalize :: String -> IO ()
handleNormalize input = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let nf = normalize t
      putStrLn $ "  " ++ prettyNf 0 nf

-- | Handle :eval command (show semantic value)
handleEval :: String -> IO ()
handleEval input = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let val = eval emptyEnv t
      putStrLn $ "Semantic value:"
      putStrLn $ "  " ++ show val
      putStrLn ""
      putStrLn "This is the result of the EVALUATION phase (Term → Val)"

-- | Handle :quote command (show quotation)
handleQuote :: String -> IO ()
handleQuote input = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let val = eval emptyEnv t
          nf = quote 0 val
      putStrLn $ "Evaluation phase (Term → Val):"
      putStrLn $ "  " ++ show val
      putStrLn ""
      putStrLn "Quotation phase (Val → Nf):"
      putStrLn $ "  " ++ prettyNf 0 nf

-- | Handle :step command (not really applicable for NbE, show eval/quote)
handleStep :: String -> IO ()
handleStep input = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      putStrLn "NbE works in two phases:"
      putStrLn ""
      putStrLn "1. EVALUATION (Term → Val):"
      let val = eval emptyEnv t
      putStrLn $ "   " ++ show val
      putStrLn ""
      putStrLn "2. QUOTATION (Val → Nf):"
      let nf = quote 0 val
      putStrLn $ "   " ++ prettyNf 0 nf

-- | Handle :steps command (show detailed phases)
handleSteps :: String -> REPLState -> IO ()
handleSteps input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      putStrLn "=== NORMALIZATION BY EVALUATION ==="
      putStrLn ""
      putStrLn "Input term:"
      putStrLn $ "  " ++ prettyTerm [] t
      putStrLn ""

      putStrLn "Phase 1: EVALUATION (Term → Val)"
      putStrLn "  - Interpret term in semantic domain"
      putStrLn "  - Use Haskell's evaluation for beta-reduction"
      let val = eval emptyEnv t
      putStrLn $ "  Result: " ++ show val
      putStrLn ""

      putStrLn "Phase 2: QUOTATION (Val → Nf)"
      putStrLn "  - Read back semantic value to normal form"
      putStrLn "  - Generate fresh variables for lambdas"
      let nf = quote 0 val
      putStrLn $ "  Result: " ++ prettyNf 0 nf
      putStrLn ""

      putStrLn "Final Normal Form:"
      putStrLn $ "  " ++ prettyNf 0 nf

-- | Handle term input
handleInput :: String -> REPLState -> IO REPLState
handleInput input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      -- Type check if enabled
      when (showTypes state) $ do
        case infer (ctx state) t of
          Left err -> putStrLn $ "Type error: " ++ show err
          Right ty -> putStrLn $ "  : " ++ prettyNf 0 (quote 0 ty)

      -- Show semantic value if enabled
      when (showVals state) $ do
        let val = eval emptyEnv t
        putStrLn $ "  Val: " ++ show val

      -- Normalize and display
      let nf = normalize t
      putStrLn $ "  " ++ prettyNf 0 nf

      return state

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Bindings:"
  if Map.null (bindings state)
    then putStrLn "  (none)"
    else mapM_ showBinding (Map.toList $ bindings state)
  where
    showBinding (x, t) = do
      let tyStr = case Map.lookup x (typeBindings state) of
            Just ty -> " : " ++ prettyNf 0 (quote 0 ty)
            Nothing -> ""
          nf = normalize t
      putStrLn $ "  " ++ x ++ tyStr ++ " = " ++ prettyNf 0 nf

-- | Helper for when
when :: Bool -> IO () -> IO ()
when True action = action
when False _ = return ()

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "Normalization by Evaluation REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Infer the type of term t"
  putStrLn "  :normalize t       Normalize term to normal form"
  putStrLn "  :nf t              Alias for :normalize"
  putStrLn "  :eval t            Show semantic value (evaluation phase)"
  putStrLn "  :quote t           Show both evaluation and quotation"
  putStrLn "  :step t            Show NbE phases"
  putStrLn "  :steps t           Show detailed normalization process"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Type                     Universe"
  putStrLn "    Bool                     Boolean type"
  putStrLn "    Nat                      Natural number type"
  putStrLn "    forall (x:A) -> B        Pi type (dependent function)"
  putStrLn "    (x : A) -> B             Pi type (alternative)"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                        Variable"
  putStrLn "    \\x. t  or  λx. t         Lambda abstraction"
  putStrLn "    t1 t2                    Application"
  putStrLn "    let x:A = t in u         Let binding"
  putStrLn "    true, false              Boolean literals"
  putStrLn "    if t1 then t2 else t3    Conditional"
  putStrLn "    zero, suc t              Natural numbers"
  putStrLn "    natElim P z s n          Natural eliminator"
  putStrLn ""
  putStrLn "Key Concepts:"
  putStrLn "  - NbE = Evaluation + Quotation"
  putStrLn "  - Evaluation: Use Haskell for beta-reduction"
  putStrLn "  - Quotation: Read back to canonical form"
  putStrLn "  - Enables type checking dependent types"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Normalization by Evaluation Examples"
  , "==========================================="
  , ""
  , "--- Basic Lambda Calculus ---"
  , ""
  , "1. Identity function:"
  , "   \\x. x"
  , "   = λx. x"
  , ""
  , "2. Beta reduction:"
  , "   (\\x. x) true"
  , "   = true"
  , ""
  , "3. Multiple application:"
  , "   (\\x. \\y. x) true false"
  , "   = true"
  , ""
  , "4. Nested application:"
  , "   (\\f. \\x. f x) (\\y. y) true"
  , "   = true"
  , ""
  , "--- Understanding NbE Phases ---"
  , ""
  , "5. Show evaluation phase:"
  , "   :eval (\\x. \\y. x) true"
  , "   Semantic value:"
  , "   VLam \"y\" (Closure [VTrue] (TVar 1))"
  , ""
  , "6. Show both phases:"
  , "   :quote (\\x. \\y. x) true"
  , "   Evaluation phase (Term → Val):"
  , "   VLam \"y\" (Closure [VTrue] (TVar 1))"
  , "   Quotation phase (Val → Nf):"
  , "   λy. true"
  , ""
  , "--- Dependent Types ---"
  , ""
  , "7. Pi type (function type):"
  , "   forall (A:Type) -> A -> A"
  , "   = (A : Type) → A → A"
  , ""
  , "8. Identity with explicit type:"
  , "   (\\A. \\x. x) Bool true"
  , "   = true"
  , ""
  , "9. Type-level application:"
  , "   (\\A. A) Bool"
  , "   = Bool"
  , ""
  , "--- Booleans ---"
  , ""
  , "10. Boolean type:"
  , "    :type Bool"
  , "    : Type"
  , ""
  , "11. If-then-else:"
  , "    if true then zero else suc zero"
  , "    = zero"
  , ""
  , "12. Conditional with variables:"
  , "    (\\b. if b then true else false) true"
  , "    = true"
  , ""
  , "--- Natural Numbers ---"
  , ""
  , "13. Natural number type:"
  , "    :type Nat"
  , "    : Type"
  , ""
  , "14. Successor:"
  , "    suc (suc zero)"
  , "    = suc (suc zero)"
  , ""
  , "15. Addition via natElim:"
  , "    :let add = \\m. \\n. natElim (\\_.Nat) n (\\_.\\r.suc r) m"
  , "    add (suc zero) (suc zero)"
  , "    = suc (suc zero)"
  , ""
  , "--- Let Bindings ---"
  , ""
  , "16. Simple let:"
  , "    let x:Bool = true in x"
  , "    = true"
  , ""
  , "17. Nested let:"
  , "    let x:Bool = true in let y:Bool = x in y"
  , "    = true"
  , ""
  , "18. Let with function:"
  , "    let id:forall(A:Type)->A->A = \\A.\\x.x in id Bool true"
  , "    = true"
  , ""
  , "--- Normalization Examples ---"
  , ""
  , "19. Eta expansion is NOT performed:"
  , "    \\x. (\\y. y) x"
  , "    = λx. x"
  , ""
  , "20. Dead code elimination:"
  , "    (\\x. \\y. x) true false"
  , "    = true"
  , ""
  , "21. Nested beta reduction:"
  , "    ((\\x. \\y. \\z. x z (y z)) (\\u.\\v.u) (\\a.a)) true"
  , "    = true"
  , ""
  , "--- Understanding Semantic Domain ---"
  , ""
  , "22. Lambda becomes closure:"
  , "    :eval \\x. x"
  , "    VLam \"x\" (Closure [] (TVar 0))"
  , "    (A closure with empty environment)"
  , ""
  , "23. Closure captures environment:"
  , "    :eval (\\x. \\y. x) true"
  , "    VLam \"y\" (Closure [VTrue] (TVar 1))"
  , "    (The closure captures VTrue in environment)"
  , ""
  , "24. Application evaluates immediately:"
  , "    :eval (\\x. x) true"
  , "    VTrue"
  , "    (Beta reduction happened during evaluation!)"
  , ""
  , "--- Quotation Process ---"
  , ""
  , "25. Quote a simple value:"
  , "    :quote true"
  , "    Quotation phase (Val → Nf):"
  , "    true"
  , ""
  , "26. Quote a function:"
  , "    :quote \\x. x"
  , "    Quotation phase (Val → Nf):"
  , "    λx. x"
  , ""
  , "27. Quote generates fresh variables:"
  , "    :quote \\f. \\x. f x"
  , "    (Fresh variables x0, x1 generated during quotation)"
  , ""
  , "--- Step-by-Step Analysis ---"
  , ""
  , "28. Detailed normalization:"
  , "    :steps (\\x. x) true"
  , "    Shows:"
  , "      - Input term"
  , "      - Evaluation phase (Term → Val)"
  , "      - Quotation phase (Val → Nf)"
  , "      - Final normal form"
  , ""
  , "29. Complex normalization:"
  , "    :steps (\\x. \\y. x) (if true then zero else suc zero) false"
  , "    Shows full NbE process for complex term"
  , ""
  , "--- Type Checking with NbE ---"
  , ""
  , "30. Type checking uses normalization:"
  , "    :type (\\A. \\x. x) Bool true"
  , "    : Bool"
  , "    (NbE normalizes types to check equality)"
  , ""
  , "31. Dependent type example:"
  , "    :let Vec = \\A.\\n.Type in Vec Nat zero"
  , "    : Type"
  , ""
  , "--- Neutral Terms ---"
  , ""
  , "32. Free variable creates neutral:"
  , "    :let f = \\x. x in :eval f"
  , "    VLam \"x\" (Closure [] (TVar 0))"
  , "    (Variables under lambda remain symbolic)"
  , ""
  , "33. Stuck computation:"
  , "    :let h = \\x. if x then true else false in h"
  , "    = λx. if x then true else false"
  , "    (Can't reduce without knowing x)"
  , ""
  , "==========================================="
  , "Key Insights"
  , "==========================================="
  , ""
  , "• **Two-Phase Process**:"
  , "    1. Evaluation: Term → Val (using Haskell)"
  , "    2. Quotation: Val → Nf (generating fresh vars)"
  , ""
  , "• **HOAS (Higher-Order Abstract Syntax)**:"
  , "    - Lambdas become Haskell closures"
  , "    - Beta reduction uses Haskell's evaluation"
  , "    - No explicit substitution needed!"
  , ""
  , "• **Semantic Domain (Val)**:"
  , "    - VLam: Lambda with closure"
  , "    - VNe: Neutral (stuck on variable)"
  , "    - VTrue, VFalse, VZero, VSuc: Data"
  , ""
  , "• **Normal Forms (Nf)**:"
  , "    - Canonical representation"
  , "    - Can compare syntactically"
  , "    - Used for type equality checking"
  , ""
  , "• **Why NbE?**"
  , "    - Efficient normalization"
  , "    - Elegant implementation"
  , "    - Essential for dependent types"
  , "    - Reuses host language evaluation"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Compare evaluation and quotation:"
  , "   :eval (\\x. \\y. x) true"
  , "   :quote (\\x. \\y. x) true"
  , ""
  , "2. See detailed normalization:"
  , "   :steps ((\\x.x)(\\y.y)) true"
  , ""
  , "3. Explore dependent types:"
  , "   :let id = \\A.\\x.x in id Bool true"
  , ""
  , "4. Build complex terms:"
  , "   :let const = \\x.\\y.x in const zero (suc zero)"
  , ""
  , "5. Type-level computation:"
  , "   (\\T. T) (if true then Nat else Bool)"
  , ""
  ]
