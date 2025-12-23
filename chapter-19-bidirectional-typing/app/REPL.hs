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
  putStrLn "============================================="
  putStrLn "Bidirectional Type Checking REPL - Chapter 19"
  putStrLn "============================================="
  putStrLn ""
  putStrLn "Key insight: Two typing judgments:"
  putStrLn "  Γ ⊢ e ⇒ A    (infer type A from e)"
  putStrLn "  Γ ⊢ e ⇐ A    (check e against type A)"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the inferred type of term t"
  putStrLn "  :infer t           Show inference mode (⇒) for term t"
  putStrLn "  :check t : T       Check term t against type T (⇐)"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Type an expression to infer its type and evaluate it."
  putStrLn "Type :examples to see comprehensive examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "bidir> "
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
  ("infer" : rest) -> handleInfer (unwords rest) state >> return state

  ("check" : rest) -> handleCheck (unwords rest) >> return state

  ("step" : rest) -> handleStep (unwords rest) >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      let ctx = buildContext state
      case infer ctx t of
        Left err -> putStrLn ("Type error: " ++ showTypeError err) >> return state
        Right ty -> do
          let v = evalClosed t
          putStrLn $ x ++ " : " ++ prettyType ty ++ " = " ++ prettyVal v
          return state
            { bindings = Map.insert x t (bindings state)
            , typeBindings = Map.insert x ty (typeBindings state)
            }

-- | Handle :type command (alias for :infer)
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input state = handleInfer input state

-- | Handle :infer command
handleInfer :: String -> REPLState -> IO ()
handleInfer input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let ctx = buildContext state
      case infer ctx t of
        Left err -> do
          putStrLn $ "Cannot infer: " ++ showTypeError err
          putStrLn "Hint: Use type annotation (t : Type) or :check command"
        Right ty -> do
          putStrLn $ "  " ++ prettyTerm t
          putStrLn $ "  ⇒ " ++ prettyType ty

-- | Handle :check command
handleCheck :: String -> IO ()
handleCheck input = do
  -- Parse "term : type"
  case break (== ':') input of
    (_, "") -> putStrLn "Usage: :check term : type"
    (termStr, ':':typeStr) -> do
      case parseTerm (trim termStr) of
        Left err -> putStrLn $ "Parse error in term: " ++ err
        Right t -> do
          case parseType (trim typeStr) of
            Left err -> putStrLn $ "Parse error in type: " ++ err
            Right ty -> do
              case check emptyCtx t ty of
                Left err -> do
                  putStrLn $ "Check failed: " ++ showTypeError err
                Right () -> do
                  putStrLn $ "  " ++ prettyTerm t
                  putStrLn $ "  ⇐ " ++ prettyType ty ++ "  ✓"
                  let v = evalClosed t
                  putStrLn $ "  = " ++ prettyVal v
    _ -> putStrLn "Usage: :check term : type"

-- | Handle :step command
handleStep :: String -> IO ()
handleStep input = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      putStrLn "  Single-step evaluation not implemented"
      putStrLn "  Use :steps to see full evaluation"

-- | Handle :steps command
handleSteps :: String -> REPLState -> IO ()
handleSteps input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      putStrLn $ "  0. " ++ prettyTerm t
      let v = evalClosed t
      putStrLn $ "  => " ++ prettyVal v
      putStrLn "  (NbE-based evaluation - single big step)"

-- | Handle term input
handleInput :: String -> REPLState -> IO REPLState
handleInput input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      let ctx = buildContext state

      -- Try to infer type and display
      case infer ctx t of
        Left err -> do
          putStrLn $ "Cannot infer: " ++ showTypeError err
          putStrLn "Hint: Use type annotation (t : Type) or :check command"
        Right ty -> do
          putStrLn $ "  " ++ prettyTerm t
          when (showTypes state) $
            putStrLn $ "  ⇒ " ++ prettyType ty

          -- Evaluate
          let result = evalClosed t
          putStrLn $ "  = " ++ prettyVal result
      return state

-- | Build context from bindings
buildContext :: REPLState -> Ctx
buildContext state = foldr (\(x, ty) ctx -> extendCtx x ty ctx)
                            emptyCtx
                            (Map.toList $ typeBindings state)

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Bindings:"
  if Map.null (bindings state)
    then putStrLn "  (none)"
    else mapM_ showBinding (Map.toList $ bindings state)
  where
    showBinding (x, t) = case Map.lookup x (typeBindings state) of
      Just ty -> putStrLn $ "  " ++ x ++ " : " ++ prettyType ty ++ " = " ++ prettyTerm t
      Nothing -> putStrLn $ "  " ++ x ++ " = " ++ prettyTerm t

-- | Helper for when
when :: Bool -> IO () -> IO ()
when True action = action
when False _ = return ()

-- | Show type error in a readable way
showTypeError :: TypeError -> String
showTypeError = \case
  UnboundVariable x -> "Unbound variable: " ++ x
  UnboundTypeVariable a -> "Unbound type variable: " ++ a
  TypeMismatch expected actual ->
    "Type mismatch: expected " ++ prettyType expected ++
    ", got " ++ prettyType actual
  ExpectedFunction ty ->
    "Expected function type, got: " ++ prettyType ty
  ExpectedForall ty ->
    "Expected polymorphic type (∀), got: " ++ prettyType ty
  ExpectedBool ty ->
    "Expected Bool, got: " ++ prettyType ty
  ExpectedNat ty ->
    "Expected Nat, got: " ++ prettyType ty
  ExpectedProduct ty ->
    "Expected product type (×), got: " ++ prettyType ty
  ExpectedSum ty ->
    "Expected sum type (+), got: " ++ prettyType ty
  CannotInfer t ->
    "Cannot infer type for this term: " ++ prettyTerm t

-- | Trim whitespace
trim :: String -> String
trim = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "============================================="
  putStrLn "Bidirectional Type Checking REPL Commands"
  putStrLn "============================================="
  putStrLn ""
  putStrLn "Core Concept:"
  putStrLn "  Two judgment forms work together:"
  putStrLn "    Γ ⊢ e ⇒ A    \"infer type A from e\"    (synthesis)"
  putStrLn "    Γ ⊢ e ⇐ A    \"check e against type A\" (checking)"
  putStrLn ""
  putStrLn "Key Principle:"
  putStrLn "  • Introduction forms are CHECKED (⇐)"
  putStrLn "    - λx. e, (e1, e2), inl e, inr e, Λα. e"
  putStrLn "  • Elimination forms are INFERRED (⇒)"
  putStrLn "    - x, e1 e2, fst e, snd e, case e, e [T]"
  putStrLn "  • Annotations switch from checking to inference"
  putStrLn "    - (e : T), λ(x:T). e"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the inferred type of term t"
  putStrLn "  :infer t           Show inference mode (⇒) for term t"
  putStrLn "  :check t : T       Check term t against type T (⇐)"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit              Base types"
  putStrLn "    T1 -> T2                     Function type"
  putStrLn "    (T1, T2)                     Product type"
  putStrLn "    (T1 + T2)                    Sum type"
  putStrLn "    forall a. T                  Universal type"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x                            Variable (⇒)"
  putStrLn "    \\x. e  or  λx. e             Unannotated lambda (⇐)"
  putStrLn "    \\(x : T). e  or  λ(x:T). e  Annotated lambda (⇒)"
  putStrLn "    (e : T)                      Type annotation (⇒)"
  putStrLn "    e1 e2                        Application (⇒)"
  putStrLn "    let x = e1 in e2             Let binding"
  putStrLn "    true, false                  Boolean literals (⇒)"
  putStrLn "    if e1 then e2 else e3        Conditional (⇒)"
  putStrLn "    zero, suc e                  Natural numbers (⇒)"
  putStrLn "    natrec z s n                 Natural recursion"
  putStrLn "    unit                         Unit value (⇒)"
  putStrLn "    (e1, e2)                     Pair (⇐)"
  putStrLn "    fst e, snd e                 Projections (⇒)"
  putStrLn "    inl e, inr e                 Sum injections (⇐)"
  putStrLn "    case e of inl x -> e1        Case analysis (⇒)"
  putStrLn "              | inr y -> e2"
  putStrLn "    /\\a. e  or  Λa. e            Type abstraction (⇐)"
  putStrLn "    e [T]                        Type application (⇒)"
  putStrLn ""
  putStrLn "Why Bidirectional?"
  putStrLn "  • Minimizes type annotations"
  putStrLn "  • Maintains decidability"
  putStrLn "  • Natural for introduction vs elimination forms"
  putStrLn "  • Works well with dependent types"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "============================================="
  , "Bidirectional Type Checking Examples"
  , "============================================="
  , ""
  , "--- Introduction vs Elimination Forms ---"
  , ""
  , "1. Unannotated lambda CANNOT be inferred:"
  , "   \\x. x"
  , "   → Error: Cannot infer type"
  , ""
  , "2. But can be CHECKED if we know the type:"
  , "   :check \\x. x : Bool -> Bool"
  , "   → λx. x"
  , "     ⇐ Bool → Bool  ✓"
  , ""
  , "3. Type annotation makes lambda inferrable:"
  , "   (\\x. x : Bool -> Bool)"
  , "   → (λx. x : Bool → Bool)"
  , "     ⇒ Bool → Bool"
  , ""
  , "4. Annotated lambda is directly inferrable:"
  , "   \\(x : Bool). x"
  , "   → λ(x : Bool). x"
  , "     ⇒ Bool → Bool"
  , ""
  , "--- Variables and Application ---"
  , ""
  , "5. Variables can be inferred (if bound):"
  , "   :let id = \\(x : Bool). x"
  , "   id"
  , "   → id : Bool → Bool"
  , ""
  , "6. Application infers function, checks argument:"
  , "   (\\(x : Bool). x) true"
  , "   → (λ(x : Bool). x) true"
  , "     ⇒ Bool"
  , "     = true"
  , ""
  , "--- Pairs (Introduction) ---"
  , ""
  , "7. Pairs CANNOT be inferred (need expected type):"
  , "   (true, zero)"
  , "   → Error: Cannot infer type"
  , ""
  , "8. Pairs can be CHECKED:"
  , "   :check (true, zero) : (Bool, Nat)"
  , "   → (true, zero)"
  , "     ⇐ (Bool, Nat)  ✓"
  , ""
  , "9. Or use annotation to make inferrable:"
  , "   ((true, zero) : (Bool, Nat))"
  , "   → ((true, zero) : (Bool, Nat))"
  , "     ⇒ (Bool, Nat)"
  , "     = (true, 0)"
  , ""
  , "--- Projections (Elimination) ---"
  , ""
  , "10. Projections CAN be inferred:"
  , "    fst ((true, zero) : (Bool, Nat))"
  , "    → fst ((true, zero) : (Bool, Nat))"
  , "      ⇒ Bool"
  , "      = true"
  , ""
  , "11. Second projection:"
  , "    snd ((true, zero) : (Bool, Nat))"
  , "    → snd ((true, zero) : (Bool, Nat))"
  , "      ⇒ Nat"
  , "      = 0"
  , ""
  , "--- Sum Types ---"
  , ""
  , "12. Sum injections CANNOT be inferred:"
  , "    inl true"
  , "    → Error: Cannot infer type (which sum type?)"
  , ""
  , "13. Sum injections can be CHECKED:"
  , "    :check inl true : (Bool + Nat)"
  , "    → inl true"
  , "      ⇐ (Bool + Nat)  ✓"
  , ""
  , "14. Case analysis CAN be inferred:"
  , "    case (inl true : (Bool + Nat)) of"
  , "      inl b -> if b then zero else suc zero"
  , "      | inr n -> n"
  , "    → ... ⇒ Nat = 0"
  , ""
  , "--- Polymorphism (System F) ---"
  , ""
  , "15. Type abstraction CANNOT be inferred:"
  , "    /\\a. \\(x : a). x"
  , "    → Error: Cannot infer type"
  , ""
  , "16. But can be CHECKED:"
  , "    :check /\\a. \\(x : a). x : forall a. a -> a"
  , "    → Λa. λ(x : a). x"
  , "      ⇐ ∀a. a → a  ✓"
  , ""
  , "17. Or annotated for inference:"
  , "    (/\\a. \\(x : a). x : forall a. a -> a)"
  , "    → (Λa. λ(x : a). x : ∀a. a → a)"
  , "      ⇒ ∀a. a → a"
  , ""
  , "18. Type application CAN be inferred:"
  , "    (/\\a. \\(x : a). x : forall a. a -> a) [Bool]"
  , "    → (Λa. λ(x : a). x : ∀a. a → a) [Bool]"
  , "      ⇒ Bool → Bool"
  , ""
  , "19. Full polymorphic identity usage:"
  , "    ((/\\a. \\(x : a). x : forall a. a -> a) [Bool]) true"
  , "    → ... ⇒ Bool = true"
  , ""
  , "--- Natural Numbers ---"
  , ""
  , "20. Natural numbers CAN be inferred:"
  , "    suc (suc zero)"
  , "    → suc (suc zero)"
  , "      ⇒ Nat"
  , "      = 2"
  , ""
  , "21. Natural recursion (natrec z s n):"
  , "    natrec zero (\\(n : Nat). \\(acc : Nat). suc acc) (suc (suc zero))"
  , "    → ... ⇒ Nat = 2"
  , ""
  , "--- Let Bindings ---"
  , ""
  , "22. Let can infer if bound term can:"
  , "    let f = \\(x : Bool). x in f true"
  , "    → let f = λ(x : Bool). x in f true"
  , "      ⇒ Bool"
  , "      = true"
  , ""
  , "23. Let binding with annotation:"
  , "    let id = (\\x. x : Bool -> Bool) in id false"
  , "    → ... ⇒ Bool = false"
  , ""
  , "--- Subsumption (Inference ⇒ Checking) ---"
  , ""
  , "24. Any inferrable term can be checked:"
  , "    :check true : Bool"
  , "    → true ⇐ Bool  ✓"
  , ""
  , "25. Function application inferred, then checked:"
  , "    :check (\\(x : Nat). suc x) zero : Nat"
  , "    → (λ(x : Nat). suc x) zero ⇐ Nat  ✓"
  , ""
  , "============================================="
  , "Key Insights"
  , "============================================="
  , ""
  , "• **Mode Switching**: Annotations (e : T) switch from"
  , "  checking mode to inference mode"
  , ""
  , "• **Minimality**: Only need annotations where necessary:"
  , "  - Lambda parameters: λ(x:T). e  or  (λx. e : T1 -> T2)"
  , "  - Pair/sum types:    (e1, e2 : T)  or  :check (e1, e2) : T"
  , "  - Type abstractions: (Λa. e : ∀a. T)"
  , ""
  , "• **Decidability**: Bidirectional checking is decidable"
  , "  even for System F (unlike full type inference)"
  , ""
  , "• **Introduction vs Elimination**:"
  , "  - λ, pairs, inl/inr, Λ → need type (CHECKED ⇐)"
  , "  - variables, app, fst/snd, case, [T] → provide type (INFERRED ⇒)"
  , ""
  , "============================================="
  , "Try It!"
  , "============================================="
  , ""
  , "1. Compare inference vs checking:"
  , "   \\x. x                        -- Error!"
  , "   :check \\x. x : Nat -> Nat    -- OK"
  , "   (\\x. x : Nat -> Nat)         -- OK"
  , ""
  , "2. See where annotations are needed:"
  , "   (true, false)                      -- Error!"
  , "   ((true, false) : (Bool, Bool))     -- OK"
  , ""
  , "3. Build polymorphic functions:"
  , "   :let polyId = (/\\a. \\(x : a). x : forall a. a -> a)"
  , "   polyId [Nat] zero"
  , "   polyId [Bool] true"
  , ""
  , "4. Explore mode switching:"
  , "   :infer (\\(x : Nat). x)      -- Can infer"
  , "   :infer \\x. x                -- Cannot infer"
  , "   :check \\x. x : Nat -> Nat   -- Can check"
  , ""
  ]
