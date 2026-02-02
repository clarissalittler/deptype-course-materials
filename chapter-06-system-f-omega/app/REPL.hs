{-# LANGUAGE LambdaCase #-}

module REPL (runREPL) where

import Syntax
import Parser
import Pretty
import TypeCheck
import Eval

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import System.IO (hFlush, stdout)
import Control.Monad (when)
import Control.Exception (catch, IOException)
import GHC.IO.Exception (IOErrorType(..))
import System.IO.Error (ioeGetErrorType)

-- | REPL State
data REPLState = REPLState
  { termBindings :: Map String Term
  , typeBindings :: Map String Type
  , kindBindings :: Map String Kind
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
  , kindBindings = Map.empty
  , stepMode = False
  , showSteps = False
  , showTypes = True
  , typeCheckMode = True
  , maxSteps = 1000
  }

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "==================================="
  putStrLn "System F-omega REPL"
  putStrLn "==================================="
  putStrLn ""
  putStrLn "Higher-kinded types with type-level computation"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help          Show this help message"
  putStrLn "  :examples      Show example expressions"
  putStrLn "  :quit          Exit the REPL"
  putStrLn "  :let x = t     Bind term t to variable x"
  putStrLn "  :tlet T = τ    Bind type τ to type variable T"
  putStrLn "  :klet K = κ    Bind kind κ to kind variable K"
  putStrLn "  :type t        Show the type of term t"
  putStrLn "  :kind τ        Show the kind of type τ"
  putStrLn "  :normalize τ   Normalize type τ (type-level beta reduction)"
  putStrLn "  :step t        Show single evaluation step"
  putStrLn "  :steps t       Show all evaluation steps"
  putStrLn "  :env           Show current bindings"
  putStrLn "  :reset         Reset all bindings"
  putStrLn ""
  putStrLn "Type an expression to evaluate it."
  putStrLn "Type :examples to see example expressions."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "λω> "
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

  ["let", x, "=", rest] -> handleLetBinding x rest state
  "let" : x : "=" : rest -> handleLetBinding x (unwords rest) state

  ["tlet", t, "=", rest] -> handleTypeBinding t rest state
  "tlet" : t : "=" : rest -> handleTypeBinding t (unwords rest) state

  ["klet", k, "=", rest] -> handleKindBinding k rest state
  "klet" : k : "=" : rest -> handleKindBinding k (unwords rest) state

  ["type", rest] -> handleTypeOf rest state >> return state
  "type" : rest -> handleTypeOf (unwords rest) state >> return state

  ["kind", rest] -> handleKindOf rest state >> return state
  "kind" : rest -> handleKindOf (unwords rest) state >> return state

  ["normalize", rest] -> handleNormalize rest state >> return state
  "normalize" : rest -> handleNormalize (unwords rest) state >> return state

  ["step", rest] -> handleStep rest state >> return state
  "step" : rest -> handleStep (unwords rest) state >> return state

  ["steps", rest] -> handleSteps rest state >> return state
  "steps" : rest -> handleSteps (unwords rest) state >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      let kctx = kindBindings state
          ctx = buildTypeCtx state
      case typeOf kctx ctx t of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right ty -> do
          let v = eval t
          when (showTypes state) $
            putStrLn $ x ++ " : " ++ prettyType ty
          return state { termBindings = Map.insert x v (termBindings state) }

-- | Handle type binding
handleTypeBinding :: String -> String -> REPLState -> IO REPLState
handleTypeBinding t input state = do
  case parseType input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right ty -> do
      let kctx = kindBindings state
      case kinding kctx ty of
        Left err -> putStrLn ("Kind error: " ++ show err) >> return state
        Right k -> do
          putStrLn $ t ++ " :: " ++ prettyKind k
          return state { typeBindings = Map.insert t ty (typeBindings state) }

-- | Handle kind binding
handleKindBinding :: String -> String -> REPLState -> IO REPLState
handleKindBinding k input state = do
  case parseKind input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right kind -> do
      putStrLn $ k ++ " = " ++ prettyKind kind
      return state { kindBindings = Map.insert k kind (kindBindings state) }

-- | Handle :type command
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let kctx = kindBindings state
          ctx = buildTypeCtx state
      case typeOf kctx ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ prettyType ty

-- | Handle :kind command
handleKindOf :: String -> REPLState -> IO ()
handleKindOf input state = do
  case parseType input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right ty -> do
      let kctx = kindBindings state
      case kinding kctx ty of
        Left err -> putStrLn $ "Kind error: " ++ show err
        Right k -> putStrLn $ "  :: " ++ prettyKind k

-- | Handle :normalize command
handleNormalize :: String -> REPLState -> IO ()
handleNormalize input state = do
  case parseType input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right ty -> do
      let kctx = kindBindings state
      case kinding kctx ty of
        Left err -> putStrLn $ "Kind error: " ++ show err
        Right k -> do
          let normalized = normalizeType ty
          putStrLn $ "  :: " ++ prettyKind k
          putStrLn $ "  =  " ++ prettyType normalized

-- | Handle :step command
handleStep :: String -> REPLState -> IO ()
handleStep input _state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      case step t of
        Nothing -> putStrLn "  (no reduction)"
        Just t' -> putStrLn $ "  ⟶  " ++ prettyTerm t'

-- | Handle :steps command
handleSteps :: String -> REPLState -> IO ()
handleSteps input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let steps = generateEvalSteps t (maxSteps state)
      mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ s) (zip [0::Int ..] steps)

-- | Generate evaluation steps
generateEvalSteps :: Term -> Int -> [String]
generateEvalSteps t maxS = go t 0
  where
    go current n
      | n >= maxS = [prettyTerm current ++ " (max steps reached)"]
      | otherwise = case step current of
          Nothing -> [prettyTerm current]
          Just next -> prettyTerm current : go next (n + 1)

-- | Handle term input
handleInput :: String -> REPLState -> IO REPLState
handleInput input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      let kctx = kindBindings state
          ctx = buildTypeCtx state

      -- Type check
      when (typeCheckMode state) $ do
        case typeOf kctx ctx t of
          Left err -> putStrLn $ "Type error: " ++ show err
          Right ty -> when (showTypes state) $
            putStrLn $ "  : " ++ prettyType ty

      -- Evaluate
      if stepMode state || showSteps state
        then do
          let steps = generateEvalSteps t (maxSteps state)
          mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ s) (zip [0::Int ..] steps)
          return state
        else do
          let result = eval t
          putStrLn $ "  " ++ prettyTerm result
          return state

-- | Build type context from bindings
buildTypeCtx :: REPLState -> TypeCtx
buildTypeCtx state = Map.foldrWithKey go Map.empty (termBindings state)
  where
    go x t ctx = case typeOf (kindBindings state) ctx t of
      Right ty -> Map.insert x ty ctx
      Left _ -> ctx

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Kind bindings:"
  if Map.null (kindBindings state)
    then putStrLn "  (none)"
    else mapM_ showKind (Map.toList $ kindBindings state)

  putStrLn ""
  putStrLn "Type bindings:"
  if Map.null (typeBindings state)
    then putStrLn "  (none)"
    else mapM_ showType (Map.toList $ typeBindings state)

  putStrLn ""
  putStrLn "Term bindings:"
  if Map.null (termBindings state)
    then putStrLn "  (none)"
    else mapM_ showTerm (Map.toList $ termBindings state)
  where
    showKind (k, kind) = putStrLn $ "  " ++ k ++ " = " ++ prettyKind kind
    showType (t, ty) = case kinding (kindBindings state) ty of
      Right k -> putStrLn $ "  " ++ t ++ " :: " ++ prettyKind k ++ " = " ++ prettyType ty
      Left _ -> putStrLn $ "  " ++ t ++ " = " ++ prettyType ty
    showTerm (x, t) = case typeOf (kindBindings state) (buildTypeCtx state) t of
      Right ty -> putStrLn $ "  " ++ x ++ " : " ++ prettyType ty ++ " = " ++ prettyTerm t
      Left _ -> putStrLn $ "  " ++ x ++ " = " ++ prettyTerm t

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn "System F-omega REPL Commands:"
  putStrLn ""
  putStrLn "  :help          Show this help message"
  putStrLn "  :examples      Show example expressions"
  putStrLn "  :quit          Exit the REPL"
  putStrLn "  :let x = t     Bind term t to variable x"
  putStrLn "  :tlet T = τ    Bind type τ to type variable T"
  putStrLn "  :klet K = κ    Bind kind κ to kind variable K"
  putStrLn "  :type t        Show the type of term t"
  putStrLn "  :kind τ        Show the kind of type τ"
  putStrLn "  :normalize τ   Normalize type τ (type-level beta reduction)"
  putStrLn "  :step t        Show single evaluation step"
  putStrLn "  :steps t       Show all evaluation steps"
  putStrLn "  :env           Show current bindings"
  putStrLn "  :reset         Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Kinds:"
  putStrLn "    *             Kind of proper types"
  putStrLn "    κ₁ -> κ₂       Kind of type constructors"
  putStrLn ""
  putStrLn "  Types:"
  putStrLn "    α             Type variable"
  putStrLn "    τ₁ -> τ₂       Function type"
  putStrLn "    forall α::κ. τ Universal type (with kind annotation)"
  putStrLn "    /\\α::κ. τ      Type-level lambda (type operator)"
  putStrLn "    τ₁ τ₂          Type-level application"
  putStrLn "    Bool, Nat     Base types"
  putStrLn ""
  putStrLn "  Terms:"
  putStrLn "    x             Variable"
  putStrLn "    \\(x:τ). t      Lambda abstraction"
  putStrLn "    t₁ t₂          Application"
  putStrLn "    /\\α::κ. t      Type abstraction (with kind annotation)"
  putStrLn "    t [τ]         Type application"
  putStrLn "    true, false   Boolean literals"
  putStrLn "    if t₁ then t₂ else t₃"
  putStrLn "    0, succ, pred, iszero"

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "=== System F-omega Examples ==="
  , ""
  , "--- Basic Higher-Kinded Types ---"
  , ""
  , "1. Type Constructor (List :: * -> *)"
  , "   :tlet List = /\\A::*. forall B::*. (A -> B -> B) -> B -> B"
  , "   :kind List"
  , "   :: * → *"
  , ""
  , "2. Type Application (List Bool :: *)"
  , "   :kind List Bool"
  , "   :: *"
  , ""
  , "3. Maybe Type Constructor"
  , "   :tlet Maybe = /\\A::*. forall B::*. (A -> B) -> B -> B"
  , "   :kind Maybe"
  , "   :: * → *"
  , ""
  , "--- Type-Level Functions ---"
  , ""
  , "4. Identity Type Function (id :: * -> *)"
  , "   :tlet Id = /\\A::*. A"
  , "   :kind Id"
  , "   :: * → *"
  , "   :normalize Id Bool"
  , "   :: *"
  , "   =  Bool"
  , ""
  , "5. Constant Type Function (const :: * -> * -> *)"
  , "   :tlet Const = /\\A::*. /\\B::*. A"
  , "   :kind Const"
  , "   :: * → * → *"
  , "   :normalize Const Bool Nat"
  , "   :: *"
  , "   =  Bool"
  , ""
  , "6. Function Type Constructor"
  , "   :tlet Arrow = /\\A::*. /\\B::*. A -> B"
  , "   :kind Arrow"
  , "   :: * → * → *"
  , ""
  , "--- Higher-Kinded Type Constructors ---"
  , ""
  , "7. Functor (type constructor that takes type constructor)"
  , "   -- F :: (* -> *) -> *"
  , "   :tlet Functor = /\\F::* -> *. forall A::*. forall B::*."
  , "                     (A -> B) -> F A -> F B"
  , "   :kind Functor"
  , "   :: (* → *) → *"
  , ""
  , "8. Monad"
  , "   :tlet Monad = /\\M::* -> *. forall A::*. forall B::*."
  , "                   (A -> M B) -> M A -> M B"
  , "   :kind Monad"
  , "   :: (* → *) → *"
  , ""
  , "--- Term-Level Examples ---"
  , ""
  , "9. Polymorphic List Constructor"
  , "   :let nil = /\\A::*. /\\B::*. \\cons:(A -> B -> B). \\nil:B. nil"
  , "   nil : ∀A::*. ∀B::*. (A → B → B) → B → B"
  , ""
  , "10. Polymorphic Cons"
  , "    :let cons = /\\A::*. \\x:A. /\\B::*. \\cons:(A -> B -> B). \\nil:B."
  , "                  cons x nil"
  , "    cons : ∀A::*. A → ∀B::*. (A → B → B) → B → B"
  , ""
  , "11. Map with Explicit Type Constructor"
  , "    -- map :: ∀F::* -> *. ∀A::*. ∀B::*. (A -> B) -> F A -> F B"
  , "    This requires dependent types for full implementation!"
  , ""
  , "--- Type-Level Computation ---"
  , ""
  , "12. Beta Reduction at Type Level"
  , "    :normalize (/\\A::*. A -> A) Bool"
  , "    :: *"
  , "    =  Bool → Bool"
  , ""
  , "13. Multiple Applications"
  , "    :normalize (/\\A::*. /\\B::*. A -> B) Bool Nat"
  , "    :: *"
  , "    =  Bool → Nat"
  , ""
  , "14. Nested Type Applications"
  , "    :tlet Pair = /\\A::*. /\\B::*. forall C::*. (A -> B -> C) -> C"
  , "    :normalize Pair Bool Nat"
  , "    :: *"
  , "    =  ∀C::*. (Bool → Nat → C) → C"
  , ""
  , "--- Church Encodings with Higher-Kinded Types ---"
  , ""
  , "15. Church Boolean (parametric in result kind)"
  , "    :tlet CBool = forall A::*. A -> A -> A"
  , "    :let ctrue = /\\A::*. \\t:A. \\f:A. t"
  , "    :let cfalse = /\\A::*. \\t:A. \\f:A. f"
  , ""
  , "16. Church Pair"
  , "    :tlet CPair = /\\A::*. /\\B::*. forall C::*. (A -> B -> C) -> C"
  , "    :let pair = /\\A::*. /\\B::*. \\x:A. \\y:B. /\\C::*. \\f:(A -> B -> C). f x y"
  , ""
  , "17. Existential Types via Universal Types"
  , "    :tlet Exists = /\\P::* -> *. forall R::*. (forall A::*. P A -> R) -> R"
  , "    :kind Exists"
  , "    :: (* → *) → *"
  , ""
  , "--- Advanced Examples ---"
  , ""
  , "18. Type-Level Composition"
  , "    :tlet Compose = /\\F::* -> *. /\\G::* -> *. /\\A::*. F (G A)"
  , "    :kind Compose"
  , "    :: (* → *) → (* → *) → * → *"
  , ""
  , "19. Identity Functor"
  , "    :tlet IdF = /\\A::*. A"
  , "    :kind IdF"
  , "    :: * → *"
  , "    :normalize Compose IdF IdF Bool"
  , "    =  Bool"
  , ""
  , "20. Apply Type Function"
  , "    :tlet Apply = /\\F::* -> *. /\\A::*. F A"
  , "    :kind Apply"
  , "    :: (* → *) → * → *"
  , ""
  , "=== Key Differences from System F ==="
  , ""
  , "1. **Kinds**: Types are classified by kinds (* for proper types, κ₁ → κ₂ for constructors)"
  , "2. **Type-Level Lambda**: /\\α::κ. τ creates type operators/functions"
  , "3. **Type-Level Application**: τ₁ τ₂ applies type functions"
  , "4. **Higher-Kinded Types**: Can abstract over type constructors (F :: * → *)"
  , "5. **Type-Level Computation**: Types can be computed via beta reduction"
  , ""
  , "=== Try It! ==="
  , ""
  , "Define your own type constructors:"
  , "  :tlet Either = /\\A::*. /\\B::*. forall C::*. (A -> C) -> (B -> C) -> C"
  , "  :kind Either"
  , "  :normalize Either Bool Nat"
  , ""
  , "Create terms that use them:"
  , "  :let left = /\\A::*. /\\B::*. \\x:A. /\\C::*. \\l:(A -> C). \\r:(B -> C). l x"
  , "  :type left"
  ]
