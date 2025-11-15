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
  { bindings :: Map String Term       -- term bindings
  , typeAnnotations :: Map String Term -- type annotations for bindings
  , showSteps :: Bool
  , showTypes :: Bool
  , maxSteps :: Int
  }

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { bindings = Map.empty
  , typeAnnotations = Map.empty
  , showSteps = False
  , showTypes = True
  , maxSteps = 1000
  }

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "==================================="
  putStrLn "Dependent Types REPL"
  putStrLn "==================================="
  putStrLn ""
  putStrLn "Types that depend on values: Π and Σ types"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help          Show this help message"
  putStrLn "  :examples      Show example expressions"
  putStrLn "  :quit          Exit the REPL"
  putStrLn "  :let x = t     Bind term t to variable x"
  putStrLn "  :type t        Show the type of term t"
  putStrLn "  :normalize t   Normalize term t to normal form"
  putStrLn "  :step t        Show single evaluation step"
  putStrLn "  :steps t       Show all evaluation steps"
  putStrLn "  :env           Show current bindings"
  putStrLn "  :reset         Reset all bindings"
  putStrLn ""
  putStrLn "Type an expression to evaluate and type check it."
  putStrLn "Type :examples to see example expressions."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "λΠ> "
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

  ["type", rest] -> handleTypeOf rest state >> return state
  "type" : rest -> handleTypeOf (unwords rest) state >> return state

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
      let ctx = buildContext state
      case typeOf ctx t of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right ty -> do
          let v = normalize t
          when (showTypes state) $
            putStrLn $ x ++ " : " ++ pretty ty
          return state
            { bindings = Map.insert x v (bindings state)
            , typeAnnotations = Map.insert x ty (typeAnnotations state)
            }

-- | Handle :type command
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let ctx = buildContext state
      case typeOf ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ pretty ty

-- | Handle :normalize command
handleNormalize :: String -> REPLState -> IO ()
handleNormalize input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let normalized = normalize t
      putStrLn $ "  =  " ++ pretty normalized

-- | Single-step evaluation (local implementation)
singleStep :: Term -> Maybe Term
singleStep = \case
  -- Beta reduction for lambda
  App (Lam x _ body) arg | isValue arg -> Just (subst x arg body)

  -- Reduce function in application
  App t1 t2 | not (isValue t1) -> App <$> singleStep t1 <*> pure t2

  -- Reduce argument in application
  App v1 t2 | isValue v1, not (isValue t2) -> App v1 <$> singleStep t2

  -- Pair projections
  Fst (Pair v1 _) | isValue v1 -> Just v1
  Fst t | not (isValue t) -> Fst <$> singleStep t

  Snd (Pair _ v2) | isValue v2 -> Just v2
  Snd t | not (isValue t) -> Snd <$> singleStep t

  -- Reduce inside pairs
  Pair t1 t2 | not (isValue t1) -> Pair <$> singleStep t1 <*> pure t2
  Pair v1 t2 | isValue v1, not (isValue t2) -> Pair v1 <$> singleStep t2

  -- Successor
  Succ t | not (isValue t) -> Succ <$> singleStep t

  -- Boolean conditionals
  If TmTrue t2 _ -> Just t2
  If TmFalse _ t3 -> Just t3
  If t1 t2 t3 | not (isValue t1) -> (\t1' -> If t1' t2 t3) <$> singleStep t1

  -- No reduction possible
  _ -> Nothing

-- | Handle :step command
handleStep :: String -> REPLState -> IO ()
handleStep input _state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      case singleStep t of
        Nothing -> putStrLn "  (no reduction)"
        Just t' -> putStrLn $ "  ⟶  " ++ pretty t'

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
      | n >= maxS = [pretty current ++ " (max steps reached)"]
      | otherwise = case singleStep current of
          Nothing -> [pretty current]
          Just next -> pretty current : go next (n + 1)

-- | Handle term input
handleInput :: String -> REPLState -> IO REPLState
handleInput input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      let ctx = buildContext state

      -- Type check and display type
      case typeOf ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> when (showTypes state) $
          putStrLn $ "  : " ++ pretty ty

      -- Evaluate
      if showSteps state
        then do
          let steps = generateEvalSteps t (maxSteps state)
          mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ s) (zip [0::Int ..] steps)
          return state
        else do
          let result = normalize t
          putStrLn $ "  " ++ pretty result
          return state

-- | Build context from bindings
buildContext :: REPLState -> Context
buildContext state = Map.foldrWithKey (\x ty ctx -> extendCtx x ty ctx) emptyCtx (typeAnnotations state)

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Bindings:"
  if Map.null (bindings state)
    then putStrLn "  (none)"
    else mapM_ showBinding (Map.toList $ bindings state)
  where
    showBinding (x, v) = case Map.lookup x (typeAnnotations state) of
      Just ty -> putStrLn $ "  " ++ x ++ " : " ++ pretty ty ++ " = " ++ pretty v
      Nothing -> putStrLn $ "  " ++ x ++ " = " ++ pretty v

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn "Dependent Types REPL Commands:"
  putStrLn ""
  putStrLn "  :help          Show this help message"
  putStrLn "  :examples      Show example expressions"
  putStrLn "  :quit          Exit the REPL"
  putStrLn "  :let x = t     Bind term t to variable x"
  putStrLn "  :type t        Show the type of term t"
  putStrLn "  :normalize t   Normalize term t"
  putStrLn "  :step t        Show single evaluation step"
  putStrLn "  :steps t       Show all evaluation steps"
  putStrLn "  :env           Show current bindings"
  putStrLn "  :reset         Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Type          The type of types (universe)"
  putStrLn "  x             Variable"
  putStrLn "  \\(x:A). t      Lambda abstraction"
  putStrLn "  t₁ t₂          Application"
  putStrLn "  Π(x:A). B     Dependent function type (Pi type)"
  putStrLn "  (x:A) -> B    Alternative syntax for Pi type"
  putStrLn "  Σ(x:A). B     Dependent pair type (Sigma type)"
  putStrLn "  (t₁, t₂)       Pair"
  putStrLn "  fst t         First projection"
  putStrLn "  snd t         Second projection"
  putStrLn "  Nat, Bool     Base types"
  putStrLn "  0, succ       Natural numbers"
  putStrLn "  true, false   Booleans"

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "=== Dependent Types Examples ==="
  , ""
  , "--- Basic Pi Types (Dependent Functions) ---"
  , ""
  , "1. Non-Dependent Function Type (A -> B)"
  , "   Pi(x:Nat). Bool"
  , "   : Type"
  , "   (When x doesn't appear in B, this is just Nat → Bool)"
  , ""
  , "2. Identity Function (Polymorphic)"
  , "   \\(A:Type). \\(x:A). x"
  , "   : Π(A:Type). Π(x:A). A"
  , "   (Or using arrow: (A:Type) -> (x:A) -> A)"
  , ""
  , "3. Const Function"
  , "   \\(A:Type). \\(B:Type). \\(x:A). \\(y:B). x"
  , "   : Π(A:Type). Π(B:Type). Π(x:A). Π(y:B). A"
  , ""
  , "--- Dependent Pairs (Sigma Types) ---"
  , ""
  , "4. Simple Dependent Pair"
  , "   (zero, true)"
  , "   : Σ(x:Nat). Bool"
  , "   (Type of second component could depend on first)"
  , ""
  , "5. Projections"
  , "   :let p = (zero, true)"
  , "   fst p"
  , "   : Nat"
  , "   =  0"
  , ""
  , "   snd p"
  , "   : Bool"
  , "   =  true"
  , ""
  , "6. Type-Value Pair"
  , "   (Nat, zero)"
  , "   : Σ(A:Type). A"
  , "   (Existential type: \"there exists a type A and a value of type A\")"
  , ""
  , "--- Advanced Dependent Types ---"
  , ""
  , "7. Type Family Indexed by Booleans"
  , "   \\(b:Bool). if b then Nat else Bool"
  , "   : Π(b:Bool). Type"
  , "   (Type depends on the boolean value!)"
  , ""
  , "8. Dependent Function Using Type Family"
  , "   :let T = \\(b:Bool). if b then Nat else Bool"
  , "   \\(b:Bool). if b then zero else true"
  , "   : Π(b:Bool). T b"
  , "   (Return type depends on the argument value)"
  , ""
  , "9. Length-Indexed Vectors (Conceptual)"
  , "   -- Vec : Π(n:Nat). Type"
  , "   -- nil  : Vec zero"
  , "   -- cons : Π(n:Nat). Π(x:A). Π(xs:Vec n). Vec (succ n)"
  , "   (Requires inductive types - see Chapter 8)"
  , ""
  , "--- Church Encodings with Dependent Types ---"
  , ""
  , "10. Church Booleans"
  , "    :let CBool = Π(A:Type). Π(t:A). Π(f:A). A"
  , "    :let ctrue = \\(A:Type). \\(t:A). \\(f:A). t"
  , "    :let cfalse = \\(A:Type). \\(t:A). \\(f:A). f"
  , "    ctrue : Π(A:Type). Π(t:A). Π(f:A). A"
  , ""
  , "11. Church Pairs"
  , "    :let CPair = \\(A:Type). \\(B:Type)."
  , "                   Π(C:Type). Π(f:Π(x:A). Π(y:B). C). C"
  , "    :let pair = \\(A:Type). \\(B:Type). \\(x:A). \\(y:B)."
  , "                  \\(C:Type). \\(f:Π(a:A). Π(b:B). C). f x y"
  , ""
  , "12. Church Naturals"
  , "    :let CNat = Π(A:Type). Π(z:A). Π(s:Π(x:A). A). A"
  , "    :let czero = \\(A:Type). \\(z:A). \\(s:Π(x:A). A). z"
  , "    :let csucc = \\(n:CNat). \\(A:Type). \\(z:A). \\(s:Π(x:A). A)."
  , "                   s (n A z s)"
  , ""
  , "--- Polymorphic Functions ---"
  , ""
  , "13. Polymorphic Identity"
  , "    :let id = \\(A:Type). \\(x:A). x"
  , "    id Nat zero"
  , "    : Nat"
  , "    =  0"
  , ""
  , "    id Bool true"
  , "    : Bool"
  , "    =  true"
  , ""
  , "14. Polymorphic Const"
  , "    :let const = \\(A:Type). \\(B:Type). \\(x:A). \\(y:B). x"
  , "    const Nat Bool zero true"
  , "    : Nat"
  , "    =  0"
  , ""
  , "15. Apply Function"
  , "    :let apply = \\(A:Type). \\(B:Type). \\(f:Π(x:A). B). \\(x:A). f x"
  , "    :type apply"
  , "    : Π(A:Type). Π(B:Type). Π(f:Π(x:A). B). Π(x:A). B"
  , ""
  , "--- Type Checking Examples ---"
  , ""
  , "16. Well-Typed Dependent Function"
  , "    \\(b:Bool). \\(x:if b then Nat else Bool). x"
  , "    : Π(b:Bool). Π(x:if b then Nat else Bool). if b then Nat else Bool"
  , ""
  , "17. Dependent Pair with Dependent Type"
  , "    (true, zero)"
  , "    Can have type: Σ(b:Bool). if b then Nat else Bool"
  , ""
  , "18. Type-Level Computation"
  , "    :let NatOrBool = \\(b:Bool). if b then Nat else Bool"
  , "    :type NatOrBool"
  , "    : Π(b:Bool). Type"
  , ""
  , "    NatOrBool true"
  , "    : Type"
  , "    =  Nat"
  , ""
  , "--- Existential Types via Sigma ---"
  , ""
  , "19. Existential Package"
  , "    -- ∃A. A  ≅  Σ(A:Type). A"
  , "    (Nat, zero)"
  , "    : Σ(A:Type). A"
  , ""
  , "20. Heterogeneous List (Conceptual)"
  , "    -- HList = Σ(A:Type). Σ(x:A). Σ(B:Type). B"
  , "    -- Example: (Nat, zero, Bool, true)"
  , ""
  , "=== Key Concepts ==="
  , ""
  , "1. **Unified Syntax**: Types and terms are the same syntactic category"
  , "2. **Type : Type**: Universe (we use Type-in-Type for simplicity)"
  , "3. **Pi Types**: Π(x:A). B - function types where B can mention x"
  , "4. **Sigma Types**: Σ(x:A). B - pair types where B can mention x"
  , "5. **Dependent**: Types can depend on runtime values!"
  , "6. **Normalization**: Type equality uses normalization (computation in types)"
  , ""
  , "=== Differences from System F-omega ==="
  , ""
  , "1. No separate kind system - everything is a term"
  , "2. Types can depend on values (not just types on types)"
  , "3. Type equality via normalization (beta reduction)"
  , "4. Dependent pairs (Sigma types) in addition to dependent functions"
  , "5. Can encode much more: GADTs, existentials, refinement types"
  , ""
  , "=== Try It! ==="
  , ""
  , "Define a dependent function:"
  , "  :let f = \\(b:Bool). if b then zero else true"
  , "  :type f"
  , ""
  , "Create a type family:"
  , "  :let Family = \\(n:Nat). if (iszero n) then Bool else Nat"
  , "  :type Family"
  , "  Family zero"
  , "  Family (succ zero)"
  , ""
  , "Build dependent pairs:"
  , "  (Bool, true)"
  , "  (Nat, succ (succ zero))"
  ]
