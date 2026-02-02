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
  { bindings :: Map String Term
  , typeAnnotations :: Map String Term
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
  putStrLn "==========================================="
  putStrLn "Full Dependent Types REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Universe hierarchy, equality types, and eliminators"
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
  putStrLn "Type :examples to see comprehensive examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "λU> "
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
handleNormalize input _state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let normalized = normalize t
      putStrLn $ "  =  " ++ pretty normalized

-- | Single-step evaluation (using locally defined step function)
singleStep :: Term -> Maybe Term
singleStep = \case
  -- Beta reduction
  App (Lam x _ body) arg | isValue arg -> Just (subst x arg body)
  App t1 t2 | not (isValue t1) -> App <$> singleStep t1 <*> pure t2
  App v1 t2 | isValue v1, not (isValue t2) -> App v1 <$> singleStep t2

  -- Pair projections
  Fst (Pair v1 _) | isValue v1 -> Just v1
  Fst t | not (isValue t) -> Fst <$> singleStep t
  Snd (Pair _ v2) | isValue v2 -> Just v2
  Snd t | not (isValue t) -> Snd <$> singleStep t

  -- Reduce inside pairs
  Pair t1 t2 | not (isValue t1) -> Pair <$> singleStep t1 <*> pure t2
  Pair v1 t2 | isValue v1, not (isValue t2) -> Pair v1 <$> singleStep t2

  -- Pattern matching
  Match v branches | isValue v -> tryMatch v branches
  Match t branches | not (isValue t) -> (\t' -> Match t' branches) <$> singleStep t

  -- Nat eliminator
  NatElim _ z _ Zero -> Just z
  NatElim p z s (Succ n) | isValue n -> Just (App (App s n) (NatElim p z s n))
  NatElim p z s t | not (isValue t) -> NatElim p z s <$> singleStep t

  -- Bool eliminator
  BoolElim _ t _ TmTrue -> Just t
  BoolElim _ _ f TmFalse -> Just f
  BoolElim p t f b | not (isValue b) -> BoolElim p t f <$> singleStep b

  -- Unit eliminator
  UnitElim _ u TT -> Just u
  UnitElim p u x | not (isValue x) -> UnitElim p u <$> singleStep x

  -- J eliminator (equality)
  J _ _ p _ _ (Refl x) -> Just (App p x)
  J a c p x y eq | not (isValue eq) -> (\eq' -> J a c p x y eq') <$> singleStep eq

  -- Succ
  Succ t | not (isValue t) -> Succ <$> singleStep t

  -- No reduction
  _ -> Nothing
  where
    -- Try to match against patterns
    tryMatch :: Term -> [(Pattern, Term)] -> Maybe Term
    tryMatch _ [] = Nothing
    tryMatch v ((pat, rhs):rest) =
      case matchPattern pat v of
        Just matchBindings -> Just (applyBindings matchBindings rhs)
        Nothing -> tryMatch v rest

    -- Apply bindings from pattern matching
    applyBindings :: Map Name Term -> Term -> Term
    applyBindings bindingsMap t = Map.foldrWithKey subst t bindingsMap

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
  putStrLn "Full Dependent Types REPL Commands:"
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
  putStrLn "  Type, Type1, Type2, ...  Universe hierarchy"
  putStrLn "  x                        Variable"
  putStrLn "  \\(x:A). t                 Lambda abstraction"
  putStrLn "  t₁ t₂                     Application"
  putStrLn "  Π(x:A). B                Dependent function type"
  putStrLn "  Σ(x:A). B                Dependent pair type"
  putStrLn "  (t₁, t₂)                  Pair"
  putStrLn "  fst t, snd t             Projections"
  putStrLn "  Eq A x y                 Equality type (x = y in A)"
  putStrLn "  refl x                   Reflexivity proof"
  putStrLn "  J(A, C, p, x, y, eq)     J eliminator for equality"
  putStrLn "  natElim(P, z, s, n)      Nat eliminator"
  putStrLn "  boolElim(P, t, f, b)     Bool eliminator"
  putStrLn "  unitElim(P, u, x)        Unit eliminator"
  putStrLn "  emptyElim(P, e)          Empty eliminator"
  putStrLn "  Nat, Bool, Unit, Empty   Base types"

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Full Dependent Types Examples"
  , "==========================================="
  , ""
  , "--- Universe Hierarchy ---"
  , ""
  , "1. Type Levels"
  , "   Type"
  , "   : Type1"
  , ""
  , "   Type1"
  , "   : Type2"
  , ""
  , "   Type2"
  , "   : Type3"
  , ""
  , "2. Type of Function Types"
  , "   :type Π(A:Type). A -> A"
  , "   : Type1"
  , ""
  , "--- Propositional Equality ---"
  , ""
  , "3. Equality Type"
  , "   Eq Nat zero zero"
  , "   : Type"
  , "   (The type of proofs that 0 = 0)"
  , ""
  , "4. Reflexivity"
  , "   refl zero"
  , "   : Eq Nat zero zero"
  , "   (Proof that 0 = 0)"
  , ""
  , "5. Symmetry (via J)"
  , "   :let sym = \\(A:Type). \\(x:A). \\(y:A). \\(eq:Eq A x y)."
  , "                J(A, \\(z:A). \\(e:Eq A x z). Eq A z x,"
  , "                  refl x, x, y, eq)"
  , "   sym : Π(A:Type). Π(x:A). Π(y:A). Π(eq:Eq A x y). Eq A y x"
  , ""
  , "6. Transitivity (via J)"
  , "   -- If x = y and y = z, then x = z"
  , "   :let trans = \\(A:Type). \\(x:A). \\(y:A). \\(z:A)."
  , "                  \\(eq1:Eq A x y). \\(eq2:Eq A y z)."
  , "                  J(A, \\(w:A). \\(e:Eq A x w). Eq A x z,"
  , "                    eq2, x, y, eq1)"
  , ""
  , "7. Congruence (via J)"
  , "   -- If x = y, then f x = f y"
  , "   :let cong = \\(A:Type). \\(B:Type). \\(f:A -> B)."
  , "                 \\(x:A). \\(y:A). \\(eq:Eq A x y)."
  , "                 J(A, \\(z:A). \\(e:Eq A x z). Eq B (f x) (f z),"
  , "                   refl (f x), x, y, eq)"
  , ""
  , "--- Natural Number Eliminator ---"
  , ""
  , "8. Addition via natElim"
  , "   :let add = \\(m:Nat). natElim(\\(n:Nat). Nat, m,"
  , "                                   \\(k:Nat). \\(rec:Nat). succ rec,"
  , "                                   m)"
  , "   add : Nat → Nat → Nat"
  , ""
  , "9. Multiplication"
  , "   :let mul = \\(m:Nat). \\(n:Nat)."
  , "                natElim(\\(x:Nat). Nat, zero,"
  , "                        \\(k:Nat). \\(rec:Nat). add m rec,"
  , "                        n)"
  , ""
  , "10. Is Zero Predicate"
  , "    :let isZeroPred = natElim(\\(n:Nat). Bool, true,"
  , "                                \\(k:Nat). \\(rec:Bool). false,"
  , "                                (succ zero))"
  , "    =  false"
  , ""
  , "--- Boolean Eliminator ---"
  , ""
  , "11. Not Function"
  , "    :let not = \\(b:Bool). boolElim(\\(x:Bool). Bool, false, true, b)"
  , "    not true"
  , "    : Bool"
  , "    =  false"
  , ""
  , "12. And Function"
  , "    :let and = \\(a:Bool). \\(b:Bool)."
  , "                 boolElim(\\(x:Bool). Bool, b, false, a)"
  , ""
  , "--- Dependent Predicates ---"
  , ""
  , "13. Even Predicate (Type Family)"
  , "    :let Even = \\(n:Nat). Eq Nat (mul (succ (succ zero)) n) n"
  , "    Even : Nat → Type"
  , ""
  , "14. Vector Type (Conceptual)"
  , "    -- Vec : Type → Nat → Type"
  , "    -- nil  : Π(A:Type). Vec A zero"
  , "    -- cons : Π(A:Type). Π(n:Nat). A → Vec A n → Vec A (succ n)"
  , "    (Requires inductive type definitions)"
  , ""
  , "--- Unit and Empty Types ---"
  , ""
  , "15. Unit Type"
  , "    TT"
  , "    : Unit"
  , ""
  , "    unitElim(\\(x:Unit). Nat, zero, TT)"
  , "    : Nat"
  , "    =  zero"
  , ""
  , "16. Empty Type (Absurdity)"
  , "    -- Ex falso quodlibet: from false, anything follows"
  , "    :let exFalso = \\(A:Type). \\(e:Empty). emptyElim(\\(x:Empty). A, e)"
  , "    exFalso : Π(A:Type). Π(e:Empty). A"
  , ""
  , "--- Sigma Types (Dependent Pairs) ---"
  , ""
  , "17. Subset Type"
  , "    -- {n:Nat | Even n}  ≅  Σ(n:Nat). Even n"
  , "    :let EvenNat = Σ(n:Nat). Eq Nat (mul (succ (succ zero)) n) n"
  , ""
  , "18. Dependent Pair Example"
  , "    (zero, refl zero)"
  , "    : Σ(x:Nat). Eq Nat x x"
  , ""
  , "--- Polymorphic Functions ---"
  , ""
  , "19. Polymorphic Identity"
  , "    :let id = \\(A:Type). \\(x:A). x"
  , "    id Nat zero"
  , "    : Nat"
  , "    =  0"
  , ""
  , "20. Composition"
  , "    :let comp = \\(A:Type). \\(B:Type). \\(C:Type)."
  , "                  \\(g:B -> C). \\(f:A -> B). \\(x:A). g (f x)"
  , "    comp : Π(A:Type). Π(B:Type). Π(C:Type)."
  , "           (B → C) → (A → B) → A → C"
  , ""
  , "--- Proof Examples ---"
  , ""
  , "21. Prove 0 = 0"
  , "    refl zero"
  , "    : Eq Nat zero zero"
  , ""
  , "22. Prove true = true"
  , "    refl true"
  , "    : Eq Bool true true"
  , ""
  , "23. Use J to Transport"
  , "    -- If x = y and P x holds, then P y holds"
  , "    :let transport = \\(A:Type). \\(P:A -> Type)."
  , "                       \\(x:A). \\(y:A). \\(eq:Eq A x y). \\(px:P x)."
  , "                       J(A, \\(z:A). \\(e:Eq A x z). P z, px, x, y, eq)"
  , ""
  , "--- Church Encodings ---"
  , ""
  , "24. Church Booleans"
  , "    :let CBool = Π(A:Type). A -> A -> A"
  , "    :let ctrue = \\(A:Type). \\(t:A). \\(f:A). t"
  , "    :let cfalse = \\(A:Type). \\(t:A). \\(f:A). f"
  , ""
  , "25. Church Naturals"
  , "    :let CNat = Π(A:Type). (A -> A) -> A -> A"
  , "    :let czero = \\(A:Type). \\(s:A -> A). \\(z:A). z"
  , "    :let csucc = \\(n:CNat). \\(A:Type). \\(s:A -> A). \\(z:A)."
  , "                   s (n A s z)"
  , ""
  , "==================================="
  , "Key Features"
  , "==================================="
  , ""
  , "1. **Universe Hierarchy**: Type : Type1 : Type2 : ..."
  , "2. **Propositional Equality**: Eq A x y is the type of proofs"
  , "3. **J Eliminator**: Pattern matching on equality proofs"
  , "4. **Eliminators**: natElim, boolElim, unitElim, emptyElim"
  , "5. **Empty Type**: Uninhabited type for contradictions"
  , "6. **Curry-Howard**: Proofs are programs, propositions are types"
  , ""
  , "=== What Can You Do? ==="
  , ""
  , "• Prove theorems about equality (symmetry, transitivity, congruence)"
  , "• Define recursive functions via eliminators"
  , "• Create dependent types that compute (type families)"
  , "• Encode subset types using Sigma types"
  , "• Reason about programs using equality proofs"
  , "• Express \"there exists\" via Sigma types"
  , "• Foundation for systems like Agda, Coq, Lean, Idris"
  , ""
  , "=== Try It! ==="
  , ""
  , "Prove symmetry of equality:"
  , "  :let sym = \\(A:Type). \\(x:A). \\(y:A). \\(eq:Eq A x y)."
  , "               J(A, \\(z:A). \\(e:Eq A x z). Eq A z x, refl x, x, y, eq)"
  , "  :type sym"
  , ""
  , "Define addition:"
  , "  :let add = \\(m:Nat). \\(n:Nat)."
  , "               natElim(\\(x:Nat). Nat, m, \\(k:Nat). \\(rec:Nat). succ rec, n)"
  , "  add (succ zero) (succ zero)"
  ]
