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
  putStrLn "Homotopy Type Theory (HoTT) REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Identity types, path operations,"
  putStrLn "          J eliminator, transport, univalence concepts"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :normalize t       Fully normalize term t"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Type an expression to evaluate and type check it."
  putStrLn "Type :examples to see comprehensive HoTT examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "hott> "
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

  ("normalize" : rest) -> handleNormalize (unwords rest) >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
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
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let ctx = buildContext state
      case infer ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ prettyType ty

-- | Handle :step command
handleStep :: String -> IO ()
handleStep input = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      case evalStep t of
        Nothing -> putStrLn "  (no reduction possible)"
        Just t' -> putStrLn $ "  ⟶  " ++ prettyTerm t'

-- | Handle :steps command
handleSteps :: String -> REPLState -> IO ()
handleSteps input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let steps = generateEvalSteps t (maxSteps state)
      mapM_ (\(i, s) -> putStrLn $ "  " ++ show i ++ ". " ++ s) (zip [0::Int ..] steps)

-- | Handle :normalize command
handleNormalize :: String -> IO ()
handleNormalize input = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let nf = eval t
      putStrLn $ "  " ++ prettyTerm nf

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
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
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
  putStrLn "Homotopy Type Theory (HoTT) REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :normalize t       Fully normalize term t"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Types:"
  putStrLn "    Bool, Nat, Unit, Void  Base types"
  putStrLn "    Type                   Universe of small types"
  putStrLn "    T1 -> T2               Function type"
  putStrLn "    T1 * T2                Product type"
  putStrLn "    T1 + T2                Sum type"
  putStrLn "    Id T a b               Identity type (a =_T b)"
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
  putStrLn "    inl t as T, inr t as T Injections"
  putStrLn "    case t of ...          Case analysis"
  putStrLn "    let x = t1 in t2       Let binding"
  putStrLn ""
  putStrLn "  Path/Identity Operations:"
  putStrLn "    refl [T] t             Reflexivity: t =_T t"
  putStrLn "    sym p                  Symmetry: (a = b) → (b = a)"
  putStrLn "    trans p q              Transitivity: (a = b) → (b = c) → (a = c)"
  putStrLn "    ap f p                 Function application: (a = b) → (f a = f b)"
  putStrLn "    transport [P] p t      Transport: (a = b) → P a → P b"
  putStrLn "    J [C] base a b p       J eliminator (path induction)"
  putStrLn ""
  putStrLn "HoTT Concepts:"
  putStrLn "  • Identity types represent paths/equalities"
  putStrLn "  • refl proves reflexivity (every term equals itself)"
  putStrLn "  • Paths can be manipulated: sym, trans, ap"
  putStrLn "  • J eliminator: universal property of identity types"
  putStrLn "  • Transport: move along paths between types"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Homotopy Type Theory (HoTT) Examples"
  , "==========================================="
  , ""
  , "--- Basic Paths (Identity Types) ---"
  , ""
  , "1. Reflexivity - every term equals itself:"
  , "   refl [Nat] 0"
  , "   : Id Nat 0 0"
  , ""
  , "2. Reflexivity for booleans:"
  , "   refl [Bool] true"
  , "   : Id Bool true true"
  , ""
  , "3. Reflexivity for functions:"
  , "   :let id = \\x:Nat. x"
  , "   refl [Nat -> Nat] id"
  , "   : Id (Nat -> Nat) id id"
  , ""
  , "--- Path Symmetry ---"
  , ""
  , "4. Symmetric path - if a = b then b = a:"
  , "   sym (refl [Nat] 0)"
  , "   : Id Nat 0 0"
  , ""
  , "5. Symmetry preserves endpoints:"
  , "   :let p = refl [Bool] true"
  , "   sym p"
  , "   : Id Bool true true"
  , ""
  , "--- Path Transitivity (Composition) ---"
  , ""
  , "6. Transitivity - if a = b and b = c then a = c:"
  , "   trans (refl [Nat] 0) (refl [Nat] 0)"
  , "   : Id Nat 0 0"
  , ""
  , "7. Composing paths:"
  , "   :let p1 = refl [Nat] (succ 0)"
  , "   :let p2 = refl [Nat] (succ 0)"
  , "   trans p1 p2"
  , "   : Id Nat 1 1"
  , ""
  , "--- Function Application to Paths (ap) ---"
  , ""
  , "8. Applying a function to a path:"
  , "   ap (\\x:Nat. succ x) (refl [Nat] 0)"
  , "   : Id Nat (succ 0) (succ 0)"
  , ""
  , "9. ap preserves function application:"
  , "   :let f = \\x:Nat. succ (succ x)"
  , "   ap f (refl [Nat] 0)"
  , "   : Id Nat (f 0) (f 0)"
  , ""
  , "10. ap with boolean negation:"
  , "    :let not = \\b:Bool. if b then false else true"
  , "    ap not (refl [Bool] true)"
  , "    : Id Bool (not true) (not true)"
  , ""
  , "--- Transport ---"
  , ""
  , "11. Transport along a path in a type family:"
  , "    transport [\\x:Nat. Nat] (refl [Nat] 0) 0"
  , "    : Nat"
  , ""
  , "12. Transport preserves values along identity:"
  , "    :let P = \\x:Nat. Bool"
  , "    transport [P] (refl [Nat] 0) true"
  , "    : Bool"
  , ""
  , "--- J Eliminator (Path Induction) ---"
  , ""
  , "13. J eliminator - the fundamental operation on paths:"
  , "    The J eliminator says: to prove a property of paths,"
  , "    it suffices to prove it for reflexivity"
  , ""
  , "14. Basic use of J:"
  , "    J [Id Nat 0 0]"
  , "      (\\x:Nat. refl [Nat] x)"
  , "      0 0"
  , "      (refl [Nat] 0)"
  , "    : Id Nat 0 0"
  , ""
  , "15. J can prove path symmetry:"
  , "    The J eliminator can derive sym, trans, ap, etc."
  , ""
  , "--- Products and Paths ---"
  , ""
  , "16. Paths in product types:"
  , "    refl [Nat * Bool] <0, true>"
  , "    : Id (Nat * Bool) <0, true> <0, true>"
  , ""
  , "17. Paths respect projections:"
  , "    :let pair = <succ 0, false>"
  , "    ap fst (refl [Nat * Bool] pair)"
  , "    : Id Nat (fst pair) (fst pair)"
  , ""
  , "--- Sums and Paths ---"
  , ""
  , "18. Paths in sum types:"
  , "    refl [Nat + Bool] (inl 0 as Nat + Bool)"
  , "    : Id (Nat + Bool) (inl 0 as Nat + Bool) (inl 0 as Nat + Bool)"
  , ""
  , "19. Paths in right injection:"
  , "    refl [Nat + Bool] (inr true as Nat + Bool)"
  , "    : Id (Nat + Bool) (inr true as Nat + Bool) (inr true as Nat + Bool)"
  , ""
  , "--- Function Types and Paths ---"
  , ""
  , "20. Paths between functions (function extensionality):"
  , "    :let f = \\x:Nat. x"
  , "    :let g = \\x:Nat. x"
  , "    refl [Nat -> Nat] f"
  , "    : Id (Nat -> Nat) f f"
  , ""
  , "21. ap with higher-order functions:"
  , "    :let apply = \\f:Nat -> Nat. f 0"
  , "    ap apply (refl [Nat -> Nat] (\\x:Nat. x))"
  , "    : Id Nat (apply (\\x:Nat. x)) (apply (\\x:Nat. x))"
  , ""
  , "--- Combining Operations ---"
  , ""
  , "22. Symmetry and transitivity together:"
  , "    :let p = refl [Nat] 0"
  , "    trans p (sym p)"
  , "    : Id Nat 0 0"
  , ""
  , "23. Apply function to symmetric path:"
  , "    :let p = refl [Nat] (succ 0)"
  , "    ap (\\x:Nat. pred x) (sym p)"
  , "    : Id Nat (pred 1) (pred 1)"
  , ""
  , "24. Nested path operations:"
  , "    trans (sym (refl [Nat] 0)) (refl [Nat] 0)"
  , "    : Id Nat 0 0"
  , ""
  , "--- Higher Groupoid Structure ---"
  , ""
  , "25. Paths form a groupoid:"
  , "    - Identity: refl"
  , "    - Inverse: sym"
  , "    - Composition: trans"
  , ""
  , "26. trans is associative (up to higher paths):"
  , "    :let p = refl [Nat] 0"
  , "    :let q = refl [Nat] 0"
  , "    :let r = refl [Nat] 0"
  , "    trans (trans p q) r"
  , "    trans p (trans q r)"
  , ""
  , "--- Unit Type and Paths ---"
  , ""
  , "27. All inhabitants of Unit are equal (contractibility):"
  , "    refl [Unit] unit"
  , "    : Id Unit unit unit"
  , ""
  , "28. This expresses that Unit is contractible:"
  , "    Every element of Unit equals unit"
  , ""
  , "--- Empty Type (Void) ---"
  , ""
  , "29. Void has no inhabitants, so vacuous paths:"
  , "    :type \\x:Void. \\y:Void. refl [Void] x"
  , "    : Void -> Void -> Id Void x x"
  , ""
  , "30. absurd eliminates Void:"
  , "    :type \\x:Void. absurd [Nat] x"
  , "    : Void -> Nat"
  , ""
  , "--- Univalence Concepts (Informal) ---"
  , ""
  , "31. Univalence axiom (not fully implemented):"
  , "    Equivalence of types is equivalent to equality of types"
  , "    (A ≃ B) ≃ (A = B)"
  , ""
  , "32. This means isomorphic types are equal (Path-wise)"
  , ""
  , "--- Evaluation and Normalization ---"
  , ""
  , "33. Watch path operations evaluate:"
  , "    :steps sym (refl [Nat] 0)"
  , ""
  , "34. See how ap evaluates:"
  , "    :steps ap (\\x:Nat. succ x) (refl [Nat] 0)"
  , ""
  , "35. Normalize complex path expression:"
  , "    :normalize trans (sym (refl [Bool] true)) (refl [Bool] true)"
  , ""
  , "--- Let Bindings for Complex Proofs ---"
  , ""
  , "36. Build up complex proofs incrementally:"
  , "    :let n = succ (succ 0)"
  , "    :let p = refl [Nat] n"
  , "    :let q = ap (\\x:Nat. succ x) p"
  , "    trans p q"
  , ""
  , "37. Define reusable functions:"
  , "    :let double = \\x:Nat. succ (succ x)"
  , "    :let path = refl [Nat] (succ 0)"
  , "    ap double path"
  , ""
  , "==========================================="
  , "Key HoTT Concepts"
  , "==========================================="
  , ""
  , "• **Identity Types**: Id A a b represents a path from a to b in type A"
  , "• **refl**: Reflexivity - every term has a path to itself"
  , "• **sym**: Symmetry - paths can be reversed"
  , "• **trans**: Transitivity - paths can be composed"
  , "• **ap**: Functoriality - functions preserve paths"
  , "• **transport**: Move data along paths between types"
  , "• **J eliminator**: Universal property - to prove something"
  , "                    about all paths, prove it for refl"
  , "• **Higher structure**: Paths between paths (2-paths, 3-paths, ...)"
  , "• **Univalence**: Isomorphic types are equal (not fully shown here)"
  , ""
  , "==========================================="
  , "Mathematical Interpretation"
  , "==========================================="
  , ""
  , "In HoTT, types are viewed as spaces and terms as points:"
  , "• A type A is like a topological space"
  , "• A term a : A is like a point in that space"
  , "• A path p : Id A a b is like a continuous path from a to b"
  , "• refl is the constant path (stay at a point)"
  , "• sym reverses a path"
  , "• trans concatenates paths"
  , "• Higher paths are homotopies between paths"
  , ""
  , "This creates a rich structure where:"
  , "• Types form ∞-groupoids"
  , "• Equality is proof-relevant (paths carry information)"
  , "• Univalence connects type equivalence with type equality"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Create basic paths:"
  , "   refl [Nat] (succ (succ 0))"
  , ""
  , "2. Manipulate paths:"
  , "   :let p = refl [Bool] true"
  , "   sym p"
  , "   trans p (sym p)"
  , ""
  , "3. Apply functions to paths:"
  , "   :let f = \\x:Nat. succ (succ x)"
  , "   ap f (refl [Nat] 0)"
  , ""
  , "4. Use transport:"
  , "   transport [\\x:Nat. Bool] (refl [Nat] 0) true"
  , ""
  , "5. Explore the J eliminator:"
  , "   J [Id Nat 0 0] (\\x:Nat. refl [Nat] x) 0 0 (refl [Nat] 0)"
  , ""
  , "6. Build complex proofs with :let"
  , ""
  , "==========================================="
  , "Further Reading"
  , "==========================================="
  , ""
  , "• HoTT Book: https://homotopytypetheory.org/book/"
  , "• Cubical Agda: https://agda.readthedocs.io/en/latest/language/cubical.html"
  , "• Univalent Foundations: https://ncatlab.org/nlab/show/univalent+foundations"
  , ""
  ]
