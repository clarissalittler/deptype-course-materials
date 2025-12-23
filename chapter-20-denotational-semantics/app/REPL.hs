{-# LANGUAGE LambdaCase #-}

module REPL (runREPL) where

import Syntax
import Parser
import Pretty
import Domain
import Denotation

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import System.IO (hFlush, stdout)
import Control.Exception (catch, IOException)
import GHC.IO.Exception (IOErrorType(..))
import System.IO.Error (ioeGetErrorType)

-- | REPL State
data REPLState = REPLState
  { termBindings :: Map String Term
  , domBindings :: Map String Dom
  , showSteps :: Bool
  }

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { termBindings = Map.empty
  , domBindings = Map.empty
  , showSteps = False
  }

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║     Denotational Semantics Explorer - Chapter 20                  ║"
  putStrLn "╠═══════════════════════════════════════════════════════════════════╣"
  putStrLn "║  The denotation [[·]] maps syntax to semantic domains.            ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Key insight: [[fix f]] = ⊔ₙ fⁿ(⊥), the least fixed point of f   ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Commands:                                                        ║"
  putStrLn "║    <term>              - Compute denotation                       ║"
  putStrLn "║    :help               - Show help message                        ║"
  putStrLn "║    :examples           - Show comprehensive examples              ║"
  putStrLn "║    :theory             - Show domain theory concepts              ║"
  putStrLn "║    :quit               - Exit the REPL                            ║"
  putStrLn "║    :let x = <term>     - Bind term to variable                    ║"
  putStrLn "║    :denote <term>      - Compute denotation                       ║"
  putStrLn "║    :eval <term>        - Alias for :denote                        ║"
  putStrLn "║    :fix n <term>       - Show n iterations of fixed point         ║"
  putStrLn "║    :fact n             - Compute factorial(n)                     ║"
  putStrLn "║    :fib n              - Compute fibonacci(n)                     ║"
  putStrLn "║    :env                - Show current bindings                    ║"
  putStrLn "║    :reset              - Reset all bindings                       ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "Type a term to compute its denotation, or :examples for examples."
  putStrLn ""
  repl initialState

-- | REPL loop
repl :: REPLState -> IO ()
repl state = do
  putStr "den> "
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
  ["theory"] -> showTheory >> return state
  ["quit"] -> putStrLn "Goodbye!" >> error "quit"
  ["env"] -> showEnv state >> return state
  ["reset"] -> putStrLn "Bindings reset." >> return initialState

  ("let" : x : "=" : rest) -> handleLetBinding x (unwords rest) state

  ("denote" : rest) -> handleDenote (unwords rest) state >> return state
  ("eval" : rest) -> handleDenote (unwords rest) state >> return state

  ("type" : rest) -> handleType (unwords rest) >> return state

  ("step" : _) -> do
    putStrLn "Note: Denotational semantics is not based on operational steps."
    putStrLn "Use :denote to compute the semantic value, or :fix to see fixed point iterations."
    return state

  ("steps" : _) -> do
    putStrLn "Note: Denotational semantics is not based on operational steps."
    putStrLn "Use :denote to compute the semantic value, or :fix to see fixed point iterations."
    return state

  ("fix" : rest) -> handleFixIterations (unwords rest) >> return state

  ("fact" : rest) -> handleFactorial (unwords rest) >> return state

  ("fib" : rest) -> handleFibonacci (unwords rest) >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd ++ "\nType :help for available commands.") >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      let env = buildEnv state
      let d = denote env t
      putStrLn $ x ++ " = " ++ prettyTerm t
      putStrLn $ "[[" ++ x ++ "]] = " ++ prettyDom d
      return state
        { termBindings = Map.insert x t (termBindings state)
        , domBindings = Map.insert x d (domBindings state)
        }

-- | Handle :denote command
handleDenote :: String -> REPLState -> IO ()
handleDenote input state = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      let env = buildEnv state
      putStrLn $ "Term:  " ++ prettyTerm t
      let d = denote env t
      putStrLn $ "[[·]] = " ++ prettyDom d

-- | Handle :type command
handleType :: String -> IO ()
handleType input = do
  case parseTerm input of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right t -> do
      putStrLn $ "Term: " ++ prettyTerm t
      case inferType t of
        Just ty -> putStrLn $ "Type: " ++ prettyType ty
        Nothing -> putStrLn "Type: (type inference not fully implemented)"

-- | Simple type inference (basic)
inferType :: Term -> Maybe Type
inferType = \case
  Var _ -> Nothing
  Lam _ ty _ -> Just (TyArr ty TyUnit)  -- Simplified
  App _ _ -> Nothing
  Let _ _ e -> inferType e
  Fix _ -> Nothing
  TmTrue -> Just TyBool
  TmFalse -> Just TyBool
  If _ _ _ -> Nothing
  Zero -> Just TyNat
  Suc _ -> Just TyNat
  Pred _ -> Just TyNat
  IsZero _ -> Just TyBool
  NatRec _ _ _ -> Nothing
  TmUnit -> Just TyUnit
  Bottom ty -> Just ty

-- | Handle :fix command - show fixed point iterations
handleFixIterations :: String -> IO ()
handleFixIterations input = do
  let (nStr, rest) = break (== ' ') input
  case reads nStr :: [(Int, String)] of
    [(n, "")] -> case parseTerm (dropWhile (== ' ') rest) of
      Left err -> putStrLn $ "Parse error: " ++ err
      Right term -> do
        putStrLn $ "Computing fixed point iterations for: " ++ prettyTerm term
        let d = denoteClosed term
        case d of
          DFun f -> do
            putStrLn "Chain: ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ f³(⊥) ⊑ ..."
            putStrLn ""
            mapM_ (showIteration f) [0..n]
          _ -> putStrLn "Error: expected function term"
      where
        showIteration f i = do
          let approxI = fixN i f
          putStrLn $ "f^" ++ show i ++ "(⊥) = " ++ prettyDom approxI
    _ -> putStrLn "Usage: :fix N <function-term>\nExample: :fix 5 \\(f : Nat -> Nat). \\(x : Nat). if iszero x then 1 else x"

-- | Handle :fact command
handleFactorial :: String -> IO ()
handleFactorial input = do
  case reads input :: [(Integer, String)] of
    [(n, "")] -> do
      putStrLn $ "Computing factorial(" ++ show n ++ ")..."
      let result = factorialDen n
      putStrLn $ "[[fact]](" ++ show n ++ ") = " ++ prettyDom result
    _ -> putStrLn "Usage: :fact N\nExample: :fact 5"

-- | Handle :fib command
handleFibonacci :: String -> IO ()
handleFibonacci input = do
  case reads input :: [(Integer, String)] of
    [(n, "")] -> do
      putStrLn $ "Computing fibonacci(" ++ show n ++ ")..."
      let result = fibonacciDen n
      putStrLn $ "[[fib]](" ++ show n ++ ") = " ++ prettyDom result
    _ -> putStrLn "Usage: :fib N\nExample: :fib 10"

-- | Handle term input
handleInput :: String -> REPLState -> IO REPLState
handleInput input state = do
  case parseTerm input of
    Left err -> putStrLn ("Parse error: " ++ err) >> return state
    Right t -> do
      let env = buildEnv state
      let d = denote env t
      putStrLn $ "  [[·]] = " ++ prettyDom d
      return state

-- | Build environment from bindings
buildEnv :: REPLState -> Env
buildEnv state = Map.foldlWithKey (\env x d -> extendEnv x d env) emptyEnv (domBindings state)

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Current bindings:"
  if Map.null (termBindings state)
    then putStrLn "  (none)"
    else mapM_ showBinding (Map.toList $ termBindings state)
  where
    showBinding (x, t) = case Map.lookup x (domBindings state) of
      Just d -> putStrLn $ "  " ++ x ++ " = " ++ prettyTerm t ++ "  →  [[" ++ x ++ "]] = " ++ prettyDom d
      Nothing -> putStrLn $ "  " ++ x ++ " = " ++ prettyTerm t

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║                    Denotational Semantics REPL                    ║"
  putStrLn "╠═══════════════════════════════════════════════════════════════════╣"
  putStrLn "║                                                                   ║"
  putStrLn "║  The denotation [[e]] maps syntax to semantic domains.            ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Key equations:                                                   ║"
  putStrLn "║    [[x]]ρ = ρ(x)                           (variable lookup)      ║"
  putStrLn "║    [[λx:A. e]]ρ = λd. [[e]]ρ[x↦d]         (abstraction)           ║"
  putStrLn "║    [[e1 e2]]ρ = [[e1]]ρ([[e2]]ρ)          (application)           ║"
  putStrLn "║    [[fix f]]ρ = ⊔ₙ ([[f]]ρ)ⁿ(⊥)           (least fixed point)     ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Commands:                                                        ║"
  putStrLn "║    <term>              Compute denotation of term                 ║"
  putStrLn "║    :help               Show this help message                     ║"
  putStrLn "║    :examples           Show comprehensive examples                ║"
  putStrLn "║    :theory             Show domain theory concepts                ║"
  putStrLn "║    :quit               Exit the REPL                              ║"
  putStrLn "║    :let x = <term>     Bind term to variable x                    ║"
  putStrLn "║    :denote <term>      Explicitly compute denotation              ║"
  putStrLn "║    :eval <term>        Alias for :denote                          ║"
  putStrLn "║    :type <term>        Show type of term (if inferrable)          ║"
  putStrLn "║    :fix n <term>       Show n iterations of fixed point           ║"
  putStrLn "║    :fact n             Compute factorial(n) using fix             ║"
  putStrLn "║    :fib n              Compute fibonacci(n) using fix             ║"
  putStrLn "║    :env                Show current bindings                      ║"
  putStrLn "║    :reset              Reset all bindings                         ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Syntax:                                                          ║"
  putStrLn "║    \\(x : T). e  or  λ(x : T). e    Lambda abstraction            ║"
  putStrLn "║    e1 e2                            Application                   ║"
  putStrLn "║    fix e                            Fixed point (for recursion)   ║"
  putStrLn "║    let x = e1 in e2                 Let binding                   ║"
  putStrLn "║    if c then t else e               Conditional                   ║"
  putStrLn "║    0, suc n, pred n                 Natural numbers               ║"
  putStrLn "║    iszero n                         Zero test                     ║"
  putStrLn "║    natrec z s n                     Primitive recursion           ║"
  putStrLn "║    true, false                      Booleans                      ║"
  putStrLn "║    (), unit                         Unit value                    ║"
  putStrLn "║    ⊥ T  or  bottom T                Explicit bottom of type T     ║"
  putStrLn "║                                                                   ║"
  putStrLn "║  Types:                                                           ║"
  putStrLn "║    Bool                             Boolean type                  ║"
  putStrLn "║    Nat                              Natural number type           ║"
  putStrLn "║    Unit                             Unit type                     ║"
  putStrLn "║    A -> B                           Function type                 ║"
  putStrLn "║                                                                   ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""

-- | Show domain theory concepts
showTheory :: IO ()
showTheory = do
  putStrLn ""
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║                       Domain Theory Primer                        ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "DOMAINS (Complete Partial Orders - CPOs)"
  putStrLn "  A domain D is a set equipped with:"
  putStrLn "  • A partial order ⊑ (approximation/information ordering)"
  putStrLn "  • A least element ⊥ (bottom = undefined/non-terminating)"
  putStrLn "  • Suprema (⊔) of all directed sets (chains converge)"
  putStrLn ""
  putStrLn "FLAT DOMAINS"
  putStrLn "  For base types like Nat and Bool, we use flat domains:"
  putStrLn ""
  putStrLn "        0   1   2   3   4  ...  (all incomparable)"
  putStrLn "         \\  |  /   /   /"
  putStrLn "          \\ | /   /   /"
  putStrLn "           \\|/   /   /"
  putStrLn "            ⊥          (only ⊥ is below everything)"
  putStrLn ""
  putStrLn "  In a flat domain:"
  putStrLn "    ⊥ ⊑ n  for all defined n"
  putStrLn "    n ⊑ m  iff  n = m (for defined values)"
  putStrLn ""
  putStrLn "FUNCTION DOMAINS [A → B]"
  putStrLn "  The function space consists of all Scott-continuous functions."
  putStrLn ""
  putStrLn "  Continuous means: f preserves suprema of directed sets"
  putStrLn "    If D is directed, then f(⊔D) = ⊔{f(d) | d ∈ D}"
  putStrLn ""
  putStrLn "  Ordered pointwise:"
  putStrLn "    f ⊑ g  iff  ∀x. f(x) ⊑ g(x)"
  putStrLn ""
  putStrLn "  The least element ⊥ₐ→ᵦ is the constantly-⊥ function:"
  putStrLn "    ⊥ₐ→ᵦ(x) = ⊥ᵦ  for all x"
  putStrLn ""
  putStrLn "LEAST FIXED POINTS"
  putStrLn "  For a continuous function f : D → D, the least fixed point is:"
  putStrLn ""
  putStrLn "    fix f = ⊔ₙ fⁿ(⊥)"
  putStrLn ""
  putStrLn "  This is the Kleene fixed point theorem. The chain:"
  putStrLn ""
  putStrLn "    ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ f³(⊥) ⊑ f⁴(⊥) ⊑ ..."
  putStrLn ""
  putStrLn "  is a directed set, and its supremum is the least fixed point."
  putStrLn ""
  putStrLn "  Each iteration gives a better approximation:"
  putStrLn "    f⁰(⊥) = ⊥           (no information)"
  putStrLn "    f¹(⊥) = f(⊥)        (one unfolding)"
  putStrLn "    f²(⊥) = f(f(⊥))     (two unfoldings)"
  putStrLn "    ..."
  putStrLn ""
  putStrLn "WHY FIXED POINTS MATTER"
  putStrLn "  Recursive definitions are fixed point equations!"
  putStrLn ""
  putStrLn "  Example: factorial"
  putStrLn "    fact = λn. if iszero n then 1 else n * fact(n-1)"
  putStrLn ""
  putStrLn "  Rewritten:"
  putStrLn "    fact = F(fact)"
  putStrLn "  where"
  putStrLn "    F = λf. λn. if iszero n then 1 else n * f(n-1)"
  putStrLn ""
  putStrLn "  So: fact = fix F"
  putStrLn ""
  putStrLn "  The denotation [[fact]] is the least function satisfying:"
  putStrLn "    [[fact]](0) = 1"
  putStrLn "    [[fact]](n+1) = (n+1) * [[fact]](n)"
  putStrLn ""
  putStrLn "APPROXIMATION SEQUENCE"
  putStrLn "  For factorial F, the iterations are:"
  putStrLn ""
  putStrLn "    F⁰(⊥) = ⊥                     (fact undefined everywhere)"
  putStrLn "    F¹(⊥)(0) = 1, F¹(⊥)(n) = ⊥    (fact defined only at 0)"
  putStrLn "    F²(⊥)(0) = 1, F²(⊥)(1) = 1    (fact defined at 0, 1)"
  putStrLn "    F³(⊥)(0) = 1, F³(⊥)(1) = 1,   (fact defined at 0, 1, 2)"
  putStrLn "          F³(⊥)(2) = 2"
  putStrLn "    ..."
  putStrLn ""
  putStrLn "  The supremum defines fact at all natural numbers."
  putStrLn ""
  putStrLn "KEY INSIGHT"
  putStrLn "  Denotational semantics makes the meaning of programs precise"
  putStrLn "  by mapping them to mathematical objects (domains)."
  putStrLn ""
  putStrLn "  Recursion is modeled via least fixed points, which are"
  putStrLn "  computed as limits of approximations."
  putStrLn ""
  putStrLn "  This is why non-termination (⊥) is fundamental:"
  putStrLn "  we start from ⊥ and iterate towards the answer!"
  putStrLn ""

-- | Show comprehensive examples
showExamples :: IO ()
showExamples = do
  putStrLn ""
  putStrLn "╔═══════════════════════════════════════════════════════════════════╗"
  putStrLn "║              Denotational Semantics Examples                      ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════════╝"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "1. BASIC VALUES"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Boolean values:"
  putStrLn "  true"
  putStrLn "  [[·]] = True"
  putStrLn ""
  putStrLn "  false"
  putStrLn "  [[·]] = False"
  putStrLn ""
  putStrLn "Natural numbers:"
  putStrLn "  0"
  putStrLn "  [[·]] = 0"
  putStrLn ""
  putStrLn "  suc (suc (suc 0))"
  putStrLn "  [[·]] = 3"
  putStrLn ""
  putStrLn "Numeric literals:"
  putStrLn "  42"
  putStrLn "  [[·]] = 42"
  putStrLn ""
  putStrLn "Unit value:"
  putStrLn "  ()"
  putStrLn "  [[·]] = ()"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "2. LAMBDA ABSTRACTION"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Identity function:"
  putStrLn "  \\(x : Nat). x"
  putStrLn "  [[·]] = <function>"
  putStrLn ""
  putStrLn "Apply identity:"
  putStrLn "  (\\(x : Nat). x) 5"
  putStrLn "  [[·]] = 5"
  putStrLn ""
  putStrLn "Constant function:"
  putStrLn "  \\(x : Nat). 42"
  putStrLn "  [[·]] = <function>"
  putStrLn ""
  putStrLn "Apply constant:"
  putStrLn "  (\\(x : Nat). 42) 0"
  putStrLn "  [[·]] = 42"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "3. ARITHMETIC"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Successor:"
  putStrLn "  suc 5"
  putStrLn "  [[·]] = 6"
  putStrLn ""
  putStrLn "Predecessor:"
  putStrLn "  pred 5"
  putStrLn "  [[·]] = 4"
  putStrLn ""
  putStrLn "Predecessor of zero:"
  putStrLn "  pred 0"
  putStrLn "  [[·]] = 0"
  putStrLn ""
  putStrLn "Zero test:"
  putStrLn "  iszero 0"
  putStrLn "  [[·]] = True"
  putStrLn ""
  putStrLn "  iszero 5"
  putStrLn "  [[·]] = False"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "4. CONDITIONALS"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Simple conditional:"
  putStrLn "  if true then 1 else 0"
  putStrLn "  [[·]] = 1"
  putStrLn ""
  putStrLn "  if false then 1 else 0"
  putStrLn "  [[·]] = 0"
  putStrLn ""
  putStrLn "Conditional with iszero:"
  putStrLn "  if iszero 0 then 42 else 0"
  putStrLn "  [[·]] = 42"
  putStrLn ""
  putStrLn "Nested conditionals:"
  putStrLn "  if iszero 1 then 0 else if true then 1 else 2"
  putStrLn "  [[·]] = 1"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "5. LET BINDINGS"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Simple let:"
  putStrLn "  let x = 3 in suc x"
  putStrLn "  [[·]] = 4"
  putStrLn ""
  putStrLn "Nested lets:"
  putStrLn "  let x = 2 in let y = 3 in natrec x (\\(_ : Nat). \\(acc : Nat). suc acc) y"
  putStrLn "  [[·]] = 5    (computes 2 + 3)"
  putStrLn ""
  putStrLn "Let with function:"
  putStrLn "  let f = \\(x : Nat). suc x in f 10"
  putStrLn "  [[·]] = 11"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "6. EXPLICIT BOTTOM (⊥)"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Bottom value:"
  putStrLn "  bottom Nat"
  putStrLn "  [[·]] = ⊥"
  putStrLn ""
  putStrLn "Bottom in conditional (strict):"
  putStrLn "  if (bottom Bool) then 1 else 0"
  putStrLn "  [[·]] = ⊥"
  putStrLn ""
  putStrLn "Bottom in function (lazy):"
  putStrLn "  (\\(x : Nat). 42) (bottom Nat)"
  putStrLn "  [[·]] = 42    (argument not used, so ⊥ is fine)"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "7. FIXED POINTS (The Heart of Recursion!)"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Show fixed point iterations:"
  putStrLn "  :fix 5 \\(f : Nat -> Nat). \\(x : Nat). if iszero x then 1 else x"
  putStrLn ""
  putStrLn "This shows the approximation sequence:"
  putStrLn "  f^0(⊥) = ⊥"
  putStrLn "  f^1(⊥) = <function>  (returns 1 for 0, ⊥ for others)"
  putStrLn "  f^2(⊥) = <function>  (returns 1 for 0, 1 for 1, ⊥ for others)"
  putStrLn "  ..."
  putStrLn ""
  putStrLn "Simple fixed point:"
  putStrLn "  fix (\\(x : Nat). suc x)"
  putStrLn "  [[·]] = ⊥    (infinite loop! no fixed point exists)"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "8. FACTORIAL (Classic Example)"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Compute factorial using the built-in function:"
  putStrLn "  :fact 0"
  putStrLn "  [[fact]](0) = 1"
  putStrLn ""
  putStrLn "  :fact 5"
  putStrLn "  [[fact]](5) = 120"
  putStrLn ""
  putStrLn "  :fact 10"
  putStrLn "  [[fact]](10) = 3628800"
  putStrLn ""
  putStrLn "How it works:"
  putStrLn "  fact = fix F"
  putStrLn "  where F = λf. λn. if iszero n then 1 else n * f(pred n)"
  putStrLn ""
  putStrLn "The denotation [[fact]] is the least function satisfying:"
  putStrLn "  fact(0) = 1"
  putStrLn "  fact(n+1) = (n+1) * fact(n)"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "9. FIBONACCI (Another Classic)"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Compute Fibonacci numbers:"
  putStrLn "  :fib 0"
  putStrLn "  [[fib]](0) = 0"
  putStrLn ""
  putStrLn "  :fib 1"
  putStrLn "  [[fib]](1) = 1"
  putStrLn ""
  putStrLn "  :fib 10"
  putStrLn "  [[fib]](10) = 55"
  putStrLn ""
  putStrLn "  :fib 20"
  putStrLn "  [[fib]](20) = 6765"
  putStrLn ""
  putStrLn "How it works:"
  putStrLn "  fib = fix F"
  putStrLn "  where F = λf. λn. if iszero n then 0"
  putStrLn "                    else if iszero (pred n) then 1"
  putStrLn "                    else f(n-1) + f(n-2)"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "10. PRIMITIVE RECURSION (natrec)"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "The natrec combinator:"
  putStrLn "  natrec z s n  =  if n=0 then z else s (n-1) (natrec z s (n-1))"
  putStrLn ""
  putStrLn "Addition using natrec (3 + 2):"
  putStrLn "  natrec 3 (\\(_ : Nat). \\(acc : Nat). suc acc) 2"
  putStrLn "  [[·]] = 5"
  putStrLn ""
  putStrLn "Multiplication using natrec (4 * 3):"
  putStrLn "  natrec 0 (\\(_ : Nat). \\(acc : Nat). natrec acc (\\(_ : Nat). \\(a : Nat). suc a) 4) 3"
  putStrLn "  [[·]] = 12"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "11. USING THE REPL ENVIRONMENT"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Bind a value:"
  putStrLn "  :let x = 42"
  putStrLn ""
  putStrLn "Use the binding:"
  putStrLn "  suc x"
  putStrLn "  [[·]] = 43"
  putStrLn ""
  putStrLn "Bind a function:"
  putStrLn "  :let double = \\(n : Nat). natrec n (\\(_ : Nat). \\(acc : Nat). suc acc) n"
  putStrLn ""
  putStrLn "Apply it:"
  putStrLn "  double 5"
  putStrLn "  [[·]] = 10"
  putStrLn ""
  putStrLn "View bindings:"
  putStrLn "  :env"
  putStrLn ""
  putStrLn "Reset bindings:"
  putStrLn "  :reset"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "12. KEY CONCEPTS DEMONSTRATED"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "Denotational semantics shows:"
  putStrLn ""
  putStrLn "  1. Mathematical Meaning"
  putStrLn "     Every program maps to a mathematical object in a domain"
  putStrLn ""
  putStrLn "  2. Compositionality"
  putStrLn "     [[e1 e2]] = [[e1]]([[e2]])"
  putStrLn "     The meaning of a composite is built from meanings of parts"
  putStrLn ""
  putStrLn "  3. Fixed Points for Recursion"
  putStrLn "     [[fix f]] = ⊔ₙ fⁿ(⊥)"
  putStrLn "     Recursive functions are least fixed points"
  putStrLn ""
  putStrLn "  4. Approximation"
  putStrLn "     We approach the answer via finite approximations"
  putStrLn "     Each iteration gives more information"
  putStrLn ""
  putStrLn "  5. Non-termination as ⊥"
  putStrLn "     Undefined and non-terminating computations map to ⊥"
  putStrLn "     This is the starting point for fixed point iteration"
  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn "TRY IT YOURSELF!"
  putStrLn "═══════════════════════════════════════════════════════════════════"
  putStrLn ""
  putStrLn "1. Compute denotations:"
  putStrLn "   suc (pred 5)"
  putStrLn "   if iszero 0 then 100 else 0"
  putStrLn ""
  putStrLn "2. Explore fixed points:"
  putStrLn "   :fix 3 \\(f : Nat -> Nat). \\(n : Nat). if iszero n then 0 else suc (f (pred n))"
  putStrLn ""
  putStrLn "3. Compute factorials and Fibonacci:"
  putStrLn "   :fact 7"
  putStrLn "   :fib 15"
  putStrLn ""
  putStrLn "4. Build your own functions with let:"
  putStrLn "   :let triple = \\(x : Nat). suc (suc (suc x))"
  putStrLn "   triple 10"
  putStrLn ""
  putStrLn "5. Learn more about domain theory:"
  putStrLn "   :theory"
  putStrLn ""
