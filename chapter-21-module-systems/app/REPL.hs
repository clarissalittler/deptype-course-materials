{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module REPL (runREPL) where

import Syntax
import Parser
import Pretty
import TypeCheck
import Eval

import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import System.IO (hFlush, stdout)
import Control.Exception (catch, IOException)
import GHC.IO.Exception (IOErrorType(..))
import System.IO.Error (ioeGetErrorType)

-- | REPL State
data REPLState = REPLState
  { moduleContext :: ModuleContext
  , showSteps :: Bool
  , showTypes :: Bool
  , maxSteps :: Int
  }

-- | Initial REPL state
initialState :: REPLState
initialState = REPLState
  { moduleContext = emptyContext
  , showSteps = False
  , showTypes = True
  , maxSteps = 1000
  }

-- | Main REPL loop
runREPL :: IO ()
runREPL = do
  putStrLn "==========================================="
  putStrLn "Module Systems REPL"
  putStrLn "==========================================="
  putStrLn ""
  putStrLn "Features: Structures, Signatures, Functors,"
  putStrLn "          Module Application, Sealing"
  putStrLn ""
  putStrLn "Commands:"
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :mod M = expr      Define a module"
  putStrLn "  :sig S = sig       Define a signature"
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
  putStr "modules> "
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
  ["reset"] -> putStrLn "Context reset." >> return initialState

  ("let" : x : "=" : rest) -> handleLetBinding x (unwords rest) state

  ("type" : rest) -> handleTypeOf (unwords rest) state >> return state

  ("mod" : m : "=" : rest) -> handleModBinding m (unwords rest) state

  ("step" : rest) -> handleStep (unwords rest) >> return state

  ("steps" : rest) -> handleSteps (unwords rest) state >> return state

  _ -> putStrLn ("Unknown command: " ++ cmd) >> return state

-- | Handle term binding
handleLetBinding :: String -> String -> REPLState -> IO REPLState
handleLetBinding x input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn ("Parse error: " ++ show err) >> return state
    Right t -> do
      let ctx = moduleContext state
      case typeOf ctx t of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right ty -> do
          let v = eval t
              ctx' = extendVar x ty ctx
          putStrLn $ x ++ " : " ++ prettyType ty ++ " = " ++ prettyTerm v
          return state { moduleContext = ctx' }

-- | Handle module binding
handleModBinding :: String -> String -> REPLState -> IO REPLState
handleModBinding m input state = do
  case parseMod (T.pack input) of
    Left err -> putStrLn ("Parse error: " ++ show err) >> return state
    Right mexpr -> do
      let ctx = moduleContext state
      case typeCheckMod ctx mexpr of
        Left err -> putStrLn ("Type error: " ++ show err) >> return state
        Right sig -> do
          let ctx' = extendMod m sig ctx
          putStrLn $ "module " ++ m ++ " : " ++ prettySig sig
          return state { moduleContext = ctx' }

-- | Handle :type command
handleTypeOf :: String -> REPLState -> IO ()
handleTypeOf input state = do
  case parseTerm (T.pack input) of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right t -> do
      let ctx = moduleContext state
      case typeOf ctx t of
        Left err -> putStrLn $ "Type error: " ++ show err
        Right ty -> putStrLn $ "  : " ++ prettyType ty

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
      let ctx = moduleContext state

      -- Type check and display type
      case typeOf ctx t of
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

-- | Show environment
showEnv :: REPLState -> IO ()
showEnv state = do
  putStrLn "Context:"
  let (valCtx, modCtx, _) = moduleContext state
  if Map.null valCtx && Map.null modCtx
    then putStrLn "  (empty)"
    else do
      when (not $ Map.null valCtx) $ do
        putStrLn "Values:"
        mapM_ (\(x, ty) -> putStrLn $ "  " ++ x ++ " : " ++ prettyType ty) (Map.toList valCtx)
      when (not $ Map.null modCtx) $ do
        putStrLn "Modules:"
        mapM_ (\(m, sig) -> putStrLn $ "  " ++ m ++ " : " ++ prettySig sig) (Map.toList modCtx)

-- | Helper for when
when :: Bool -> IO () -> IO ()
when True action = action
when False _ = return ()

-- | Show help
showHelp :: IO ()
showHelp = do
  putStrLn ""
  putStrLn "Module Systems REPL Commands:"
  putStrLn ""
  putStrLn "  :help              Show this help message"
  putStrLn "  :examples          Show example expressions"
  putStrLn "  :quit              Exit the REPL"
  putStrLn "  :let x = t         Bind term t to variable x"
  putStrLn "  :type t            Show the type of term t"
  putStrLn "  :mod M = expr      Define a module"
  putStrLn "  :sig S = sig       Define a signature"
  putStrLn "  :step t            Show single evaluation step"
  putStrLn "  :steps t           Show all evaluation steps"
  putStrLn "  :env               Show current bindings"
  putStrLn "  :reset             Reset all bindings"
  putStrLn ""
  putStrLn "Syntax:"
  putStrLn "  Structures:"
  putStrLn "    struct"
  putStrLn "      val x : Nat = 5"
  putStrLn "      type t = Nat"
  putStrLn "    end"
  putStrLn ""
  putStrLn "  Signatures:"
  putStrLn "    sig"
  putStrLn "      val x : Nat"
  putStrLn "      type t"
  putStrLn "    end"
  putStrLn ""
  putStrLn "  Functors:"
  putStrLn "    functor(X : sig val x : Nat end) =>"
  putStrLn "      struct val y : Nat = X.x end"
  putStrLn ""
  putStrLn "  Sealing:"
  putStrLn "    (M :> S)"
  putStrLn ""

-- | Show examples
showExamples :: IO ()
showExamples = putStrLn $ unlines
  [ "==========================================="
  , "Module Systems Examples"
  , "==========================================="
  , ""
  , "--- Basic Structures ---"
  , ""
  , "1. Simple structure with a value:"
  , "   :mod M = struct val x : Nat = 5 end"
  , ""
  , "2. Structure with type and value:"
  , "   :mod M = struct type t = Nat val x : t = 0 end"
  , ""
  , "3. Nested modules:"
  , "   :mod M = struct module N = struct val x : Nat = 5 end end"
  , ""
  , "--- Signatures ---"
  , ""
  , "4. Abstract type signature:"
  , "   sig type t val x : t end"
  , ""
  , "5. Manifest type signature:"
  , "   sig type t = Nat val x : t end"
  , ""
  , "--- Functors ---"
  , ""
  , "6. Simple functor:"
  , "   functor(X : sig val x : Nat end) =>"
  , "     struct val y : Nat = succ X.x end"
  , ""
  , "7. Functor with type abstraction:"
  , "   functor(X : sig type t end) =>"
  , "     struct type u = X.t end"
  , ""
  , "--- Sealing (Signature Ascription) ---"
  , ""
  , "8. Hide implementation details:"
  , "   (struct val x : Nat = 5 val y : Nat = 10 end"
  , "    :> sig val x : Nat end)"
  , ""
  , "9. Abstract type:"
  , "   (struct type t = Nat val x : t = 0 end"
  , "    :> sig type t val x : t end)"
  , ""
  , "==========================================="
  , "Try It!"
  , "==========================================="
  , ""
  , "1. Define a simple module:"
  , "   :mod Counter = struct val count : Nat = 0 end"
  , ""
  , "2. Define a functor that increments:"
  , "   :mod Inc = functor(X : sig val n : Nat end) =>"
  , "              struct val m : Nat = succ X.n end"
  , ""
  , "3. Apply the functor:"
  , "   :mod Result = (Inc)(Counter)"
  , ""
  ]
