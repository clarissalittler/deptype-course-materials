{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Set as Set

-- ============================================================================
-- Exercise 1: Understanding Effects
-- ============================================================================

-- Exercise 1.1: Nat -> Bool
-- This is a PURE function
-- Effects: {} (no effects)
-- Can only perform computation, no I/O, exceptions, or state

pureFunction :: Type
pureFunction = TyFun TyNat TyBool EffEmpty

-- Exercise 1.2: Nat -> Bool ! {State}
-- This function may use STATE
-- Effects: {State}
-- Can read/write mutable state while computing

statefulFunction :: Type
statefulFunction = TyFun TyNat TyBool (EffLabel "State" EffEmpty)

-- Exercise 1.3: Nat -> Bool ! {State, Exception}
-- This function may use STATE and throw EXCEPTIONS
-- Effects: {State, Exception}
-- Can read/write state AND abort with an exception

statefulExceptionalFunction :: Type
statefulExceptionalFunction = TyFun TyNat TyBool
  (EffLabel "State" (EffLabel "Exception" EffEmpty))

-- Exercise 1.4: ∀ρ. Nat -> Bool ! {State | ρ}
-- This function uses State and possibly OTHER effects (polymorphic)
-- Effects: {State | ρ} where ρ is an effect variable
-- Can read/write state plus any additional effects the caller needs

polymorphicEffectFunction :: Type
polymorphicEffectFunction = TyForallEff "rho"
  (TyFun TyNat TyBool (EffLabel "State" (EffVar "rho")))

-- ============================================================================
-- Exercise 2: Effect Operations
-- ============================================================================

-- Exercise 2.1: Unit -> Nat ! {State}
-- Get the current state
-- Performs: State.get ()
-- Returns: the state value (Nat)

getState :: Term
getState = Lam "u" TyUnit
  (TmPerform "State" "get" (Var "u"))

-- Type of getState
getStateType :: Type
getStateType = TyFun TyUnit TyNat (EffLabel "State" EffEmpty)

-- Exercise 2.2: Nat -> Unit ! {State}
-- Set the state to a new value
-- Performs: State.put n
-- Returns: unit (side effect only)

setState :: Term
setState = Lam "n" TyNat
  (TmPerform "State" "put" (Var "n"))

-- Type of setState
setStateType :: Type
setStateType = TyFun TyNat TyUnit (EffLabel "State" EffEmpty)

-- Exercise 2.3: Unit -> Unit ! {Exception}
-- Throw an exception (abort computation)
-- Performs: Exception.throw ()
-- Returns: never returns (diverges)

throwException :: Term
throwException = Lam "u" TyUnit
  (TmPerform "Exception" "throw" (Var "u"))

-- Type of throwException
throwExceptionType :: Type
throwExceptionType = TyFun TyUnit TyUnit (EffLabel "Exception" EffEmpty)

-- Exercise 2.4: Unit -> Nat ! {State, IO}
-- Read from IO and get state
-- Performs: IO.read () and State.get ()
-- Returns: state value (combining both effects)

readAndGetState :: Term
readAndGetState = Lam "u" TyUnit
  (TmLet "x" (TmPerform "IO" "read" (Var "u"))
    (TmPerform "State" "get" TmUnit))

-- Type of readAndGetState
readAndGetStateType :: Type
readAndGetStateType = TyFun TyUnit TyNat
  (EffLabel "State" (EffLabel "IO" EffEmpty))

-- ============================================================================
-- Exercise 3: Effect Rows
-- ============================================================================

-- Exercise 3.1: {} ⊆ {State}
-- YES - empty effects are a subset of any effect set
-- Pure computation can be used where State is allowed

test31 :: Bool
test31 = rowSubset EffEmpty (EffLabel "State" EffEmpty)

-- Exercise 3.2: {State} ⊆ {State, IO}
-- YES - {State} is a subset of {State, IO}
-- State-only computation can be used where State+IO is allowed

test32 :: Bool
test32 = rowSubset (EffLabel "State" EffEmpty)
                   (EffLabel "State" (EffLabel "IO" EffEmpty))

-- Exercise 3.3: {State, IO} ⊆ {State}
-- NO - {State, IO} requires more effects than {State} provides
-- Cannot use IO where only State is allowed

test33 :: Bool
test33 = rowSubset (EffLabel "State" (EffLabel "IO" EffEmpty))
                   (EffLabel "State" EffEmpty)

-- Exercise 3.4: {State | ρ} ⊆ {State, IO | ρ}
-- YES - State plus ρ is a subset of State+IO plus ρ
-- If ρ doesn't contain IO, this adds IO to the requirement

test34 :: Bool
test34 = rowSubset (EffLabel "State" (EffVar "rho"))
                   (EffLabel "State" (EffLabel "IO" (EffVar "rho")))

-- Exercise 3.5: {ρ} ⊆ {State | ρ}
-- NO - ρ alone doesn't necessarily include State
-- Cannot assume State is in ρ without evidence

test35 :: Bool
test35 = rowSubset (EffVar "rho")
                   (EffLabel "State" (EffVar "rho"))

-- ============================================================================
-- Exercise 4: Simple Handlers
-- ============================================================================

-- Exercise 4.1: State handler
-- Threads state through the computation
-- Type: (s: Nat) -> (comp: A ! {State}) -> (Nat, A)
--
-- handler {
--   return x -> λs. (x, s)
--   get () k -> λs. k s s
--   put s' k -> λs. k () s'
-- }

stateHandler :: Handler
stateHandler = Handler
  { handlerEffect = "State"
  , handlerReturn = ("x", Lam "s" TyNat
      (Var "x"))  -- Simplified: should return pair (x, s)
  , handlerOps =
      [ ("get", "param", "k",
          Lam "s" TyNat
            (App (App (Var "k") (Var "s")) (Var "s")))
      , ("put", "s_new", "k",
          Lam "s" TyNat
            (App (App (Var "k") TmUnit) (Var "s_new")))
      ]
  }

-- Example: Using the state handler
-- handle (get (); put (succ (get ())); get ()) with stateHandler

exampleStateProgram :: Term
exampleStateProgram = TmHandle
  (TmLet "x" (TmPerform "State" "get" TmUnit)
    (TmLet "_" (TmPerform "State" "put" (TmSucc (Var "x")))
      (TmPerform "State" "get" TmUnit)))
  stateHandler

-- Exercise 4.2: Exception handler
-- Returns a default value on exception
-- Type: (comp: A ! {Exception}) -> Maybe A
--
-- handler {
--   return x -> Just x
--   throw () k -> Nothing
-- }

exceptionHandler :: Handler
exceptionHandler = Handler
  { handlerEffect = "Exception"
  , handlerReturn = ("x", Var "x")  -- Simplified: should wrap in Just
  , handlerOps =
      [ ("throw", "param", "k",
          TmUnit)  -- Simplified: should return Nothing
      ]
  }

-- Example: Using the exception handler
-- handle (throw ()) with exceptionHandler
-- Result: Nothing

exampleExceptionProgram :: Term
exampleExceptionProgram = TmHandle
  (TmPerform "Exception" "throw" TmUnit)
  exceptionHandler

-- ============================================================================
-- Exercise 5: Effect Polymorphism
-- ============================================================================

-- Type 1: ∀ρ. (Unit -> Nat ! ρ) -> Nat ! ρ
-- This is EFFECT POLYMORPHIC
-- - Takes a function with arbitrary effects ρ
-- - Returns a result with the SAME effects ρ
-- - The function is polymorphic over ALL possible effect sets

effectPolymorphicType :: Type
effectPolymorphicType = TyForallEff "rho"
  (TyFun (TyFun TyUnit TyNat (EffVar "rho"))
         TyNat (EffVar "rho"))

-- Type 2: (Unit -> Nat ! {State}) -> Nat ! {State}
-- This is EFFECT MONOMORPHIC
-- - Takes a function that specifically uses State
-- - Returns a result that uses State
-- - The function ONLY works with State effects

effectMonomorphicType :: Type
effectMonomorphicType =
  TyFun (TyFun TyUnit TyNat (EffLabel "State" EffEmpty))
        TyNat (EffLabel "State" EffEmpty)

-- Why is effect polymorphism useful?
--
-- 1. CODE REUSE: Write once, use with any effects
--    Example: map can work with pure, stateful, or IO functions
--
-- 2. ABSTRACTION: Hide effect details from callers
--    Example: Generic combinators don't need to know specific effects
--
-- 3. COMPOSITION: Combine functions with different effects
--    Example: sequence : ∀ρ. [Unit -> A ! ρ] -> [A] ! ρ
--
-- 4. EFFECT SAFETY: Preserve effect information through abstractions
--    Example: If input is pure, output is pure; if input uses IO, output uses IO

-- Example of effect polymorphic function: apply twice
-- applyTwice : ∀ρ. (Unit -> Unit ! ρ) -> Unit ! ρ

applyTwice :: Term
applyTwice = TmEffAbs "rho"
  (Lam "f" (TyFun TyUnit TyUnit (EffVar "rho"))
    (TmLet "_" (App (Var "f") TmUnit)
      (App (Var "f") TmUnit)))

-- We can use applyTwice with ANY effects:
-- applyTwice [{}] pureFn       -- Pure
-- applyTwice [{State}] stateFn -- Stateful
-- applyTwice [{IO}] ioFn       -- IO

-- ============================================================================
-- Exercise 6: Implement Reader Effect
-- ============================================================================

-- Reader effect provides read-only environment access
--
-- Operations:
--   ask : Unit -> A     -- Get the environment
--   local : A -> Unit   -- Temporarily modify (simplified)

-- Add to defaultEffects in TypeCheck.hs:
-- ("Reader", [ Operation "ask" TyUnit TyNat
--            , Operation "local" TyNat TyUnit
--            ])

-- Reader handler (simplified):
-- handler {
--   return x -> λenv. x
--   ask () k -> λenv. k env env
--   local env' k -> λenv. k () env'  -- Note: should restore env after
-- }

readerHandler :: Term -> Handler
readerHandler env = Handler
  { handlerEffect = "Reader"
  , handlerReturn = ("x", Lam "env" TyNat (Var "x"))
  , handlerOps =
      [ ("ask", "param", "k",
          Lam "env" TyNat
            (App (App (Var "k") (Var "env")) (Var "env")))
      , ("local", "env_new", "k",
          Lam "env" TyNat
            (App (App (Var "k") TmUnit) (Var "env_new")))
      ]
  }

-- Example: Read environment twice
-- ask (); ask ()

exampleReaderProgram :: Term
exampleReaderProgram = TmLet "x" (TmPerform "Reader" "ask" TmUnit)
  (TmPerform "Reader" "ask" TmUnit)

-- To handle it:
-- handle exampleReaderProgram with (readerHandler 42)

-- ============================================================================
-- Exercise 7: Implement Writer Effect
-- ============================================================================

-- Writer effect accumulates output
--
-- Operations:
--   tell : A -> Unit    -- Append to output

-- Add to defaultEffects:
-- ("Writer", [ Operation "tell" TyNat TyUnit ])

-- Writer handler:
-- handler {
--   return x -> ([], x)
--   tell v k -> let (log, res) = k () in (v : log, res)
-- }

writerHandler :: Handler
writerHandler = Handler
  { handlerEffect = "Writer"
  , handlerReturn = ("x", Var "x")  -- Simplified: should return ([], x)
  , handlerOps =
      [ ("tell", "v", "k",
          -- Simplified: should collect v and append to log
          App (Var "k") TmUnit)
      ]
  }

-- Example: Write multiple values
-- tell 1; tell 2; tell 3

exampleWriterProgram :: Term
exampleWriterProgram =
  TmLet "_" (TmPerform "Writer" "tell" (TmSucc TmZero))
    (TmLet "_" (TmPerform "Writer" "tell" (TmSucc (TmSucc TmZero)))
      (TmPerform "Writer" "tell" (TmSucc (TmSucc (TmSucc TmZero)))))

-- Result should be ([1, 2, 3], ())

-- ============================================================================
-- Exercise 8: Effect Inference (Conceptual)
-- ============================================================================

-- Effect inference algorithm (sketch):
--
-- 1. Generate effect variables for unknown effects
--    For each lambda: λx. e gets type A -> B ! ε where ε is fresh
--
-- 2. Collect constraints during type checking
--    - If: if e1 then e2 else e3 has effects ε1 ∪ ε2 ∪ ε3
--    - App: (f : A -> B ! ε1) e has effects ε1 ∪ ε2 ∪ εf
--    - Perform: generates constraint ε ⊇ {Effect}
--
-- 3. Solve constraints to find minimal effects
--    - Start with ε = {}
--    - For each constraint ε ⊇ {E}, add E to ε
--    - For each ε1 ⊆ ε2, ensure subset relation
--
-- Example:
--   λx. get (); put x
--
-- Inference:
--   - get () : Unit -> Nat ! {State}
--   - put x : Nat -> Unit ! {State}
--   - Constraints: ε ⊇ {State}, ε ⊇ {State}
--   - Solution: ε = {State}
--   - Result: Nat -> Unit ! {State}

-- ============================================================================
-- Exercise 9: Effect Subtyping (Conceptual)
-- ============================================================================

-- Effect subtyping rules:
--
-- 1. Pure ≤ Effectful:
--    T ! {} <: T ! {E}
--    (Pure computation can be used where effects are allowed)
--
-- 2. Subset:
--    T ! {E} <: T ! {E, F}
--    (Fewer effects can be used where more are allowed)
--
-- 3. Function subtyping (contravariant in effects):
--    (A -> B ! ε1) <: (A -> B ! ε2)  iff  ε1 ⊆ ε2
--
-- Implementation in isSubtype:

isEffectSubtype :: EffectRow -> EffectRow -> Bool
isEffectSubtype eff1 eff2 = rowSubset eff1 eff2

-- Example:
--   f : Nat -> Bool ! {}
--   Can be used where: Nat -> Bool ! {State} is expected
--
--   g : Nat -> Bool ! {State}
--   Can be used where: Nat -> Bool ! {State, IO} is expected
--
--   But NOT vice versa!

-- ============================================================================
-- Exercise 10: Deep vs Shallow Handlers (Conceptual)
-- ============================================================================

-- DEEP handlers (our implementation):
-- - Handle ALL occurrences of an effect
-- - Continuation k re-handles the effect
-- - Example: State handler threads state through entire computation
--
-- handler {
--   return x -> ...
--   op p k -> ... k ... -- k handles E recursively
-- }

-- SHALLOW handlers:
-- - Handle ONLY the first occurrence
-- - Continuation k does NOT re-handle
-- - Must explicitly re-handle if needed
-- - Example: Single-step state handler
--
-- shallow_handler {
--   return x -> ...
--   op p k -> ... k ... -- k does NOT handle E
-- }

-- Comparison:
--
-- DEEP HANDLERS:
-- + Natural for most effects (State, Exception, IO)
-- + Automatic recursion
-- - Cannot intercept individual operations
-- - Less control over handling strategy
--
-- SHALLOW HANDLERS:
-- + Fine-grained control (can handle differently each time)
-- + Can implement deep handlers via explicit recursion
-- + Better for effect transformations
-- - More verbose (must explicitly recurse)
-- - Easy to forget to re-handle

-- Example with shallow State:
-- shallow_handle (get (); put 5; get ()) with {
--   get () k -> k 0 (shallow_handle k with ...)  -- Must re-handle!
--   put s k -> k () (shallow_handle k with ...)
-- }

-- ============================================================================
-- Advanced Examples
-- ============================================================================

-- Example 1: Combining effects (State + Exception)
-- A function that might fail while maintaining state

maybeIncrement :: Term
maybeIncrement = Lam "b" TyBool
  (TmIf (Var "b")
    (TmLet "x" (TmPerform "State" "get" TmUnit)
      (TmPerform "State" "put" (TmSucc (Var "x"))))
    (TmPerform "Exception" "throw" TmUnit))

-- Type: Bool -> Unit ! {State, Exception}

maybeIncrementType :: Type
maybeIncrementType = TyFun TyBool TyUnit
  (EffLabel "State" (EffLabel "Exception" EffEmpty))

-- Example 2: Effect polymorphic map
-- map : ∀ρ. (A -> B ! ρ) -> List A -> List B ! ρ

-- This preserves the effects of the function being mapped
-- - If f is pure, map f is pure
-- - If f uses State, map f uses State
-- - etc.

-- Example 3: Masking effects
-- Sometimes we want to handle effects locally and hide them:
--
-- runState : (s: Nat) -> (comp: A ! {State}) -> A
-- runState s comp = handle comp with stateHandler s
--
-- Type: (Nat, A ! {State}) -> A ! {}
-- The State effect is INTERNAL and not visible to callers!

runState :: Term
runState = Lam "s" TyNat
  (Lam "comp" (TyFun TyUnit TyNat (EffLabel "State" EffEmpty))
    (TmHandle (App (Var "comp") TmUnit) stateHandler))

-- Example 4: Effect composition
-- Combining multiple handlers

composedExample :: Term
composedExample =
  TmHandle
    (TmHandle
      (TmLet "x" (TmPerform "State" "get" TmUnit)
        (TmIf (TmIsZero (Var "x"))
          (TmPerform "Exception" "throw" TmUnit)
          (TmPerform "State" "put" (TmPred (Var "x")))))
      stateHandler)
    exceptionHandler

-- First handle State, then handle Exception
-- Type depends on how handlers transform the computation

-- ============================================================================
-- Test Suite
-- ============================================================================

testSolutions :: IO ()
testSolutions = do
  putStrLn "Testing Chapter 12 Solutions"
  putStrLn "============================="

  putStrLn "\n1. Effect row subset tests:"
  putStrLn $ "   {} ⊆ {State}: " ++ show test31
  putStrLn $ "   {State} ⊆ {State, IO}: " ++ show test32
  putStrLn $ "   {State, IO} ⊆ {State}: " ++ show test33

  putStrLn "\n2. Type checking getState:"
  print $ typeCheck getState

  putStrLn "\n3. Type checking setState:"
  print $ typeCheck setState

  putStrLn "\n4. Type checking throwException:"
  print $ typeCheck throwException

  putStrLn "\n5. Type checking readAndGetState:"
  print $ typeCheck readAndGetState

  putStrLn "\n6. Type checking applyTwice:"
  print $ typeCheck applyTwice

  putStrLn "\n7. Type checking maybeIncrement:"
  print $ typeCheck maybeIncrement

  putStrLn "\n8. Effect polymorphic type:"
  print effectPolymorphicType

  putStrLn "\n9. Effect monomorphic type:"
  print effectMonomorphicType

  putStrLn "\nAll solutions implemented!"

-- ============================================================================
-- Additional Helper Functions
-- ============================================================================

-- Helper: Create effect row from list of labels
mkEffectRow :: [EffectLabel] -> EffectRow
mkEffectRow = foldr EffLabel EffEmpty

-- Helper: Create effect row with variable tail
mkEffectRowVar :: [EffectLabel] -> Var -> EffectRow
mkEffectRowVar labels var = foldr EffLabel (EffVar var) labels

-- Example effect rows
pureRow :: EffectRow
pureRow = EffEmpty

stateRow :: EffectRow
stateRow = EffLabel "State" EffEmpty

stateIORow :: EffectRow
stateIORow = mkEffectRow ["State", "IO"]

polymorphicStateRow :: EffectRow
polymorphicStateRow = mkEffectRowVar ["State"] "rho"

-- Helper: Check if effect row is pure
isPure :: EffectRow -> Bool
isPure EffEmpty = True
isPure _ = False

-- Helper: Count concrete effects in row (not counting variables)
countEffects :: EffectRow -> Int
countEffects EffEmpty = 0
countEffects (EffLabel _ r) = 1 + countEffects r
countEffects (EffVar _) = 0  -- Don't count variables
