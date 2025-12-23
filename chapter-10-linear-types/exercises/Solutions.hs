{-# LANGUAGE OverloadedStrings #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Map.Strict as Map

-- ============================================================================
-- Linear Types: Core Concepts
-- ============================================================================

-- Linear types ensure that values are used exactly once. This is useful for:
-- 1. Resource management (file handles, locks, memory)
-- 2. Protocol enforcement (session types)
-- 3. Safe concurrency (preventing aliasing)
--
-- Key rules:
-- - Linear variables (multiplicity One) must be used exactly once
-- - Unrestricted variables (multiplicity Many) can be used any number of times
-- - The !-type (bang) converts linear values to unrestricted ones

-- ============================================================================
-- Exercise 1: Linear vs Unrestricted
-- ============================================================================

-- Exercise 1.1: λx :1 Nat. x
-- Well-typed: Yes
-- Type: Nat -o Nat
-- Explanation: x is linear and used exactly once (in the body)
ex1_1 :: Term
ex1_1 = Lam "x" One TyNat (Var "x")

ex1_1_type :: Either TypeError Type
ex1_1_type = typeCheck ex1_1
-- Result: Right (Nat -o Nat)

-- Exercise 1.2: λx :1 Nat. (x, x)
-- Well-typed: No
-- Error: LinearVariableUsedTwice
-- Explanation: x is linear but used twice (in both components of the pair)
ex1_2 :: Term
ex1_2 = Lam "x" One TyNat (TmPair (Var "x") (Var "x"))

ex1_2_type :: Either TypeError Type
ex1_2_type = typeCheck ex1_2
-- Result: Left (LinearVariableUsedTwice "x")

-- Exercise 1.3: λx :ω Nat. (x, x)
-- Well-typed: Yes
-- Type: Nat -> (Nat * Nat)
-- Explanation: x is unrestricted (Many), so it can be used multiple times
ex1_3 :: Term
ex1_3 = Lam "x" Many TyNat (TmPair (Var "x") (Var "x"))

ex1_3_type :: Either TypeError Type
ex1_3_type = typeCheck ex1_3
-- Result: Right (Nat -> (Nat * Nat))

-- Exercise 1.4: λx :1 Nat. 0
-- Well-typed: No
-- Error: LinearVariableUnused
-- Explanation: x is linear but not used at all
ex1_4 :: Term
ex1_4 = Lam "x" One TyNat TmZero

ex1_4_type :: Either TypeError Type
ex1_4_type = typeCheck ex1_4
-- Result: Left (LinearVariableUnused "x")

-- Exercise 1.5: λx :ω Nat. 0
-- Well-typed: Yes
-- Type: Nat -> Nat
-- Explanation: x is unrestricted, so not using it is fine
ex1_5 :: Term
ex1_5 = Lam "x" Many TyNat TmZero

ex1_5_type :: Either TypeError Type
ex1_5_type = typeCheck ex1_5
-- Result: Right (Nat -> Nat)

-- Exercise 1.6: λx :1 Nat. let y :1 = x in y
-- Well-typed: Yes
-- Type: Nat -o Nat
-- Explanation: x is used once (in the let binding), and y is used once (in the body)
ex1_6 :: Term
ex1_6 = Lam "x" One TyNat (TmLet "y" One (Var "x") (Var "y"))

ex1_6_type :: Either TypeError Type
ex1_6_type = typeCheck ex1_6
-- Result: Right (Nat -o Nat)

-- ============================================================================
-- Exercise 2: Pair Usage
-- ============================================================================

-- All pairs in these examples are created with linear components,
-- so when we deconstruct them, both components must be used exactly once.

-- Exercise 2.1: let (a, b) = (0, true) in a
-- Well-typed: No
-- Error: LinearVariableUnused "b"
-- Explanation: b is linear (from the pair) but not used
ex2_1 :: Term
ex2_1 = TmLetPair "a" "b" (TmPair TmZero TmTrue) (Var "a")

ex2_1_type :: Either TypeError Type
ex2_1_type = typeCheck ex2_1
-- Result: Left (LinearVariableUnused "b")

-- Exercise 2.2: let (a, b) = (0, true) in (a, b)
-- Well-typed: Yes
-- Type: Nat * Bool
-- Explanation: Both a and b are used exactly once
ex2_2 :: Term
ex2_2 = TmLetPair "a" "b" (TmPair TmZero TmTrue) (TmPair (Var "a") (Var "b"))

ex2_2_type :: Either TypeError Type
ex2_2_type = typeCheck ex2_2
-- Result: Right (Nat * Bool)

-- Exercise 2.3: let (a, b) = (0, true) in (b, a)
-- Well-typed: Yes
-- Type: Bool * Nat
-- Explanation: Both a and b are used exactly once (in swapped order)
ex2_3 :: Term
ex2_3 = TmLetPair "a" "b" (TmPair TmZero TmTrue) (TmPair (Var "b") (Var "a"))

ex2_3_type :: Either TypeError Type
ex2_3_type = typeCheck ex2_3
-- Result: Right (Bool * Nat)

-- Exercise 2.4: let (a, b) = (0, true) in (a, a)
-- Well-typed: No
-- Error: LinearVariableUsedTwice "a" or LinearVariableUnused "b"
-- Explanation: a is used twice, b is not used
ex2_4 :: Term
ex2_4 = TmLetPair "a" "b" (TmPair TmZero TmTrue) (TmPair (Var "a") (Var "a"))

ex2_4_type :: Either TypeError Type
ex2_4_type = typeCheck ex2_4
-- Result: Left (LinearVariableUnused "b") -- or UsedTwice "a", depending on order

-- ============================================================================
-- Exercise 3: Bang Types
-- ============================================================================

-- The bang type ! allows us to make linear values unrestricted.
-- This is essential for duplicating or discarding values.

-- Exercise 3.1: !0
-- Type: !Nat
-- Explanation: The bang wraps a Nat value, making it unrestricted.
-- We can use this value multiple times after unwrapping with let !x = ...
ex3_1 :: Term
ex3_1 = TmBang TmZero

ex3_1_type :: Either TypeError Type
ex3_1_type = typeCheck ex3_1
-- Result: Right (!Nat)

-- Exercise 3.2: let !x = !0 in (x, x)
-- Type: Nat * Nat
-- Explanation: The !0 has type !Nat. When we unwrap it with let !x = ...,
-- x gets type Nat with unrestricted multiplicity (Many).
-- So we can use x twice in the pair.
ex3_2 :: Term
ex3_2 = TmLetBang "x" (TmBang TmZero) (TmPair (Var "x") (Var "x"))

ex3_2_type :: Either TypeError Type
ex3_2_type = typeCheck ex3_2
-- Result: Right (Nat * Nat)

-- Exercise 3.3: λf :1 (!Nat -o Nat). f !0
-- Type: (!Nat -o Nat) -o Nat
-- Explanation: f is a linear function that takes a !Nat and returns Nat.
-- We use f exactly once, applying it to !0.
-- The !0 is an unrestricted value, so it can be passed to f.
ex3_3 :: Term
ex3_3 = Lam "f" One (TyFun One (TyBang TyNat) TyNat)
            (App (Var "f") (TmBang TmZero))

ex3_3_type :: Either TypeError Type
ex3_3_type = typeCheck ex3_3
-- Result: Right ((!Nat -o Nat) -o Nat)

-- Why can't we write λx :1 Nat. !x?
-- Answer: To create a !-value (!x), we must ensure that x doesn't use any
-- linear resources. But x itself is linear (multiplicity One), so it IS
-- a linear resource. Therefore, we cannot wrap it in !.
--
-- The ! constructor requires that its contents use no linear variables.
-- This prevents us from "escaping" linear constraints by wrapping linear
-- values in !.

ex3_invalid :: Term
ex3_invalid = Lam "x" One TyNat (TmBang (Var "x"))

ex3_invalid_type :: Either TypeError Type
ex3_invalid_type = typeCheck ex3_invalid
-- Result: Left (TypeError "Cannot use linear variables under !")

-- ============================================================================
-- Exercise 4: Implement Swap
-- ============================================================================

-- swap : (A * B) -o (B * A)
-- Takes a pair and swaps its components

swap :: Term
swap = Lam "p" One (TyPair TyNat TyBool)  -- Concrete types for example
       (TmLetPair "a" "b" (Var "p")
         (TmPair (Var "b") (Var "a")))

-- More polymorphic version (conceptual, as our system doesn't have type params):
-- swap = Λ(A:Type). Λ(B:Type). λp :1 (A * B).
--          let (a, b) = p in (b, a)

swap_type :: Either TypeError Type
swap_type = typeCheck swap
-- Result: Right ((Nat * Bool) -o (Bool * Nat))

-- Why must this be a linear function?
-- Answer: The pair p contains two linear components a and b. When we
-- pattern match with let (a, b) = p, both a and b must be used exactly
-- once. We use them once each in the result pair (b, a), which satisfies
-- the linear constraint.
--
-- If swap were unrestricted (Many), we could call it multiple times on
-- the same pair, which would violate the linearity of the components.
-- For example:
--   let p = (resource1, resource2) in (swap p, swap p)
-- would try to use resource1 and resource2 twice!

-- ============================================================================
-- Exercise 5: Implement Apply
-- ============================================================================

-- apply : ((A -o B) * A) -o B
-- Takes a pair of a function and an argument, and applies the function

apply :: Term
apply = Lam "pair" One (TyPair (TyFun One TyNat TyBool) TyNat)
        (TmLetPair "f" "x" (Var "pair")
          (App (Var "f") (Var "x")))

-- More polymorphic version (conceptual):
-- apply = Λ(A:Type). Λ(B:Type). λp :1 ((A -o B) * A).
--           let (f, x) = p in f x

apply_type :: Either TypeError Type
apply_type = typeCheck apply
-- Result: Right (((Nat -o Bool) * Nat) -o Bool)

-- Explanation:
-- - p is a linear pair containing a function f and an argument x
-- - Both f and x are linear (from the pair)
-- - We use f once (in the application) and x once (as the argument)
-- - The result has type B (in our concrete example, Bool)

-- This pattern is fundamental in linear logic: it shows how to consume
-- a packaged function and argument together, ensuring both are used exactly once.

-- ============================================================================
-- Example: Linear Resource Management
-- ============================================================================

-- Let's demonstrate a practical use case: file handles

-- Suppose we have:
-- - openFile : String -> FileHandle
-- - readFile : FileHandle -o (String * FileHandle)
-- - closeFile : FileHandle -o ()

-- We can encode a safe file reading pattern:
-- safeRead : String -> String
-- safeRead filename =
--   let handle = openFile filename in
--   let (content, handle') = readFile handle in
--   let () = closeFile handle' in
--   content

-- The linear types ensure that:
-- 1. The file handle is used exactly once by readFile
-- 2. The new handle from readFile is used exactly once by closeFile
-- 3. We can't forget to close the file (handle' must be used)
-- 4. We can't use a closed file handle (it's consumed by closeFile)

-- In our simplified system, we can model this as:

-- Simulate FileHandle as Nat (for demonstration)
type FileHandle = Type
fileHandle :: FileHandle
fileHandle = TyNat

-- readFileHandle : FileHandle -o (String * FileHandle)
-- In our system: Nat -o (Bool * Nat)  (Bool simulates String)
readFileHandle :: Term
readFileHandle = Lam "handle" One fileHandle
           (TmPair TmTrue (Var "handle"))

-- closeFileHandle : FileHandle -o ()
-- In our system: Nat -o ()
closeFileHandle :: Term
closeFileHandle = Lam "handle" One fileHandle TmUnit

-- safeRead : FileHandle -o Bool  (Bool simulates String)
safeRead :: Term
safeRead = Lam "handle" One fileHandle
           (TmLetPair "content" "handle'" (App readFileHandle (Var "handle"))
             (TmLet "unit" One (App closeFileHandle (Var "handle'")) (Var "content")))

safeRead_type :: Either TypeError Type
safeRead_type = typeCheck safeRead
-- This would work if readFile and closeFile were values, not just terms

-- ============================================================================
-- Example: Session Types (Simplified)
-- ============================================================================

-- Session types use linear types to enforce communication protocols.
-- For example, a simple request-response protocol:
--
-- 1. Send a request (Nat)
-- 2. Receive a response (Bool)
-- 3. Close the channel
--
-- Type: Send Nat (Recv Bool End)
--
-- In a linear system, each step consumes the channel and returns a new
-- channel in the next state:
--
-- send : a -o Channel (Send a s) -o Channel s
-- recv : Channel (Recv a s) -o (a * Channel s)
-- close : Channel End -o ()

-- This ensures:
-- - We can't skip protocol steps (each step consumes the channel)
-- - We can't reuse old channel states (they're linear)
-- - We must follow the protocol to completion (to satisfy linearity)

-- ============================================================================
-- Example: The Difference Between Linear and Unrestricted
-- ============================================================================

-- Linear function: uses argument exactly once
linearId :: Term
linearId = Lam "x" One TyNat (Var "x")

-- Unrestricted function: can use argument multiple times (or not at all)
unrestrictedDup :: Term
unrestrictedDup = Lam "x" Many TyNat (TmPair (Var "x") (Var "x"))

-- We can convert linear to unrestricted using !
-- promote : a -o !a
promote :: Term
promote = Lam "x" One TyNat (TmBang (Var "x"))
-- ERROR: This would fail! Can't use linear variable under !

-- Correct promotion requires the value to be unrestricted already
promoteCorrect :: Term
promoteCorrect = Lam "x" Many TyNat (TmBang (Var "x"))

promoteCorrect_type :: Either TypeError Type
promoteCorrect_type = typeCheck promoteCorrect
-- Result: Right (Nat -> !Nat)

-- ============================================================================
-- Advanced Example: Linear State Threading
-- ============================================================================

-- Linear types can enforce single-threaded state, preventing aliasing:
--
-- type State s a = s -o (a * s)
--
-- return : a -> State s a
-- return = λx. λs. (x, s)
--
-- (>>=) : State s a -o (a -o State s b) -o State s b
-- (>>=) = λm. λk. λs.
--   let (a, s') = m s in
--   k a s'
--
-- get : State s s
-- get = λs. (s, s)  -- Wait, this uses s twice! Need to think about this...
--
-- Actually, in a linear state monad, we need to be more careful:
--
-- get : State s !s   -- Returns unrestricted copy
-- get = λs. (!s, s)
--
-- put : s -o State s ()
-- put = λnew. λold. ((), new)  -- old is discarded linearly

-- This ensures that state is never aliased, making it safe for in-place updates.

-- ============================================================================
-- Test Suite
-- ============================================================================

testSolutions :: IO ()
testSolutions = do
  putStrLn "Testing Chapter 10: Linear Types Solutions"
  putStrLn "==========================================="

  putStrLn "\nExercise 1: Linear vs Unrestricted"
  putStrLn "-----------------------------------"
  putStrLn $ "1.1 λx:1 Nat. x: " ++ show ex1_1_type
  putStrLn $ "1.2 λx:1 Nat. (x,x): " ++ show ex1_2_type
  putStrLn $ "1.3 λx:ω Nat. (x,x): " ++ show ex1_3_type
  putStrLn $ "1.4 λx:1 Nat. 0: " ++ show ex1_4_type
  putStrLn $ "1.5 λx:ω Nat. 0: " ++ show ex1_5_type
  putStrLn $ "1.6 λx:1 Nat. let y:1=x in y: " ++ show ex1_6_type

  putStrLn "\nExercise 2: Pair Usage"
  putStrLn "----------------------"
  putStrLn $ "2.1 let (a,b)=(0,true) in a: " ++ show ex2_1_type
  putStrLn $ "2.2 let (a,b)=(0,true) in (a,b): " ++ show ex2_2_type
  putStrLn $ "2.3 let (a,b)=(0,true) in (b,a): " ++ show ex2_3_type
  putStrLn $ "2.4 let (a,b)=(0,true) in (a,a): " ++ show ex2_4_type

  putStrLn "\nExercise 3: Bang Types"
  putStrLn "----------------------"
  putStrLn $ "3.1 !0: " ++ show ex3_1_type
  putStrLn $ "3.2 let !x=!0 in (x,x): " ++ show ex3_2_type
  putStrLn $ "3.3 λf:1 (!Nat-o Nat). f !0: " ++ show ex3_3_type
  putStrLn $ "3.invalid λx:1 Nat. !x: " ++ show ex3_invalid_type

  putStrLn "\nExercise 4: Swap"
  putStrLn "----------------"
  putStrLn $ "swap: " ++ show swap_type
  putStrLn "Explanation: swap must be linear because it deconstructs a pair"
  putStrLn "whose components are linear. Each component must be used exactly once."

  putStrLn "\nExercise 5: Apply"
  putStrLn "-----------------"
  putStrLn $ "apply: " ++ show apply_type
  putStrLn "Explanation: apply consumes a linear pair containing a function and"
  putStrLn "an argument, using each exactly once in the application."

  putStrLn "\nKey Concepts Demonstrated:"
  putStrLn "- Linear variables must be used exactly once"
  putStrLn "- Unrestricted variables can be used any number of times"
  putStrLn "- Bang (!) converts linear values to unrestricted (when safe)"
  putStrLn "- Pairs distribute linearity to their components"
  putStrLn "- Linear types enable safe resource management"

  putStrLn "\nAll solutions demonstrated!"
