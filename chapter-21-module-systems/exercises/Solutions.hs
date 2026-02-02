{-|
Module: Solutions
Description: Solutions to Module Systems exercises

This module contains reference solutions for all exercises in EXERCISES.md.
These are meant to be studied AFTER attempting the exercises yourself.
-}

module Solutions
  ( exercise1
  , exercise1Sig
  , exercise2
  , exercise3Sig
  , exercise3
  , exercise4
  , exercise5
  , exercise5Test
  , exercise6
  , exercise7
  , exercise8
  , exercise9
  , exercise10Sig
  , exercise10
  , functorF
  , functorG
  , exercise11
  , exercise12
  , exercise13
  , exercise14
  , exercise15
  , checkExercise
  , runAllExercises
  ) where

import Syntax
import TypeCheck
import qualified Data.Map.Strict as Map

-- =============================================================================
-- Exercise 1: Basic Structures
-- =============================================================================

-- Solution: Create a structure with x and y coordinates
exercise1 :: ModExpr
exercise1 = Struct
  [ ValDecl "x" TyNat TmZero
  , ValDecl "y" TyNat TmZero
  ]

-- Expected signature:
exercise1Sig :: Signature
exercise1Sig = Sig
  [ ValSpec "x" TyNat
  , ValSpec "y" TyNat
  ]

-- =============================================================================
-- Exercise 2: Type Definitions
-- =============================================================================

-- Solution: Structure with type definition and values
exercise2 :: ModExpr
exercise2 = Struct
  [ TypeDecl "coordinate" (Just TyNat)
  , ValDecl "x" (TyNamed "coordinate") TmZero
  , ValDecl "y" (TyNamed "coordinate") TmZero
  ]

-- =============================================================================
-- Exercise 3: Signature Matching
-- =============================================================================

-- Target signature
exercise3Sig :: Signature
exercise3Sig = Sig
  [ TypeSpec "t" Nothing  -- Abstract type
  , ValSpec "value" (TyNamed "t")
  , ValSpec "increment" (TyArr (TyNamed "t") (TyNamed "t"))
  ]

-- Solution: Implementation using Nat
exercise3 :: ModExpr
exercise3 = Struct
  [ TypeDecl "t" (Just TyNat)
  , ValDecl "value" (TyNamed "t") TmZero
  , ValDecl "increment" (TyArr (TyNamed "t") (TyNamed "t"))
      (Lam "x" (TyNamed "t") (TmSucc (Var "x")))
  ]

-- =============================================================================
-- Exercise 4: Sealing for Information Hiding
-- =============================================================================

-- Solution: Secret module with abstract password type
exercise4 :: ModExpr
exercise4 = Seal
  ( Struct
      [ TypeDecl "password" (Just TyNat)
      , ValDecl "create" (TyArr TyNat (TyNamed "password"))
          (Lam "n" TyNat (Var "n"))
      , ValDecl "verify" (TyArr (TyNamed "password") (TyArr TyNat TyBool))
          (Lam "p" (TyNamed "password")
            (Lam "n" TyNat
              (TmIsZero (Var "p"))))  -- Simplified: just check if zero
      ]
  )
  ( Sig
      [ TypeSpec "password" Nothing  -- Abstract!
      , ValSpec "create" (TyArr TyNat (TyNamed "password"))
      , ValSpec "verify" (TyArr (TyNamed "password") (TyArr TyNat TyBool))
      ]
  )

-- =============================================================================
-- Exercise 5: Simple Functor
-- =============================================================================

-- Solution: Successor functor
exercise5 :: ModExpr
exercise5 = Functor "X"
  (Sig [ValSpec "n" TyNat])
  (Struct [ValDecl "next" TyNat (TmSucc (TmModProj (ModPath ["X"] "n") "n"))])

-- Test application
exercise5Test :: ModExpr
exercise5Test = ModApp
  exercise5
  (Struct [ValDecl "n" TyNat (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))))])
  -- n = 5

-- =============================================================================
-- Exercise 6: Parameterized Container
-- =============================================================================

-- Solution: MakeBox functor
exercise6 :: ModExpr
exercise6 = Functor "Elem"
  (Sig [TypeSpec "t" Nothing])
  (Struct
    [ TypeDecl "elem" (Just (TyNamed "t"))
    , TypeDecl "box" (Just (TyRecord (Map.fromList [("content", TyNamed "elem")])))
    , ValDecl "make" (TyArr (TyNamed "elem") (TyNamed "box"))
        (Lam "x" (TyNamed "elem")
          (TmRecord (Map.fromList [("content", Var "x")])))
    , ValDecl "get" (TyArr (TyNamed "box") (TyNamed "elem"))
        (Lam "b" (TyNamed "box")
          (TmProj (Var "b") "content"))
    ])

-- =============================================================================
-- Exercise 7: Abstract Stack
-- =============================================================================

-- Solution: Abstract stack module
exercise7 :: ModExpr
exercise7 = Seal
  ( Struct
      [ TypeDecl "stack" (Just TyNat)
      , ValDecl "empty" (TyNamed "stack") TmZero
      , ValDecl "push" (TyArr TyNat (TyArr (TyNamed "stack") (TyNamed "stack")))
          (Lam "n" TyNat
            (Lam "s" (TyNamed "stack")
              (TmSucc (Var "s"))))
      , ValDecl "isEmpty" (TyArr (TyNamed "stack") TyBool)
          (Lam "s" (TyNamed "stack")
            (TmIsZero (Var "s")))
      , ValDecl "size" (TyArr (TyNamed "stack") TyNat)
          (Lam "s" (TyNamed "stack") (Var "s"))
      ]
  )
  ( Sig
      [ TypeSpec "stack" Nothing  -- Abstract type
      , ValSpec "empty" (TyNamed "stack")
      , ValSpec "push" (TyArr TyNat (TyArr (TyNamed "stack") (TyNamed "stack")))
      , ValSpec "isEmpty" (TyArr (TyNamed "stack") TyBool)
      , ValSpec "size" (TyArr (TyNamed "stack") TyNat)
      ]
  )

-- =============================================================================
-- Exercise 8: Nested Modules
-- =============================================================================

-- Solution: Math module with nested modules
exercise8 :: ModExpr
exercise8 = Struct
  [ ModDecl "Basic"
      (Struct
        [ ValDecl "id" (TyArr TyNat TyNat)
            (Lam "x" TyNat (Var "x"))
        ])
  , ModDecl "Advanced"
      (Struct
        [ ValDecl "double" (TyArr TyNat TyNat)
            (Lam "x" TyNat (TmSucc (TmSucc (Var "x"))))
        ])
  ]

-- =============================================================================
-- Exercise 9: Functor with Type
-- =============================================================================

-- Solution: MakeCounter functor
exercise9 :: ModExpr
exercise9 = Functor "Base"
  (Sig [ TypeSpec "t" Nothing
       , ValSpec "zero" (TyNamed "t")
       ])
  (Struct
    [ TypeDecl "counter" (Just (TyNamed "t"))
    , ValDecl "initial" (TyNamed "counter")
        (TmModProj (ModPath ["Base"] "zero") "zero")
    ])

-- =============================================================================
-- Exercise 10: Multiple Component Signature
-- =============================================================================

-- Target signature
exercise10Sig :: Signature
exercise10Sig = Sig
  [ TypeSpec "key" (Just TyNat)
  , TypeSpec "value" (Just TyBool)
  , TypeSpec "entry" (Just (TyRecord (Map.fromList
      [("k", TyNamed "key"), ("v", TyNamed "value")])))
  , ValSpec "make" (TyArr (TyNamed "key")
      (TyArr (TyNamed "value") (TyNamed "entry")))
  ]

-- Solution: Implementation
exercise10 :: ModExpr
exercise10 = Struct
  [ TypeDecl "key" (Just TyNat)
  , TypeDecl "value" (Just TyBool)
  , TypeDecl "entry" (Just (TyRecord (Map.fromList
      [("k", TyNamed "key"), ("v", TyNamed "value")])))
  , ValDecl "make" (TyArr (TyNamed "key")
      (TyArr (TyNamed "value") (TyNamed "entry")))
      (Lam "k" (TyNamed "key")
        (Lam "v" (TyNamed "value")
          (TmRecord (Map.fromList [("k", Var "k"), ("v", Var "v")]))))
  ]

-- =============================================================================
-- Exercise 11: Functor Composition
-- =============================================================================

-- F functor
functorF :: ModExpr
functorF = Functor "X"
  (Sig [ValSpec "n" TyNat])
  (Struct [ValDecl "m" TyNat
    (TmSucc (TmModProj (ModPath ["X"] "n") "n"))])

-- G functor
functorG :: ModExpr
functorG = Functor "Y"
  (Sig [ValSpec "m" TyNat])
  (Struct [ValDecl "p" TyNat
    (TmSucc (TmModProj (ModPath ["Y"] "m") "m"))])

-- Composition: G(F(input))
exercise11 :: ModExpr
exercise11 = ModApp functorG
  (ModApp functorF
    (Struct [ValDecl "n" TyNat TmZero]))

-- Result: p = 2 (0 -> 1 -> 2)

-- =============================================================================
-- Exercise 12: Width Subtyping
-- =============================================================================

-- This demonstrates width subtyping
exercise12 :: ModExpr
exercise12 = Seal
  ( Struct
      [ ValDecl "x" TyNat (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))))  -- 5
      , ValDecl "y" TyNat (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero))))))))))  -- 10
      , ValDecl "z" TyBool TmTrue
      ]
  )
  ( Sig
      [ ValSpec "x" TyNat
      , ValSpec "y" TyNat
      -- Note: z is NOT in the signature, so it's hidden
      ]
  )

-- =============================================================================
-- Exercise 13: Two-Parameter Functor
-- =============================================================================

-- Solution: Nested functors for two parameters
exercise13 :: ModExpr
exercise13 = Functor "X"
  (Sig [TypeSpec "t" Nothing])
  (Functor "Y"
    (Sig [TypeSpec "u" Nothing])
    (Struct
      [ TypeDecl "pair" (Just (TyRecord (Map.fromList
          [ ("fst", TyNamed "t")
          , ("snd", TyNamed "u")
          ])))
      ]))

-- =============================================================================
-- Exercise 14: Abstract Type with Operations
-- =============================================================================

-- Solution: Counter module with abstract type
exercise14 :: ModExpr
exercise14 = Seal
  ( Struct
      [ TypeDecl "counter" (Just TyNat)
      , ValDecl "zero" (TyNamed "counter") TmZero
      , ValDecl "inc" (TyArr (TyNamed "counter") (TyNamed "counter"))
          (Lam "c" (TyNamed "counter") (TmSucc (Var "c")))
      , ValDecl "dec" (TyArr (TyNamed "counter") (TyNamed "counter"))
          (Lam "c" (TyNamed "counter") (TmPred (Var "c")))
      , ValDecl "toNat" (TyArr (TyNamed "counter") TyNat)
          (Lam "c" (TyNamed "counter") (Var "c"))
      ]
  )
  ( Sig
      [ TypeSpec "counter" Nothing  -- Abstract!
      , ValSpec "zero" (TyNamed "counter")
      , ValSpec "inc" (TyArr (TyNamed "counter") (TyNamed "counter"))
      , ValSpec "dec" (TyArr (TyNamed "counter") (TyNamed "counter"))
      , ValSpec "toNat" (TyArr (TyNamed "counter") TyNat)
      ]
  )

-- =============================================================================
-- Exercise 15: Dependent Module
-- =============================================================================

-- Solution: Modules referencing each other
exercise15 :: ModExpr
exercise15 = Struct
  [ ModDecl "Base"
      (Struct
        [ TypeDecl "t" (Just TyNat)
        , ValDecl "zero" (TyNamed "t") TmZero
        ])
  , ModDecl "Extended"
      (Struct
        [ TypeDecl "u" (Just (TyNamed "t"))  -- References Base.t
        , ValDecl "one" (TyNamed "u")
            (TmSucc (TmModProj (ModPath ["Base"] "zero") "zero"))
        ])
  ]

-- =============================================================================
-- Helper Functions
-- =============================================================================

-- Type check an exercise solution
checkExercise :: String -> ModExpr -> IO ()
checkExercise name modExpr = do
  putStrLn $ "=== " ++ name ++ " ==="
  case typeCheckMod emptyContext modExpr of
    Left err -> putStrLn $ "Error: " ++ err
    Right sig -> do
      putStrLn "Success!"
      putStrLn $ "Signature: " ++ show sig
  putStrLn ""

-- Run all exercise checks
runAllExercises :: IO ()
runAllExercises = do
  checkExercise "Exercise 1" exercise1
  checkExercise "Exercise 2" exercise2
  checkExercise "Exercise 3" exercise3
  checkExercise "Exercise 4" exercise4
  checkExercise "Exercise 5" exercise5
  checkExercise "Exercise 6" exercise6
  checkExercise "Exercise 7" exercise7
  checkExercise "Exercise 8" exercise8
  checkExercise "Exercise 9" exercise9
  checkExercise "Exercise 10" exercise10
  checkExercise "Exercise 11" exercise11
  checkExercise "Exercise 12" exercise12
  checkExercise "Exercise 13" exercise13
  checkExercise "Exercise 14" exercise14
  checkExercise "Exercise 15" exercise15
