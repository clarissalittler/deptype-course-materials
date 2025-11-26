# Chapter 2 Mini-Project: Type Error Explainer

## Overview

Build a **type error explainer** that not only reports type errors but explains *why* they occurred and *how* to fix them.

**Time estimate**: 3-4 hours

---

## Learning Objectives

- Deepen understanding of type checking
- Practice generating helpful error messages
- Understand common type errors and their causes

---

## The Project

### Input
A potentially ill-typed STLC term.

### Output
A detailed error explanation with:
1. What went wrong
2. Why it's an error
3. How to fix it

---

## Example

### Input
```
(\x:Nat. x) true
```

### Output
```
TYPE ERROR at position 1:12

  (\x:Nat. x) true
             ^^^^

Problem: Function expected Nat but received Bool

Explanation:
  The function (\x:Nat. x) has type Nat → Nat.
  This means it expects an argument of type Nat.
  But 'true' has type Bool, not Nat.

How to fix:
  Option 1: Change the argument to a Nat value
    (\x:Nat. x) 0

  Option 2: Change the function to accept Bool
    (\x:Bool. x) true
```

---

## Specification

### Step 1: Enhanced Error Type

```haskell
data TypeError
  = TypeMismatch
      { expected :: Type
      , actual :: Type
      , location :: Position
      , context :: String
      }
  | UnboundVariable
      { varName :: String
      , location :: Position
      , suggestions :: [String]
      }
  | NotAFunction
      { actualType :: Type
      , location :: Position
      }
  | OtherError String
```

### Step 2: Error Explanation

```haskell
explain :: TypeError -> String
explain (TypeMismatch exp act loc ctx) =
  "Expected " ++ show exp ++ " but got " ++ show act
  -- Plus detailed explanation...
```

### Step 3: Fix Suggestions

```haskell
suggestFix :: TypeError -> [String]
suggestFix (TypeMismatch exp act _ _) =
  -- Generate possible fixes
```

---

## Starter Code

```haskell
module TypeErrorExplainer where

import Syntax
import TypeCheck

data Position = Position Int Int  -- line, column

data DetailedError = DetailedError
  { errorType :: String
  , location :: Maybe Position
  , sourceSnippet :: String
  , explanation :: String
  , howToFix :: [String]
  }

-- Main function
explainError :: String -> Term -> Either DetailedError Type
explainError source term = case typeOf emptyCtx term of
  Right ty -> Right ty
  Left err -> Left (elaborate source err)

-- Turn simple error into detailed explanation
elaborate :: String -> String -> DetailedError
elaborate source simpleErr = undefined  -- Your implementation!

-- Generate code snippet with error highlighted
highlight :: String -> Position -> String
highlight source pos = undefined

-- Suggest fixes based on error type
suggestFixes :: TypeError -> [String]
suggestFixes = undefined
```

---

## Error Categories to Handle

### 1. Type Mismatch
```
(\x:Nat. x + 1) true
-- Expected Nat, got Bool
```

### 2. Unbound Variable
```
\x:Nat. y
-- Variable 'y' not in scope
-- Did you mean 'x'?
```

### 3. Not a Function
```
5 3
-- Cannot apply: 5 is not a function
-- 5 has type Nat
```

### 4. Wrong Number of Arguments
```
(\x:Nat. \y:Nat. x + y) 5
-- Function expects 2 arguments
-- Only 1 provided
```

---

## Example Detailed Outputs

### Unbound Variable
```
TYPE ERROR: Unbound variable

  \x:Nat. y + x
          ^

The variable 'y' is not defined in this scope.

In scope: x (Nat)

Did you mean: x?

How to fix:
  1. Define 'y' before using it:
     \y:Nat. \x:Nat. y + x

  2. Use a variable that's in scope:
     \x:Nat. x + x
```

### Not a Function
```
TYPE ERROR: Not a function

  (5) (3)
   ^

You're trying to call '5' as if it were a function,
but 5 has type Nat, not a function type.

In STLC, only terms of type (A → B) can be applied.

How to fix:
  Make sure the first term is a function:
    (\x:Nat. x) 3
```

---

## Extension Ideas

### 1. Interactive Mode
Let users type terms and get instant feedback.

### 2. Fix Suggestions
Actually apply suggested fixes and show results.

### 3. Visual Type Derivation
Show the type derivation tree with the error highlighted.

### 4. Multi-Error Reporting
Report all errors, not just the first one.

---

## Testing

```haskell
testCases :: [(String, String)]
testCases =
  [ ("(\\x:Nat. x) true", "Type mismatch")
  , ("\\x:Nat. y", "Unbound variable")
  , ("5 3", "Not a function")
  , ("\\x:Nat. x x", "Occurs check")
  ]

main = forM_ testCases $ \(code, expected) -> do
  putStrLn $ "Testing: " ++ code
  case explainError code (parse code) of
    Left err -> print err
    Right ty -> putStrLn $ "OK: " ++ show ty
```

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Handles type mismatch | 25 |
| Handles unbound variable | 25 |
| Handles not-a-function | 20 |
| Clear explanations | 15 |
| Fix suggestions | 15 |

---

## Resources

- `src/TypeCheck.hs` - Type checker
- `COMMON_MISTAKES.md` - Common error patterns
- Elm's error messages for inspiration
