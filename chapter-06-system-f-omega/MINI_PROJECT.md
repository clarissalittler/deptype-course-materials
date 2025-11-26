# Chapter 6 Mini-Project: Type-Level Calculator

## Overview

Build a **type-level calculator** that performs arithmetic at compile time using type-level natural numbers and type operators.

**Time estimate**: 4-5 hours

---

## Learning Objectives

- Understand type-level computation
- Practice with higher-kinded types
- See type operators in action

---

## The Project

### Features

1. **Type-level naturals**: 0, 1, 2, ... as types
2. **Type-level arithmetic**: Plus, Mult, Exp at the type level
3. **Type-level comparison**: Less, Equal, etc.
4. **Normalization**: Reduce type-level expressions

---

## Example

### Type-Level Definition
```haskell
-- Types
type Zero = λα:*. λf:*→*. α
type Succ = λn:((*→*)→*→*). λα:*. λf:*→*. f (n α f)

-- Type-level numbers
type One   = Succ Zero
type Two   = Succ One
type Three = Succ Two

-- Type-level addition
type Plus = λm. λn. m n Succ
-- Plus Two Three = Five
```

### Usage
```
> :kind Three
Three :: (* → *) → * → *

> :normalize Plus Two Three
Five

> :equal (Plus Two Three) Five
true

> :less Two Three
true
```

---

## Specification

### Step 1: Type-Level Naturals

```haskell
-- Kind of type-level naturals
-- TyNat :: (* → *) → * → *

-- Zero: λf:*→*. λα:*. α
tyZero :: Type
tyZero = TyLam "f" (KArr KStar KStar) $
         TyLam "α" KStar $
         TyVar "α"

-- Successor: λn:TyNat. λf:*→*. λα:*. f (n f α)
tySucc :: Type -> Type
tySucc n = TyLam "f" (KArr KStar KStar) $
           TyLam "α" KStar $
           TyApp (TyVar "f") (TyApp (TyApp n (TyVar "f")) (TyVar "α"))
```

### Step 2: Type-Level Arithmetic

```haskell
-- Plus: λm:TyNat. λn:TyNat. m Succ n
tyPlus :: Type -> Type -> Type
tyPlus m n = TyApp (TyApp m tySucc') n
  where tySucc' = -- Type-level succ function

-- Mult: λm:TyNat. λn:TyNat. m (Plus n) Zero
tyMult :: Type -> Type -> Type
tyMult m n = undefined

-- Exp: λm:TyNat. λn:TyNat. n (Mult m) One
tyExp :: Type -> Type -> Type
tyExp m n = undefined
```

### Step 3: Normalization

```haskell
-- Normalize type to canonical form
normalizeType :: Type -> Type
normalizeType ty = case ty of
  TyVar v -> TyVar v
  TyLam v k t -> TyLam v k (normalizeType t)
  TyApp (TyLam v k body) arg ->
    normalizeType (substType v arg body)
  TyApp t1 t2 ->
    case normalizeType t1 of
      TyLam v k body -> normalizeType (substType v (normalizeType t2) body)
      t1' -> TyApp t1' (normalizeType t2)
  TyArr t1 t2 -> TyArr (normalizeType t1) (normalizeType t2)
  TyForall v k t -> TyForall v k (normalizeType t)
```

---

## Starter Code

```haskell
module TypeLevelCalc where

import Data.Map (Map)
import qualified Data.Map as Map

-- Kinds
data Kind = KStar | KArr Kind Kind
  deriving (Show, Eq)

-- Types (with type-level lambdas)
data Type
  = TyVar String
  | TyLam String Kind Type
  | TyApp Type Type
  | TyArr Type Type
  | TyForall String Kind Type
  deriving (Show, Eq)

-- Type-level naturals
tyNatKind :: Kind
tyNatKind = KArr (KArr KStar KStar) (KArr KStar KStar)

-- Zero
tyZero :: Type
tyZero = TyLam "f" (KArr KStar KStar) $
         TyLam "z" KStar $
         TyVar "z"

-- Natural number literals
tyNat :: Int -> Type
tyNat 0 = tyZero
tyNat n = tySucc (tyNat (n-1))

tySucc :: Type -> Type
tySucc n = TyLam "f" (KArr KStar KStar) $
           TyLam "z" KStar $
           TyApp (TyVar "f")
                 (TyApp (TyApp n (TyVar "f")) (TyVar "z"))

-- Type-level addition
-- Plus m n = m Succ n
-- Intuition: apply Succ m times starting from n
tyPlus :: Type -> Type -> Type
tyPlus m n = undefined  -- Your implementation!

-- Type-level multiplication
tyMult :: Type -> Type -> Type
tyMult m n = undefined  -- Your implementation!

-- Normalize a type expression
normalize :: Type -> Type
normalize = undefined  -- Your implementation!

-- Convert type-level nat back to Int (for display)
typeToInt :: Type -> Maybe Int
typeToInt ty =
  let norm = normalize ty
  in countSucc norm
  where
    countSucc t = undefined  -- Your implementation!

-- Check if two type-level nats are equal
tyEqual :: Type -> Type -> Bool
tyEqual t1 t2 = normalize t1 == normalize t2

-- REPL
main :: IO ()
main = do
  putStrLn "Type-Level Calculator"
  putStrLn "====================="
  putStrLn ""
  putStrLn "Examples:"
  putStrLn $ "  2 + 3 = " ++ show (typeToInt (tyPlus (tyNat 2) (tyNat 3)))
  putStrLn $ "  2 * 3 = " ++ show (typeToInt (tyMult (tyNat 2) (tyNat 3)))
  repl

repl :: IO ()
repl = do
  putStr "> "
  line <- getLine
  -- Parse and evaluate
  -- ... your implementation
  repl
```

---

## Extension Ideas

### 1. Predecessor and Subtraction
Implement type-level predecessor (tricky!).

### 2. Division
Implement type-level division (even trickier!).

### 3. Comparison
Implement type-level `<`, `≤`, `=`.

### 4. Fibonacci
Implement type-level Fibonacci sequence.

### 5. Proofs
Prove properties like: `Plus m n = Plus n m`

---

## Test Cases

```haskell
tests :: [(String, Type, Int)]
tests =
  [ ("0", tyNat 0, 0)
  , ("5", tyNat 5, 5)
  , ("2 + 3", tyPlus (tyNat 2) (tyNat 3), 5)
  , ("3 * 4", tyMult (tyNat 3) (tyNat 4), 12)
  , ("2^3", tyExp (tyNat 2) (tyNat 3), 8)
  ]

runTests :: IO ()
runTests = forM_ tests $ \(name, ty, expected) -> do
  let result = typeToInt ty
  putStrLn $ name ++ " = " ++ show result ++
             (if result == Just expected then " ✓" else " ✗ (expected " ++ show expected ++ ")")
```

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Type-level naturals | 25 |
| Addition works | 25 |
| Multiplication works | 20 |
| Normalization correct | 20 |
| Extension implemented | 10 |
