# Chapter 7 Mini-Project: Safe Vector Library

## Overview

Build a **safe vector library** with length-indexed vectors that prevent out-of-bounds access at compile time.

**Time estimate**: 4-5 hours

---

## Learning Objectives

- Implement dependent types in practice
- See how types prevent runtime errors
- Understand Pi and Sigma types through use

---

## The Project

### Features

1. **Length-indexed vectors**: `Vec n A`
2. **Safe operations**: `head`, `tail`, `index` that can't fail
3. **Length-aware operations**: `append`, `reverse`, `map`
4. **Type-safe indexing**: Using `Fin n`

---

## Example

```
-- Creating vectors
> let v1 = [1, 2, 3] : Vec 3 Nat
v1 : Vec 3 Nat

-- Safe head (can't be called on empty!)
> head v1
1 : Nat

-- Safe indexing with Fin
> index v1 (fin 1)
2 : Nat

> index v1 (fin 5)
TYPE ERROR: fin 5 is not a valid Fin 3

-- Append preserves lengths
> let v2 = [4, 5] : Vec 2 Nat
> append v1 v2
[1, 2, 3, 4, 5] : Vec 5 Nat
```

---

## Specification

### Step 1: Basic Types

```haskell
-- Natural numbers
data Nat = Zero | Succ Nat

-- Vectors indexed by length
data Vec :: Nat -> Type -> Type where
  Nil  : Vec Zero a
  Cons : a -> Vec n a -> Vec (Succ n) a

-- Finite sets (indices)
data Fin :: Nat -> Type where
  FZero : Fin (Succ n)
  FSucc : Fin n -> Fin (Succ n)
```

### Step 2: Safe Operations

```haskell
-- Safe head: only works on non-empty vectors
head : Vec (Succ n) a -> a
head (Cons x xs) = x

-- Safe tail
tail : Vec (Succ n) a -> Vec n a
tail (Cons x xs) = xs

-- Safe indexing
index : Vec n a -> Fin n -> a
index (Cons x xs) FZero     = x
index (Cons x xs) (FSucc i) = index xs i

-- Safe last
last : Vec (Succ n) a -> a
```

### Step 3: Length-Aware Operations

```haskell
-- Append: lengths add up!
append : Vec m a -> Vec n a -> Vec (plus m n) a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- Map preserves length
map : (a -> b) -> Vec n a -> Vec n b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

-- Reverse preserves length
reverse : Vec n a -> Vec n a

-- Zip requires same length
zip : Vec n a -> Vec n b -> Vec n (a, b)
```

---

## Starter Code

```haskell
module SafeVec where

-- Natural numbers at type and value level
data Nat = Zero | Succ Nat
  deriving (Show, Eq)

-- Type-level addition
type family Plus (m :: Nat) (n :: Nat) :: Nat where
  Plus Zero     n = n
  Plus (Succ m) n = Succ (Plus m n)

-- Vectors indexed by length
data Vec (n :: Nat) a where
  Nil  :: Vec Zero a
  Cons :: a -> Vec n a -> Vec (Succ n) a

instance Show a => Show (Vec n a) where
  show Nil = "[]"
  show (Cons x xs) = show x ++ " : " ++ show xs

-- Finite sets for safe indexing
data Fin (n :: Nat) where
  FZero :: Fin (Succ n)
  FSucc :: Fin n -> Fin (Succ n)

-- Smart constructor for Fin
fin :: Int -> Fin n
fin = undefined  -- Needs runtime checking

-- Safe head
head :: Vec (Succ n) a -> a
head (Cons x _) = x

-- Safe tail
tail :: Vec (Succ n) a -> Vec n a
tail (Cons _ xs) = xs

-- Safe indexing
index :: Vec n a -> Fin n -> a
index (Cons x _)  FZero     = x
index (Cons _ xs) (FSucc i) = index xs i

-- Your implementations:

-- Append two vectors
append :: Vec m a -> Vec n a -> Vec (Plus m n) a
append = undefined

-- Map over vector
vmap :: (a -> b) -> Vec n a -> Vec n b
vmap = undefined

-- Reverse vector
vreverse :: Vec n a -> Vec n a
vreverse = undefined

-- Zip two vectors of same length
vzip :: Vec n a -> Vec n b -> Vec n (a, b)
vzip = undefined

-- Replicate: create vector of n copies
replicate :: SNat n -> a -> Vec n a
replicate = undefined

-- Singleton Nat for runtime length
data SNat (n :: Nat) where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

-- Example usage
example :: Vec (Succ (Succ (Succ Zero))) Int
example = Cons 1 (Cons 2 (Cons 3 Nil))

main :: IO ()
main = do
  putStrLn $ "Vector: " ++ show example
  putStrLn $ "Head: " ++ show (head example)
  putStrLn $ "Index 1: " ++ show (index example (FSucc FZero))
```

---

## Extension Ideas

### 1. Take and Drop
```haskell
take :: SNat m -> Vec (Plus m n) a -> Vec m a
drop :: SNat m -> Vec (Plus m n) a -> Vec n a
```

### 2. Split
```haskell
splitAt :: SNat m -> Vec (Plus m n) a -> (Vec m a, Vec n a)
```

### 3. Bounded Append
```haskell
-- Append with maximum length
appendBounded :: Vec m a -> Vec n a -> Maybe (Vec (Plus m n) a)
```

### 4. Matrix Operations
```haskell
type Matrix m n a = Vec m (Vec n a)
transpose :: Matrix m n a -> Matrix n m a
```

### 5. Filter with Length Bound
```haskell
-- Result length is at most input length
filter :: (a -> Bool) -> Vec n a -> (m ** Vec m a)  -- Sigma type!
```

---

## Test Cases

```haskell
-- Test vectors
v3 :: Vec (Succ (Succ (Succ Zero))) Int
v3 = Cons 1 (Cons 2 (Cons 3 Nil))

v2 :: Vec (Succ (Succ Zero)) Int
v2 = Cons 4 (Cons 5 Nil)

tests :: IO ()
tests = do
  -- head always works on non-empty
  print $ head v3  -- 1

  -- index is safe
  print $ index v3 FZero  -- 1
  print $ index v3 (FSucc FZero)  -- 2

  -- append preserves types
  let v5 = append v3 v2  -- Vec 5 Int
  print v5

  -- map preserves length
  let doubled = vmap (*2) v3  -- Vec 3 Int
  print doubled

  -- These should NOT compile:
  -- head Nil              -- Empty vector!
  -- index v3 (FSucc (FSucc (FSucc FZero)))  -- Out of bounds!
```

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Basic Vec operations | 25 |
| Safe head/tail/index | 25 |
| Append with correct types | 20 |
| Map/reverse | 15 |
| Extension implemented | 15 |
