# Haskell Quick Tutorial for Type Systems Course

## Purpose

This course uses Haskell to implement type systems. You don't need to be a Haskell expert, but you need to read and understand the code. This tutorial covers the Haskell features used in the course.

## Table of Contents

1. [Basic Syntax](#basic-syntax)
2. [Data Types](#data-types)
3. [Pattern Matching](#pattern-matching)
4. [Functions](#functions)
5. [Type Signatures](#type-signatures)
6. [Common Functions Used](#common-functions-used)
7. [Monads (Just Enough)](#monads-just-enough)
8. [Reading Course Code](#reading-course-code)

---

## Basic Syntax

### Comments

```haskell
-- Single line comment

{- Multi-line
   comment -}
```

### Let Bindings

```haskell
let x = 5
    y = 10
in x + y    -- Result: 15
```

### Where Clauses

```haskell
result = x + y
  where
    x = 5
    y = 10
```

### If-Then-Else

```haskell
max x y = if x > y then x else y
```

**Note**: `else` is required (not like Python)!

---

## Data Types

### Defining Data Types

```haskell
-- Simple enumeration
data Bool = True | False

-- With fields
data Point = Point Int Int

-- Recursive
data List a = Nil | Cons a (List a)

-- Multiple constructors with fields
data Maybe a = Nothing | Just a
```

### Type Parameters

```haskell
data Pair a b = Pair a b

-- Usage
myPair :: Pair Int String
myPair = Pair 42 "hello"
```

### Records (Named Fields)

```haskell
data Person = Person
  { name :: String
  , age :: Int
  }

-- Create
john = Person { name = "John", age = 30 }

-- Access
getName :: Person -> String
getName p = name p    -- or: getName = name
```

### Type Synonyms

```haskell
type String = [Char]
type Name = String
type Age = Int
```

---

## Pattern Matching

### Basic Pattern Matching

```haskell
-- Match on constructors
not :: Bool -> Bool
not True = False
not False = True

-- Match on values
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)
```

### Case Expressions

```haskell
describe :: Maybe a -> String
describe x = case x of
  Nothing -> "empty"
  Just _  -> "has value"
```

### Pattern Guards

```haskell
sign :: Int -> String
sign n
  | n > 0     = "positive"
  | n < 0     = "negative"
  | otherwise = "zero"
```

### Nested Patterns

```haskell
-- Matching pairs
addPair :: (Int, Int) -> Int
addPair (x, y) = x + y

-- Matching lists
head :: [a] -> a
head (x:xs) = x
head []     = error "empty list"
```

### Wildcard (_)

```haskell
-- Ignore parts you don't need
first :: (a, b) -> a
first (x, _) = x    -- Ignore second element
```

---

## Functions

### Basic Definition

```haskell
add :: Int -> Int -> Int
add x y = x + y

-- Call it
result = add 3 4    -- 7
```

### Lambda Functions (Anonymous)

```haskell
-- Syntax: \param1 param2 -> body
square = \x -> x * x

-- Multiple parameters
add = \x y -> x + y

-- Used inline
map (\x -> x * 2) [1, 2, 3]    -- [2, 4, 6]
```

### Partial Application (Currying)

```haskell
add :: Int -> Int -> Int
add x y = x + y

add5 = add 5        -- Partially applied
add5 10             -- 15
```

### Higher-Order Functions

```haskell
-- Function takes function as argument
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)

-- Usage
applyTwice (+3) 10    -- 16
```

### Composition

```haskell
-- (f . g) x = f (g x)
increment = (+1)
double = (*2)

doubleThenIncrement = increment . double
doubleThenIncrement 5    -- 11 (not 12!)
```

---

## Type Signatures

### Reading Type Signatures

```haskell
map :: (a -> b) -> [a] -> [b]
  --   ↑         ↑     ↑
  --   function  input output
  --            list   list
```

"map takes a function (a→b) and list of a's, returns list of b's"

### Type Variables

```haskell
id :: a -> a         -- Works for ANY type
-- a is type variable (like generics)

length :: [a] -> Int
-- List of any type → Int
```

### Type Constraints

```haskell
-- Eq a => means "a must support equality"
elem :: Eq a => a -> [a] -> Bool

-- Multiple constraints
sort :: (Ord a, Show a) => [a] -> String
```

### Function Types

```haskell
-- Functions are right-associative
Int -> Int -> Int
  = Int -> (Int -> Int)    -- Take Int, return function

-- Multi-argument functions return functions!
add :: Int -> Int -> Int
-- add 5 :: Int -> Int    -- Partially applied
```

---

## Common Functions Used

### List Functions

```haskell
-- Construction
[]              -- Empty list
[1, 2, 3]       -- List literal
1 : [2, 3]      -- Cons (prepend): [1, 2, 3]
[1, 2] ++ [3]   -- Append: [1, 2, 3]

-- Deconstruction
head [1, 2, 3]       -- 1
tail [1, 2, 3]       -- [2, 3]
null []              -- True
null [1]             -- False

-- Higher-order
map f [1, 2, 3]      -- Apply f to each element
filter p [1, 2, 3]   -- Keep elements where p is true
foldr f z [1, 2, 3]  -- Right fold
foldl f z [1, 2, 3]  -- Left fold

-- Example
map (*2) [1, 2, 3]              -- [2, 4, 6]
filter (>2) [1, 2, 3, 4]        -- [3, 4]
foldr (+) 0 [1, 2, 3]           -- 6
```

### Maybe Functions

```haskell
maybe :: b -> (a -> b) -> Maybe a -> b
-- maybe defaultValue function maybeValue

maybe 0 (*2) Nothing     -- 0
maybe 0 (*2) (Just 5)    -- 10
```

### Either Functions

```haskell
either :: (a -> c) -> (b -> c) -> Either a b -> c
-- either leftHandler rightHandler value

either (*2) length (Left 5)      -- 10
either (*2) length (Right "hi")  -- 2
```

---

## Monads (Just Enough)

### What You Need to Know

Monads appear in the course code. You don't need to fully understand them, just recognize the patterns.

### Common Pattern: `do` Notation

```haskell
-- This is monadic code
example :: Maybe Int
example = do
  x <- Just 3        -- Extract value from Maybe
  y <- Just 4
  return (x + y)     -- Wrap result in Maybe
-- Result: Just 7
```

**Mental model**: Sequence of operations that might fail.

### The `>>=` Operator (Bind)

```haskell
-- These are equivalent:
do
  x <- Just 3
  y <- Just 4
  return (x + y)

Just 3 >>= \x ->
Just 4 >>= \y ->
return (x + y)
```

### Common Monads in Course

**Maybe** - Computation that might fail:
```haskell
safeDivide :: Int -> Int -> Maybe Int
safeDivide _ 0 = Nothing
safeDivide x y = Just (x `div` y)
```

**Either** - Computation with errors:
```haskell
typeCheck :: Term -> Either TypeError Type
typeCheck t = ...
```

**State** - Stateful computation:
```haskell
-- You'll see this in type inference
infer :: Term -> StateT Int (Either TypeError) Type
```

### Pattern: Error Handling

```haskell
-- Without monads (tedious!)
case expr1 of
  Left err -> Left err
  Right val1 -> case expr2 of
    Left err -> Left err
    Right val2 -> Right (val1 + val2)

-- With monads (clean!)
do
  val1 <- expr1
  val2 <- expr2
  return (val1 + val2)
```

---

## Reading Course Code

### Chapter 1 Example - Lambda Calculus

```haskell
-- Data type definition
data Term
  = Var String              -- Variable
  | Lam String Term         -- Lambda abstraction
  | App Term Term           -- Application
  deriving (Show, Eq)

-- Pattern matching on data
eval :: Term -> Term
eval (Var x) = Var x                    -- Variable is value
eval (Lam x body) = Lam x body          -- Lambda is value
eval (App (Lam x body) arg) =           -- Beta reduction
  eval (subst x arg body)
eval (App f arg) =                      -- Reduce function first
  let f' = eval f
  in eval (App f' arg)

-- Recursive helper
subst :: String -> Term -> Term -> Term
subst x s (Var y)
  | x == y    = s        -- Replace x with s
  | otherwise = Var y    -- Keep other variables
subst x s (Lam y body)
  | x == y    = Lam y body               -- Shadowing
  | otherwise = Lam y (subst x s body)   -- Recurse into body
subst x s (App t1 t2) =
  App (subst x s t1) (subst x s t2)      -- Recurse into both
```

### Chapter 2 Example - Type Checking

```haskell
-- Type definition
data Type
  = TyNat
  | TyBool
  | TyFun Type Type
  deriving (Show, Eq)

-- Environment (context)
type Env = [(String, Type)]

-- Type checking with Maybe (might fail)
typeCheck :: Env -> Term -> Maybe Type
typeCheck env (Var x) =
  lookup x env                           -- Maybe Type

typeCheck env (Lam x t body) =
  do
    -- Add x:t to environment
    let env' = (x, t) : env
    bodyType <- typeCheck env' body      -- Check body
    return (TyFun t bodyType)            -- Return function type

typeCheck env (App t1 t2) =
  do
    funType <- typeCheck env t1
    argType <- typeCheck env t2
    case funType of
      TyFun t1 t2 | t1 == argType -> return t2
      _ -> Nothing                       -- Type error
```

### Chapter 4 Example - Type Inference

```haskell
-- Type with variables
data Type
  = TyVar String      -- Type variable
  | TyFun Type Type
  deriving (Show, Eq)

-- Substitution
type Subst = [(String, Type)]

-- Apply substitution
applySubst :: Subst -> Type -> Type
applySubst s (TyVar x) =
  case lookup x s of
    Just t  -> t
    Nothing -> TyVar x
applySubst s (TyFun t1 t2) =
  TyFun (applySubst s t1) (applySubst s t2)

-- Unification
unify :: Type -> Type -> Maybe Subst
unify (TyVar x) t = return [(x, t)]     -- Bind x to t
unify t (TyVar x) = return [(x, t)]
unify (TyFun t1 t2) (TyFun s1 s2) =
  do
    s1' <- unify t1 s1                   -- Unify arguments
    let t2' = applySubst s1' t2
    let s2' = applySubst s1' s2
    s2'' <- unify t2' s2'                -- Unify results
    return (s1' ++ s2'')                 -- Compose substitutions
unify _ _ = Nothing                      -- Mismatch
```

---

## Haskell Features You Can Skip

For this course, you CAN skip or skim:
- Advanced type classes (Functor, Applicative, beyond basics)
- Monad transformers (though they appear)
- Lens/Prisms
- Template Haskell
- Advanced GHC extensions
- Lazy evaluation details (helps to know basics)

**Focus on**: Data types, pattern matching, basic functions!

---

## Quick Lookup: Common Syntax

| Haskell | Meaning |
|---------|---------|
| `::` | "has type" |
| `->` | Function type arrow |
| `=>` | Type constraint |
| `\x ->` | Lambda function |
| `<-` | Bind in do-notation |
| `x:xs` | List pattern (head:tail) |
| `[x]` | List of x |
| `(x, y)` | Tuple/pair |
| `_` | Wildcard (ignore) |
| `` `f` `` | Infix function call |
| `$` | Function application (low precedence) |
| `.` | Function composition |

---

## Tips for Reading Course Code

1. **Start with types**: Type signatures tell you what functions do
2. **Follow pattern matching**: Each case handles a constructor
3. **Trace small examples**: Run code mentally on simple inputs
4. **Ignore monads initially**: Focus on the logic, not the plumbing
5. **Use GHCi REPL**: Load modules, test functions interactively

### Example GHCI Session

```haskell
$ stack ghci
Prelude> :load src/Syntax.hs
*Syntax> let term = Var "x"
*Syntax> :type term
term :: Term
*Syntax> eval term
Var "x"
```

---

## Further Haskell Resources

**If you want to learn more Haskell**:
- *Learn You a Haskell for Great Good!* - Fun, gentle intro
- *Haskell Programming from First Principles* - Comprehensive
- *Real World Haskell* - Practical focus

**For this course**: The Haskell above is sufficient! Focus on type systems, not Haskell mastery.

---

## Quick Start Commands

```bash
# Build a chapter
cd chapter-01-untyped-lambda
stack build

# Run tests
stack test

# Start REPL with code loaded
stack ghci
> :load src/Syntax.hs
> :type Var

# Run the chapter REPL
stack exec untyped-lambda-repl
```

---

**Remember**: You're here to learn type systems, not become a Haskell expert! This tutorial gives you enough to read and understand the course code. Focus on the *type system concepts*, not Haskell minutiae.

Good luck! 🚀
