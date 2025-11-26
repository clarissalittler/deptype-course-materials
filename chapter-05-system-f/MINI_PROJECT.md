# Chapter 5 Mini-Project: Church Encoding Playground

## Overview

Build an **interactive playground** for Church encodings that lets users define and test Church-encoded data types in System F.

**Time estimate**: 3-4 hours

---

## Learning Objectives

- Master Church encodings
- Understand parametricity through examples
- Practice with explicit type abstraction

---

## The Project

### Features

1. **Built-in Church encodings**: Booleans, Naturals, Pairs, Lists
2. **Evaluation**: Reduce Church-encoded expressions
3. **Conversion**: Convert between Church and native representations
4. **Testing**: Verify properties of Church encodings

---

## Example Session

```
Church Encoding Playground
==========================

> :define true = Λα. λt:α. λf:α. t
Defined: true : ∀α. α → α → α

> :define false = Λα. λt:α. λf:α. f
Defined: false : ∀α. α → α → α

> :define not = λb:(∀α. α → α → α). Λα. λt:α. λf:α. b [α] f t
Defined: not : (∀α. α → α → α) → ∀α. α → α → α

> :eval not true
Result: Λα. λt:α. λf:α. f
This is: false

> :define zero = Λα. λs:α→α. λz:α. z
Defined: zero : ∀α. (α → α) → α → α

> :define succ = λn:(∀α. (α→α)→α→α). Λα. λs:α→α. λz:α. s (n [α] s z)
Defined: succ : Nat → Nat

> :eval succ (succ zero)
Result: Λα. λs:α→α. λz:α. s (s z)
This is: 2

> :toNat succ (succ (succ zero))
3

> :fromNat 5
Λα. λs:α→α. λz:α. s (s (s (s (s z))))
```

---

## Specification

### Step 1: Built-in Encodings

```haskell
-- Built-in Church encodings
builtins :: [(String, Term, Type)]
builtins =
  [ ("true",  churchTrue,  boolType)
  , ("false", churchFalse, boolType)
  , ("not",   churchNot,   boolType :-> boolType)
  , ("and",   churchAnd,   boolType :-> boolType :-> boolType)
  , ("or",    churchOr,    boolType :-> boolType :-> boolType)
  , ("zero",  churchZero,  natType)
  , ("succ",  churchSucc,  natType :-> natType)
  , ("plus",  churchPlus,  natType :-> natType :-> natType)
  , ("mult",  churchMult,  natType :-> natType :-> natType)
  , ("pair",  churchPair,  pairType)
  , ("fst",   churchFst,   fstType)
  , ("snd",   churchSnd,   sndType)
  ]

boolType = Forall "α" (TVar "α" :-> TVar "α" :-> TVar "α")
natType  = Forall "α" ((TVar "α" :-> TVar "α") :-> TVar "α" :-> TVar "α")
```

### Step 2: Conversion Functions

```haskell
-- Convert Church numeral to Int
churchToNat :: Term -> Maybe Int
churchToNat term = eval $ App (App (TyApp term natTy) succFn) zeroVal
  where
    natTy = -- Native Nat type representation
    succFn = -- Function that increments
    zeroVal = -- Zero

-- Convert Int to Church numeral
natToChurch :: Int -> Term
natToChurch 0 = churchZero
natToChurch n = App churchSucc (natToChurch (n-1))

-- Convert Church boolean to Bool
churchToBool :: Term -> Maybe Bool
churchToBool term = eval $ App (App (TyApp term boolTy) trueVal) falseVal
```

### Step 3: REPL Commands

```haskell
data Command
  = Define String Term
  | Eval Term
  | TypeOf Term
  | ToNat Term
  | FromNat Int
  | ToBool Term
  | FromBool Bool
  | Help
  | Quit
```

---

## Starter Code

```haskell
module ChurchPlayground where

import Syntax
import Eval
import TypeCheck

-- Church Boolean type
boolTy :: Type
boolTy = TForall "α" $ TVar "α" `TArr` TVar "α" `TArr` TVar "α"

-- Church Nat type
natTy :: Type
natTy = TForall "α" $ (TVar "α" `TArr` TVar "α") `TArr` TVar "α" `TArr` TVar "α"

-- Church true: Λα. λt:α. λf:α. t
churchTrue :: Term
churchTrue = TyAbs "α" $
  Lam "t" (TVar "α") $
  Lam "f" (TVar "α") $
  Var "t"

-- Church false: Λα. λt:α. λf:α. f
churchFalse :: Term
churchFalse = TyAbs "α" $
  Lam "t" (TVar "α") $
  Lam "f" (TVar "α") $
  Var "f"

-- Church zero: Λα. λs:α→α. λz:α. z
churchZero :: Term
churchZero = TyAbs "α" $
  Lam "s" (TVar "α" `TArr` TVar "α") $
  Lam "z" (TVar "α") $
  Var "z"

-- Church successor: λn. Λα. λs:α→α. λz:α. s (n [α] s z)
churchSucc :: Term
churchSucc = Lam "n" natTy $
  TyAbs "α" $
  Lam "s" (TVar "α" `TArr` TVar "α") $
  Lam "z" (TVar "α") $
  App (Var "s")
      (App (App (TyApp (Var "n") (TVar "α")) (Var "s")) (Var "z"))

-- Convert Church numeral to Int for display
toNativeNat :: Term -> Int
toNativeNat term =
  -- Apply to increment function and 0
  undefined  -- Your implementation!

-- REPL loop
repl :: IO ()
repl = do
  putStrLn "Church Encoding Playground"
  putStrLn "Type :help for commands"
  loop Map.empty

loop :: Env -> IO ()
loop env = do
  putStr "> "
  line <- getLine
  case parseCommand line of
    Just (Define name term) -> do
      case typeCheck env term of
        Right ty -> do
          putStrLn $ "Defined: " ++ name ++ " : " ++ show ty
          loop (Map.insert name (term, ty) env)
        Left err -> do
          putStrLn $ "Error: " ++ err
          loop env
    Just (Eval term) -> do
      let result = eval term
      putStrLn $ "Result: " ++ pretty result
      -- Try to identify what it is
      case identify result of
        Just desc -> putStrLn $ "This is: " ++ desc
        Nothing -> return ()
      loop env
    -- ... handle other commands
```

---

## Extension Ideas

### 1. Lists
Add Church-encoded lists with operations.

### 2. Maybe/Option
Add Church-encoded Option type.

### 3. Arithmetic Tests
Verify: `plus (succ zero) (succ zero) = succ (succ zero)`

### 4. Free Theorem Demo
Show parametricity in action.

---

## Testing

```haskell
tests :: [(String, Term, String)]
tests =
  [ ("not true = false",
     App churchNot churchTrue,
     "false")
  , ("succ zero = 1",
     App churchSucc churchZero,
     "1")
  , ("plus 2 3 = 5",
     App (App churchPlus (fromNat 2)) (fromNat 3),
     "5")
  ]
```

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Booleans work | 20 |
| Naturals work | 25 |
| Pairs work | 20 |
| Conversion functions | 20 |
| Interactive REPL | 15 |
