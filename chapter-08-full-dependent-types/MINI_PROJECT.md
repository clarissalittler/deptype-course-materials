# Chapter 8 Mini-Project: Mini Proof Assistant

## Overview

Build a **mini proof assistant** that can verify simple mathematical proofs about natural numbers using dependent types.

**Time estimate**: 5-6 hours

---

## Learning Objectives

- Apply full dependent types to theorem proving
- Use equality types and the J eliminator
- Understand proofs as programs

---

## The Project

### Features

1. **Propositions as types**: Express theorems as types
2. **Proofs as terms**: Verify proofs by type checking
3. **Built-in tactics**: `refl`, `sym`, `trans`, `cong`
4. **Natural number properties**: Prove basic arithmetic facts

---

## Example Session

```
Mini Proof Assistant
====================

> -- Define proposition: 0 + n = n
> theorem plus_zero_left : (n : Nat) -> Eq Nat (plus Zero n) n
> proof plus_zero_left n = refl n

Theorem plus_zero_left verified ✓

> -- Define proposition: n + 0 = n (harder!)
> theorem plus_zero_right : (n : Nat) -> Eq Nat (plus n Zero) n
> proof plus_zero_right Zero = refl Zero
> proof plus_zero_right (Succ n) = cong Succ (plus_zero_right n)

Theorem plus_zero_right verified ✓

> -- Symmetry
> theorem my_sym : (a : Nat) -> (b : Nat) -> Eq Nat a b -> Eq Nat b a
> proof my_sym a b p = sym p

Theorem my_sym verified ✓
```

---

## Specification

### Step 1: Core Types

```haskell
-- Natural numbers
data Nat = Zero | Succ Nat

-- Equality type
data Eq : (A : Type) -> A -> A -> Type where
  Refl : (x : A) -> Eq A x x

-- Addition
plus : Nat -> Nat -> Nat
plus Zero     n = n
plus (Succ m) n = Succ (plus m n)
```

### Step 2: Basic Lemmas

```haskell
-- Reflexivity (built-in)
refl : (x : A) -> Eq A x x
refl x = Refl x

-- Symmetry
sym : Eq A x y -> Eq A y x
sym (Refl x) = Refl x

-- Transitivity
trans : Eq A x y -> Eq A y z -> Eq A x z
trans (Refl x) (Refl _) = Refl x

-- Congruence
cong : (f : A -> B) -> Eq A x y -> Eq B (f x) (f y)
cong f (Refl x) = Refl (f x)
```

### Step 3: Proof Checker

```haskell
-- Check if a term proves a proposition
checkProof :: Type -> Term -> Either String ()
checkProof prop proof =
  case typeCheck proof of
    Right ty | ty == prop -> Right ()
    Right ty -> Left $ "Type mismatch: expected " ++ show prop ++
                       " but got " ++ show ty
    Left err -> Left $ "Type error: " ++ err
```

---

## Starter Code

```haskell
module MiniProver where

-- Natural numbers
data Nat = Zero | Succ Nat
  deriving (Show, Eq)

-- Expressions (terms and types unified)
data Expr
  = Var String
  | App Expr Expr
  | Lam String Expr Expr    -- Lam x type body
  | Pi String Expr Expr     -- Pi x type body (dependent function)
  | Nat_                    -- Nat type
  | Zero_                   -- Zero constructor
  | Succ_                   -- Succ constructor
  | Eq_ Expr Expr Expr      -- Eq A x y
  | Refl_ Expr              -- Refl x
  | Type_                   -- Type (universe)
  | NatElim Expr Expr Expr Expr  -- Eliminator
  deriving (Show, Eq)

-- Type checking context
type Ctx = [(String, Expr)]

-- Type checking
typeOf :: Ctx -> Expr -> Either String Expr
typeOf ctx expr = case expr of
  Var x -> case lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Unbound variable: " ++ x

  -- Nat constructors
  Zero_ -> Right Nat_
  App Succ_ n -> do
    ty <- typeOf ctx n
    if ty == Nat_
      then Right Nat_
      else Left "Succ expects Nat"

  -- Refl
  Refl_ x -> do
    ty <- typeOf ctx x
    Right $ Eq_ ty x x

  -- Function application
  App f a -> do
    fty <- typeOf ctx f
    case fty of
      Pi x aty bty -> do
        aty' <- typeOf ctx a
        if aty == aty'
          then Right $ subst x a bty
          else Left "Argument type mismatch"
      _ -> Left "Expected function type"

  -- Lambda
  Lam x ty body -> do
    bodyTy <- typeOf ((x, ty) : ctx) body
    Right $ Pi x ty bodyTy

  -- ... more cases

  _ -> Left $ "Cannot infer type of: " ++ show expr

-- Substitution
subst :: String -> Expr -> Expr -> Expr
subst x s (Var y) | x == y    = s
                  | otherwise = Var y
subst x s (App f a) = App (subst x s f) (subst x s a)
subst x s (Lam y ty body)
  | x == y    = Lam y (subst x s ty) body
  | otherwise = Lam y (subst x s ty) (subst x s body)
subst x s (Pi y ty body)
  | x == y    = Pi y (subst x s ty) body
  | otherwise = Pi y (subst x s ty) (subst x s body)
subst x s (Eq_ a l r) = Eq_ (subst x s a) (subst x s l) (subst x s r)
subst x s (Refl_ t) = Refl_ (subst x s t)
subst _ _ e = e

-- Normalize (reduce to normal form)
normalize :: Expr -> Expr
normalize expr = case expr of
  App (Lam x _ body) arg -> normalize (subst x arg body)
  App f a ->
    let f' = normalize f
        a' = normalize a
    in case f' of
         Lam x _ body -> normalize (subst x a' body)
         _ -> App f' a'
  _ -> expr

-- Prove: 0 + n = n
plus_zero_left :: Expr
plus_zero_left =
  Lam "n" Nat_ $
    Refl_ (Var "n")
  -- Type: Pi n : Nat. Eq Nat (plus Zero n) n
  -- Since plus Zero n normalizes to n, Refl works!

-- Prove: n + 0 = n (by induction)
plus_zero_right :: Expr
plus_zero_right = undefined  -- Your implementation!

-- REPL
main :: IO ()
main = do
  putStrLn "Mini Proof Assistant"
  putStrLn "===================="

  -- Test plus_zero_left
  let prop1 = Pi "n" Nat_ (Eq_ Nat_ (App (App plus Zero_) (Var "n")) (Var "n"))
  case typeOf [] plus_zero_left of
    Right ty ->
      if normalize ty == normalize prop1
        then putStrLn "plus_zero_left: VERIFIED ✓"
        else putStrLn $ "plus_zero_left: FAILED - wrong type"
    Left err -> putStrLn $ "plus_zero_left: ERROR - " ++ err

-- Helper: plus function
plus :: Expr
plus = undefined  -- Define plus as a term
```

---

## Theorems to Prove

### Level 1: Easy
```
1. plus_zero_left:  0 + n = n
2. plus_succ_right: n + (1 + m) = 1 + (n + m)
```

### Level 2: Medium
```
3. plus_zero_right: n + 0 = n        (needs induction)
4. plus_succ_left:  (1 + n) + m = 1 + (n + m)
```

### Level 3: Hard
```
5. plus_comm:       n + m = m + n    (needs helper lemmas)
6. plus_assoc:      (a + b) + c = a + (b + c)
```

---

## Extension Ideas

### 1. More Data Types
Add lists and prove properties about `length` and `append`.

### 2. Interactive Mode
Let users enter proofs step by step.

### 3. Proof Search
Automatically find simple proofs.

### 4. Better Error Messages
Show where proofs go wrong.

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Core type checker | 30 |
| Equality type works | 20 |
| Basic lemmas (refl, sym, cong) | 20 |
| At least 2 theorems verified | 20 |
| Extension or more theorems | 10 |
