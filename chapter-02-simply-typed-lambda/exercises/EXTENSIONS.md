# Syntax Extensions for Chapter 2 Exercises

This document provides step-by-step guidance for implementing the exercises that require extending the STLC syntax (Exercises 2, 3, and 5).

## Table of Contents

1. [Exercise 2: Product Types](#exercise-2-product-types)
2. [Exercise 3: Sum Types](#exercise-3-sum-types)
3. [Exercise 5: Fixed Point Combinator](#exercise-5-fixed-point-combinator)
4. [Testing Your Extensions](#testing-your-extensions)

---

## Exercise 2: Product Types

Product types (pairs/tuples) allow combining multiple values into one.

### Step 1: Extend the Type Data Type

In `src/Syntax.hs`, add the product type constructor:

```haskell
data Type
  = TyVar Var
  | TyArr Type Type
  | TyBool
  | TyNat
  | TyProd Type Type    -- NEW: Product type τ₁ × τ₂
  deriving (Eq, Show, Ord)
```

### Step 2: Extend the Term Data Type

Add terms for creating and destructing pairs:

```haskell
data Term
  = ... (existing constructors)
  | TmPair Term Term    -- NEW: Pair construction ⟨t₁, t₂⟩
  | TmFst Term          -- NEW: First projection (fst t)
  | TmSnd Term          -- NEW: Second projection (snd t)
  deriving (Eq, Show)
```

### Step 3: Update Free Variables

In `freeVars`:

```haskell
freeVars (TmPair t1 t2) = freeVars t1 `Set.union` freeVars t2
freeVars (TmFst t) = freeVars t
freeVars (TmSnd t) = freeVars t
```

### Step 4: Update Substitution

In `substVar`:

```haskell
substVar x s (TmPair t1 t2) = TmPair (substVar x s t1) (substVar x s t2)
substVar x s (TmFst t) = TmFst (substVar x s t)
substVar x s (TmSnd t) = TmSnd (substVar x s t)
```

### Step 5: Add Typing Rules

In `src/TypeCheck.hs`, add these cases to `typeOf`:

```haskell
-- Pair construction
typeOf ctx (TmPair t1 t2) = do
  ty1 <- typeOf ctx t1
  ty2 <- typeOf ctx t2
  return (TyProd ty1 ty2)

-- First projection
typeOf ctx (TmFst t) = do
  ty <- typeOf ctx t
  case ty of
    TyProd ty1 ty2 -> return ty1
    _ -> Left "fst requires a pair type"

-- Second projection
typeOf ctx (TmSnd t) = do
  ty <- typeOf ctx t
  case ty of
    TyProd ty1 ty2 -> return ty2
    _ -> Left "snd requires a pair type"
```

### Step 6: Add Evaluation Rules

In `src/Eval.hs`:

```haskell
-- Check if term is a value
isValue (TmPair v1 v2) = isValue v1 && isValue v2
isValue (TmFst _) = False
isValue (TmSnd _) = False

-- Evaluation step
step (TmPair t1 t2)
  | not (isValue t1) = TmPair <$> step t1 <*> pure t2
  | not (isValue t2) = TmPair t1 <$> step t2
  | otherwise = Nothing

step (TmFst (TmPair v1 v2))
  | isValue v1 && isValue v2 = Just v1
step (TmFst t) = TmFst <$> step t

step (TmSnd (TmPair v1 v2))
  | isValue v1 && isValue v2 = Just v2
step (TmSnd t) = TmSnd <$> step t
```

### Step 7: Update Parser and Pretty Printer

In `src/Parser.hs`:

```haskell
-- Add to termAtom
pairP = do
  _ <- symbol "⟨" <|> symbol "<"
  t1 <- termP
  _ <- symbol ","
  t2 <- termP
  _ <- symbol "⟩" <|> symbol ">"
  return (TmPair t1 t2)

fstP = do
  _ <- symbol "fst"
  t <- termAtom
  return (TmFst t)

sndP = do
  _ <- symbol "snd"
  t <- termAtom
  return (TmSnd t)
```

In `src/Pretty.hs`:

```haskell
pretty (TmPair t1 t2) = "⟨" ++ pretty t1 ++ ", " ++ pretty t2 ++ "⟩"
pretty (TmFst t) = "fst " ++ prettyAtom t
pretty (TmSnd t) = "snd " ++ prettyAtom t
```

### Step 8: Add Tests

In `test/Spec.hs`:

```haskell
describe "Product Types" $ do
  it "types pair construction" $ do
    let pair = TmPair (natFromInt 3) TmTrue
    typeOf emptyCtx pair `shouldBe` Right (TyProd TyNat TyBool)

  it "projects first component" $ do
    let pair = TmPair (natFromInt 3) TmTrue
    eval (TmFst pair) `shouldBe` natFromInt 3

  it "projects second component" $ do
    let pair = TmPair (natFromInt 3) TmTrue
    eval (TmSnd pair) `shouldBe` TmTrue

  it "evaluates components before creating pair" $ do
    let pair = TmPair (TmSucc TmZero) (TmPred (natFromInt 1))
    eval pair `shouldBe` TmPair (natFromInt 1) TmZero
```

### Example Usage

```haskell
-- Create a pair
myPair :: Term
myPair = TmPair (natFromInt 42) TmTrue

-- Type: Nat × Bool

-- Extract components
getFirst :: Term
getFirst = TmFst myPair  -- Evaluates to 42

getSecond :: Term
getSecond = TmSnd myPair  -- Evaluates to true

-- Swap function: (τ₁ × τ₂) → (τ₂ × τ₁)
swap :: Term
swap = Lam "p" (TyProd TyNat TyBool) $
       TmPair (TmSnd (Var "p")) (TmFst (Var "p"))
```

---

## Exercise 3: Sum Types

Sum types (disjoint unions) represent a choice between alternatives.

### Step 1: Extend Type

```haskell
data Type
  = ... (existing constructors)
  | TySum Type Type    -- NEW: Sum type τ₁ + τ₂
  deriving (Eq, Show, Ord)
```

### Step 2: Extend Term

```haskell
data Term
  = ... (existing constructors)
  | TmInl Type Term         -- NEW: Left injection inl[τ₂] t
  | TmInr Type Term         -- NEW: Right injection inr[τ₁] t
  | TmCase Term Var Term Var Term  -- NEW: case analysis
  deriving (Eq, Show)
```

**Why the type annotations?**
- `inl[τ₂] t` injects `t : τ₁` to get `τ₁ + τ₂`
- We need to know `τ₂` to determine the full type
- Similarly for `inr[τ₁]`

### Step 3: Update Helpers

```haskell
-- Free variables
freeVars (TmInl _ t) = freeVars t
freeVars (TmInr _ t) = freeVars t
freeVars (TmCase t x t1 y t2) =
  freeVars t `Set.union`
  (Set.delete x (freeVars t1)) `Set.union`
  (Set.delete y (freeVars t2))

-- Substitution
substVar x s (TmInl ty t) = TmInl ty (substVar x s t)
substVar x s (TmInr ty t) = TmInr ty (substVar x s t)
substVar x s (TmCase t y t1 z t2)
  | x == y && x == z = TmCase (substVar x s t) y t1 z t2
  | x == y = TmCase (substVar x s t) y t1 z (substVar x s t2)
  | x == z = TmCase (substVar x s t) y (substVar x s t1) z t2
  | otherwise =
      TmCase (substVar x s t)
             y (substVar x s t1)
             z (substVar x s t2)
```

### Step 4: Typing Rules

```haskell
-- Left injection: Γ ⊢ t : τ₁  ⟹  Γ ⊢ inl[τ₂] t : τ₁ + τ₂
typeOf ctx (TmInl ty2 t) = do
  ty1 <- typeOf ctx t
  return (TySum ty1 ty2)

-- Right injection: Γ ⊢ t : τ₂  ⟹  Γ ⊢ inr[τ₁] t : τ₁ + τ₂
typeOf ctx (TmInr ty1 t) = do
  ty2 <- typeOf ctx t
  return (TySum ty1 ty2)

-- Case analysis
typeOf ctx (TmCase t x t1 y t2) = do
  tty <- typeOf ctx t
  case tty of
    TySum ty1 ty2 -> do
      -- Check left branch with x : ty1
      resTy1 <- typeOf (Map.insert x ty1 ctx) t1
      -- Check right branch with y : ty2
      resTy2 <- typeOf (Map.insert y ty2 ctx) t2
      -- Both branches must have same type
      if resTy1 == resTy2
        then return resTy1
        else Left "case branches have different types"
    _ -> Left "case requires sum type"
```

### Step 5: Evaluation

```haskell
-- Values
isValue (TmInl _ v) = isValue v
isValue (TmInr _ v) = isValue v
isValue (TmCase _ _ _ _ _) = False

-- Evaluation steps
step (TmInl ty t) = TmInl ty <$> step t
step (TmInr ty t) = TmInr ty <$> step t

-- Case reduction
step (TmCase (TmInl _ v) x t1 y t2)
  | isValue v = Just (substVar x v t1)
step (TmCase (TmInr _ v) x t1 y t2)
  | isValue v = Just (substVar y v t2)
step (TmCase t x t1 y t2) = do
  t' <- step t
  return (TmCase t' x t1 y t2)
```

### Example Usage

```haskell
-- Option type: Option τ = Unit + τ
type Option a = TySum TyUnit a

none :: Type -> Term
none ty = TmInl ty TmUnit

some :: Term -> Term
some t = TmInr TyUnit t

-- Maybe division
safeDiv :: Term -> Term -> Term
safeDiv m n =
  TmIf (TmIsZero n)
       (none TyNat)  -- Division by zero returns none
       (some (div m n))  -- Otherwise returns some (result)

-- Using case to extract option value
getOrElse :: Term -> Term -> Term
getOrElse opt default_ =
  TmCase opt
         "_" default_       -- none case: return default
         "x" (Var "x")      -- some case: return x
```

---

## Exercise 5: Fixed Point Combinator

The fix operator enables general recursion in a typed setting.

### Step 1: Extend Term

```haskell
data Term
  = ... (existing constructors)
  | TmFix Term    -- NEW: fix t
  deriving (Eq, Show)
```

**Note:** We don't add a new type - fix uses existing function types.

### Step 2: Update Helpers

```haskell
-- Free variables
freeVars (TmFix t) = freeVars t

-- Substitution
substVar x s (TmFix t) = TmFix (substVar x s t)
```

### Step 3: Typing Rule

```haskell
-- fix : (τ → τ) → τ
typeOf ctx (TmFix t) = do
  ty <- typeOf ctx t
  case ty of
    TyArr ty1 ty2 | ty1 == ty2 -> return ty1
    _ -> Left "fix requires function of type τ → τ"
```

**Key insight:** The function must map a type to itself!

### Step 4: Evaluation

```haskell
-- Values
isValue (TmFix _) = False

-- Evaluation: fix v → v (fix v)
step (TmFix v) | isValue v = Just (App v (TmFix v))
step (TmFix t) = TmFix <$> step t
```

**Important:** This creates infinite expansion!
- `fix f → f (fix f) → f (f (fix f)) → ...`
- Termination depends on `f` being lazy or having a base case

### Step 5: Example - Factorial

```haskell
-- factorial = fix (λf:Nat→Nat. λn:Nat.
--                   if iszero n then 1
--                   else mult n (f (pred n)))

factorialBody :: Term
factorialBody =
  Lam "f" (TyArr TyNat TyNat) $
  Lam "n" TyNat $
  TmIf (TmIsZero (Var "n"))
       (natFromInt 1)
       (multNat (Var "n")
                (App (Var "f") (TmPred (Var "n"))))

factorial :: Term
factorial = TmFix factorialBody

-- Usage:
-- eval (App factorial (natFromInt 5))  -- Should give 120
```

### Step 6: Example - Fibonacci

```haskell
-- fib = fix (λf:Nat→Nat. λn:Nat.
--             if iszero n then 0
--             else if iszero (pred n) then 1
--             else add (f (pred n)) (f (pred (pred n))))

fibonacciBody :: Term
fibonacciBody =
  Lam "f" (TyArr TyNat TyNat) $
  Lam "n" TyNat $
  TmIf (TmIsZero (Var "n"))
       TmZero
       (TmIf (TmIsZero (TmPred (Var "n")))
             (natFromInt 1)
             (addNat (App (Var "f") (TmPred (Var "n")))
                     (App (Var "f") (TmPred (TmPred (Var "n"))))))

fibonacci :: Term
fibonacci = TmFix fibonacciBody
```

### Why We Need fix in STLC

**Question:** Why can't we use the Y combinator?

**Answer:** The Y combinator involves self-application:
```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

The term `(x x)` requires `x` to have type `α → β` AND type `α` simultaneously, which is impossible in STLC!

In untyped lambda calculus, this works because there are no types. In STLC, we need `fix` as a primitive.

**Alternative in System F:** In System F (Chapter 5), we can encode fix using polymorphism, but it's still easier to have it as a primitive.

---

## Testing Your Extensions

### Unit Tests

Add these to `test/Spec.hs`:

```haskell
describe "Extended STLC" $ do
  describe "Product Types" $ do
    it "creates and projects pairs" $ do
      let pair = TmPair (natFromInt 3) TmTrue
      eval (TmFst pair) `shouldBe` natFromInt 3
      eval (TmSnd pair) `shouldBe` TmTrue

  describe "Sum Types" $ do
    it "handles left injection" $ do
      let left = TmInl TyBool (natFromInt 5)
      let result = TmCase left "x" (Var "x") "y" TmZero
      eval result `shouldBe` natFromInt 5

    it "handles right injection" $ do
      let right = TmInr TyNat TmTrue
      let result = TmCase right "x" TmZero "y" (natFromInt 1)
      eval result `shouldBe` natFromInt 1

  describe "Fixed Point" $ do
    it "computes factorial" $ do
      eval (App factorial (natFromInt 5)) `shouldBe` natFromInt 120

    it "computes fibonacci" $ do
      eval (App fibonacci (natFromInt 7)) `shouldBe` natFromInt 13
```

### Interactive Testing

```haskell
-- In GHCi:
> let pair = TmPair (natFromInt 3) TmTrue
> typeOf emptyCtx pair
Right (TyProd TyNat TyBool)

> eval (TmFst pair)
TmSucc (TmSucc (TmSucc TmZero))

> eval (App factorial (natFromInt 5))
TmSucc (TmSucc ... TmZero)  -- 120

> termToInt it
Just 120
```

---

## Common Issues and Solutions

### Issue 1: Type Inference for Injections

**Problem:** How do we know the full type of `inl (natFromInt 3)`?

**Solution:** Require type annotations:
```haskell
inl[Bool] 3  -- Type is Nat + Bool
```

### Issue 2: Case Expression Type Checking

**Problem:** Branches have different types.

**Solution:** Both branches must return the same type. Check this in `typeOf`.

### Issue 3: fix Doesn't Terminate

**Problem:** `fix f` creates infinite expansion.

**Solution:** This is expected! The function `f` must have a base case that stops recursion.

### Issue 4: Substitution in Case

**Problem:** Variable capture in case branches.

**Solution:** Check if substituted variable is bound by case:
```haskell
substVar x s (TmCase t y t1 z t2)
  | x == y || x == z = ... -- x is shadowed
  | otherwise = ...        -- x is free, substitute
```

---

## Further Exercises

Once you've implemented these extensions, try:

1. **Implement Either type** using sum types
2. **Implement List type** using sum and product types
3. **Write more recursive functions** using fix
4. **Prove type safety** still holds with extensions
5. **Add record types** (named products)
6. **Add variant types** (named sums)

---

## References

- Pierce, TAPL, Chapter 11: Simple Extensions
- Harper, PFPL, Chapter 10: Product and Sum Types
- Harper, PFPL, Chapter 19: Fixed Points

---

**Next:** Once you've mastered these extensions, move on to Chapter 3 where these features are built into the language from the start!
