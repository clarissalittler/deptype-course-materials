# Chapter 4 Mini-Project: Type Inference Visualizer

## Overview

Build a **type inference visualizer** that shows the step-by-step process of Algorithm W, including unification and substitution.

**Time estimate**: 4-5 hours

---

## Learning Objectives

- Deeply understand Algorithm W
- See unification in action
- Trace substitution threading

---

## The Project

### Input
A lambda term without type annotations.

### Output
Step-by-step visualization of type inference.

---

## Example

### Input
```
\f. \x. f x
```

### Output
```
INFERRING TYPE OF: λf. λx. f x

Step 1: Create fresh type variable for f
  f : α₀
  Environment: {f : α₀}

Step 2: Create fresh type variable for x
  x : α₁
  Environment: {f : α₀, x : α₁}

Step 3: Infer type of (f x)
  f has type α₀
  x has type α₁
  Application requires: α₀ = α₁ → α₂

Step 4: Unify α₀ with α₁ → α₂
  Substitution: [α₀ ↦ α₁ → α₂]

Step 5: Build function type
  Inner lambda: α₁ → α₂
  Outer lambda: (α₁ → α₂) → α₁ → α₂

Step 6: Generalize
  Free variables: {α₁, α₂}
  Final type: ∀α₁ α₂. (α₁ → α₂) → α₁ → α₂

RESULT: ∀α β. (α → β) → α → β
        (renamed for readability)
```

---

## Specification

### Step 1: Instrumented Inference

```haskell
data InferStep
  = FreshVar String Type
  | EnvExtend String TypeScheme
  | InferApp Type Type Type  -- fun arg result
  | Unify Type Type Subst
  | Generalize Type TypeScheme
  | Instantiate TypeScheme Type

type InferTrace = [InferStep]

inferWithTrace :: Env -> Term -> (Either Error Type, InferTrace)
```

### Step 2: Pretty Printing

```haskell
ppStep :: InferStep -> String
ppTrace :: InferTrace -> String
```

### Step 3: Interactive Mode

Show inference interactively, pausing at each step.

---

## Starter Code

```haskell
module InferenceVisualizer where

import Syntax
import qualified Data.Map as Map

-- Types
type TyVar = String
data Type = TVar TyVar | TArr Type Type deriving (Show, Eq)
data TypeScheme = Forall [TyVar] Type deriving (Show)
type Subst = Map.Map TyVar Type
type Env = Map.Map String TypeScheme

-- Inference steps
data InferStep
  = Step_FreshVar TyVar
  | Step_Lookup String TypeScheme
  | Step_Instantiate TypeScheme Type
  | Step_EnterLambda String TyVar
  | Step_ExitLambda String Type Type  -- param, body, result
  | Step_Application Type Type TyVar  -- fun, arg, result var
  | Step_Unify Type Type
  | Step_UnifyResult Subst
  | Step_Generalize Type TypeScheme
  deriving (Show)

-- State monad with logging
type InferM a = StateT InferState (Either String) a

data InferState = InferState
  { counter :: Int
  , trace :: [InferStep]
  , currentSubst :: Subst
  }

-- Log a step
logStep :: InferStep -> InferM ()
logStep step = modify $ \s -> s { trace = trace s ++ [step] }

-- Fresh variable with logging
freshVar :: InferM Type
freshVar = do
  n <- gets counter
  modify $ \s -> s { counter = n + 1 }
  let var = "α" ++ show n
  logStep $ Step_FreshVar var
  return $ TVar var

-- Main inference with trace
inferWithTrace :: Term -> Either String (Type, [InferStep])
inferWithTrace term = do
  let initial = InferState 0 [] Map.empty
  (ty, final) <- runStateT (infer Map.empty term) initial
  return (apply (currentSubst final) ty, trace final)

-- Your implementation of infer goes here
infer :: Env -> Term -> InferM Type
infer env term = undefined
```

---

## Visualization Formats

### Text Format
```
┌─────────────────────────────────────────┐
│ Step 4: UNIFICATION                     │
├─────────────────────────────────────────┤
│ Unifying:                               │
│   α₀  with  α₁ → α₂                    │
│                                         │
│ Process:                                │
│   α₀ is a variable                      │
│   α₀ ∉ FV(α₁ → α₂)  ✓ (occurs check)   │
│   Bind: α₀ ↦ α₁ → α₂                   │
│                                         │
│ Result: [α₀ ↦ α₁ → α₂]                 │
└─────────────────────────────────────────┘
```

### Tree Format
```
infer(λf. λx. f x)
├── fresh α₀ for f
├── infer(λx. f x) in {f:α₀}
│   ├── fresh α₁ for x
│   ├── infer(f x) in {f:α₀, x:α₁}
│   │   ├── lookup f → α₀
│   │   ├── lookup x → α₁
│   │   ├── fresh α₂ for result
│   │   ├── unify(α₀, α₁→α₂) → [α₀↦α₁→α₂]
│   │   └── result: α₂
│   └── result: α₁ → α₂
└── result: (α₁→α₂) → α₁ → α₂
```

---

## Extension Ideas

### 1. Unification Animation
Show unification as a series of small steps.

### 2. Occurs Check Visualization
Highlight when occurs check prevents infinite types.

### 3. Let-Polymorphism Highlight
Show where generalization happens.

### 4. Error Explanation
When inference fails, show exactly where and why.

---

## Test Cases

```haskell
testCases :: [String]
testCases =
  [ "\\x. x"                      -- α → α
  , "\\f. \\x. f x"               -- (α→β) → α → β
  , "\\f. \\x. f (f x)"           -- (α→α) → α → α
  , "\\x. \\y. x"                 -- α → β → α
  , "let id = \\x. x in id id"    -- α → α
  , "\\x. x x"                    -- Fails! (occurs check)
  ]
```

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Basic inference traced | 30 |
| Unification steps shown | 25 |
| Substitution application shown | 20 |
| Clear output format | 15 |
| Extension implemented | 10 |
