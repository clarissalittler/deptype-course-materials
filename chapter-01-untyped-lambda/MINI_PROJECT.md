# Chapter 1 Mini-Project: Lambda Term Visualizer

## Overview

Build a **lambda term visualizer** that takes a lambda expression and produces an ASCII art representation of its abstract syntax tree.

**Time estimate**: 2-4 hours

---

## Learning Objectives

- Reinforce understanding of lambda calculus syntax
- Practice parsing and tree traversal
- Understand how lambda terms are structured

---

## The Project

### Input
A lambda term as a string:
```
(\x. \y. x y) z
```

### Output
An ASCII tree representation:
```
      App
     /   \
   Lam    z
   / \
  x  Lam
     / \
    y  App
       / \
      x   y
```

---

## Specification

### Step 1: Parse to AST

Use the existing `Parser.hs` or write your own simple parser.

```haskell
data Term = Var String
          | Lam String Term
          | App Term Term
```

### Step 2: Generate Tree

Write a function:
```haskell
visualize :: Term -> String
```

That produces an ASCII tree.

### Step 3: Add Features

1. **Show reductions**: Display step-by-step β-reduction
2. **Highlight free variables**: Mark them differently
3. **Color output** (optional): Use ANSI colors for different node types

---

## Starter Code

```haskell
module Visualizer where

import Syntax (Term(..))

-- Calculate width needed for a subtree
width :: Term -> Int
width (Var x) = length x
width (Lam x t) = max (length x + 1) (width t) + 2
width (App t1 t2) = width t1 + width t2 + 3

-- Generate the visualization
visualize :: Term -> String
visualize term = undefined  -- Your implementation here!

-- Helper: create a box around text
box :: String -> [String]
box s = [s]

-- Helper: connect two subtrees
connect :: [String] -> [String] -> [String]
connect left right = undefined  -- Your implementation here!
```

---

## Example Output

### Input: `\x. x`

```
Lam
├─ x
└─ Var
   └─ x
```

### Input: `(\x. x) y`

```
    App
   /   \
 Lam   Var
 │ │    │
 x │    y
   │
  Var
   │
   x
```

### Input: `\f. \x. f (f x)`

```
         Lam
        /   \
       f    Lam
           /   \
          x    App
              /   \
           Var    App
            │    /   \
            f  Var   Var
                │     │
                f     x
```

---

## Extension Ideas

### 1. Interactive Mode
Let users type terms and see them visualized in real-time.

### 2. Reduction Animation
Show β-reduction step by step with visual diffs.

### 3. De Bruijn Indices
Add option to show terms with de Bruijn indices.

### 4. Export Formats
Generate SVG, DOT (Graphviz), or HTML output.

---

## Testing Your Implementation

```haskell
-- Test cases
test1 = Var "x"
test2 = Lam "x" (Var "x")
test3 = App (Lam "x" (Var "x")) (Var "y")
test4 = Lam "f" (Lam "x" (App (Var "f") (App (Var "f") (Var "x"))))

main = do
  putStrLn $ visualize test1
  putStrLn $ visualize test2
  putStrLn $ visualize test3
  putStrLn $ visualize test4
```

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Basic visualization works | 40 |
| Handles nested lambdas | 20 |
| Handles complex applications | 20 |
| Code is clean and documented | 10 |
| Extension implemented | 10 |

---

## Resources

- `src/Syntax.hs` - Term data type
- `src/Parser.hs` - Existing parser
- `src/Pretty.hs` - Pretty printing (for ideas)
