# Chapter 4 Exercises: Hindley-Milner Type Inference

## Exercise 1: Type Inference Practice (Easy)

Manually infer the principal types of the following terms, then verify with the type checker:

### 1a. Composition
```
λf. λg. λx. f (g x)
```

### 1b. S Combinator
```
λx. λy. λz. x z (y z)
```

### 1c. Twice
```
λf. λx. f (f x)
```

### 1d. Flip
```
λf. λx. λy. f y x
```

## Exercise 2: Polymorphic List Operations (Medium)

Implement the following with full type inference (no type annotations):

### 2a. Basic Operations
```haskell
map = λf. λlist. ...
filter = λpred. λlist. ...
length = λlist. ...
```

### 2b. Higher-Order Operations
```haskell
foldl = λf. λz. λlist. ...
foldr = λf. λz. λlist. ...
zipWith = λf. λxs. λys. ...
```

### 2c. Verify Inferred Types
- `map : (α → β) → List α → List β`
- `filter : (α → Bool) → List α → List α`
- `foldl : (β → α → β) → β → List α → β`

## Exercise 3: Let-Polymorphism vs Lambda (Medium)

### 3a. Demonstrate Polymorphic Let
Show that this type checks:
```
let id = λx. x in
  pair (id 0) (id true)
```

### 3b. Demonstrate Monomorphic Lambda
Show that this does NOT type check:
```
(λid. pair (id 0) (id true)) (λx. x)
```

### 3c. Explain
Write a brief explanation of why let-polymorphism allows the first but not the second.

## Exercise 4: Mutual Recursion (Hard)

### 4a. Extend Syntax
Add support for mutually recursive definitions:
```
let rec even = λn. if (iszero n) then true else odd (pred n)
    and odd = λn. if (iszero n) then false else even (pred n)
in even 4
```

### 4b. Implement Inference
Extend the type inference algorithm to handle mutual recursion.

**Hint**: Generalize all mutually recursive functions together, not separately.

## Exercise 5: Polymorphic Trees (Medium)

Define and implement operations on polymorphic trees:

### 5a. Tree Type
```
data Tree a = Leaf | Node a (Tree a) (Tree a)
```

### 5b. Operations
Implement without type annotations:
```
treeMap = λf. λtree. ...
treeFold = λleaf. λnode. λtree. ...
height = λtree. ...
```

Verify inferred types:
- `treeMap : (α → β) → Tree α → Tree β`
- `treeFold : β → (α → β → β → β) → Tree α → β`

## Exercise 6: Type Error Improvements (Hard)

### 6a. Better Unification Errors
Improve error messages to show:
- Expected type
- Actual type
- Location of mismatch

### 6b. Type Hole Support
Add support for type holes (`_`) that print the inferred type:
```
let id = λx. _ in id 5
-- Should print: "Type of hole: Nat"
```

### 6c. Did You Mean?
Suggest corrections for typos in variable names.

## Exercise 7: Constraint-Based Inference (Hard)

### 7a. Constraint Generation
Rewrite inference to use constraint generation + solving:
1. Generate type constraints
2. Solve constraints via unification

### 7b. Better Error Messages
Show that constraint-based approaches can provide better error locations.

## Solutions

See `Solutions.hs` for reference implementations.

## Testing

```bash
stack test --test-arguments "--match 'Chapter 4'"
```

## Learning Objectives

- Understand Algorithm W deeply
- Master let-polymorphism
- Learn about unification and substitution
- Practice with principal types
- Explore advanced type system features

## References

- Milner (1978): "A Theory of Type Polymorphism in Programming"
- Damas & Milner (1982): "Principal Type-Schemes for Functional Programs"
- Pierce TAPL Chapter 22: "Type Reconstruction"
