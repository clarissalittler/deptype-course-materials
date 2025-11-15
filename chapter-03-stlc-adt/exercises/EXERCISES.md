# Chapter 3 Exercises: STLC with Algebraic Data Types

## Exercise 1: List Operations (Easy)

Implement the following operations using the existing list type and pattern matching:

### 1a. Append
```
append : List τ → List τ → List τ
append [] ys = ys
append (x :: xs) ys = x :: append xs ys
```

### 1b. Reverse
```
reverse : List τ → List τ
```

### 1c. Length
```
length : List τ → Nat
```

## Exercise 2: Binary Trees (Medium)

Define and implement operations on binary trees:

### 2a. Tree Definition
Define a variant type for binary trees:
```
Tree τ = <leaf: Unit, node: τ × Tree τ × Tree τ>
```

### 2b. Tree Operations
- `height : Tree τ → Nat`
- `mirror : Tree τ → Tree τ` (flip left and right subtrees)
- `map : (τ₁ → τ₂) → Tree τ₁ → Tree τ₂`
- `fold : (τ → β → β → β) → β → Tree τ → β`

## Exercise 3: Option Type (Medium)

Using the sum type encoding:

### 3a. Option Operations
```
Option τ = Unit + τ

none : Option τ = inl unit
some : τ → Option τ = λx. inr x

map : (τ₁ → τ₂) → Option τ₁ → Option τ₂
bind : Option τ₁ → (τ₁ → Option τ₂) → Option τ₂
getOrElse : Option τ → τ → τ
```

## Exercise 4: Expression Evaluator (Hard)

Build an interpreter for a simple expression language:

### 4a. Expression Type
```
Expr = <lit: Nat,
        add: Expr × Expr,
        mul: Expr × Expr,
        let: {var: Nat, value: Expr, body: Expr}>
```

Note: Use naturals as de Bruijn indices for variables.

### 4b. Evaluator
```
eval : Expr → Nat
```

### 4c. Optimizer
Implement constant folding:
```
optimize : Expr → Expr
```

Examples:
- `add (lit 2) (lit 3)` → `lit 5`
- `mul (lit 0) e` → `lit 0`

## Exercise 5: Record Operations (Medium)

### 5a. Record Update
Implement a function to update a field in a record:
```
updateX : {x: τ₁, y: τ₂} → τ₁ → {x: τ₁, y: τ₂}
```

### 5b. Record Merge
Merge two records (assuming disjoint fields).

## Exercise 6: Pattern Matching Exhaustiveness (Hard)

### 6a. Exhaustiveness Checker
Implement a function that checks if all constructors of a variant are covered in a case expression.

### 6b. Unreachable Pattern Detection
Detect patterns that can never match due to previous patterns.

### 6c. Redundant Pattern Warning
Identify patterns that are subsumed by earlier patterns.

## Solutions

See `Solutions.hs` for reference implementations.

## Testing

```bash
stack test --test-arguments "--match 'Chapter 3'"
```

## Learning Objectives

- Master pattern matching
- Design with algebraic data types
- Understand recursive data structures
- Practice type-driven development
- Learn exhaustiveness checking
