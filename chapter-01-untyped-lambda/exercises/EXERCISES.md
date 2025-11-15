# Chapter 1 Exercises: Untyped Lambda Calculus

## Exercise 1: Church Boolean Operations (Easy)

Implement the following Church boolean operations:

### 1a. AND operation
Implement `and` such that:
- `and true true → true`
- `and true false → false`
- `and false true → false`
- `and false false → false`

**Hint**: Use the Church encoding where `true = λt. λf. t` and `false = λt. λf. f`.

### 1b. OR operation
Implement `or` such that:
- `or true true → true`
- `or true false → true`
- `or false true → true`
- `or false false → false`

### 1c. XOR operation
Implement `xor` (exclusive or) such that:
- `xor true true → false`
- `xor true false → true`
- `xor false true → true`
- `xor false false → false`

## Exercise 2: Church Numeral Arithmetic (Medium)

Implement the following operations on Church numerals:

### 2a. Predecessor
Implement `pred` such that `pred (succ n) = n` and `pred 0 = 0`.

**Hint**: This is one of the most challenging Church numeral operations! You'll need to use pairs to "shift" values.

### 2b. Subtraction
Implement `sub` such that `sub m n = m - n` (with `sub n m = 0` when `n < m`).

**Hint**: Use `pred` repeatedly.

### 2c. Equality test
Implement `isEqual` that tests if two Church numerals are equal.

**Hint**: You can use subtraction in both directions and check if both results are zero.

## Exercise 3: Recursion and Fixed Points (Hard)

### 3a. Y Combinator
Implement the Y combinator (fixed-point combinator):
```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

**Note**: In call-by-value evaluation, you'll need the Z combinator instead:
```
Z = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
```

### 3b. Factorial using Y
Using your fixed-point combinator, implement factorial.

**Hint**:
```
factorial = Y (λf. λn. if (isZero n) then 1 else (mult n (f (pred n))))
```

You'll need to implement this using Church encodings.

### 3c. Fibonacci
Implement the Fibonacci function using the Y combinator.

## Exercise 4: Advanced Combinators (Hard)

### 4a. Implement the S, K, I combinators
- **I** (identity): `I x = x`
- **K** (constant): `K x y = x`
- **S** (substitution): `S x y z = x z (y z)`

### 4b. Implement omega (Ω)
Create the non-terminating term `Ω = ω ω` where `ω = λx. x x`.

Show that it diverges under normal-order evaluation.

### 4c. Derive I from S and K
Show that `I = S K K` by demonstrating that `S K K x` reduces to `x`.

## Exercise 5: List Operations (Medium-Hard)

Using the Church encoding for lists where:
```
nil = λc. λn. n
cons h t = λc. λn. c h (t c n)
```

Implement:

### 5a. Length
Implement `length` that returns the length of a list as a Church numeral.

### 5b. Map
Implement `map` that applies a function to each element of a list.

### 5c. Filter
Implement `filter` that keeps only elements satisfying a predicate.

### 5d. Fold (Reduce)
Implement `fold` (also called reduce or fold-right) for lists.

**Hint**: For Church-encoded lists, `fold` is particularly simple!

## Solutions

Solutions are provided in `Solutions.hs` with full implementations and explanations. Tests are in `test/ExerciseSpec.hs`.

## Testing Your Solutions

Run the exercise tests with:
```bash
stack test --test-arguments "--match Exercises"
```

## Learning Objectives

After completing these exercises, you should understand:
- How to encode data structures using only functions
- The power and limitations of Church encodings
- Fixed-point combinators and recursion in lambda calculus
- The differences between normal-order and call-by-value evaluation
- The computational completeness of lambda calculus

## Additional Challenges

1. **Ackermann function**: Implement the Ackermann function, which is not primitive recursive.
2. **Binary numbers**: Design an encoding for binary numbers and implement arithmetic.
3. **Church vs Scott encoding**: Implement lists using Scott encoding and compare with Church encoding.
4. **Lazy evaluation**: Modify the evaluator to support lazy evaluation and show how it affects your solutions.
