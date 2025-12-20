# Chapter 1: Untyped Lambda Calculus - Frequently Asked Questions

## Table of Contents

1. [Conceptual Questions](#conceptual-questions)
2. [Syntax and Notation](#syntax-and-notation)
3. [Reduction and Evaluation](#reduction-and-evaluation)
4. [Church Encodings](#church-encodings)
5. [Recursion and Fixed Points](#recursion-and-fixed-points)
6. [Practical "I'm Stuck" Scenarios](#practical-im-stuck-scenarios)

---

## Conceptual Questions

### Q1: Why study untyped lambda calculus?

**A**: Lambda calculus is the foundation of:
- **All functional programming**: Haskell, OCaml, Lisp, JavaScript arrows
- **Type theory**: Every type system builds on these concepts
- **Computability**: Lambda calculus = Turing machines in expressive power

Understanding lambda calculus deeply makes everything else clearer.

### Q2: Is lambda calculus actually useful, or just theoretical?

**A**: Both! Every time you write:
```javascript
const add = x => y => x + y;   // JavaScript
```
You're writing lambda calculus! The `=>` is just `λ`.

Lambda calculus also underlies:
- Closures in all languages
- Higher-order functions (map, filter, reduce)
- Callbacks and continuations

### Q3: What's the difference between lambda calculus and regular functions?

**A**: Lambda calculus is **pure**:
- No side effects
- No mutation
- No built-in numbers, booleans, etc.
- ONLY: variables, abstraction (λ), and application

Everything else (numbers, conditionals, loops) must be encoded!

### Q4: What does "Turing complete" mean for lambda calculus?

**A**: Any computation that a computer can do, lambda calculus can do too:
- Arithmetic
- Conditionals
- Loops (via recursion)
- Data structures

The catch: It's not always convenient! That's why we add types and features in later chapters.

---

## Syntax and Notation

### Q5: What's the difference between `λx.` and `\x.`?

**A**: They're the same! `\` is just ASCII for `λ`.
```
λx. x   =   \x. x   (both mean "identity function")
```
The parser accepts both.

### Q6: How do I read `λx. λy. x`?

**A**: Right to left for the body:
```
λx. (λy. x)
```
This is a function that:
1. Takes `x`
2. Returns a function that takes `y` and returns `x`

In other words: "take two arguments, return the first" (the K combinator).

### Q7: How does application associate?

**A**: **Left to right**:
```
f x y z  =  ((f x) y) z
```
This is called "currying" - multi-argument functions are chains of single-argument functions.

### Q8: What are "free" vs "bound" variables?

**A**:
- **Bound**: Has a corresponding λ above it
- **Free**: Not bound by any λ

```
λx. x y
    ↑ ↑
    │ └── y is FREE (no λy above)
    └──── x is BOUND (by λx)
```

Free variables are "undefined" - they refer to the outside world.

### Q9: What is α-equivalence (alpha equivalence)?

**A**: Two terms are α-equivalent if they differ only in bound variable names:
```
λx. x  ≡α  λy. y  ≡α  λz. z
```
All are the identity function - the name doesn't matter!

**But not**:
```
λx. y  ≢α  λx. z   (y and z are FREE, so renaming changes meaning)
```

---

## Reduction and Evaluation

### Q10: What's the difference between β-reduction and evaluation?

**A**:
- **β-reduction**: One step of substitution: `(λx. t) s → t[x := s]`
- **Evaluation**: Keep reducing until you can't anymore (reach normal form)

### Q11: What are the different evaluation strategies?

**A**: Three main strategies:

| Strategy | Reduce... | Example: `(λx. x x)(λy. y)` |
|----------|-----------|------------------------------|
| **Normal Order** | Leftmost-outermost redex first | Always finds normal form if one exists |
| **Call-by-Name** | Like normal, but don't reduce under λ | Lazy evaluation (Haskell) |
| **Call-by-Value** | Arguments first, then apply | Eager evaluation (most languages) |

### Q12: What's "normal form"?

**A**: A term with no redexes (nothing left to reduce):
```
λx. x               ✓ Normal form
λx. λy. x           ✓ Normal form
(λx. x) y           ✗ Not normal (can reduce to y)
```

### Q13: Do all terms have a normal form?

**A**: **NO!** The classic example:
```
Ω = (λx. x x)(λx. x x)
  → (λx. x x)(λx. x x)
  → (λx. x x)(λx. x x)
  → ...forever!
```

This is why we need types (Chapter 2) - to guarantee termination.

### Q14: What's the Church-Rosser theorem?

**A**: If a term can reduce to two different terms, those terms can both reduce to a common term:
```
        t
       / \
      /   \
     t1   t2
      \   /
       \ /
        t'
```

**Consequence**: Normal forms are unique! If a term has a normal form, it's the same no matter which reduction order you use.

---

## Church Encodings

### Q15: What are Church encodings?

**A**: Ways to represent data using only lambdas:
- **Church Booleans**: `true = λt. λf. t`, `false = λt. λf. f`
- **Church Numerals**: `0 = λf. λx. x`, `1 = λf. λx. f x`, etc.
- **Church Pairs**: `pair = λa. λb. λf. f a b`

Everything is a function!

### Q16: Why does `true = λt. λf. t` make sense?

**A**: Think of it as a "chooser":
```
true  = λt. λf. t   -- "choose the first"
false = λt. λf. f   -- "choose the second"
```

So `if-then-else` is just:
```
if cond then a else b  =  cond a b
```
If `cond = true`, we get `a`. If `cond = false`, we get `b`.

### Q17: How do Church numerals work?

**A**: A numeral n represents "apply f n times":
```
0 = λf. λx. x           (apply f zero times)
1 = λf. λx. f x         (apply f once)
2 = λf. λx. f (f x)     (apply f twice)
3 = λf. λx. f (f (f x)) (apply f thrice)
```

**Addition**: n + m = "apply f n times, then m more times"
```
add = λm. λn. λf. λx. m f (n f x)
```

### Q18: Why is predecessor (pred) so hard?

**A**: Church numerals are "one-way" - they apply f repeatedly but don't track the count!

The trick is to use pairs:
```
pred n = first (n step (pair 0 0))
where step = λp. pair (second p) (succ (second p))
```

Start with `(0, 0)`, and each step makes `(a, b) → (b, b+1)`.
After n steps: `(n-1, n)`. Take the first element!

---

## Recursion and Fixed Points

### Q19: How can we have recursion without naming functions?

**A**: Use a **fixed-point combinator** (Y combinator):
```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

Property: `Y F = F (Y F)` for any F.

### Q20: What does "fixed point" mean?

**A**: A value x where `f(x) = x`. For the Y combinator:
```
Y F = F (Y F)
```
So `Y F` is a fixed point of F!

### Q21: Why does the Y combinator work?

**A**: Let's trace it:
```
Y F = (λf. (λx. f (x x)) (λx. f (x x))) F
    → (λx. F (x x)) (λx. F (x x))
    → F ((λx. F (x x)) (λx. F (x x)))
    = F (Y F)
```

The self-application `x x` creates the "loop"!

### Q22: Why can't I type `λx. x x`?

**A**: In the **typed** lambda calculus, `x x` would require:
```
x : A → B    (x is a function)
x : A        (x is also the argument)
```
So `A = A → B`, which is infinite!

This is why typed calculus prevents infinite loops - but also prevents the Y combinator. We'll add `fix` as a primitive in Chapter 2.

---

## Practical "I'm Stuck" Scenarios

### Q23: "My reduction never terminates!"

**A**: Common causes:
1. **Omega term**: Check for `(λx. x x)(λx. x x)` patterns
2. **Wrong Y combinator application**: Make sure F is a "step function"
3. **Infinite Church numeral arithmetic**: Some operations don't terminate on all inputs

**Debug**: Try reducing by hand for a few steps. Do you see a pattern?

### Q24: "I'm getting the wrong result for Church arithmetic"

**A**: Common issues:
1. **Argument order**: `sub m n` = m - n, not n - m
2. **Off-by-one errors**: Remember `pred 0 = 0` in Church encoding
3. **Forgetting to apply to base case**: Church numerals need `f` and `x`

**Debug**: Test with small numbers first (0, 1, 2).

### Q25: "Variable capture is confusing me"

**A**: Use this checklist before any substitution `[x := s]t`:
1. Find free variables in `s`: `FV(s)`
2. Find bound variables in `t` (the λ's)
3. If any overlap: α-rename first!

Example:
```
[y := x](λx. y)
FV(x) = {x}, bound vars = {x}
Overlap! Rename: λx. y → λz. y
Now substitute: λz. x ✓
```

### Q26: "The SKI combinators are confusing"

**A**: Think of them as:
- **I = λx. x**: Identity - return the argument
- **K = λx. λy. x**: Konstant - return first, ignore second
- **S = λx. λy. λz. x z (y z)**: Substitution - apply x and y to z, combine

**Key insight**: S, K, I can encode ANY lambda term! They're a minimal basis.

### Q27: "How do I test if my Church encoding is correct?"

**A**: Convert back to Haskell and check:
```haskell
-- Convert Church numeral to Int
churchToInt n = n (+1) 0

-- Test
churchToInt (add two three)  -- Should be 5
```

The REPL has helpers for this!

---

## Quick Reference: Key Terms

| Term | Meaning |
|------|---------|
| **Redex** | Reducible expression: `(λx. t) s` |
| **Normal form** | No redexes left |
| **α-equivalence** | Same up to bound variable renaming |
| **β-reduction** | `(λx. t) s → t[x := s]` |
| **η-equivalence** | `λx. f x = f` (if x not free in f) |
| **Combinator** | Closed term (no free variables) |

---

## Further Reading

- **Church (1936)**: "An Unsolvable Problem of Elementary Number Theory" - introduces lambda calculus
- **Barendregt (1984)**: "The Lambda Calculus: Its Syntax and Semantics" - the definitive reference
- **Pierce TAPL Chapter 5**: Excellent modern introduction

**Remember**: Lambda calculus is simple but deep. Master substitution and reduction, and everything else follows!
