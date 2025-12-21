# Chapter 1: Untyped Lambda Calculus

## Overview

The untyped lambda calculus is a foundational model of computation introduced by Alonzo Church in the 1930s. Despite its simplicity—having just three syntactic forms—it is Turing-complete and serves as the theoretical basis for functional programming languages.

This chapter introduces the core concepts of lambda calculus and implements an interpreter with multiple evaluation strategies.

## Syntax

The syntax of untyped lambda calculus consists of three constructs:

```
t ::=                  (terms)
    x                  variable
    λx. t              abstraction (function)
    t t                application
```

### Examples

- **Identity function**: `λx. x`
- **Constant function**: `λx. λy. x` (returns first argument, ignores second)
- **Self-application**: `λx. x x`
- **Application**: `(λx. x) y` (applying identity to `y`)

## Mathematical Foundations

### Free and Bound Variables

A variable `x` is **bound** in term `t` if it appears within the scope of a lambda abstraction `λx`. Otherwise, it is **free**.

**Definition** (Free Variables):

```
FV(x) = {x}
FV(λx. t) = FV(t) \ {x}
FV(t₁ t₂) = FV(t₁) ∪ FV(t₂)
```

### Substitution

Substitution `[x ↦ s]t` replaces all free occurrences of `x` in `t` with `s`. To avoid **variable capture**, bound variables may need to be renamed (α-conversion).

**Definition** (Capture-Avoiding Substitution):

```
[x ↦ s]x = s
[x ↦ s]y = y                           (if x ≠ y)
[x ↦ s](λx. t) = λx. t                 (x is shadowed)
[x ↦ s](λy. t) = λy. [x ↦ s]t          (if y ≠ x and y ∉ FV(s))
[x ↦ s](λy. t) = λz. [x ↦ s][y ↦ z]t   (if y ≠ x and y ∈ FV(s), z fresh)
[x ↦ s](t₁ t₂) = ([x ↦ s]t₁) ([x ↦ s]t₂)
```

### Operational Semantics

The core reduction rule is **β-reduction**:

```
(λx. t) s → [x ↦ s]t
```

This says: applying a function `λx. t` to an argument `s` yields `t` with `x` replaced by `s`.

#### Evaluation Strategies

Different evaluation strategies determine the order in which β-reductions are performed:

**1. Normal Order** (Leftmost-Outermost)
- Always reduces the leftmost-outermost redex first
- **Strongly normalizing**: if a term has a normal form, normal order will find it
- May reduce under lambdas and may not terminate for some arguments

**2. Call-by-Name**
- Like normal order, but doesn't reduce under lambdas
- Arguments are passed unevaluated
- Used in Haskell (with optimizations like sharing)

**3. Call-by-Value**
- Reduces the leftmost-outermost redex, but only after its argument is a value
- Arguments are fully evaluated before function application
- Used in most strict languages (ML, Scheme, JavaScript)

### Small-Step Semantics

**Call-by-Value:**

```
              t₁ → t₁'
        ─────────────────               (E-App1)
        t₁ t₂ → t₁' t₂

              t₂ → t₂'
        ─────────────────               (E-App2)
        v₁ t₂ → v₁ t₂'

        (λx. t) v → [x ↦ v]t            (E-AppAbs)
```

Where `v` represents a value (lambda abstraction).

**Normal Order:**

```
              t₁ → t₁'
        ─────────────────               (E-App1)
        t₁ t₂ → t₁' t₂

        (λx. t₁) t₂ → [x ↦ t₂]t₁       (E-AppAbs)

              t₂ → t₂'
        ─────────────────               (E-App2) [only if t₁ is in normal form]
        t₁ t₂ → t₁ t₂'
```

## Church Encodings

Since lambda calculus has no built-in primitives, we can encode data structures and control flow using only functions.

### Booleans

```
true  = λt. λf. t
false = λt. λf. f
if    = λp. λt. λf. p t f
and   = λp. λq. p q false
or    = λp. λq. p true q
not   = λp. p false true
```

### Natural Numbers (Church Numerals)

A Church numeral represents `n` by applying a function `f` n times:

```
0 = λf. λx. x
1 = λf. λx. f x
2 = λf. λx. f (f x)
3 = λf. λx. f (f (f x))
...

succ = λn. λf. λx. f (n f x)
plus = λm. λn. λf. λx. m f (n f x)
mult = λm. λn. λf. m (n f)
```

### Pairs

```
pair = λx. λy. λf. f x y
fst  = λp. p (λx. λy. x)
snd  = λp. p (λx. λy. y)
```

## Fixed-Point Combinator

The Y combinator allows recursion without named functions:

```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

**Property**: `Y g = g (Y g)` for any `g`

This enables defining recursive functions like factorial:

```
fact = Y (λf. λn. if (isZero n) 1 (mult n (f (pred n))))
```

**Note**: Y combinator doesn't terminate under call-by-value. For CBV, use the Z combinator:

```
Z = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
```

## Implementation

### Project Structure

```
chapter-01-untyped-lambda/
├── src/
│   ├── Syntax.hs      -- AST and substitution
│   ├── Eval.hs        -- Evaluation strategies
│   ├── Parser.hs      -- Parser for lambda terms
│   └── Pretty.hs      -- Pretty printer
├── test/
│   └── Spec.hs        -- Test suite
├── package.yaml       -- Haskell package configuration
└── README.md          -- This file
```

### Building and Testing

```bash
# Build the project
stack build

# Run tests
stack test

# Load in GHCi
stack ghci
```

### Usage Example

```haskell
import Syntax
import Eval
import Parser
import Pretty

-- Parse a term
let Right term = parseTerm "(\\x. x) y"

-- Evaluate it
let result = eval term

-- Pretty print
putStrLn $ pretty result  -- Output: y
```

## Key Concepts

1. **Abstraction**: Functions are first-class values
2. **Application**: The only way to compute is by function application
3. **Substitution**: The mechanism for parameter passing
4. **α-equivalence**: `λx. x` and `λy. y` are equivalent (renaming)
5. **β-reduction**: The core computation rule
6. **η-equivalence**: `λx. f x` and `f` are equivalent (if `x ∉ FV(f)`)
7. **Confluence**: Different reduction orders lead to the same result (if they terminate)
8. **Normalization**: Not all terms have a normal form (e.g., `(λx. x x) (λx. x x)`)

## Theoretical Properties

### Church-Rosser Theorem (Confluence)

If `t →* t₁` and `t →* t₂`, then there exists a term `t'` such that `t₁ →* t'` and `t₂ →* t'`.

**Consequence**: Normal forms are unique (up to α-equivalence).

### Standardization Theorem

Every terminating reduction sequence can be reordered into a standard reduction sequence (leftmost-outermost).

**Consequence**: Normal order evaluation is complete—if a normal form exists, normal order will find it.

## Real-World Connections

While the untyped lambda calculus is a theoretical foundation, its concepts appear throughout modern programming languages. Understanding lambda calculus helps you recognize these patterns and use them effectively.

### Where You've Seen This

#### **JavaScript / TypeScript**
```javascript
// Lambda abstraction → Arrow functions
const identity = x => x;                    // λx. x
const constant = x => y => x;               // λx. λy. x
const compose = f => g => x => f(g(x));     // λf. λg. λx. f (g x)

// Higher-order functions everywhere
[1, 2, 3].map(x => x * 2);                  // map is function application
const twice = f => x => f(f(x));            // λf. λx. f (f x)
```

#### **Python**
```python
# Lambda expressions (limited to single expressions)
identity = lambda x: x
add = lambda x: lambda y: x + y

# List comprehensions are lambda calculus under the hood
squares = [x**2 for x in range(10)]
# Equivalent to: map (λx. x²) [0..9]
```

#### **Haskell / OCaml / F#**
```haskell
-- Pure lambda calculus is the foundation
identity :: a -> a
identity = \x -> x                          -- λx. x

-- Currying is automatic (every function takes one argument)
add :: Int -> Int -> Int
add = \x -> \y -> x + y                     -- λx. λy. x + y

-- Pattern matching is Church encoding made practical
```

#### **Scheme / Racket / Clojure**
```scheme
;; Lisp dialects are essentially lambda calculus + primitives
(define identity (lambda (x) x))
(define (compose f g) (lambda (x) (f (g x))))

;; Y combinator actually works (unlike in typed languages)!
(define Y
  (lambda (f)
    ((lambda (x) (f (lambda (v) ((x x) v))))
     (lambda (x) (f (lambda (v) ((x x) v)))))))
```

#### **C++ / Java**
```cpp
// Lambdas added in C++11, Java 8
auto identity = [](auto x) { return x; };                    // λx. x
auto twice = [](auto f) {                                    // λf. λx. f (f x)
    return [f](auto x) { return f(f(x)); };
};

// Java
Function<Integer, Integer> identity = x -> x;
Function<Function<Integer,Integer>, Function<Integer,Integer>> twice =
    f -> x -> f.apply(f.apply(x));
```

### Concepts in Action

| Lambda Calculus Concept | Modern Programming Feature |
|-------------------------|----------------------------|
| **λ-abstraction** | Anonymous functions, lambdas, closures |
| **β-reduction** | Function application, method calls |
| **Currying** | Partial application, argument binding |
| **Church encoding** | Functional data structures, visitor pattern |
| **Recursion via Y** | Fixed-point operators, recursive definitions |
| **Call-by-value** | Eager evaluation (Java, Python, JavaScript) |
| **Call-by-name** | Lazy evaluation (Haskell), short-circuit operators |
| **α-conversion** | Variable renaming, avoiding shadowing |
| **Closure** | Captured variables in nested functions |

### What Problems Does This Solve?

#### **1. First-Class Functions**
**Problem in early languages**: Functions weren't "real" values.
```c
// C (pre-C11): No lambda, must define named functions
int add(int x, int y) { return x + y; }
// Can't easily pass custom logic to qsort without defining a global function
```

**Lambda calculus solution**: Functions are values like any other.
```javascript
// Modern JavaScript: Functions are first-class
const numbers = [3, 1, 4, 1, 5, 9];
numbers.sort((a, b) => a - b);  // Pass lambda directly
```

#### **2. Abstraction and Composition**
**Problem**: Code duplication when operations differ slightly.
```javascript
// Without lambdas: repetitive code
function processNumbers(arr) {
    let result = [];
    for (let i = 0; i < arr.length; i++) {
        result.push(arr[i] * 2);
    }
    return result;
}
```

**Lambda calculus solution**: Abstract the varying part.
```javascript
// With lambdas: reusable higher-order function
const map = f => arr => arr.map(f);
const double = map(x => x * 2);
const square = map(x => x * x);
```

#### **3. Deferred Computation**
**Problem**: Need to delay computation or pass around behavior.
```python
# Without lambdas: awkward
def make_multiplier(n):
    def multiplier(x):
        return x * n
    return multiplier
```

**Lambda calculus solution**: Closures capture environment.
```python
# With lambdas: clean
make_multiplier = lambda n: lambda x: x * n
times_10 = make_multiplier(10)
times_10(5)  # 50
```

### Historical Impact

The untyped lambda calculus has profoundly influenced programming language design:

1. **Lisp (1958)**: First language based on lambda calculus
   - Introduced `lambda` keyword (directly from Church)
   - S-expressions mirror lambda term structure

2. **Scheme (1975)**: Purified Lisp with proper tail calls
   - Lexical scoping = capture-avoiding substitution
   - Continuations = reified β-reductions

3. **ML (1973)**: Added types to lambda calculus
   - Led to Hindley-Milner type inference (Chapter 4)
   - OCaml, F#, Standard ML descended from this

4. **Haskell (1990)**: Pure lazy functional language
   - Call-by-name evaluation (with optimizations)
   - Everything is lambda calculus under the hood

5. **JavaScript (1995)**: Lambdas hidden in C-like syntax
   - Functions are first-class (from Scheme influence)
   - Closures work exactly like lambda calculus

6. **Modern languages**: C++11, Java 8, C# 3.0, Swift, Kotlin, Rust
   - All added lambdas/closures after 2000s
   - Recognition that lambda calculus patterns are essential

### Common Patterns from Lambda Calculus

#### **Pattern 1: Higher-Order Functions**
```javascript
// map, filter, reduce are all lambda calculus
const pipeline = arr => arr
    .map(x => x * 2)           // λx. x * 2
    .filter(x => x > 10)       // λx. x > 10
    .reduce((a, b) => a + b);  // λa. λb. a + b
```

#### **Pattern 2: Function Composition**
```haskell
-- Haskell (.) operator is function composition from lambda calculus
(f . g) x = f (g x)            -- λf. λg. λx. f (g x)

-- Build complex transformations
processData = filter isValid . map transform . sort
```

#### **Pattern 3: Currying and Partial Application**
```javascript
// Currying: multi-argument function → chain of single-argument functions
const add = x => y => x + y;   // λx. λy. x + y
const add5 = add(5);           // Partial application
add5(3);  // 8
```

#### **Pattern 4: Callbacks and Continuations**
```javascript
// Continuation-passing style (CPS) is lambda calculus
fetchData(url, data => {             // λdata. processData data
    processData(data, result => {    // λresult. saveResult result
        saveResult(result);
    });
});

// Modern async/await is syntactic sugar for CPS!
```

### Why Study Untyped Lambda Calculus?

1. **Understand closures**: Why captured variables work the way they do
2. **Master higher-order functions**: map, filter, reduce, compose
3. **Recognize patterns**: See lambda calculus everywhere in code
4. **Debug functional code**: Understand evaluation strategies
5. **Learn new languages faster**: Functional languages are variations on lambda calculus
6. **Prepare for advanced topics**: Types (Ch 2), inference (Ch 4), dependent types (Ch 7-8)

### Limitations and Extensions

**What untyped lambda calculus lacks** (addressed in later chapters):

| Limitation | Problem | Solution (Chapter) |
|------------|---------|-------------------|
| **No types** | `(λx. x x) (λx. x x)` loops forever | Simply Typed Lambda Calculus (Ch 2) |
| **No data structures** | Must encode booleans, numbers, lists | Algebraic Data Types (Ch 3) |
| **No automatic inference** | Verbose type annotations | Hindley-Milner (Ch 4) |
| **No polymorphism** | Can't write generic functions | System F (Ch 5) |
| **No type-level functions** | Can't abstract over type constructors | System F-omega (Ch 6) |
| **Types can't depend on values** | Can't express "vector of length n" | Dependent Types (Ch 7-8) |

## References

### Essential Reading

1. **Barendregt, H. P.** (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
   The definitive reference on lambda calculus with comprehensive treatment of theory and metatheory.
   [Google Scholar](https://scholar.google.com/scholar?cluster=8536428947517588697)

2. **Pierce, Benjamin C.** (2002). *Types and Programming Languages*. MIT Press.
   Chapter 5: The Untyped Lambda Calculus - Excellent introduction with implementation focus.
   [MIT Press](https://www.cis.upenn.edu/~bcpierce/tapl/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=2853553209915529600)

3. **Hankin, Chris** (2004). *An Introduction to Lambda Calculi for Computer Scientists*. College Publications.
   Concise introduction with good balance of theory and practice.
   [Google Scholar](https://scholar.google.com/scholar?cluster=17827063328737839947)

### Additional Resources

4. **Church, Alonzo** (1941). *The Calculi of Lambda Conversion*. Princeton University Press.
   Original work introducing lambda calculus.
   [Google Scholar](https://scholar.google.com/scholar?cluster=14093673424906302135)

5. **Hindley, J. Roger and Seldin, Jonathan P.** (2008). *Lambda-Calculus and Combinators: An Introduction*. Cambridge University Press.
   Modern introduction with combinatory logic.
   [Google Scholar](https://scholar.google.com/scholar?cluster=9220574068893588976)

6. **Sørensen, Morten Heine and Urzyczyn, Paweł** (2006). *Lectures on the Curry-Howard Isomorphism*. Elsevier.
   Connection between lambda calculus and logic.
   [Google Scholar](https://scholar.google.com/scholar?cluster=16458152610971891441)

### Online Resources

7. **Lambda Calculus on Wikipedia**: https://en.wikipedia.org/wiki/Lambda_calculus
   Good overview and historical context.

8. **Cardone, Felice & Hindley, J. Roger** (2006). "History of Lambda-calculus and Combinatory Logic". *Handbook of the History of Logic*.
   Historical perspective on lambda calculus.
   [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S1570086806800119) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=11366270838458659855)

9. **Rojas, Raúl** (2015). "A Tutorial Introduction to the Lambda Calculus". arXiv:1503.09060.
   Accessible tutorial with examples.
   [arXiv](https://arxiv.org/abs/1503.09060) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=4134096290685168656)

## Exercises

1. Implement additional Church encodings (lists, trees)
2. Add α-conversion as an explicit operation
3. Implement the η-reduction rule
4. Add a step-by-step evaluator with visualization
5. Implement the Z combinator and test recursive functions
6. Compare performance of different evaluation strategies
7. Implement DeBruijn indices to avoid variable capture issues
8. Add a REPL (Read-Eval-Print-Loop) for interactive exploration

## Next Chapter

In [Chapter 2](../chapter-02-simply-typed-lambda), we add a simple type system to prevent certain runtime errors and ensure termination.
