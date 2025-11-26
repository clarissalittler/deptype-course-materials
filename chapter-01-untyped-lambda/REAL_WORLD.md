# Chapter 1: Real-World Connections

## Where Lambda Calculus Appears

### JavaScript/TypeScript: Arrow Functions

Lambda calculus is the foundation of arrow functions:

```javascript
// Lambda calculus: λx. x
const identity = x => x;

// Lambda calculus: λx. λy. x
const constant = x => y => x;

// Lambda calculus: λf. λg. λx. f(g(x))
const compose = f => g => x => f(g(x));
```

**Key insight**: JavaScript's arrow functions are literally lambda abstractions with different syntax.

### Python: Lambda Expressions

```python
# Lambda calculus: λx. x * 2
double = lambda x: x * 2

# Lambda calculus: λx. λy. x + y
add = lambda x: lambda y: x + y

# Currying in action
add_five = add(5)  # λy. 5 + y
add_five(3)        # 8
```

### Haskell: First-Class Functions

```haskell
-- Lambda calculus: λx. x
identity = \x -> x

-- Lambda calculus: λf. λx. f (f x)
twice = \f -> \x -> f (f x)

-- Application
twice (+1) 5  -- 7
```

### Ruby: Blocks and Lambdas

```ruby
# Lambda calculus: λx. x + 1
increment = ->(x) { x + 1 }

# Lambda calculus: λf. λx. f(f(x))
twice = ->(f) { ->(x) { f.(f.(x)) } }
```

---

## Church Encodings in Practice

### Booleans as Functions

The Church encoding of booleans appears in some functional patterns:

```javascript
// Church booleans
const TRUE = t => f => t;
const FALSE = t => f => f;

// Usage (like if-then-else)
const result = condition(whenTrue)(whenFalse);

// Real-world equivalent: the ternary operator
const result = condition ? whenTrue : whenFalse;
```

### Church Numerals and Iteration

```javascript
// Church numeral: apply f n times
const three = f => x => f(f(f(x)));

// This is like Array.reduce!
[1, 2, 3].reduce((acc, _) => acc + 1, 0);  // Apply (+1) three times
```

### Scott Encoding (Variant)

Pattern matching in functional languages uses a similar idea:

```haskell
-- Instead of:
case maybeValue of
  Nothing -> defaultValue
  Just x  -> f x

-- Scott encoding:
maybeValue defaultValue f
```

---

## Evaluation Strategies

### Call-by-Value (Most Languages)

```javascript
// JavaScript uses call-by-value
function example(x) {
  return 42;
}

// This expression is evaluated BEFORE the call
example(expensiveComputation());  // expensiveComputation runs!
```

### Call-by-Name / Lazy Evaluation (Haskell)

```haskell
-- Haskell uses lazy evaluation
example x = 42

-- This expression is NOT evaluated (not needed!)
example expensiveComputation  -- expensiveComputation doesn't run
```

### Short-Circuit Evaluation

```javascript
// This is like call-by-name for the second argument
const result = false && expensiveComputation();  // Doesn't run!
const result = true || expensiveComputation();   // Doesn't run!
```

---

## Substitution and Scope

### Variable Shadowing

```javascript
const x = "outer";
const f = (x) => {
  // This x shadows the outer x
  return x;  // Returns parameter, not "outer"
};
```

```python
x = "outer"
def f(x):
    # Parameter x shadows global x
    return x  # Returns parameter
```

### Closures = Free Variables

```javascript
function makeAdder(x) {
  // y is bound, x is FREE (captured from outer scope)
  return function(y) {
    return x + y;
  };
}

const add5 = makeAdder(5);  // x=5 is captured
add5(3);  // 8
```

This is exactly capture of free variables in lambda calculus!

---

## The Y Combinator in Real Code

### JavaScript

```javascript
// Y combinator (for call-by-value, use Z combinator)
const Y = f => (x => f(y => x(x)(y)))(x => f(y => x(x)(y)));

// Factorial without explicit recursion
const factorial = Y(f => n => n === 0 ? 1 : n * f(n - 1));
factorial(5);  // 120
```

### Why This Matters

The Y combinator shows up in:
- **Memoization frameworks**: Caching recursive calls
- **Dependency injection**: Providing implementations at runtime
- **Testing**: Injecting mock recursive calls

---

## Practical Applications

### 1. Functional Programming Libraries

**Ramda (JavaScript)**:
```javascript
const R = require('ramda');
R.compose(f, g)(x);  // Function composition
R.curry(fn);         // Currying
R.pipe(f, g, h);     // Left-to-right composition
```

**Lodash FP**:
```javascript
const fp = require('lodash/fp');
fp.flow(f, g, h);    // Composition
fp.curry(fn);        // Currying
```

### 2. React Hooks

```javascript
// Hooks are higher-order functions!
const [state, setState] = useState(initialValue);

// useCallback captures free variables
const memoizedFn = useCallback(
  () => doSomethingWith(a, b),  // a, b are free variables
  [a, b]
);
```

### 3. Redux Reducers

```javascript
// Reducers are pure functions
const reducer = (state, action) => {
  // λstate. λaction. newState
  switch(action.type) {
    case 'INCREMENT': return state + 1;
    default: return state;
  }
};
```

---

## Key Takeaways for Practitioners

1. **Arrow functions are lambdas**: `x => x` is literally `λx. x`

2. **Currying is practical**: Partial application enables function composition
   ```javascript
   const add = a => b => a + b;
   const add5 = add(5);  // Partially applied
   ```

3. **Closures are free variable capture**: Understanding lambda calculus explains why closures work

4. **Evaluation order matters**: JavaScript's strict evaluation vs Haskell's laziness comes from these foundations

5. **Higher-order functions everywhere**: map, filter, reduce are all based on lambda calculus

---

## Further Reading

- *JavaScript: The Good Parts* - Douglas Crockford
- *Functional Programming in JavaScript* - Luis Atencio
- *Professor Frisby's Mostly Adequate Guide to FP* (free online)
- *Learn You a Haskell for Great Good* (free online)
