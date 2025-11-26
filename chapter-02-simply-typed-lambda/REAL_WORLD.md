# Chapter 2: Real-World Connections

## Type Annotations in Popular Languages

### TypeScript

```typescript
// Type annotations are exactly like STLC
const identity = (x: number): number => x;

// Function types: τ₁ → τ₂
type NumberToString = (n: number) => string;

// Higher-order functions
const apply = (f: (x: number) => number, x: number): number => f(x);
```

### Python Type Hints

```python
# PEP 484 type hints follow STLC principles
def identity(x: int) -> int:
    return x

# Function types
from typing import Callable
def apply(f: Callable[[int], int], x: int) -> int:
    return f(x)
```

### Java/Kotlin

```java
// Java with explicit types
Function<Integer, Integer> identity = x -> x;

// Kotlin with type inference (but STLC underneath)
val identity: (Int) -> Int = { x -> x }
```

### Rust

```rust
// Rust has explicit function types
fn identity(x: i32) -> i32 { x }

// Closures with type annotations
let add_one: fn(i32) -> i32 = |x| x + 1;
```

---

## Type Safety in Practice

### Preventing Runtime Errors

**Without types (JavaScript)**:
```javascript
function add(a, b) {
  return a + b;
}
add("hello", 5);  // "hello5" - probably not intended!
```

**With types (TypeScript)**:
```typescript
function add(a: number, b: number): number {
  return a + b;
}
add("hello", 5);  // Compile error!
```

### The Progress Property

In STLC, well-typed terms don't get stuck. In TypeScript:

```typescript
// TypeScript prevents "stuck" states at compile time
function processUser(user: User): string {
  return user.name.toUpperCase();
}

// If user could be null, TypeScript catches it
processUser(null);  // Error: Argument of type 'null' is not assignable
```

### The Preservation Property

Types are preserved through execution:

```typescript
const x: number = 5;        // x: number
const y: number = x + 3;    // Still number after operation
const z: number = Math.abs(y);  // Still number
```

---

## Why Some Code Doesn't Type Check

### Self-Application Problem

```typescript
// This won't work in TypeScript (just like STLC)
const selfApply = (f: any) => f(f);

// To type this, you'd need:
// f: (f → τ) → τ where f = f → τ
// That's an infinite type!
```

### The Fix: Explicit Typing

```typescript
// With explicit interface, we can control what's allowed
interface SelfApplicable<T> {
  (self: SelfApplicable<T>): T;
}
```

---

## Type Systems Hierarchy

### How Languages Extend STLC

```
STLC (this chapter)
  │
  ├── + Generics ──────────► Java, C#, Go 1.18+
  │
  ├── + Type Inference ────► TypeScript, Kotlin, Swift
  │
  ├── + ADTs ──────────────► Rust, Haskell, F#, OCaml
  │
  ├── + Null Safety ───────► Kotlin, Swift, Rust
  │
  └── + Dependent Types ───► Idris, Agda, Lean
```

---

## Practical Type Checking

### TypeScript's Structural Typing

```typescript
// TypeScript uses structural typing (like STLC)
interface Point {
  x: number;
  y: number;
}

function printPoint(p: Point) {
  console.log(`${p.x}, ${p.y}`);
}

// This works because the structure matches
const myObj = { x: 10, y: 20, z: 30 };
printPoint(myObj);  // OK! Has x and y
```

### Flow's Type Inference

```javascript
// @flow
function add(a, b) {
  return a + b;
}

// Flow infers: (number, number) => number
add("hi", 5);  // Error!
```

---

## Real Applications

### 1. API Contracts

```typescript
// Types define the contract
interface ApiResponse<T> {
  data: T;
  status: number;
  error?: string;
}

async function fetchUser(id: number): Promise<ApiResponse<User>> {
  // Return type is guaranteed!
}
```

### 2. State Management

```typescript
// Redux with TypeScript
interface State {
  count: number;
  loading: boolean;
}

type Action =
  | { type: 'INCREMENT' }
  | { type: 'SET_LOADING'; payload: boolean };

function reducer(state: State, action: Action): State {
  // Type checker ensures we handle all cases correctly
}
```

### 3. React Components

```typescript
interface Props {
  name: string;
  age: number;
  onUpdate: (name: string) => void;
}

const UserCard: React.FC<Props> = ({ name, age, onUpdate }) => {
  // Props are type-checked!
};
```

### 4. Database Queries

```typescript
// Prisma generates types from schema
const user = await prisma.user.findUnique({
  where: { id: 1 }
});
// user is typed as User | null
```

---

## The Value of Type Safety

### Catching Errors Early

```
                    Cost to fix
                         │
                         │                    ████
                         │               ███████
                         │          █████████
                         │      ████████
                         │   ████
                         │ ██
                         │█
                         └──────────────────────────
                          Compile  Test  Deploy  Production
                           time   time   time    (outage!)

Types catch errors at compile time = lowest cost!
```

### Documentation Through Types

```typescript
// Types ARE documentation
function processOrder(
  order: Order,
  customer: Customer,
  options: ProcessingOptions
): Promise<Receipt>

// vs undocumented
function processOrder(order, customer, options)
```

---

## Limitations of Simple Types

### What STLC Can't Express

1. **Generic functions**: Need polymorphism (Chapter 5)
   ```typescript
   // Can't write without generics:
   function identity<T>(x: T): T { return x; }
   ```

2. **Variable-length structures**: Need recursive types
   ```typescript
   // Lists need more than simple types
   type List<T> = null | { head: T; tail: List<T> };
   ```

3. **Optional values**: Need sum types (Chapter 3)
   ```typescript
   // Option/Maybe pattern
   type Option<T> = { tag: 'none' } | { tag: 'some'; value: T };
   ```

---

## Key Takeaways for Practitioners

1. **Type annotations prevent bugs**: Most type errors catch real logic errors

2. **Types are documentation**: Function signatures tell you what a function does

3. **Type inference helps**: You don't always need to write types explicitly

4. **Not all programs type check**: Some valid programs are rejected (self-application)

5. **Types compose**: Well-typed components combine into well-typed systems

---

## Tools Using These Concepts

- **TypeScript**: JavaScript with STLC-style types
- **Flow**: Static type checker for JavaScript
- **mypy**: Python type checker
- **Sorbet**: Ruby type checker
- **Dialyzer**: Erlang type analysis
- **Psalm/PHPStan**: PHP type checkers
