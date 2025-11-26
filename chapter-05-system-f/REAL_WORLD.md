# Chapter 5: Real-World Connections

## Generics Are System F

### Java Generics

```java
// This is System F polymorphism!
public <T> T identity(T x) {
    return x;
}

// Type abstraction: Λα
// Type application: identity<String>("hello")
String result = identity("hello");  // Type inferred
String explicit = <String>identity("hello");  // Explicit (rare)
```

### C++ Templates

```cpp
// Templates are a form of polymorphism
template<typename T>
T identity(T x) {
    return x;
}

// Usage (type application)
int n = identity(42);        // T = int (inferred)
int m = identity<int>(42);   // Explicit
```

### TypeScript Generics

```typescript
// Generic function (System F style)
function identity<T>(x: T): T {
  return x;
}

// Type application
const n: number = identity<number>(42);
const s: string = identity("hello");  // Inferred

// Generic classes
class Box<T> {
  constructor(public value: T) {}
}

const numBox = new Box<number>(42);
```

### Rust Generics

```rust
// Generic function
fn identity<T>(x: T) -> T {
    x
}

// With trait bounds (like type classes)
fn print_it<T: std::fmt::Display>(x: T) {
    println!("{}", x);
}

// Turbofish syntax for type application
let n = identity::<i32>(42);
```

---

## Explicit vs Implicit Type Application

### System F (This Course)

```
id = Λα. λx:α. x      -- Type abstraction
id [Nat] 5            -- Explicit type application
```

### Real Languages

| Language | Type Application | Typical Usage |
|----------|------------------|---------------|
| Java | `<String>method(...)` | Usually omitted |
| C++ | `method<int>(...)` | Sometimes needed |
| Rust | `method::<i32>(...)` | When inference fails |
| TypeScript | `method<string>(...)` | When inference fails |
| Go | `Method[int](...)` | Go 1.18+ |

---

## Higher-Rank Types

### The Problem

```typescript
// What if we want a function that takes a polymorphic function?
function applyTwice(f: ???, x: number, y: string) {
  return [f(x), f(y)];
}

// We need: f: ∀α. α → α (not just T → T for some T)
```

### TypeScript (Limited)

```typescript
// TypeScript can do this with careful syntax:
function applyTwice<A, B>(
  f: <T>(x: T) => T,  // Polymorphic parameter!
  x: A,
  y: B
): [A, B] {
  return [f(x), f(y)];
}

applyTwice(x => x, 42, "hello");  // [42, "hello"]
```

### Haskell (RankNTypes)

```haskell
{-# LANGUAGE RankNTypes #-}

applyTwice :: (forall a. a -> a) -> b -> c -> (b, c)
applyTwice f x y = (f x, f y)

applyTwice id 42 "hello"  -- (42, "hello")
```

### Why It's Tricky

Higher-rank types require explicit type abstraction because inference is undecidable (as you learned!).

---

## Parametricity in Practice

### Free Theorems

```typescript
// From the type alone, we know:
function mystery<T>(x: T): T {
  // Must be identity! Can't inspect or create T values
  return x;
}

// From this type:
function mystery2<T>(xs: T[]): T[] {
  // Can only: reorder, duplicate, drop elements
  // Cannot: change elements, filter by value
}
```

### Why This Matters

```typescript
// Parametricity guarantees this is safe:
const userIds: UserId[] = [1, 2, 3];
const reversed = reverse(userIds);
// Type system guarantees no IDs were modified!

// reverse: ∀α. α[] → α[]
// Can't peek inside UserId, so can't corrupt it
```

### Map-Fusion Optimization

```typescript
// Parametricity proves:
array.map(f).map(g) === array.map(x => g(f(x)))

// Compilers can optimize the left into the right!
// Only one pass through the array, not two
```

---

## Church Encodings Today

### Option Type as Church Encoding

```typescript
// Church-encoded Maybe
type ChurchMaybe<T> = <R>(onNothing: R, onJust: (x: T) => R) => R;

const nothing: ChurchMaybe<never> = (onNothing, onJust) => onNothing;
const just = <T>(x: T): ChurchMaybe<T> => (onNothing, onJust) => onJust(x);

// Usage (like pattern matching)
const result = maybeValue(
  "default",           // nothing case
  x => x.toString()    // just case
);
```

### Continuation-Passing Style

```typescript
// Church encodings are related to CPS
type Cont<R, A> = (k: (a: A) => R) => R;

// Instead of returning A, call continuation with A
const addCPS = (a: number, b: number): Cont<any, number> =>
  k => k(a + b);

addCPS(1, 2)(console.log);  // Prints 3
```

---

## Existential Types

### Abstract Types in Modules

```typescript
// TypeScript doesn't have direct existentials, but...
// Module pattern achieves similar effect:

interface Counter {
  increment(): void;
  get(): number;
}

function createCounter(): Counter {
  let count = 0;  // Hidden implementation detail
  return {
    increment: () => { count++; },
    get: () => count
  };
}

// The internal 'number' type is hidden!
// Client only sees the Counter interface
```

### Java Wildcards

```java
// Existential-like in Java:
List<?> unknownList = someList;

// We know there's SOME type, but not which
// Can read as Object, but can't add to it
```

### Rust's impl Trait

```rust
// Return "some type implementing Iterator"
fn numbers() -> impl Iterator<Item = i32> {
    vec![1, 2, 3].into_iter()
}

// Caller doesn't know exact type - existential!
```

---

## Real-World Applications

### 1. Generic Collections

```typescript
// Array<T> is System F polymorphism
const numbers: Array<number> = [1, 2, 3];
const strings: Array<string> = ["a", "b", "c"];

// Map<K, V>
const userNames: Map<UserId, string> = new Map();
```

### 2. Promise/Future

```typescript
// Promise<T> is polymorphic
async function fetchUser(id: string): Promise<User> {
  const response = await fetch(`/users/${id}`);
  return response.json();
}
```

### 3. React Components

```typescript
// Generic components
interface ListProps<T> {
  items: T[];
  renderItem: (item: T) => JSX.Element;
}

function List<T>({ items, renderItem }: ListProps<T>) {
  return <ul>{items.map(renderItem)}</ul>;
}

// Usage (type inferred from items)
<List items={users} renderItem={u => <li>{u.name}</li>} />
```

### 4. Data Structures

```typescript
// Generic tree
class TreeNode<T> {
  constructor(
    public value: T,
    public children: TreeNode<T>[] = []
  ) {}
}

// Works for any type!
const numTree = new TreeNode(1, [new TreeNode(2), new TreeNode(3)]);
const strTree = new TreeNode("a", [new TreeNode("b")]);
```

---

## When to Use Explicit Polymorphism

### Good: Library Code

```typescript
// Generic library functions benefit everyone
export function zip<A, B>(as: A[], bs: B[]): [A, B][] {
  return as.map((a, i) => [a, bs[i]]);
}
```

### Good: Type-Safe APIs

```typescript
// API client with type safety
async function apiCall<T>(endpoint: string): Promise<T> {
  const response = await fetch(endpoint);
  return response.json() as T;
}

const user = await apiCall<User>('/user/1');
```

### Overkill: Simple Functions

```typescript
// Don't over-generalize
function addNumbers<T extends number>(a: T, b: T): T {
  return (a + b) as T;
}

// Just use:
function addNumbers(a: number, b: number): number {
  return a + b;
}
```

---

## Key Takeaways for Practitioners

1. **Generics = System F**: When you write `<T>`, you're doing type abstraction

2. **Inference helps**: You rarely need to write explicit type arguments

3. **Parametricity is powerful**: Types constrain behavior predictably

4. **Higher-rank is advanced**: Most code doesn't need it

5. **Think universally**: Generic code is reusable code

---

## Tools and Languages

- **Java**: Generics since Java 5
- **C#**: Generics with reification
- **C++**: Templates (more powerful but different)
- **Rust**: Generics with trait bounds
- **TypeScript**: Full generic support
- **Go**: Generics since Go 1.18
- **Swift**: Generics with protocols
- **Kotlin**: Generics with variance annotations
