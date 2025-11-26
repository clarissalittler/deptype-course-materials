# Chapter 3: Real-World Connections

## Algebraic Data Types Everywhere

### Rust Enums and Structs

```rust
// Product type (struct)
struct Point {
    x: f64,
    y: f64,
}

// Sum type (enum)
enum Option<T> {
    None,
    Some(T),
}

enum Result<T, E> {
    Ok(T),
    Err(E),
}

// Pattern matching
match result {
    Ok(value) => println!("Success: {}", value),
    Err(e) => println!("Error: {}", e),
}
```

### TypeScript Discriminated Unions

```typescript
// Sum type with discriminant
type Shape =
  | { kind: 'circle'; radius: number }
  | { kind: 'rectangle'; width: number; height: number }
  | { kind: 'triangle'; base: number; height: number };

// Pattern matching via switch
function area(shape: Shape): number {
  switch (shape.kind) {
    case 'circle':
      return Math.PI * shape.radius ** 2;
    case 'rectangle':
      return shape.width * shape.height;
    case 'triangle':
      return 0.5 * shape.base * shape.height;
  }
}
```

### Haskell Data Types

```haskell
-- Product type
data Point = Point { x :: Double, y :: Double }

-- Sum type
data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

-- Pattern matching
case maybeValue of
  Nothing -> "empty"
  Just x  -> "got: " ++ show x
```

### Swift Enums

```swift
// Sum type with associated values
enum Result<T, E> {
    case success(T)
    case failure(E)
}

// Pattern matching
switch result {
case .success(let value):
    print("Got \(value)")
case .failure(let error):
    print("Error: \(error)")
}
```

### Kotlin Sealed Classes

```kotlin
// Sum type via sealed class
sealed class Result<out T> {
    data class Success<T>(val value: T) : Result<T>()
    data class Error(val message: String) : Result<Nothing>()
}

// Pattern matching with when
when (result) {
    is Result.Success -> println("Got ${result.value}")
    is Result.Error -> println("Error: ${result.message}")
}
```

---

## The Option/Maybe Pattern

### Null Safety Through Types

**Problem with null**:
```javascript
function getUser(id) {
  // Might return null!
  return database.find(id);
}

const user = getUser(123);
user.name;  // 💥 Runtime error if null!
```

**Solution with Option**:
```typescript
type Option<T> = { tag: 'none' } | { tag: 'some'; value: T };

function getUser(id: number): Option<User> {
  const user = database.find(id);
  return user ? { tag: 'some', value: user } : { tag: 'none' };
}

// Must handle both cases!
const result = getUser(123);
if (result.tag === 'some') {
  console.log(result.value.name);  // Safe!
}
```

### Languages with Built-in Option

| Language | Option Type | None | Some |
|----------|------------|------|------|
| Rust | `Option<T>` | `None` | `Some(x)` |
| Haskell | `Maybe a` | `Nothing` | `Just x` |
| OCaml | `'a option` | `None` | `Some x` |
| Swift | `Optional<T>` | `nil` | `value` |
| Kotlin | `T?` | `null` | `value` |
| Scala | `Option[T]` | `None` | `Some(x)` |

---

## The Result/Either Pattern

### Error Handling Through Types

**Problem with exceptions**:
```javascript
function parseJson(str) {
  return JSON.parse(str);  // Might throw!
}

// Caller might forget to handle error
const data = parseJson(userInput);
```

**Solution with Result**:
```typescript
type Result<T, E> =
  | { tag: 'ok'; value: T }
  | { tag: 'error'; error: E };

function parseJson(str: string): Result<unknown, string> {
  try {
    return { tag: 'ok', value: JSON.parse(str) };
  } catch (e) {
    return { tag: 'error', error: String(e) };
  }
}

// Must handle both cases!
const result = parseJson(userInput);
if (result.tag === 'ok') {
  useData(result.value);
} else {
  showError(result.error);
}
```

### Rust's Result Type

```rust
fn read_file(path: &str) -> Result<String, io::Error> {
    fs::read_to_string(path)
}

// Must handle error
match read_file("config.txt") {
    Ok(content) => println!("{}", content),
    Err(e) => eprintln!("Error: {}", e),
}

// Or propagate with ?
fn load_config() -> Result<Config, io::Error> {
    let content = read_file("config.txt")?;  // Propagates error
    Ok(parse_config(&content))
}
```

---

## Pattern Matching in Practice

### Destructuring

```typescript
// Product type destructuring
const { x, y } = point;

// Array destructuring (tuple-like)
const [first, second, ...rest] = array;
```

```rust
// Tuple destructuring
let (x, y) = point;

// Struct destructuring
let Point { x, y } = point;
```

```python
# Tuple unpacking
x, y = point

# With pattern matching (Python 3.10+)
match command:
    case ['quit']:
        quit()
    case ['load', filename]:
        load(filename)
    case _:
        print("Unknown command")
```

### Exhaustiveness Checking

**Rust enforces exhaustive patterns**:
```rust
enum Color {
    Red,
    Green,
    Blue,
}

fn describe(c: Color) -> &str {
    match c {
        Color::Red => "red",
        Color::Green => "green",
        // Error: non-exhaustive patterns: `Blue` not covered
    }
}
```

**TypeScript with exhaustive checks**:
```typescript
type Color = 'red' | 'green' | 'blue';

function describe(c: Color): string {
  switch (c) {
    case 'red': return 'Red';
    case 'green': return 'Green';
    // TypeScript warns if you forget 'blue'
  }
}

// Exhaustiveness helper
function assertNever(x: never): never {
  throw new Error(`Unexpected: ${x}`);
}
```

---

## Real-World Applications

### 1. State Machines

```typescript
type LoadingState<T, E> =
  | { status: 'idle' }
  | { status: 'loading' }
  | { status: 'success'; data: T }
  | { status: 'error'; error: E };

function renderState<T, E>(state: LoadingState<T, E>) {
  switch (state.status) {
    case 'idle': return <IdleView />;
    case 'loading': return <Spinner />;
    case 'success': return <DataView data={state.data} />;
    case 'error': return <ErrorView error={state.error} />;
  }
}
```

### 2. Message Types

```typescript
type WebSocketMessage =
  | { type: 'ping' }
  | { type: 'pong' }
  | { type: 'message'; content: string; from: string }
  | { type: 'error'; code: number; reason: string };

function handleMessage(msg: WebSocketMessage) {
  switch (msg.type) {
    case 'ping': send({ type: 'pong' }); break;
    case 'message': display(msg.content, msg.from); break;
    case 'error': handleError(msg.code, msg.reason); break;
  }
}
```

### 3. AST Representation

```typescript
// Representing expressions (like in this course!)
type Expr =
  | { type: 'num'; value: number }
  | { type: 'var'; name: string }
  | { type: 'add'; left: Expr; right: Expr }
  | { type: 'mul'; left: Expr; right: Expr };

function evaluate(expr: Expr, env: Map<string, number>): number {
  switch (expr.type) {
    case 'num': return expr.value;
    case 'var': return env.get(expr.name) ?? 0;
    case 'add': return evaluate(expr.left, env) + evaluate(expr.right, env);
    case 'mul': return evaluate(expr.left, env) * evaluate(expr.right, env);
  }
}
```

### 4. Command Pattern

```rust
enum Command {
    Move { x: i32, y: i32 },
    Rotate(f64),
    Scale(f64),
    Reset,
}

fn execute(cmd: Command, state: &mut State) {
    match cmd {
        Command::Move { x, y } => state.translate(x, y),
        Command::Rotate(angle) => state.rotate(angle),
        Command::Scale(factor) => state.scale(factor),
        Command::Reset => state.reset(),
    }
}
```

---

## Benefits of ADTs

### 1. Impossible States Are Unrepresentable

```typescript
// Bad: possible invalid states
interface User {
  name: string;
  email: string | null;
  verificationCode: string | null;
  isVerified: boolean;
}
// Can have isVerified=true but verificationCode set

// Good: only valid states possible
type User =
  | { status: 'unverified'; name: string; email: string; code: string }
  | { status: 'verified'; name: string; email: string };
```

### 2. Self-Documenting Code

```rust
// The type tells you exactly what can happen
fn divide(a: f64, b: f64) -> Option<f64> {
    if b == 0.0 { None } else { Some(a / b) }
}
```

### 3. Compiler-Enforced Handling

```rust
// Can't forget to handle error cases
let file = File::open("data.txt")?;  // Must handle or propagate
```

---

## Key Takeaways for Practitioners

1. **Use sum types for variants**: Don't use strings or magic numbers

2. **Use Option instead of null**: Make absence explicit

3. **Use Result instead of exceptions**: Make errors part of the API

4. **Let the compiler help**: Exhaustiveness checking catches bugs

5. **Model your domain**: ADTs represent business logic precisely

---

## Tools and Libraries

- **TypeScript**: Built-in discriminated unions
- **fp-ts** (TypeScript): Full FP with Option, Either
- **Rust**: First-class enums and pattern matching
- **neverthrow** (TypeScript): Result type library
- **Kotlin**: Sealed classes and when expressions
