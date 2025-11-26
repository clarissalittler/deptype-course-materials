# Chapter 4: Real-World Connections

## Type Inference in Popular Languages

### TypeScript

```typescript
// TypeScript infers types
const x = 5;           // x: number (inferred)
const y = "hello";     // y: string (inferred)

const add = (a: number, b: number) => a + b;
const result = add(1, 2);  // result: number (inferred)

// Generic inference
const identity = <T>(x: T): T => x;
const n = identity(42);     // n: number (inferred from argument)
const s = identity("hi");   // s: string (inferred from argument)
```

### Rust

```rust
// Rust has powerful type inference
let x = 5;              // i32 inferred
let v = vec![1, 2, 3];  // Vec<i32> inferred

// Closure inference
let add_one = |x| x + 1;  // Type inferred from usage

// Sometimes needs help
let v: Vec<i32> = Vec::new();  // Need annotation for empty container
```

### Kotlin

```kotlin
// Kotlin infers types
val x = 5              // Int inferred
val list = listOf(1, 2, 3)  // List<Int> inferred

// Lambda inference
val double = { x: Int -> x * 2 }  // Still need param type
val result = list.map { it * 2 }  // 'it' type inferred from context
```

### Go (Limited)

```go
// Go has limited inference
x := 5        // int inferred
s := "hello"  // string inferred

// But no generics inference until Go 1.18
// Now:
func Min[T constraints.Ordered](a, b T) T {
    if a < b { return a }
    return b
}
Min(1, 2)  // T=int inferred
```

---

## Let-Polymorphism in Practice

### The Key Insight

```typescript
// This works (let-polymorphism style):
const id = <T>(x: T): T => x;
const a = id(5);      // number
const b = id("hi");   // string

// This is like HM's let:
// let id = λx. x in (id 5, id "hi")
```

### Why Lambda Parameters Are Monomorphic

```typescript
// This DOESN'T work:
function useId(f: <T>(x: T) => T) {  // Higher-rank type!
  return [f(5), f("hi")];
}

// TypeScript struggles with this because f is a parameter,
// not a let-binding. You need explicit higher-rank types.
```

---

## Algorithm W in TypeScript Type Inference

### Unification at Work

```typescript
function example<T, U>(f: (x: T) => U, x: T): U {
  return f(x);
}

// When called:
example((x: number) => x.toString(), 42);

// Unification:
//   (x: T) => U  ≈  (x: number) => string
//   T ≈ number
//   U ≈ string
//   Result: string
```

### Occurs Check in Practice

```typescript
// This fails (occurs check):
type Infinite<T> = {
  value: T;
  self: Infinite<T>;  // OK: recursive type explicitly defined
}

// But this would be a problem:
// T = { self: T }  -- circular without explicit recursion
```

---

## Type Inference Limitations

### When Inference Fails

```typescript
// 1. Empty containers need annotation
const empty = [];           // any[] or never[]
const typed: number[] = []; // Need annotation

// 2. Overloaded functions
const parse = JSON.parse;   // Signature unclear
parse(str);                 // Type is 'any'

// 3. Callback inference can be tricky
[1, 2, 3].reduce((acc, x) => acc + x, 0);
// Sometimes needs: (acc: number, x: number) => acc + x
```

### When to Add Annotations

```typescript
// Good: annotate function signatures
function processUser(user: User): ProcessedUser {
  // Implementation
}

// Good: annotate when inference is unclear
const config: Config = {};

// Don't need: obvious from literal
const x = 5;  // Clearly number
```

---

## Polymorphism Comparison

### Hindley-Milner vs TypeScript

| Feature | HM | TypeScript |
|---------|----|-----------:|
| Full inference | Yes | Mostly |
| Principal types | Yes | No |
| Let-polymorphism | Yes | Yes |
| Higher-rank types | No | Limited |
| Subtyping | No | Yes |
| Type classes | No | No |

### Why TypeScript Isn't Pure HM

1. **Subtyping**: `{x: number, y: number}` is subtype of `{x: number}`
2. **Structural typing**: Based on shape, not declaration
3. **Union types**: `number | string` not in pure HM
4. **Gradual typing**: Can escape to `any`

---

## Real-World Applications

### 1. IDE Support

Type inference powers:
- **Autocomplete**: Know what methods are available
- **Hover information**: Show inferred types
- **Refactoring**: Safe renaming, extraction

```typescript
// Hover over 'result' shows inferred type
const result = users
  .filter(u => u.active)
  .map(u => u.name);
// result: string[] (inferred through chain)
```

### 2. Error Messages

```typescript
const add = (a: number, b: number) => a + b;
add("hello", 5);
// Error: Argument of type 'string' is not assignable
//        to parameter of type 'number'

// This error comes from unification failure!
// unify(string, number) fails
```

### 3. Generic Libraries

```typescript
// Library author writes generic code:
function map<T, U>(arr: T[], f: (x: T) => U): U[] {
  return arr.map(f);
}

// User doesn't need to specify types:
const lengths = map(["a", "bb", "ccc"], s => s.length);
// lengths: number[] (all inferred)
```

### 4. JSON Parsing with Type Safety

```typescript
// Zod: runtime validation with inferred types
import { z } from 'zod';

const UserSchema = z.object({
  name: z.string(),
  age: z.number(),
});

type User = z.infer<typeof UserSchema>;
// User = { name: string; age: number } (inferred!)

const user = UserSchema.parse(json);  // user: User
```

---

## Best Practices

### Let Inference Work

```typescript
// Good: let inference do its job
const numbers = [1, 2, 3];
const doubled = numbers.map(n => n * 2);

// Unnecessary: over-annotation
const numbers: Array<number> = [1, 2, 3];
const doubled: Array<number> = numbers.map((n: number): number => n * 2);
```

### Annotate Public APIs

```typescript
// Good: clear function signature
export function fetchUser(id: string): Promise<User | null> {
  // Implementation with inference inside
}

// Bad: no signature
export const fetchUser = async (id) => {
  // Caller has no idea what this returns
};
```

### Use Generics Appropriately

```typescript
// Good: generic when needed
function first<T>(arr: T[]): T | undefined {
  return arr[0];
}

// Overkill: generic when specific type is fine
function addNumbers<T extends number>(a: T, b: T): T {
  return (a + b) as T;  // Just use number!
}
```

---

## Tools Powered by HM-Style Inference

- **TypeScript**: Microsoft's typed JavaScript
- **Flow**: Facebook's JavaScript type checker
- **Reason/ReScript**: ML for JavaScript
- **PureScript**: Haskell-like for JavaScript
- **Elm**: ML for web apps
- **mypy**: Python type checker
- **Sorbet**: Ruby type checker
- **Dialyzer**: Erlang/Elixir type analysis

---

## Key Takeaways for Practitioners

1. **Trust the inference**: Don't over-annotate

2. **Annotate boundaries**: Function signatures, exports, APIs

3. **Understand let-polymorphism**: Why generic functions work

4. **Know the limits**: When inference needs help

5. **Read error messages**: Unification failures point to real bugs

---

## Further Reading

- *Programming TypeScript* - Boris Cherny
- TypeScript Handbook: Type Inference
- *Real World OCaml* - Chapters on type inference
- Original Milner paper: "A Theory of Type Polymorphism in Programming" (1978)
