# Chapter 13: Gradual Typing - Tutorial

This tutorial walks through gradual typing with step-by-step examples.

## Part 1: Why Gradual Typing?

### The Problem

Static and dynamic typing each have trade-offs:

**Static typing**:
```
add : Nat -> Nat -> Nat
add x y = x + y
-- Pro: Catches errors at compile time
-- Con: Requires annotations, less flexible
```

**Dynamic typing**:
```
def add(x, y):
    return x + y
# Pro: Flexible, no annotations
# Con: Runtime errors, no static guarantees
```

**Real codebases need both!**
- Legacy code is often dynamic
- Libraries may be untyped
- Prototyping benefits from flexibility
- Production code wants guarantees

### The Solution

Gradual typing introduces `?` (dynamic type):
- `?` is consistent with any type
- Runtime checks ensure safety
- Add types incrementally

```
-- Start dynamic
add : ? -> ? -> ?
add x y = x + y

-- Gradually add types
add : Nat -> ? -> Nat
add x y = x + y

-- Fully typed
add : Nat -> Nat -> Nat
add x y = x + y
```

## Part 2: The Dynamic Type

### What is `?`?

The dynamic type `?` represents values of unknown type:

```
x : ?          -- x has dynamic type
f : ? -> Nat   -- f takes dynamic, returns Nat
g : Nat -> ?   -- g takes Nat, returns dynamic
```

### Consistency, Not Equality

The key innovation is the **consistency relation** `~`:

```
? ~ T           -- Dynamic is consistent with anything
T ~ ?           -- Anything is consistent with dynamic
T ~ T           -- Types are consistent with themselves
```

For functions:
```
T₁ -> T₂ ~ S₁ -> S₂   when T₁ ~ S₁ and T₂ ~ S₂
```

### Why Consistency Matters

In normal type systems:
```
f : Nat -> Bool
f 5 : Bool       -- Argument must EQUAL expected type
```

In gradual typing:
```
f : Nat -> Bool
x : ?
f x : Bool       -- Argument must be CONSISTENT with expected type
```

### Consistency is NOT Transitive!

This is crucial:
```
Nat ~ ?      ✓ (Nat consistent with dynamic)
? ~ Bool     ✓ (Dynamic consistent with Bool)
Nat ~ Bool   ✗ (Nat NOT consistent with Bool)
```

If consistency were transitive, everything would be consistent with everything!

## Part 3: Cast Calculus

### Implicit Casts

The surface language has implicit type coercions:
```
(λx : ?. x + 1) true
```

This type checks because `Bool ~ ?`, but needs runtime checking!

### Explicit Casts

The internal language makes casts explicit:
```
<T₁ => T₂>^l t
```

Meaning: Cast t from type T₁ to type T₂, with blame label l.

### Cast Insertion Example

Source program:
```
(λx : ?. x + 1) true
```

After cast insertion:
```
(λx : ?. <? => Nat>^body x + 1) <Bool => ?>^arg true
```

Casts inserted:
1. `<Bool => ?>`: Inject `true` into dynamic type
2. `<? => Nat>`: Project `x` from dynamic to Nat

### Cast Semantics

Casts reduce at runtime:

**Identity cast**:
```
<T => T> v = v
```
Same type, no work needed.

**Injection** (into dynamic):
```
<Bool => ?> true = <Bool => ?> true   -- Stays as tagged value
```

**Projection** (from dynamic):
```
<? => Bool> (<Bool => ?> true) = true    -- Success: tags match
<? => Nat> (<Bool => ?> true) = blame^l  -- Failure: wrong tag!
```

**Function casts** (distribute):
```
<T₁->T₂ => S₁->S₂>^l f = λx. <T₂ => S₂>^l (f (<S₁ => T₁>^l̄ x))
```
Note: argument cast uses opposite blame (negative).

## Part 4: Ground Types

### What Are Ground Types?

Ground types are the "runtime tags" for dynamic values:
- `Bool`, `Nat`, `Unit` -- base types are ground
- `? -> ?` -- THE function ground type

### Why Ground Types?

When injecting into `?`, we use ground types:
```
<Bool => ?> true           -- Tag: Bool
<Nat -> Bool => ?> f       -- Tag: ? -> ? (all functions same tag!)
```

### Projection Through Ground

To project from `?`, we go through ground types:
```
<? => Nat> v
```
Actually means:
```
Check: is v tagged with Nat?
If yes: extract value
If no: blame!
```

### Function Projection

For functions:
```
<? => Nat -> Bool> v
```
Becomes:
```
<? => ? -> ?> v            -- First check it's a function
<? -> ? => Nat -> Bool> v  -- Then cast function type
```

## Part 5: Blame Tracking

### What is Blame?

When a cast fails, we need to know WHO is responsible:
```
(<Bool => Nat>^myLabel true)  →  blame^myLabel : Nat
```

The label `myLabel` identifies the problematic code location.

### Positive vs Negative Blame

Consider a function boundary:
```
f : (Nat -> Bool) -> Nat
g : ?

f g  -- What if g returns Nat instead of Bool?
```

**Positive blame**: The value provided was wrong
**Negative blame**: The function misused its input

### Blame Theorem

> Well-typed programs can't be blamed.

If code is fully statically typed (no `?`), it will never be the source of blame!

Blame always originates from the dynamic parts.

### Worked Example

```
let f : ? -> Nat = λx. x + 1
let v : Bool = true
f v
```

Cast insertion:
```
f (<Bool => ?>^call v)
```

Inside f, there's:
```
<? => Nat>^body x + 1
```

Execution:
1. `v` cast to `?` with tag Bool
2. Inside f, x has type ?
3. Cast `<? => Nat>` fails because tag is Bool!
4. Result: `blame^body`

## Part 6: Gradual Migration

### The Migration Path

Start with dynamic code:
```
-- Version 1: All dynamic
let process = λdata : ?. λconfig : ?.
  ... process data based on config ...
```

Add types to critical paths:
```
-- Version 2: Partial types
let process = λdata : Data. λconfig : ?.
  ... process data based on config ...
```

Complete the migration:
```
-- Version 3: Fully typed
let process = λdata : Data. λconfig : Config.
  ... process data based on config ...
```

### Benefits of Gradual Migration

1. **No big bang**: Don't rewrite everything at once
2. **Testing ground**: Try types, revert if needed
3. **Documentation**: Types document intent
4. **Safety**: More types = more static guarantees

### Real-World Strategy

1. **Start at boundaries**: Type public APIs first
2. **Follow dependencies**: Type modules that others depend on
3. **Add critical paths**: Type security-sensitive code
4. **Fill in the rest**: Gradually complete coverage

## Practice Problems

### Problem 1: Consistency

Are these types consistent?
```
a) Nat ~ ?
b) ? ~ Nat -> Bool
c) (Nat -> Bool) ~ (? -> ?)
d) (Nat -> Nat) ~ (Bool -> Bool)
```

<details>
<summary>Solution</summary>

a) Yes: Nat ~ ?
b) Yes: ? ~ anything
c) Yes: Nat ~ ? and Bool ~ ?
d) No: Nat ≁ Bool
</details>

### Problem 2: Cast Insertion

Insert casts into:
```
(λf : ?. f 0) (λx : Nat. x)
```

<details>
<summary>Solution</summary>

```
(λf : ?. (<? => Nat -> ?>^body f) 0)
  (<Nat -> Nat => ?>^arg (λx : Nat. x))
```

The function is cast to `?`, then inside we cast it back to a function type to apply it.
</details>

### Problem 3: Cast Reduction

What does this reduce to?
```
<? => Nat> (<Bool => ?> true)
```

<details>
<summary>Solution</summary>

`blame^l`

The value is tagged as Bool, but we're projecting to Nat. Tag mismatch = blame!
</details>

### Problem 4: Blame

In this code, where does blame originate?
```
let f : Nat -> Nat = λx. x + 1
let g : ? -> ? = f
g true
```

<details>
<summary>Solution</summary>

Blame is at the call site `g true`.

- `f` is fully typed (can't be blamed)
- `g : ? -> ?` accepts the cast of `true`
- Inside, the cast `<? => Nat>` fails on `true`
- Blame label points to where we called `g` with `true`
</details>

### Problem 5: Migration

Type this gradually:
```
let compose = λf. λg. λx. f (g x)
```

<details>
<summary>Solution</summary>

Step 1: All dynamic
```
compose : ? -> ? -> ? -> ?
```

Step 2: Type structure
```
compose : (? -> ?) -> (? -> ?) -> ? -> ?
```

Step 3: Add type parameters
```
compose : ∀a b c. (b -> c) -> (a -> b) -> a -> c
```

(Full polymorphism requires gradual polymorphism.)
</details>
