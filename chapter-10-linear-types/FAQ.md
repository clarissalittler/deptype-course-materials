# Chapter 10: Linear Types - Frequently Asked Questions

## Conceptual Questions

### Q: What are linear types?

**A:** Linear types are a type system feature that tracks how many times values are used. A linear value must be used exactly once—it can't be duplicated or discarded.

This enables:
- Compile-time resource management
- Memory safety without garbage collection
- Protocol verification

### Q: Why "linear"? What does the name mean?

**A:** The name comes from linear logic (Girard, 1987). In linear logic, hypotheses must be used exactly once, unlike classical logic where they can be used any number of times.

The key connective is linear implication (⊸), which becomes the linear function type (-o) in type theory.

### Q: How is this different from Rust's ownership?

**A:** Rust's ownership is closely related but not identical:

**Linear types**: Must use exactly once (can't discard)
**Rust ownership**: Must use at most once (can discard with `drop`)

Rust is closer to **affine** types. However, Rust's `Drop` trait makes resources "effectively linear" because drop is called automatically.

### Q: What's the difference between -o and ->?

**A:**

`A -o B` (linear function):
- Uses argument exactly once
- Can only be called once if the function itself is linear

`A -> B` (unrestricted function):
- May use argument any number of times
- Traditional function semantics

### Q: What is the bang type (!A)?

**A:** `!A` represents an unrestricted value of type A. It's a way to "escape" linearity:

```
!5 : !Nat      -- 5 is unrestricted

let !x = e in t   -- Unwrap !A to get x :ω A
```

You can only create `!t` if t doesn't use any linear variables.

### Q: Why can't I just ignore a linear variable?

**A:** Ignoring a linear variable would mean using it zero times, violating "exactly once."

For resources, this makes sense:
- File handle ignored → file never closed (leak)
- Memory pointer ignored → memory never freed (leak)

Linear types make these bugs compile errors.

## Technical Questions

### Q: How does context splitting work?

**A:** When typing `(t₁, t₂)` with context Γ containing linear variables:

1. Split Γ into Γ₁ and Γ₂
2. Each linear variable goes to exactly one side
3. Type t₁ with Γ₁, t₂ with Γ₂

```
Γ = {x :1 A, y :1 B}
(x, y) uses split: {x :1 A} | {y :1 B}
```

Unrestricted variables can appear on both sides.

### Q: How does usage tracking work?

**A:** The type checker maintains usage counts:

```haskell
data Usage = Unused | UsedOnce | UsedMany

check linear variable:
  - Unused: not yet used
  - UsedOnce: used exactly once (good for linear)
  - UsedMany: used multiple times (bad for linear)
```

At the end, linear variables must be `UsedOnce`.

### Q: Can I make a linear variable unrestricted?

**A:** Only through bang:

```
-- Wrong: direct conversion
λ(x :1 Nat). let y :ω Nat = x in (y, y)  -- Invalid

-- Right: use bang
λ(x :1 !Nat). let !y = x in (y, y)       -- Valid
```

The input must already be banged.

### Q: How do I implement a linear data structure?

**A:** Thread the resource through operations:

```
-- Linear list with destructive operations
data LList a = LNil | LCons a (LList a)

-- head consumes the list, returns element + tail
head : LList a -o Maybe (a * LList a)

-- Can't just "peek" without consuming!
```

### Q: What about recursion with linear types?

**A:** Recursion needs care. The fix combinator has type:

```
fix : ((A -o B) -o A -o B) -o A -o B
```

Or with unrestricted recursion:

```
fix : ((A -> B) -> A -> B) -> A -> B
```

The recursive call is unrestricted (used many times).

## Common Confusions

### Q: Can I use a linear variable in both branches of if-then-else?

**A:** Yes! Only one branch executes:

```
λ(x :1 Nat). if c then x else x    -- OK: x used once
λ(x :1 Nat). if c then (x, x) else x  -- ERROR: x used twice in then
```

The context is shared (not split) for conditionals.

### Q: Why is `let (x, y) = p in x` invalid?

**A:** Both x and y are bound linearly. You must use both:

```
let (x, y) = p in x      -- y unused
let (x, y) = p in (x, y)  -- both used ✓
```

This is the "tensor elimination" rule.

### Q: Is Bool linear or unrestricted?

**A:** In our system, base types like Bool and Nat can be either—it depends on the context they're introduced in.

```
λ(b :1 Bool). if b then 1 else 0   -- b is linear
λ(b :ω Bool). (b, b)               -- b is unrestricted
```

### Q: What's the relationship to substructural logics?

**A:** Linear types correspond to linear logic. The substructural hierarchy:

| Logic | Weakening | Contraction |
|-------|-----------|-------------|
| Classical | Yes | Yes |
| Affine | Yes | No |
| Relevant | No | Yes |
| Linear | No | No |

- Weakening = can ignore hypotheses
- Contraction = can duplicate hypotheses

Linear types forbid both.

## Troubleshooting

### Q: I keep getting "variable used multiple times."

**A:** Check:
1. Are you using the variable directly multiple times?
2. Are you using it in multiple subterms of a pair?
3. Did you forget to make it unrestricted?

Solution: Either restructure code or change multiplicity to ω.

### Q: I keep getting "variable not used."

**A:** Check:
1. Do you actually need this variable?
2. Did you forget to include it in the return value?
3. Is there a way to "consume" it?

Solution: Use the variable, or change multiplicity to ω.

### Q: My banged value won't type check.

**A:** Check:
1. Is the value being banged free of linear variables?
2. Are you using `!e` or `let !x = e`?
3. Does e already have type `!A`?

Remember: bang introduction requires no linear variables. Bang elimination requires `!A` input.

### Q: How do I debug context splitting issues?

**A:** Trace through:
1. List all linear variables in scope
2. For each subterm, which variables does it need?
3. Check each variable goes to exactly one place

If variable needed in multiple places, you need to restructure or use bang.
