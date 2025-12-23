# Chapter 13: Gradual Typing - Common Mistakes

This guide covers frequent errors when learning gradual typing.

---

## Mistake 1: Thinking Consistency is Transitive

### The Problem
Assuming if A ~ B and B ~ C, then A ~ C.

### Wrong Thinking
```
Nat ~ ?     (Nat consistent with dynamic)
? ~ Bool    (Dynamic consistent with Bool)
∴ Nat ~ Bool  -- WRONG!
```

### Correct Understanding
Consistency is NOT transitive by design:
```
Nat ~ ?     ✓
? ~ Bool    ✓
Nat ~ Bool  ✗  -- Still not consistent!
```

### Why?
If consistency were transitive, everything would be consistent with everything through ?. Gradual typing would lose all precision!

### How to Remember
> "Consistency is reflexive and symmetric, NOT transitive."

---

## Mistake 2: Confusing Consistency with Equality

### The Problem
Thinking consistent types are the same type.

### Wrong Thinking
```
Nat ~ ?
∴ Nat = ?  -- WRONG!
```

### Correct Understanding
Consistency means "compatible for this interaction":
- `Nat ~ ?` means you can pass Nat where ? expected
- But Nat and ? are different types
- Runtime cast still needed

### How to Remember
> "Consistent ≠ Equal. Casts may still fail at runtime."

---

## Mistake 3: Forgetting Casts Are Needed

### The Problem
Thinking type checking alone ensures safety.

### Wrong Thinking
```
f : ? -> Nat
f true       -- "Type checks, so it works!"
```

### Correct Understanding
Type checking succeeds, but runtime cast may fail:
```
f (<Bool => ?>^arg true)   -- Cast inserted
-- Inside f:
<? => Nat>^body x          -- This will fail!
```

### How to Remember
> "Consistency allows type checking. Casts ensure runtime safety."

---

## Mistake 4: Misunderstanding Blame Direction

### The Problem
Not knowing who to blame when cast fails.

### Wrong Analysis
```
let f : ? -> Nat = ...
f true
-- "f is wrong!"  -- Not necessarily!
```

### Correct Understanding
Blame labels track the SOURCE of the problem:
- If `f` is well-typed, it can't be blamed
- The caller passing `true` into `f` is blamed
- Blame points to the dynamic boundary

### How to Remember
> "Well-typed code can't be blamed. Look at the ? boundaries."

---

## Mistake 5: Wrong Ground Type for Functions

### The Problem
Thinking each function type has its own ground type.

### Wrong Thinking
```
Nat -> Bool    has ground type Nat -> Bool
Int -> String  has ground type Int -> String
```

### Correct Understanding
ALL functions share the same ground type:
```
Nat -> Bool    has ground type ? -> ?
Int -> String  has ground type ? -> ?
A -> B         has ground type ? -> ?
```

### Why?
Ground types are runtime tags. One tag for "is a function".

### How to Remember
> "Ground types: base types as themselves, ALL functions as ? -> ?."

---

## Mistake 6: Forgetting Argument Cast is Contravariant

### The Problem
Getting the direction wrong for function casts.

### Wrong Distribution
```
<A -> B => C -> D>^l f
= λx. <B => D>^l (f (<A => C>^l x))  -- WRONG!
```

### Correct Distribution
```
<A -> B => C -> D>^l f
= λx. <B => D>^l (f (<C => A>^l̄ x))  -- Correct!
```

Note:
- Result: covariant (B => D)
- Argument: contravariant (C => A, backwards!)
- Argument uses opposite blame (l̄)

### How to Remember
> "Function casts: result forward, argument backward with opposite blame."

---

## Mistake 7: Thinking ? Makes Everything Type Check

### The Problem
Assuming any program with ? types will work.

### Wrong Thinking
```
λx : ?. x + "hello"   -- "Works because x is dynamic!"
```

### Correct Understanding
Type checking still applies:
- x : ? is consistent with Nat (for +)
- "hello" : String must be checked
- If String isn't consistent with Nat, error!

```
λx : ?. x + 1    ✓  (1 : Nat, consistent with Nat)
λx : ?. x + "a"  ✗  (String not consistent with Nat for +)
```

### How to Remember
> "? is flexible but doesn't bypass ALL type checking."

---

## Mistake 8: Confusing Type Precision with Subtyping

### The Problem
Thinking ? ⊑ T means ? <: T.

### The Difference
**Precision** (⊑): Static knowledge relationship
```
? ⊑ Nat    (? is less precise than Nat)
```

**Subtyping** (<:): Value inclusion
```
Different relation entirely!
```

### Why Different?
- Precision is about what we KNOW statically
- ? is less precise because we don't know the type
- Subtyping is about which values are valid

### How to Remember
> "Precision is about knowledge. Subtyping is about values."

---

## Mistake 9: Not Understanding Injection vs Projection

### The Problem
Confusing the two directions of casts.

### Definitions
**Injection** (<T => ?>): Into dynamic
```
<Nat => ?> 5    -- Wraps 5 with Nat tag
-- Always succeeds
```

**Projection** (<? => T>): Out of dynamic
```
<? => Nat> x    -- Checks x has Nat tag
-- May fail with blame!
```

### How to Remember
> "Injection always works (wrap). Projection may fail (check)."

---

## Mistake 10: Ignoring the Gradual Guarantee

### The Problem
Not using the guarantee to guide migration.

### What the Guarantee Says
- **Static**: More types = same typeability
- **Dynamic**: More types = same behavior (up to blame)

### How to Use It
```
-- If this works:
λx : ?. x + 1

-- This also works (just with more static checking):
λx : Nat. x + 1
```

### How to Remember
> "Adding types is safe. Use the guarantee to migrate confidently."

---

## Debugging Checklist

When gradual typing fails:

1. **Check consistency**: Are all types pairwise consistent?
2. **Check cast direction**: Injection always works, projection may fail
3. **Check blame labels**: Where does the error originate?
4. **Check ground types**: Are function types using ? -> ??
5. **Check transitivity**: Don't assume A ~ C from A ~ B ~ C

---

## Practice Problems

### Problem 1: Consistency Check

Is `(Nat -> ?) ~ (? -> Bool)`?

<details>
<summary>Answer</summary>

Yes!
- Nat ~ ? ✓
- ? ~ Bool ✓
- Therefore (Nat -> ?) ~ (? -> Bool) ✓
</details>

### Problem 2: Find the Blame

```
let f : Nat -> Nat = λx. x + 1
let g : ? = f
g true
```

Where's the blame?

<details>
<summary>Answer</summary>

At the call `g true`:
- `f` is well-typed (can't be blamed)
- `g : ?` accepts any call
- Inside, cast `<? => Nat>` on `true` fails
- Blame label is at the call site where `true` was passed
</details>

### Problem 3: Cast Reduction

What does this reduce to?
```
<? => ? -> ?> (<Nat => ?> 5)
```

<details>
<summary>Answer</summary>

`blame`

- 5 is tagged as Nat
- Projecting to ? -> ? checks for function tag
- Nat ≠ ? -> ? (ground type mismatch)
- Result: blame!
</details>
