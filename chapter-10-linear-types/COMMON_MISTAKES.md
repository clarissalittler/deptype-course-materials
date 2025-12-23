# Chapter 10: Linear Types - Common Mistakes

This guide covers frequent errors when learning linear types.

---

## Mistake 1: Trying to Duplicate Linear Variables

### The Problem
Using a linear variable more than once.

### Wrong Code
```
λ(x :1 Nat). (x, x)    -- ERROR: x used twice
```

### Correct Understanding
Linear means "exactly once." To duplicate, use unrestricted:
```
λ(x :ω Nat). (x, x)    -- OK: x is unrestricted
```

Or use bang:
```
λ(b :1 !Nat). let !x = b in (x, x)  -- OK: unwrap to unrestricted
```

### How to Remember
> "Linear = exactly once. No copies allowed."

---

## Mistake 2: Trying to Discard Linear Variables

### The Problem
Not using a linear variable at all.

### Wrong Code
```
λ(x :1 Nat). 0    -- ERROR: x not used
```

### Correct Understanding
Linear variables MUST be used. If you don't need it, make it unrestricted:
```
λ(x :ω Nat). 0    -- OK: unrestricted can be ignored
```

Or consume it in a meaningful way:
```
λ(x :1 Nat). let _ = x in 0    -- Still ERROR in strict systems
```

### How to Remember
> "Linear resources can't be thrown away."

---

## Mistake 3: Banging a Linear Variable

### The Problem
Trying to wrap a linear variable in bang.

### Wrong Code
```
λ(x :1 Nat). !x    -- ERROR: can't bang linear x
```

### Correct Understanding
Bang can only be applied when the result uses no linear variables:
```
λ(x :ω Nat). !x    -- OK: x is unrestricted
!5                  -- OK: no variables at all
```

### Why?
If you could bang a linear variable, you could use it unrestrictedly, violating linearity.

### How to Remember
> "Bang only works on unrestricted things."

---

## Mistake 4: Forgetting to Use Both Pair Components

### The Problem
Not using all components when destructuring a linear pair.

### Wrong Code
```
let (x, y) = p in x    -- ERROR: y not used
```

### Correct Code
```
let (x, y) = p in (x, y)   -- OK: both used
let (x, _) = p in x        -- Only OK if _ means "discard unrestricted"
```

### Why?
Both components of a linear pair are themselves linear.

### How to Remember
> "Linear pairs: use ALL the pieces."

---

## Mistake 5: Confusing Linear and Unrestricted Functions

### The Problem
Thinking `-o` and `->` are interchangeable.

### The Difference
- `A -o B`: Uses argument exactly once
- `A -> B`: May use argument any number of times

### Wrong Thinking
```
f : A -o B
g : A -> B

-- They're NOT the same!
```

### Example
```
dup : Nat -o Nat * Nat  -- IMPOSSIBLE
dup : Nat -> Nat * Nat  -- OK: λx. (x, x)
```

### How to Remember
> "-o = one use. -> = any uses."

---

## Mistake 6: Wrong Context Splitting

### The Problem
Using a linear variable in multiple subterms.

### Wrong Code
```
λ(x :1 Nat). (x, x)    -- x can't go to both sides
```

### Correct Understanding
In `(t₁, t₂)`, each linear variable goes to exactly one side:
```
λ(x :1 Nat). λ(y :1 Nat). (x, y)  -- x left, y right: OK
```

### How to Remember
> "Linear variables can't be in two places at once."

---

## Mistake 7: Misunderstanding Bang Elimination

### The Problem
Thinking `let !x = e in t` makes e unrestricted.

### Correct Understanding
It unwraps an already-banged value:
```
let !x = !5 in (x, x)     -- OK: !5 has type !Nat
let !x = 5 in (x, x)      -- ERROR: 5 has type Nat, not !Nat
```

### Why?
The `let !x = e` expects e to have type `!A`, not `A`.

### How to Remember
> "Bang elimination unwraps. Bang must already be there."

---

## Mistake 8: Not Threading Linear State

### The Problem
Losing track of a linear resource through a computation.

### Wrong Code
```
let h = open "file" in
let data = read h in        -- h consumed, but...
close h                      -- ERROR: h already used!
```

### Correct Code
```
let h = open "file" in
let (data, h') = read h in  -- read returns NEW handle
close h'                     -- close the new handle
```

### Pattern
Linear resources return "updated" versions of themselves.

### How to Remember
> "Thread the resource through. Each use returns the next version."

---

## Mistake 9: Forgetting Multiplicities in Higher-Order Functions

### The Problem
Getting function multiplicities wrong in higher-order code.

### Wrong Code
```
apply : (A -o B) -> A -o B
apply f x = f x            -- ERROR: f might be used again

apply : (A -o B) -o A -o B
apply f x = f x            -- OK: f used exactly once
```

### Why?
If `f : A -o B` is passed unrestrictedly, someone might call it multiple times.

### How to Remember
> "Match multiplicities all the way through."

---

## Mistake 10: Thinking Affine = Linear

### The Problem
Confusing "at most once" with "exactly once."

### The Difference
- **Linear**: Exactly once (can't discard, can't duplicate)
- **Affine**: At most once (can discard, can't duplicate)
- **Relevant**: At least once (can duplicate, can't discard)
- **Unrestricted**: Any number of times

### This Chapter
We implement linear types. Some systems (like Rust) are closer to affine.

### How to Remember
> "Linear = exactly once. Affine = at most once."

---

## Debugging Checklist

When linear type checking fails:

1. **Count uses**: Is each linear variable used exactly once?
2. **Check splitting**: Are linear variables split correctly in pairs/applications?
3. **Check bang**: Are you trying to bang something linear?
4. **Check destruction**: When destructuring, are all components used?
5. **Check threading**: Are linear resources threaded through?

---

## Practice Problems

### Problem 1: Find the Error

```
swap : (A * B) -o (B * A)
swap = λp. let (x, y) = p in (x, x)
```

<details>
<summary>Answer</summary>

Error: `x` used twice, `y` not used.

Fix:
```
swap = λp. let (x, y) = p in (y, x)
```
</details>

### Problem 2: Find the Error

```
dup : !Nat -o !Nat * !Nat
dup = λx. (!x, !x)
```

<details>
<summary>Answer</summary>

Error: `x` has type `!Nat`, but we're trying to use it twice (once in each `!x`).

Fix:
```
dup = λx. let !n = x in (!n, !n)
```

Unwrap first, then n is unrestricted and can be banged multiple times.
</details>

### Problem 3: Why Is This Wrong?

```
const : A -o B -> A
const = λx. λy. x
```

<details>
<summary>Answer</summary>

y is unrestricted (`B ->`), so we can ignore it.
x is linear (`A -o`), and we use it once.

Actually this IS correct! The return type is `A`, and we return `x`.

The ERROR would be:
```
const : A -> B -o A
const = λx. λy. x  -- y linear but unused!
```
</details>
