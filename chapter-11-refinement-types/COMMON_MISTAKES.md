# Chapter 11: Refinement Types - Common Mistakes

This guide covers frequent errors when learning refinement types.

---

## Mistake 1: Reversing Subtyping Direction

### The Problem
Thinking more general is a subtype of more specific.

### Wrong Thinking
```
{x: Nat | x > 0} <: {x: Nat | x > 10}   -- WRONG!
```

### Correct Understanding
More specific (stronger predicate) is the subtype:
```
{x: Nat | x > 10} <: {x: Nat | x > 0}   -- Correct
```

**Intuition**: Values satisfying the stronger constraint also satisfy the weaker one.

### How to Remember
> "Stronger predicate = fewer values = subtype"

---

## Mistake 2: Confusing Implication Direction

### The Problem
Getting the implication backwards when checking subtyping.

### Wrong Check
```
{x: Nat | x > 0} <: {x: Nat | x > 10}
Check: (x > 10) ⟹ (x > 0)   -- Checking wrong direction!
```

### Correct Check
```
{x: Nat | φ} <: {x: Nat | ψ}
Check: φ(x) ⟹ ψ(x)          -- φ implies ψ, not reverse
```

### Example
```
{x: Nat | x > 10} <: {x: Nat | x > 0}
Check: (x > 10) ⟹ (x > 0)   -- True! ✓
```

### How to Remember
> "Subtype's predicate implies supertype's predicate"

---

## Mistake 3: Forgetting Path Conditions

### The Problem
Not using information from conditionals.

### Wrong Analysis
```
λx : Nat. if iszero x then 0 else pred x
-- "pred x is unsafe!" -- Wrong!
```

### Correct Analysis
```
λx : Nat. if iszero x then 0 else pred x
-- In else: x != 0, so x > 0
-- pred on positive is safe! ✓
```

### Why?
Path sensitivity means we know the condition is false in else branch.

### How to Remember
> "Branches give you information. Use it!"

---

## Mistake 4: Thinking Refinements Are Runtime Checks

### The Problem
Believing refinement types add runtime overhead.

### Wrong Thinking
```
{x: Nat | x > 0}
-- "This checks x > 0 at runtime"
```

### Correct Understanding
Refinement checks are STATIC (compile-time):
- Type checker verifies predicates
- No runtime overhead
- Errors caught before running

### Exception
Some systems (hybrid type checking) use runtime checks as fallback.

### How to Remember
> "Refinements = static verification, not dynamic checks"

---

## Mistake 5: Expecting Full Decidability

### The Problem
Thinking all predicate implications can be automatically checked.

### Wrong Expectation
```
-- "The type checker will prove this automatically"
{x: Nat | isPrime x && x > 1000000} <: {x: Nat | x > 0}
```

### Reality
- Simple arithmetic: Usually decidable (SMT solvers)
- Complex predicates: May be undecidable
- Our simple checker: Very limited

### How to Remember
> "Predicate validity can be hard. Keep predicates simple."

---

## Mistake 6: Forgetting Variable Scope in Predicates

### The Problem
Using variables not in scope in predicates.

### Wrong Code
```
λx : Nat. let y = x + 1 in
  (x : {z: Nat | z < y})   -- y not in scope for refinement!
```

### Correct Understanding
Predicates can only mention:
- The bound variable (x in `{x: T | ...}`)
- Variables in the current scope
- Constants

### How to Remember
> "Predicates follow normal scoping rules"

---

## Mistake 7: Confusing Dependent and Simple Function Types

### The Problem
Not realizing when function types are dependent.

### Non-Dependent
```
Nat -> Nat -> Nat          -- Result doesn't mention args
```

### Dependent
```
(n: Nat) -> Vec a n -> a   -- Result mentions n
(x: Nat) -> {y: Nat | y > x}  -- Result mentions x
```

### Why It Matters
Dependent types let you express relationships between inputs and outputs.

### How to Remember
> "If result type mentions argument name, it's dependent"

---

## Mistake 8: Ignoring Base Type Subtyping

### The Problem
Only checking predicate implication, not base types.

### Wrong Check
```
{x: Int | x > 0} <: {x: Nat | x > 0}
-- "Predicates are same, so subtype!" -- WRONG!
```

### Correct Check
```
{x: T₁ | φ} <: {x: T₂ | ψ}
Requires: T₁ <: T₂ AND φ ⟹ ψ
```

Int is not a subtype of Nat, so the check fails!

### How to Remember
> "Check both base type AND predicate"

---

## Mistake 9: Weakening When You Need Strengthening

### The Problem
Trying to produce a stronger type than you have evidence for.

### Wrong Code
```
weaken : {x: Nat | x > 0} -> {x: Nat | x > 100}
weaken x = x  -- Can't work!
```

### Why Wrong?
- Input: any positive number (1, 2, 3, ...)
- Output: must be > 100
- 5 is positive but NOT > 100

### Correct Direction
```
strengthen : {x: Nat | x > 100} -> {x: Nat | x > 0}
strengthen x = x  -- Works! x > 100 implies x > 0
```

### How to Remember
> "Can only weaken constraints, not strengthen"

---

## Mistake 10: Not Using Singleton Types

### The Problem
Missing opportunities to use exact value types.

### Less Precise
```
zero : {x: Nat | x >= 0}
zero = 0
```

### More Precise
```
zero : {x: Nat | x == 0}
zero = 0
```

### Why Better?
Singleton types give maximum information:
- `{x: Nat | x == 0}` has exactly one value
- Strongest possible refinement for a constant

### How to Remember
> "For constants, use equality refinements"

---

## Debugging Checklist

When refinement type checking fails:

1. **Check subtyping direction**: Is stronger <: weaker?
2. **Check implication**: Does φ really imply ψ?
3. **Check path conditions**: Are you in a branch that gives info?
4. **Check base types**: Are the underlying types compatible?
5. **Check scope**: Are all predicate variables in scope?

---

## Practice Problems

### Problem 1: Fix the Subtyping

What's wrong?
```
{x: Nat | x < 10} <: {x: Nat | x < 5}
```

<details>
<summary>Answer</summary>

The subtyping is WRONG because x < 10 does NOT imply x < 5.
Counter-example: x = 7 satisfies x < 10 but not x < 5.

Correct direction:
```
{x: Nat | x < 5} <: {x: Nat | x < 10}   -- ✓
```
</details>

### Problem 2: Use Path Sensitivity

Type this function:
```
safePred : Nat -> Nat
safePred x = if iszero x then 0 else pred x
```

<details>
<summary>Answer</summary>

The function is well-typed because:
- In then branch: x == 0, return 0 (safe)
- In else branch: x > 0, pred x is safe

Type: `Nat -> Nat`

Path sensitivity ensures pred is only called on positive x.
</details>

### Problem 3: Spot the Error

```
div : Nat -> Nat -> Nat
div n d = if d > 0 then n / d else 0
```

What's wrong with this "solution" for safe division?

<details>
<summary>Answer</summary>

This uses RUNTIME checking instead of type-level safety.
The caller can still pass 0 and get 0 back, hiding the error.

Better solution:
```
div : Nat -> {d: Nat | d > 0} -> Nat
div n d = n / d
```

Now the TYPE system prevents passing 0 - can't even call div with 0!
</details>
