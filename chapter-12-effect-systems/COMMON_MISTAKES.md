# Chapter 12: Effect Systems - Common Mistakes

This guide covers frequent errors when learning algebraic effect systems.

---

## Mistake 1: Forgetting Effects Propagate

### The Problem
Assuming a function is pure when it calls effectful code.

### Wrong Thinking
```
wrapper : Unit -> Nat ! {}        -- Claims pure!
wrapper = λ_. perform State.get ()  -- But uses State!
```

### Correct Understanding
Effects propagate through function calls:
```
wrapper : Unit -> Nat ! {State}   -- Must declare State effect
wrapper = λ_. perform State.get ()
```

### How to Remember
> "Effects bubble up. If you call effectful code, you're effectful."

---

## Mistake 2: Confusing Lambda Creation with Application

### The Problem
Thinking creating a lambda has effects.

### Wrong Thinking
```
makeGetter : Unit -> (Unit -> Nat ! {State}) ! {State}  -- Wrong!
makeGetter = λ_. λ_. perform State.get ()
```

### Correct Understanding
Creating a lambda is PURE; effects happen when called:
```
makeGetter : Unit -> (Unit -> Nat ! {State}) ! {}  -- Creating lambda is pure
makeGetter = λ_. λ_. perform State.get ()
```

### How to Remember
> "Building a function doesn't run it. Effects wait until called."

---

## Mistake 3: Not Calling the Continuation

### The Problem
Forgetting to call `k` when you want computation to continue.

### Wrong Code
```
handle (perform State.get () + 1) with {
  State:
  return x -> x
  get () k -> 0    -- Forgot to call k!
}
-- Result: 0 (not 1!)
```

### Correct Code
```
handle (perform State.get () + 1) with {
  State:
  return x -> x
  get () k -> k 0   -- Call k with the state value
}
-- Result: 1
```

### How to Remember
> "k is 'the rest of the computation'. Call it to continue!"

---

## Mistake 4: Wrong Handler Result Type

### The Problem
Handler return clause type doesn't match operation clauses.

### Wrong Code
```
handle computation with {
  State:
  return x -> x              -- Returns x (same type)
  get () k -> (k 0, "log")   -- Returns pair! Wrong!
}
```

### Correct Understanding
All clauses must produce the same result type:
```
handle computation with {
  State:
  return x -> (x, "done")      -- Returns pair
  get () k -> let (r, s) = k 0 in (r, s)  -- Also pair
}
```

### How to Remember
> "All handler clauses converge to same type."

---

## Mistake 5: Forgetting Effect Removal

### The Problem
Not realizing handlers remove effects from the type.

### Wrong Expectation
```
handle (perform State.get ()) with stateHandler
-- Type: Nat ! {State}  -- Wrong!
```

### Correct Understanding
```
handle (perform State.get ()) with stateHandler
-- Type: Nat ! {}  -- State is handled, so removed!
```

### The Rule
`handle t ! {E | ρ} with h` gives result with effect `ρ` (E removed).

### How to Remember
> "Handlers consume their effect. It disappears from the type."

---

## Mistake 6: Misusing Row Variables

### The Problem
Confusing row variables with concrete effects.

### Wrong Code
```
f : ∀ρ. (Unit -> Nat ! ρ) -> Nat ! ρ
f g = handle (g ()) with stateHandler  -- Wrong! Can't handle ρ
```

### Why Wrong?
`ρ` could be ANY effect row. You can't assume it contains State.

### Correct Approaches
```
-- Require State specifically
f : ∀ρ. (Unit -> Nat ! {State | ρ}) -> Nat ! ρ
f g = handle (g ()) with stateHandler  -- OK: State is there

-- Or don't handle
f : ∀ρ. (Unit -> Nat ! ρ) -> Nat ! ρ
f g = g ()  -- Just call it, no handling
```

### How to Remember
> "Row variables are abstract. Handle concrete effects only."

---

## Mistake 7: Effect Row Order Matters (Not!)

### The Problem
Thinking effect order in rows matters.

### Wrong Thinking
```
{State, IO} ≠ {IO, State}  -- Wrong!
```

### Correct Understanding
Effect rows are SETS, not ordered:
```
{State, IO} = {IO, State}  -- Same!
```

### How to Remember
> "Effect rows are sets. Order doesn't matter."

---

## Mistake 8: Handling Effects in Wrong Scope

### The Problem
Trying to handle effects in a context that doesn't have them.

### Wrong Code
```
pure : Unit -> Nat ! {}
pure = λ_.
  handle (5) with {
    State:
    return x -> x
    get () k -> k 0
  }
```

### Why Wrong?
The expression `5` has no State effect. Handler is pointless.

### When Handlers Help
```
effectful : Unit -> Nat ! {State}
effectful = λ_. perform State.get ()

safe : Unit -> Nat ! {}
safe = λ_. handle (effectful ()) with stateHandler
```

### How to Remember
> "Handlers intercept effects. No effect = nothing to intercept."

---

## Mistake 9: Calling Continuation with Wrong Type

### The Problem
Passing wrong type to continuation.

### Wrong Code
```
handle (perform State.get () : Nat) with {
  State:
  get () k -> k "hello"  -- k expects Nat, not String!
}
```

### Correct Code
```
handle (perform State.get () : Nat) with {
  State:
  get () k -> k 42       -- Nat value
}
```

### How to Remember
> "Continuation expects the operation's return type."

---

## Mistake 10: Forgetting Deep Handler Semantics

### The Problem
Not realizing effects in continuation are also handled.

### Example
```
handle (perform State.get (); perform State.get ()) with {
  State:
  return x -> x
  get () k -> k 1
}
```

### What Happens?
1. First `get ()` handled, k called with 1
2. Second `get ()` ALSO handled (deep handler)
3. Both get value 1

### Shallow Alternative
```
-- Shallow handler would only handle first occurrence
-- Would need explicit re-handling for second
```

### How to Remember
> "Deep handlers handle ALL occurrences. Effects in k are handled too."

---

## Debugging Checklist

When effect type checking fails:

1. **Check effect annotations**: Does function type include all effects?
2. **Check lambda vs call**: Is the effect in creation or application?
3. **Check handler coverage**: Does handler handle the right effect?
4. **Check continuation calls**: Are you calling k with correct type?
5. **Check row variables**: Are you assuming concrete effects for ρ?

---

## Practice Problems

### Problem 1: Find the Effect Error

```
pure : Unit -> Nat ! {}
pure = λ_. perform IO.print 5; 42
```

<details>
<summary>Answer</summary>

Effect mismatch! Function claims `! {}` but uses IO.

Fix:
```
effectful : Unit -> Nat ! {IO}
effectful = λ_. perform IO.print 5; 42
```
</details>

### Problem 2: Fix the Handler

```
handle (perform Exception.throw ()) with {
  Exception:
  return x -> x
  throw () k -> k 0
}
```

What's wrong? What will happen?

<details>
<summary>Answer</summary>

Calling `k 0` continues the computation. After `throw`, there's typically no meaningful continuation or wrong type.

For exception, usually DON'T call k:
```
handle (perform Exception.throw (); 42) with {
  Exception:
  return x -> x
  throw () k -> 0   -- Return default, don't continue
}
```
</details>

### Problem 3: Why No Effect Removal?

```
f : (Unit -> Nat ! {State}) -> Nat ! {State}
f g = handle (g ()) with stateHandler
```

Why does result still have `{State}`?

<details>
<summary>Answer</summary>

If `stateHandler` properly handles State, result should be:
```
f : (Unit -> Nat ! {State}) -> Nat ! {}
```

If result still shows `{State}`, either:
1. Handler doesn't fully handle State
2. Handler itself uses State
3. Type annotation is wrong

Check handler definition!
</details>
