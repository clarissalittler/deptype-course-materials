# Chapter 12: Effect Systems - Exercises

## Exercise 1: Understanding Effects

For each function type, describe what effects it may perform:

1. `Nat -> Bool`
2. `Nat -> Bool ! {State}`
3. `Nat -> Bool ! {State, Exception}`
4. `∀ρ. Nat -> Bool ! {State | ρ}`

## Exercise 2: Effect Operations

Write terms with the following types:

1. `Unit -> Nat ! {State}` (get the state)
2. `Nat -> Unit ! {State}` (set the state)
3. `Unit -> Unit ! {Exception}` (throw an exception)
4. `Unit -> Nat ! {State, IO}` (read from IO and get state)

## Exercise 3: Effect Rows

Determine if the first effect row is a subset of the second:

1. `{}` ⊆ `{State}`
2. `{State}` ⊆ `{State, IO}`
3. `{State, IO}` ⊆ `{State}`
4. `{State | ρ}` ⊆ `{State, IO | ρ}`
5. `{ρ}` ⊆ `{State | ρ}`

## Exercise 4: Simple Handlers

Write handlers for the following:

1. A handler for `State` that threads state through computation:
```
handler {
  State:
  return x -> λs. (x, s)
  get () k -> λs. k s s
  put s' k -> λs. k () s'
}
```

2. A handler for `Exception` that returns a default value:
```
handler {
  Exception:
  return x -> Just x
  throw () k -> Nothing
}
```

## Exercise 5: Effect Polymorphism

Explain the difference between these two types:

1. `∀ρ. (Unit -> Nat ! ρ) -> Nat ! ρ`
2. `(Unit -> Nat ! {State}) -> Nat ! {State}`

Why is effect polymorphism useful?

## Exercise 6: Implement Reader Effect

Add a Reader effect with operations:

```
Reader:
  ask : Unit -> A        -- Get the environment
  local : A -> Unit      -- Temporarily modify environment (simplified)
```

1. Define the effect in `TypeCheck.hs`
2. Implement a handler for Reader
3. Write tests

## Exercise 7: Implement Writer Effect

Add a Writer effect with operations:

```
Writer:
  tell : A -> Unit       -- Append to output
```

1. Define the effect
2. Implement a handler that collects all outputs
3. Write tests

## Exercise 8: Effect Inference

Currently, effects must be annotated. Design and implement basic effect inference:

1. Generate effect variables for unknown effects
2. Collect constraints during type checking
3. Solve constraints to find minimal effect annotations

## Exercise 9: Effect Subtyping

Implement effect subtyping:

- `T ! {}` should be usable where `T ! {E}` is expected (pure ≤ effectful)
- `T ! {E}` should be usable where `T ! {E, F}` is expected (subset)

Update the type checker to use subsumption.

## Exercise 10: Deep vs Shallow Handlers

Our handlers are "deep" - they handle all occurrences of an effect. Implement "shallow" handlers that only handle the first occurrence:

```
shallow_handle t with {
  E: return x -> ...
  op p k -> ...  -- k does NOT re-handle E
}
```

Compare the semantics and use cases.

## Challenge Exercises

### Challenge 1: Effect Masking

Implement effect masking to hide effects from callers:

```
mask E in t  -- Performs E internally but not visible in type
```

This requires proving that all E effects in t are handled internally.

### Challenge 2: Parameterized Effects

Extend effects to have type parameters:

```
State[S]:          -- State parameterized by state type S
  get : Unit -> S
  put : S -> Unit
```

This allows multiple independent state effects.

### Challenge 3: Effect Handlers as First-Class Values

Make handlers first-class values that can be passed around:

```
let h = handler { State: ... } in
let f = λx. handle x with h in
...
```

This requires representing handlers in the type system.

### Challenge 4: Efficient Compilation

Design a compilation strategy for effects:

1. CPS transformation for continuation-based semantics
2. Evidence passing for effects
3. Fusion optimizations for nested handlers

Implement a simple compiler that eliminates effect overhead for pure code.

## References

- Plotkin & Power, "Algebraic Operations and Generic Effects" (2003)
- Plotkin & Pretnar, "Handlers of Algebraic Effects" (2013)
- Leijen, "Type Directed Compilation of Row-typed Algebraic Effects" (2017)
- Hillerström & Lindley, "Liberating Effects with Rows and Handlers" (2016)
- Brachthäuser et al., "Effects as Capabilities" (2020)
- Dolan et al., "Effective Concurrency through Algebraic Effects" (2017)
