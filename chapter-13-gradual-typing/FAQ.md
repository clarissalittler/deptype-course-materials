# Chapter 13: Gradual Typing - Frequently Asked Questions

## Conceptual Questions

### Q: What is gradual typing?

**A:** Gradual typing is a type system that allows mixing statically-typed and dynamically-typed code in the same program. It introduces:

- **Dynamic type (?)**: Represents values of unknown type
- **Consistency (~)**: Replaces equality for type checking
- **Casts**: Runtime checks for type safety
- **Blame**: Tracks error sources

This enables incremental migration from dynamic to static typing.

### Q: Why not just use union types?

**A:** Union types and gradual typing serve different purposes:

**Union types**:
```
x : Int | String    -- x is either Int or String
```
Must handle both cases explicitly.

**Dynamic type**:
```
x : ?               -- x is unknown, will check at runtime
```
Accepts anything, checks when used.

Gradual typing is for interop and migration, not type alternatives.

### Q: How is this different from TypeScript's `any`?

**A:** TypeScript's `any` is similar but weaker:

| Feature | Our `?` | TypeScript `any` |
|---------|---------|------------------|
| Runtime checks | Yes (casts) | No |
| Blame tracking | Yes | No |
| Gradual guarantee | Yes | No |
| Type safety | Preserved | Bypassed |

TypeScript's `any` opts out of type checking entirely. Our `?` maintains safety with runtime checks.

### Q: What is the consistency relation?

**A:** Consistency (~) is like type equality but with a "wildcard":

```
T ~ T          -- Types consistent with themselves
? ~ T          -- Dynamic consistent with anything
T ~ ?          -- Anything consistent with dynamic
```

Key property: **NOT transitive**!
- Nat ~ ? ✓
- ? ~ Bool ✓
- Nat ~ Bool ✗

### Q: Why isn't consistency transitive?

**A:** If consistency were transitive:
```
Nat ~ ? ~ Bool ~ ? ~ String ~ ...
∴ Nat ~ Bool ~ String ~ ...  -- Everything consistent!
```

This would make gradual typing useless. Non-transitivity preserves type distinctions while allowing ? as a bridge.

## Technical Questions

### Q: What is a cast?

**A:** A cast `<T₁ => T₂>^l t` is a runtime type check:

- Source type: T₁
- Target type: T₂
- Blame label: l (for error tracking)
- Term: t

Casts are inserted where types are consistent but not equal.

### Q: When are casts inserted?

**A:** At type consistency boundaries:

```
f : ? -> Nat
f 5
```

Becomes:
```
f (<Nat => ?>^arg 5)
```

The argument 5 (Nat) is cast to ? because f expects ?.

### Q: What are ground types?

**A:** Ground types are the runtime type tags:

- **Base types**: Bool, Nat, Unit, etc.
- **Function ground**: ? -> ? (one tag for all functions)

When casting to ?, values are tagged with their ground type. When casting from ?, the tag is checked.

### Q: Why is there only one function ground type?

**A:** Efficiency and simplicity:

- Only need to distinguish "is a function" vs "is not"
- Function type details checked when function is applied
- Reduces number of runtime tags

### Q: How does blame work?

**A:** Blame tracks who's responsible for type errors:

```
(<Bool => Nat>^l true)  →  blame^l : Nat
```

The label `l` identifies the source location. Blame theorem: well-typed code can't be blamed.

### Q: What's positive vs negative blame?

**A:**
- **Positive**: Caller provided wrong value
- **Negative**: Function returned wrong value or misused input

In function casts:
```
<A -> B => C -> D>^l f = λx. <B => D>^l (f (<C => A>^l̄ x))
```
- Result: positive blame (l)
- Argument: negative blame (l̄, opposite)

### Q: What is the gradual guarantee?

**A:** Two properties well-designed gradual systems should satisfy:

**Static gradual guarantee**: If program P type checks, and P' is P with more precise types, P' also type checks.

**Dynamic gradual guarantee**: If P evaluates to v, and P' is P with more precise types, P' evaluates to v or a more precise blame error.

### Q: How do I migrate code gradually?

**A:** Strategy:

1. Start with all `?` types
2. Add types to public APIs first
3. Add types to critical paths
4. Fill in remaining code
5. Eventually eliminate all `?`

Each step preserves correctness (gradual guarantee).

## Common Confusions

### Q: Does `?` mean "any type" or "no type"?

**A:** Neither exactly. `?` means "unknown type":
- It's consistent with any type
- Runtime checks ensure safety
- It represents dynamic/untyped values

### Q: Can I cast between any types?

**A:** Only consistent types:
```
<Nat => ?>   ✓  -- Nat ~ ?
<? => Bool>  ✓  -- ? ~ Bool
<Nat => Bool> ✗ -- Nat ≁ Bool
```

### Q: What if a cast fails?

**A:** The program produces blame:
```
<? => Nat> (<Bool => ?> true)
→ blame^l : Nat
```

Blame indicates a runtime type error with the source location.

### Q: Is gradual typing slower?

**A:** Potentially, due to:
- Runtime checks from casts
- Space overhead for tags
- Optimization challenges

But:
- Fully typed code has no overhead
- Casts can sometimes be optimized away
- Trade-off for flexibility

### Q: Can I mix gradual and static type checking?

**A:** Yes! That's the point:
- Typed modules interact with untyped
- Each module can have its own precision level
- The system ensures safety at boundaries

## Troubleshooting

### Q: "Types not consistent" error

**A:** Check the types actually are consistent:
- Nat ~ Bool? No!
- (Nat -> Bool) ~ (Int -> String)? No!
- T ~ ? and ? ~ T? Always yes.

### Q: "Blame" at runtime

**A:** A cast failed. Check:
1. What's the blame label pointing to?
2. What value was cast?
3. What type was expected?

Fix by adding more precise types or handling the case.

### Q: "Ground type mismatch"

**A:** Projecting to wrong type:
```
<? => Nat> (<Bool => ?> true)  -- Bool tag, expected Nat
```

The value's tag doesn't match the target ground type.

### Q: Performance issues

**A:** Reduce casts:
1. Add more types (fewer boundaries)
2. Use space-efficient cast representations
3. Optimize repeated casts

### Q: How do I debug blame?

**A:** Trace execution:
1. Find the blamed label's source location
2. Check what value was there
3. Check what type was expected
4. Either fix the value or adjust types
