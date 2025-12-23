# Chapter 14: Row Types & Extensible Records - Frequently Asked Questions

## Conceptual Questions

### Q: What are row types?

**A:** Row types are type-level mappings from labels to types, possibly with a "tail" variable representing unknown additional fields.

```
()                -- Empty row
(x: Nat | ())     -- Row with just x
(x: Nat | ρ)      -- Row with x plus unknown ρ
```

Row types enable:
- Extensible records: `{name: String | ρ}`
- Polymorphic variants: `<ok: Nat | ρ>`
- Row polymorphic functions: `∀ρ. {x: Nat | ρ} -> Nat`

### Q: What is row polymorphism?

**A:** Row polymorphism is the ability to abstract over unknown record fields using row variables.

```
-- Works with ANY record having at least name field
getName : ∀ρ. {name: String | ρ} -> String
getName r = r.name

getName {name = "Alice"}               -- OK
getName {name = "Bob", age = 30}       -- OK
getName {name = "Carol", id = 42, active = true}  -- OK
```

### Q: How is this different from structural subtyping?

**A:** Both enable similar functionality but through different mechanisms:

| Aspect | Row Polymorphism | Structural Subtyping |
|--------|------------------|---------------------|
| Mechanism | ∀ρ abstraction | <: relation |
| Inference | Full Hindley-Milner | Limited |
| Expressiveness | Row variables | Width subtyping |
| Example | `∀ρ. {x: A | ρ}` | `{x: A, y: B} <: {x: A}` |

Row polymorphism has better inference properties!

### Q: What's the relationship to duck typing?

**A:** Row polymorphism is "static duck typing":

**Duck typing** (Python, JS):
```python
def get_name(obj):
    return obj.name  # Works if obj has name, fails at runtime otherwise
```

**Row polymorphism**:
```
getName : ∀ρ. {name: String | ρ} -> String
```
Same flexibility, but checked at compile time!

### Q: What are polymorphic variants?

**A:** Polymorphic variants are the dual of extensible records—open sum types:

```
<ok: Nat | error: String | ρ>  -- At least these cases, maybe more
```

While records say "has at least these fields," variants say "is at least one of these cases."

## Technical Questions

### Q: What are the three record operations?

**A:**

1. **Projection** (access field):
   ```
   r.l : T    where r : {l: T | ρ}
   ```

2. **Extension** (add field):
   ```
   {l = t | r} : {l: T | ρ}    where l ∉ ρ
   ```

3. **Restriction** (remove field):
   ```
   r \ l : {ρ}    where r : {l: T | ρ}
   ```

### Q: How do I update a field?

**A:** Combine restriction and extension:

```
updateName : ∀ρ. String -> {name: String | ρ} -> {name: String | ρ}
updateName newName r = {name = newName | r \ name}
```

Steps:
1. Remove old `name`: `r \ name`
2. Add new `name`: `{name = newName | ...}`

### Q: What are lack constraints?

**A:** Lack constraints ensure a label is NOT in a row:

```
addField : ∀ρ. (x ∉ ρ) => T -> {ρ} -> {x: T | ρ}
```

The constraint `x ∉ ρ` prevents adding a duplicate field.

### Q: How does row unification work?

**A:** Row unification has special rules:

1. **Order doesn't matter**:
   ```
   {x: A, y: B} unifies with {y: B, x: A}
   ```

2. **Labels can be found anywhere**:
   ```
   {x: A | α} ~ {x: A, y: B}
   -- Solves: α = (y: B)
   ```

3. **Rows can reorder to match**:
   ```
   {x: A | α} ~ {y: B | β}
   -- Solves: α = (y: B | γ), β = (x: A | γ)
   ```

### Q: Can I have duplicate labels?

**A:** In standard row types, no. Each label appears at most once.

Some systems add "scoped labels" for controlled duplication:
```
{x: Nat | x: Bool | ρ}  -- Scoped: outer x shadows inner
```

### Q: How are variants handled?

**A:** Use case analysis with patterns:

```
handleResult : ∀ρ. <ok: A | error: String | ρ> -> B
handleResult v = case v of
  <ok = a> -> ...
  <error = s> -> ...
  <other = x> -> ...  -- Catch remaining cases
```

## Common Confusions

### Q: Is `{x: Nat}` the same as `{x: Nat | ()}`?

**A:** Yes, semantically. `()` is the empty row, so `{x: Nat | ()}` means "x and nothing else."

### Q: Does field order matter?

**A:** No! Rows are like sets/maps:
```
{x: Nat, y: Bool} = {y: Bool, x: Nat}
```

### Q: Can I access fields in ρ?

**A:** No, ρ is abstract. You can only access explicitly named fields:
```
f : ∀ρ. {x: Nat | ρ} -> Nat
f r = r.x   -- OK
f r = r.y   -- ERROR: y might not exist
```

### Q: What's the difference between row and record?

**A:**
- **Row**: Type-level sequence of label-type pairs `(x: Nat | ρ)`
- **Record**: Value-level mapping from labels to values `{x = 5}`
- **Record type**: Row wrapped in braces `{x: Nat | ρ}`

## Troubleshooting

### Q: "Label already in row" error

**A:** You're extending with an existing field:
```
{x = 5 | {x = 3}}  -- Error: x exists
```

Fix: Use restriction first:
```
{x = 5 | {x = 3} \ x}  -- OK
```

### Q: "Cannot unify rows" error

**A:** Row variables might be incompatible:
```
f : ∀ρ. {x: Nat | ρ} -> {y: Bool | ρ}
-- ρ would need to contain both x (input) and y (output)!
```

Check that row constraints are satisfiable.

### Q: Function loses fields

**A:** Check return type preserves ρ:
```
-- BAD: returns closed record
f : ∀ρ. {x: Nat | ρ} -> {x: Nat}

-- GOOD: preserves ρ
f : ∀ρ. {x: Nat | ρ} -> {x: Nat | ρ}
```

### Q: Variant pattern incomplete

**A:** Open variants need catch-all:
```
-- Error: doesn't handle ρ cases
case v of <ok = n> -> n

-- OK: handles remaining
case v of
  <ok = n> -> n
  <other = _> -> 0
```

### Q: Which languages support row types?

**A:**
- **PureScript**: Full row polymorphism for records and effects
- **Elm**: Extensible records (limited—no restriction)
- **OCaml**: Polymorphic variants (special syntax)
- **Koka**: Row-based effects
- **Links**: Row types for web programming
- **Ur/Web**: Advanced row types
