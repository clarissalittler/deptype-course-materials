# Chapter 15: Recursive Types (μ Types) - Frequently Asked Questions

## Conceptual Questions

### Q: What are recursive types?

**A:** Recursive types allow type definitions to refer to themselves. Using the μ (mu) binder:

```
μα. T
```

Where α is bound in T and refers to the whole type.

Example:
```
NatList = μα. Unit + (Nat × α)
-- α represents NatList itself
```

### Q: Why do we need recursive types?

**A:** Many data structures are inherently self-referential:

- **Lists**: Empty, or element + more list
- **Trees**: Leaf, or branches containing subtrees
- **Streams**: Element + more stream (forever)

Without recursive types, we can't express these in a typed language.

### Q: What does μ mean?

**A:** μ (mu) is the "least fixed point" operator. `μα. T` is the smallest type satisfying:

```
α ≅ T[α]
```

Intuitively, if you keep "unrolling" the definition, you get the type.

### Q: What's the difference between iso-recursive and equi-recursive?

**A:**

**Iso-recursive** (our approach):
- `μα.T` ≅ `T[μα.T/α]` (isomorphic but not equal)
- Need explicit `fold` and `unfold`
- Simpler type checking

**Equi-recursive**:
- `μα.T` = `T[μα.T/α]` (actually equal)
- Implicit coercions
- Requires coinductive type equality

### Q: Why use iso-recursive over equi-recursive?

**A:** Trade-offs:

| Aspect | Iso-recursive | Equi-recursive |
|--------|---------------|----------------|
| Type checking | Simpler | Complex |
| Annotations | More | Fewer |
| Decidability | Clear | Subtle |
| Real languages | OCaml, Rust | Some MLs |

Most practical languages use iso-recursive.

## Technical Questions

### Q: What does fold do?

**A:** `fold` wraps a value of the unfolded type into the recursive type:

```
fold : T[μα.T/α] → μα.T

fold [NatList] (inl unit)
-- Takes: Unit + (Nat × NatList)
-- Returns: NatList
```

### Q: What does unfold do?

**A:** `unfold` unwraps a recursive type to expose its structure:

```
unfold : μα.T → T[μα.T/α]

unfold [NatList] myList
-- Takes: NatList
-- Returns: Unit + (Nat × NatList)
```

### Q: What is T[μα.T/α]?

**A:** Type substitution. Replace every occurrence of α in T with the full μ type.

Example:
```
T = Unit + (Nat × α)
μα.T = μα. Unit + (Nat × α)

T[μα.T/α] = Unit + (Nat × μα. Unit + (Nat × α))
```

### Q: How do fold and unfold interact?

**A:** They're inverses:
```
unfold (fold v) → v
fold (unfold v) → v   (up to normalization)
```

This reflects the isomorphism between μα.T and T[μα.T/α].

### Q: Why must I annotate fold and unfold with types?

**A:** The same inner structure could belong to different μ types:

```
fold [μα. Unit + α] (inl unit)        -- Type A
fold [μβ. Unit + β] (inl unit)        -- Type B (different!)
```

The annotation specifies which recursive type we mean.

### Q: Can I pattern match directly on recursive types?

**A:** No, you must unfold first:

```
-- Wrong:
case myList of ...

-- Right:
case unfold [NatList] myList of
  inl _ => ...      -- Empty case
  inr p => ...      -- Cons case
```

### Q: How do I handle streams (infinite data)?

**A:** Streams need general recursion:

```
Stream = μα. Nat × α    -- No Unit+ means no empty case!

ones = fix (λself. fold [Stream] <1, self>)
```

Access with unfold:
```
head s = fst (unfold [Stream] s)
tail s = snd (unfold [Stream] s)
```

### Q: Can recursive types cause non-termination?

**A:** Yes! Recursive types enable self-application:

```
SelfApp = μα. α → Nat
omega = λx:SelfApp. (unfold x) x
loop = omega (fold omega)   -- Loops forever!
```

This breaks strong normalization.

## Common Confusions

### Q: Is Maybe recursive?

**A:** No! `Maybe A = Unit + A` has no self-reference.

```
Maybe Nat = Unit + Nat    -- Not recursive
List Nat = μα. Unit + (Nat × α)    -- Recursive (α appears)
```

### Q: Is μα.Nat the same as Nat?

**A:** Yes, effectively. α doesn't appear in the body, so:
```
μα. Nat = Nat
```

But this is unusual usage of μ.

### Q: What are positive occurrences?

**A:** Occurrences of α in "covariant" positions:
- Right side of →
- Inside products (×)
- Inside sums (+)

Negative occurrence (left of →) can cause problems:
```
μα. α → Nat    -- α is negative here
```

### Q: How do I encode mutual recursion?

**A:** Use products or sums:

```
-- Even and Odd
EvenOdd = μα. (Nat × α) × (Nat × α)
--        ^-Even-^   ^-Odd-^

Even = fst
Odd = snd
```

Or use sum types to combine.

## Troubleshooting

### Q: "Type mismatch: expected μα.T, got T'"

**A:** Probably missing fold. Check:
```
-- Wrong:
inl unit

-- Right:
fold [μα...] (inl unit)
```

### Q: "Cannot pattern match on μ type"

**A:** Add unfold:
```
-- Wrong:
case l of inl _ => ...

-- Right:
case unfold [NatList] l of inl _ => ...
```

### Q: "Infinite loop in type checking"

**A:** Might have non-positive occurrence or complex equi-recursive structure. Check:
1. Is α only in positive positions?
2. Is the definition well-founded?

### Q: "Cannot infer type for fold"

**A:** Add explicit annotation:
```
fold [μα. Unit + (Nat × α)] (inl unit)
```

### Q: My recursive function doesn't terminate

**A:** Recursive types enable non-termination. Check:
1. Is recursion structurally decreasing?
2. Are you using fix appropriately?
3. Is the structure finite (lists) or infinite (streams)?
