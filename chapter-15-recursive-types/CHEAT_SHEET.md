# Chapter 15: Recursive Types (μ Types) - Cheat Sheet

## Syntax

```
T ::=                          (types)
    μα. T                      recursive type (mu)
    α                          type variable
    T₁ → T₂                    function type
    T₁ × T₂                    product type
    T₁ + T₂                    sum type
    Unit | Nat | Bool          base types

t ::=                          (terms)
    fold [μα.T] t              wrap into recursive type
    unfold [μα.T] t            unwrap from recursive type
    inl t | inr t              sum constructors
    <t₁, t₂>                   pair
    case t of ...              sum elimination
    fst t | snd t              product elimination
```

## Key Concepts

### Recursive Type Definition

```
μα. T    -- Type α where T can refer to α
```

The bound variable α refers to the entire recursive type.

### Type Substitution

```
T[μα.T/α]  -- Replace α with μα.T in T
```

Example:
```
NatList = μα. Unit + (Nat × α)
T[μα.T/α] = Unit + (Nat × NatList)
```

## Core Operations

### Fold (Introduction)

```
   Γ ⊢ t : T[μα.T/α]
─────────────────────────── (T-Fold)
 Γ ⊢ fold [μα.T] t : μα.T
```

**Purpose**: Wrap an unfolded value into the recursive type.

### Unfold (Elimination)

```
      Γ ⊢ t : μα.T
───────────────────────────── (T-Unfold)
 Γ ⊢ unfold [μα.T] t : T[μα.T/α]
```

**Purpose**: Unwrap a recursive value to examine it.

## Iso-Recursive Semantics

| Aspect | Description |
|--------|-------------|
| **Key Insight** | `μα.T ≅ T[μα.T/α]` (isomorphic, NOT equal) |
| **Fold** | Witnesses: `T[μα.T/α] → μα.T` |
| **Unfold** | Witnesses: `μα.T → T[μα.T/α]` |
| **Evaluation** | `unfold (fold v) → v` |

## Common Data Structures

### Lists

```
NatList = μα. Unit + (Nat × α)
--            ^^^^   ^^^^^^^^^
--            empty  element + rest

-- Constructors
nil  = fold [NatList] (inl unit)
cons = λn:Nat. λl:NatList. fold [NatList] (inr <n, l>)

-- Destructors
isEmpty = λl:NatList.
  case unfold [NatList] l of
    inl _ => true
  | inr _ => false

head = λl:NatList.
  case unfold [NatList] l of
    inl _ => 0  -- error case
  | inr p => fst p

tail = λl:NatList.
  case unfold [NatList] l of
    inl _ => nil
  | inr p => snd p
```

### Binary Trees

```
Tree = μα. Nat + (α × α)
--         ^^^^  ^^^^^^^^
--         leaf  left × right

-- Constructors
leaf = λn:Nat. fold [Tree] (inl n)
branch = λl:Tree. λr:Tree. fold [Tree] (inr <l, r>)

-- Example tree
--     *
--    / \
--   1   2
branch (leaf 1) (leaf 2)
```

### Streams (Infinite)

```
Stream = μα. Nat × α
--           ^^^^^^^^
--           head × tail (no empty case!)

-- Operations
head = λs:Stream. fst (unfold [Stream] s)
tail = λs:Stream. snd (unfold [Stream] s)

-- Constructors (need general recursion)
ones = fold [Stream] <1, ones>
nats = λn:Nat. fold [Stream] <n, nats (succ n)>
```

## The Pattern

For any recursive structure:

1. **Define type**: `μα. F(α)` where F is a type operator
2. **Constructors**: Use `fold` with appropriate sum/product
3. **Destructors**: Use `unfold` then `case` or projection

## Self-Application

```
SelfApp = μα. α → Nat

omega : SelfApp → Nat
omega = λx:SelfApp. (unfold [SelfApp] x) x

-- Can type-check self-application!
fold [SelfApp] omega : SelfApp
```

## Comparison: Iso vs Equi-Recursive

| Aspect | Iso-recursive | Equi-recursive |
|--------|---------------|----------------|
| **Equality** | `μα.T ≠ T[μα.T/α]` | `μα.T = T[μα.T/α]` |
| **Operations** | Explicit fold/unfold | Implicit coercions |
| **Type Checking** | Simpler, syntax-directed | Requires coinduction |
| **Annotations** | Required | Can be inferred |
| **Languages** | OCaml, Haskell, Rust | Some ML variants |

## Common Patterns

### Pattern 1: Optional Recursion
```
-- Type variable unused = not really recursive
Maybe = μα. Unit + Nat
-- Equivalent to: Unit + Nat
```

### Pattern 2: Mutual Recursion Encoding
```
-- Must nest μ types
Expr = μα. Nat + α + (List α)
  where List β = μγ. Unit + (β × γ)
```

### Pattern 3: Nested Recursion
```
RoseTree = μα. Nat × (μβ. Unit + (α × β))
--                    ^^^^^^^^^^^^^^^^^^
--                    list of children
```

## Evaluation Rules

```
-- Fold of value is a value
isValue (fold [μα.T] v) = isValue v

-- Unfold/fold cancellation
unfold [μα.T] (fold [μα.T] v) → v   (if v is a value)

-- Congruence
  t → t'
──────────────────────────
fold [μα.T] t → fold [μα.T] t'

    t → t'
──────────────────────────
unfold [μα.T] t → unfold [μα.T] t'
```

## Remember

### Do
- Always `fold` when creating recursive values
- Always `unfold` before pattern matching
- Include type annotation in fold/unfold: `[μα.T]`
- Think of μ as a type-level fixed point

### Avoid
- Forgetting fold (wrong type!)
- Forgetting unfold (can't match!)
- Confusing iso and equi semantics
- Non-positive occurrences of α (can cause paradoxes)

## Fixed Points and Recursion

### The Connection
```
μα. F(α)  is the least fixed point of F
```

Where F is a type operator, μα.F(α) satisfies:
```
μα.F(α) ≅ F(μα.F(α))
```

### Enables General Recursion
```
fix : (T → T) → T
fix = λf. (λx. f (unfold x x)) (fold (λx. f (unfold x x)))
```

### Consequence
Recursive types break strong normalization:
```
loop = omega (fold omega)  -- Diverges!
```

## Practical Examples

### List Length
```
length : NatList → Nat
length = λl.
  case unfold [NatList] l of
    inl _ => 0
  | inr p => succ (length (snd p))
```

### Tree Sum
```
sum : Tree → Nat
sum = λt.
  case unfold [Tree] t of
    inl n => n
  | inr p => sum (fst p) + sum (snd p)
```

### Stream Take
```
take : Nat → Stream → NatList
take = λn. λs.
  if iszero n
    then nil
    else cons (head s) (take (pred n) (tail s))
```

## Quick Reference

### Type Definition
```
Name = μα. Body    -- α refers to Name in Body
```

### Creating Values
```
fold [Name] (construct using Body)
```

### Examining Values
```
case unfold [Name] value of ...
```

### Positive Occurrences
α should appear only in:
- Right of arrows: `T → α` ✓
- Products: `T × α` ✓
- Sums: `T + α` ✓

Avoid:
- Left of arrows: `α → T` ✗ (negative position)

## Debugging Tips

1. **Type mismatch on constructor**: Did you forget `fold`?
2. **Can't pattern match**: Did you forget `unfold`?
3. **Wrong type annotation**: Use `μα.T`, not `T[μα.T/α]`
4. **Infinite loop**: Recursive types enable non-termination

## Further Reading

- **Pierce, TAPL Chapter 20**: Iso and equi-recursive types
- **Amadio & Cardelli (1993)**: Subtyping recursive types
- **Connection**: μ types ↔ least fixed points ↔ inductive types

## Next Steps

- **Chapter 16 (HoTT)**: Higher inductive types generalize μ
- **Advanced**: Sized types, coinductive types, equi-recursive algorithms
