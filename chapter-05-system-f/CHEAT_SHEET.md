# Chapter 5: System F (Polymorphic Lambda Calculus) - Cheat Sheet

## Key Idea

**Explicit polymorphism**: Types are first-class, can abstract over them.

## Syntax

```
τ ::= α | τ → τ | ∀α. τ    (types)
t ::= x | λx:τ. t | t t    (terms)
    | Λα. t                (type abstraction)
    | t [τ]                (type application)
```

## Typing Rules

### Type Abstraction
```
Γ, α ⊢ t : τ
──────────────  (T-TAbs)
Γ ⊢ Λα. t : ∀α. τ
```

### Type Application
```
Γ ⊢ t : ∀α. τ
───────────────────  (T-TApp)
Γ ⊢ t [τ'] : [α ↦ τ']τ
```

## Evaluation

```
(Λα. t) [τ] → [α ↦ τ]t    (Type β-reduction)
```

## Common Patterns

### Polymorphic Identity
```
id = Λα. λx:α. x : ∀α. α → α
id [Nat] 5 → 5
id [Bool] true → true
```

### Church Encodings

#### Option Type
```
Option α = ∀R. R → (α → R) → R

none = Λα. ΛR. λn:R. λs:α→R. n
some = Λα. λx:α. ΛR. λn:R. λs:α→R. s x
```

#### Either Type
```
Either α β = ∀R. (α → R) → (β → R) → R

left  = Λα. Λβ. λx:α. ΛR. λl:α→R. λr:β→R. l x
right = Λα. Λβ. λy:β. ΛR. λl:α→R. λr:β→R. r y
```

#### Church Numerals
```
CNat = ∀α. (α → α) → α → α

zero = Λα. λs:α→α. λz:α. z
succ = λn:CNat. Λα. λs:α→α. λz:α. s (n [α] s z)
```

## Parametricity

**Free Theorems from Types:**

```
f : ∀α. α → α
⇒ f MUST be identity (only choice!)

f : ∀α. List α → List α
⇒ f can only rearrange/duplicate/drop
   (cannot inspect/modify elements)

f : ∀α β. (α → β) → List α → List β
⇒ f must be map-like
```

## Existential Types (Encoded)

```
∃α. τ  ≡  ∀R. (∀α. τ → R) → R

pack   = Λα. λx:τ. ΛR. λf:(∀α. τ→R). f [α] x
unpack = λpkg:(∃α. τ). ΛR. λf:(∀α. τ→R). pkg [R] f
```

### Abstract Data Type Example
```
Counter = ∃State. (State × (State → State) × (State → Nat))

makeCounter = pack [Nat] (0, succ, id)
```

## Impredicativity

**Can quantify over ALL types, including polymorphic ones:**

```
id : ∀α. α → α
id [∀β. β → β] id : ∀β. β → β   ✓ Self-application works!
```

## Remember

### ✓ Do
- Write type abstractions: `Λα. t`
- Write type applications: `t [τ]`
- Use parametricity to reason about code
- Church-encode data types

### ✗ Avoid
- Forgetting type applications
- Expecting type inference (undecidable!)
- Breaking parametricity

## Comparison

| Feature | HM | System F |
|---------|-----|----------|
| **Type inference** | ✓ Automatic | ✗ Undecidable |
| **Polymorphism** | Let-bound only | Everywhere |
| **Rank** | Rank-1 (prenex) | Rank-∞ (impredicative) |
| **Expressiveness** | Medium | High |
| **Annotations** | Optional | Required |

## Real-World Influence

| System F Feature | Modern Language |
|------------------|-----------------|
| Type abstraction | Generics in Java/C#/TypeScript |
| Type application | Type parameters |
| Parametricity | Generic constraints |
| Church encoding | Visitor pattern |
| Existentials | Abstract types, interfaces |

## Limitations

1. **No type inference** - Must annotate everything
2. **No recursive types** - Need μ-types extension
3. **No type operators** - Need System F-omega (Ch 6)
4. **No dependent types** - Need dependent types (Ch 7-8)

## Quick Reference

### Example: Polymorphic Twice
```
twice = Λα. λf:α→α. λx:α. f (f x)
      : ∀α. (α → α) → α → α

twice [Nat] succ 0 → 2
```

### Example: Self-Application
```
polyId = Λα. λx:α. x
selfApp = polyId [∀β. β → β] polyId
        : ∀β. β → β
```

## Debugging Tips

1. **Check type abstractions** - `Λα` before `λx`
2. **Check type applications** - Explicit `[τ]`
3. **Use parametricity** - Type restricts what's possible
4. **Draw derivation trees** - Visualize typing

## Further Reading

- Girard (1972): Original System F paper
- Reynolds (1974): Polymorphic lambda calculus
- Wadler (1989): "Theorems for free!"

## Next Steps

→ **Chapter 6**: System F-omega (higher-kinded types)
→ **Chapter 7**: Dependent types (types depend on values!)
