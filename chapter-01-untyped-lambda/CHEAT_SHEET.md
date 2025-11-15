# Chapter 1: Untyped Lambda Calculus - Cheat Sheet

## Syntax (3 constructs only!)

```
t ::=                  (terms)
    x                  variable
    λx. t              abstraction (function)
    t t                application
```

## Key Concepts

### Free Variables (FV)
```
FV(x) = {x}
FV(λx. t) = FV(t) \ {x}
FV(t₁ t₂) = FV(t₁) ∪ FV(t₂)
```

### Substitution [x ↦ s]t
```
[x ↦ s]x = s
[x ↦ s]y = y                    (if x ≠ y)
[x ↦ s](λx. t) = λx. t          (x is shadowed)
[x ↦ s](λy. t) = λy. [x ↦ s]t   (if y ∉ FV(s))
[x ↦ s](t₁ t₂) = ([x ↦ s]t₁) ([x ↦ s]t₂)
```

## Core Reduction Rule

**β-reduction**: `(λx. t) s → [x ↦ s]t`

## Evaluation Strategies

| Strategy | Description | Used In |
|----------|-------------|---------|
| **Normal Order** | Leftmost-outermost redex first | Complete (finds normal form if exists) |
| **Call-by-Name** | Like normal order, don't reduce under λ | Haskell (lazy) |
| **Call-by-Value** | Reduce arguments before applying | Most languages (strict) |

### Small-Step Semantics (Call-by-Value)

```
t₁ → t₁'
───────────────  (E-App1)
t₁ t₂ → t₁' t₂

t₂ → t₂'
───────────────  (E-App2)
v₁ t₂ → v₁ t₂'

(λx. t) v → [x ↦ v]t  (E-AppAbs)
```

## Church Encodings

### Booleans
```
true  = λt. λf. t
false = λt. λf. f
if    = λp. λt. λf. p t f
and   = λp. λq. p q false
or    = λp. λq. p true q
not   = λp. p false true
```

### Natural Numbers (Church Numerals)
```
0    = λf. λx. x
1    = λf. λx. f x
2    = λf. λx. f (f x)
succ = λn. λf. λx. f (n f x)
plus = λm. λn. λf. λx. m f (n f x)
mult = λm. λn. λf. m (n f)
```

### Pairs
```
pair = λx. λy. λf. f x y
fst  = λp. p (λx. λy. x)
snd  = λp. p (λx. λy. y)
```

### Lists
```
nil  = λc. λn. n
cons = λh. λt. λc. λn. c h (t c n)
```

## Famous Combinators

```
I = λx. x                          Identity
K = λx. λy. x                      Constant
S = λx. λy. λz. x z (y z)         Substitution
ω = λx. x x                        Self-application
Ω = ω ω = (λx. x x) (λx. x x)     Infinite loop
```

## Fixed-Point Combinator (Y)

```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

**Property**: `Y f → f (Y f)` (unrolls recursion)

**Example** (factorial):
```
fact = Y (λf. λn. if (iszero n) 1 (mult n (f (pred n))))
```

## Common Idioms

| Pattern | Lambda Term | Type (if typed) |
|---------|-------------|-----------------|
| Identity | `λx. x` | `α → α` |
| Constant | `λx. λy. x` | `α → β → α` |
| Apply | `λf. λx. f x` | `(α → β) → α → β` |
| Compose | `λf. λg. λx. f (g x)` | `(β → γ) → (α → β) → α → γ` |
| Flip | `λf. λx. λy. f y x` | `(α → β → γ) → β → α → γ` |
| Twice | `λf. λx. f (f x)` | `(α → α) → α → α` |

## Evaluation Examples

### Example 1: Simple Application
```
(λx. x) y
→ [x ↦ y]x
→ y
```

### Example 2: Curried Function
```
(λx. λy. x) a b
→ (λy. a) b
→ a
```

### Example 3: Church Numeral Addition
```
plus 1 2
= (λm. λn. λf. λx. m f (n f x)) (λf. λx. f x) (λf. λx. f (f x))
→ λf. λx. (λf. λx. f x) f ((λf. λx. f (f x)) f x)
→ λf. λx. f ((λf. λx. f (f x)) f x)
→ λf. λx. f (f (f x))
= 3
```

## Remember

### ✓ Do
- α-rename to avoid variable capture
- Use parentheses for clarity: `(λx. x x) (λx. x x)`
- Normal order finds normal form if it exists
- Church encodings can represent any data

### ✗ Avoid
- Variable capture: `[y ↦ x](λx. y)` ≠ `λx. x` (capture!)
  - Correct: α-rename first → `[y ↦ x](λz. y)` = `λz. x`
- Assuming termination: `Ω = (λx. x x) (λx. x x)` loops forever
- Confusing bound and free variables

## Quick Reference

### Precedence
1. Application (left-associative): `x y z` = `(x y) z`
2. Abstraction (right-associative): `λx. λy. t` = `λx. (λy. t)`
3. Application binds tighter: `λx. x y` = `λx. (x y)` ≠ `(λx. x) y`

### α-equivalence
```
λx. x ≡ λy. y         (α-equivalent)
λx. x ≢ λx. y         (different behavior)
```

### β-normal form
A term with no β-redexes (no more reductions possible).

### η-conversion
```
λx. f x ≡ f           (if x ∉ FV(f))
```

## Connection to Programming

| Lambda Calculus | JavaScript | Python | Haskell |
|-----------------|------------|--------|---------|
| `λx. x` | `x => x` | `lambda x: x` | `\x -> x` |
| `(λx. x) y` | `(x => x)(y)` | `(lambda x: x)(y)` | `(\x -> x) y` |
| `λx. λy. x + y` | `x => y => x + y` | `lambda x: lambda y: x + y` | `\x y -> x + y` |

## Debugging Tips

1. **Trace reduction steps**: Write out each β-reduction
2. **Check for capture**: Ensure substitution doesn't capture variables
3. **Identify strategy**: Know if you're using call-by-name or call-by-value
4. **Look for patterns**: Many bugs are from wrong evaluation order

## Further Reading

- **Pierce, TAPL**: Chapter 5 (clear introduction)
- **Barendregt**: The definitive reference (advanced)
- **Online**: https://en.wikipedia.org/wiki/Lambda_calculus

## Next Steps

→ **Chapter 2**: Add types to prevent infinite loops and ensure termination
