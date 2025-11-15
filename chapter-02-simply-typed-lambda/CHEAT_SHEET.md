# Chapter 2: Simply Typed Lambda Calculus - Cheat Sheet

## Syntax

```
τ ::=                  (types)
    Bool               boolean type
    Nat                natural number type
    τ → τ              function type

t ::=                  (terms)
    x                  variable
    λx:τ. t            abstraction with type annotation
    t t                application
    true | false       boolean constants
    if t then t else t conditional
    0 | succ t | pred t | iszero t    natural numbers
```

## Typing Rules

### Variables
```
x:τ ∈ Γ
─────────  (T-Var)
Γ ⊢ x : τ
```

### Abstraction
```
Γ, x:τ₁ ⊢ t : τ₂
──────────────────  (T-Abs)
Γ ⊢ λx:τ₁. t : τ₁ → τ₂
```

### Application
```
Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : τ₁
────────────────────────────────  (T-App)
Γ ⊢ t₁ t₂ : τ₂
```

### Booleans
```
─────────────────  (T-True)    ─────────────────  (T-False)
Γ ⊢ true : Bool                 Γ ⊢ false : Bool

Γ ⊢ t₁ : Bool    Γ ⊢ t₂ : τ    Γ ⊢ t₃ : τ
───────────────────────────────────────────  (T-If)
Γ ⊢ if t₁ then t₂ else t₃ : τ
```

### Natural Numbers
```
────────────  (T-Zero)
Γ ⊢ 0 : Nat

Γ ⊢ t : Nat
─────────────────  (T-Succ)
Γ ⊢ succ t : Nat

Γ ⊢ t : Nat
─────────────────  (T-Pred)
Γ ⊢ pred t : Nat

Γ ⊢ t : Nat
──────────────────────  (T-IsZero)
Γ ⊢ iszero t : Bool
```

## Evaluation Rules (Call-by-Value)

### Application
```
t₁ → t₁'
───────────────  (E-App1)
t₁ t₂ → t₁' t₂

t₂ → t₂'
───────────────  (E-App2)
v₁ t₂ → v₁ t₂'

(λx:τ. t) v → [x ↦ v]t  (E-AppAbs)
```

### Conditionals
```
t₁ → t₁'
──────────────────────────────────────  (E-If)
if t₁ then t₂ else t₃ → if t₁' then t₂ else t₃

if true then t₂ else t₃ → t₂   (E-IfTrue)
if false then t₂ else t₃ → t₃  (E-IfFalse)
```

### Natural Numbers
```
t → t'
────────────────  (E-Succ)
succ t → succ t'

pred 0 → 0         (E-PredZero)
pred (succ nv) → nv  (E-PredSucc)

iszero 0 → true            (E-IsZeroZero)
iszero (succ nv) → false   (E-IsZeroSucc)
```

## Type Safety Theorems

### Progress
**If** `⊢ t : τ` **then either**:
1. `t` is a value, **or**
2. ∃ `t'` such that `t → t'`

**Meaning**: Well-typed programs don't get stuck.

### Preservation (Subject Reduction)
**If** `Γ ⊢ t : τ` **and** `t → t'` **then** `Γ ⊢ t' : τ`

**Meaning**: Types are preserved during evaluation.

### Type Safety = Progress + Preservation
Well-typed programs **cannot** go wrong!

## Common Idioms

| Pattern | Term | Type |
|---------|------|------|
| Identity | `λx:τ. x` | `τ → τ` |
| Constant | `λx:τ₁. λy:τ₂. x` | `τ₁ → τ₂ → τ₁` |
| Apply | `λf:τ₁→τ₂. λx:τ₁. f x` | `(τ₁ → τ₂) → τ₁ → τ₂` |
| Compose | `λf:τ₂→τ₃. λg:τ₁→τ₂. λx:τ₁. f (g x)` | `(τ₂→τ₃)→(τ₁→τ₂)→τ₁→τ₃` |
| Self-app | `λx:τ→τ. x x` | `(τ → τ) → τ` |

## Example Type Derivations

### Example 1: Identity Function
```
x:Nat ∈ (x:Nat)
─────────────────  (T-Var)
x:Nat ⊢ x : Nat
────────────────────────  (T-Abs)
∅ ⊢ λx:Nat. x : Nat → Nat
```

### Example 2: Constant Function
```
                   x:Bool ∈ (x:Bool, y:Nat)
                   ─────────────────────────  (T-Var)
                   x:Bool, y:Nat ⊢ x : Bool
        ───────────────────────────────────────────  (T-Abs)
        x:Bool ⊢ λy:Nat. x : Nat → Bool
────────────────────────────────────────────────────  (T-Abs)
∅ ⊢ λx:Bool. λy:Nat. x : Bool → Nat → Bool
```

## Comparison with Untyped Lambda Calculus

| Feature | Untyped λ | STLC |
|---------|-----------|------|
| **Type annotations** | No | Yes (required) |
| **Type errors** | Runtime | Compile-time |
| **Termination** | May loop | Always terminates |
| **Expressiveness** | More (Turing-complete) | Less (not Turing-complete) |
| **Safety** | No guarantees | Type safety |
| **Omega** `(λx. x x)(λx. x x)` | ✓ Types | ✗ Type error |
| **Y combinator** | ✓ Works | ✗ Doesn't type-check |

## Remember

### ✓ Do
- Write type annotations on all lambdas: `λx:τ. t`
- Check that function arguments match expected types
- Use type derivation trees to debug type errors
- Remember: all STLC programs terminate (strong normalization)

### ✗ Avoid
- Forgetting type annotations: `λx. x` is **not** valid STLC
- Type mismatches: `(λx:Bool. x) 0` doesn't type-check
- Self-application: `λx:τ. x x` cannot type-check (would need τ = τ → τ₂)
- General recursion: Y combinator doesn't type-check

## Common Type Errors

```
// Error 1: Argument type mismatch
(λx:Nat. succ x) true
✗ Expected Nat, got Bool

// Error 2: Condition must be Bool
if 0 then true else false
✗ Expected Bool, got Nat

// Error 3: Self-application impossible
λx:τ. x x
✗ Cannot unify τ with τ → τ₂ (would be infinite type)

// Error 4: Wrong return type
if true then 0 else false
✗ Branches have different types (Nat vs Bool)
```

## Encoding Data (Without Extensions)

### Booleans (Already Built-in)
```
true  : Bool
false : Bool
if t then t else t : τ
```

### Natural Numbers (Already Built-in)
```
0 : Nat
succ t : Nat
pred t : Nat
iszero t : Bool
```

### Church Booleans (Alternative Encoding)
```
tru  = λt:τ. λf:τ. t       : τ → τ → τ
fls  = λt:τ. λf:τ. f       : τ → τ → τ
test = λl:τ→τ→τ. λm:τ. λn:τ. l m n : (τ→τ→τ) → τ → τ → τ
```

Note: Church encoding in STLC is less elegant than in untyped lambda calculus due to type annotations.

## Metatheory Summary

| Property | STLC | Proof Technique |
|----------|------|-----------------|
| **Type Safety** | ✓ | Progress + Preservation |
| **Decidable Type Checking** | ✓ | Algorithm (syntax-directed) |
| **Strong Normalization** | ✓ | Reducibility method |
| **Confluence** | ✓ | Same as untyped λ-calculus |
| **Uniqueness of Types** | ✓ | Induction on typing derivation |

## Connection to Real Languages

| STLC Concept | TypeScript | Java | Rust |
|--------------|------------|------|------|
| `λx:Nat. x` | `(x: number) => x` | `(Integer x) -> x` | `\|x: i32\| x` |
| `τ₁ → τ₂` | `(x: T1) => T2` | `Function<T1, T2>` | `Fn(T1) -> T2` |
| Type error at compile time | ✓ | ✓ | ✓ |
| Strong normalization | ✗ (has loops) | ✗ (has loops) | ✗ (has loops) |
| Type inference | Partial | No | Yes |

## Quick Reference: Type Checking Algorithm

```haskell
typeOf :: Context -> Term -> Either TypeError Type
typeOf ctx (Var x) = case lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left $ "Variable " ++ x ++ " not in scope"

typeOf ctx (Abs x ty t) =
    case typeOf (extend ctx x ty) t of
        Right ty2 -> Right (TyArr ty ty2)
        Left err -> Left err

typeOf ctx (App t1 t2) =
    case (typeOf ctx t1, typeOf ctx t2) of
        (Right (TyArr ty11 ty12), Right ty2) ->
            if ty11 == ty2
            then Right ty12
            else Left "Argument type mismatch"
        (Right ty, _) -> Left "Expected function type"
        (Left err, _) -> Left err
```

## Extensions (See EXTENSIONS.md)

Want more expressiveness? Add:
1. **Product types** (pairs): `τ₁ × τ₂`
2. **Sum types** (unions): `τ₁ + τ₂`
3. **Let bindings**: `let x = t₁ in t₂` (syntactic sugar)
4. **Fix operator**: `fix : (τ → τ) → τ` (enables recursion)
5. **Records**: `{x: τ₁, y: τ₂}`
6. **Variants**: `<left: τ₁, right: τ₂>`

See `exercises/EXTENSIONS.md` for step-by-step implementation guides!

## Debugging Type Errors

1. **Draw the type derivation tree** - Start from leaves (variables)
2. **Check each rule application** - Ensure premises match
3. **Identify the failing rule** - Where does the tree break?
4. **Fix the term** - Adjust to satisfy the rule

## Further Reading

- **Pierce, TAPL**: Chapter 9 (canonical reference)
- **Harper, PFPL**: Chapter 10 (alternative presentation)
- **Online**: Software Foundations Vol 2 (Coq formalization)

## Next Steps

→ **Chapter 3**: Add algebraic data types (products, sums, records, variants, lists)
→ **Chapter 4**: Add type inference (remove annotations!)
→ **Chapter 5**: Add polymorphism (generics)
