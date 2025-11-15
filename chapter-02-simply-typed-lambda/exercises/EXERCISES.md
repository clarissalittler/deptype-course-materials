# Chapter 2 Exercises: Simply Typed Lambda Calculus

## Exercise 1: Arithmetic Extensions (Easy)

### 1a. Multiplication
Extend the language with a `mult` operation for natural numbers.
- Add `TmMult :: Term -> Term -> Term` to the syntax
- Implement typing rules
- Implement evaluation semantics

### 1b. Less Than
Add a comparison operation `lt : Nat → Nat → Bool`.

### 1c. Equality
Add `eq : Nat → Nat → Bool` for testing equality of natural numbers.

## Exercise 2: Product Types (Medium)

Add product types (pairs) to STLC:

### 2a. Syntax
- Type: `TyProd :: Type -> Type -> Type` for `τ₁ × τ₂`
- Terms:
  - `TmPair :: Term -> Term -> Term` for `⟨t₁, t₂⟩`
  - `TmFst :: Term -> Term` for `fst t`
  - `TmSnd :: Term -> Term` for `snd t`

### 2b. Typing Rules
```
Γ ⊢ t₁ : τ₁    Γ ⊢ t₂ : τ₂
────────────────────────────── (T-Pair)
Γ ⊢ ⟨t₁, t₂⟩ : τ₁ × τ₂

Γ ⊢ t : τ₁ × τ₂
─────────────── (T-Fst)
Γ ⊢ fst t : τ₁

Γ ⊢ t : τ₁ × τ₂
─────────────── (T-Snd)
Γ ⊢ snd t : τ₂
```

### 2c. Evaluation
```
fst ⟨v₁, v₂⟩ → v₁
snd ⟨v₁, v₂⟩ → v₂
```

## Exercise 3: Sum Types (Medium)

Add sum types (disjoint unions):

### 3a. Syntax
- Type: `TySum :: Type -> Type -> Type` for `τ₁ + τ₂`
- Terms:
  - `TmInl :: Type -> Term -> Term` for `inl[τ] t`
  - `TmInr :: Type -> Term -> Term` for `inr[τ] t`
  - `TmCase :: Term -> Var -> Term -> Var -> Term -> Term` for `case t of inl x => t₁ | inr y => t₂`

### 3b. Typing and Evaluation
Implement full typing rules and evaluation for sum types.

## Exercise 4: Let Bindings (Medium)

Add let-bindings as syntactic sugar:

```
let x = t₁ in t₂  ≡  (λx:τ. t₂) t₁
```

where τ is the type of t₁.

## Exercise 5: Fixed Point Combinator (Hard)

Add a typed fixed-point combinator:

### 5a. Syntax
```
fix : (τ → τ) → τ
```

### 5b. Typing Rule
```
Γ ⊢ t : τ → τ
───────────── (T-Fix)
Γ ⊢ fix t : τ
```

### 5c. Evaluation
```
fix v → v (fix v)
```

### 5d. Factorial
Implement factorial using fix:
```
factorial = fix (λf:Nat→Nat. λn:Nat.
  if iszero n then 1 else mult n (f (pred n)))
```

## Exercise 6: Type Safety Proof (Hard)

### 6a. Progress
Prove that if `⊢ t : τ` then either:
- t is a value, or
- there exists t' such that t → t'

Implement a function that demonstrates this:
```haskell
progress :: Term -> Either Value Step
```

### 6b. Preservation
Prove that if `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`.

Implement:
```haskell
preservation :: Term -> Type -> Term -> Bool
```

## Solutions

Solutions are provided in `Solutions.hs`. Tests are in `test/ExerciseSpec.hs`.

## Testing

```bash
stack test --test-arguments "--match Exercises"
```

## Learning Objectives

- Understand how to extend type systems systematically
- Practice implementing typing rules and evaluation semantics
- Learn about type safety (progress and preservation)
- Work with product and sum types
- Understand recursion in typed settings
