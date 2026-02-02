# Chapter 8: Full Dependent Types - Cheat Sheet

## Key Idea

**Complete foundation for mathematics and verified programming** with universe hierarchy, equality types, and inductive families.

## Universe Hierarchy

```
Type 0 : Type 1 : Type 2 : Type 3 : ...

Prevents Russell's paradox (no Type : Type)
```

### Cumulativity
```
Type i ⊆ Type (i+1)

If t : Type i, then t : Type (i+1)
```

## Syntax

```
t ::= x | λx:t. t | t t
    | Π(x:t). t | Σ(x:t). t
    | Type i                    (universe levels)
    | Eq t t t                  (equality type)
    | refl t                    (reflexivity)
    | J t t t t t t            (J eliminator)
    | inductive types...
```

## Equality Types

### Propositional Equality
```
Eq : Π(A:Type). A → A → Type

refl : Π(A:Type). Π(x:A). Eq A x x
```

### J Eliminator (Equality Induction)
```
J : Π(A:Type).
    Π(x:A).
    Π(P : Π(y:A). Eq A x y → Type).
    P x (refl A x) →
    Π(y:A). Π(e : Eq A x y). P y e

J A x P prefl x (refl A x) → prefl
```

### Derived Equality Operations
```
-- Symmetry
sym : Π(A:Type). Π(x y:A). Eq A x y → Eq A y x

-- Transitivity  
trans : Π(A:Type). Π(x y z:A). Eq A x y → Eq A y z → Eq A x z

-- Congruence
cong : Π(A B:Type). Π(f:A→B). Π(x y:A). Eq A x y → Eq B (f x) (f y)
```

## Inductive Families

### Natural Numbers
```
data Nat : Type 0 where
  zero : Nat
  succ : Nat → Nat

natElim : Π(P : Nat → Type 0).
          P zero →
          (Π(n:Nat). P n → P (succ n)) →
          Π(n:Nat). P n
```

### Vectors (Length-Indexed Lists)
```
data Vec (A : Type 0) : Nat → Type 0 where
  nil  : Vec A zero
  cons : Π(n:Nat). A → Vec A n → Vec A (succ n)

vecElim : Π(A : Type 0).
          Π(P : Π(n:Nat). Vec A n → Type 0).
          P zero nil →
          (Π(n:Nat). Π(x:A). Π(xs:Vec A n). P n xs → P (succ n) (cons n x xs)) →
          Π(n:Nat). Π(v:Vec A n). P n v
```

### Finite Sets
```
data Fin : Nat → Type 0 where
  fzero : Π(n:Nat). Fin (succ n)
  fsucc : Π(n:Nat). Fin n → Fin (succ n)

-- Safe indexing
index : Π(A:Type 0). Π(n:Nat). Vec A n → Fin n → A
```

## Common Proofs

### Addition Commutativity
```
+-comm : Π(m n : Nat). Eq Nat (m + n) (n + m)
+-comm = natElim
  (λm. Π(n:Nat). Eq Nat (m + n) (n + m))
  (λn. +-zero-r n)
  (λm ih n. +-succ-r m n ; cong succ (ih n))
```

### Vector Append Associativity
```
++-assoc : Π(A:Type 0). Π(l m n:Nat).
           Π(xs:Vec A l). Π(ys:Vec A m). Π(zs:Vec A n).
           Eq (Vec A (l + (m + n)))
              ((xs ++ ys) ++ zs)
              (xs ++ (ys ++ zs))
```

## Curry-Howard Correspondence

| Logic | Type Theory |
|-------|-------------|
| Proposition P | Type τ |
| Proof of P | Term t : τ |
| True | Unit type |
| False | Empty type |
| P ∧ Q | Σ(x:P). Q |
| P ∨ Q | Sum type P + Q |
| P → Q | Π(x:P). Q |
| ¬P | P → Empty |
| ∀x. P(x) | Π(x:A). P x |
| ∃x. P(x) | Σ(x:A). P x |

## Real-World Systems

### Coq
```coq
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n; simpl; auto.
  intros. rewrite IHn. rewrite <- plus_n_Sm. auto.
Qed.
```

### Agda
```agda
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identity n)
+-comm (suc m) n = 
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + suc m
  ∎
```

### Lean
```lean
theorem add_comm (m n : ℕ) : m + n = n + m :=
nat.rec_on n
  (show m + 0 = 0 + m, from add_zero_right m ▸ add_zero_left m)
  (λ n ih, show m + succ n = succ n + m, from
    calc m + succ n = succ (m + n) : add_succ m n
                ... = succ (n + m) : ih ▸ rfl
                ... = succ n + m   : add_succ_left n m)
```

## Remember

### ✓ Do
- Use universe levels to avoid paradoxes
- Encode invariants in inductive families
- Prove properties with J eliminator
- Write terminating functions only

### ✗ Avoid
- Type : Type (Russell's paradox!)
- Non-terminating recursion
- Axiom K (inconsistent with HoTT)

## Practical Applications

| Application | Language | Achievement |
|-------------|----------|-------------|
| CompCert | Coq | Verified C compiler (no bugs in 10+ years) |
| seL4 | Isabelle | Verified microkernel |
| Fiat-Crypto | Coq | Verified crypto (Curve25519, etc.) |
| HACL* | F* | Verified crypto in Firefox |
| mathlib | Lean | Formal mathematics library |

## Type-Level Programming

### Safe Array Access
```
get : Π(A:Type 0). Π(n:Nat). Vec A n → Fin n → A
```

### Matrix Operations
```
Matrix : Nat → Nat → Type 0 → Type 0

matMult : Π(m n p:Nat). Π(A:Type 0).
          Matrix m n A → Matrix n p A → Matrix m p A
```

## Quick Reference

### Universe Levels
- **Type 0**: Regular types (Nat, Bool, Vec 5 Nat)
- **Type 1**: Types of types (Type 0, Nat → Type 0)
- **Type 2**: Types of Type 1, etc.

### Key Eliminators
- **natElim**: Induction on natural numbers
- **vecElim**: Induction on vectors
- **J**: Induction on equality

### Common Patterns
- Use Π for dependent functions
- Use Σ for dependent pairs
- Use Eq for proofs
- Use inductive families for indexed types

## Why This Matters

1. **Verified Software**: Prove programs correct
2. **Mathematics**: Digital proof libraries
3. **Security**: Cryptography with proofs
4. **Safety**: Autonomous vehicles (seL4)
5. **Education**: Learn rigorous reasoning

## Next Steps

- Study Coq, Agda, or Lean
- Read "Software Foundations"
- Try formalizing simple proofs
- Explore Homotopy Type Theory
