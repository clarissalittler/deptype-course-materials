# Chapter 19: Bidirectional Type Checking

## Overview

Bidirectional type checking is a technique that combines the benefits of type inference
with the simplicity of type checking. Instead of either fully inferring types (like
Hindley-Milner) or requiring complete annotations (like Church-style), bidirectional
typing uses two mutually recursive judgments to minimize annotations while maintaining
decidability.

The key insight: **introduction forms are checked, elimination forms are inferred**.

## The Two Judgments

```
Γ ⊢ e ⇒ A     "synthesize type A for e"    (inference/synthesis mode)
Γ ⊢ e ⇐ A     "check e against type A"     (checking/analysis mode)
```

### When to use each mode:

| Construct | Mode | Reason |
|-----------|------|--------|
| Variables | ⇒ | Look up in context |
| Application | ⇒ | Infer function, check argument |
| Annotated lambda | ⇒ | Annotation provides type |
| Annotation | ⇒ | Check against annotation, return it |
| Unannotated lambda | ⇐ | Need expected type for parameter |
| Pairs | ⇐ | Need expected product type |
| Injections (inl/inr) | ⇐ | Need expected sum type |
| Type abstraction | ⇐ | Need expected ∀ type |

## Core Rules

### Inference (⇒)

```
                  x : A ∈ Γ
Variables:        ─────────────
                  Γ ⊢ x ⇒ A

                  Γ, x:A ⊢ e ⇒ B
Annotated λ:      ──────────────────────
                  Γ ⊢ (λx:A. e) ⇒ A → B

                  Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
Application:      ─────────────────────────────────
                  Γ ⊢ e₁ e₂ ⇒ B

                  Γ ⊢ e ⇐ A
Annotation:       ─────────────────
                  Γ ⊢ (e : A) ⇒ A
```

### Checking (⇐)

```
                  Γ, x:A ⊢ e ⇐ B
Lambda:           ─────────────────────
                  Γ ⊢ (λx. e) ⇐ A → B

                  Γ ⊢ e₁ ⇐ A    Γ ⊢ e₂ ⇐ B
Pair:             ────────────────────────────
                  Γ ⊢ (e₁, e₂) ⇐ A × B

                  Γ ⊢ e ⇐ A
Inl:              ─────────────────
                  Γ ⊢ inl e ⇐ A + B

                  Γ ⊢ e ⇒ A    A = B
Subsumption:      ──────────────────────
                  Γ ⊢ e ⇐ B
```

## Implementation

### Type Checker Structure

```haskell
-- The two mutually recursive judgments
infer :: Ctx -> Term -> Either TypeError Type
check :: Ctx -> Term -> Type -> Either TypeError ()

-- Key insight: subsumption connects the modes
check ctx e expected = do
  inferred <- infer ctx e
  unless (inferred == expected) $
    throwError $ TypeMismatch expected inferred
```

### Syntax

```haskell
data Term
  = Var Name                    -- x
  | Lam Name Term               -- λx. e       (checked)
  | LamAnn Name Type Term       -- λ(x:A). e   (inferred)
  | App Term Term               -- e₁ e₂
  | Ann Term Type               -- (e : A)
  | Pair Term Term              -- (e₁, e₂)   (checked)
  | Fst Term | Snd Term         -- fst e, snd e
  | Inl Term | Inr Term         -- inl e, inr e (checked)
  | Case Term Name Term Name Term
  | TyLam Name Term             -- Λα. e      (checked)
  | TyApp Term Type             -- e [A]
  | ...

data Type
  = TyVar Name                  -- α
  | TyArr Type Type             -- A → B
  | TyForall Name Type          -- ∀α. A
  | TyProd Type Type            -- A × B
  | TySum Type Type             -- A + B
  | TyBool | TyNat | TyUnit
```

## File Structure

```
chapter-19-bidirectional-typing/
├── src/
│   ├── Syntax.hs       -- Terms, types, values
│   ├── TypeCheck.hs    -- Bidirectional type checker
│   ├── Eval.hs         -- Call-by-value evaluator
│   ├── Parser.hs       -- Megaparsec parser
│   └── Pretty.hs       -- Pretty printing
├── app/
│   └── Main.hs         -- Interactive REPL
├── test/
│   └── Spec.hs         -- Test suite
└── exercises/
    └── EXERCISES.md    -- Practice problems
```

## Building and Running

```bash
cd chapter-19-bidirectional-typing
stack build
stack test
stack exec bidir-repl
```

## REPL Examples

```
bidir> true
true ⇒ Bool
Value: true

bidir> \x. x
Cannot infer type for this term (try adding annotation)
Hint: Use annotation (term : Type) or :check command

bidir> \(x : Bool). x
λ(x : Bool). x ⇒ Bool → Bool
Value: <λx. ...>

bidir> (\x. x : Bool -> Bool)
(λx. x : Bool → Bool) ⇒ Bool → Bool
Value: <λx. ...>

bidir> :check \x. x : Bool -> Bool
✓ λx. x ⇐ Bool → Bool
Value: <λx. ...>

bidir> (\(x : Bool). x) true
(λ(x : Bool). x) true ⇒ Bool
Value: true
```

## Key Design Decisions

### 1. Mode Switching at Annotations

Annotations are the bridge between modes:
- In checking mode, an annotation lets us check and return a type
- In inference mode, we check against the annotation

### 2. Subsumption

The subsumption rule lets us fall back from checking to inference:
```haskell
check ctx e expected = do
  inferred <- infer ctx e
  unless (inferred == expected) $ throwError ...
```

This is tried last, after all introduction-form rules.

### 3. Local Type Inference

We only infer "locally" - annotations on lambda-bound variables suffice.
No global unification is needed, making the algorithm simple and predictable.

## Comparison with Other Approaches

| Approach | Annotations | Complexity | Decidable |
|----------|-------------|------------|-----------|
| Church-style | All terms | Simple | Yes |
| Curry-style (HM) | None | Complex (unification) | Yes |
| **Bidirectional** | **Minimal** | **Medium** | **Yes** |
| Dependent types | Varies | High | Often undecidable |

## Extensions

### Adding Subtyping

With subtyping, subsumption becomes:
```
Γ ⊢ e ⇒ A    A <: B
────────────────────
Γ ⊢ e ⇐ B
```

### Higher-Rank Polymorphism

Bidirectional typing extends elegantly to higher-rank types. The key insight
from Dunfield & Krishnaswami (2013):
- Synthesize monotypes
- Check polytypes

### Dependent Types

Bidirectional typing is essential for dependent types, where:
- Types can contain terms
- Type equality requires evaluation
- Mode annotations guide when to reduce

## Why Bidirectional?

1. **Minimal annotations**: Only where truly needed
2. **Predictable**: Clear rules for when inference succeeds
3. **Compositional**: Local checking, no global constraints
4. **Extensible**: Easy to add new constructs
5. **Good errors**: Mode indicates what was expected

## Common Patterns

### The "Annotation Trick"

When you can't infer, wrap in an annotation:
```
(\x. x)              -- Cannot infer
(\x. x : A -> A)     -- Now inferrable
```

### Checking Mode Propagation

Introduction forms propagate checking mode inward:
```
check (Pair e1 e2) (A × B) = check e1 A >> check e2 B
```

This lets nested structures work without internal annotations.

## References

1. **Pierce & Turner** - "Local Type Inference" (2000)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=14006122847956984404)
   - The foundational paper on bidirectional typing

2. **Dunfield & Krishnaswami** - "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" (2013)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=6aboringtype2312412)
   - Modern treatment with higher-rank types

3. **Dunfield & Pfenning** - "Tridirectional Typechecking" (2004)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=15953637488566932221)
   - Extension with intersection and union types

4. **Chlipala** - "Certified Programming with Dependent Types"
   - [Book](http://adam.chlipala.net/cpdt/)
   - Uses bidirectional for dependent types in Coq

5. **Davies & Pfenning** - "Intersection Types and Computational Effects" (2000)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=6706811715738374068)
   - Bidirectional with effects

6. **Abel et al.** - "Decidability of Conversion for Type Theory in Type Theory" (2017)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=10916766549901962574)
   - Bidirectional for dependent types with normalization

7. **Löh, McBride & Swierstra** - "A Tutorial Implementation of a Dependently Typed Lambda Calculus" (2010)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=14554396587341558454)
   - Practical bidirectional implementation

## Exercises

See `exercises/EXERCISES.md` for:
- Mode classification problems
- Derivation tree exercises
- Annotation placement challenges
- Implementation extensions (subtyping, holes, patterns)

## Tests

Run the test suite:
```bash
stack test
```

Tests cover:
- Inference mode: variables, annotated lambdas, application, annotations
- Checking mode: lambdas, pairs, sum injections, type abstraction
- Polymorphism: type application, type abstraction
- Error cases: unbound variables, type mismatches, cannot-infer errors
