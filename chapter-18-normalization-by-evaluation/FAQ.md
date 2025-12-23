# Chapter 18: Normalization by Evaluation - Frequently Asked Questions

## Conceptual Questions

### Q: What is Normalization by Evaluation?

**A:** NbE is a technique for computing normal forms of lambda calculus terms (and richer languages). It works in two phases:

1. **Evaluation**: Interpret syntactic terms into a semantic domain (Haskell values), letting Haskell do beta reduction
2. **Quotation**: Read the semantic values back into normal form syntax

The composition `quote ∘ eval` gives normalization.

### Q: Why not just apply reduction rules until we're stuck?

**A:** Reduction-based normalization has issues:

1. **Efficiency**: Repeated traversal and substitution
2. **Complexity**: Need reduction rules for every construct
3. **Correctness**: Easy to get wrong, hard to prove correct
4. **Termination**: May not halt for non-normalizing terms

NbE avoids most of these by using the host language's evaluation.

### Q: What's a "semantic domain"?

**A:** The semantic domain is the type of values that `eval` produces. It represents the "meaning" of terms rather than their syntax.

```haskell
data Val
  = VLam Name Closure    -- Function: a closure
  | VPi Name Val Closure -- Dependent function type
  | VNe Neutral          -- Stuck on variable
  | ...
```

The key insight is that lambdas become closures (Haskell functions + captured environment), not syntactic lambda expressions.

### Q: What's a closure and why do we need it?

**A:** A closure pairs a lambda body with its defining environment:

```haskell
data Closure = Closure Env Term
```

We need closures because lambda bodies may have free variables that refer to the enclosing scope. The closure "closes over" these variables.

Example:
```
let y = 5 in λx. x + y
```

The closure for `λx. x + y` is `Closure {y ↦ 5} (x + y)`. When we apply it to an argument, we evaluate `x + y` in `{x ↦ arg, y ↦ 5}`.

### Q: What's a "neutral" value?

**A:** A neutral value is stuck on a free variable—we can't reduce further without knowing what the variable is.

```haskell
data Neutral = NVar Lvl | NApp Neutral Val | ...
```

Examples:
- `x` (free variable)
- `x 5` (application of free variable)
- `f (y z)` (nested neutral)

Neutrals preserve structure during normalization. They become variables and applications in the normal form.

### Q: What's the difference between levels and indices?

**A:** Both are ways to represent bound variables without names.

**De Bruijn indices**: Count binders inward from the use site
```
λ. λ. 0 1    -- 0 = inner λ, 1 = outer λ
```

**De Bruijn levels**: Count binders outward from the root
```
λ. λ. 1 0    -- 0 = outer λ, 1 = inner λ (at depth 2)
```

NbE uses levels internally because fresh variable generation is just incrementing the level. We convert to indices when producing the final normal form.

Conversion: `index = depth - level - 1`

### Q: How does quoting a lambda work?

**A:** To quote a lambda (represented as a closure), we:

1. Create a fresh neutral variable at the current level
2. Apply the closure to this fresh variable
3. Recursively quote the result

```haskell
quote lvl (VLam x closure) =
  let freshVar = VNe (NVar lvl)
      body = applyClosure closure freshVar
  in NfLam x (quote (lvl + 1) body)
```

This "opens" the closure to see what it does to its argument.

### Q: What is eta expansion?

**A:** Eta expansion converts `f` to `λx. f x` for functions. In NbE, it happens naturally when quoting a neutral of function type:

```haskell
quoteWithEta lvl (TyArr a b) (VNe neutral) =
  let freshVar = VNe (NVar lvl)
      body = vApp (VNe neutral) freshVar
  in NfLam "x" (quote (lvl + 1) body b)
```

This is useful because it makes `f` and `λx. f x` have the same normal form, which is correct for extensional function equality.

## Implementation Questions

### Q: How do I add a new term form to NbE?

**A:** Three steps:

1. **Add to Term and Nf**: New syntactic constructs
2. **Add to Val**: New semantic value (if needed)
3. **Extend eval and quote**: Handle the new cases

Example: Adding pairs
```haskell
-- Term
| TPair Term Term
| TFst Term
| TSnd Term

-- Val
| VPair Val Val

-- Nf
| NfPair Nf Nf
| NfFst Nf
| NfSnd Nf

-- eval
eval env (TPair a b) = VPair (eval env a) (eval env b)
eval env (TFst p) = vFst (eval env p)
eval env (TSnd p) = vSnd (eval env p)

-- quote
quote lvl (VPair a b) = NfPair (quote lvl a) (quote lvl b)
```

### Q: How does NbE handle recursion/fixpoints?

**A:** Carefully! The simplest approach uses Haskell's laziness:

```haskell
eval env (TFix f) = fix (\v -> vApp (eval env f) v)

-- where fix is Haskell's fixpoint
fix :: (a -> a) -> a
fix f = let x = f x in x
```

This only works for productive fixpoints. For non-normalizing terms, it may loop.

### Q: Can NbE handle effects?

**A:** Standard NbE assumes pure computation. For effects, you need:

1. **Monadic NbE**: `eval` returns in a monad
2. **Effectful semantic domain**: Values may be computations
3. **Normalization under effects**: Careful about when effects happen

This is an active research area.

### Q: How do I implement typed NbE?

**A:** In typed NbE, quotation is type-directed:

```haskell
quote :: Lvl -> Type -> Val -> Nf
quote lvl (TyArr a b) f =
  let x = VNe (NVar lvl)
  in NfLam "x" (quote (lvl + 1) b (vApp f x))
quote lvl TyBool (VBool b) = NfBool b
quote lvl _ (VNe ne) = NfNe (quoteNe lvl ne)
```

This enables proper eta expansion for each type former.

### Q: How does NbE relate to type checking?

**A:** In dependent type theory, type equality requires normalization:

```haskell
-- Check if two types are definitionally equal
typeEq :: Ctx -> Val -> Val -> Bool
typeEq ctx t1 t2 =
  quote (ctxLevel ctx) t1 == quote (ctxLevel ctx) t2
```

When checking `f e` where `f : (x : A) → B`, we need `B[x := e]`. This is computed by:

```haskell
resultType = applyClosure closureForB (eval env e)
```

NbE handles the "substitution" seamlessly via closures.

## Common Confusions

### Q: Why does eval return Val instead of Nf?

**A:** Val and Nf serve different purposes:

- **Val**: Efficient for computation (closures, not substituted terms)
- **Nf**: Canonical representation for comparison and output

We compute in Val (eval), then convert to Nf (quote) when needed.

### Q: Is NbE only for lambda calculus?

**A:** No! NbE works for many type theories:

- Simply typed lambda calculus
- System F (polymorphism)
- Dependent type theory (Pi, Sigma, universes)
- Cubical type theory
- Modal type theories

The pattern (eval to semantics, quote back to syntax) is very general.

### Q: How does NbE handle open terms?

**A:** Via neutral values! When we encounter a free variable:

```haskell
eval env (TVar i) = env !! i
-- If env !! i is a neutral, we get a neutral
```

Neutrals propagate through computation, preserving the structure of stuck terms.

### Q: Does NbE always terminate?

**A:** For normalizing terms, yes (assuming correct implementation). For non-normalizing terms, NbE will loop just like reduction would.

The advantage is that NbE termination follows from Haskell's termination for the corresponding semantic computation.

## Troubleshooting

### Q: My NbE produces wrong normal forms. What to check?

**A:** Common issues:

1. **Environment capture**: Are closures capturing the right environment?
2. **Level increment**: Are you incrementing level when entering binders?
3. **Index conversion**: Is level-to-index conversion correct?
4. **Neutral handling**: Are neutrals being preserved properly?

Add tracing to see intermediate values.

### Q: Some terms normalize differently than expected.

**A:** Check:

1. **Evaluation order**: NbE is usually call-by-name in the object language
2. **Eta behavior**: Are you eta-expanding? Should you be?
3. **Sharing**: Environments share values; make sure this is correct

### Q: I get an "index out of bounds" error.

**A:** This usually means:

1. Free variable in a supposedly closed term
2. Wrong environment being passed to eval
3. Environment not extended when entering a binder

Check that environments are built correctly.

### Q: Performance is poor. How can I improve?

**A:** Common optimizations:

1. **Lazy evaluation**: Don't evaluate until needed
2. **Whnf**: Evaluate to weak head normal form, not full Nf
3. **Sharing**: Use Haskell's sharing effectively
4. **Hash-consing**: For the normal form type
5. **Spine form**: Represent applications efficiently

For production implementations, see the "Elaboration Zoo" for modern techniques.
