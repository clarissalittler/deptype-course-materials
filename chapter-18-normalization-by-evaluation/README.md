# Chapter 18: Normalization by Evaluation

## Overview

Normalization by Evaluation (NbE) is a powerful technique for implementing type checkers, especially for dependently-typed languages. The key insight is to use the host language's (Haskell's) evaluation to perform beta reduction, then "read back" the result into a normal form.

**Why NbE matters:**
- Type checking dependent types requires comparing types for equality
- Types can contain arbitrary terms, so we need normalization
- NbE is elegant, efficient, and scales to complex type systems

## The Core Idea

NbE works in two phases:

```
            eval                    quote
    Term  ────────►  Val  ────────►  Nf
           (compute)      (read back)
```

1. **Evaluation** (`eval`): Interpret syntactic terms into semantic values, using Haskell's evaluation for beta reduction.

2. **Quotation** (`quote`): Convert semantic values back into normal forms (canonical syntactic representation).

**Normalization** = quote ∘ eval

## Why Not Just Reduce?

Traditional approach: apply reduction rules repeatedly until no rules apply.

```
(λx. x + x) 3
→ 3 + 3           -- beta reduction
→ 6               -- arithmetic
```

Problems:
- Need to define reduction for every construct
- May not terminate (for non-normalizing terms)
- Efficiency concerns (repeated traversal)

NbE approach:
- Use Haskell functions to represent lambdas
- Haskell does beta reduction for us!
- Guaranteed termination for normalizing terms

## Syntax

We use a simple dependently-typed lambda calculus:

```haskell
data Term
  = TVar Ix                  -- Variable (de Bruijn index)
  | TLam Name Term           -- Lambda abstraction
  | TApp Term Term           -- Application
  | TPi Name Term Term       -- Pi type: (x : A) → B
  | TU                       -- Universe (Type)
  | ...
```

## Semantic Domain

The semantic domain represents "computed" values:

```haskell
data Val
  = VLam Name Closure        -- Function closure
  | VPi Name Val Closure     -- Pi type
  | VU                       -- Universe
  | VNe Neutral              -- Stuck on a variable
  | ...

data Closure = Closure Env Term
type Env = [Val]
```

### Key Insight: Closures

A closure packages a term with its environment:

```
Closure env (λx. body) = "a function waiting for an argument"
```

When we apply it:
```haskell
applyClosure (Closure env body) arg = eval (arg : env) body
```

### Neutral Values

A **neutral** value is "stuck" on a free variable:

```haskell
data Neutral
  = NVar Lvl           -- Free variable
  | NApp Neutral Val   -- Application to neutral
  | ...
```

We can't reduce `x 5` further without knowing what `x` is.

## Evaluation

Evaluation interprets terms into values:

```haskell
eval :: Env -> Term -> Val

eval env (TVar i)     = env !! i           -- Look up in environment
eval env (TLam x t)   = VLam x (Closure env t)  -- Create closure
eval env (TApp t u)   = vApp (eval env t) (eval env u)
eval env (TPi x a b)  = VPi x (eval env a) (Closure env b)
eval _   TU           = VU
```

### Application

```haskell
vApp :: Val -> Val -> Val
vApp (VLam _ closure) arg = applyClosure closure arg  -- Beta!
vApp (VNe neutral) arg    = VNe (NApp neutral arg)    -- Stuck
```

This is where the magic happens: `applyClosure` evaluates the body with the argument bound. Haskell does the work!

## Quotation

Quotation reads values back into normal forms:

```haskell
quote :: Lvl -> Val -> Nf

quote l (VLam x closure) =
  let var = VNe (NVar l)              -- Fresh variable
      body = applyClosure closure var  -- Apply to it
  in NfLam x (quote (l + 1) body)     -- Quote the body

quote l (VNe neutral) = NfNe (quoteNe l neutral)

quote _ VU = NfU
```

### The Fresh Variable Trick

To quote a lambda, we:
1. Create a fresh *neutral* variable at the current level
2. Apply the closure to this variable
3. Quote the result

This "opens" the closure to peek inside.

## Normal Forms

Normal forms are canonical representations:

```haskell
data Nf
  = NfLam Name Nf            -- Lambda (introduction)
  | NfPi Name Nf Nf          -- Pi type
  | NfU                      -- Universe
  | NfNe Ne                  -- Neutral (can't reduce)
  | ...

data Ne
  = NeVar Lvl                -- Variable
  | NeApp Ne Nf              -- Application
  | ...
```

Key property: **Two terms are definitionally equal iff their normal forms are identical.**

## De Bruijn Levels vs. Indices

We use two different numbering schemes:

**Indices** (in terms): Count inward from binding site
```
λx. λy. x    has    x = 1, y = 0
```

**Levels** (in semantics): Count outward from root
```
λx. λy. x    has    x = 0, y = 1  (at depth 2)
```

Why levels? Fresh variable generation is just incrementing the level!

Conversion: `index = depth - level - 1`

## Example: Normalizing Church Numerals

```
two = λf. λx. f (f x)
suc = λn. λf. λx. f (n f x)

normalize (suc two) = ?
```

Evaluation:
1. `eval [] (suc two)`
2. `vApp (VLam "n" ...) <two>`
3. Returns `VLam "f" (Closure [<two>] (λx. f (n f x)))`

Quotation:
1. `quote 0 (VLam "f" ...)`
2. Create fresh `f = NVar 0`
3. Apply closure to `f`
4. Continue recursively...
5. Result: `λf. λx. f (f (f x))` = `three`!

## Type Checking with NbE

To check if types `A` and `B` are equal:

```haskell
equal :: Ctx -> Val -> Val -> Bool
equal ctx a b =
  let nfA = quote (ctxLvl ctx) a
      nfB = quote (ctxLvl ctx) b
  in nfA == nfB
```

Normalize both, compare syntactically.

## Implementation Structure

```
chapter-18-normalization-by-evaluation/
├── src/
│   ├── Syntax.hs    -- Terms, normal forms
│   ├── Semantic.hs  -- Semantic domain (Val, Closure)
│   ├── NbE.hs       -- eval, quote, normalize
│   ├── TypeCheck.hs -- Type checking using NbE
│   ├── Parser.hs    -- Term parser
│   └── Pretty.hs    -- Pretty printer
├── app/
│   └── Main.hs      -- REPL
├── test/
│   └── Spec.hs      -- Test suite
├── exercises/
│   └── EXERCISES.md
├── package.yaml
├── stack.yaml
└── README.md
```

## Building and Testing

```bash
cd chapter-18-normalization-by-evaluation
stack build
stack test
stack exec nbe-repl
```

## REPL Examples

```
nbe> (\x. x) true
Normal form: true

nbe> (\x. \y. x) true false
Normal form: true

nbe> \f. \x. f (f x)
Normal form: λf. λx. f (f x)

nbe> if true then zero else (suc zero)
Normal form: zero
```

## Eta Expansion

NbE naturally performs eta expansion for functions:

```
f : A → B   (where f is neutral)

quote(f) = λx. f x
```

Why? When we quote `f`:
1. Create fresh `x`
2. Apply `f` to `x` → `VNe (NApp f x)`
3. Quote that → `λx. f x`

This is often desirable for type checking.

## Connection to Logical Relations

NbE is closely related to logical relations proofs of normalization:

- The semantic domain is like the "logical predicate"
- Evaluation shows terms satisfy the predicate
- Quotation extracts normal forms

This connection makes NbE particularly elegant for proving metatheory.

## Performance Considerations

NbE is generally efficient because:
- No need to substitute under binders
- Host language does the heavy lifting
- Sharing via closures

But watch out for:
- Space leaks from captured environments
- Exponential blowup in pathological cases

## References

### Primary Sources

1. **Berger, U. & Schwichtenberg, H.** (1991). "An Inverse of the Evaluation Functional for Typed λ-calculus." *LICS 1991*.
   The original NbE paper.
   [IEEE](https://ieeexplore.ieee.org/document/185392) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=12108219074478762106)

2. **Coquand, T. & Dybjer, P.** (1997). "Intuitionistic Model Constructions and Normalization Proofs." *MSCS*, 7(1).
   NbE for dependent types.
   [Cambridge](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/intuitionistic-model-constructions-and-normalization-proofs/B45AA0D8B89A0E4D4B024A97BC2BD9DE) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=5814155706806578802)

3. **Abel, A.** (2013). "Normalization by Evaluation: Dependent Types and Impredicativity." Habilitation thesis.
   Comprehensive treatment of advanced NbE.
   [PDF](http://www.cse.chalmers.se/~abela/habil.pdf) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=9697295952341022769)

4. **Altenkirch, T. & Kaposi, A.** (2016). "Type Theory in Type Theory using Quotient Inductive Types." *POPL 2016*.
   NbE for type theory in type theory.
   [ACM DL](https://dl.acm.org/doi/10.1145/2837614.2837638) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=3614510226927082506)

### Tutorials

5. **Löh, A., McBride, C., & Swierstra, W.** (2010). "A Tutorial Implementation of a Dependently Typed Lambda Calculus." *Fundamenta Informaticae*, 102(2).
   Excellent practical introduction.
   [IOS Press](https://content.iospress.com/articles/fundamenta-informaticae/fi102-2-04) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=6164396108445577991)

6. **Kovács, A.** (2022). "Elaboration Zoo."
   Modern NbE implementations.
   [GitHub](https://github.com/AndrasKovacs/elaboration-zoo)

### Applications

7. **Gratzer, D., Sterling, J., & Birkedal, L.** (2019). "Implementing a Modal Dependent Type Theory." *ICFP 2019*.
   NbE for modal types.
   [ACM DL](https://dl.acm.org/doi/10.1145/3341711) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=14108098553894082716)

8. **Abel, A. & Coquand, T.** (2007). "Untyped Algorithmic Equality for Martin-Löf's Logical Framework with Surjective Pairs." *TLCA 2007*.
   NbE for eta rules.
   [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-540-73228-0_3) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=1620866089856428768)

## Exercises

See `exercises/EXERCISES.md` for:
- Adding pairs and Sigma types
- Implementing eta expansion
- Universe levels
- Typed NbE

## Key Takeaways

1. **eval ∘ quote = normalize**: Simple composition gives normalization
2. **Closures = delayed substitution**: More efficient than actual substitution
3. **Neutrals = stuck terms**: Can't reduce further, so preserve structure
4. **Levels for fresh vars**: Just increment the counter
5. **Host language does beta**: Haskell's evaluation = our beta reduction

## Next Steps

- **Chapter 19**: Bidirectional type checking (uses NbE for type equality)
- **Chapter 20**: Denotational semantics (mathematical perspective)

---

**Tests**: 30+ passing | **Exercises**: 10 problems + 3 challenges
