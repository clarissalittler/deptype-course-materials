# Chapter 18: Normalization by Evaluation - REPL User Guide

## Overview

The NbE REPL lets you experiment with normalization by evaluation, see the eval and quote phases separately, inspect closures and environments, and test definitional equality.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-18-normalization-by-evaluation
stack build

# Run the REPL
stack exec nbe-repl
```

### Quick Start

```
nbe> \x. x
Normal form: λx. x

nbe> (\x. x) 5
Normal form: 5

nbe> :help
[Shows available commands]
```

## Features

### 1. Normalization

Simply type a term to normalize it:

```
nbe> ((\x. x + x) 3)
Normal form: 6

nbe> (\x. \y. x) true false
Normal form: true

nbe> ((\n. \f. \x. f (n f x)) (\f. \x. f x))
Normal form: λf. λx. f (f x)
```

### 2. Eval and Quote Separately

See the two phases independently:

#### Eval Phase (Syntax → Semantics)

```
nbe> :eval \x. x + 1
Value: VLam "x" (Closure env={} body=(x + 1))

nbe> :eval let y = 10 in \x. x + y
Value: VLam "x" (Closure env={y→10} body=(x + y))

nbe> :eval ((\x. x) 5)
Value: VInt 5
```

#### Quote Phase (Semantics → Normal Form)

```
nbe> :quote (VLam "x" (Closure [] (TVar 0)))
Normal form: λx. x

nbe> :quote (VInt 42)
Normal form: 42
```

### 3. Tracing

See complete eval and quote steps:

```
nbe> :trace (\x. x + 1) 5

=== EVAL PHASE ===
Step 1: eval [] ((\x. x+1) 5)
Step 2: vApp (eval [] (\x. x+1)) (eval [] 5)
Step 3: vApp (VLam "x" (Closure [] (x+1))) (VInt 5)
Step 4: applyClosure (Closure [] (x+1)) (VInt 5)
Step 5: eval [VInt 5] (x + 1)
Step 6: 5 + 1
Result: VInt 6

=== QUOTE PHASE ===
Step 1: quote 0 (VInt 6)
Result: NfInt 6

Normal form: 6
```

Disable traces with `:notrace`.

### 4. Step-by-Step Mode

Step through normalization manually:

```
nbe> :step (\x. x) 5

Eval Step 1/5: eval [] ((\x. x) 5)
  [Press Enter to continue, 'q' to quit]

Eval Step 2/5: vApp (VLam "x" (Closure [] (TVar 0))) (VInt 5)
  [Press Enter to continue, 'q' to quit]

...

Quote Step 1/1: quote 0 (VInt 5)
  [Press Enter to continue, 'q' to quit]

Normal form: 5
```

### 5. Definitional Equality

Check if two terms are definitionally equal:

```
nbe> :equal (\x. x) (\y. y)
Definitionally equal: true

nbe> :equal ((\x. x) 5) 5
Definitionally equal: true

nbe> :equal (\f. \x. f x) (\g. \y. g y)
Definitionally equal: true

nbe> :equal (\x. x) (\x. x + 1)
Definitionally equal: false
```

### 6. Environment Inspection

See what closures capture:

```
nbe> :env let x = 5 in let y = 10 in \z. x + y + z

Closure environment:
  x → VInt 5
  y → VInt 10

Full closure:
  VLam "z" (Closure env={x→5, y→10} body=(x + y + z))
```

### 7. Fresh Variable Visualization

See fresh variable generation during quote:

```
nbe> :quote-verbose \f. \x. f (f x)

Quote at level 0:
  Quoting VLam "f" (Closure [] ...)
  Creating fresh variable f₀ at level 0
  Applying closure to f₀
  Result: VLam "x" (Closure [f₀] ...)

Quote at level 1:
  Quoting VLam "x" (Closure [f₀] ...)
  Creating fresh variable x₁ at level 1
  Applying closure to x₁
  Result: VNe (NApp (NApp (NVar 0) (NVar 1)) (NVar 1))

Quote at level 2:
  Quoting neutral application
  Converting level 0 → index 1 (f)
  Converting level 1 → index 0 (x)
  Result: f (f x)

Normal form: λf. λx. f (f x)
```

## Term Syntax

### Lambda Abstraction

```
\x. x                 Single argument
\x y. x               Multiple arguments (desugars to nested)
λx. x                 Unicode lambda
```

### Application

```
f x                   Simple application
f x y                 Left-associative: (f x) y
(f x) (g y)           Parentheses for grouping
```

### Types (for dependent types)

```
Type                  Universe
(x : A) -> B          Pi type (dependent function)
A -> B                Simple function type
```

### Let Bindings

```
let x = 5 in x + 1
```

### Literals and Operators

```
0, 1, 42, -5          Integers
true, false           Booleans
x + y, x - y, x * y   Arithmetic
```

## Command Reference

### Normalization Commands

| Command | Description |
|---------|-------------|
| `term` | Normalize term (eval then quote) |
| `:normalize term` | Same as above (explicit) |
| `:eval term` | Eval phase only (show value) |
| `:quote value` | Quote phase only (show normal form) |

### Inspection Commands

| Command | Description |
|---------|-------------|
| `:trace term` | Show full eval and quote trace |
| `:step term` | Step-by-step normalization |
| `:env term` | Show closure environment |
| `:quote-verbose val` | Show fresh variable generation |
| `:notrace` | Disable automatic traces |

### Equality Commands

| Command | Description |
|---------|-------------|
| `:equal t1 t2` | Check definitional equality |
| `:alpha t1 t2` | Check alpha equivalence |
| `:beta t1 t2` | Check beta equivalence (normalize) |

### Binding Commands

| Command | Description |
|---------|-------------|
| `:let name = term` | Define a binding |
| `:bindings` | Show all bindings |
| `:clear` | Clear all bindings |

### Information Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help message |
| `:examples` | Show example programs |
| `:type term` | Show type (if type checking enabled) |
| `:quit` | Exit the REPL |

## Advanced Examples

### Church Numerals

```
nbe> :let zero = \f. \x. x
nbe> :let one = \f. \x. f x
nbe> :let two = \f. \x. f (f x)
nbe> :let three = \f. \x. f (f (f x))

nbe> :let succ = \n. \f. \x. f (n f x)
nbe> :let add = \m. \n. \f. \x. m f (n f x)
nbe> :let mult = \m. \n. \f. m (n f)

nbe> succ two
Normal form: λf. λx. f (f (f x))  -- three!

nbe> add one two
Normal form: λf. λx. f (f (f x))  -- three!

nbe> mult two three
Normal form: λf. λx. f (f (f (f (f (f x)))))  -- six!
```

### Church Booleans

```
nbe> :let true = \t. \f. t
nbe> :let false = \t. \f. f
nbe> :let if = \b. \t. \f. b t f
nbe> :let and = \p. \q. p q p
nbe> :let or = \p. \q. p p q
nbe> :let not = \p. p false true

nbe> if true 1 2
Normal form: 1

nbe> and true false
Normal form: λt. λf. f  -- false

nbe> not false
Normal form: λt. λf. t  -- true
```

### Church Pairs

```
nbe> :let pair = \x. \y. \f. f x y
nbe> :let fst = \p. p (\x. \y. x)
nbe> :let snd = \p. p (\x. \y. y)

nbe> fst (pair true false)
Normal form: λt. λf. t  -- true

nbe> snd (pair 1 2)
Normal form: 2
```

### Closures and Environments

```
nbe> :env let x = 5 in \y. x + y
Closure: VLam "y" (Closure env={x→5} body=(x + y))

nbe> :normalize (let x = 5 in (\y. x + y) 3)
Normal form: 8

nbe> :trace let x = 1 in let f = \y. x + y in let x = 100 in f 5

Eval phase:
  Evaluating: let x = 1 in ...
  Environment: {x → 1}

  Evaluating: let f = \y. x + y in ...
  Closure created: VLam "y" (Closure {x→1} (x + y))
  Environment: {f → VLam..., x → 1}

  Evaluating: let x = 100 in ...
  Environment: {x → 100, f → VLam..., x → 1}  -- x shadowed!

  Evaluating: f 5
  Using closure with {x → 1}  -- Lexical scoping!
  Result: 6

Normal form: 6
```

### Type-Level Computation

```
nbe> :let Vec = \n. \A. Type  -- Simplified
nbe> :equal (Vec 0) (Vec ((\x. x) 0))
Definitionally equal: true

nbe> :let Fin = \n. Type
nbe> :equal (Fin (1 + 1)) (Fin 2)
Definitionally equal: true
```

### Neutral Terms

```
nbe> :eval \x. x 5
Value: VLam "x" (Closure [] (x 5))

When we quote with fresh variable for x:

nbe> :quote-verbose (VLam "x" (Closure [] (TApp (TVar 0) (TLit 5))))

Quote at level 0:
  Fresh variable x₀ at level 0
  Applying closure to x₀

  Eval in environment [x₀]:
    eval [VNe (NVar 0)] (TApp (TVar 0) (TLit 5))
    → vApp (VNe (NVar 0)) (VInt 5)
    → VNe (NApp (NVar 0) (VInt 5))  -- Stuck!

Quote the neutral:
  Result: x 5

Normal form: λx. x 5
```

## Comparing with Reduction

### Traditional Beta Reduction

```
manual> ((\x. x + x) 3)
Step 1: [x ↦ 3](x + x)
Step 2: 3 + 3
Step 3: 6
```

### NbE

```
nbe> :trace (\x. x + x) 3

Eval:
  vApp (VLam "x" (Closure [] (x + x))) (VInt 3)
  → applyClosure (Closure [] (x + x)) (VInt 3)
  → eval [VInt 3] (x + x)
  → 3 + 3
  → 6

Quote:
  quote 0 (VInt 6) → 6

Normal form: 6
```

Key difference: NbE uses environment lookup instead of substitution!

## Practice Exercises

### Exercise 1: Trace Analysis

Trace both phases for:

```
nbe> :trace (\f. \x. f (f x)) (\n. n + 1) 0
```

Questions:
- How many closures are created?
- What environments do they capture?
- What fresh variables are used in quote?

### Exercise 2: Definitional Equality

Which are equal?

```
nbe> :equal (\x. (\y. y) x) (\z. z)
nbe> :equal (\f. \x. f x) (\f. f)
nbe> :equal ((\x. x) (\y. y)) (\z. z)
```

### Exercise 3: Closure Capture

Predict the result before running:

```
nbe> let x = 1 in
     let y = 2 in
     let f = \z. x + y + z in
     let x = 100 in
     let y = 200 in
     f 3
```

Then use `:trace` to verify.

### Exercise 4: Fresh Variables

For `\f. \x. f x`, show:
- What fresh variables are created
- At what levels
- How they're converted to indices

Use `:quote-verbose`.

### Exercise 5: Church Numeral Arithmetic

Verify these identities:

```
nbe> :equal (add one one) two
nbe> :equal (mult two three) (add three three)
nbe> :equal (succ (succ zero)) two
```

## Common Patterns

### Identity

```
nbe> \x. x
Normal form: λx. x
```

### Constant

```
nbe> \x. \y. x
Normal form: λx. λy. x

nbe> (\x. \y. x) 5 10
Normal form: 5
```

### Composition

```
nbe> :let compose = \f. \g. \x. f (g x)
nbe> compose (\x. x + 1) (\y. y * 2) 3
Normal form: 7  -- (3 * 2) + 1
```

### Application

```
nbe> :let apply = \f. \x. f x
nbe> apply (\n. n + 1) 5
Normal form: 6
```

### Twice

```
nbe> :let twice = \f. \x. f (f x)
nbe> twice (\n. n + 1) 0
Normal form: 2
```

## Troubleshooting

### Values vs Terms Confusion

**Problem**: Trying to quote a term directly.

**Solution**:
```
nbe> :eval term      # Get value first
nbe> :quote value    # Then quote
```

Or just use:
```
nbe> term            # Does eval + quote automatically
```

### Index/Level Confusion

**Problem**: Wrong de Bruijn index in output.

**Solution**: Remember the conversion:
```
index = depth - level - 1
```

Use `:quote-verbose` to see conversion.

### Environment Not Captured

**Problem**: Free variable errors or wrong values.

**Solution**: Check closure creation in trace:
```
nbe> :trace let x = 5 in \y. x + y
```

Verify the closure captures `{x → 5}`.

### Infinite Types

**Problem**: Type checking diverges (if type checker enabled).

**Solution**: Check for recursive types or non-normalizing terms.

## Advanced Topics

### Type-Directed Quote

With types, we can do eta-expansion:

```haskell
-- For a neutral f of type A → B
quote (TyArr a b) lvl (VNe neu) =
  let x = VNe (NVar lvl)
      body = vApp (VNe neu) x
  in NfLam "x" (quote b (lvl + 1) body)
```

This makes `f` and `λx. f x` equal (eta equality).

### Dependent Types

For Pi types `(x : A) → B`:

```haskell
quote lvl (VPi x a closure) =
  let dom = quote lvl a
      fresh = VNe (NVar lvl)
      cod = quote (lvl + 1) (applyClosure closure fresh)
  in NfPi x dom cod
```

### Universe Levels

For multiple universes:

```haskell
data Val = ... | VU Lvl  -- Universe at level

quote _ (VU l) = NfU l
```

## Further Reading

- [Chapter 18 README](README.md) - Complete theory
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step examples
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- Berger & Schwichtenberg (1991): Original NbE paper
- Abel (2013): Comprehensive treatment
- Löh, McBride, Swierstra (2010): Tutorial implementation

## Next Steps

After mastering NbE:
- Chapter 19: Bidirectional type checking (uses NbE for equality)
- Implement your own NbE for a richer calculus
- Study NbE for modal types, cubical type theory

Have fun normalizing!
