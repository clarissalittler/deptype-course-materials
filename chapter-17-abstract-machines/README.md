# Chapter 17: Abstract Machines

## Overview

Abstract machines bridge the gap between high-level operational semantics and actual implementation. While substitution-based semantics are elegant for reasoning, they're inefficient for execution. Abstract machines make the "machinery" of evaluation explicit: environments, continuations, and control flow.

This chapter implements three classic abstract machines:
- **CEK Machine**: Call-by-value, continuation-based
- **SECD Machine**: Stack-based, compiled
- **Krivine Machine**: Call-by-name (lazy)

**Why this matters for research**: Understanding abstract machines is essential for:
- Implementing interpreters and compilers
- Reasoning about evaluation strategies
- Designing new language features
- Understanding papers on operational semantics

## The Key Insight

Consider evaluating `(λx. x + x) (1 + 2)`:

**Substitution semantics:**
```
(λx. x + x) (1 + 2)
→ (λx. x + x) 3        -- evaluate argument
→ 3 + 3                -- substitute
→ 6
```

**Problem**: Substitution traverses the entire term body, which is expensive.

**Abstract machine approach:**
```
Instead of substituting, maintain an environment:
  env = {x ↦ 3}

When we see x, look it up in env instead of having substituted.
```

## CEK Machine

The CEK machine is named for its three components:
- **C**ontrol: The current term being evaluated
- **E**nvironment: Bindings for free variables
- **K**ontinuation: What to do after evaluating the current term

### State

```haskell
data State
  = Eval Term Env Kont      -- Evaluating a term
  | Apply Kont Value        -- Applying continuation to a value
```

### Continuation as Evaluation Context

The key insight is reifying the *evaluation context* as a data structure.

In substitution semantics, we implicitly have a context:
```
E ::= []
    | E t
    | v E
    | E + t
    | v + E
    | ...
```

The CEK machine makes this explicit as a list of *frames*:

```haskell
type Kont = [Frame]

data Frame
  = FApp1 Term Env    -- [_ t2] with env
  | FApp2 Value       -- [v1 _]
  | FAdd1 Term Env    -- [_ + t2]
  | FAdd2 Value       -- [v1 + _]
  | ...
```

### Transition Rules

**Variable lookup:**
```
⟨x, ρ, κ⟩  →  ⟨κ, ρ(x)⟩
```
Look up x in environment, apply continuation to result.

**Lambda (creates closure):**
```
⟨λx.t, ρ, κ⟩  →  ⟨κ, ⟨λx.t, ρ⟩⟩
```
Package lambda with current environment as a closure.

**Application (evaluate function first):**
```
⟨t₁ t₂, ρ, κ⟩  →  ⟨t₁, ρ, (□ t₂)ρ :: κ⟩
```
Push "evaluate argument next" onto continuation.

**Apply function to argument:**
```
⟨(v □) :: κ, ⟨λx.t, ρ'⟩⟩  →  ⟨t, ρ'[x↦v], κ⟩
```
Extend closure's environment with argument, continue with body.

### Example Trace

Evaluating `(λx. x + 1) 5`:

```
Eval (λx. x+1) 5, {}, []
→ Eval (λx. x+1), {}, [FApp1 5 {}]      -- push arg frame
→ Apply [FApp1 5 {}], <λx.x+1, {}>      -- lambda → closure
→ Eval 5, {}, [FApp2 <λx.x+1, {}>]      -- now eval argument
→ Apply [FApp2 <λx.x+1, {}>], 5         -- 5 is a value
→ Eval x+1, {x↦5}, []                   -- beta reduction
→ Eval x, {x↦5}, [FAdd1 1 {x↦5}]
→ Apply [FAdd1 1 {x↦5}], 5              -- looked up x
→ Eval 1, {x↦5}, [FAdd2 5]
→ Apply [FAdd2 5], 1
→ Apply [], 6                           -- Done!
```

## SECD Machine

The SECD machine (Landin, 1964) was one of the first abstract machines. It's closer to how real VMs work because it compiles terms to instructions first.

### Components

- **S**tack: For intermediate values
- **E**nvironment: Variable bindings (by de Bruijn index)
- **C**ontrol: List of instructions to execute
- **D**ump: Saved states for function returns

### Instructions

```haskell
data Instr
  = IAccess Int      -- Push env[i] onto stack
  | IClosure Code    -- Push closure onto stack
  | IApply           -- Apply top two stack values
  | IReturn          -- Return from function
  | IConst Integer   -- Push constant
  | IAdd | ISub | IMul
  | IIf0 Code Code   -- Conditional
```

### Compilation

```haskell
compile (TmVar x)     = [IAccess (index of x)]
compile (TmLam x t)   = [IClosure (compile t ++ [IReturn])]
compile (TmApp t1 t2) = compile t1 ++ compile t2 ++ [IApply]
compile (TmInt n)     = [IConst n]
compile (TmAdd t1 t2) = compile t1 ++ compile t2 ++ [IAdd]
```

### Example

Compiling `(λx. x + 1) 5`:

```
λx. x + 1  compiles to  [IClosure [IAccess 0, IConst 1, IAdd, IReturn]]
5          compiles to  [IConst 5]
application adds        [IApply]

Full: [IClosure [...], IConst 5, IApply]
```

## Krivine Machine

The Krivine machine implements **call-by-name** (lazy) evaluation. Arguments are not evaluated until they're used.

### Key Difference from CEK

In CEK (call-by-value):
```
(λx. 42) (divergent)  -- Diverges! Must evaluate argument.
```

In Krivine (call-by-name):
```
(λx. 42) (divergent)  -- Returns 42! Argument never needed.
```

### State

```haskell
data State = State Term Env Stack

-- Stack holds *unevaluated* closures (thunks)
type Stack = [Thunk]
data Thunk = Thunk Term Env
```

### Rules

**Variable:**
```
⟨x, ρ, π⟩  →  ⟨t, ρ', π⟩  where ρ(x) = (t, ρ')
```

**Lambda with argument:**
```
⟨λx.t, ρ, c::π⟩  →  ⟨t, ρ[x↦c], π⟩
```

**Application:**
```
⟨t₁ t₂, ρ, π⟩  →  ⟨t₁, ρ, (t₂,ρ)::π⟩
```
Push argument as thunk, don't evaluate it!

## Comparison

| Feature | CEK | SECD | Krivine |
|---------|-----|------|---------|
| Strategy | Call-by-value | Call-by-value | Call-by-name |
| Compilation | No | Yes | No |
| Continuation | Explicit | Implicit (dump) | Implicit (stack) |
| Environment | Map | List (de Bruijn) | Map |
| Use case | Interpreters | VMs | Lazy languages |

## Connection to Real Systems

### CEK → Modern Interpreters

Many interpreters use CEK-like designs:
- JavaScript engines (V8, SpiderMonkey)
- Python's eval loop
- Scheme interpreters

### SECD → Virtual Machines

SECD inspired:
- OCaml's ZINC machine
- Java bytecode
- WebAssembly

### Krivine → Lazy Evaluation

Krivine machines underlie:
- GHC's STG machine (with memoization)
- Lazy evaluation in Haskell

## Building and Testing

```bash
cd chapter-17-abstract-machines
stack build
stack test
stack exec abstract-machines-repl
```

## REPL Examples

```
am> (\\x. x + x) 21
Result: 42

am> let fact = fix (\\f. \\n. if0 n then 1 else n * f (n - 1)) in fact 5
Result: 120

am> :trace (\\x. x) 5
Trace (5 steps):
  Eval { term = (λx. x) 5, env = 0 bindings, kont = 0 frames }
  ...
```

## File Structure

```
chapter-17-abstract-machines/
├── src/
│   ├── Syntax.hs    -- Shared syntax, values, environments
│   ├── CEK.hs       -- CEK machine implementation
│   ├── SECD.hs      -- SECD machine implementation
│   ├── Krivine.hs   -- Krivine machine implementation
│   ├── Parser.hs    -- Term parser
│   └── Pretty.hs    -- Pretty printer
├── app/
│   └── Main.hs      -- REPL
├── test/
│   └── Spec.hs      -- Test suite
├── exercises/
│   └── EXERCISES.md -- Practice problems
├── package.yaml
├── stack.yaml
└── README.md
```

## References

### Primary Sources

1. **Landin, P.J.** (1964). "The Mechanical Evaluation of Expressions." *Computer Journal*, 6(4), 308-320.
   The original SECD machine paper.
   [Oxford Academic](https://academic.oup.com/comjnl/article/6/4/308/375725) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=5765678926931721822)

2. **Plotkin, G.D.** (1975). "Call-by-Name, Call-by-Value and the λ-Calculus." *Theoretical Computer Science*, 1(2), 125-159.
   Foundational paper on evaluation strategies.
   [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0304397575900171) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=16aborb84641858676)

3. **Krivine, J.-L.** (2007). "A Call-by-Name Lambda-Calculus Machine." *Higher-Order and Symbolic Computation*, 20(3), 199-207.
   The Krivine machine explained.
   [SpringerLink](https://link.springer.com/article/10.1007/s10990-007-9018-9) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=1549626957444577335)

4. **Felleisen, M. & Friedman, D.P.** (1986). "Control Operators, the SECD-machine, and the λ-calculus." *Formal Description of Programming Concepts III*.
   Connecting abstract machines to control operators.
   [Google Scholar](https://scholar.google.com/scholar?cluster=17451491855641141613)

### Modern Treatments

5. **Danvy, O. & Millikin, K.** (2008). "A Rational Deconstruction of Landin's SECD Machine with the J Operator." *Logical Methods in Computer Science*, 4(4).
   Modern analysis of SECD.
   [LMCS](https://lmcs.episciences.org/1147) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=16893507754395912345)

6. **Biernacka, M. & Danvy, O.** (2007). "A Concrete Framework for Environment Machines." *ACM TOCL*, 8(1).
   Systematic derivation of abstract machines.
   [ACM DL](https://dl.acm.org/doi/10.1145/1182613.1182615) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=10766785089459578587)

7. **Ager, M.S., Biernacki, D., Danvy, O., & Midtgaard, J.** (2003). "A Functional Correspondence between Evaluators and Abstract Machines." *PPDP 2003*.
   Deriving machines from interpreters.
   [ACM DL](https://dl.acm.org/doi/10.1145/888251.888254) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=15648385296877374926)

### Books

8. **Pierce, B.C.** (2002). *Types and Programming Languages*. MIT Press.
   Chapter 12: Normalization (discusses evaluation).
   [MIT Press](https://www.cis.upenn.edu/~bcpierce/tapl/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=2853553209915529600)

9. **Friedman, D.P. & Wand, M.** (2008). *Essentials of Programming Languages*, 3rd ed. MIT Press.
   Excellent treatment of interpreters and machines.
   [MIT Press](https://mitpress.mit.edu/9780262062794/essentials-of-programming-languages/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=7548855325641613780)

### Implementation

10. **Leroy, X.** (1990). "The ZINC Experiment: An Economical Implementation of the ML Language." *INRIA Technical Report 117*.
    OCaml's abstract machine.
    [INRIA](https://hal.inria.fr/inria-00070049) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=5645197908tried2986)

11. **Peyton Jones, S.** (1987). *The Implementation of Functional Programming Languages*. Prentice Hall.
    Classic book on implementing lazy languages.
    [Free PDF](https://www.microsoft.com/en-us/research/publication/the-implementation-of-functional-programming-languages/) |
    [Google Scholar](https://scholar.google.com/scholar?cluster=9891156127668451601)

## Exercises

See `exercises/EXERCISES.md` for:
- Extending CEK with pairs, exceptions, state
- Implementing call-by-name CEK
- Tail call optimization
- Building a debugger

## Next Steps

- **Chapter 18 (NbE)**: A different approach using normalization by evaluation
- **Chapter 20 (Denotational Semantics)**: Mathematical meaning vs. operational behavior

## Key Takeaways

1. **Environments replace substitution**: More efficient, explicit variable binding
2. **Continuations reify control flow**: The "rest of the computation" as data
3. **Different machines, same answer**: CEK, SECD, Krivine all compute the same values (for terminating programs without effects)
4. **Compilation vs. interpretation**: SECD pre-compiles; CEK/Krivine interpret directly
5. **Evaluation strategy**: CEK = strict; Krivine = lazy

---

**Tests**: 35+ passing | **Exercises**: 10 problems + 3 challenges
