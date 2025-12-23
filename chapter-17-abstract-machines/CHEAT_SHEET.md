# Chapter 17: Abstract Machines - Cheat Sheet

## Core Concept

Abstract machines make evaluation explicit through **environments** (variable bindings) and **continuations** (control flow), avoiding expensive substitution.

```
Substitution:    (λx. t) v → [x ↦ v]t     (textual replacement)
Environment:     (λx. t) v → eval t in {x ↦ v}     (lookup)
```

## Three Classic Machines

| Machine | Strategy | Key Feature | Use Case |
|---------|----------|-------------|----------|
| CEK | Call-by-value | Explicit continuations | Interpreters, control operators |
| SECD | Call-by-value | Compiled to instructions | VMs, bytecode |
| Krivine | Call-by-name (lazy) | Thunks on stack | Lazy languages |

---

## CEK Machine

### Components

- **C**ontrol: Current term being evaluated
- **E**nvironment: Variable bindings (Map Name Value)
- **K**ontinuation: Stack of frames (what to do next)

### State

```haskell
data State
  = Eval Term Env Kont      -- Evaluating a term
  | Apply Kont Value        -- Applying continuation to value

type Kont = [Frame]
data Frame
  = FApp1 Term Env    -- [_ t] - waiting to eval function
  | FApp2 Value       -- [v _] - waiting to eval argument
  | FAdd1 Term Env    -- [_ + t]
  | FAdd2 Value       -- [v + _]
```

### Key Transitions

```
Variable lookup:
  ⟨x, ρ, κ⟩ → ⟨κ, ρ(x)⟩

Lambda (create closure):
  ⟨λx.t, ρ, κ⟩ → ⟨κ, ⟨λx.t, ρ⟩⟩

Application (eval function first):
  ⟨t₁ t₂, ρ, κ⟩ → ⟨t₁, ρ, (□ t₂)ρ :: κ⟩

Apply function to argument:
  ⟨(□ t) :: κ, ⟨λx.body, ρ'⟩⟩ → ⟨t, ρ', (v □) :: κ⟩

Apply closure:
  ⟨(v □) :: κ, v'⟩ → ⟨body, ρ'[x ↦ v'], κ⟩
    where v = ⟨λx.body, ρ'⟩

Done (empty continuation):
  ⟨[], v⟩ → v
```

### Example Trace

```
(λx. x + 1) 5

Eval (λx. x+1) 5, {}, []
→ Eval (λx. x+1), {}, [FApp1 5 {}]
→ Apply [FApp1 5 {}], ⟨λx.x+1, {}⟩
→ Eval 5, {}, [FApp2 ⟨λx.x+1, {}⟩]
→ Apply [FApp2 ⟨λx.x+1, {}⟩], 5
→ Eval x+1, {x↦5}, []
→ Eval x, {x↦5}, [FAdd1 1 {x↦5}]
→ Apply [FAdd1 1 {x↦5}], 5
→ Eval 1, {x↦5}, [FAdd2 5]
→ Apply [FAdd2 5], 1
→ Apply [], 6
→ Done: 6
```

---

## SECD Machine

### Components

- **S**tack: Intermediate values
- **E**nvironment: Variable bindings (List, de Bruijn indices)
- **C**ontrol: Instruction list to execute
- **D**ump: Saved states for function calls

### Instructions

```haskell
data Instr
  = IAccess Int      -- Push env[i] onto stack
  | IClosure Code    -- Create closure with env
  | IApply           -- Apply top two stack values
  | IReturn          -- Return from function
  | IConst Integer   -- Push constant
  | IAdd | ISub | IMul
  | IIf0 Code Code   -- Branch on zero
```

### Compilation Rules

```haskell
compile (Var x)     = [IAccess (index of x)]
compile (Lam x t)   = [IClosure (compile t ++ [IReturn])]
compile (App t1 t2) = compile t1 ++ compile t2 ++ [IApply]
compile (Lit n)     = [IConst n]
compile (Add t1 t2) = compile t1 ++ compile t2 ++ [IAdd]
```

### Execution Rules

```
IAccess i:
  (s, e, IAccess i : c, d) → (e[i] : s, e, c, d)

IClosure code:
  (s, e, IClosure code : c, d) → (Closure(code, e) : s, e, c, d)

IApply:
  (arg : Closure(c', e') : s, e, IApply : c, d)
    → ([], arg : e', c', (s, e, c) : d)

IReturn:
  (v : s', e', IReturn : [], (s, e, c) : d) → (v : s, e, c, d)

IConst n:
  (s, e, IConst n : c, d) → (n : s, e, c, d)

IAdd:
  (n2 : n1 : s, e, IAdd : c, d) → (n1+n2 : s, e, c, d)
```

### De Bruijn Indices

```
λx. λy. x + y
```

- `y` is bound by inner λ: index 0
- `x` is bound by outer λ: index 1

Rule: Count binders **outward** from variable to its binder.

---

## Krivine Machine

### Components

- **Term**: Current term
- **Environment**: Variable bindings (Map Name Thunk)
- **Stack**: Unevaluated arguments (thunks)

### State

```haskell
data State = State Term Env Stack

type Stack = [Thunk]
data Thunk = Thunk Term Env  -- Unevaluated closure
```

### Key Difference: Thunks

Arguments are **not evaluated** until needed:

```
CEK:      (λx. 42) expensive  →  evaluate expensive, then return 42
Krivine:  (λx. 42) expensive  →  return 42 immediately
```

### Transitions

```
Variable (look up thunk):
  ⟨x, ρ, π⟩ → ⟨t, ρ', π⟩
    where ρ(x) = Thunk(t, ρ')

Lambda with argument:
  ⟨λx.t, ρ, Thunk(t', ρ') :: π⟩ → ⟨t, ρ[x ↦ Thunk(t', ρ')], π⟩

Application (push thunk):
  ⟨t₁ t₂, ρ, π⟩ → ⟨t₁, ρ, Thunk(t₂, ρ) :: π⟩

Value with empty stack:
  ⟨v, ρ, []⟩ → v
```

### Call-by-Name Caveat

```
(λx. x + x) expensive
```

In Krivine, `x` is looked up **twice**, so `expensive` is computed **twice**!

To get Haskell-style call-by-need (lazy), add **memoization** to thunks.

---

## Key Concepts

### Closures

Package a lambda with its environment:

```
Closure = ⟨λx. body, env⟩
```

Why? The body may have free variables that need to be remembered.

```
let y = 10 in λx. x + y
→ ⟨λx. x + y, {y ↦ 10}⟩
```

### Evaluation Order (Call-by-Value)

1. Evaluate function
2. Evaluate argument
3. Apply (extend closure's environment)

```
(λx. x) (1 + 2)
→ eval function: ⟨λx. x, {}⟩
→ eval argument: 3
→ apply: eval x in {x ↦ 3} = 3
```

### Continuation as Evaluation Context

The continuation represents "the hole in the context":

```
Evaluating:  (1 + 2) * 3
               ^^^^^
Currently evaluating 1+2

Continuation: [FMul2 3]  -- "multiply result by 3"
```

---

## Common Patterns

### CEK: Evaluating Application

```haskell
step (Eval (App f t) env k) =
  Eval f env (FApp1 t env : k)  -- Eval f first

step (Apply (FApp1 t env : k) fval) =
  Eval t env (FApp2 fval : k)   -- Now eval t

step (Apply (FApp2 (Closure x body cenv) : k) arg) =
  Eval body (extend x arg cenv) k  -- Apply!
```

### SECD: Compiling Lambda

```haskell
compile (Lam x t) = [IClosure (compile t ++ [IReturn])]
```

Always end closure code with `IReturn`!

### Krivine: Lazy Application

```haskell
step (State (App f t) env stack) =
  State f env (Thunk t env : stack)  -- Don't eval t!
```

---

## Comparison Table

| Feature | CEK | SECD | Krivine |
|---------|-----|------|---------|
| Evaluation | Strict | Strict | Lazy |
| Compilation | No | Yes | No |
| Arguments | Values | Values | Thunks |
| Continuation | Explicit frames | Implicit (dump) | Implicit (stack) |
| Environment | Map/hashtable | List (de Bruijn) | Map/hashtable |
| Beta reduction | Extend env | Push to env list | Bind thunk |

---

## Implementation Tips

### ✓ Do

- Capture environment when creating closures
- Extend **closure's** environment, not current
- Push frames in correct order (function first for CBV)
- Handle empty continuation (terminal state)
- Use de Bruijn indices for SECD

### ✗ Avoid

- Forgetting to capture environment in closure
- Evaluating arguments in Krivine
- Wrong de Bruijn index counting
- Forgetting IReturn in SECD closures
- Confusing evaluation order

---

## Debugging Checklist

1. Is the environment captured in closures?
2. Are frames pushed/popped in correct order?
3. Is the closure's environment extended (not current)?
4. For SECD: Are de Bruijn indices counting outward?
5. For Krivine: Are arguments pushed as thunks?

---

## Connection to Real Systems

**CEK → Modern Interpreters**
- JavaScript V8, SpiderMonkey
- Python eval loop
- Scheme interpreters

**SECD → Virtual Machines**
- OCaml's ZINC machine
- Java bytecode
- WebAssembly

**Krivine → Lazy Evaluation**
- GHC's STG machine (+ memoization)
- Haskell runtime

---

## Next Steps

- **Chapter 18 (NbE)**: Normalization without explicit reduction
- **Chapter 20 (Denotational Semantics)**: Mathematical meaning

---

## Further Reading

- Landin (1964): Original SECD paper
- Plotkin (1975): Call-by-name vs call-by-value
- Krivine (2007): The Krivine machine
- Danvy & Millikin (2008): Rational deconstruction of SECD
- Biernacka & Danvy (2007): Framework for environment machines
