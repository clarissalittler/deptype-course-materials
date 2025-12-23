# Chapter 17: Abstract Machines - Frequently Asked Questions

## Conceptual Questions

### Q: Why are they called "abstract" machines?

**A:** They're abstract in the sense that they describe evaluation *conceptually* without being tied to physical hardware. Unlike real machines with registers, memory addresses, and instruction sets, abstract machines work directly on syntax (terms) and semantic concepts (environments, closures).

They're more concrete than substitution-based semantics (which hide implementation details) but more abstract than real machine code.

### Q: What's the relationship between abstract machines and interpreters?

**A:** An abstract machine is essentially a *small-step operational semantics* that's close to an actual interpreter implementation. The machine's `step` function corresponds directly to an interpreter's evaluation loop:

```haskell
-- Abstract machine
run :: State -> Value
run (Done v) = v
run s = run (step s)

-- Interpreter (similar structure!)
eval :: Term -> Env -> Value
eval (Var x) env = lookup x env
eval (App f t) env = apply (eval f env) (eval t env)
...
```

Many real interpreters are designed as abstract machines internally.

### Q: Why use environments instead of substitution?

**A:** Two main reasons:

1. **Efficiency**: Substitution traverses the entire term body, copying subterms. With large terms, this is O(n) work per substitution. Environments only do O(1) work to extend them; lookup is O(n) in the worst case but often O(1) with hashtables.

2. **Sharing**: With environments, multiple closures can share parts of the same environment. Substitution creates separate copies.

```
Substitution: ((λx.x) t)[y:=big] → (λx.x) t[y:=big]  -- copies "big"
Environment: no copying needed
```

### Q: What exactly is a closure?

**A:** A closure is a function value that "closes over" its free variables by capturing the environment where it was defined:

```
Closure = (Lambda body, Environment)
```

Example:
```
let x = 10 in λy. x + y
```

The lambda `λy. x + y` has free variable `x`. The closure is:
```
⟨λy. x + y, {x ↦ 10}⟩
```

When this closure is later called with argument 5:
```
(⟨λy. x + y, {x ↦ 10}⟩) 5
→ evaluate (x + y) with env = {x ↦ 10, y ↦ 5}
→ 15
```

### Q: What is a continuation, intuitively?

**A:** A continuation is "the rest of the computation" - what you're going to do with the current result.

In `(1 + 2) * 3`:
- When evaluating `1 + 2`, the continuation is "multiply the result by 3"
- When evaluating `1`, the continuation is "add 2 to the result, then multiply by 3"

The CEK machine makes this explicit as a list of frames:
```
[FMul2 3]           -- "multiply by 3"
[FAdd2 1, FMul2 3]  -- "add 2, then multiply by 3"
```

Continuations are powerful because you can save them, restore them, or even call them multiple times (first-class continuations, call/cc).

## Comparison Questions

### Q: When would I use CEK vs SECD vs Krivine?

**A:**

**CEK**: Best for teaching and when you need first-class continuations. It's simple, direct, and explicit about control flow. Good starting point for implementing interpreters.

**SECD**: Best when you want a bytecode compiler. The compilation phase separates concerns and enables optimizations. Inspired OCaml's ZINC, Java bytecode, etc.

**Krivine**: Best for lazy languages. If you're implementing something like Haskell where arguments shouldn't be evaluated until needed, start here. Add memoization to get call-by-need.

### Q: What's the difference between call-by-value, call-by-name, and call-by-need?

**A:**

**Call-by-value** (CEK, SECD):
- Evaluate arguments *before* the function is called
- Each argument evaluated exactly once
- Used by: ML, Scheme, Python, JavaScript

**Call-by-name** (Krivine):
- Arguments are *not* evaluated until used
- May be evaluated multiple times if used multiple times
- `(λx. x + x) expensive` evaluates `expensive` twice

**Call-by-need** (Haskell):
- Like call-by-name, but results are memoized
- Each argument evaluated *at most* once
- `(λx. x + x) expensive` evaluates `expensive` once, shares result

### Q: Why doesn't Krivine have explicit continuation frames?

**A:** In call-by-name, the "continuation" is implicit in the stack of thunks. Each thunk represents a delayed argument that might need the current result.

For `f g x`:
- Stack after processing: `[thunk(x), thunk(g)]`
- When `f` is a lambda, it binds the top thunk
- The remaining stack is the implicit continuation

CEK needs explicit frames because in call-by-value, we need to track *where* we are in evaluating each subterm. Krivine just pushes thunks and lets the lambda structure guide control flow.

## Implementation Questions

### Q: How do I add pairs/tuples to CEK?

**A:** Add new term forms, value forms, and frames:

```haskell
-- Terms
data Term = ... | Pair Term Term | Fst Term | Snd Term

-- Values
data Value = ... | VPair Value Value

-- Frames
data Frame = ... | FPair1 Term Env | FPair2 Value | FFst | FSnd

-- Transitions
step (Eval (Pair t1 t2), env, k) =
  Eval t1 env (FPair1 t2 env : k)

step (Apply (FPair1 t2 env : k), v1) =
  Eval t2 env (FPair2 v1 : k)

step (Apply (FPair2 v1 : k), v2) =
  Apply k (VPair v1 v2)

step (Eval (Fst t), env, k) =
  Eval t env (FFst : k)

step (Apply (FFst : k), VPair v1 _) =
  Apply k v1
```

### Q: How do I add recursion/fix to CEK?

**A:** The fix-point combinator:

```haskell
-- Term
data Term = ... | Fix Term  -- fix (λf. ...)

-- Transition
step (Eval (Fix t), env, k) = Eval t env (FFix : k)

step (Apply (FFix : k), VClosure x body cenv) =
  let fixval = VClosure x body (extend x fixval cenv)  -- cyclic!
  in Apply k fixval
```

The key is creating a cyclic environment where the function is bound to itself. Haskell's laziness makes this work!

### Q: How do I implement the SECD Dump?

**A:** The Dump saves machine state before function calls:

```haskell
type Dump = [(Stack, Env, Code)]

-- IApply: save current state, start executing closure
exec (IApply : c, Closure code cenv : v : s, e, d) =
  ([], v : cenv, code, (s, e, c) : d)

-- IReturn: restore saved state, push result
exec (IReturn : _, v : s, e, (s', e', c') : d) =
  (v : s', e', c', d)
```

### Q: How would I add memoization to Krivine for call-by-need?

**A:** Use mutable thunks that get overwritten after evaluation:

```haskell
data Thunk = Unevaluated Term Env | Evaluated Value

-- When looking up variable, check if already evaluated
step (State (Var x) env stack) =
  case lookup x env of
    Unevaluated t e ->
      -- Evaluate and remember to update
      State t e (UpdateFrame x env : stack)
    Evaluated v ->
      -- Already computed, use cached value
      returnValue v stack

-- When value is produced with UpdateFrame
step (ReturnValue v (UpdateFrame x env : stack)) =
  update x (Evaluated v) env  -- Mutate!
  returnValue v stack
```

## Troubleshooting

### Q: My machine loops forever on a simple example. What's wrong?

**A:** Common causes:

1. **Forgot terminal case**: Check that `Apply [] v` returns `v`
2. **Wrong frame order**: Are you pushing frames for later work?
3. **Not extending environment**: Variable lookup failing?
4. **Infinite loop in source**: Does the term actually terminate?

Debug by adding tracing:
```haskell
run s = do
  print s
  case step s of
    Done v -> return v
    s' -> run s'
```

### Q: My closures are looking up wrong values. Help!

**A:** Almost certainly an environment problem:

1. Are you capturing the environment when creating closures?
2. Are you extending the *closure's* environment when applying?
3. Are you using the right environment in frames like `FApp1 t env`?

Add debug output showing environments at each step.

### Q: SECD is giving wrong results for nested functions.

**A:** Check de Bruijn indices:

1. Are you computing indices correctly during compilation?
2. Remember: innermost binder = index 0
3. Is the environment being extended in the right order?

Example:
```
λx. λy. x  -- x should be index 1, not 0!
```

### Q: Krivine evaluates things it shouldn't.

**A:** Make sure you're:

1. Pushing thunks (term + env), not values
2. Only evaluating when looking up a variable
3. Not accidentally forcing thunks during lambda application

The only place evaluation happens is variable lookup!
