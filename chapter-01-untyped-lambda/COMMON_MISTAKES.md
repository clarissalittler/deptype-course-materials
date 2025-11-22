# Chapter 1: Common Mistakes and How to Avoid Them

## Introduction

Lambda calculus looks deceptively simple - just three syntactic forms! But beginners consistently make the same mistakes. This guide identifies these pitfalls and shows you how to avoid them.

**Use this guide**:
- When your reductions give unexpected results
- When exercise tests fail mysteriously
- When something "just doesn't work"
- As a reference while doing exercises

---

## Mistake #1: Variable Capture (THE BIG ONE)

### The Mistake

**Problem**: Performing substitution without checking for variable capture.

**Wrong**:
```
[y ↦ x](λx. y)  =  λx. x   ❌ WRONG!
```

**Why it's wrong**: The free variable `y` became bound by `λx` after substitution! This completely changes the meaning of the term.

Before: `λx. y` - function that ignores argument, returns `y` (from outer scope)
After: `λx. x` - function that returns its argument

These are totally different functions!

### How to Recognize It

You're at risk of variable capture when:
1. You're substituting `[x ↦ s]t`
2. AND `s` contains a free variable (say `y`)
3. AND `t` contains a lambda binding that variable (`λy`)

**Example**:
```
[z ↦ x](λx. λy. z)
```
Danger! We're substituting `x` (which contains free variable `x`), and the term has `λx`.

### How to Fix It

**Always α-convert first when there's danger**:

```
[y ↦ x](λx. y)
```

Step 1: Recognize danger (substituting x, and there's λx)
Step 2: Rename the bound variable
```
λx. y  →  λz. y   (α-conversion)
```
Step 3: Now substitute safely
```
[y ↦ x](λz. y)  =  λz. x  ✓ CORRECT
```

### Detection Strategy

Before any substitution `[x ↦ s]t`:
1. Compute `FV(s)` (free variables of what you're substituting)
2. Look for any `λy` in `t` where `y ∈ FV(s)`
3. If found: α-convert those lambdas first
4. Then substitute

### Practice Problems

Try these (answers below):
1. `[y ↦ x](λx. x y)`
2. `[x ↦ y](λy. x)`
3. `[z ↦ x](λx. λy. z x)`

<details>
<summary>Answers</summary>

1. `[y ↦ x](λx. x y)` - Danger! Need α-conversion
   - `λx. x y` → `λa. a y` (rename x to a)
   - `[y ↦ x](λa. a y)` = `λa. a x` ✓

2. `[x ↦ y](λy. x)` - Danger! Need α-conversion
   - `λy. x` → `λb. x` (rename y to b)
   - `[x ↦ y](λb. x)` = `λb. y` ✓

3. `[z ↦ x](λx. λy. z x)` - Danger! Need α-conversion
   - `λx. λy. z x` → `λa. λb. z a` (rename both)
   - `[z ↦ x](λa. λb. z a)` = `λa. λb. x a` ✓
</details>

---

## Mistake #2: Wrong Precedence/Associativity

### The Mistake

**Problem**: Mis-parsing terms due to wrong precedence rules.

**Wrong**:
```
λx. x y  =  (λx. x) y   ❌
f g h    =  f (g h)      ❌
```

**Correct**:
```
λx. x y  =  λx. (x y)   ✓
f g h    =  (f g) h      ✓
```

### The Rules

**Rule 1: Application is LEFT-associative**
```
a b c d  =  ((a b) c) d
```

Think: Currying. `f x y` means "apply f to x, then apply result to y"

**Rule 2: Abstraction extends RIGHT as far as possible**
```
λx. λy. x y  =  λx. (λy. (x y))
λx. x y      =  λx. (x y)
```

**Rule 3: Application binds tighter than abstraction**
```
λx. x y  ≠  (λx. x) y
λx. x y  =  λx. (x y)
```

### Common Misreadings

| Written | WRONG Parsing | CORRECT Parsing |
|---------|---------------|-----------------|
| `λx. x x` | `(λx. x) x` | `λx. (x x)` |
| `f g h` | `f (g h)` | `(f g) h` |
| `λx. λy. x y z` | `(λx. λy. x) y z` | `λx. (λy. ((x y) z))` |

### How to Fix It

**Use parentheses liberally when writing**:
```
Instead of: λx. f x
Write: λx. (f x)    [until you're confident]
```

**When parsing, work from left to right for applications**:
```
f g h i
= ((f g) h) i
  ^^^^ First
= (((f g) h) i)
   ^^^^^^^ Second
```

**For abstractions, find where they end**:
```
λx. something
    ^^^^^^^^^ Everything from here to end (or close paren)
```

### Practice Problems

Parse these (answers below):
1. `λf. λx. f x`
2. `f g h i`
3. `λx. x y z`
4. `(λx. x) y z`

<details>
<summary>Answers</summary>

1. `λf. (λx. (f x))`
2. `(((f g) h) i)`
3. `λx. ((x y) z)`
4. `((λx. x) y) z` - Note: parentheses force different parsing!
</details>

---

## Mistake #3: Substituting Bound Variables

### The Mistake

**Problem**: Substituting variables that are bound (shadowed).

**Wrong**:
```
[x ↦ a](λx. x)  =  λx. a   ❌
```

**Correct**:
```
[x ↦ a](λx. x)  =  λx. x   ✓  (x is bound, don't substitute!)
```

### Why It Happens

Beginners see `x` and substitute it everywhere, forgetting that `λx` creates a new scope.

### The Rule

**Never substitute a variable in a scope where it's shadowed**:
```
[x ↦ s](λx. t)  =  λx. t   (x is shadowed, DON'T substitute in t)
```

Think of it like:
```javascript
let x = "outer";
function foo(x) {  // This x shadows outer x
  return x;        // Refers to parameter, not outer variable
}
```

### Visualization

```
[x ↦ a] applied to:

λy. x        → λy. a     ✓ (x is free here)
λx. x        → λx. x     ✓ (x is bound by this λx, leave it alone)
λx. y x      → λx. y x   ✓ (x in body is bound by λx)
λy. λx. x    → λy. λx. x ✓ (inner x is bound by inner λx)
```

### Practice Problems

Evaluate these (answers below):
1. `[x ↦ y](λx. λy. x)`
2. `[a ↦ b](λa. a a)`
3. `[x ↦ z](λy. λx. y x)`

<details>
<summary>Answers</summary>

1. `λx. λy. x` - Outer λx shadows x, so no substitution
2. `λa. a a` - λa shadows a, so no substitution
3. `λy. λx. y x` - Inner λx shadows x; but y is free in outer scope... wait! Need to check if there's capture.
   - Actually: The x in `y x` is bound by `λx`, so it doesn't get substituted
   - The y is free and not affected by our substitution `[x ↦ z]`
   - Result: `λy. λx. y x` (unchanged)
</details>

---

## Mistake #4: Wrong Evaluation Order

### The Mistake

**Problem**: Not following the evaluation strategy consistently.

**Example with Call-by-Value**:
```
(λx. λy. y) ((λz. z z) (λz. z z))
```

**Wrong (not following CBV)**:
- Reduce outer application first → `λy. y` ❌

**Correct (following CBV)**:
- Must evaluate argument first → loops forever ✓

### The Strategies

**Call-by-Value**: Arguments before application
```
(λx. t) s
         ^ Reduce s to a value first!
         Then apply
```

**Normal-Order**: Leftmost-outermost first
```
(λx. t) s
^^^^^^^^^ This is leftmost-outermost
         Substitute immediately
```

### How to Avoid It

**Be explicit about which strategy you're using**:
- Write "Using call-by-value:" at the top of your work
- Follow the rules mechanically
- When in doubt, use normal-order (it's simpler)

### Recognition Example

Term: `(λx. λy. y) ((λa. a a) (λa. a a)) v`

**Call-by-Value**:
1. Try to reduce argument `(λa. a a) (λa. a a)`
2. This reduces to itself → infinite loop
3. **Never reaches the outer function**

**Normal-Order**:
1. Reduce leftmost: `(λx. λy. y) ...` →  `(λy. y) v`
2. Reduce again: `v`
3. **Terminates!**

---

## Mistake #5: Confusing Values and Normal Forms

### The Mistake

**Problem**: Thinking a term is "done" when it's not.

**Example**:
```
λx. (λy. y) x
```

**Wrong**: "It's a lambda, so it's in normal form" ❌

**Correct**: "There's a redex inside!" ✓

The redex `(λy. y) x` can reduce to `x`, giving `λx. x`.

### The Rule

A term is in **normal form** if:
- No β-redexes exist anywhere (including inside lambdas)

A term is a **value** (in call-by-value) if:
- It's a lambda abstraction (and we don't reduce under lambdas in CBV)

These are different!

### Examples

| Term | Value (CBV)? | Normal Form? |
|------|--------------|--------------|
| `x` | No | Yes |
| `λx. x` | Yes | Yes |
| `λx. (λy. y) x` | Yes (CBV doesn't look inside) | No (has redex inside) |
| `(λx. x) y` | No | No |
| `x y` | No | Yes (if x is a variable, can't reduce) |

### How to Avoid It

Check **everywhere** for redexes:
- Inside lambda bodies
- In both parts of applications
- Nested deeply

Don't stop until you've looked everywhere!

---

## Mistake #6: Forgetting Church Encoding Semantics

### The Mistake

**Problem**: Implementing Church encodings without understanding what they represent.

**Wrong**:
```
and = λp. λq. p q q   ❌
```

**Correct**:
```
and = λp. λq. p q false   ✓
```

### Why It Matters

Church encodings represent data by behavior:
- Booleans: **choose between two options**
- Numbers: **apply function n times**
- Lists: **fold over elements**

If you don't understand the behavior, you'll get the encoding wrong.

### Boolean Example

`true = λt. λf. t` - "selects first argument"

For `and p q`:
- If `p` is `true`: return `q` (whatever it is)
- If `p` is `false`: return `false`

So: `and = λp. λq. p q false`

When `p = true`: `true q false` → `q` ✓
When `p = false`: `false q false` → `false` ✓

### Number Example

Church numeral `n` means "apply f n times to x":
```
0 = λf. λx. x
1 = λf. λx. f x
2 = λf. λx. f (f x)
```

For `plus m n`:
- Apply f `n` times to x: `n f x`
- Then apply f `m` more times: `m f (n f x)`

So: `plus = λm. λn. λf. λx. m f (n f x)`

### How to Avoid It

1. **Understand the representation first**
2. **Think about behavior, not structure**
3. **Test with concrete examples**
4. **Verify with the REPL**

---

## Mistake #7: Infinite Loops (Not Recognizing Non-Termination)

### The Mistake

**Problem**: Expecting all terms to terminate.

**Example**:
```
(λx. x x) (λx. x x)
→ (λx. x x) (λx. x x)
→ (λx. x x) (λx. x x)
→ ...
```

This is `Ω` (omega) - it loops forever!

### Warning Signs

**These patterns often loop**:
- Self-application: `(λx. x x) ...`
- Y combinator without base case: `Y f`
- Recursive functions called on wrong values

### How to Detect

Before evaluating:
1. **Look for self-application** `(λx. ... x x ...)`
2. **Check for infinite unrolling** (Y combinator)
3. **Verify base cases** (in recursive functions)

### When Loops are Good

Sometimes non-termination is intentional:
- Y combinator (for recursion)
- Recursive functions (they loop until base case)

Just make sure you have a base case!

### How to Avoid Accidental Loops

- **Test on small inputs first**
- **Use the REPL with timeouts**
- **Trace first few steps** manually
- **Add base cases** to recursive functions

---

## Mistake #8: Misunderstanding Currying

### The Mistake

**Problem**: Trying to pass multiple arguments at once.

**Wrong Thinking**:
```
λ(x, y). x + y   ❌ (not valid lambda calculus!)
```

**Correct**:
```
λx. λy. x + y   ✓ (curried)
```

### What is Currying?

Every function takes exactly ONE argument. To take multiple arguments, return a function that takes the next argument.

```
λx. λy. x + y
```

Is really:
```
λx. (λy. x + y)
     ^^^^^^^^^^^ This is the return value!
```

### How Multi-Argument Application Works

```
(λx. λy. x) a b
```

Step 1: Apply to first argument
```
(λx. λy. x) a  →  λy. a
```

Step 2: Apply result to second argument
```
(λy. a) b  →  a
```

### Partial Application

Because of currying, you can apply arguments one at a time:
```
add = λx. λy. x + y
add5 = add 5           (partially applied)
add5 3  →  8           (fully applied)
```

---

## Mistake #9: Not Using the REPL

### The Mistake

**Problem**: Trying to trace complex reductions by hand when you don't need to.

**Solution**: Use the REPL!

### REPL Features You Should Use

```bash
stack run
```

**Essential commands**:
- `:step <term>` - See reduction step-by-step
- `:type <term>` - Understand structure
- `:examples` - See working examples
- `:let name = term` - Name terms for reuse

### Example Session

```
λ> :step (\x. \y. x) a b
(λx. λy. x) a b
→ (λy. a) b
→ a

λ> :let id = \x. x
Defined: id

λ> :step id (id (\z. z))
id (id (λz. z))
→ id (λz. z)
→ λz. z
```

### When to Use the REPL

- **Checking your work**: Verify manual reductions
- **Exploring**: Try variations of examples
- **Debugging**: When exercises fail, test pieces
- **Learning**: Experiment with Church encodings

---

## Mistake #10: Skipping Steps

### The Mistake

**Problem**: Trying to do too much in one reduction step.

**Wrong**:
```
(λx. λy. x) a b  →  a   (skipped intermediate step!)
```

**Correct**:
```
(λx. λy. x) a b
→ (λy. a) b      (first application)
→ a              (second application)
```

### Why It Matters

Skipping steps leads to:
- Mistakes in substitution
- Missing variable capture
- Wrong evaluation order
- Lost understanding

### How to Avoid It

**Write every single reduction**:
```
term1
→ term2   (because rule X)
→ term3   (because rule Y)
→ result
```

**Annotate your steps**:
```
(λx. x x) (λy. y)
→ (λy. y) (λy. y)    [β-reduction: x ↦ (λy. y)]
→ λy. y              [β-reduction: y ↦ (λy. y)]
```

This seems tedious, but it **prevents mistakes**!

---

## Debugging Checklist

When something goes wrong:

**1. Variable Capture?**
- [ ] Did I α-convert before substituting?
- [ ] Did I check FV(s) against bound variables in t?

**2. Parsing?**
- [ ] Did I parse applications left-to-right?
- [ ] Did I extend λ to the right?
- [ ] Did I use parentheses to clarify?

**3. Shadowing?**
- [ ] Did I substitute a bound variable by mistake?
- [ ] Did I check if λx shadows x?

**4. Evaluation Strategy?**
- [ ] Am I using call-by-value or normal-order?
- [ ] Did I reduce arguments first (if CBV)?
- [ ] Did I reduce leftmost-outermost (if normal)?

**5. Church Encoding?**
- [ ] Do I understand what this encoding represents?
- [ ] Did I test with concrete examples?
- [ ] Does the behavior match the specification?

**6. Infinite Loop?**
- [ ] Is there self-application?
- [ ] Is there a base case?
- [ ] Should this terminate?

**7. Using Tools?**
- [ ] Have I tested in the REPL?
- [ ] Have I used `:step` to trace?
- [ ] Have I run the test suite?

---

## Quick Reference: Substitution Algorithm

To compute `[x ↦ s]t` safely:

```
1. If t is x:
   return s

2. If t is some other variable y:
   return y

3. If t is (λx. body):
   return (λx. body)    [x is shadowed!]

4. If t is (λy. body) where y ≠ x:
   a. Check if y ∈ FV(s)
   b. If yes: α-convert first!
      (λy. body) → (λz. [y ↦ z]body)  [z fresh]
      Then: return (λz. [x ↦ s][y ↦ z]body)
   c. If no: return (λy. [x ↦ s]body)

5. If t is (t1 t2):
   return ([x ↦ s]t1) ([x ↦ s]t2)
```

**Fresh variable**: Pick a name that doesn't appear anywhere in the term.

---

## Summary: Top 5 Mistakes and Fixes

| # | Mistake | Fix |
|---|---------|-----|
| 1 | Variable capture | Always α-convert when FV(s) conflicts with bound vars |
| 2 | Wrong precedence | Application left-assoc, λ extends right |
| 3 | Substituting bound vars | Check if variable is shadowed before substituting |
| 4 | Wrong eval strategy | Be explicit: CBV or normal-order |
| 5 | Skipping steps | Write every single reduction step |

**Remember**: Lambda calculus is simple in theory, tricky in practice. Take your time, write out steps, and use the REPL!

---

## What's Next?

- Review these mistakes periodically
- Keep this guide handy while doing exercises
- When tests fail, check this list
- Use the REPL to verify your understanding

**Ready to practice?** Head to `exercises/EXERCISES.md` and test your knowledge!
