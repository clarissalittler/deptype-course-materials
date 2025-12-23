# Chapter 13: Gradual Typing - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce gradual typing concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Consistency Checking ⭐
Determine if these type pairs are consistent:

a) `Nat ~ ?`
b) `? ~ ? -> Bool`
c) `(Nat -> Bool) ~ (? -> ?)`
d) `(? -> Nat) ~ (Bool -> ?)`
e) `Nat ~ Bool`
f) `? ~ ?`

### Problem 1.2: Type Precision ⭐
Order these types by precision (⊑):

a) `?`, `Nat`, `Nat -> Bool`
b) `? -> ?`, `Nat -> ?`, `Nat -> Bool`
c) `(? -> ?) -> ?`, `(Nat -> Bool) -> Nat`

### Problem 1.3: Ground Types ⭐
What is the ground type for each?

a) `Bool`
b) `Nat -> Nat`
c) `(Nat -> Bool) -> Bool`
d) `Unit`

### Problem 1.4: Basic Cast Semantics ⭐
What do these casts reduce to?

a) `<Nat => Nat> 42`
b) `<Bool => ?> true`
c) `<? => Bool> (<Bool => ?> true)`
d) `<? => Nat> (<Bool => ?> true)`

### Problem 1.5: Blame Labels ⭐
In this term, identify all blame labels:

```
(<Nat => ?>^l1 42) : ?
let f = <? => Nat -> Bool>^l2 x in f 0
```

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Cast Insertion ⭐⭐
Insert casts for these terms:

a) `(λx : ?. x + 1) 42`
b) `(λf : ?. f 0) (λx : Nat. succ x)`
c) `let x : ? = true in (if x then 0 else 1)`
d) `(λg : Nat -> ?. g 5) (λy : ?. y)`

Show the fully elaborated terms with all casts and blame labels.

### Problem 2.2: Consistency Proofs ⭐⭐
Prove or disprove these consistency relations:

a) `(Nat -> Bool) ~ (? -> Bool)`
b) `(? -> ?) ~ (Nat -> Nat)`
c) `((Nat -> ?) -> Bool) ~ ((? -> Nat) -> ?)`
d) `Unit ~ ?`

For each, either show a derivation or explain why it fails.

### Problem 2.3: Cast Reduction Traces ⭐⭐
Show step-by-step reduction for:

a) `<? => Nat> (<Nat => ?> 42)`
b) `<Nat -> Bool => ?> (λx : Nat. true)`
c) `(<? -> ? => Nat -> Bool> (<Nat -> Bool => ?> f)) 0`

### Problem 2.4: Blame Tracking ⭐⭐
For each scenario, determine where blame occurs:

a)
```
let f : Nat -> Nat = λx. x + 1
let g : ? -> ? = f
g true
```

b)
```
let h : ? = λx. x
let i : Nat -> Bool = h
i 42
```

c)
```
let safe : Nat -> Nat = λn. n
let unsafe : ? = safe
(unsafe true) : Nat
```

### Problem 2.5: Gradual Migration Strategy ⭐⭐
Given this dynamic function:

```
process : ? -> ? -> ?
process config data =
  if config.debug
  then trace data
  else compute data
```

Design a 4-phase migration plan to make it fully typed. Show intermediate types.

### Problem 2.6: Meet Operation ⭐⭐
Compute the **meet** (most precise common type) for:

a) `Nat` and `?`
b) `Nat -> Bool` and `? -> ?`
c) `?` and `Nat -> ?`
d) `Bool` and `Nat`

The meet is the most precise type consistent with both.

### Problem 2.7: Blame Polarity ⭐⭐
Explain the blame polarity (positive/negative) for each cast:

```
<T₁ -> T₂ => S₁ -> S₂>^l f = λx. <T₂ => S₂>^l (f (<S₁ => T₁>^l̄ x))
```

a) Why does the result cast use positive label `l`?
b) Why does the argument cast use negative label `l̄`?
c) Give an example where each polarity is blamed.

### Problem 2.8: Dynamic Guarantee ⭐⭐
Consider these three versions:

```
v1 = (λx : ?. λy : ?. x + y) 2 3
v2 = (λx : Nat. λy : ?. x + y) 2 3
v3 = (λx : Nat. λy : Nat. x + y) 2 3
```

a) Do they all type check?
b) Do they produce the same value?
c) Show where casts are inserted in each.
d) Which can fail at runtime?

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Non-Transitivity of Consistency ⭐⭐⭐
Prove that consistency is NOT transitive by:

a) Giving a counterexample
b) Explaining why transitivity would break gradual typing
c) Showing what would happen if we made it transitive

### Problem 3.2: Space-Efficient Casts ⭐⭐⭐
Naive cast semantics can create "cast chains":

```
<? => Nat> (<Nat => ?> (<? => Nat> (<Nat => ?> 42)))
```

a) Show this reduces but creates intermediate casts
b) Design a **coercion** representation that is space-efficient
c) Define composition of coercions: `⌈c₁⌉; ⌈c₂⌉`

### Problem 3.3: Gradual Polymorphism ⭐⭐⭐
Extend gradual typing to polymorphic types:

a) What should `∀α. α -> α` be consistent with?
b) Define consistency for `∀α. T`:
   ```
   ∀α. T ~ ???
   ```
c) How do you cast `<∀α. α -> α => ?>` ?
d) Show an example of gradual parametricity violation

### Problem 3.4: Blame Soundness ⭐⭐⭐
Prove (informally) the **Blame Theorem**:

> If `⊢ t : T` and `t` contains no `?`, then `t ⇓ v` or `t ⇓ blame^l` where `l` is negative.

Steps:
a) Define what it means for a term to be "fully typed"
b) Show fully typed terms generate no positive casts
c) Conclude fully typed terms can only receive negative blame

### Problem 3.5: Gradual Subtyping ⭐⭐⭐
Combine gradual typing with subtyping:

a) Define the **consistent subtyping** relation `<:~`
b) Show it satisfies: `T <: S` implies `T <:~ S`
c) Show it satisfies: `T ~ S` implies `T <:~ S`
d) Give an example where `T <:~ S` but neither `T <: S` nor `T ~ S`

### Problem 3.6: Blame and Effects ⭐⭐⭐
Extend blame tracking to effectful computations:

a) Define `?ₑ` (dynamic effect)
b) Show consistency for effect types: `{E₁} T ~ {E₂} S`
c) Design cast semantics for effect casts
d) Show how blame interacts with exception handling

---

## Debugging Exercises (30 minutes)

### Debug 1: Cast Insertion Error ⭐
Student wrote:
```
(λx : ?. x) 42  -- No casts needed, x is dynamic!
```
Why is this incomplete? Where should casts go?

### Debug 2: Blame Direction Confusion ⭐⭐
Student's function:
```
applyDyn : (? -> Nat) -> ? -> Nat
applyDyn f x = f x
```

They claim: "If `x` is the wrong type, `f` gets blamed."

Is this correct? Trace the blame.

### Debug 3: Consistency Mistake ⭐⭐
Student claims:
```
Nat ~ ?       (correct)
? ~ Bool      (correct)
Therefore: Nat ~ Bool  (by transitivity)
```
What's wrong with this reasoning?

### Debug 4: Ground Type Error ⭐⭐
Student implements projection:
```
<? => Nat -> Bool> v =
  case v of
    <Nat -> Bool => ?> f -> f
    _ -> blame
```
Why is this wrong? What's the correct implementation?

### Debug 5: Meet Confusion ⭐⭐
Student computes:
```
meet(Nat, ?) = ?         -- Wrong!
```
What's the correct meet? Why?

---

## Code Review Exercises (30 minutes)

### Review 1: Gradual Migration ⭐⭐
A student is migrating this code:

```
-- Original
processData : ? -> ?
processData input =
  let parsed = parseJSON input
  let validated = validate parsed
  in transform validated

-- Student's migration
processData : String -> ?
processData input =
  let parsed = parseJSON input
  let validated = validate parsed
  in transform validated
```

Review:
- Is this a good first step?
- What should be typed next?
- What's the final fully-typed version?

### Review 2: Cast Optimization ⭐⭐
Two implementations of dynamic application:

**Version A**:
```
applyDyn f x = (<? => Nat -> Bool> f) (<Nat => ?> x)
```

**Version B**:
```
applyDyn f x = f x
```

Both have type `? -> ? -> ?`. Which is better and why?

### Review 3: Blame Design ⭐⭐⭐
Student proposes:
```
-- Instead of blame labels, use stack traces
blame^l  →  blame (getCurrentStackTrace())
```

Critique:
- Does this preserve the blame theorem?
- What information is lost?
- What about separate compilation?

---

## Real-World Scenarios (45 minutes)

### Scenario 1: TypeScript Migration ⭐⭐
You have this JavaScript code:
```javascript
function processUser(user) {
  if (user.admin) {
    return user.permissions.map(p => p.toUpperCase());
  }
  return [];
}
```

Migrate to TypeScript in 3 phases:
a) Add minimal types (use `any` where needed)
b) Type the structure but keep some `any`
c) Fully type with no `any`

### Scenario 2: Python Type Hints ⭐⭐
Add type hints gradually:
```python
def compute(config, data):
    if config['mode'] == 'fast':
        return fast_compute(data)
    else:
        return slow_compute(data)
```

Show 3 versions with increasing precision.

### Scenario 3: FFI Boundary ⭐⭐⭐
You're calling a C library from a gradually-typed language:

```
-- C signature (untyped)
external parse : ? -> ?

-- Your gradually-typed wrapper
safeParse : String -> Option ParseResult
safeParse input = ???
```

Design a safe wrapper that:
a) Validates input type
b) Checks result type
c) Provides good blame messages

---

## Solutions

### Warm-Up Solutions

**1.1**: a) Yes, b) Yes, c) Yes, d) Yes, e) No, f) Yes

**1.2**:
- a) `?` ⊑ `Nat`, but `?` and `Nat -> Bool` are incomparable
- b) `? -> ?` ⊑ `Nat -> ?` ⊑ `Nat -> Bool`
- c) `(? -> ?) -> ?` ⊑ `(Nat -> Bool) -> Nat`

**1.3**: a) `Bool`, b) `? -> ?`, c) `? -> ?`, d) `Unit`

**1.4**:
- a) `42`
- b) `<Bool => ?> true` (value form)
- c) `true`
- d) `blame^l`

**1.5**: Labels are `l1` and `l2`

### Standard Solutions

**2.1**:
```
a) (λx : ?. (<? => Nat>^body x) + 1) (<Nat => ?>^arg 42)
b) (λf : ?. (<? => Nat -> Nat>^body f) (<Nat => ?>^arg 0))
     (<Nat->Nat => ?>^arg (λx : Nat. succ x))
c) let x : ? = <Bool => ?>^bind true in
   (if (<? => Bool>^use x) then 0 else 1)
d) (λg : Nat -> ?. g (<Nat => ?>^arg 5))
     (<Nat->? => Nat->?>^arg (λy : ?. <? => ?>^ret y))
```

**2.2**: All are consistent. Derivations follow consistency rules.

**2.3**:
```
a) <? => Nat> (<Nat => ?> 42)
   → 42

b) <Nat -> Bool => ?> (λx : Nat. true)
   → <Nat -> Bool => ? -> ?> (λx : Nat. true)
   → <? -> ? => ?> (λx : Nat. true)
   (value form with tag ? -> ?)
```

**2.4**:
```
a) Blame at body of f when casting ? => Nat
b) Blame at body of h when casting ? => Bool
c) Blame when casting ? => Nat on result
```

**2.5**:
```
Phase 1: config : Config, data : ?
Phase 2: config : Config, data : Data, return : ?
Phase 3: config : Config, data : Data, return : Result
Phase 4: Full types with specific Config/Data/Result types
```

**2.6**:
```
a) Nat
b) Nat -> Bool
c) Nat -> ?
d) None (inconsistent types have no meet)
```

**2.7**:
- a) Positive because we're checking the function's output
- b) Negative because we're checking what we give to the function
- c) Positive: function returns wrong type; Negative: we pass wrong argument

**2.8**:
- a) Yes, all type check
- b) Yes, all produce 5
- c) v1 has most casts, v3 has none
- d) v1 and v2 can fail; v3 cannot

### Challenge Solutions

**3.1**:
Counterexample: `Nat ~ ?` and `? ~ Bool` but `Nat ≁ Bool`.
Transitivity would make all types consistent, losing all static checking.

**3.2**:
Use coercion algebra: `c ::= id | G⇒? | ?⇒G | c₁→c₂ | c₁;c₂`
Composition: `(?⇒G);(G⇒?) = id`, etc.

**3.3**:
`∀α. T ~ ?` is consistent.
Polymorphic casts need runtime type application.
Example: `(Λα. λx:α. x) [Bool]` loses parametricity.

**3.4**:
Fully typed terms have no `?` in types. All casts are identity or come from other sources. Only negative blame possible.

**3.5**:
`T <:~ S` iff `∃ T', S'. T <: T' ~ S' <: S`
Example: `Nat <:~ ?` via `Nat <: Nat ~ ?`

**3.6**:
`?ₑ ~ E` for any effect E. Effect casts check at effect boundaries.

### Debug Solutions

**Debug 1**: Need `<Nat => ?>` on argument and `<? => ?>` on result.

**Debug 2**: Incorrect. `f` expects `?`, so no blame on `f`. If `f`'s body casts `?` to wrong type, then that cast is blamed.

**Debug 3**: Consistency is NOT transitive. This is fundamental to gradual typing.

**Debug 4**: Must go through ground type: `<? => ? -> ?>` first, then `<? -> ? => Nat -> Bool>`.

**Debug 5**: `meet(Nat, ?) = Nat` (most precise common type).

### Code Review Solutions

**Review 1**: Good first step. Next: type `parsed` and `validated`. Final: all intermediate types specified.

**Review 2**: Version B is better if fully dynamic context. Version A inserts unnecessary casts.

**Review 3**: Stack traces don't preserve separate compilation. Blame labels are compile-time, stack traces are runtime. Blame theorem requires static labels.

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 6 hard, 5 debug, 3 review, 3 scenarios

**Note**: These problems complement the main exercises. Focus on understanding gradual typing principles!
