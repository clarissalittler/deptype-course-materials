# Chapter 4: Hindley-Milner Type Inference - Frequently Asked Questions

## Table of Contents

1. [Conceptual Questions](#conceptual-questions)
2. [Let-Polymorphism Questions](#let-polymorphism-questions)
3. [Type Inference Questions](#type-inference-questions)
4. [Unification Questions](#unification-questions)
5. [Comparison Questions](#comparison-questions)
6. [Practical "I'm Stuck" Scenarios](#practical-im-stuck-scenarios)
7. [Advanced Questions](#advanced-questions)

---

## Conceptual Questions

### Q1: What's the main difference between Hindley-Milner and previous chapters?

**A**: **Automatic type inference!** In Chapter 2-3, you wrote:
```
\x:Nat. x      -- Must annotate type
```

In Hindley-Milner (Chapter 4):
```
\x. x          -- No annotation! Type is inferred
```

The type system figures out types automatically using **Algorithm W** (unification + substitution).

### Q2: What does "polymorphic" mean in this context?

**A**: A polymorphic function works for **multiple types**. Example:
```
id : ∀a. a → a
```
This means `id` works for:
- `id 42` (where `a = Int`)
- `id true` (where `a = Bool`)
- `id (\x. x)` (where `a = a' → a'`)

ONE function, MANY types! The `∀a` means "for any type a".

### Q3: What are "type variables" (α, β, etc.)?

**A**: Type variables represent **unknown types** that will be determined later:
```
\x. x    has type    α → α
```
The `α` means "we don't know what type yet, but input and output are the SAME type."

When you apply it:
```
(\x. x) 42    -- Now α = Int, so result type is Int
```

Think of type variables as placeholders that get filled in.

### Q4: What's a "principal type"?

**A**: The **most general** type for a term. For `\x. x`:
- `Int → Int` is A type (works)
- `Bool → Bool` is A type (works)
- `∀a. a → a` is the **principal type** (most general, works for all)

Hindley-Milner **always finds** the principal type!

### Q5: Why is type inference "complete" and "decidable"?

**A**:
- **Complete**: If a term has a type, HM will find it
- **Decidable**: HM always terminates (doesn't loop forever)

This is AMAZING! You get:
1. Full type safety
2. No annotations needed
3. Guaranteed to finish

System F (Chapter 5) sacrifices decidability for more expressiveness.

---

## Let-Polymorphism Questions

### Q6: What's the difference between `let` and `lambda`?

**A**: THIS IS THE KEY INSIGHT OF HINDLEY-MILNER!

**Let-bound variables are POLYMORPHIC**:
```
let id = \x. x in (id 1, id true)
✓ Works! id is used at TWO different types
```

**Lambda-bound variables are MONOMORPHIC**:
```
(\id. (id 1, id true)) (\x. x)
✗ Fails! id must have ONE type
```

### Q7: Why does `let` get special treatment?

**A**: Design choice in Hindley-Milner! The algorithm:
1. Infers type for `\x. x`: `α → α`
2. **Generalizes** to `∀a. a → a` for let-binding
3. Each use of `id` can **instantiate** `a` differently

Lambda variables don't get generalized - they must have one type throughout their scope.

### Q8: Can you explain "generalization" and "instantiation"?

**A**:
**Generalization** (let-binding):
```
\x. x    infers to    α → α
         generalizes to    ∀a. a → a
```
Free type variables become universally quantified.

**Instantiation** (usage):
```
id 42         -- Instantiate ∀a to Int: Int → Int
id true       -- Instantiate ∀a to Bool: Bool → Bool
```
Each use can pick a different type!

### Q9: What's the "value restriction"?

**A**: Only **values** can be polymorphic. Consider:
```
let f = (if true then \x. x else \y. y + 1) in ...
```

This is NOT a value (it's a conditional). If we made it polymorphic:
- `f 42` would need `Int → Int`
- `f true` would need `Bool → Bool`

But the conditional might compute to `\y. y + 1` which only works for `Int`!

Solution: Only syntactic values (lambdas, constructors) get generalized.

### Q10: Can I use let-bound variables at multiple types in the SAME expression?

**A**: YES! That's the power:
```
let id = \x. x in
let pair = \x. \y. (x, y) in
pair (id 1) (id true)

Works! id used at Int AND Bool
```

---

## Type Inference Questions

### Q11: How does Algorithm W work (intuition)?

**A**: Three main steps:

1. **Generate constraints**:
   ```
   For (\x. x + 1), generate:
   - x has type α (unknown)
   - + requires Int
   - So α must equal Int
   ```

2. **Unify constraints**:
   ```
   α = Int (solve the equations)
   ```

3. **Apply substitution**:
   ```
   Result type: Int → Int
   ```

Like solving algebraic equations, but with types!

### Q12: What is "unification"?

**A**: Finding substitutions that make types equal:
```
Unify (α → β) with (Int → Bool):
  α = Int
  β = Bool

Unify (α → α) with (Int → Bool):
  α = Int AND α = Bool
  ✗ Contradiction! Cannot unify
```

### Q13: What's an "occurs check"?

**A**: Prevents infinite types:
```
Unify α with (α → β):
  α = α → β
  α = (α → β) → β
  α = ((α → β) → β) → β
  ... INFINITE!
```

Occurs check: α cannot appear in the type it's being unified with.

Example where this matters:
```
\f. f f
```
This CANNOT be typed because we'd need `α = α → β` (infinite type).

### Q14: Why can't I type `\f. f f`?

**A**: Let's try:
```
f : α               (f is some type)
f f means f applied to f
  So f : α → β      (f is a function)
  And f : α         (f is also the argument)
```

Unifying `α → β` with `α` requires `α = α → β` - INFINITE TYPE!

The occurs check prevents this. Some terms simply cannot be typed in HM!

### Q15: What types CAN'T be inferred?

**A**: Terms that would require:
1. **Infinite types**: `\f. f f`
2. **Impredicative polymorphism**: Poly types instantiated with poly types
3. **Higher-rank types**: Polymorphic arguments

These need **System F** (Chapter 5) with explicit annotations.

---

## Unification Questions

### Q16: What's a "substitution"?

**A**: A mapping from type variables to types:
```
[α ↦ Int, β ↦ Bool]

Applied to (α → β) gives (Int → Bool)
```

Substitutions are the "solutions" to type equations.

### Q17: How do you compose substitutions?

**A**: Apply one after another:
```
S1 = [α ↦ β]
S2 = [β ↦ Int]

S2 ∘ S1 applied to α:
  First S1: α becomes β
  Then S2: β becomes Int
  Result: α ↦ Int
```

**Order matters!** S2 ∘ S1 ≠ S1 ∘ S2

### Q18: What's the "most general unifier" (MGU)?

**A**: The **least committed** substitution:
```
Unify (α → β) with (α → Int):

MGU: [β ↦ Int]
  (Only commits β, leaves α free)

NOT MGU: [α ↦ Bool, β ↦ Int]
  (Over-commits α unnecessarily)
```

Algorithm W always finds the MGU!

### Q19: Can all type pairs be unified?

**A**: NO! Examples that cannot unify:
```
Int with Bool              ✗ Different base types
α → β with Int             ✗ Function vs base type
α with α → α               ✗ Occurs check fails
(α → β) with (γ → δ → ε)   ✗ Different arities
```

Unification failure = type error!

---

## Comparison Questions

### Q20: Hindley-Milner vs System F?

**A**:

| Feature | Hindley-Milner (Ch4) | System F (Ch5) |
|---------|---------------------|----------------|
| **Annotations** | None needed | Required (`/\A`) |
| **Polymorphism** | Let-polymorphism only | Full polymorphism |
| **Type inference** | Complete & decidable | Undecidable |
| **Expressiveness** | Limited | Higher |
| **Ease of use** | Easier | More verbose |

**Use HM when**: You want convenience (ML, Haskell, OCaml)
**Use F when**: You need more expressiveness (Scala, explicit Haskell)

### Q21: Why is HM inference decidable but F isn't?

**A**:
**HM**: Type variables only quantified at `let`
  - Limited places to be polymorphic
  - Unification always terminates

**System F**: Explicit `∀` anywhere
  - Can have polymorphic arguments
  - Inference becomes undecidable (proven by Wells, 1999)

Trade-off: Convenience vs Expressiveness

### Q22: What can System F express that HM can't?

**A**:

1. **Polymorphic arguments**:
   ```
   System F: \(f : ∀a. a → a). ...  ✓
   HM: \f. ...                       ✗ f is monomorphic
   ```

2. **Nested polymorphism**:
   ```
   System F: id [∀a. a → a] id  ✓
   HM: Can't express this         ✗
   ```

3. **Church encodings**:
   ```
   System F: ∀A. A → A → A (Church bools)  ✓
   HM: Can't encode this way               ✗
   ```

---

## Practical "I'm Stuck" Scenarios

### Q23: "I get 'Cannot unify Int with Bool' - what does this mean?"

**A**: Your code expects different types in the same place:
```
\x. if x then (x + 1) else x

x used as Bool (in condition)
x used as Int (in x + 1)
Can't be both!
```

**Fix**: Use different variables:
```
\b. \n. if b then (n + 1) else n
```

### Q24: "I get 'Occurs check failed: α in α → β' - help!"

**A**: You're trying to create an infinite type:
```
\f. f f    -- Trying to make f : α where α = α → β
```

**This term cannot be typed in HM!** It's fundamentally ill-typed.

**Workaround**: Restructure your code, or move to System F if you truly need this.

### Q25: "Why does `(\x. (x 1, x true))` fail?"

**A**: `x` is lambda-bound, so it's **monomorphic**:
```
x 1 requires x : Int → α
x true requires x : Bool → β
But x can only have ONE type!
```

**Fix**: Use `let`:
```
let x = \y. y in (x 1, x true)    ✓ Works!
```

### Q26: "My recursive function won't type check!"

**A**: You probably need an explicit fixpoint operator:
```
Bad:
\f. \x. if (x == 0) then 1 else x * (f (x - 1))
     ↑ f is not in scope!

Good:
fix (\f. \x. if (x == 0) then 1 else x * (f (x - 1)))
```

HM supports recursion through `let` or explicit fix-point combinators.

### Q27: "I want a function that works on lists of any type - how?"

**A**: Use let-polymorphism:
```
let map = \f. \list.
  if (null list)
  then []
  else cons (f (head list)) (map f (tail list))
in ...

map : ∀a b. (a → b) → List a → List b
```

The `let` makes `map` polymorphic!

### Q28: "How do I debug type inference errors?"

**A**: Strategy:
1. **Break down the term**: Type check smaller pieces
2. **Add explicit let bindings**: See where types are inferred
3. **Check the REPL**: Use `:type` on subexpressions
4. **Read error carefully**: It tells you what couldn't unify
5. **Think about data flow**: Where does each variable come from?

Example:
```
\f. \g. \x. f (g x) x    -- Error!

Break down:
:type \f. \g. \x. f (g x)     -- What's this type?
:type \f. \g. \x. x           -- And this?
-- Now see where they conflict
```

---

## Advanced Questions

### Q29: What's "let-generalization" formally?

**A**: When type-checking `let x = e1 in e2`:

1. Infer type for `e1`: get type `τ` with free vars `{α1, ..., αn}`
2. **Generalize**: `σ = ∀α1...αn. τ`
3. Type-check `e2` with `x : σ`

When using `x`:
- **Instantiate**: Create fresh type vars for each `αi`
- Each use of `x` can have different instantiation!

### Q30: Can I have polymorphic recursion?

**A**: **NO** in basic HM! This would make inference undecidable.

```
Bad (polymorphic recursion):
let f = \x.
  if (small x)
  then f (convert_to_int x)    -- Use at Int
  else f (convert_to_bool x)   -- Use at Bool
```

**Workaround**: Use explicit type annotations (moves toward System F).

Some modern languages (GHC Haskell) support this with annotations.

### Q31: What's "first-class polymorphism" and why doesn't HM have it?

**A**: First-class polymorphism means polymorphic values can be:
- Passed as arguments: `\(f : ∀a. a → a). ...`
- Stored in data structures: `[id, id, id] : List (∀a. a → a)`
- Returned from functions: `... : ... → ∀a. a → a`

**HM doesn't have this** because it makes inference undecidable!

HM restriction: Polymorphism only at let-bindings (not inside types).

### Q32: How does HM relate to logic (Curry-Howard)?

**A**:
- **Simply Typed LC**: Intuitionistic propositional logic
- **Hindley-Milner**: Intuitionistic logic with let-polymorphism
- **System F**: Second-order intuitionistic logic

HM types-as-propositions:
```
∀a. a → a          "For all propositions A, A implies A"
∀a b. a → b → a    "For all A, B: A and B implies A"
```

---

## Quick Reference: Common Error Messages

| Error | Meaning | Fix |
|-------|---------|-----|
| Cannot unify X with Y | Types X and Y conflict | Check variable usage |
| Occurs check failed | Infinite type attempted | Term not typeable in HM |
| Type too polymorphic | Needs monomorphic type | Add annotation or use let |
| Undefined variable | Variable not in scope | Check spelling, add let binding |
| Ambiguous type variable | Can't determine type | Add annotation or more constraints |

---

## Further Reading

- **Damas & Milner (1982)**: Original HM paper - "Principal type-schemes for functional programs"
- **Pierce TAPL Chapter 22**: Excellent HM explanation
- **Heeren et al. (2002)**: "Generalizing Hindley-Milner Type Inference Algorithms"

**Remember**: Type inference is an algorithm, not magic. Understanding unification and substitution is key!

