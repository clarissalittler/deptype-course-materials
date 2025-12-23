# Chapter 14: Row Types & Extensible Records - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce row types and extensible records concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Basic Row Types ⭐
Write the row type for each:

a) A record with exactly fields x:Nat and y:Bool
b) A record with at least field name:String
c) An empty record
d) A record with at least x:Nat and y:Nat, plus unknown fields

### Problem 1.2: Record Operations ⭐
Evaluate these expressions:

a) `{x = 3, y = 4}.x`
b) `{z = 5 | {x = 3, y = 4}}`
c) `{x = 3, y = 4, z = 5} \ y`
d) `{name = "New" | {name = "Old", age = 30} \ name}`

### Problem 1.3: Type Checking ⭐
Which of these type check?

a) `(λr. r.x) : {x: Nat} -> Nat`
b) `(λr. r.x) : ∀ρ. {x: Nat | ρ} -> Nat`
c) `(λr. {y = 0 | r}) : ∀ρ. {ρ} -> {y: Nat | ρ}`
d) `(λr. {x = 0 | r}) : ∀ρ. {x: Nat | ρ} -> {x: Nat | ρ}`

### Problem 1.4: Row Unification ⭐
Unify these row type pairs:

a) `{x: Nat | α}` with `{x: Nat}`
b) `{x: Nat | α}` with `{x: Nat, y: Bool}`
c) `{x: Nat, y: Bool}` with `{y: Bool, x: Nat}`
d) `{x: Nat | α}` with `{y: Bool | β}`

### Problem 1.5: Polymorphic Variants ⭐
Write the type for each:

a) `<ok = 42>`
b) `<error = "fail">`
c) A handler that handles `<ok: Nat>` and `<error: String>` cases
d) A handler that handles `<int: Nat>` and passes through other cases

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Row-Polymorphic Functions ⭐⭐
Implement these functions:

a) `getAge : ∀ρ. {age: Nat | ρ} -> Nat`
   Extract the age field from any record.

b) `setAge : ∀ρ. Nat -> {age: Nat | ρ} -> {age: Nat | ρ}`
   Update the age field in any record.

c) `addEmail : ∀ρ. String -> {ρ} -> {email: String | ρ}`
   Add an email field to any record.

d) `fullName : ∀ρ. {first: String, last: String | ρ} -> String`
   Concatenate first and last name.

### Problem 2.2: Record Manipulation ⭐⭐
Implement these operations:

a) `renameField : ∀ρ. {old: T | ρ} -> {new: T | ρ}`
   Rename field `old` to `new`.

b) `swapFields : ∀ρ. {x: T, y: S | ρ} -> {x: S, y: T | ρ}`
   Swap the values of x and y fields.

c) `projectTwo : ∀ρ. {x: T, y: S | ρ} -> {x: T, y: S}`
   Keep only x and y fields.

d) `copyField : ∀ρ. {src: T | ρ} -> {src: T, dest: T | ρ}`
   Copy src field to new dest field.

### Problem 2.3: Variant Handlers ⭐⭐
Implement these variant operations:

a) `handleBinary : ∀ρ. <left: T | right: T | ρ> -> T`
   Handle left and right cases, return default for others.

b) `mapOk : ∀α β ρ. (α -> β) -> <ok: α | ρ> -> <ok: β | ρ>`
   Map function over ok case, pass through others.

c) `flattenResult : ∀α ρ. <ok: <ok: α | ρ> | error: String | ρ> -> <ok: α | error: String | ρ>`
   Flatten nested ok case.

d) `injectError : ∀ρ. String -> <error: String | ρ>`
   Create error variant.

### Problem 2.4: Row Constraints ⭐⭐
Add appropriate lack constraints to these:

a) `addId : ∀ρ. Nat -> {ρ} -> {id: Nat | ρ}`
   Ensure id field doesn't already exist.

b) `extendPoint : ∀ρ. Nat -> {x: Nat, y: Nat | ρ} -> {x: Nat, y: Nat, z: Nat | ρ}`
   Add z field to a 2D point.

c) `mergDisjoint : ∀ρ₁ ρ₂. {ρ₁} -> {ρ₂} -> {ρ₁, ρ₂}`
   Merge two records with no overlapping fields.

d) `replaceOrAdd : ∀ρ. T -> {ρ} -> {l: T | ρ}`
   Replace field l if exists, otherwise add it.

### Problem 2.5: Row Unification Proofs ⭐⭐
Show unification for these type equations:

a) `∀ρ. {x: Nat | ρ} -> Nat` applied to `{x: Nat, y: Bool}`
   What is `ρ`?

b) `∀ρ₁ ρ₂. {x: Nat | ρ₁} -> {y: Bool | ρ₂} -> {x: Nat, y: Bool | ρ₃}`
   What is `ρ₃` in terms of `ρ₁` and `ρ₂`?

c) Unify `{x: Nat | α}` with `{y: Bool | β}` where result has both fields.
   What are `α` and `β`?

d) Can `{x: Nat}` unify with `{x: Bool | ρ}`? Why or why not?

### Problem 2.6: Extensible Data Structures ⭐⭐
Model these with row types:

a) Extensible points (2D, 3D, or more)
   ```
   type Point2D ρ = ???
   type Point3D ρ = ???
   ```

b) Extensible people records (name, age, plus optional fields)
   ```
   type Person ρ = ???
   ```

c) Extensible configuration (base settings plus plugins)
   ```
   type Config ρ = ???
   ```

d) Extensible result type (ok, error, plus custom cases)
   ```
   type Result α ρ = ???
   ```

### Problem 2.7: Relationship to Subtyping ⭐⭐
Show how row polymorphism encodes these subtyping relations:

a) `{x: Nat, y: Bool} <: {x: Nat}`
b) `{name: String, age: Nat, email: String} <: {name: String, age: Nat}`
c) `{} <: {x: Nat}`
d) How is this different from nominal subtyping?

### Problem 2.8: Polymorphic Variant Composition ⭐⭐
Implement:

a) `embedLeft : ∀ρ. <ρ> -> <left: <ρ> | ρ'>`
   Embed variant into left case.

b) `mergeVariants : ∀ρ₁ ρ₂. <ρ₁> -> <ρ₂> -> <ρ₁ | ρ₂>`
   Merge two variants (requires disjoint rows).

c) `distributeOk : ∀α β ρ. <ok: (α, β) | ρ> -> (<ok: α | ρ>, <ok: β | ρ>)`
   Distribute ok case over pair.

d) `variantMap : ∀α β ρ. (α -> β) -> <l: α | ρ> -> <l: β | ρ>`
   Map over specific variant case.

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Row Algebra ⭐⭐⭐
Define operations on rows:

a) **Row union**: `ρ₁ ⊔ ρ₂` (requires disjoint)
b) **Row intersection**: `ρ₁ ⊓ ρ₂`
c) **Row difference**: `ρ₁ \ ρ₂` (remove labels from ρ₁ that appear in ρ₂)
d) Prove: `(ρ₁ ⊔ ρ₂) ⊓ ρ₁ = ρ₁`

### Problem 3.2: Scoped Labels ⭐⭐⭐
Handle duplicate labels with scoping:

a) Design syntax for scoped labels: `module1.name` vs `module2.name`
b) Define type rules for scoped record access
c) Show how to resolve label ambiguity
d) Implement a renaming strategy

### Problem 3.3: Row Types for Effects ⭐⭐⭐
Use row types to track effects:

a) Define effect rows: `{State, IO | ε}`
b) Type `get : ∀ε. {State | ε} T`
c) Type `put : ∀ε. T -> {State | ε} Unit`
d) Show how to compose effectful computations

### Problem 3.4: Object Encoding ⭐⭐⭐
Encode OOP with row types:

a) Define object type: `Object ρ = {ρ, self: Object ρ}`
b) Encode class with inheritance
c) Encode method calls with dynamic dispatch
d) Show subtyping corresponds to row polymorphism

### Problem 3.5: Type Inference for Rows ⭐⭐⭐
Design a type inference algorithm:

a) Define constraint generation for row-polymorphic terms
b) Design row unification algorithm
c) Handle lack constraints during inference
d) Show inference for: `λr. {z = 0 | r \ x}`

### Problem 3.6: Row Types vs Structural Subtyping ⭐⭐⭐
Compare expressiveness:

a) Show a type expressible with rows but not subtyping
b) Show a type expressible with subtyping but not rows
c) Can row polymorphism + lack constraints express depth subtyping?
d) Design a system combining both

---

## Debugging Exercises (30 minutes)

### Debug 1: Extension Error ⭐
Student wrote:
```
addX : ∀ρ. Nat -> {ρ} -> {x: Nat | ρ}
addX n r = {x = n | r}
```

They call `addX 5 {x = 3, y = 4}` and get error. Why?

### Debug 2: Lack Constraint Violation ⭐⭐
```
extend : ∀ρ. {l: T | ρ} -> {l: T, l: T | ρ}   -- WRONG!
```

What's wrong with this type? How to fix it?

### Debug 3: Row Variable Scope ⭐⭐
```
f : {x: Nat | ρ} -> {y: Bool | ρ} -> {x: Nat, y: Bool}
f r1 r2 = {x = r1.x, y = r2.y}
```

Student expects this to type check. Why doesn't it?

### Debug 4: Variant Case Coverage ⭐⭐
```
handle : ∀ρ. <ok: Nat | error: String | ρ> -> Nat
handle v = case v of
  <ok = n> -> n
  <error = _> -> 0
  -- Missing: <other = _> -> ???
```

Why is the `other` case needed?

### Debug 5: Record Merge ⭐⭐
```
merge : ∀ρ₁ ρ₂. {ρ₁} -> {ρ₂} -> {ρ₁, ρ₂}
merge r1 r2 = {??? | r1}   -- How to add all of r2?
```

Why is this hard to implement? What constraint is needed?

---

## Code Review Exercises (30 minutes)

### Review 1: Point Implementation ⭐⭐
Student's code:
```
type Point = {x: Nat, y: Nat}

distance : Point -> Point -> Nat
distance p1 p2 = sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)
```

Improvements:
- Make it work with 3D points too
- Allow additional fields
- Make it row-polymorphic

### Review 2: Record Update ⭐⭐
Two versions:

**Version A**:
```
updateName r newName = {name = newName | r \ name}
```

**Version B**:
```
updateName r newName =
  let rest = r \ name in
  {name = newName | rest}
```

Which is better? Any differences?

### Review 3: Variant Handler ⭐⭐⭐
Student's Result handler:
```
unwrapResult : <ok: Nat | error: String> -> Nat
unwrapResult v = case v of
  <ok = n> -> n
  <error = _> -> 0
```

Critique:
- Is this row-polymorphic?
- Should it handle other cases?
- Better error handling strategy?

---

## Real-World Scenarios (45 minutes)

### Scenario 1: Configuration System ⭐⭐
Design a plugin-based config system:

```
-- Base config
type BaseConfig = {host: String, port: Nat}

-- Plugins add fields
type PluginConfig ρ = {host: String, port: Nat | ρ}

-- Different plugins
type LoggingPlugin = {logLevel: String, logFile: String}
type CachePlugin = {cacheSize: Nat, cacheTTL: Nat}
```

Implement:
a) `loadConfig : ∀ρ. PluginConfig ρ -> App`
b) `addPlugin : ∀ρ₁ ρ₂. PluginConfig ρ₁ -> {ρ₂} -> PluginConfig (ρ₁ ⊔ ρ₂)`

### Scenario 2: Database Records ⭐⭐
Model database rows with optional columns:

```
-- Base user
type User ρ = {id: Nat, name: String | ρ}

-- Extended users
type FullUser = User (email: String, phone: String)
type BasicUser = User ()
```

Implement:
a) `getUser : ∀ρ. Nat -> DB (User ρ)`
b) `updateUser : ∀ρ. Nat -> User ρ -> DB Unit`
c) How to handle optional fields vs required fields?

### Scenario 3: UI Components ⭐⭐⭐
Model React-style components with props:

```
type Component props = props -> JSX

-- Button component accepts at least label
button : ∀ρ. Component {label: String | ρ}

-- Can pass extra props
button {label = "Click", onClick = handler, className = "btn"}
```

Design:
a) Type-safe component composition
b) Prop validation with row types
c) Optional vs required props
d) Event handlers with row polymorphism

---

## Solutions

### Warm-Up Solutions

**1.1**:
- a) `{x: Nat, y: Bool}` or `{x: Nat, y: Bool | ()}`
- b) `∀ρ. {name: String | ρ}`
- c) `{}`or `{()}`
- d) `{x: Nat, y: Nat | ρ}`

**1.2**:
- a) `3`
- b) `{x = 3, y = 4, z = 5}`
- c) `{x = 3, z = 5}`
- d) `{name = "New", age = 30}`

**1.3**:
- a) Yes (closed record)
- b) Yes (row-polymorphic, better!)
- c) Yes
- d) No (would create duplicate x)

**1.4**:
- a) `α = ()`
- b) `α = (y: Bool | ())`
- c) Already equal (order doesn't matter)
- d) `α = (y: Bool | γ)`, `β = (x: Nat | γ)` for fresh `γ`

**1.5**:
- a) `<ok: Nat | ρ>`
- b) `<error: String | ρ>`
- c) `∀ρ. <ok: Nat | error: String | ρ> -> T`
- d) `∀ρ. <int: Nat | ρ> -> <int: Nat | ρ>`

### Standard Solutions

**2.1**:
```
a) getAge r = r.age
b) setAge n r = {age = n | r \ age}
c) addEmail e r = {email = e | r}
d) fullName r = r.first ++ " " ++ r.last
```

**2.2**:
```
a) renameField r = {new = r.old | r \ old}
b) swapFields r = {x = r.y, y = r.x | r \ x \ y}
c) projectTwo r = {x = r.x, y = r.y}
d) copyField r = {dest = r.src | r}
```

**2.3**:
```
a) handleBinary v = case v of
     <left = x> -> x
     <right = x> -> x
     <other = _> -> default

b) mapOk f v = case v of
     <ok = x> -> <ok = f x>
     <other = x> -> <other = x>
```

**2.4**:
```
a) (id ∉ ρ) =>
b) (z ∉ ρ) =>
c) ρ₁ ∩ ρ₂ = ∅ (disjoint rows)
d) No constraint needed (remove first if exists)
```

**2.5**:
- a) `ρ = (y: Bool | ())`
- b) `ρ₃` is the union of `ρ₁` and `ρ₂` minus x and y
- c) `α = (y: Bool | γ)`, `β = (x: Nat | γ)` for fresh `γ`
- d) No, Nat ≠ Bool

**2.6**:
```
a) type Point2D ρ = {x: Nat, y: Nat | ρ}
   type Point3D ρ = {x: Nat, y: Nat, z: Nat | ρ}

b) type Person ρ = {name: String, age: Nat | ρ}

c) type Config ρ = {baseSettings: Settings | ρ}

d) type Result α ρ = <ok: α | error: String | ρ>
```

**2.7**: Row polymorphism uses `∀ρ. {required fields | ρ}` where subtyping uses `<:`.

**2.8**: Solutions involve case analysis and variant injection patterns.

### Challenge Solutions

**3.1**: Define row operations algebraically with appropriate constraints.

**3.2**: Scoped labels require module system integration and disambiguation.

**3.3**: Effect rows track computational effects at type level.

**3.4**: Objects as records of methods with self-reference.

**3.5**: Constraint-based inference with row unification.

**3.6**: Row types and subtyping are complementary; combining gives more power.

### Debug Solutions

**Debug 1**: Need lack constraint `(x ∉ ρ)` to prevent duplicate.

**Debug 2**: Can't have duplicate label `l`. Type makes no sense.

**Debug 3**: The `ρ` in both arguments might differ. Need: `{x: Nat | ρ} -> {y: Bool | ρ} -> {x: Nat, y: Bool | ρ}`.

**Debug 4**: Row `ρ` might have other cases beyond ok and error.

**Debug 5**: Need structural induction or fold over r2. Requires disjoint rows.

### Code Review Solutions

**Review 1**: Make it `∀ρ. Point2D ρ -> Point2D ρ -> Nat` to work with any point.

**Review 2**: Version A and B are equivalent; B is clearer for debugging.

**Review 3**: Should be row-polymorphic and handle `other` case.

---

**Estimated Time**: 5-7 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 6 hard, 5 debug, 3 review, 3 scenarios

**Note**: These problems complement the main exercises. Focus on understanding row polymorphism principles!
