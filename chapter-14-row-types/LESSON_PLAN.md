# Chapter 14: Row Types & Extensible Records - Lesson Plan

**Estimated Total Time**: 12-16 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus (Chapter 2)
- [ ] Polymorphism (Chapter 6)
- [ ] Subtyping basics (Chapter 9)
- [ ] Basic understanding of records and variants

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain what row types are and why they matter
2. Write row-polymorphic functions
3. Work with extensible records (add, remove, access fields)
4. Handle polymorphic variants
5. Connect row polymorphism to structural typing
6. See application in effect systems

---

## Lesson 1: The Problem with Closed Records (2-3 hours)

### Learning Goals
- Understand limitations of nominal records
- See how row polymorphism helps
- Learn the core intuition

### Activities

1. **Read** README.md sections: Overview, The Problem with Nominal Records

2. **The record problem**:
   ```
   type Person = {name: String, age: Nat}
   type Employee = {name: String, age: Nat, salary: Nat}

   getName : Person -> String
   getName p = p.name

   getName someEmployee  -- Error! Employee ≠ Person
   ```
   Employee has ALL the fields, but types don't match!

3. **The row solution**:
   ```
   getName : ∀ρ. {name: String | ρ} -> String
   getName p = p.name

   getName {name = "Alice"}                    -- OK
   getName {name = "Bob", age = 30}            -- OK
   getName {name = "Carol", salary = 50000}    -- OK
   ```

4. **Key notation**:
   ```
   {l: T | ρ}     -- Record with field l:T, plus row ρ
   ∀ρ. T          -- Polymorphic over row ρ
   α              -- Row variable (unknown fields)
   ```

5. **Experiment** with the REPL:
   ```
   stack exec row-repl
   row> :type λr. r.name
   row> {x = 0, y = true}.x
   ```

### Self-Check Questions
- [ ] Why can't nominal records express "at least these fields"?
- [ ] What does `{name: String | ρ}` mean?
- [ ] How does row polymorphism enable code reuse?

---

## Lesson 2: Row Types Syntax and Semantics (2-3 hours)

### Learning Goals
- Understand row type syntax
- Learn about row extension
- See row variables in action

### Activities

1. **Read** README.md sections: Row Types, Syntax

2. **Row syntax**:
   ```
   ()              -- Empty row
   (l: T | ρ)      -- Field l with type T, rest is ρ
   α               -- Row variable
   ```

3. **Record types from rows**:
   ```
   {}              -- Empty record: {()}
   {x: Nat}        -- Record with x: {(x: Nat | ())}
   {x: Nat, y: Bool} -- Multiple fields
   {x: Nat | ρ}    -- Open record (at least x)
   ```

4. **Row extension vs record extension**:
   - Row: (l: T | ρ) is a TYPE-level operation
   - Record: {l = t | r} is a TERM-level operation

5. **Practice**: Write row types for:
   - A record with at least x and y fields (both Nat)
   - A record with exactly three string fields
   - An open record with a boolean flag field

### Self-Check Questions
- [ ] What's the difference between `{x: Nat}` and `{x: Nat | ρ}`?
- [ ] What does an empty row `()` represent?
- [ ] How do row variables enable polymorphism?

---

## Lesson 3: Record Operations (2-3 hours)

### Learning Goals
- Learn projection (field access)
- Learn extension (adding fields)
- Learn restriction (removing fields)

### Activities

1. **Read** README.md sections: Record Operations

2. **Projection** (access field):
   ```
   r.l : T    where r : {l: T | ρ}

   {x = 3, y = 4}.x  →  3
   ```

3. **Extension** (add field):
   ```
   {l = t | r} : {l: T | ρ}    where t : T, r : {ρ}

   {z = 5 | {x = 3, y = 4}}  →  {x = 3, y = 4, z = 5}
   ```
   Note: l must NOT already be in r (or use restriction first).

4. **Restriction** (remove field):
   ```
   r \ l : {ρ}    where r : {l: T | ρ}

   {x = 3, y = 4} \ x  →  {y = 4}
   ```

5. **Update pattern**:
   ```
   setName : ∀ρ. String -> {name: String | ρ} -> {name: String | ρ}
   setName newName r = {name = newName | r \ name}
   ```

### Self-Check Questions
- [ ] How do you access a field in a record?
- [ ] What constraint exists when extending a record?
- [ ] How do you update a field in a row-polymorphic way?

---

## Lesson 4: Row Polymorphic Functions (2-3 hours)

### Learning Goals
- Write functions polymorphic over rows
- Understand row instantiation
- See practical patterns

### Activities

1. **Read** README.md sections: Row Polymorphism, Examples

2. **Basic row polymorphism**:
   ```
   -- Works with any record having x and y
   magnitude : ∀ρ. {x: Nat, y: Nat | ρ} -> Nat
   magnitude p = sqrt (p.x * p.x + p.y * p.y)
   ```

3. **Multiple fields**:
   ```
   fullName : ∀ρ. {first: String, last: String | ρ} -> String
   fullName p = p.first ++ " " ++ p.last
   ```

4. **Preserving unknown fields**:
   ```
   addAge : ∀ρ. Nat -> {ρ} -> {age: Nat | ρ}
   addAge n r = {age = n | r}
   ```

5. **Row abstraction and application**:
   ```
   Λα. λr : {x: Nat | α}. r.x    -- Explicit abstraction
   f [(y: Bool | ())]             -- Instantiate with row
   ```

### Self-Check Questions
- [ ] What does `∀ρ.` in a type mean?
- [ ] How do you write a function that preserves extra fields?
- [ ] When is explicit row instantiation needed?

---

## Lesson 5: Polymorphic Variants (2-3 hours)

### Learning Goals
- Understand open sum types
- Write variant handlers
- See duality with records

### Activities

1. **Read** README.md sections: Polymorphic Variants

2. **Variant syntax**:
   ```
   <l: T | ρ>     -- Variant with at least case l

   <int: Nat | float: Nat | ρ>  -- Open variant
   ```

3. **Variant injection**:
   ```
   <ok = 42> : <ok: Nat | ρ>
   <error = "fail"> : <error: String | ρ>
   ```

4. **Case analysis**:
   ```
   handleNum : ∀ρ. <int: Nat | float: Nat | ρ> -> Nat
   handleNum v = case v of
     <int = n> -> n
     <float = n> -> n
     <other = x> -> 0
   ```

5. **Duality with records**:
   - Records: "has at least these fields" (conjunction)
   - Variants: "is at least one of these cases" (disjunction)

### Self-Check Questions
- [ ] What's the difference between closed and open variants?
- [ ] How do you inject into a polymorphic variant?
- [ ] What's the dual relationship between records and variants?

---

## Lesson 6: Row Unification and Typing Rules (2-3 hours)

### Learning Goals
- Understand row unification
- Learn key typing rules
- See row reordering

### Activities

1. **Read** README.md sections: Type System, Row Unification

2. **Typing rules**:
   ```
      Γ ⊢ r : {l: T | ρ}
     ────────────────────     (Projection)
        Γ ⊢ r.l : T

      Γ ⊢ r : {ρ}    Γ ⊢ t : T    l ∉ ρ
     ─────────────────────────────────────   (Extension)
          Γ ⊢ {l = t | r} : {l: T | ρ}
   ```

3. **Row unification**:
   - Labels can appear in any order
   - `{x: Nat, y: Bool}` ~ `{y: Bool, x: Nat}`
   - Row variables unify with row extensions

4. **Lack constraints**:
   ```
   (l ∉ ρ)   -- Constraint that l is not in ρ
   ```
   Ensures no duplicate fields when extending.

5. **Study** `src/TypeCheck.hs`:
   - Find `rowHas` function
   - See row unification
   - Understand constraint solving

### Self-Check Questions
- [ ] What makes row unification special?
- [ ] Why can labels appear in any order?
- [ ] What are lack constraints for?

---

## Lesson 7: Connections and Applications (2-3 hours)

### Learning Goals
- Connect to subtyping
- See real language examples
- Understand effect rows

### Activities

1. **Read** README.md sections: Relationship to Subtyping, Connections

2. **Row polymorphism vs subtyping**:
   | Feature | Subtyping | Row Polymorphism |
   |---------|-----------|------------------|
   | Mechanism | <: relation | ∀ρ abstraction |
   | Inference | Limited | Full inference |
   | Flexibility | Width subtyping | Arbitrary fields |

3. **Real languages**:
   - **PureScript**: Full row polymorphism
   - **Elm**: Extensible records (limited)
   - **OCaml**: Polymorphic variants
   - **TypeScript**: Structural typing

4. **Effect rows** (Chapter 12 connection):
   ```
   {State, IO | ρ}    -- Effect row
   ```
   Same machinery, different domain!

5. **Duck typing connection**:
   Row polymorphism is statically typed duck typing!

### Self-Check Questions
- [ ] What advantage does row polymorphism have over subtyping?
- [ ] Which languages support row polymorphism?
- [ ] How are effect rows related to record rows?

---

## Lesson 8: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Row-polymorphic functions
   - Record operations
   - Variant handling
   - Object encoding

2. **Run all tests**:
   ```bash
   stack test
   ```
   All 65 tests should pass.

3. **Challenge problems**:
   - Implement a typed OOP-style object system
   - Add scoped labels for duplicate handling
   - Integrate rows with effects

4. **Self-assessment**: Can you...
   - [ ] Write row-polymorphic functions?
   - [ ] Use all record operations?
   - [ ] Handle polymorphic variants?
   - [ ] See connection to duck typing?

---

## Progress Tracker

### Lesson 1: The Problem
- [ ] Understood record limitations
- [ ] Saw row polymorphism solution
- [ ] Experimented with REPL

### Lesson 2: Syntax
- [ ] Know row syntax
- [ ] Understand row variables
- [ ] Can write row types

### Lesson 3: Operations
- [ ] Know projection
- [ ] Know extension
- [ ] Know restriction

### Lesson 4: Polymorphism
- [ ] Can write row-polymorphic functions
- [ ] Understand abstraction/application
- [ ] See practical patterns

### Lesson 5: Variants
- [ ] Understand open sum types
- [ ] Can inject and match
- [ ] See duality with records

### Lesson 6: Type System
- [ ] Understand unification
- [ ] Know typing rules
- [ ] Understand lack constraints

### Lesson 7: Applications
- [ ] Connected to subtyping
- [ ] Know real languages
- [ ] See effect rows

### Lesson 8: Exercises
- [ ] Completed exercises
- [ ] All tests pass
- [ ] Can apply concepts

---

## Key Takeaways

1. **Row types**: Map from labels to types with possible extension
2. **Row polymorphism**: Abstract over unknown fields with `∀ρ`
3. **Operations**: Project, extend, restrict records
4. **Variants**: Dual to records for open sum types
5. **Better inference**: Row polymorphism infers better than subtyping

## Next Steps

After mastering this chapter:
- **Chapter 15 (Recursive Types)**: Self-referential types
- **Research**: Scoped labels, effect rows, object encoding
- **Practice**: Use row types in PureScript or Koka
