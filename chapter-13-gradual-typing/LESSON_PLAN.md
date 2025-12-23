# Chapter 13: Gradual Typing - Lesson Plan

**Estimated Total Time**: 12-16 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus (Chapter 2)
- [ ] Subtyping concepts (Chapter 9)
- [ ] Basic understanding of runtime type checks
- [ ] Familiarity with dynamic languages is helpful

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain what gradual typing is and why it matters
2. Understand the dynamic type (?) and consistency relation
3. Insert casts to bridge static and dynamic code
4. Track blame for runtime type errors
5. Connect gradual typing to real languages (TypeScript, Python)
6. Design gradual migration strategies

---

## Lesson 1: The Problem of Mixing Paradigms (2-3 hours)

### Learning Goals
- Understand the tension between static and dynamic typing
- See how gradual typing bridges both worlds
- Learn the core intuition

### Activities

1. **Read** README.md sections: Overview, The Dynamic Type

2. **The typing tension**:
   - Static typing: Catches errors early, requires annotations
   - Dynamic typing: Flexible, errors at runtime
   - Most codebases need BOTH!

3. **Real scenarios**:
   - Migrating legacy Python to typed Python
   - Using dynamic libraries from typed code
   - Prototyping before adding types

4. **The gradual solution**:
   - Type `?` (dynamic) is consistent with any type
   - Runtime checks ensure safety
   - Add types gradually, not all at once

5. **Key notation**:
   ```
   ?               -- Dynamic type
   T₁ ~ T₂         -- Consistency (not equality!)
   <T₁ => T₂>^l t  -- Cast with blame label l
   ```

### Self-Check Questions
- [ ] Why can't we just use static typing everywhere?
- [ ] Why can't we just use dynamic typing everywhere?
- [ ] What does the dynamic type `?` represent?

---

## Lesson 2: Consistency vs. Equality (2-3 hours)

### Learning Goals
- Understand the consistency relation
- See why it's not equality
- Learn the rules

### Activities

1. **Read** README.md sections: Consistency Relation

2. **Consistency rules**:
   ```
   ? ~ T           -- Dynamic consistent with anything
   T ~ ?           -- Anything consistent with dynamic
   T ~ T           -- Reflexivity for base types
   T₁ -> T₂ ~ S₁ -> S₂   if T₁ ~ S₁ and T₂ ~ S₂
   ```

3. **Key insight**: Consistency is NOT transitive!
   ```
   Nat ~ ?     ✓
   ? ~ Bool    ✓
   Nat ~ Bool  ✗   (Not transitive!)
   ```

4. **Why not transitive?**
   - Would collapse to universal equality
   - Gradual typing would lose precision
   - Runtime checks still needed

5. **Practice**: Are these consistent?
   - `Nat ~ ?`
   - `? ~ ?`
   - `(Nat -> Bool) ~ (? -> ?)`
   - `Nat ~ Bool`

### Self-Check Questions
- [ ] What is the consistency relation?
- [ ] Why is consistency not transitive?
- [ ] Is `(Nat -> ?) ~ (? -> Bool)`?

---

## Lesson 3: Casts and Runtime Checks (2-3 hours)

### Learning Goals
- Understand cast insertion
- Learn cast semantics
- See ground types in action

### Activities

1. **Read** README.md sections: Cast Calculus

2. **Cast syntax**:
   ```
   <T₁ => T₂>^l t
   ```
   - Cast t from type T₁ to T₂
   - Label l for blame tracking

3. **Cast insertion**:
   ```
   -- Source (implicit)
   (λx : ?. succ x) true

   -- After elaboration (explicit casts)
   (λx : ?. succ <? => Nat> x) <Bool => ?> true
   ```

4. **Cast semantics**:
   ```
   <T => T> v = v                    -- Identity
   <G => ?> v = tagged value         -- Injection
   <? => G> (<G => ?> v) = v         -- Round-trip success
   <? => G'> (<G => ?> v) = blame    -- Ground mismatch
   ```

5. **Ground types**:
   - `Bool`, `Nat`, `Unit` -- base types
   - `? -> ?` -- the function ground type

### Self-Check Questions
- [ ] What is a cast?
- [ ] When does a cast fail at runtime?
- [ ] What are ground types?

---

## Lesson 4: Blame Tracking (2-3 hours)

### Learning Goals
- Understand what blame is
- Learn positive vs negative blame
- See the blame theorem

### Activities

1. **Read** README.md sections: Blame Tracking

2. **Blame labels**:
   ```
   <Nat => ?>^l₁ ...     -- Cast labeled l₁
   <? => Bool>^l₂ ...    -- Cast labeled l₂
   ```
   When cast fails: `blame^l : T`

3. **Blame direction**:
   - **Positive blame**: Caller provided wrong type
   - **Negative blame**: Function returned wrong type

4. **Blame theorem** (Wadler & Findler):
   > Well-typed programs can't be blamed.

   Fully typed code never causes blame!

5. **Example**:
   ```
   let f : ? -> Nat = ...        -- Boundary
   let x : Bool = true
   f x                            -- If fails, blame is on ?
   ```

### Self-Check Questions
- [ ] What does blame track?
- [ ] What's the difference between positive and negative blame?
- [ ] Can fully typed code be blamed?

---

## Lesson 5: The Gradual Guarantee (2-3 hours)

### Learning Goals
- Understand gradual guarantee properties
- See how precision affects behavior
- Learn about type precision

### Activities

1. **Read** README.md sections: Gradual Guarantee

2. **Type precision**:
   ```
   ? ⊑ Nat         -- ? is less precise than Nat
   ? -> ? ⊑ Nat -> Bool
   Nat ⊑ Nat       -- Same precision
   ```

3. **Static gradual guarantee**:
   - Making types more precise preserves typeability
   - If `e` type checks with `?`, replacing `?` with `T` still type checks

4. **Dynamic gradual guarantee**:
   - Making types more precise doesn't change behavior (up to blame)
   - Less precise = more casts = more potential errors
   - But if it succeeds, same result!

5. **Migration path**:
   ```
   -- Start: all dynamic
   λx : ?. λy : ?. x + y

   -- Intermediate
   λx : Nat. λy : ?. x + y

   -- Final: all typed
   λx : Nat. λy : Nat. x + y
   ```

### Self-Check Questions
- [ ] What is type precision?
- [ ] What does the static gradual guarantee ensure?
- [ ] What does the dynamic gradual guarantee ensure?

---

## Lesson 6: Real-World Gradual Typing (2-3 hours)

### Learning Goals
- Connect to TypeScript, Python
- See practical applications
- Understand trade-offs

### Activities

1. **Read** README.md sections: Connections to Real Languages

2. **TypeScript**:
   ```typescript
   let x: any = 42;        // any is like ?
   let y: number = x;      // Implicit cast
   ```

3. **Python with type hints**:
   ```python
   from typing import Any
   def f(x: Any) -> int:   # Any is like ?
       return x + 1
   ```

4. **Typed Racket**:
   - Full gradual typing with contracts
   - Explicit boundaries between typed/untyped

5. **Trade-offs**:
   - Performance: Casts have overhead
   - Ergonomics: Annotations vs inference
   - Safety: How much runtime checking?

### Self-Check Questions
- [ ] What is TypeScript's `any` type?
- [ ] How does Python handle gradual types?
- [ ] What's the runtime cost of gradual typing?

---

## Lesson 7: Implementation (2-3 hours)

### Learning Goals
- Understand consistency checking
- Learn cast insertion
- See blame propagation

### Activities

1. **Study** `src/TypeCheck.hs`:
   - Find the `consistent` function
   - See how `meet` computes join types
   - Understand cast insertion

2. **Study** `src/Eval.hs`:
   - Find `applyCast`
   - See how blame propagates
   - Understand ground type checks

3. **Key implementation patterns**:
   ```haskell
   consistent :: Type -> Type -> Bool
   consistent TyDyn _ = True
   consistent _ TyDyn = True
   consistent (TyFun t1 t2) (TyFun s1 s2) =
     consistent t1 s1 && consistent t2 s2
   consistent t1 t2 = t1 == t2
   ```

4. **Experiment** with REPL:
   ```
   stack exec gradual-repl
   gradual> :casts (λx : ?. x) 0
   gradual> :type λf : ?. f 0
   ```

### Self-Check Questions
- [ ] How is consistency checked?
- [ ] How are casts inserted?
- [ ] How does blame propagate?

---

## Lesson 8: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Consistency problems
   - Cast insertion
   - Blame tracking
   - Migration exercises

2. **Run all tests**:
   ```bash
   stack test
   ```
   All 52 tests should pass.

3. **Challenge problems**:
   - Implement space-efficient casts
   - Add gradual polymorphism
   - Extend to gradual dependent types

4. **Self-assessment**: Can you...
   - [ ] Determine consistency of types?
   - [ ] Insert casts correctly?
   - [ ] Track blame through computation?
   - [ ] Plan a gradual migration?

---

## Progress Tracker

### Lesson 1: The Problem
- [ ] Understood typing tension
- [ ] Saw gradual solution
- [ ] Learned basic notation

### Lesson 2: Consistency
- [ ] Know consistency rules
- [ ] Understand non-transitivity
- [ ] Can determine consistency

### Lesson 3: Casts
- [ ] Understand cast insertion
- [ ] Know cast semantics
- [ ] Understand ground types

### Lesson 4: Blame
- [ ] Know what blame tracks
- [ ] Understand blame theorem
- [ ] Can trace blame

### Lesson 5: Guarantees
- [ ] Understand type precision
- [ ] Know static guarantee
- [ ] Know dynamic guarantee

### Lesson 6: Real-World
- [ ] Connected to TypeScript
- [ ] Connected to Python
- [ ] Understand trade-offs

### Lesson 7: Implementation
- [ ] Read type checker code
- [ ] Read evaluator code
- [ ] Experimented with REPL

### Lesson 8: Exercises
- [ ] Completed exercises
- [ ] All tests pass
- [ ] Can apply concepts

---

## Key Takeaways

1. **Dynamic type (?)**: Compatible with everything, checked at runtime
2. **Consistency (~)**: Reflexive, symmetric, NOT transitive
3. **Casts**: Bridge between static and dynamic types
4. **Blame**: Tracks who's responsible for type errors
5. **Gradual migration**: Add types incrementally

## Next Steps

After mastering this chapter:
- **Chapter 14 (Row Types)**: Extensible records and variants
- **Research**: Gradual dependent types, effect graduality
- **Practice**: Add types to a dynamic codebase
