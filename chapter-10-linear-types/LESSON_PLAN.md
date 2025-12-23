# Chapter 10: Linear Types - Lesson Plan

**Estimated Total Time**: 12-16 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus (Chapter 2)
- [ ] Basic type checking concepts
- [ ] Function types and application
- [ ] Pairs and pattern matching

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain what linear types are and why they matter
2. Distinguish between linear (1) and unrestricted (ω) multiplicities
3. Track variable usage in type checking
4. Use the bang type (!) to control linearity
5. Connect linear types to Rust's ownership system
6. Apply linear types to resource management

---

## Lesson 1: The Problem of Resources (2-3 hours)

### Learning Goals
- Understand why resource management is hard
- See how linear types help
- Learn the core intuition

### Activities

1. **Read** README.md sections: Overview, Types

2. **The resource problem**:
   - File handles must be closed exactly once
   - Memory must be freed exactly once
   - Network connections must be managed properly
   - What happens if you forget? Or do it twice?

3. **The linear solution**:
   - Linear types ensure resources are used **exactly once**
   - The type system enforces this statically
   - No runtime overhead!

4. **Key notation**:
   ```
   A -o B   -- Linear function (uses argument once)
   A -> B   -- Unrestricted function (uses argument any times)
   !A       -- Bang type (makes A unrestricted)
   ```

5. **Experiment** with the REPL:
   ```
   stack exec linear-repl
   linear> :type \(x :1 Nat). x
   linear> :type \(x :ω Nat). (x, x)
   ```

### Self-Check Questions
- [ ] What does "use exactly once" mean?
- [ ] Why can't linear variables be duplicated?
- [ ] Why can't linear variables be discarded?

---

## Lesson 2: Multiplicities and Usage (2-3 hours)

### Learning Goals
- Understand the two multiplicities
- Learn usage tracking
- See how contexts are split

### Activities

1. **Read** README.md sections: Typing Rules, Usage Tracking

2. **The two multiplicities**:
   - **Linear (1)**: Must use exactly once
   - **Unrestricted (ω)**: Can use any number of times (0, 1, many)

3. **Context splitting**:
   When typing `(t₁, t₂)`, variables are split:
   ```
   Γ ⊢ t₁ : A    Δ ⊢ t₂ : B
   ─────────────────────────────
   Γ, Δ ⊢ (t₁, t₂) : A * B
   ```
   Each linear variable goes to exactly one side!

4. **Study** `src/TypeCheck.hs`:
   - Find the `Usage` type
   - See how `addUsage` works
   - Understand context splitting

5. **Practice**: Which are valid?
   - `λ(x :1 Nat). x`
   - `λ(x :1 Nat). (x, x)`
   - `λ(x :1 Nat). 0`
   - `λ(x :ω Nat). (x, x)`

### Self-Check Questions
- [ ] How do multiplicities affect variable usage?
- [ ] What happens when you split a context?
- [ ] Can an unrestricted variable be treated as linear?

---

## Lesson 3: The Bang Type (2-3 hours)

### Learning Goals
- Understand bang introduction and elimination
- Know when to use bang
- See the connection to exponentials

### Activities

1. **Read** README.md section: Bang Introduction/Elimination

2. **Bang introduction** (`!t`):
   ```
   Γ ⊢ t : A    (Γ has no linear variables)
   ──────────────────────────────────────────
   Γ ⊢ !t : !A
   ```
   Can only bang values built from unrestricted things!

3. **Bang elimination** (`let !x = t₁ in t₂`):
   ```
   Γ ⊢ t₁ : !A    Δ, x :ω A ⊢ t₂ : B
   ───────────────────────────────────
   Γ, Δ ⊢ let !x = t₁ in t₂ : B
   ```
   Unwrap the bang, use the contents unrestrictedly!

4. **Example**:
   ```
   let !x = !5 in (x, x)    -- OK! x is unrestricted
   ```

5. **Practice**:
   - What's the type of `!true`?
   - Can you write `λ(x :1 Nat). !x`? Why or why not?

### Self-Check Questions
- [ ] When can you introduce a bang?
- [ ] What does bang elimination give you?
- [ ] Why is bang important for practical programs?

---

## Lesson 4: Pairs and Pattern Matching (2-3 hours)

### Learning Goals
- Understand linear pairs (tensor product)
- Learn destructuring with let
- See the difference from regular pairs

### Activities

1. **Read** README.md sections: Pairs (Tensor Product), Pair Elimination

2. **Tensor product** (A * B):
   - Both components must be used
   - Elimination requires using both

3. **Pair elimination**:
   ```
   Γ ⊢ t₁ : A * B    Δ, x :1 A, y :1 B ⊢ t₂ : C
   ──────────────────────────────────────────────
   Γ, Δ ⊢ let (x, y) = t₁ in t₂ : C
   ```
   Both x and y are linear—must use each once!

4. **Valid examples**:
   ```
   let (x, y) = (1, true) in (y, x)   -- OK: both used
   ```

5. **Invalid examples**:
   ```
   let (x, y) = (1, true) in x    -- ERROR: y unused
   let (x, y) = (1, true) in (x, x)  -- ERROR: x used twice
   ```

### Self-Check Questions
- [ ] What makes linear pairs different from regular pairs?
- [ ] What happens if you don't use a component?
- [ ] Can pair components have different multiplicities?

---

## Lesson 5: Real-World Applications (2-3 hours)

### Learning Goals
- Connect to Rust's ownership
- Understand session types
- See file handle safety

### Activities

1. **Read** README.md section: Real-World Applications

2. **Rust's ownership**:
   - Each value has one owner (linear)
   - Moving transfers ownership
   - Clone is like bang

3. **File handles**:
   ```
   open  : Path -o Handle
   read  : Handle -o (String * Handle)
   close : Handle -o ()
   ```
   Handle is linear—must close exactly once!

4. **Session types** (concept):
   ```
   Send Int (Recv Bool End)
   ```
   Protocol must be followed exactly.

5. **Memory safety**:
   ```
   malloc : Size -o Ptr
   free   : Ptr -o ()
   ```
   No double-free, no memory leaks!

### Self-Check Questions
- [ ] How does Rust implement linearity?
- [ ] Why are file handles naturally linear?
- [ ] What guarantees do session types provide?

---

## Lesson 6: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Basic linear functions
   - Usage tracking
   - Bang type exercises
   - Resource protocols

2. **Run all tests**:
   ```bash
   stack test
   ```
   All 45 tests should pass.

3. **Challenge problems**:
   - Implement a linear file API
   - Model a simple protocol with session types
   - Add affine types (use at most once)

4. **Self-assessment**: Can you...
   - [ ] Write linear and unrestricted functions?
   - [ ] Use bang to escape linearity?
   - [ ] Track usage correctly in type checking?
   - [ ] Design a linear API for resources?

---

## Progress Tracker

### Lesson 1: The Problem
- [ ] Understood resource management issues
- [ ] Grasped linearity intuition
- [ ] Experimented with REPL

### Lesson 2: Multiplicities
- [ ] Know linear vs unrestricted
- [ ] Understand context splitting
- [ ] Can track usage

### Lesson 3: Bang Type
- [ ] Understand introduction/elimination
- [ ] Know when bang is needed
- [ ] Can use it in examples

### Lesson 4: Pairs
- [ ] Understand tensor product
- [ ] Can destructure linearly
- [ ] Know the constraints

### Lesson 5: Applications
- [ ] Connected to Rust
- [ ] Understand file handle pattern
- [ ] See session type idea

### Lesson 6: Exercises
- [ ] Completed exercises
- [ ] All tests pass
- [ ] Can design linear APIs

---

## Key Takeaways

1. **Linear = exactly once**: No duplication, no discarding
2. **Unrestricted = any times**: Traditional functional semantics
3. **Bang escapes linearity**: Wrap to make unrestricted
4. **Context splitting**: Each linear variable to one subterm
5. **Resource safety**: Linear types prevent leaks and double-free

## Next Steps

After mastering this chapter:
- **Chapter 11 (Refinement Types)**: Add predicates to types
- **Research**: Session types, quantitative type theory
- **Practice**: Implement linear data structures
