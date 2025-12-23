# Chapter 15: Recursive Types (μ Types) - Lesson Plan

**Estimated Total Time**: 12-16 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus (Chapter 2)
- [ ] Algebraic data types: sums and products (Chapter 3)
- [ ] Type variables and substitution
- [ ] Basic understanding of fixed points

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain what recursive types are and why they're needed
2. Distinguish iso-recursive from equi-recursive semantics
3. Use fold and unfold operations
4. Encode lists, trees, and streams as recursive types
5. Understand the connection to fixed points
6. See how recursive types enable general recursion

---

## Lesson 1: The Problem of Self-Reference (2-3 hours)

### Learning Goals
- Understand why types need to refer to themselves
- See limitations without recursive types
- Learn the μ notation

### Activities

1. **Read** README.md sections: Overview, Key Concepts

2. **The self-reference problem**:
   ```
   -- How do we type a list in STLC?
   List Nat = ???
   -- A list is either empty OR a Nat followed by... another list!
   ```

3. **The solution: μ types**:
   ```
   NatList = μα. Unit + (Nat × α)
              ↑           ↑
              |           α refers back to NatList!
              binds α
   ```

4. **Reading μ types**:
   - `μα.` means "the type α where..."
   - Body T uses α to refer to the whole type
   - `NatList = μα. Unit + (Nat × α)`: Either Unit (empty) OR Nat paired with more list

5. **Key insight**: α is a TYPE variable bound in T, referring to the whole μ type.

### Self-Check Questions
- [ ] Why can't we define List in simply typed lambda calculus?
- [ ] What does the μ binder do?
- [ ] What does α represent in `μα. T`?

---

## Lesson 2: Iso-Recursive Semantics (2-3 hours)

### Learning Goals
- Understand iso-recursive approach
- Learn fold and unfold operations
- See the isomorphism

### Activities

1. **Read** README.md sections: Iso-recursive Semantics, Typing Rules

2. **The key insight**:
   ```
   μα. T  ≅  T[μα.T/α]     -- Isomorphic, NOT equal!
   ```

   For NatList:
   ```
   μα. Unit + (Nat × α)  ≅  Unit + (Nat × NatList)
   ```

3. **The operations**:
   ```
   fold   : T[μα.T/α] → μα.T      -- Wrap into recursive type
   unfold : μα.T → T[μα.T/α]      -- Unwrap from recursive type
   ```

4. **Typing rules**:
   ```
      Γ ⊢ t : T[μα.T/α]
   ─────────────────────────
   Γ ⊢ fold [μα.T] t : μα.T

        Γ ⊢ t : μα.T
   ─────────────────────────────
   Γ ⊢ unfold [μα.T] t : T[μα.T/α]
   ```

5. **Evaluation**:
   ```
   unfold (fold v) → v    -- They cancel out!
   ```

### Self-Check Questions
- [ ] What's the difference between ≅ and =?
- [ ] What does fold do? What does unfold do?
- [ ] Why do fold and unfold cancel?

---

## Lesson 3: Working with Lists (2-3 hours)

### Learning Goals
- Encode list type as μ type
- Write constructors (nil, cons)
- Write destructors (head, tail, isEmpty)

### Activities

1. **Read** README.md sections: Working with Recursive Types, Natural Number Lists

2. **List type**:
   ```
   NatList = μα. Unit + (Nat × α)
   ```

3. **Constructors**:
   ```
   -- nil: empty list
   nil = fold [NatList] (inl unit)

   -- cons: add element
   cons = λn:Nat. λl:NatList.
     fold [NatList] (inr <n, l>)
   ```

4. **Destructors**:
   ```
   -- isEmpty: check if empty
   isEmpty = λl:NatList.
     case unfold [NatList] l of
       inl _ => true
     | inr _ => false

   -- head: get first element
   head = λl:NatList.
     case unfold [NatList] l of
       inl _ => 0  -- error case
     | inr p => fst p
   ```

5. **Building lists**:
   ```
   [1, 2, 3] = cons 1 (cons 2 (cons 3 nil))
   ```

### Self-Check Questions
- [ ] Why do we need `inl` and `inr` in list constructors?
- [ ] Why must we unfold before pattern matching?
- [ ] How does the list structure mirror the type definition?

---

## Lesson 4: Trees and Other Structures (2-3 hours)

### Learning Goals
- Encode binary trees
- Encode other recursive structures
- See the pattern

### Activities

1. **Binary trees**:
   ```
   Tree = μα. Nat + (α × α)
   --       leaf    branch with two subtrees
   ```

2. **Tree constructors**:
   ```
   leaf = λn:Nat. fold [Tree] (inl n)
   branch = λl:Tree. λr:Tree. fold [Tree] (inr <l, r>)
   ```

3. **Rose trees** (arbitrary branching):
   ```
   RoseTree = μα. Nat × (List α)
   -- Each node has a value and list of children
   ```

4. **Optional type**:
   ```
   Maybe = μα. Unit + Nat
   -- But actually Maybe is NOT recursive! Just Unit + Nat
   -- Recursive types are for self-referential structures
   ```

5. **Pattern**: The type `μα. F(α)` where F is a type operator.

### Self-Check Questions
- [ ] How do you encode binary trees?
- [ ] What makes a structure truly need recursion?
- [ ] What's the general pattern for μ types?

---

## Lesson 5: Streams and Infinite Data (2-3 hours)

### Learning Goals
- Understand infinite structures
- Work with streams
- See codata perspective

### Activities

1. **Read** README.md section: Streams (Infinite Data)

2. **Stream type**:
   ```
   Stream = μα. Nat × α
   -- A Nat followed by... more stream (forever!)
   ```

3. **Stream constructors** (need general recursion):
   ```
   ones = fold [Stream] <1, ones>  -- Infinite stream of 1s
   nats = λn:Nat. fold [Stream] <n, nats (n+1)>  -- 0, 1, 2, ...
   ```

4. **Stream operations**:
   ```
   head = λs:Stream. fst (unfold [Stream] s)
   tail = λs:Stream. snd (unfold [Stream] s)
   take = λn:Nat. λs:Stream. ...  -- Get first n elements
   ```

5. **Data vs Codata**:
   - Lists: Finite, constructed inductively
   - Streams: Infinite, observed coinductively

### Self-Check Questions
- [ ] How do streams differ from lists structurally?
- [ ] Why do streams need general recursion?
- [ ] What's the difference between data and codata?

---

## Lesson 6: Self-Application and the Y Combinator (2-3 hours)

### Learning Goals
- See how μ types enable self-application
- Understand typed omega combinator
- See connection to general recursion

### Activities

1. **Read** README.md sections: Self-Application, Termination

2. **The problem in STLC**:
   ```
   λx. x x    -- What's x's type? T = T → S? Impossible!
   ```

3. **The solution with μ**:
   ```
   SelfApp = μα. α → Nat

   omega = λx:SelfApp. (unfold [SelfApp] x) x
   -- This type checks!
   ```

4. **Typed Y combinator**:
   ```
   fix : (T → T) → T
   fix = λf. (λx. f ((unfold x) x)) (fold (λx. f ((unfold x) x)))
   ```

5. **Non-termination**:
   ```
   loop = omega (fold [SelfApp] omega)
   -- Reduces forever: omega (fold omega) → omega (fold omega) → ...
   ```

### Self-Check Questions
- [ ] Why can't STLC type self-application?
- [ ] How do μ types solve this?
- [ ] What's the consequence for termination?

---

## Lesson 7: Iso vs Equi-Recursive (2-3 hours)

### Learning Goals
- Compare two semantic approaches
- Understand trade-offs
- See real language choices

### Activities

1. **Read** README.md section: Comparison: Iso-recursive vs Equi-recursive

2. **Iso-recursive** (our approach):
   ```
   μα.T ≠ T[μα.T/α]     -- NOT equal
   Need explicit fold/unfold
   ```

3. **Equi-recursive**:
   ```
   μα.T = T[μα.T/α]     -- Equal types!
   Implicit coercions
   ```

4. **Comparison**:
   | Aspect | Iso-recursive | Equi-recursive |
   |--------|---------------|----------------|
   | Equality | ≅ (iso) | = (equal) |
   | Operations | Explicit | Implicit |
   | Type checking | Simpler | More complex |
   | Annotation | Needed | Less needed |

5. **Language choices**:
   - OCaml, Haskell, Rust: Iso-recursive
   - Some ML dialects: Equi-recursive

### Self-Check Questions
- [ ] What's the main difference between approaches?
- [ ] Which is easier for type checking?
- [ ] Which requires more annotations?

---

## Lesson 8: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Encode data structures
   - Fold/unfold practice
   - Y combinator derivation
   - Mutual recursion encoding

2. **Run all tests**:
   ```bash
   stack test
   ```

3. **Challenge problems**:
   - Implement sized types with μ
   - Encode mutual recursion
   - Add positive occurrence check

4. **Self-assessment**: Can you...
   - [ ] Define recursive types with μ?
   - [ ] Use fold and unfold correctly?
   - [ ] Encode lists and trees?
   - [ ] Explain the fixed point connection?

---

## Progress Tracker

### Lesson 1: Self-Reference
- [ ] Understood the need
- [ ] Learned μ notation
- [ ] Can read μ types

### Lesson 2: Iso-Recursive
- [ ] Know the isomorphism
- [ ] Understand fold/unfold
- [ ] Know typing rules

### Lesson 3: Lists
- [ ] Can encode list type
- [ ] Can write constructors
- [ ] Can write destructors

### Lesson 4: Trees
- [ ] Can encode trees
- [ ] Understand the pattern
- [ ] Can design new structures

### Lesson 5: Streams
- [ ] Understand infinite data
- [ ] Know stream operations
- [ ] Grasp codata

### Lesson 6: Self-Application
- [ ] Understand SelfApp type
- [ ] See recursion connection
- [ ] Know termination impact

### Lesson 7: Comparison
- [ ] Know both approaches
- [ ] Understand trade-offs
- [ ] Know language choices

### Lesson 8: Exercises
- [ ] Completed exercises
- [ ] Tests pass
- [ ] Can apply concepts

---

## Key Takeaways

1. **μα.T**: Type α where T can refer to α (the whole type)
2. **Iso-recursive**: μα.T ≅ T[μα.T/α] with explicit fold/unfold
3. **fold**: Wrap into recursive type
4. **unfold**: Unwrap from recursive type
5. **Enables**: Self-reference, general recursion, infinite data

## Next Steps

After mastering this chapter:
- **Chapter 16 (HoTT)**: Higher inductive types generalize μ
- **Research**: Sized types, positive types, equi-recursive algorithms
- **Practice**: Implement more data structures
