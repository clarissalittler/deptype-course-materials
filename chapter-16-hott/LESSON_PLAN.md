# Chapter 16: Homotopy Type Theory - Lesson Plan

**Estimated Total Time**: 16-20 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Dependent types (Chapter 7-8)
- [ ] Basic understanding of equality types
- [ ] Familiarity with induction principles
- [ ] Some exposure to topology is helpful but not required

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain the geometric interpretation of types as spaces
2. Understand identity types as paths
3. Use the J eliminator (path induction)
4. Work with path operations: sym, trans, ap, transport
5. Appreciate the groupoid structure of types
6. Understand the conceptual foundation of univalence

---

## Lesson 1: Types as Spaces (2-3 hours)

### Learning Goals
- Understand the geometric perspective on types
- See the intuition behind "types as spaces"
- Learn basic terminology

### Activities

1. **Read** README.md sections: Overview, Key Concepts (Identity Types as Paths)

2. **The geometric perspective**:
   ```
   Types     ↔  Spaces
   Terms     ↔  Points
   Equalities ↔  Paths
   ```

3. **Examples**:
   ```
   Bool = discrete space with two points
   Nat = discrete space with infinitely many points
   Unit = space with one point (contractible)
   ```

4. **Key insight**:
   - `a = b` is not just a proposition (true/false)
   - It's a TYPE whose elements are paths from a to b
   - There can be many different paths!

5. **Identity type notation**:
   ```
   Id A a b     -- The type of paths from a to b in A
   a =_A b      -- Alternative notation
   ```

### Self-Check Questions
- [ ] What does it mean to interpret types as spaces?
- [ ] What are paths in this interpretation?
- [ ] Can there be multiple paths between two points?

---

## Lesson 2: Reflexivity and Path Induction (2-3 hours)

### Learning Goals
- Understand refl as the trivial path
- Master the J eliminator
- See path induction in action

### Activities

1. **Read** README.md sections: Reflexivity (refl), Path Induction (J)

2. **Reflexivity**:
   ```
   refl : (a : A) → Id A a a
   ```
   The "staying in place" path—a constant path at a.

3. **The J eliminator** (path induction):
   ```
   J : (C : (x y : A) → Id A x y → Type) →
       ((x : A) → C x x refl) →
       (a b : A) → (p : Id A a b) →
       C a b p
   ```

4. **Understanding J**:
   - C is the "motive"—what we want to prove about paths
   - Base case: prove it for refl
   - J extends this to ALL paths

5. **Computation rule**:
   ```
   J C base a a refl = base a
   ```
   J on refl reduces to the base case.

### Self-Check Questions
- [ ] What does refl represent geometrically?
- [ ] Why is it sufficient to prove things for refl?
- [ ] What is the computation rule for J?

---

## Lesson 3: Path Operations (2-3 hours)

### Learning Goals
- Derive symmetry (path inverse)
- Derive transitivity (path composition)
- See how J gives these operations

### Activities

1. **Read** README.md sections: Path Operations (sym, trans)

2. **Symmetry** (path inverse):
   ```
   sym : Id A a b → Id A b a
   sym p = J (λx y _. Id A y x) (λx. refl) a b p
   ```
   Think: reverse the direction of the path.

3. **Transitivity** (path composition):
   ```
   trans : Id A a b → Id A b c → Id A a c
   trans refl q = q
   ```
   Think: walk p then walk q.

4. **The pattern**:
   - Define using J
   - Base case: what happens on refl
   - J extends to all paths

5. **Visualize**:
   ```
   a --p--> b       becomes    a --sym p--> b  (reversed)

   a --p--> b --q--> c   becomes   a --trans p q--> c  (composed)
   ```

### Self-Check Questions
- [ ] What does sym do to a path?
- [ ] What does trans do with two paths?
- [ ] How does J help define these operations?

---

## Lesson 4: ap and transport (2-3 hours)

### Learning Goals
- Understand functoriality (ap)
- Understand transport (path lifting)
- See these as derived from J

### Activities

1. **Read** README.md sections: Path Operations (ap, transport)

2. **ap** (action on paths / functoriality):
   ```
   ap : (f : A → B) → Id A a b → Id B (f a) (f b)
   ap f refl = refl
   ```
   Functions preserve paths!

3. **Intuition for ap**:
   ```
   f : A → B is continuous (in topology sense)
   Path in A maps to path in B
   ```

4. **transport** (path lifting):
   ```
   transport : (P : A → Type) → Id A a b → P a → P b
   transport P refl x = x
   ```
   Paths let us move between fibers.

5. **Intuition for transport**:
   ```
   P is a family of types over A
   Path from a to b in A
   Lifts to path from P(a) to P(b)
   ```

### Self-Check Questions
- [ ] What does ap f p produce?
- [ ] What does transport P p x produce?
- [ ] Why is transport useful?

---

## Lesson 5: Path Algebra (Groupoid Laws) (2-3 hours)

### Learning Goals
- See paths form a groupoid
- Understand the groupoid laws
- Realize these are paths between paths

### Activities

1. **Read** README.md sections: Path Algebra

2. **Groupoid laws**:
   ```
   Left identity:  trans refl p = p
   Right identity: trans p refl = p
   Inverses:       trans p (sym p) = refl
   Associativity:  trans (trans p q) r = trans p (trans q r)
   ```

3. **Key insight**: These equalities are themselves paths!
   ```
   trans refl p = p
   -- This is a path (2-path) between trans refl p and p
   ```

4. **Higher structure**:
   - Paths between points (1-paths)
   - Paths between paths (2-paths)
   - Paths between paths between paths (3-paths)
   - This continues infinitely (∞-groupoid)

5. **Why "groupoid"?**:
   - Like a group, but with multiple objects
   - Every morphism (path) has an inverse (sym)
   - Composition (trans) is associative

### Self-Check Questions
- [ ] What are the four groupoid laws?
- [ ] What does it mean that laws are "paths between paths"?
- [ ] Why is this structure called a groupoid?

---

## Lesson 6: J in Depth (2-3 hours)

### Learning Goals
- Deeply understand J's universality
- Derive complex operations from J
- See J as the fundamental principle

### Activities

1. **Study** J's type more carefully:
   ```
   J : (C : (x y : A) → Id A x y → Type) →
       ((x : A) → C x x refl) →
       (a b : A) → (p : Id A a b) →
       C a b p
   ```

2. **Why J is powerful**:
   - ANY property of paths reduces to refl case
   - Based on the fact that all paths are "the same"
   - (Technically: based points are contractible)

3. **Deriving sym with J**:
   ```
   C = λx y p. Id A y x
   base = λx. refl
   J C base a b p : Id A b a
   ```

4. **Deriving transport with J**:
   ```
   C = λx y p. P x → P y
   base = λx. λz. z    -- identity function
   J C base a b p : P a → P b
   ```

5. **J's limitations**:
   - Gives definitional equality only on refl
   - Other paths give propositional equality
   - This affects proof complexity

### Self-Check Questions
- [ ] How does J's motive C work?
- [ ] Why is the base case sufficient?
- [ ] How do you derive transport from J?

---

## Lesson 7: Univalence and Higher Types (2-3 hours)

### Learning Goals
- Understand the univalence principle
- See higher inductive types
- Appreciate h-levels

### Activities

1. **Read** README.md sections: The Bigger Picture

2. **Univalence axiom**:
   ```
   (A ≃ B) ≃ (A = B)
   ```
   Equivalent types are equal!

3. **Implications of univalence**:
   - Function extensionality
   - Structure identity principle
   - Isomorphic types are interchangeable

4. **Higher inductive types** (HITs):
   ```
   data S¹ where
     base : S¹
     loop : Id S¹ base base   -- A non-trivial path!
   ```
   Types with both points AND paths as constructors.

5. **h-levels**:
   ```
   -2: Contractible (unique up to path)
   -1: Propositions (at most one element)
    0: Sets (equality is propositional)
    1: Groupoids (paths form sets)
   ...
   ```

### Self-Check Questions
- [ ] What does univalence say?
- [ ] What makes higher inductive types special?
- [ ] What is an h-level?

---

## Lesson 8: Exercises and Mastery (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Path algebra proofs
   - J eliminator practice
   - Transport examples
   - Conceptual univalence problems

2. **Run all tests**:
   ```bash
   stack test
   ```

3. **Challenge problems**:
   - Prove associativity of trans
   - Derive ap from J
   - Understand the circle S¹

4. **Self-assessment**: Can you...
   - [ ] Explain types-as-spaces?
   - [ ] Use J to define operations?
   - [ ] Work with path algebra?
   - [ ] Explain univalence conceptually?

---

## Progress Tracker

### Lesson 1: Types as Spaces
- [ ] Understood geometric perspective
- [ ] Learned terminology
- [ ] See types as spaces

### Lesson 2: refl and J
- [ ] Understand refl
- [ ] Know J's type
- [ ] See computation rule

### Lesson 3: sym and trans
- [ ] Can use symmetry
- [ ] Can use transitivity
- [ ] Derive from J

### Lesson 4: ap and transport
- [ ] Understand functoriality
- [ ] Understand path lifting
- [ ] See uses

### Lesson 5: Path Algebra
- [ ] Know groupoid laws
- [ ] Understand higher paths
- [ ] See groupoid structure

### Lesson 6: J in Depth
- [ ] Deep J understanding
- [ ] Can derive operations
- [ ] Know limitations

### Lesson 7: Univalence
- [ ] Understand the axiom
- [ ] Know about HITs
- [ ] Understand h-levels

### Lesson 8: Exercises
- [ ] Completed exercises
- [ ] Tests pass
- [ ] Can apply concepts

---

## Key Takeaways

1. **Types are spaces**: Points, paths, paths between paths...
2. **refl**: The trivial/constant path at a point
3. **J eliminator**: Reduce path problems to refl case
4. **Path operations**: sym, trans, ap, transport
5. **Univalence**: Equivalent types are equal

## Next Steps

After mastering this chapter:
- **Cubical Type Theory**: Constructive univalence
- **Proof assistants**: Agda (--cubical), Arend
- **Research**: HITs, synthetic homotopy theory
- **The HoTT Book**: Full treatment of the subject
