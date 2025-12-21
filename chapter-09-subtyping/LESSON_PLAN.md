# Chapter 9: Subtyping - Lesson Plan

**Estimated Total Time**: 14-18 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus (Chapter 2)
- [ ] Records and projections (Chapter 3)
- [ ] Type checking algorithms
- [ ] Basic set theory (subsets, unions, intersections)

## Learning Objectives

By the end of this chapter, you will be able to:
1. Explain the subtyping relation and its intuition
2. Understand covariance and contravariance
3. Implement a subtyping algorithm for functions and records
4. Compute joins and meets of types
5. Apply subsumption in type checking
6. Connect subtyping to object-oriented programming concepts

---

## Lesson 1: Introduction to Subtyping (2-3 hours)

### Learning Goals
- Understand the motivation for subtyping
- Learn the basic subtyping rules (reflexivity, transitivity)
- Understand Top and Bot types

### Activities

1. **Read** README.md sections: Overview, Types, Top and Bottom Types
2. **Study** the subtyping lattice diagram
3. **Explore** `src/Syntax.hs`:
   - Find where `TyTop` and `TyBot` are defined
   - Understand the `Type` data type

4. **Practice**: Write out which of these hold and why:
   - `Nat <: Nat`
   - `Bool <: Top`
   - `Bot <: Bool`
   - `Top <: Nat`

5. **Experiment** with the REPL:
   ```
   stack exec subtyping-repl
   :subtype Nat Top
   :subtype Bot Bool
   :subtype Top Nat
   ```

### Self-Check Questions
- [ ] What does `S <: T` mean intuitively?
- [ ] Why is Top called "top" in the lattice?
- [ ] Can there be a value of type Bot? Why or why not?
- [ ] What is the relationship between Top, Bot, and other types?

---

## Lesson 2: Record Subtyping (2-3 hours)

### Learning Goals
- Understand width subtyping (more fields = subtype)
- Understand depth subtyping (more specific field types = subtype)
- Combine width and depth subtyping

### Activities

1. **Read** README.md section: Record Subtyping
2. **Study** `src/TypeCheck.hs`:
   - Find the `recordSubtype` function
   - Trace through its logic

3. **Work through examples**:
   ```
   {x: Nat, y: Bool} <: {x: Nat}          -- Width
   {x: Bot} <: {x: Nat}                   -- Depth
   {x: Nat, y: Bool} <: {x: Top}          -- Width + Depth
   ```

4. **Experiment** with the REPL:
   ```
   :type {x = 0, y = true}
   :type (\r:{x: Nat}. r.x) {x = 0, y = true}
   ```

5. **Exercise**: Determine if these hold:
   - `{a: Nat, b: Bool, c: Top} <: {a: Nat, c: Top}`
   - `{x: {a: Nat}} <: {x: {a: Top, b: Bool}}`

### Self-Check Questions
- [ ] Why does having MORE fields make a record a subtype?
- [ ] How do width and depth subtyping interact?
- [ ] What happens if a field is missing in the subtype?

---

## Lesson 3: Function Subtyping (2-3 hours)

### Learning Goals
- Understand contravariance in function arguments
- Understand covariance in function results
- Apply the arrow subtyping rule

### Activities

1. **Read** README.md section: Function Subtyping
2. **Study** the S-Arrow rule carefully
3. **Work through the intuition**:
   - If `f : Animal -> String` and callers provide Dogs...
   - If `g : Dog -> Animal` and callers expect Animals...

4. **Study** `src/TypeCheck.hs`:
   - Find the function case in `subtype`
   - Note the argument direction flip: `subtype u1 s1`

5. **Practice examples**:
   ```
   (Top -> Bool) <: (Bool -> Bool)   -- contravariant arg
   (Bool -> Bot) <: (Bool -> Nat)    -- covariant result
   (Top -> Bot) <: (Nat -> Bool)     -- both
   ```

6. **Challenge**: Work out variance in `(A -> B) -> C`

### Self-Check Questions
- [ ] Why is the argument position contravariant?
- [ ] What does it mean for a function to be "substitutable"?
- [ ] If `S <: T`, is `S -> U <: T -> U`? Is `U -> S <: U -> T`?

---

## Lesson 4: Subsumption and Type Checking (2-3 hours)

### Learning Goals
- Understand the subsumption rule
- See how subtyping integrates with type checking
- Understand ascription

### Activities

1. **Read** README.md section: Typing Rules with Subsumption
2. **Study** `src/TypeCheck.hs`:
   - Find the T-Sub applications in `typeOf`
   - Study the `TmAscribe` case
   - Look at the modified `App` case

3. **Trace through type checking**:
   ```
   (\x:Top. x) true
   -- Need: true : Top (for application)
   -- Have: true : Bool
   -- Use: Bool <: Top (subsumption)
   ```

4. **Experiment** with ascription:
   ```
   :type true as Top
   :type {x = 0, y = true} as {x: Nat}
   ```

5. **Practice**: What's the type of each?
   - `(\f:Top -> Nat. f true) (\x:Top. 0)`
   - `{x = 0, y = {a = true}} as {x: Top}`

### Self-Check Questions
- [ ] Where in type checking is subsumption applied?
- [ ] What's the difference between implicit and explicit upcasting?
- [ ] Can ascription be used for downcasting?

---

## Lesson 5: Join and Meet (2-3 hours)

### Learning Goals
- Understand least upper bound (join)
- Understand greatest lower bound (meet)
- Apply join/meet to conditionals and functions

### Activities

1. **Read** README.md section: Join and Meet
2. **Study** `src/TypeCheck.hs`:
   - Find the `join` and `meet` functions
   - Trace through `joinRecords` and `meetRecords`

3. **Work through examples**:
   ```
   Nat ⊔ Bool = Top           -- no better common supertype
   {x: Nat} ⊔ {y: Bool} = {}  -- no common fields
   {x: Nat, y: Bool} ⊔ {x: Nat, z: Top} = {x: Nat}
   ```

4. **Understand conditional typing**:
   ```
   :type if true then {x=0, y=true} else {x=0, z=false}
   -- Result type is {x: Nat} (common fields)
   ```

5. **Practice**: Compute these joins and meets:
   - `(Nat -> Bool) ⊔ (Top -> Bool)`
   - `{a: Nat} ⊓ {a: Bool}`
   - `(Bot -> Top) ⊔ (Top -> Bot)`

### Self-Check Questions
- [ ] Why is join used for if-then-else branches?
- [ ] What's the join of two incompatible types?
- [ ] How does variance affect join of function types?

---

## Lesson 6: Variance Analysis (2 hours)

### Learning Goals
- Identify covariant, contravariant, and invariant positions
- Understand why mutable references are invariant
- Apply variance to design type constructors

### Activities

1. **Read** README.md section: Variance
2. **Study** variance in nested types:
   ```
   In (A -> B):
     A is in contravariant (-) position
     B is in covariant (+) position

   In ((A -> B) -> C):
     A is in (- × -) = + position (covariant!)
     B is in (+ × -) = - position (contravariant)
     C is in + position (covariant)
   ```

3. **Practice**: Find the variance of X in:
   - `X -> Bool`
   - `Bool -> X`
   - `(X -> Bool) -> Nat`
   - `((Bool -> X) -> X)`

4. **Think about**: Why are Java arrays unsound?

### Self-Check Questions
- [ ] What multiplies variance? (hint: composition)
- [ ] When is a position invariant?
- [ ] Why does mutability force invariance?

---

## Lesson 7: Exercises and Application (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Exercise 1: Subtype Relationships
   - Exercise 2: Maximum and Minimum Types
   - Exercise 3: Join and Meet
   - Exercise 6: Covariant and Contravariant Positions

2. **Run the test suite**:
   ```
   stack test
   ```
   Study the test cases to understand expected behavior.

3. **Experiment** with the REPL:
   - Try encoding simple OOP patterns
   - Test the limits of the type system

4. **Optional Challenge**: Try Exercise 5 (Bounded Quantification)

### Self-Check Questions
- [ ] Can you predict subtyping results without running code?
- [ ] Do you understand why each test case passes?
- [ ] Can you explain subtyping to someone else?

---

## Progress Tracker

Use this checklist to track your progress:

### Lesson 1: Introduction to Subtyping
- [ ] Read overview materials
- [ ] Explored Syntax.hs
- [ ] Practiced basic subtyping examples
- [ ] Used REPL for subtype checking

### Lesson 2: Record Subtyping
- [ ] Understood width subtyping
- [ ] Understood depth subtyping
- [ ] Studied recordSubtype implementation
- [ ] Completed record exercises

### Lesson 3: Function Subtyping
- [ ] Understood contravariance
- [ ] Understood covariance
- [ ] Worked through function examples
- [ ] Can explain arrow subtyping rule

### Lesson 4: Subsumption and Type Checking
- [ ] Understood subsumption rule
- [ ] Studied typeOf implementation
- [ ] Practiced with ascription
- [ ] Traced type checking examples

### Lesson 5: Join and Meet
- [ ] Understood join as LUB
- [ ] Understood meet as GLB
- [ ] Computed joins and meets manually
- [ ] Understood conditional typing

### Lesson 6: Variance Analysis
- [ ] Can identify variance positions
- [ ] Understand nested variance
- [ ] Know why mutability is invariant

### Lesson 7: Exercises and Application
- [ ] Completed core exercises
- [ ] All tests pass (74/74)
- [ ] Can explain subtyping concepts

---

## Key Takeaways

After completing this chapter, remember:

1. **Subtyping is about substitutability**: S <: T means S can be used where T is expected
2. **Width subtyping**: More fields = subtype (counterintuitive!)
3. **Function variance**: Contravariant in argument, covariant in result
4. **Join/Meet**: LUB for "either type works", GLB for "both types required"
5. **Subsumption**: Implicit upcasting at specific type checking points

## Next Steps

After mastering this chapter:
- **Chapter 10 (Linear Types)**: Resource tracking and ownership
- **Chapter 11 (Refinement Types)**: Types with logical predicates
- **Advanced reading**: F<: (bounded quantification), intersection/union types
