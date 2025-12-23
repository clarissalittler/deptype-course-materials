# Chapter 15: Recursive Types (μ Types) - Tutorial

This tutorial walks through recursive types with step-by-step examples.

## Part 1: The Need for Recursive Types

### The Problem

Consider defining a list type in simply typed lambda calculus:

```
List Nat = ???

-- A list is either:
--   Empty (no elements), OR
--   An element followed by... another list!
```

How do we express "another list" without naming List?

### The Solution: μ Types

The μ (mu) type constructor enables self-reference:

```
NatList = μα. Unit + (Nat × α)
```

Reading this:
- `μα.` binds type variable α
- `Unit + (Nat × α)` is the body
- `Unit` represents the empty list case
- `Nat × α` represents an element paired with the rest (α)
- `α` refers to NatList itself!

### Unfolding the Definition

What does NatList "really" look like?

```
NatList = μα. Unit + (Nat × α)

One unfolding:
  = Unit + (Nat × NatList)

Two unfoldings:
  = Unit + (Nat × (Unit + (Nat × NatList)))

And so on...
```

## Part 2: Iso-Recursive Semantics

### The Key Insight

In iso-recursive types:
```
μα.T ≅ T[μα.T/α]
```

The types are **isomorphic** but **not equal**!

For NatList:
```
μα. Unit + (Nat × α) ≅ Unit + (Nat × NatList)
```

### Fold and Unfold

We need explicit operations to move between the types:

**fold**: Go from unfolded to folded
```
fold : T[μα.T/α] → μα.T
```

**unfold**: Go from folded to unfolded
```
unfold : μα.T → T[μα.T/α]
```

### Typing Rules

```
   Γ ⊢ t : T[μα.T/α]
───────────────────────────   (T-Fold)
Γ ⊢ fold [μα.T] t : μα.T

      Γ ⊢ t : μα.T
───────────────────────────────   (T-Unfold)
Γ ⊢ unfold [μα.T] t : T[μα.T/α]
```

### Evaluation

Fold and unfold cancel:
```
unfold (fold v) → v
```

This makes sense: they're inverse operations!

## Part 3: Building Lists

### The List Type

```
NatList = μα. Unit + (Nat × α)
```

Unfolded type:
```
Unit + (Nat × NatList)
```

### Constructor: nil

Empty list is `inl unit`:

```
nil : NatList
nil = fold [NatList] (inl unit)
```

Step by step:
1. `unit : Unit`
2. `inl unit : Unit + (Nat × NatList)`  -- left injection
3. `fold [NatList] (inl unit) : NatList`  -- wrap up

### Constructor: cons

Non-empty list is `inr <element, rest>`:

```
cons : Nat → NatList → NatList
cons = λn:Nat. λl:NatList.
  fold [NatList] (inr <n, l>)
```

Step by step:
1. `<n, l> : Nat × NatList`  -- pair
2. `inr <n, l> : Unit + (Nat × NatList)`  -- right injection
3. `fold [NatList] (inr <n, l>) : NatList`  -- wrap up

### Building a List

```
[1, 2, 3] = cons 1 (cons 2 (cons 3 nil))
```

Expanded:
```
fold (inr <1, fold (inr <2, fold (inr <3, fold (inl unit)>)>)>)
```

### Destructor: isEmpty

```
isEmpty : NatList → Bool
isEmpty = λl:NatList.
  case unfold [NatList] l of
    inl _ => true     -- left = empty
  | inr _ => false    -- right = non-empty
```

### Destructor: head

```
head : NatList → Nat
head = λl:NatList.
  case unfold [NatList] l of
    inl _ => 0       -- error case
  | inr p => fst p   -- first of pair
```

### Destructor: tail

```
tail : NatList → NatList
tail = λl:NatList.
  case unfold [NatList] l of
    inl _ => nil     -- error case
  | inr p => snd p   -- second of pair
```

## Part 4: Binary Trees

### Tree Type

```
Tree = μα. Nat + (α × α)
```

Reading:
- `Nat`: Leaf with a number
- `α × α`: Branch with two subtrees

### Constructors

```
leaf : Nat → Tree
leaf = λn:Nat. fold [Tree] (inl n)

branch : Tree → Tree → Tree
branch = λl:Tree. λr:Tree. fold [Tree] (inr <l, r>)
```

### Example Tree

```
    *
   / \
  1   *
     / \
    2   3

= branch (leaf 1) (branch (leaf 2) (leaf 3))
```

### Tree Sum

```
treeSum : Tree → Nat
treeSum = λt:Tree.
  case unfold [Tree] t of
    inl n => n                           -- leaf value
  | inr p => treeSum (fst p) + treeSum (snd p)  -- sum children
```

## Part 5: Streams (Infinite Data)

### Stream Type

```
Stream = μα. Nat × α
```

Note: No `Unit +`! There's no empty case—streams are infinite!

### Stream of Ones

```
ones : Stream
ones = fold [Stream] <1, ones>   -- Needs general recursion!
```

Structure: `<1, <1, <1, ...>>>` forever.

### Natural Numbers Stream

```
nats : Nat → Stream
nats = λn:Nat. fold [Stream] <n, nats (succ n)>
```

`nats 0 = <0, <1, <2, ...>>>`

### Stream Operations

```
head : Stream → Nat
head = λs:Stream. fst (unfold [Stream] s)

tail : Stream → Stream
tail = λs:Stream. snd (unfold [Stream] s)

-- Get first n elements as list
take : Nat → Stream → NatList
take = λn:Nat. λs:Stream.
  if iszero n then nil
  else cons (head s) (take (pred n) (tail s))
```

## Part 6: Self-Application

### The Problem

In STLC, we cannot type self-application:

```
λx. x x
```

What type would x have? If x : T, then we need T = T → S, which is impossible!

### The Solution

With recursive types:

```
SelfApp = μα. α → Nat
```

Unfolded:
```
SelfApp → Nat
```

### The Omega Combinator

```
omega : SelfApp → Nat
omega = λx:SelfApp. (unfold [SelfApp] x) x
```

Why this works:
1. `x : SelfApp`
2. `unfold [SelfApp] x : SelfApp → Nat`
3. `(unfold [SelfApp] x) x : Nat`  ✓

### The Danger

```
loop = omega (fold [SelfApp] omega)
```

This loops forever:
```
  omega (fold omega)
→ (unfold (fold omega)) (fold omega)
→ omega (fold omega)
→ ...
```

Recursive types break strong normalization!

## Practice Problems

### Problem 1: Maybe Type

Define an option type (Maybe Nat):

```
Maybe = μα. ???
```

<details>
<summary>Solution</summary>

Actually, Maybe doesn't need recursion!

```
Maybe = Unit + Nat    -- Not recursive!

nothing = inl unit
just = λn:Nat. inr n
```

But we COULD write it as:
```
Maybe = μα. Unit + Nat    -- α unused in body = non-recursive
```
</details>

### Problem 2: String Type

Define strings as lists of booleans (simplified):

```
String = ???
```

<details>
<summary>Solution</summary>

```
String = μα. Unit + (Bool × α)

emptyString = fold [String] (inl unit)
appendChar = λc:Bool. λs:String. fold [String] (inr <c, s>)
```
</details>

### Problem 3: Rose Tree

Define a tree where each node has a value and a LIST of children:

```
RoseTree = μα. Nat × ???
```

<details>
<summary>Solution</summary>

```
-- First, define List of RoseTrees
ListRT = μβ. Unit + (RoseTree × β)

-- Then RoseTree (mutual recursion is tricky!)
RoseTree = μα. Nat × (μβ. Unit + (α × β))
```

Or, nest the definitions:
```
RoseTree = μα. Nat × (List α)
  where List β = μγ. Unit + (β × γ)
```
</details>

### Problem 4: Unfold Practice

What's the type after unfolding `Tree = μα. Nat + (α × α)` once?

<details>
<summary>Solution</summary>

```
Nat + (Tree × Tree)
```

Substituting `Tree` for `α` in the body.
</details>

### Problem 5: Why Wrong?

Why doesn't this work?

```
bad : NatList
bad = inl unit
```

<details>
<summary>Solution</summary>

`inl unit` has type `Unit + (Nat × NatList)`, but we need `NatList`.

Missing the fold!

```
good : NatList
good = fold [NatList] (inl unit)
```
</details>
