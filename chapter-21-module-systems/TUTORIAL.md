# Tutorial: Learning Module Systems Step-by-Step

This tutorial will guide you through module systems from basic concepts to advanced features.

## Prerequisites

- Understanding of simply typed lambda calculus (STLC)
- Familiarity with records and basic types
- Completed chapters 1-3 of this course (recommended)

## Setup

```bash
cd chapter-21-module-systems
stack build
stack run module-systems-repl
```

You should see:
```
===========================================
Module Systems REPL
===========================================
modules>
```

## Part 1: Basic Structures

### Step 1: Your First Structure

A structure is a module containing definitions. Let's create the simplest possible structure:

```
modules> struct val x : Nat = 5 end
  : sig
      val x : Nat
    end
```

**What happened?**
- We defined a structure with one value `x` of type `Nat` equal to `5`
- The REPL showed us the signature: `sig val x : Nat end`
- This signature tells us what the module provides

### Step 2: Multiple Components

Structures can contain multiple values:

```
modules> struct val x : Nat = 5 val y : Bool = true end
  : sig
      val x : Nat
      val y : Bool
    end
```

### Step 3: Adding Types

Structures can define types as well as values:

```
modules> struct type t = Nat val x : t = 0 end
  : sig
      type t = Nat
      val x : t
    end
```

Notice how `x` uses the type `t` we just defined!

### Step 4: Named Modules

Use `:mod` to give a module a name:

```
modules> :mod Counter = struct val count : Nat = 0 end
module Counter : sig
                   val count : Nat
                 end
```

Now you can reference it by name:

```
modules> Counter
Counter : sig
            val count : Nat
          end
```

**Exercise 1:** Create a module called `Point` with two natural number fields `x` and `y`.

<details>
<summary>Solution</summary>

```
:mod Point = struct val x : Nat = 0 val y : Nat = 0 end
```
</details>

## Part 2: Signatures

### Step 5: Understanding Signatures

A signature specifies what a module must provide. It's like an interface or contract.

Syntax:
```
sig
  val x : Nat
  val y : Bool
  type t
end
```

Signatures contain **specifications** (specs):
- `val x : Nat` - value specification
- `type t` - abstract type specification
- `type t = Nat` - manifest (concrete) type specification

### Step 6: Signature Matching

A module **matches** a signature if it provides everything the signature requires (and possibly more).

Example:
```
modules> :mod M = struct val x : Nat = 5 val y : Bool = true val z : Nat = 10 end
module M : sig
             val x : Nat
             val y : Bool
             val z : Nat
           end
```

This module matches the signature `sig val x : Nat end` because it provides `x : Nat` (and more).

**Key insight:** Modules can have MORE than the signature requires. This is called **width subtyping**.

### Step 7: Abstract vs. Manifest Types

**Manifest type** (concrete):
```
sig
  type t = Nat
  val x : t
end
```
Clients can see that `t = Nat`.

**Abstract type** (opaque):
```
sig
  type t
  val x : t
end
```
Clients know `t` exists but can't see its definition.

**Exercise 2:** What's the difference between these two signatures?
```
sig type counter = Nat val get : counter end
sig type counter val get : counter end
```

<details>
<summary>Answer</summary>

First signature: `counter`'s definition is visible (manifest)
Second signature: `counter` is abstract (hidden)

Abstract types enable information hiding!
</details>

## Part 3: Sealing (Signature Ascription)

### Step 8: Hiding Extra Components

Sealing restricts a module to a signature:

```
modules> (struct val x : Nat = 5 val secret : Nat = 42 end :> sig val x : Nat end)
  : sig
      val x : Nat
    end
```

After sealing, `secret` is hidden! Only `x` is visible.

**Syntax:** `(Module :> Signature)`

### Step 9: Making Types Abstract

This is the most powerful use of sealing:

```
modules> :mod Stack = (struct type t = Nat val empty : t = 0 end :> sig type t val empty : t end)
module Stack : sig
                 type t
                 val empty : t
               end
```

Now `Stack.t` is abstract. Clients can't see that it's `Nat`!

**Why is this useful?**
- Information hiding: Change implementation without breaking clients
- Type safety: Prevent misuse of internal representation
- Abstraction: Enforce invariants

### Step 10: Practical Example - Abstract Stack

Let's build a more realistic stack:

```
:mod Stack = (
  struct
    type stack = Nat
    val empty : stack = 0
    val push : Nat -> stack -> stack = \n:Nat. \s:stack. succ s
    val size : stack -> Nat = \s:stack. s
  end
  :>
  sig
    type stack
    val empty : stack
    val push : Nat -> stack -> stack
    val size : stack -> Nat
  end
)
```

**What we did:**
1. Defined concrete type `stack = Nat` (using Nat to track size, simplified)
2. Implemented operations
3. Sealed to hide that `stack = Nat`

Clients can use the stack but can't create invalid stacks!

**Exercise 3:** What happens if you try to use a `Nat` where a `stack` is expected?

<details>
<summary>Answer</summary>

It fails! Even though `stack` is internally `Nat`, after sealing it's an abstract type. Type checker prevents confusion.
</details>

## Part 4: Functors

### Step 11: Your First Functor

A functor is a function from modules to modules.

**Syntax:**
```
functor(ParamName : ParamSignature) => BodyModule
```

Example - increment functor:
```
:mod Inc = functor(X : sig val n : Nat end) =>
             struct val m : Nat = succ X.n end
```

**What this means:**
- `Inc` is a functor
- It takes a module `X` with signature `sig val n : Nat end`
- It returns a module with `m = succ X.n`

### Step 12: Applying Functors

Apply a functor to a module:

```
modules> (Inc)(struct val n : Nat = 5 end)
  : sig
      val m : Nat
    end
  = struct val m : Nat = 6 end
```

**Syntax:** `(Functor)(Argument)`

The result is a new module!

### Step 13: Parameterized Data Structures

Functors enable generic programming. Example - pairs:

```
:mod MakePair = functor(Elem : sig type t end) =>
  struct
    type elem = Elem.t
    type pair = {fst: elem, snd: elem}
    val make : elem -> elem -> pair =
      \a:elem. \b:elem. {fst = a, snd = b}
  end
```

Now instantiate for natural numbers:

```
:mod NatPair = (MakePair)(struct type t = Nat end)
```

And for booleans:

```
:mod BoolPair = (MakePair)(struct type t = Bool end)
```

**Key insight:** Write the code once, instantiate for any type!

### Step 14: Multiple Parameters

Functors can take multiple parameters by nesting:

```
:mod MakePairOfTwo = functor(T1 : sig type t end) =>
  functor(T2 : sig type u end) =>
    struct
      type pair = {fst: T1.t, snd: T2.u}
    end
```

Apply it:
```
:mod NatBoolPair = ((MakePairOfTwo)(struct type t = Nat end))
                                   (struct type u = Bool end)
```

**Exercise 4:** Write a functor that takes a module with `val n : Nat` and returns a module that doubles it.

<details>
<summary>Solution</summary>

```
:mod Double = functor(X : sig val n : Nat end) =>
  struct
    val result : Nat = succ (succ X.n)
  end
```

Test it:
```
(Double)(struct val n : Nat = 3 end)
-- Should give: struct val result : Nat = 6 end (if we had addition)
```
</details>

## Part 5: Nested Modules

### Step 15: Modules Inside Modules

Structures can contain module definitions:

```
:mod Library = struct
  module Math = struct
    val id : Nat -> Nat = \x:Nat. x
  end

  module Utils = struct
    val const : Nat = 42
  end
end
```

Access nested components:
```
Library.Math.id
Library.Utils.const
```

### Step 16: Organizing Code

Use nested modules to organize related functionality:

```
:mod DataStructures = struct
  module Stack = struct
    type t = Nat
    val empty : t = 0
  end

  module Queue = struct
    type t = Bool  -- simplified
    val empty : t = false
  end
end
```

**Exercise 5:** Create a module `Geometry` with nested modules `Circle` and `Rectangle`, each with a `val name : Bool` (simplified, using Bool as string).

<details>
<summary>Solution</summary>

```
:mod Geometry = struct
  module Circle = struct
    val name : Bool = true
  end

  module Rectangle = struct
    val name : Bool = false
  end
end
```
</details>

## Part 6: Real-World Patterns

### Pattern 1: Abstract Data Type (ADT)

Combine abstract types with operations:

```
:mod Counter = (
  struct
    type counter = Nat
    val zero : counter = 0
    val increment : counter -> counter = \c:counter. succ c
    val value : counter -> Nat = \c:counter. c
  end
  :>
  sig
    type counter
    val zero : counter
    val increment : counter -> counter
    val value : counter -> Nat
  end
)
```

**Benefits:**
- `counter` is abstract - representation hidden
- Can change implementation without breaking clients
- Type safety: can't misuse counters

### Pattern 2: Functor for Code Reuse

```
:mod MakeContainer = functor(Element : sig type t end) =>
  struct
    type elem = Element.t
    type container = {value: elem}
    val make : elem -> container = \x:elem. {value = x}
    val get : container -> elem = \c:container. c.value
  end
```

Instantiate multiple times:
```
:mod IntContainer = (MakeContainer)(struct type t = Nat end)
:mod BoolContainer = (MakeContainer)(struct type t = Bool end)
```

### Pattern 3: Signature Constraints

Use signatures to enforce interfaces:

```
sig
  type t
  val compare : t -> t -> Bool
  val equal : t -> t -> Bool
end
```

Any module matching this signature must provide `compare` and `equal` for type `t`.

### Pattern 4: Layered Abstraction

Build complex modules from simpler ones:

```
:mod Base = struct
  type t = Nat
  val zero : t = 0
end

:mod Extended = struct
  module B = Base
  val one : B.t = succ B.zero
end
```

**Exercise 6:** Create an abstract `Stack` module with `push`, `empty`, and `isEmpty` operations. Use sealing to hide the representation.

<details>
<summary>Solution</summary>

```
:mod Stack = (
  struct
    type stack = Nat
    val empty : stack = 0
    val push : Nat -> stack -> stack = \n:Nat. \s:stack. succ s
    val isEmpty : stack -> Bool = \s:stack. iszero s
  end
  :>
  sig
    type stack
    val empty : stack
    val push : Nat -> stack -> stack
    val isEmpty : stack -> Bool
  end
)
```
</details>

## Part 7: Advanced Topics

### Functor Composition

Functors can be composed:

```
:mod F = functor(X : sig val n : Nat end) =>
           struct val m : Nat = succ X.n end

:mod G = functor(Y : sig val m : Nat end) =>
           struct val p : Nat = succ Y.m end

:mod Input = struct val n : Nat = 5 end

:mod Result = (G)((F)(Input))
-- Result.p should be 7 (5 + 1 + 1)
```

### Type Abstraction Boundaries

Abstract types create abstraction boundaries:

```
:mod M1 = (struct type t = Nat val x : t = 0 end
           :> sig type t val x : t end)

:mod M2 = (struct type t = Nat val x : t = 0 end
           :> sig type t val x : t end)
```

Even though both have `type t`, `M1.t` and `M2.t` are DIFFERENT types! They're incompatible.

This prevents accidental confusion between different abstract types.

## Summary

You've learned:

1. ✅ **Structures** - concrete modules with definitions
2. ✅ **Signatures** - module types specifying requirements
3. ✅ **Sealing** - hiding implementation details
4. ✅ **Abstract types** - information hiding for types
5. ✅ **Functors** - parameterized modules
6. ✅ **Nested modules** - organizing code hierarchically
7. ✅ **Signature matching** - width subtyping
8. ✅ **Real-world patterns** - ADTs, code reuse, layering

## Next Steps

1. **Practice**: Try the exercises in [PRACTICE_PROBLEMS.md](PRACTICE_PROBLEMS.md)
2. **Deep Dive**: Read [README.md](README.md) for formal typing rules
3. **Explore**: Check out `:examples` in the REPL
4. **Questions**: See [FAQ.md](FAQ.md) for common issues
5. **Compare**: Study real module systems (SML, OCaml)

## Key Takeaways

- **Modules organize code** at a higher level than functions
- **Signatures specify interfaces** - what modules must provide
- **Sealing enables information hiding** - implementation details stay hidden
- **Functors enable parameterization** - write code once, instantiate many times
- **Abstract types provide type safety** - prevent representation exposure

Module systems are essential for building large, maintainable programs with strong abstraction boundaries!

## Further Reading

- Chapter 24 of "Types and Programming Languages" (Pierce)
- "Advanced Topics in Types and Programming Languages" (Pierce) - Module Systems chapter
- SML documentation: [smlnj.org](https://www.smlnj.org/)
- OCaml documentation: [ocaml.org/manual/moduleexamples.html](https://ocaml.org/manual/moduleexamples.html)

Happy module programming! 🎉
