# Frequently Asked Questions: Module Systems

## Conceptual Questions

### Q1: What's the difference between a structure and a signature?

**A:** A **structure** is a concrete module with actual implementations:
```ocaml
struct
  val x : Nat = 5
  type t = Nat
end
```

A **signature** is a module type - it specifies what a module must provide:
```ocaml
sig
  val x : Nat
  type t
end
```

Think of it like:
- Structure = Class implementation (concrete)
- Signature = Interface (abstract specification)

### Q2: What are functors and why do I need them?

**A:** Functors are functions from modules to modules. They enable parameterized programming at the module level.

Without functors:
```ocaml
struct  -- Set of integers
  type elem = Nat
  (* set operations on Nat *)
end

struct  -- Set of booleans (duplicate code!)
  type elem = Bool
  (* set operations on Bool *)
end
```

With functors:
```ocaml
functor(Elem : sig type t end) =>
  struct
    type elem = Elem.t
    (* generic set operations *)
  end
```

Now you can instantiate for any type!

### Q3: What does sealing (:>) do?

**A:** Sealing restricts a module to a signature, hiding extra components:

```ocaml
-- Before sealing:
struct
  type t = Nat
  val x : t = 5
  val secret : Nat = 42
end

-- After sealing:
(... :> sig type t; val x : t end)
-- Now 'secret' is hidden and 't' is abstract!
```

Benefits:
1. **Information hiding**: Hide implementation details
2. **Abstraction**: Make types opaque
3. **Interface enforcement**: Only expose what's needed

### Q4: What's the difference between abstract and manifest type specs?

**A:**
- **Abstract type spec** (`type t`): Type exists but implementation is hidden
- **Manifest type spec** (`type t = Nat`): Type's definition is visible

Example:
```ocaml
-- Abstract - implementation hidden
sig
  type t
  val x : t
end

-- Manifest - implementation visible
sig
  type t = Nat
  val x : t
end
```

Abstract types enable **information hiding** - clients can't depend on the representation.

### Q5: How does signature matching work?

**A:** Module M matches signature S (written M <: S) if:

1. **Every required component is present**: M provides everything S specifies
2. **Types match**: Values have the specified types
3. **Width subtyping**: M can have MORE than S requires
4. **Abstract types are flexible**: Abstract type specs match any type

Example:
```ocaml
-- This module:
struct
  val x : Nat = 5
  val y : Bool = true
  val z : Nat = 10
end

-- Matches this signature:
sig
  val x : Nat
  val y : Bool
end
-- Extra 'z' is OK (width subtyping)
```

### Q6: Can I have recursive modules?

**A:** Our simple implementation doesn't support recursive modules, but many real module systems do (SML, OCaml):

```ocaml
module rec A : SIG_A = struct
  let f x = B.g x
end
and B : SIG_B = struct
  let g x = A.f x
end
```

This requires more complex type checking to prevent cycles.

### Q7: What's the difference between module systems and objects?

**A:**

| Feature | Module Systems | Object Systems |
|---------|---------------|----------------|
| Encapsulation | Yes (sealing) | Yes (private) |
| Parameterization | Functors | Generics/Templates |
| Type abstraction | Strong | Limited |
| First-class | Sometimes | Yes (objects are values) |
| Inheritance | No | Yes |
| Static/Compile-time | Yes | Varies |

Module systems excel at:
- Large-scale program organization
- Compile-time guarantees
- Strong type abstraction

Objects excel at:
- Runtime polymorphism
- Incremental extension
- Dynamic dispatch

## Practical Questions

### Q8: How do I define a module with multiple components?

**A:**
```ocaml
:mod MyModule = struct
  type counter = Nat
  val zero : counter = 0
  val increment : counter -> counter = \c:counter. succ c

  module Nested = struct
    val helper : Nat = 42
  end
end
```

### Q9: How do I access values from a module?

**A:** Use module projection with dot notation:
```ocaml
:mod M = struct val x : Nat = 5 end
M.x  -- Access x from M
```

For nested modules:
```ocaml
M.N.x  -- Access x from nested module N inside M
```

### Q10: How do I create a functor that takes multiple parameters?

**A:** Nest functors:
```ocaml
functor(X : sig type t end) =>
  functor(Y : sig type u end) =>
    struct
      type pair = {fst: X.t, snd: Y.u}
    end
```

Apply it:
```ocaml
(((F)(ModX))(ModY))
```

Or use a signature with multiple module specs:
```ocaml
functor(XY : sig
  module X : sig type t end
  module Y : sig type u end
end) => ...
```

### Q11: How do I hide a type's implementation?

**A:** Use sealing with an abstract type:
```ocaml
:mod Stack = (
  struct
    type t = Nat  -- Concrete implementation
    val empty : t = 0
  end
  :>
  sig
    type t  -- Abstract type (no '= Nat')
    val empty : t
  end
)

-- Now clients can't know that t = Nat!
```

### Q12: Can I partially seal a module?

**A:** Yes! Only seal what you want to hide:
```ocaml
(struct
  type secret = Nat
  type public = Bool
  val x : secret = 5
  val y : public = true
end :> sig
  type secret       -- Hide secret's definition
  type public = Bool  -- Keep public's definition visible
  val x : secret
  val y : public
end)
```

## Type Checking Questions

### Q13: Why does this signature matching fail?

```ocaml
struct val x : Nat = 5 end  -- ERROR
:> sig val x : Bool end
```

**A:** Type mismatch! The module provides `x : Nat` but the signature requires `x : Bool`. Types must match exactly (no implicit conversion).

### Q14: Why can't I access this module component after sealing?

```ocaml
:mod M = (struct val x : Nat = 5 val y : Nat = 10 end
          :> sig val x : Nat end)
M.y  -- ERROR: y is not visible!
```

**A:** Sealing hides components not in the signature. After sealing to `sig val x : Nat end`, only `x` is visible. `y` is hidden.

### Q15: Why does this functor application fail?

```ocaml
:mod F = functor(X : sig val n : Nat end) => struct val m : Nat = X.n end
(F)(struct val k : Nat = 5 end)  -- ERROR
```

**A:** The argument module has `k` but the functor expects `n`. Field names must match! Fix:
```ocaml
(F)(struct val n : Nat = 5 end)  -- OK
```

## Error Messages

### Q16: "Unbound module: M"

**A:** You're referencing a module that hasn't been defined. Define it first:
```ocaml
:mod M = struct val x : Nat = 5 end
```

### Q17: "Type mismatch in value declaration"

**A:** The term's type doesn't match the declared type:
```ocaml
val x : Nat = true  -- ERROR: true : Bool, not Nat
val x : Nat = 0     -- OK
```

### Q18: "Missing value: x"

**A:** Your module doesn't provide a required value:
```ocaml
struct val y : Nat = 5 end  -- ERROR: signature requires 'x'
:> sig val x : Nat end
```

Fix: Add the missing component:
```ocaml
struct val x : Nat = 5 val y : Nat = 10 end  -- OK
:> sig val x : Nat end
```

## Advanced Questions

### Q19: Can modules be first-class values?

**A:** In our simple system, no. But OCaml supports first-class modules:
```ocaml
let m = (module M : S)  -- Pack module as value
let module N = (val m : S) in ...  -- Unpack
```

This enables passing modules as function arguments!

### Q20: How do module systems relate to dependent types?

**A:** Module systems and dependent types both support abstraction, but:

**Module Systems:**
- Type abstraction via abstract types
- Parameterization via functors
- Phase distinction (compile/runtime)

**Dependent Types:**
- Types depend on values
- More expressive (can encode modules)
- No phase distinction

Some systems (Agda, Coq) combine both!

### Q21: What are applicative vs. generative functors?

**A:**
- **Applicative functors** (SML, OCaml with `()` syntax): Same argument → same result type
  ```ocaml
  F(M) and F(M) have the same types (type sharing)
  ```

- **Generative functors** (Standard ML): Each application generates fresh types
  ```ocaml
  F(M) and F(M) have distinct types (even with same M)
  ```

Our implementation uses applicative semantics (simpler).

### Q22: How do I prevent functor argument duplication?

**A:** Use let-bindings or sharing constraints:
```ocaml
:mod M = struct val n : Nat = 5 end
:mod Result = (F)(M)  -- Reuse M, don't duplicate
```

In real systems, you can use sharing constraints:
```ocaml
sig
  module A : S
  module B : S
  sharing type A.t = B.t
end
```

## Performance Questions

### Q23: Do modules have runtime overhead?

**A:** Depends on the language:
- **SML/OCaml**: Modules are mostly compile-time, minimal overhead
- **Our implementation**: Modules are lightweight (mostly type-checking)
- **First-class modules**: May have packing/unpacking overhead

Generally, module abstraction is zero-cost at runtime!

### Q24: Are functors expensive?

**A:** No! Functor application is typically compile-time. The compiler:
1. Type-checks the functor application
2. Instantiates the functor body
3. No runtime cost (like C++ templates)

## Debugging Tips

### Tip 1: Use `:type` to check components

```ocaml
:type M.x  -- Check the type of a module component
```

### Tip 2: Use `:env` to see what's defined

```ocaml
:env  -- Show all modules and values in context
```

### Tip 3: Build incrementally

Start with a simple module, test it, then add complexity:
```ocaml
:mod M = struct val x : Nat = 5 end  -- Start simple
:mod M = struct val x : Nat = 5 val y : Nat = 10 end  -- Add more
```

### Tip 4: Match signatures explicitly

When sealing fails, check each component:
```ocaml
-- Does my module have the right fields?
-- Do the types match exactly?
-- Are there typos in field names?
```

## Further Reading

See [README.md](README.md) for comprehensive information on:
- Typing rules
- Module system theory
- Real-world applications
- Academic papers and references
