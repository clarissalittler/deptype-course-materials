# Quick Start: Module Systems

Get started with module systems in 5 minutes!

## Installation

```bash
cd chapter-21-module-systems
stack build
```

## Run the REPL

```bash
stack run module-systems-repl
```

## Your First Module

### 1. Define a Simple Structure

```
modules> struct val x : Nat = 5 end
  : sig
      val x : Nat
    end
```

### 2. Create a Named Module

```
modules> :mod Counter = struct val count : Nat = 0 end
module Counter : sig
                   val count : Nat
                 end
```

### 3. Define a Signature

A signature specifies what a module must provide:

```
sig
  val x : Nat
  val y : Bool
end
```

### 4. Create a Functor

A functor is a parameterized module:

```
modules> :mod Inc = functor(X : sig val n : Nat end) => struct val m : Nat = succ X.n end
module Inc : ...
```

### 5. Apply a Functor

```
modules> (Inc)(struct val n : Nat = 5 end)
  : sig
      val m : Nat
    end
  = struct val m : Nat = 6 end
```

### 6. Seal a Module

Hide implementation details:

```
modules> (struct val x : Nat = 5 val secret : Nat = 42 end :> sig val x : Nat end)
  : sig
      val x : Nat
    end
  -- 'secret' is now hidden!
```

## Core Syntax Reference

### Terms
- Variables: `x`, `y`, `counter`
- Lambdas: `\x:Nat. succ x` or `λx:Nat. succ x`
- Application: `f x`
- Booleans: `true`, `false`
- Conditionals: `if t then t1 else t2`
- Natural numbers: `0`, `succ n`, `pred n`, `iszero n`
- Records: `{x = 5, y = true}`
- Projection: `r.x`

### Types
- Base types: `Bool`, `Nat`
- Function types: `Nat -> Bool`
- Record types: `{x: Nat, y: Bool}`

### Module Expressions
- Structure: `struct ... end`
- Module variable: `M`
- Functor: `functor(X : S) => M`
- Application: `F(M)`
- Sealing: `(M :> S)`

### Declarations (inside structures)
- Value: `val x : Nat = 5`
- Type (manifest): `type t = Nat`
- Type (abstract): `type t`
- Module: `module M = ...`

### Signatures
- Signature: `sig ... end`
- Value spec: `val x : Nat`
- Type spec (abstract): `type t`
- Type spec (manifest): `type t = Nat`
- Module spec: `module M : S`

## Common Patterns

### Pattern 1: Abstract Data Type

```
:mod Stack = (
  struct
    type t = {items: Nat}
    val empty : t = {items = 0}
    val push : Nat -> t -> t = \n:Nat. \s:t. {items = succ s.items}
  end
  :>
  sig
    type t
    val empty : t
    val push : Nat -> t -> t
  end
)
```

Now `Stack.t` is abstract - clients can't see it's a record!

### Pattern 2: Parameterized Module

```
:mod MakePair = functor(X : sig type t end) =>
  struct
    type pair = {fst: X.t, snd: X.t}
    val make : X.t -> X.t -> pair = \a:X.t. \b:X.t. {fst = a, snd = b}
  end
```

### Pattern 3: Nested Modules

```
:mod Library = struct
  module Math = struct
    val add : Nat -> Nat -> Nat = \x:Nat. \y:Nat. succ x  -- simplified
  end

  module Utils = struct
    val id : Nat -> Nat = \x:Nat. x
  end
end
```

## REPL Commands

- `:help` - Show all commands
- `:examples` - Show comprehensive examples
- `:quit` - Exit REPL
- `:let x = t` - Bind a term to a variable
- `:type t` - Show type of a term
- `:mod M = expr` - Define a module
- `:step t` - Show one evaluation step
- `:steps t` - Show all evaluation steps
- `:env` - Show current context
- `:reset` - Clear all bindings

## Testing

Run the test suite:

```bash
stack test
```

## Next Steps

1. Read [README.md](README.md) for comprehensive theory
2. Try [TUTORIAL.md](TUTORIAL.md) for step-by-step guide
3. Check [FAQ.md](FAQ.md) for common questions
4. Practice with examples in the REPL (`:examples`)

## Key Takeaways

- **Structures** define concrete modules with implementations
- **Signatures** specify module interfaces (what must be provided)
- **Functors** are functions from modules to modules
- **Sealing** hides implementation details
- **Abstract types** let you hide representation

Module systems help organize large programs and provide type-safe encapsulation!
