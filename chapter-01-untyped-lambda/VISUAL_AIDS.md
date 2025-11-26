# Chapter 1: Visual Aids

## Abstract Syntax Trees

### Simple Terms

**Variable `x`**
```
  x
```

**Identity Function `λx. x`**
```
    Lam
   /   \
  x    Var
        |
        x
```

**Application `f x`**
```
   App
  /   \
Var   Var
 |     |
 f     x
```

### Complex Terms

**`λf. λx. f x`** (apply function)
```
         Lam
        /   \
       f    Lam
           /   \
          x    App
              /   \
           Var    Var
            |      |
            f      x
```

**`(λx. x) y`** (identity applied to y)
```
       App
      /   \
   Lam    Var
  /   \    |
 x   Var   y
      |
      x
```

---

## Beta-Reduction Traces

### Identity Function

```
   (λx. x) y
       │
       ▼  β-reduce: substitute y for x
       y
```

### Constant Function

```
   ((λx. λy. x) a) b
          │
          ▼  β-reduce: substitute a for x
      (λy. a) b
          │
          ▼  β-reduce: substitute b for y (y unused)
          a
```

### Self-Application

```
   (λx. x x) (λy. y)
          │
          ▼  β-reduce: substitute (λy. y) for x
   (λy. y) (λy. y)
          │
          ▼  β-reduce: substitute (λy. y) for y
       (λy. y)
```

### Non-Terminating (Omega)

```
   (λx. x x) (λx. x x)
            │
            ▼  β-reduce
   (λx. x x) (λx. x x)
            │
            ▼  β-reduce
   (λx. x x) (λx. x x)
            │
            ▼  ... forever
```

---

## Free Variables

### Visual Scoping

**`λx. x y`** - x is bound, y is free
```
┌─────────────────┐
│ λx.             │
│  ┌───────────┐  │
│  │ x    y    │  │
│  │ ↑    ↑    │  │
│  │ │    │    │  │
│  │bound free │  │
│  └───────────┘  │
└─────────────────┘
```

**`λx. λy. x y z`** - x,y bound; z free
```
┌───────────────────────┐
│ λx.                   │
│  ┌───────────────────┐│
│  │ λy.               ││
│  │  ┌─────────────┐  ││
│  │  │ x   y   z   │  ││
│  │  │ ↑   ↑   ↑   │  ││
│  │  │ │   │   │   │  ││
│  │  │ │  bound │   │  ││
│  │  │bound   free │  ││
│  │  └─────────────┘  ││
│  └───────────────────┘│
└───────────────────────┘

FV(λx. λy. x y z) = {z}
```

---

## Substitution

### Safe Substitution

**`[y ↦ 5](λx. x + y)`**
```
Before:                  After:
    Lam                     Lam
   /   \                   /   \
  x    Add                x    Add
      /   \                   /   \
   Var    Var              Var    5
    |      |                |
    x      y                x

y is free, so replace it with 5
```

### Shadowing (No Substitution)

**`[x ↦ 5](λx. x)`**
```
Before:                  After:
    Lam                     Lam
   /   \                   /   \
  x    Var                x    Var
        |                       |
        x                       x

Inner x shadows outer, no substitution in body
```

### Capture-Avoidance

**`[y ↦ x](λx. y)`** - DANGER! Must α-convert first
```
WRONG:                    RIGHT:
    Lam                      Lam
   /   \                    /   \
  x    Var    ──▶         z    Var     (first α-convert x→z)
        |                       |
        y                       y
                                │
                                ▼
                              Lam
                             /   \
                            z    Var
                                  |
                                  x      (now safe to substitute)
```

---

## Church Encodings

### Booleans

```
TRUE  = λt. λf. t          FALSE = λt. λf. f

        Lam                        Lam
       /   \                      /   \
      t    Lam                   t    Lam
          /   \                      /   \
         f    Var                   f    Var
               |                          |
               t                          f
      (select first)              (select second)
```

### Numerals

```
ZERO = λf. λx. x           ONE = λf. λx. f x

       Lam                        Lam
      /   \                      /   \
     f    Lam                   f    Lam
         /   \                      /   \
        x    Var                   x    App
              |                       /   \
              x                    Var    Var
       (apply f 0 times)            |      |
                                    f      x
                                  (apply f 1 time)

TWO = λf. λx. f (f x)

         Lam
        /   \
       f    Lam
           /   \
          x    App
              /   \
           Var    App
            |    /   \
            f  Var   Var
                |     |
                f     x
        (apply f 2 times)
```

### Successor

```
SUCC n = λf. λx. f (n f x)

"Apply f one more time than n does"

SUCC ZERO:
  λf. λx. f ((λf. λx. x) f x)
       │
       ▼ reduce inner application
  λf. λx. f ((λx. x) x)
       │
       ▼ reduce
  λf. λx. f x
       │
       = ONE ✓
```

---

## Evaluation Strategies

### Call-by-Value vs Call-by-Name

**Term**: `(λx. λy. y) ((λz. z z) (λz. z z))`

**Call-by-Value** (evaluate argument first):
```
(λx. λy. y) ((λz. z z) (λz. z z))
                  │
                  ▼  try to evaluate argument
          (λz. z z) (λz. z z)
                  │
                  ▼
          (λz. z z) (λz. z z)
                  │
                  ▼  ... loops forever!
```

**Call-by-Name** (substitute immediately):
```
(λx. λy. y) ((λz. z z) (λz. z z))
                  │
                  ▼  substitute (argument not used!)
              λy. y
                  │
                  = DONE ✓
```

---

## Y Combinator

### Structure

```
Y = λf. (λx. f (x x)) (λx. f (x x))

          Lam
         /   \
        f    App
            /   \
         Lam    Lam
        /   \   /   \
       x   App x   App
          /   \   /   \
        Var App Var  App
         |  / \  |   / \
         f x  x  f  x   x
```

### Expansion

```
Y F = (λf. (λx. f (x x)) (λx. f (x x))) F
    │
    ▼ β-reduce
    (λx. F (x x)) (λx. F (x x))
    │
    ▼ β-reduce
    F ((λx. F (x x)) (λx. F (x x)))
    │
    = F (Y F)

So Y F = F (Y F) = F (F (Y F)) = F (F (F (Y F))) = ...
```

---

## Parsing Precedence

### Application Associates Left

```
a b c   =   (a b) c   ≠   a (b c)

      App                    App
     /   \                  /   \
   App    c                a    App
  /   \                        /   \
 a     b                      b     c

 CORRECT                   WRONG
```

### Lambda Extends Right

```
λx. λy. t   =   λx. (λy. t)

      Lam                   WRONG:
     /   \
    x    Lam                 App
        /   \               /   \
       y     t            Lam   ???
                         /   \
                        x     y
```

### Parentheses Override

```
(λx. x) y   ≠   λx. (x y)

     App                    Lam
    /   \                  /   \
  Lam   Var               x    App
 /   \   |                    /   \
x   Var  y                  Var   Var
     |                       |     |
     x                       x     y
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│                    LAMBDA CALCULUS                          │
├─────────────────────────────────────────────────────────────┤
│  SYNTAX                                                     │
│    t ::= x | λx. t | t t                                   │
│                                                             │
│  BETA REDUCTION                                             │
│    (λx. t) v → [x ↦ v]t                                    │
│                                                             │
│  FREE VARIABLES                                             │
│    FV(x) = {x}                                             │
│    FV(λx. t) = FV(t) \ {x}                                 │
│    FV(t₁ t₂) = FV(t₁) ∪ FV(t₂)                            │
│                                                             │
│  CHURCH BOOLEANS                                            │
│    true  = λt. λf. t                                       │
│    false = λt. λf. f                                       │
│                                                             │
│  CHURCH NUMERALS                                            │
│    0 = λf. λx. x                                           │
│    n = λf. λx. fⁿ x                                        │
└─────────────────────────────────────────────────────────────┘
```
