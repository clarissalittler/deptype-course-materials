# Chapter 10: Linear Types - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce linear types concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Linear vs Unrestricted ⭐
Which of these type check?

a) `λ(x :1 Nat). x`
b) `λ(x :1 Nat). (x, x)`
c) `λ(x :ω Nat). (x, x)`
d) `λ(x :1 Nat). 0`
e) `λ(x :ω Nat). 0`

### Problem 1.2: Context Splitting ⭐
Can these be type checked? Why or why not?

a) `λ(x :1 Nat). λ(y :1 Bool). (x, y)`
b) `λ(x :1 Nat). λ(y :1 Bool). (x, x)`
c) `λ(x :1 Nat). λ(y :1 Nat). (x, y)`
d) `λ(x :ω Nat). λ(y :1 Bool). (x, y)`

### Problem 1.3: Bang Types ⭐
Which are valid?

a) `!5`
b) `!(true, false)`
c) `λ(x :1 Nat). !x`
d) `λ(x :ω Nat). !x`
e) `let !x = !5 in x`

### Problem 1.4: Pair Elimination ⭐
Type check these:

a) `let (x, y) = (0, true) in (y, x)`
b) `let (x, y) = (0, true) in x`
c) `let (x, y) = (0, true) in (x, x)`
d) `let (x, y) = (!0, !true) in (x, y)`

### Problem 1.5: Function Types ⭐
What are the types?

a) `λ(x :1 Nat). x`
b) `λ(x :ω Nat). (x, x)`
c) `λ(f :1 Nat -o Bool). λ(x :1 Nat). f x`
d) `λ(x :1 !Nat). let !y = x in (y, y)`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Implementing Basic Combinators ⭐⭐
Implement these with correct multiplicities:

a) **Linear identity**: `id : A -o A`
b) **Linear const**: Returns first arg, consumes second
c) **Linear swap**: `swap : (A * B) -o (B * A)`
d) **Linear compose**: `compose : (B -o C) -o (A -o B) -o (A -o C)`

### Problem 2.2: Bang Manipulation ⭐⭐
Implement these operations:

a) `bangPair : !A -o !B -o !(A * B)`
b) `bangMap : (A -> B) -o !A -o !B`
c) `bangDup : !A -o (!A * !A)`
d) `unbang : !(A -o B) -o !A -o !B`

### Problem 2.3: Resource Threading ⭐⭐
Design types for a file API:

```haskell
open  : String -o Handle
read  : Handle -o (String * Handle)
write : (Handle * String) -o Handle
close : Handle -o ()
```

Now implement:
```haskell
readAndClose : String -o String
-- Opens file, reads it, closes it, returns content
```

### Problem 2.4: Usage Tracking ⭐⭐
For each term, track the usage of all variables:

a) `λ(x :1 Nat). λ(y :1 Bool). (x, y)`
b) `λ(x :1 Nat). λ(y :1 Bool). let (a, b) = (x, y) in (b, a)`
c) `λ(x :ω Nat). if (iszero x) then x else (succ x)`
d) `λ(p :1 (Nat * Bool)). let (x, y) = p in if y then x else 0`

### Problem 2.5: Conditional Linearity ⭐⭐
Type check these conditionals:

a) `λ(x :1 Nat). if true then x else 0`
b) `λ(x :1 Nat). if true then x else x`
c) `λ(x :ω Nat). if true then x else (x, x)`
d) `λ(x :1 Nat). λ(y :1 Nat). if true then x else y`

### Problem 2.6: Higher-Order Linear Functions ⭐⭐
Implement:

a) `apply : (A -o B) -o A -o B`
b) `applyTwice : (A -o A) -o A -o A`  (Can you?)
c) `flip : (A -o B -o C) -o B -o A -o C`
d) `curry : ((A * B) -o C) -o A -o B -o C`

### Problem 2.7: Linear Lists ⭐⭐
Design a linear list type:

```haskell
data LinearList A = Nil | Cons A (LinearList A)
```

Implement:
```haskell
singleton : A -o LinearList A
append : (LinearList A * LinearList A) -o LinearList A
reverse : LinearList A -o LinearList A
```

### Problem 2.8: Bang Introduction Conditions ⭐⭐
Which of these can be banged (wrapped in `!`)?

a) `5`
b) `(true, false)`
c) `λ(x :1 Nat). x`
d) `λ(x :ω Nat). x`
e) `λ(x :ω Nat). λ(y :ω Bool). (x, y)`
f) `λ(x :1 Nat). λ(y :ω Bool). (x, y)`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Church Encodings with Linearity ⭐⭐⭐
Church numerals in linear logic:

a) Define linear Church numerals: `ChurchNat = (A -o A) -o A -o A`
b) Implement `succLin : ChurchNat -o ChurchNat`
c) Can you implement `addLin : ChurchNat -o ChurchNat -o ChurchNat`?
d) Why is linear Church addition harder than unrestricted?

### Problem 3.2: Session Types ⭐⭐⭐
Implement a simple session type system:

```haskell
data Session
  = Send Nat Session     -- Send Nat, continue with Session
  | Recv Nat Session     -- Receive Nat, continue with Session
  | End                  -- End session

type Channel Session -o ...
```

Implement:
```haskell
send : (Channel (Send Nat s) * Nat) -o Channel s
recv : Channel (Recv Nat s) -o (Nat * Channel s)
close : Channel End -o ()
```

Create a simple protocol:
```haskell
-- Client sends two numbers, receives sum
clientProtocol : (Nat * Nat) -o Nat
```

### Problem 3.3: Linear State Monad ⭐⭐⭐
Implement a linear state monad:

```haskell
type State s a = s -o (a * s)

return : a -> State s a
bind   : State s a -o (a -o State s b) -o State s b
get    : State s s
put    : s -o State s ()
```

Why is this more powerful than the unrestricted state monad for resource management?

### Problem 3.4: Proving Linearity Properties ⭐⭐⭐
Prove (informally) that:

a) If `Γ ⊢ t : A -o B` and all variables in `Γ` are linear, then `t` uses its argument exactly once.
b) Context splitting preserves linearity: if `Γ, Δ ⊢ (t₁, t₂) : A * B`, then each linear variable in `Γ ∪ Δ` is used exactly once total.
c) Bang introduction is sound: if `⊢ !t : !A`, then `t` uses no linear variables.

### Problem 3.5: Linear Continuation Passing ⭐⭐⭐
Implement CPS with linear types:

```haskell
type Cont r a = (a -o r) -o r

return_cps : a -> Cont r a
bind_cps   : Cont r a -o (a -o Cont r b) -o Cont r b
callcc     : ((a -o Cont r b) -o Cont r a) -o Cont r a
```

Why are linear continuations more restrictive than unrestricted ones?

### Problem 3.6: Array Operations ⭐⭐⭐
Design a linear array API:

```haskell
type Array a  -- Linear array

create : Nat -o Array a
get    : (Array a * Nat) -o (a * Array a)
set    : (Array a * Nat * a) -o Array a
destroy: Array a -o ()
```

Why is this safe for in-place updates without garbage collection?

### Problem 3.7: Affine Types vs Linear ⭐⭐⭐
Compare affine types (at most once) with linear types:

a) What operations are allowed in affine but not linear?
b) Give an example where affine is more convenient
c) Give an example where linear provides better guarantees
d) How does Rust's ownership relate to affine types?

### Problem 3.8: Bounded Linear Logic ⭐⭐⭐
Extend to bounded linear logic with resource counts:

```haskell
type Resource (n : Nat) a  -- Can be used n times
```

Define:
```haskell
use  : Resource (S n) a -o (a * Resource n a)
done : Resource 0 a -o ()
```

How does this generalize linear (n=1) and unrestricted (n=∞)?

---

## Debugging Exercises (30 minutes)

### Debug 1: Duplication Error ⭐
What's wrong?

```haskell
double : Nat -o (Nat * Nat)
double = λ(x :1 Nat). (x, x)
```

Fix it with minimal changes.

### Debug 2: Missing Usage ⭐
Why doesn't this work?

```haskell
fst : (A * B) -o A
fst = λ(p :1 (A * B)). let (x, y) = p in x
```

### Debug 3: Bang Confusion ⭐⭐
What's the error?

```haskell
duplicate : Nat -o (Nat * Nat)
duplicate = λ(x :1 Nat). let !y = x in (y, y)
```

### Debug 4: Context Splitting ⭐⭐
Find the problem:

```haskell
bad : (Nat * Nat) -o Nat
bad = λ(p :1 (Nat * Nat)). let (x, y) = p in (x, x)
```

### Debug 5: Linear Function Reuse ⭐⭐
Why is this invalid?

```haskell
applyTwice : (A -o A) -o A -o A
applyTwice = λ(f :1 A -o A). λ(x :1 A). f (f x)
```

### Debug 6: Bang Introduction ⭐⭐
What's wrong?

```haskell
storeLinear : (Nat -o Bool) -o !(Nat -o Bool)
storeLinear = λ(f :1 Nat -o Bool). !f
```

---

## Code Review Exercises (30 minutes)

### Review 1: File Handling ⭐⭐
Review this implementation:

```haskell
processFile : String -o String
processFile = λ(path :1 String).
  let h = open path in
  let (content, h') = read h in
  let h'' = write (h', "processed") in
  let () = close h'' in
  content
```

Questions:
- Is the handle properly managed?
- Could we forget to close?
- What if read or write fails?

### Review 2: Resource Pool ⭐⭐⭐
Two implementations of a resource pool:

**Version A (Linear)**:
```haskell
type Pool a = LinearList a

acquire : Pool a -o (a * Pool a)
release : (Pool a * a) -o Pool a
```

**Version B (Unrestricted)**:
```haskell
type Pool a = Ref [a]

acquire : Pool a -> IO a
release : Pool a -> a -> IO ()
```

Compare:
- Which prevents resource leaks at compile time?
- Which is easier to use?
- Tradeoffs?

### Review 3: Linear Parsers ⭐⭐⭐
Student implemented a linear parser:

```haskell
type Parser a = String -o (a * String)

char   : Char -> Parser Char
many   : Parser a -o Parser [a]
choice : (Parser a * Parser a) -o Parser a
```

Questions:
- Why is `String -o (a * String)` linear?
- Can we implement `many` with this signature?
- What changes would make this work?

### Review 4: Transaction System ⭐⭐⭐
Review this transaction API:

```haskell
type Transaction
type TVar a

begin    : () -o Transaction
read     : (Transaction * TVar a) -o (a * Transaction)
write    : (Transaction * TVar a * a) -o Transaction
commit   : Transaction -o ()
rollback : Transaction -o ()
```

Is it safe? Can you:
- Read a var after commit?
- Commit twice?
- Forget to commit/rollback?

---

## Real-World Applications (30 minutes)

### Application 1: Rust Ownership ⭐⭐
Model Rust ownership with linear types:

```rust
let file = File::open("data.txt")?;
let contents = read_to_string(file)?;
// file is moved, can't use again
```

Express in linear types:
```haskell
let file : File = open "data.txt" in
let (contents, ()) = readToString file in
contents
```

### Application 2: Network Protocol ⭐⭐
Model a TCP connection:

```haskell
type Socket

connect : (Host * Port) -o Socket
send    : (Socket * Bytes) -o Socket
recv    : Socket -o (Bytes * Socket)
close   : Socket -o ()
```

Implement an HTTP request:
```haskell
httpGet : Url -o String
```

### Application 3: Database Transactions ⭐⭐⭐
Design a type-safe database API:

```haskell
type DB
type Transaction
type Query a

openDB   : String -o DB
begin    : DB -o (Transaction * DB)
execute  : (Transaction * Query a) -o (a * Transaction)
commit   : Transaction -o DB
rollback : Transaction -o DB
closeDB  : DB -o ()
```

Why is this better than `Maybe` or exceptions?

---

## Solutions

### Warm-Up Solutions

**1.1**: a) ✓, b) ✗ (duplicate), c) ✓, d) ✗ (discard), e) ✓

**1.2**: a) ✓, b) ✗ (x used twice), c) ✓, d) ✓ (x unrestricted can be in both)

**1.3**: a) ✓, b) ✓, c) ✗ (can't bang linear), d) ✓, e) ✓

**1.4**: a) ✓, b) ✗ (y unused), c) ✗ (x twice, y unused), d) Depends on bang elimination

**1.5**:
- a) `Nat -o Nat`
- b) `Nat -> (Nat * Nat)`
- c) `(Nat -o Bool) -o Nat -o Bool`
- d) `!Nat -o (Nat * Nat)`

### Standard Solutions

**2.1**:
```haskell
a) id = λ(x :1 A). x
b) const = λ(x :ω A). λ(y :1 B). x
c) swap = λ(p :1 (A * B)). let (x, y) = p in (y, x)
d) compose = λ(g :1 B -o C). λ(f :1 A -o B). λ(x :1 A). g (f x)
```

**2.2**:
```haskell
a) bangPair = λ(a :1 !A). λ(b :1 !B).
     let !x = a in let !y = b in !(x, y)
b) bangMap = λ(f :1 A -> B). λ(a :1 !A).
     let !x = a in !(f x)
c) bangDup = λ(a :1 !A). let !x = a in (!x, !x)
d) unbang = λ(f :1 !(A -o B)). λ(a :1 !A).
     let !g = f in let !x = a in !(g x)
```

**2.3**:
```haskell
readAndClose = λ(path :1 String).
  let h = open path in
  let (content, h') = read h in
  let () = close h' in
  content
```

**2.4**:
- a) x: once, y: once
- b) x: once, y: once, a: once, b: once
- c) x: many (condition + branches)
- d) p: once, x: once (in conditional), y: once (in condition)

**2.5**: a) ✓, b) ✗ (x twice), c) ✓, d) ✓ (max usage)

**2.6**:
```haskell
a) apply = λ(f :1 A -o B). λ(x :1 A). f x
b) Can't! Would need to use f twice
c) flip = λ(f :1 A -o B -o C). λ(b :1 B). λ(a :1 A). f a b
d) curry = λ(f :1 (A * B) -o C). λ(a :1 A). λ(b :1 B). f (a, b)
```

**2.7**: Implementations use standard linear patterns

**2.8**: a) ✓, b) ✓, c) ✗ (uses linear x), d) ✓, e) ✓, f) ✗ (uses linear x)

### Challenge Solutions

**3.1**: Linear Church numerals are tricky - the function must be used n times

**3.2**: Session types ensure protocol adherence at compile time

**3.3**: Linear state ensures state is threaded through properly

**3.4**: Proofs by induction on typing derivations

**3.5**: Linear continuations can only be invoked once

**3.6**: Linear arrays allow safe in-place updates

**3.7**: Affine allows discard, linear ensures consumption

**3.8**: Bounded linear logic generalizes resource counting

### Debug Solutions

**Debug 1**: Make x unrestricted: `λ(x :ω Nat). (x, x)`

**Debug 2**: y is unused. Need: `let (x, y) = p in (x, y)` or different approach

**Debug 3**: Can't bang x directly (linear). Need: `λ(x :ω Nat). !(x, x)`

**Debug 4**: x used twice, y unused

**Debug 5**: f used twice. Can't apply linear function twice.

**Debug 6**: f is linear, can't bang it

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 8 hard, 6 debug, 4 review

**Note**: Linear types are subtle! Focus on understanding usage tracking and context splitting.
