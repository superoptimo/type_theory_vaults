---
title: Object Encodings with Imperative State
source: "Types and Programming Languages — Benjamin C. Pierce (2002)"
chapter: "Ch. 18, Case Study: Imperative Objects (pp. 225–246)"
tags: [type-theory, tapl, objects, classes, self, inheritance, encapsulation, subtyping, references, fix, open-recursion, case-study]
---

[[book-guidelines|↩ Back to guidelines]]

## Why encode objects at all, instead of just having them

Chapter 18 is deliberately a *case study*, not a new calculus. Pierce adds no new syntax, no new typing rules, no new evaluation rules. Everything in it is assembled from four features you already have by Chapter 18: functions, records (Ch. 11), general recursion via `fix` (§11.11), and mutable references (Ch. 13), glued together with [[Subtyping|subtyping]] (Ch. 15). The point of the exercise is a claim about *what objects and classes fundamentally are*: not a primitive feature a language designer bolts on, but a **derived form** — a reusable pattern of encoding — built from strictly lower-level parts. If that claim is right, then "understanding object-oriented programming" reduces to understanding a small number of encoding tricks, and everything Smalltalk, Java, or C++ programmers think of as mysterious about `self`, `super`, and dynamic dispatch becomes explicable in terms of lambda-abstraction, record projection, and the store.

This matters for a second reason that shows up explicitly in §18.11: the encoding *mostly* works cleanly, but one specific feature — open recursion through `self` — collides with the evaluation order of `fix`, and the chapter has to work around it. That collision is not a minor implementation wrinkle; it's the reason Chapter 19 abandons the encoding approach entirely and gives objects their own primitive syntax and rules. So this chapter is doing double duty: it's both "here's how you *could* build objects out of parts you already have" and "here's exactly where that strategy starts to strain," setting up why a *direct* treatment (Featherweight Java) is worth having.

Pierce identifies five features that, in combination, characterize the object-oriented style (§18.1), and the chapter is organized as a sequence of encodings, each adding one of these:

1. **Multiple representations** — the same interface, many implementations, resolved by *dynamic dispatch* (looking up the operation in a method table at call time) rather than by a single static implementation as in an abstract data type.
2. **Encapsulation** — internal state reachable only through the object's own methods.
3. **Subtyping** — an object satisfying more operations can stand in for one requiring fewer; structurally identical to record subtyping.
4. **Inheritance** — reusing a superclass's method implementations when building a subclass, without retyping them.
5. **Open recursion** — a method body can call *another* method of the same object through a special name (`self`/`this`), and that call is *late-bound*: it resolves to whatever version of the method exists in the actual (possibly more-derived) object, not necessarily the class that wrote the calling method.

Everything below builds these five up in order, on a single running example: counters.

## Objects as records of mutable-state-closing methods (§18.2)

The simplest possible object is a reference cell paired with a record of functions that close over it:

$$
c = \mathtt{let}\ x = \mathtt{ref}\ 1\ \mathtt{in}\ \{\mathtt{get} = \lambda\_\!:\!\mathtt{Unit}.\ !x,\ \ \mathtt{inc} = \lambda\_\!:\!\mathtt{Unit}.\ x \mathrel{:=} \mathtt{succ}(!x)\}
$$

with inferred type $c : \{\mathtt{get}\!:\!\mathtt{Unit}\to\mathtt{Nat},\ \mathtt{inc}\!:\!\mathtt{Unit}\to\mathtt{Unit}\}$, abbreviated `Counter`. Three things about this definition carry the whole chapter's weight:

- **Methods are functions from `Unit`, not values.** If `get` were bound directly to `!x`'s current value at construction time, it would be a `Nat`, frozen forever. Wrapping it in `λ_:Unit. ...` — a *thunk* — defers evaluation of the body to each call, so successive calls can observe successive states of `x`. This same trick (delay a computation by wrapping it in a throwaway-argument lambda) reappears, load-bearingly, in §18.11.
- **Encapsulation is free, not designed in.** Nothing in the type `Counter` mentions `x`. The reason nothing outside the `let` can touch `x` is ordinary lexical scoping — the same reason a closure's captured variable is invisible to its caller in *any* functional language. Pierce is explicit about this (§18.13, point 2): object encapsulation in this encoding *is* variable scoping; there is no separate mechanism.
- **A method table is a record, and method invocation is field projection followed by application** (`c.inc unit`). "Dynamic dispatch" in this encoding is nothing more exotic than: extract a field by name, apply it.

**[[Bounded-Quantification#Grounding|Grounding]] (Rust).** The closure-over-mutable-state pattern is exactly a `struct` with private fields plus an `impl` block, or more literally, a struct of boxed closures:

```rust
struct Counter {
    inc: Box<dyn FnMut()>,
    get: Box<dyn Fn() -> i64>,
}

fn make_counter() -> Counter {
    use std::cell::Cell;
    use std::rc::Rc;
    let x = Rc::new(Cell::new(1));
    let x_inc = Rc::clone(&x);
    Counter {
        inc: Box::new(move || x_inc.set(x_inc.get() + 1)),
        get: Box::new(move || x.get()),
    }
}
```

This is more machinery than idiomatic Rust would use for a counter (you'd just write a struct with a method), but it's the honest translation of Pierce's encoding: two closures sharing one heap cell via `Rc<Cell<_>>`, exactly playing the role of TAPL's shared reference `x`. The point of writing it this clunky way is to see that ordinary Rust structs-with-methods are *already* doing, at the language level, what this chapter does by hand at the term level.

**Grounding (Python).** Python's own object model is close enough to make the correspondence almost too easy — `self.x` *is* the shared reference cell, and bound methods *are* the record of closures:

```python
def make_counter():
    state = {"x": 1}
    return {
        "get": lambda: state["x"],
        "inc": lambda: state.__setitem__("x", state["x"] + 1),
    }
```

The dict-of-closures version is deliberately more primitive than `class Counter: ...` precisely because it exposes what a Python object already *is* under the hood: a namespace of mutable state, plus bound-method lookup that's really dictionary lookup.

## Object generators and classes (§18.3, §18.6)

An **object generator** is just a function `Unit → Counter` — call it, get a fresh object, each with its own private reference:

$$
\mathtt{newCounter} = \lambda\_\!:\!\mathtt{Unit}.\ \mathtt{let}\ x = \mathtt{ref}\ 1\ \mathtt{in}\ \{\mathtt{get} = \ldots,\ \mathtt{inc} = \ldots\}
$$

This alone gets you multiple independent instances, but it doesn't get you *code reuse across similar objects*. If you write `newCounter` and then, separately, `newResetCounter` with one extra method, the `get`/`inc` bodies are duplicated verbatim. A **class**, in this minimal encoding, is the fix: factor the method-body code out from the object-allocation code, so the method code can be shared.

$$
\mathtt{counterClass} : \mathtt{CounterRep} \to \mathtt{Counter} \qquad \mathtt{counterClass} = \lambda r\!:\!\mathtt{CounterRep}.\ \{\mathtt{get} = \lambda\_\!:\!\mathtt{Unit}.\ !(r.x),\ \mathtt{inc} = \ldots\}
$$

$$
\mathtt{newCounter} = \lambda\_\!:\!\mathtt{Unit}.\ \mathtt{let}\ r = \{x = \mathtt{ref}\ 1\}\ \mathtt{in}\ \mathtt{counterClass}\ r
$$

So concretely: **a class is a function from a record of (as-yet-unallocated) instance variables to a record of methods.** `counterClass` is not itself an object — it's a *template* waiting for storage. This is why Pierce stresses (§18.6, closing remark) that classes here are **values, not types**: `counterClass` has an ordinary function type, `CounterRep → Counter`; there's no new type-level notion of "class-hood" the way C++ or Java reify classes as compile-time entities as well as runtime ones.

Note the prerequisite step, §18.5: before classes can be written this way, instance variables that used to be one bare `ref` get grouped into a record (`CounterRep = {x: Ref Nat}`), because a class needs to abstract over *all* of an object's state as a single parameter, not thread each variable through separately.

**Grounding (Rust).** A class-as-function-from-state-to-methods is close to a constructor plus a `trait`/`impl`, but the more literal translation is a function that takes an "instance variable" struct and returns a struct of closures over it — which is exactly what you'd write if Rust had no `impl` sugar at all:

```rust
struct CounterRep { x: Rc<Cell<i64>> }

fn counter_class(r: Rc<CounterRep>) -> Counter {
    let r1 = Rc::clone(&r);
    let r2 = Rc::clone(&r);
    Counter {
        get: Box::new(move || r1.x.get()),
        inc: Box::new(move || r2.x.set(r2.x.get() + 1)),
    }
}
```

**Grounding (Lean).** Lean has no mutable references in pure code, so the state-as-reference-cell part doesn't transliterate directly (Lean's `IO.Ref` exists, but is monadic, not a first-class term the way TAPL's `Ref Nat` is). What *does* transliterate cleanly is the shape "class = function from representation to interface":

```lean
structure CounterRep where
  x : Nat

structure Counter where
  get : Unit → Nat
  inc : CounterRep → CounterRep   -- purely functional: returns new state

def counterClass (r : CounterRep) : Counter :=
  { get := fun _ => r.x, inc := fun r => { r with x := r.x + 1 } }
```

This is worth pausing on: it's the same "class = function from rep to method-record" shape, but because Lean has no mutation, `inc` has to *return* a new representation instead of side-effecting one — the purely functional cousin of exactly this encoding is what TAPL itself develops later, in Chapter 32.

## Subtyping between object types (§18.4)

Nothing new is invented here — it's a direct application of record subtyping (Ch. 15). If `ResetCounter = {get:Unit→Nat, inc:Unit→Unit, reset:Unit→Unit}` has strictly more fields than `Counter`, then `ResetCounter <: Counter` by the width-subtyping rule for records, and any function expecting a `Counter` (like `inc3 : Counter → Unit`) accepts a `ResetCounter` object without modification. This is worth calling out explicitly because it's the entire mechanism behind "an object satisfying a richer interface can be used wherever the narrower interface is expected" — polymorphism in the object-oriented sense reduces here to ordinary structural subtyping, no separate "object subtyping" rule required.

## Instance variables and encapsulation, across inheritance (§18.5, §18.7)

Grouping instance variables into a record (§18.5) is what makes it possible for a **subclass to extend the representation**, not just the methods. When `BackupCounterClass` needs an extra field `b: Ref Nat` beyond what `CounterClass` uses, it defines a strictly larger representation type, `BackupCounterRep = {x: Ref Nat, b: Ref Nat}`, and — crucially — this is *safe* precisely because subtyping is contravariant-friendly here in the right direction:

$$
\mathtt{resetCounterClass} : \mathtt{CounterRep} \to \mathtt{ResetCounter}
$$

expects a `CounterRep`, and `BackupCounterRep <: CounterRep` (it has a superset of fields), so passing a `BackupCounterRep` where a `CounterRep` is expected typechecks by ordinary subsumption. The superclass genuinely doesn't need to know about `b` — and *can't* see it, since its methods only ever project the fields it declares. This is encapsulation surviving inheritance: a subclass can hand a strictly bigger record to superclass code, and the superclass code stays oblivious to (and hence can't corrupt) the extra fields.

## Calling superclass methods (`super`) (§18.6, §18.8)

Building a subclass is: instantiate the superclass's class-function on your own (possibly extended) instance variables, bind the result to `super`, then build a new method record that either copies fields straight from `super` or overrides them:

$$
\mathtt{resetCounterClass} = \lambda r\!:\!\mathtt{CounterRep}.\ \mathtt{let}\ \mathtt{super} = \mathtt{counterClass}\ r\ \mathtt{in}\ \{\mathtt{get}=\mathtt{super}.\mathtt{get},\ \mathtt{inc}=\mathtt{super}.\mathtt{inc},\ \mathtt{reset}=\lambda\_\!:\!\mathtt{Unit}.\ r.x \mathrel{:=} 1\}
$$

`super` is nothing but a local variable bound to an ordinary object — the "parent object," built on the *same* instance-variable record `r` that the subclass's own new methods will also close over, which is exactly why `reset`'s assignment `r.x := 1` and `super.get`'s read of `r.x` see each other's effects. §18.8 shows the natural extension: a method body can call `super.someMethod` *from inside its own definition*, not just copy it verbatim, to extend rather than replace behavior (e.g. `inc = λ_:Unit. (super.backup unit; super.inc unit)`). There is no new mechanism for this at all — `super` is a value in scope like any other, and `super.backup unit` is just an application.

**What breaks without instance-variable grouping (§18.5) done first:** if each instance variable were still a separate `ref` parameter rather than a record field, a subclass extending the representation would have to change the *arity* of the class function, breaking every place that calls the superclass constructor with the old argument count. Grouping into one record turns "add a field" into a subtyping-safe operation instead of a signature-breaking one.

## Open recursion through `self` (§18.9–§18.10)

This is the chapter's technical center of gravity, and the place where "objects are just records of closures" stops being quite enough.

**The problem.** Suppose `inc` should be defined *in terms of* `get` and `set`, both siblings in the same method record. `inc`, `get`, and `set` are mutually recursive — but not recursive with anything outside the object. Pierce's first move (§18.9) is to recognize this as *exactly* the mutually-recursive-record-of-functions pattern already built in §11.11: abstract the whole record on a parameter representing "the record itself," call it `self`, and use `fix` to tie the knot:

$$
\mathtt{setCounterClass} = \lambda r\!:\!\mathtt{CounterRep}.\ \mathtt{fix}\ (\lambda \mathtt{self}\!:\!\mathtt{SetCounter}.\ \{\mathtt{get}=\ldots,\ \mathtt{set}=\ldots,\ \mathtt{inc} = \lambda\_\!:\!\mathtt{Unit}.\ \mathtt{self}.\mathtt{set}\,(\mathtt{succ}(\mathtt{self}.\mathtt{get}\ \mathtt{unit}))\})
$$

This works, but the `fix` is entirely internal to the class — `self` always resolves to *this exact* method record. That's ordinary (closed) recursion, not open recursion: a subclass overriding `set` wouldn't change what `inc` calls, because `inc`'s `self` was already tied to the specific fixed point computed inside `setCounterClass`.

**The fix (pun unavoidable): move `fix` outside the class (§18.10).** Instead of the class computing its own fixed point, it becomes a function that *also* takes `self` as a parameter, deferring the tying-of-the-knot to whoever instantiates the (possibly most-derived subclass's) object:

$$
\mathtt{setCounterClass} : \mathtt{CounterRep} \to \mathtt{SetCounter} \to \mathtt{SetCounter}, \qquad \mathtt{newSetCounter} = \lambda\_\!:\!\mathtt{Unit}.\ \mathtt{let}\ r = \ldots\ \mathtt{in}\ \mathtt{fix}\ (\mathtt{setCounterClass}\ r)
$$

Now when `instrCounterClass` is built on top of `setCounterClass`, it takes the *same* `self` parameter and threads it down: `let super = setCounterClass r self in ...`. When the final object is instantiated, a **single** `fix` — applied once, at the outermost, most-derived class — ties every level of the hierarchy to the *same* `self`, which is the record of methods of the most-derived class actually being constructed. This is precisely what "late binding of `self`" means formally: `self` inside a superclass method is not bound to "the superclass's own methods," it's bound to whatever gets passed in from outside, which turns out (via the fixed point) to be the full, most-derived object. A call from `inc` (defined in the superclass) to `self.set` can land on the *subclass's* overriding `set` — because `self` was never "the superclass's `self`," it was always "whatever `self` the eventual instantiation supplies."

**Grounding (Rust).** Rust's trait objects and dynamic dispatch already give you late-bound `self` for free — a default trait method calling `self.other_method()` dispatches through the vtable of whatever concrete type actually implements the trait, exactly mirroring "the superclass method calls the subclass's override":

```rust
trait SetCounter {
    fn get(&self) -> i64;
    fn set(&mut self, v: i64);
    fn inc(&mut self) {
        let v = self.get();      // "self.get" here is late-bound —
        self.set(v + 1);         // resolves through whatever concrete `Self` implements this trait
    }
}
```

If a type `InstrCounter` implements `SetCounter` and overrides `set` to also bump an access counter, then the *default* `inc` above — inherited unmodified — automatically calls the overridden `set`, purely because Rust resolves `self.set` dynamically (well, statically-but-generically via monomorphization/vtable, depending on `dyn` vs generic bound) through whatever `Self` actually is. This is the trait-object-shaped mirror of tying `fix` to the outermost `self`.

**Grounding (Lean).** Lean's `structure`/typeclass mechanism has no native mutable dispatch, but the *fixed-point* reading of `self` — the formal heart of §18.9 — is exactly what Lean's own well-founded recursion or `Nat.rec`-style fixed points are doing when you define mutually recursive functions and then ask "what does one clause see of the others." A closer literal match is building the mutual record via `WellFoundedRecursion`/`fix`-combinator style definitions, which is precisely TAPL's own presentation lifted into Lean's term language — the book's `fix` combinator and Lean's own internal handling of recursive definitions are doing the same job of "solve for the record whose fields refer to each other."

## The evaluation-order subtlety (§18.11)

Moving `fix` outward (§18.10) breaks something operationally, and this is the sharpest, most concrete piece of formal reasoning in the chapter. When `instrCounterClass` is instantiated —

$$
\mathtt{newInstrCounter} = \lambda\_\!:\!\mathtt{Unit}.\ \mathtt{let}\ r = \ldots\ \mathtt{in}\ \mathtt{fix}\ (\mathtt{instrCounterClass}\ r)
$$

— evaluation **diverges**. Pierce walks the reduction sequence step by step (§18.11, numbered steps 1–8): `instrCounterClass` immediately needs to build `super = setCounterClass r self`, and to do *that* it needs `self` reduced to a value — but `self` *is* `fix ⟨the very function being unfolded⟩`, so unfolding it via `E-Fix` (which substitutes `fix f` for `self` in `f`'s body) produces a term that again needs `self` reduced to a value before it can proceed, ad infinitum. The root cause: `fix`'s [[Operational-Semantics|operational semantics]] assumes the recursive reference to `self` only occurs in a "protected" position — inside an inner lambda, not needed immediately. But `instrCounterClass` uses `self` *right away*, unprotected, to build `super`.

**The repair: thunk `self`.** Change `self`'s type from `SetCounter` to `Unit → SetCounter` — an *object thunk* — and rewrite every use of `self` in a method body as `(self unit)`. Since a thunk `λ_:Unit. ...` is already a syntactic value, `fix` can unfold once and stop; the actual computation inside the thunk is deferred until something calls `self unit`. This is the identical protect-with-a-dummy-abstraction trick from §18.2's `get`/`inc` methods, now applied one level up, to `self` itself rather than to individual methods.

**The cost, flagged immediately (leading into §18.12):** every recursive call through `self` — e.g. `inc`'s `self.set(...)` becomes `(self unit).set(...)` — *recomputes the entire method table* on the spot, because `self unit` re-evaluates the thunk from scratch each time. Correctness is restored; efficiency is not.

**What breaks without the thunk, concretely:** `newInstrCounter unit` never returns a value at all — this is a genuine non-termination bug in the naive open-recursion encoding, not a performance nuisance, and it's the direct operational cost of choosing "closed-over-mutual-recursion via `fix`" as the encoding strategy for something (dynamic method dispatch) that real object-oriented languages implement with an entirely different mechanism (indirect table lookup at call time, no re-derivation).

## Efficient method-table construction (§18.12)

The thunking fix in §18.11 buys correctness at the price of recomputing the method table on every self-call. §18.12 replaces `fix` with an explicit, imperative "tie the knot" using references — closer to how a real runtime actually implements a vtable:

1. Allocate a heap cell for the method table *first*, initialized to a dummy record: `cAux = ref dummySetCounter`.
2. Build the real methods, passing them `cAux` (a *pointer to* the eventual table, not the table itself) as `self`, so method bodies read through `!self` rather than closing over the resolved table directly:
   $$
   \mathtt{setCounterClass} = \lambda r\!:\!\mathtt{CounterRep}.\ \lambda \mathtt{self}\!:\!\mathtt{Ref}\ \mathtt{SetCounter}.\ \{\ldots,\ \mathtt{inc} = \lambda\_\!:\!\mathtt{Unit}.\ (!\mathtt{self}).\mathtt{set}(\ldots)\}
   $$
3. **Back-patch**: `cAux := (setCounterClass r cAux); !cAux` — write the real methods into the cell after the fact, then read the cell out as the returned object.

Because every `!self` dereference is itself inside a `λ_:Unit.` (a method body, only entered when called), the cell is never actually read *during* construction — only after back-patching, when a caller later invokes a method. This sidesteps the divergence from §18.11 without needing a thunk-and-rethink on every call: **the method table is computed exactly once, at object-creation time**, and each subsequent method call just dereferences the (by-then-stable) cell — no recomputation.

**A typing subtlety that forces `Source` over `Ref`.** Naively typing `self` as `Ref InstrCounter` in a subclass fails to typecheck against a superclass expecting `Ref SetCounter`, because `Ref` is *invariant*: `Ref InstrCounter` and `Ref SetCounter` aren't subtypes of each other even though `InstrCounter <: SetCounter`, since `Ref` grants both read and write capability, and unrestricted covariant write would let you stash a `SetCounter`-only value into a cell that's supposed to only ever hold `InstrCounter`s. Since a class's `self` parameter is only ever *read* (`!self`), never written, Pierce switches its type to `Source InstrCounter` — the read-only capability introduced with references in Ch. 13, §15.5 — which *is* safely covariant: `Source InstrCounter <: Source SetCounter`. This is a nice small payoff of having built covariant/invariant/contravariant reference subtyping earlier in the book: it's exactly what's needed to let a subclass's `self` pointer stand in for a superclass's, with no unsoundness.

Even this version isn't the last word — Pierce flags explicitly (closing §18.12) that the method table, while now computed once per *object*, is still recomputed once per object even though it's *identical for every object of the same class*. The fix for that — building the table once per *class*, using [[Bounded-Quantification|bounded quantification]] — is deferred to Chapter 27, revisited below.

**Grounding (Rust).** The back-patch-a-heap-cell strategy is, almost verbatim, how you'd build a self-referential vtable-style structure in Rust without `dyn` dispatch's built-in machinery — allocate behind `Rc<RefCell<_>>`, fill in a placeholder, then overwrite:

```rust
use std::cell::RefCell;
use std::rc::Rc;

type MethodTable = Rc<RefCell<SetCounterMethods>>;

fn new_set_counter() -> MethodTable {
    let dummy = SetCounterMethods::dummy();
    let cell = Rc::new(RefCell::new(dummy));
    let real = build_set_counter_methods(Rc::clone(&cell)); // closures capture `cell`, read it lazily
    *cell.borrow_mut() = real;
    cell
}
```

This is precisely what a real vtable-based dynamic-dispatch implementation does at a lower level: allocate the object, then fill in a pointer to its method table — except in Rust's built-in `dyn Trait`, the compiler generates this vtable once per *type* at compile time rather than per object at runtime, which is exactly the efficiency gap Chapter 27 closes for the encoded version.

**Grounding (Python).** Python's actual object model already does the class-level (not per-object) version of this: a class's method table (`__dict__` on the class, or the MRO-resolved lookup chain) is built once, when `class Foo(Bar): ...` executes, and every instance shares it — `instance.method` looks the method up on the *class*, with `self` bound at call time via the descriptor protocol. This is the real-world proof that Chapter 27's optimization (build once per class, not once per object) isn't a curiosity — it's how every mainstream object system actually works, and Chapter 18's per-object construction is the "obviously correct but naively slow" baseline that motivates it.

## Recap and the chapter's own synthesis (§18.13)

Pierce closes by mapping each of the five defining features from §18.1 back onto its encoding, and it's worth restating why each mapping is not just definitional bookkeeping:

- **Multiple representations** → different classes producing the same interface type (`Counter`) from structurally different `*Rep` records; nothing about the *type* reveals which.
- **Encapsulation** → falls out of lexical scoping over the representation record, not a dedicated privacy mechanism.
- **Subtyping** → literally record subtyping; no separate "object subtyping" judgment was ever introduced.
- **Inheritance** → superclass instantiation (`let super = ... in ...`) plus selective field copy/override in a new record.
- **Open recursion** → a `self` parameter, resolved by a *single, outermost* `fix` (or its reference-cell equivalent) at object-construction time, so that every level of the class hierarchy shares the same, most-derived `self`.

Every one of these five is recovered from tools introduced chapters earlier — no new primitive was needed anywhere in the chapter. That's the chapter's real thesis, stated at the very end via the recap rather than upfront: object-oriented programming is not a different kind of computation, it's a *design pattern* expressible entirely inside a typed lambda-calculus with records, `fix`, and references.

## Where this leads

```
Ch. 13 (References) ─┐
Ch. 11 (Records, fix) ┼──► Ch. 18: encoded objects/classes/self ──┬──► Ch. 19: Featherweight Java
Ch. 15 (Subtyping)   ─┘         (this article)                    │      (objects as primitives, not an encoding —
                                                                    │       because §18.11's evaluation-order problem
                                                                    │       shows the encoding has real seams)
                                                                    ├──► Ch. 27: Imperative Objects, Redux
                                                                    │      (§18.12's per-object table rebuilt
                                                                    │       once-per-class via bounded quantification)
                                                                    └──► Ch. 32: purely functional objects in F<:ω
                                                                           (same self/fix pattern, no references —
                                                                            note the Lean grounding above already
                                                                            previews this)
```

The most direct forward pointer is technical and precise: the inefficiency flagged at the very end of §18.12 — one method table built per *object*, when it's identical for every object of a class — is exactly the problem Chapter 27 solves with bounded quantification, so this chapter's closing dissatisfaction *is* Chapter 27's opening motivation.

For the standing project of building a Rust verifier/compiler and a Lean-style elaborator: the `fix`-then-thunk maneuver in §18.9–§18.11 is a clean, self-contained illustration of a recurring theme — a construction that is *semantically* correct (mutual recursion via `fix`) can still be *operationally* broken (divergence) if the evaluation strategy's assumptions (arguments to `fix` must use their recursive reference only in protected position) aren't respected, and the fix is a syntactic discipline (thunking), not a change to the underlying typing rules. That is precisely the kind of distinction a type checker alone cannot catch — the `fix`-applied-to-`instrCounterClass` term above is perfectly well-typed and still diverges — which is a useful cautionary data point for any checker/verifier project: [[Type-Safety|type safety]] (progress + preservation) guarantees a well-typed term doesn't get *stuck*, but says nothing about whether it *terminates*. Ill-behaved recursion schemes can hide behind a clean type signature.
