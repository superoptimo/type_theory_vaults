---
title: Generic Programming
source: "Practical Foundations for Programming Languages (Robert Harper, 2012)"
chapter: "Chapter 14, Generic Programming"
pages: "121–125"
tags: [type-theory, generic-programming, type-operators, functors, positivity, praxis-harper]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem: "apply f here, but not there"

Suppose you have a function `f : ρ → ρ'` — Harper's example is doubling a natural number. You have some larger structure that contains values of type `ρ` sitting inside it, say a pair `bool × ρ`, and you want to lift `f` into a function that transforms the whole structure: `bool × ρ → bool × ρ'`, sending `⟨a, b⟩` to `⟨a, f(b)⟩`.

That sounds trivial for a pair — obviously you touch the second component and leave the first alone. But state the problem in general: given `f : ρ → ρ'`, and *some* type `τ` built up out of `ρ` (formally, `[ρ/t]τ` — the type `τ` with a variable `t` instantiated to `ρ`), how do you extend `f` to a function `[ρ/t]τ → [ρ'/t]τ`?

**What breaks without a marker.** If `ρ` occurs more than once inside `τ`, or if `ρ` happens to equal some other type already present in `τ` for unrelated reasons, there is no way to tell, just by staring at the *type* `[ρ/t]τ`, which occurrences of `ρ` are "the ones from the pattern" that `f` should touch, and which are incidental. The extension is genuinely ambiguous. You need to mark, *before* substituting `ρ` in, exactly which slots are meant to be transformed.

This is the same shape of question you hit constantly in Rust or Lean generic code: given `impl<T> Foo<T>` and a function `f: T -> U`, which fields of `Foo<T>` does `.map(f)` actually touch? The answer isn't determined by the concrete type `Foo<i32>` — it's determined by the *shape* of the generic definition, i.e. by where `T` appears in `struct Foo<T> { ... }` before you ever plug in `i32`.

## Type operators: naming the transformation spots

Harper's fix is to keep the pattern and the instantiation as separate objects. A **type operator** is a type expression `τ` with a designated free variable `t`, written as the abstractor `t.τ`, subject to the formation judgment `t type ⊢ τ type`. The variable `t` is not a type you ever inhabit directly — it is a placeholder marking every spot where the transformation should apply.

Example straight from the book:

$$t.\ \mathbf{unit} + (\mathbf{bool} \times t)$$

Every occurrence of `t` here is a marked spot. An **instance** of the operator `t.τ` at a concrete type `ρ` is the ordinary substitution `[ρ/t]τ`, also written `Map[t.τ](ρ)`. So `t.τ` is the *pattern*, and `[ρ/t]τ` is one *particular data type* obtained by filling in the pattern — the operator itself is not a type, it's a type-with-a-hole together with a name for the hole.

This is exactly the difference between a Rust generic struct definition and one of its monomorphizations:

```rust
// the "type operator": t.τ, i.e. Vec<t> where t marks the slot
struct Wrapper<T> {
    tag: bool,
    payload: T,
}

// the instance [ρ/t]τ at ρ = i32
type WrapperI32 = Wrapper<i32>;
```

`struct Wrapper<T>` is the abstractor; `T` is `t`; `Wrapper<i32>` is `[i32/t]τ`. In Lean the same distinction shows up as an inductive family parameterized over a type variable versus one of its instantiations — the family declaration is the operator, a specific instantiation is the instance.

### Polynomial type operators

Not every type expression with a hole is tractable to extend generically — Harper restricts attention first to **polynomial type operators**: those built from the variable `t`, the empty type `void`, the unit type `unit`, and products and sums (`τ₁ × τ₂`, `τ₁ + τ₂`). This is precisely the "algebraic data type" fragment — no function types allowed yet. The judgment `t.τ poly` is defined by a straightforward structural induction over this grammar. Every ordinary Rust `enum`/`struct` built from other such types (no closures, no trait objects) is a polynomial type operator in this sense; so is every plain algebraic data type in Lean or Haskell.

## Generic extension: `map`

Now the actual lifting operation. Harper introduces a primitive expression form:

$$\text{map}[t.\tau](x.e'; e)$$

with the static typing rule

$$\frac{t\ \text{type} \vdash \tau\ \text{type} \qquad \Gamma, x:\rho \vdash e' : \rho' \qquad \Gamma \vdash e : [\rho/t]\tau}{\Gamma \vdash \text{map}[t.\tau](x.e'; e) : [\rho'/t]\tau}$$

Read it as three ingredients: the *shape* `t.τ` (where to transform), the *transformer* `x.e'` (an abstractor describing `f : ρ → ρ'`, written out as an expression with a bound variable rather than a bare function symbol), and the *subject* `e` (a value of the pre-instance type `[ρ/t]τ`). The result has type `[ρ'/t]τ` — same shape, `ρ` replaced by `ρ'` everywhere `t` was marked.

This is the formal, unambiguous version of "`.map(f)`" — and the reason it needed a whole apparatus before this point is that `.map` in most languages is defined once per data type by the library author, baking in by hand which fields get touched. Harper's `map[t.τ]` makes that choice a first-class part of the term, driven by the operator `t.τ` itself, and *derives* the traversal by recursion on the structure of `τ` rather than requiring a hand-written instance per type.

### Dynamics: structural recursion on the operator

The reduction rules for `map` are given by cases on the syntactic shape of `τ`, one rule per polynomial constructor:

$$\text{map}[t.t](x.e'; e) \mapsto [e/x]e' \tag{14.2a}$$
$$\text{map}[t.\mathbf{unit}](x.e'; e) \mapsto \langle\rangle \tag{14.2b}$$
$$\text{map}[t.\tau_1 \times \tau_2](x.e'; e) \mapsto \langle \text{map}[t.\tau_1](x.e'; e\cdot l),\ \text{map}[t.\tau_2](x.e'; e\cdot r)\rangle \tag{14.2c}$$
$$\text{map}[t.\mathbf{void}](x.e'; e) \mapsto \text{abort}(e) \tag{14.2d}$$
$$\text{map}[t.\tau_1+\tau_2](x.e'; e) \mapsto \mathbf{case}\ e\ \{l\cdot x_1 \Rightarrow l\cdot\text{map}[t.\tau_1](x.e'; x_1) \mid r\cdot x_2 \Rightarrow r\cdot\text{map}[t.\tau_2](x.e'; x_2)\} \tag{14.2e}$$

Read them as: (a) at the marked spot itself, actually apply the transformer; (b) `unit` has one value and it maps to itself; (c) on a pair, map each component independently according to its own sub-operator; (d) `void` has no values, so this case is vacuously handled by `abort`; (e) on a sum, case-split and map whichever side matched. Each rule strictly decreases the size of `τ`, so this recursion terminates in tandem with type-checking — the traversal is completely determined by the type operator's syntax, not chosen ad hoc.

Harper's worked example: take `t.τ = t.unit + (bool × t)`, and let `x.e` be `x.s(x)` (successor, i.e. increment). Then

$$\text{map}[t.\tau](x.e;\ r\cdot\langle\text{true}, n\rangle) \mapsto^* r\cdot\langle\text{true}, n+1\rangle.$$

The `n` gets incremented because that's where `t` sits in the operator; `true` is untouched because it sits in a position that was never marked.

In Rust terms, this is exactly what `#[derive(Functor)]`-style macros (or a hand-rolled `Bifunctor`/traversal impl) generate mechanically per-`enum`-variant and per-`struct`-field: a `match` that recurses into products field-by-field and sums variant-by-variant, applying `f` only at the type parameter's position. In Lean, the analogous mechanically-derived function is what `Functor.map` looks like when auto-generated for a structure or inductive type parameterized by `t`.

```rust
enum Shape<T> {
    Base,               // unit
    Cont(bool, T),       // bool × t
}

fn map_shape<T, U>(f: impl Fn(T) -> U, s: Shape<T>) -> Shape<U> {
    match s {
        Shape::Base => Shape::Base,               // rule (14.2b)/(14.2d)-ish: no t here
        Shape::Cont(b, t) => Shape::Cont(b, f(t)), // rule (14.2c): map bool untouched, t transformed
    }
}
```

That `match` arm structure is precisely rules (14.2c) and (14.2e) unrolled for this one operator.

**Preservation.** Theorem 14.1 states the expected [[Dynamic-Classification#Safety|safety]] property: if `map[t.τ](x.e'; e) : τ'` and it steps to `e''`, then `e'' : τ'` too. The proof is by inversion on the typing derivation followed by cases on which reduction rule (14.2a)–(14.2e) applies — e.g. for the product case, both projections retain their expected instance types by the induction hypothesis, so the reassembled pair does too. It's a routine structural induction, but it's the formal guarantee that "generic `map` never produces ill-typed junk," which is exactly the property you'd want a derive-macro or a generated traversal to satisfy before trusting it in a compiler.

## Positive type operators: letting functions in, carefully

Polynomial operators forbid function types entirely. But plenty of realistic generic containers involve functions — e.g. `t.ρ₀ → t` (a "callback returning a `t`"), or more usefully, higher-order representations of trees where children are given by functions. Can `map` be extended to `τ₁ → τ₂` where `t` might appear in either side?

**What breaks:** Consider the naive attempt on `t.τ₁ → τ₂` with no restriction on where `t` may occur. We're given `e : [ρ/t]τ₁ → [ρ/t]τ₂` and want to produce a function of type `[ρ'/t]τ₁ → [ρ'/t]τ₂`. If `t` occurs in `τ₁` (the *domain*), we'd need to build an argument of type `[ρ/t]τ₁` out of one of type `[ρ'/t]τ₁` in order to feed it to `e` — but the transformer `x.e'` we were handed only goes forward, `ρ → ρ'`, not backward. There is, in general, no way to invert it. Generic extension across an *arbitrary* occurrence of `t` inside a domain position is simply not well-defined with the tools given.

Harper's terminology for this, borrowed from logic (a function type `τ₁ → τ₂` is classically like `¬τ₁ ∨ τ₂`, so domain occurrences sit under a negation): occurrences of `t` in the **domain** of a function type are **negative occurrences**; occurrences in the **range** of a function type, or inside a product or sum, are **positive occurrences**.

A **positive type operator** is one in which `t` occurs only positively. Formally, `t.τ₁ → τ₂` is positive provided (1) `t` does not occur in `τ₁` at all, and (2) `t.τ₂` is itself positive. This is a strictly weaker fragment than "no functions at all" — it permits function types, just not ones that consume the generic parameter.

The [[Exceptions#Dynamics|dynamics]] extends with one more rule:

$$\text{map}[t.\tau_1 \to \tau_2](x.e'; e) \mapsto \lambda(x_1{:}\tau_1)\ \text{map}[t.\tau_2](x.e'; e(x_1)) \tag{14.3}$$

Because `t` is guaranteed absent from `τ₁`, the argument `x_1` needs no transformation at all — apply `e` directly, and only transform the *result*, recursively, according to `t.τ₂`.

This is the same variance discipline that governs `Fn` trait bounds and covariant/contravariant generics in Rust, and that shows up in Lean/category theory as the distinction between a covariant functor (`Functor`) and something requiring a `Contravariant` instance (or, for mixed variance, a full profunctor). "Positive occurrence" is literally "covariant position"; the restriction that `map` only handles positive operators is the type-operator-level statement of "you can only functorially map over covariant slots, not contravariant ones, without extra structure."

```rust
// t.(bool -> t): positive — t only in the range. map lifts the *output*.
fn map_fn<T, U>(f: impl Fn(T) -> U, g: impl Fn(bool) -> T) -> impl Fn(bool) -> U {
    move |b| f(g(b))
}
// t.(t -> bool): NEGATIVE — t in the domain. There is no general way to
// turn a "consumer of ρ'" into a "consumer of ρ" from just f : ρ -> ρ'.
```

**Recovering full functoriality with isomorphisms.** Harper notes the fix for negative occurrences: if the transformer `x.e'` is actually one half of a *type isomorphism* — a pair of mutually inverse maps `ρ ↔ ρ'` — then you can use the inverse to turn a `ρ'` back into a `ρ` wherever a negative (domain) occurrence demands one, apply the original function `e`, and transform the output forward again. So full functorial action over arbitrary operators (positive *and* negative occurrences of `t`) is recoverable, but only by strengthening the input from "a function" to "an isomorphism, with its inverse in hand" — you pay for the extra power at the interface.

## Why this is "functorial programming"

Harper is explicit (§14.4) that generic extension is exactly the categorical notion of a **functor** (MacLane, 1998): an assignment of objects to objects (types `ρ ↦ [ρ/t]τ`) together with an assignment of morphisms to morphisms (functions `f ↦ map[t.τ](x.f(x); -)`) that respects identities and composition. "Generic programming is essentially functorial programming, exploiting the functorial action of polynomial type operators" (Hinze and Jeuring, 2003, as cited by Harper).

Concretely: `t.τ` is the *object part* of the functor (it tells you, for every type `ρ`, what type `[ρ/t]τ` is); `map[t.τ]` is the *morphism part* (it tells you, for every function `f : ρ → ρ'`, what function `[ρ/t]τ → [ρ'/t]τ` you get). Rule (14.2a) through (14.2e) collectively are the proof-by-construction that this assignment is well-behaved on the polynomial fragment; positivity is exactly the condition category theorists know as "being covariant" — it's what lets an assignment on morphisms go the same direction as the assignment on objects.

This is also precisely `impl<T> Functor for MyType<T>` in Haskell/Rust-with-a-Functor-trait, or `Functor` instances auto-derivable in Lean for strictly-positive inductive families — the positivity restriction here is the *same* strict-positivity condition that inductive type theories (Lean included) impose on constructors to guarantee termination and consistency, just specialized to the "can I `map` over this slot" question rather than the "can I recurse on this slot" question.

## Where this leads

Chapter 15 ([[Inductive-and-Coinductive-Types|Inductive and Coinductive Types]]) builds recursors and generators directly on top of positive type operators, and uses `map[t.τ]` as the engine that drives one step of unfolding a recursive/corecursive definition — this chapter's `map` is literally the machinery Chapter 15's fold/unfold dynamics is built from. The positivity restriction introduced here is also the direct ancestor of the strict-positivity check that any inductive-type kernel (Lean's included) runs on constructor argument types before accepting a declaration, precisely to block the same negative-occurrence problem this chapter diagnoses — so if the Rust verifier or elaborator project ever needs to validate a user-declared generic/inductive type, this positivity check (walk the type, classify each occurrence of the parameter as positive or negative, reject negative ones outside a domain-empty context) is the mechanism to reimplement.
