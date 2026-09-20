---
title: Type Formers
source: A HoTT Approach to Computational Effects (Wells, 2019)
chapter: "2.1.4–2.1.8: Sums and Products, Finite Types, Dependent Types"
pages: "13–18"
tags: [hott, type-theory, sum-types, product-types, dependent-types, sigma-types, pi-types]
---

[[book-guidelines|↩ Back to guidelines]]

## What a "type former" is actually for

[[Foundations-of-Homotopy-Type-Theory|The previous article]] gave you judgments and functions — the bare minimum to say "this is a type" and "here's a mapping between types." This article is about the machinery for actually *constructing* new types out of old ones. Every construct here follows the same three-part shape, worth naming explicitly because it recurs identically for every type former: **constructors** (how do you build an object of this type), **eliminators/computation rules** (how do you consume/pattern-match an object of this type), and — later, once dependent types are introduced — **a topological picture** for what the type "looks like" as a space. If you've written an `enum` and a `match` in Rust, or an `Inductive` and pattern-matching function in Coq, you already have the right mental model; the book is about to show you it generalizes far beyond `Option`/`Result`-shaped enums.

## Sum types: disjoint union, not "OR"

Given types $A$ and $B$, the **sum type** $A + B$ contains objects that are either $a : A$ or $b : B$ — but crucially, **disjoint copies**. This is worth dwelling on: $A + A$ is *not* the same type as $A$, even though naively "$A$ or $A$" sounds redundant. Topologically the sum type is a genuinely distinct space from either summand — you haven't merged $A$ and $A$, you've built a new space with two separate labeled copies of $A$ inside it.

Two **constructors** build objects of $A + B$: the left injection $\mathrm{inl} : A \to A + B$ and the right injection $\mathrm{inr} : B \to A + B$. Consuming a sum type requires case analysis on *both* injections — given $f : A + B \to C$, you must supply $g : A \to C$ for the $\mathrm{inl}$ case and $h : B \to C$ for the $\mathrm{inr}$ case.

```rust
// A + B, faithfully
enum Sum<A, B> {
    Inl(A),
    Inr(B),
}

fn swap<A, B>(x: Sum<A, B>) -> Sum<B, A> {
    match x {
        Sum::Inl(a) => Sum::Inr(a),
        Sum::Inr(b) => Sum::Inl(b),
    }
}
```

If you've ever wondered why Rust's `Result<T, E>` forces you to handle both `Ok` and `Err` — this is why, structurally. `Result<T, E>` *is* $T + E$, and the exhaustiveness checker is enforcing the sum type's computation rule: you cannot consume a sum without addressing every injection.

## Product types: ordered pairs, nothing fancier

$A \times B$ is the classical Cartesian product — objects are pairs $(a, b) : A \times B$. Consuming a product means supplying a function $g : A \to B \to C$ that gets applied to the pair's two components; this is the product's computation rule. The book works a small example combining both formers — a function $f : A \times B \to A + B$ defined by case-splitting on a helper $g : A \to B \to A + B$:

$$f\ (a, b) :\equiv (g\ a)\ b, \qquad (g\ a)\ b :\equiv \mathrm{inl}_{\mathrm{inl}\ a} \mid \mathrm{inr}_{\mathrm{inr}\ b}$$

```rust
fn combine<A, B>((a, _b): (A, B)) -> Sum<A, B> {
    Sum::Inl(a) // or Sum::Inr(b), depending on which projection you want
}
```

Nothing here should feel unfamiliar — `struct`/tuple types in Rust and `A × B` are the same thing under different notation.

## The empty and unit types: the two smallest possible spaces

The **empty type** $0$ has **zero constructors** — there is no way to build an object of $0$ at all. Topologically: a space with no points. The interesting consequence is a function $f : 0 \to A$ always exists, for *any* $A$ — because there's nothing to check the function against, vacuous totality is free. (This is the type-theoretic reading of "false implies anything," made concrete in the next article's predicate-logic section.) Going the other direction, $g : A \to 0$ can only exist if $A$ *is itself* empty — you can't map a nonempty space into nothing.

The **unit type** $1$ has exactly one object, written $\bullet : 1$ — a single-point space. Any computation over $1$ needs to handle exactly one case.

```rust
enum Empty {}      // 0 — uninhabited, zero constructors
struct Unit;        // 1 — exactly one value
```

`Empty` (or `!`, the never type) and `()` in Rust are the literal Rust names for these — if you've ever used `Result<T, Infallible>` to statically guarantee a function can't fail, you were using $0$ (or a type isomorphic to it) exactly as HoTT defines it.

**Building other finite types for free:** $0$ and $1$ aren't just curiosities — they're the raw material for every finite type. The book's example: $2$ (a type with exactly two objects, i.e. Booleans) is constructed as $1 + 1$, with the two injections $\mathrm{inl}\ \bullet$ and $\mathrm{inr}\ \bullet$ renamed $\mathrm{true}$ and $\mathrm{false}$. This is a genuinely different *justification* for Booleans than "there happen to be two truth values" — Boolean-ness falls out of composing two type formers you already have, rather than being postulated as primitive.

```rust
// 2 = 1 + 1, with the two injections renamed
type Bool2 = Sum<Unit, Unit>; // Inl(Unit) = true, Inr(Unit) = false
```

## Dependent types: when the *output type* depends on the input value

Everything so far builds fixed types from fixed types. A **dependent type** (type family) breaks that: it's a function $f : A \to \mathcal{U}$ — takes an ordinary *value*, returns a *type*. The book's canonical example is $V : \mathbb{N} \to \mathcal{U}$, mapping a natural number $n$ to the type of all length-$n$ vectors. This is the single most important idea in this article for a refinement/dependent-type compiler project, so it's worth being precise about what's new: in ordinary (simply-typed) programming, a type never depends on a runtime value. Here, it explicitly does — $V\ 3$ and $V\ 5$ are *different types*, and which one you get depends on which natural number you plugged in.

```rust
// Rust can only approximate this with const generics —
// the const parameter IS a value baked into the type
struct Vector<const N: usize> {
    data: [f64; N],
}
// Vector<3> and Vector<5> are genuinely different types,
// exactly as V 3 and V 5 are different types in HoTT.
```

```lean
-- Lean expresses V : N → U directly and natively — no encoding needed
def V : Nat → Type := fun n => Vector Float n
-- `Vector Float 3` and `Vector Float 5` are literally different types,
-- and Lean's elaborator tracks this dependency through every subsequent
-- use, the same way it tracks any other term-level dependency.
```

This is exactly the mechanism a length-indexed vector, a refinement type `{x : Int | x > 0}`, or a Hoare-style pre/postcondition type all rest on: **the type itself is allowed to mention a value**. Once you accept dependent types as a primitive, "the type of sorted lists of length $n$" and "the type of proofs that $x > 0$" stop being special cases — they're just type families like $V$.

## Dependent product ($\Pi$) types: functions with value-dependent codomains

The **dependent product type**, written $\prod_{a:A}(B\ a)$ for $A : \mathcal{U}$ and $B : A \to \mathcal{U}$, generalizes ordinary function types — if $B$ happens to be *constant* (ignoring its input), $\prod_{a:A}(B\ a)$ collapses exactly to the ordinary $A \to B$. The book's worked example: given $V : \mathbb{N} \to \mathcal{U}$,

$$f : \prod_{n:\mathbb{N}} (V\ n)$$

is a function that, applied to a specific $n$, yields a specific $n$-dimensional vector $\vec{v}$ — its *return type itself changes* depending on which $n$ you feed it.

**Why "$\Pi$"?** This isn't arbitrary notation — a dependent product over a *finite* index set really is literally a product (in the categorical/set-theoretic sense) of the family $\{B\ a\}_{a:A}$, one factor per index. $\Pi$-types are the type-theoretic generalization of that finite product to an arbitrary (possibly infinite, possibly type-level) index.

**This is precisely the type of universal quantification**, which the next article makes fully explicit — but it's worth flagging early because it's the single most load-bearing construct for a Hoare-logic-style verifier: a $\Pi$-type is how you express "for all inputs satisfying precondition $P$, the output satisfies postcondition $Q$" as an actual *type*, not as an external annotation bolted onto a type.

```lean
-- A function whose return type depends on its argument value —
-- this IS a Π-type, spelled `(n : Nat) → Vector Float n` in Lean.
def zeroVec : (n : Nat) → Vector Float n
  | n => Vector.replicate n 0.0
```

## Dependent sum ($\Sigma$) types: pairs with a value-dependent second component

The **dependent sum type**, $\sum_{a:A}(B\ a)$, generalizes the product type the same way $\Pi$ generalizes function types: objects are pairs $(a, b)$ where **the type of $b$ depends on the value of $a$**. If $B$ is constant, $\sum_{a:A}(B\ a)$ collapses to the ordinary product $A \times B$. Continuing the vector example, you can package a length together with a vector of exactly that length:

$$(n, \vec{v}) : \sum_{n:\mathbb{N}}(V\ n)$$

This single object *is* a length-tagged vector — the length and the vector are bundled so that the type system can see they're consistent, which is exactly the shape of a **refinement type carrying its own witness**: "a value together with a proof/index that it satisfies some property."

```rust
// Rust can only fake this with an enum over fixed sizes, or erase
// the dependency and check it at runtime — Sigma types are precisely
// what Rust's type system is missing here.
enum SizedVec {
    Len3(Vector<3>),
    Len5(Vector<5>),
    // ... this does not scale; a real Sigma type needs no such enumeration
}
```

```lean
-- Sigma types are native: `Σ n : Nat, Vector Float n`
def sized : Σ n : Nat, Vector Float n := ⟨3, Vector.replicate 3 0.0⟩
-- `.1` recovers the length, `.2` the vector — and Lean's kernel knows
-- `.2`'s type is `Vector Float sized.1`, not some fixed n.
```

## Where this leads

$\Pi$-types and $\Sigma$-types are the two constructs everything downstream of Chapter 2 is built from — the [[Propositions-as-Types|next article]]'s treatment of predicate logic reads universal quantification as literally a $\Pi$-type and existential quantification as literally a $\Sigma$-type, and the identity type (also introduced there) is itself defined as a dependent type $\mathrm{Id} : A \to A \to \mathcal{U}$. Later, the [[Equivalence-and-Univalence|equivalence and Univalence]] machinery both lean on $\Sigma$-types (a fiber is defined as a $\Sigma$-type over the domain) to state precisely what it means for two types to be "the same." Sum and product types, meanwhile, resurface concretely in Chapter 5's action types — the Interactive Input and Exception Handling actions are literally inductive types built from constructors in exactly the "zero, one, or two constructors" style introduced here for $0$, $1$, and $A + B$.

**Connection to the standing project:** $\Sigma$-types are, almost by definition, what a refinement type *is* — `{x : Int | x > 0}` is nothing more than $\sum_{x:\mathrm{Int}} (x > 0)$, a value paired with a proof of a property, exactly like the length-tagged vector above. $\Pi$-types are what a dependent function's Hoare-style contract lives inside — the precondition shapes what values of $A$ are even well-typed inputs, and the postcondition is the dependent codomain $B\ a$. Any elaborator resolving implicit arguments for $\Pi$- or $\Sigma$-typed terms is doing exactly the metavariable unification your project's elaborator needs, just described here in its purest, un-annotated form.
