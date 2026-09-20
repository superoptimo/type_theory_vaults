---
title: Foundations of Homotopy Type Theory
source: A HoTT Approach to Computational Effects (Wells, 2019)
chapter: "2.1: Type and Space"
pages: "7–17"
tags: [hott, type-theory, judgments, universes, functions, dependent-types]
---

[[book-guidelines|↩ Back to guidelines]]

## Why a foundation without set theory at all?

Homotopy type theory (HoTT) is presented as an extension of Per Martin-Löf's *intensional type theory*, itself a formalization of Russell's theory of types. The pitch is not "types, but with extra rules bolted on" — it's a genuinely different foundation for mathematics, one with **no first-order logic underneath it at all**. There is no ambient logic that types are built on top of; the type system *is* the logic (this becomes concrete in the next article's treatment of propositions-as-types). What you get in exchange for giving up the familiar set-theoretic ground is a foundation where **types can be visualized as topological spaces** and their inhabitants as points — a link to homotopy theory (and, one level further, higher category theory) that lets you reason about paths and shapes without needing general topology's machinery.

If you're coming from a compilers/type-systems background, the header-level thing to hold onto is: **everything here is going to look like a type system, because it is one** — but it's also meant to be read as geometry. Every construct in this article gets a double life: a syntactic rule, and a picture.

## Judgments: the only two things you're allowed to say

Without predicate logic as scaffolding, HoTT limits itself to exactly two basic **judgments** — not propositions, but *syntactic* statements about well-formedness:

1. $a : A$ — "$a$ is an object of type $A$," equivalently "$a$ is a point of space $A$."
2. $A \equiv B$ (types) or $a \equiv b : A$ (objects) — **judgmental equality**, "equal by definition."

A judgmental equality is introduced with $A :\equiv B$, "$A$ is *defined as* $B$." These definitions are static — checking judgmental equality is just term reduction, nothing more clever than that. Topologically: judgmental equality is symmetry — two shapes that are literally the same shape, viewed from different angles.

**The detail that trips people up first:** $a : A$ and $a \equiv a$ are not propositions. They can't be true or false — they can only be *syntactically valid or invalid*. `-1 : N` isn't a false statement, it's not a statement at all; it doesn't parse. `1 ≡ 2 : N` is the same kind of non-statement. This is exactly the distinction a compiler engineer already lives with: a type error isn't a false claim about your program, it's a rejection at the grammar level, before truth or falsity is even on the table. The book explicitly makes this comparison: a type-checker's job (compiler or mathematician's) is to keep ill-formed statements from being expressible in the first place.

*Lean framing:* this is literally what `#check` versus `#eval` is doing for you. `#check` asks "is this syntactically/typally valid" — judgment 1. Definitional unfolding during elaboration (`rfl`-provable-by-reduction goals) is judgment 2 in action. When Lean's elaborator says a term "failed to synthesize," it's rejecting at the level of judgment 1 — not claiming your term is *false*, claiming it's *not even a candidate* for truth.

## Universes: types that contain types

A **universe** is a type whose inhabitants are themselves types. Writing $A : \mathcal{U}$ says "$A$ is a type living in universe $\mathcal{U}$." The book adopts the **Russellian-style cumulative hierarchy**:

$$\mathcal{U}_0 : \mathcal{U}_1 : \mathcal{U}_2 : \dots$$

**What breaks without this:** if you allow one universe of *all* types, including itself ($\mathcal{U}_\infty : \mathcal{U}_\infty$), you reconstruct Russell's paradox inside the type theory — the type of all types would have to contain itself, and "does the type of all types belong to itself" is exactly the self-reference that broke naive set theory. The hierarchy is the fix: every universe lives strictly inside the next one up, so there's no rung of the ladder that contains itself.

**Typical ambiguity** is the practical relief valve: when the exact level of a universe doesn't matter to the argument, you write $\mathcal{U}$ without a subscript and let it be implicit. This is convenient but genuinely dangerous if abused — sloppy typical ambiguity is exactly how you'd smuggle a paradox back in. The book's own resolution mirrors how real proof assistants handle it: Coq (and Lean, for that matter) tracks universe levels automatically under the hood via **universe polymorphism/unification**, so informal HoTT prose can freely use typical ambiguity while the machine-checked version pins down consistent levels behind the scenes.

*Lean framing — this is not a toy concern:* Lean's own kernel has exactly this hierarchy (`Sort 0`, `Type 0 = Sort 1`, `Type 1`, ...), and Lean's elaborator performs universe-level unification as a real, load-bearing part of elaboration — solving metavariables that stand for universe levels, not just term-level metavariables. If you're building an elaborator with implicit-argument resolution via metavariable unification, universe-level metavariables are a second, easy-to-forget unification problem living alongside your ordinary term metavariables — get this wrong and you either reject valid Coq/Lean-like polymorphic code or, worse, silently reconstruct Russell's paradox in your kernel.

## Functions: total, continuous, first-class threads between spaces

Functions are **primitive** — not derived from sets of ordered pairs, but built-in structures of type theory in their own right: $f : A \to B$. The topological picture: a function is a thread connecting a point in $A$ to a point in $B$.

```rust
// Rust already commits to "functions are total" the moment you write
// a signature without an Option/Result in the return type.
fn add_five(n: u64) -> u64 { n + 5 }
```

Function definition and application follow familiar rules — right-associativity for application (`f g x` means `f (g x)`), and **currying** for multi-argument functions: $f : A \to B \to C$ really means $f : A \to (B \to C)$, a function that takes an $A$ and *returns a function* $B \to C$. Applying a curried function needs explicit parens to force left-associativity: $(f\ a)\ b$.

```rust
// add : N -> N -> N, i.e. add : N -> (N -> N)
fn add(n: u64) -> impl Fn(u64) -> u64 {
    move |m| n + m
}
// (add n) m corresponds to add(n)(m)
```

Two more definitions worth having named precisely, because they recur constantly later in the thesis:

- A function $f : A \to B$ is **constant** if $f\ a \equiv b$ for *every* $a : A$, landing on one single $b$.
- The **fiber** of $f$ over $b : B$ is the collection of every $a : A$ that maps to $b$, written $f^{-1}\ b$ — visualized as every thread from $A$ that gets "woven together" into the single point $b$ in $B$.

**Fibers matter far beyond this section** — the entire definition of *equivalence* in the Univalence discussion later in this chapter is built on top of fibers being singletons (one-element). If you don't have a solid picture of "fiber = preimage, but visualized as bundled threads," the equivalence definition later will feel unmotivated.

*Rust framing for fibers:* think of `f^{-1} b` as the (possibly-empty, possibly-many-element) set of inputs your `PartialEq`-style inverse lookup would return for a given output — a fiber is a preimage, full stop, just given a spatial name.

Finally: type-theoretic functions are always **total** (well-defined on every input of the domain — partiality has to be *encoded* on top, e.g. via a sum type, as Chapter 3 will do for Turing machines) and always **continuous** (they preserve paths — a notion that only becomes fully precise once identity types are introduced, but the promise is that functions can't tear spaces apart arbitrarily). Discontinuous or partial functions are always defined *in terms of* the well-behaved primitive kind, never as new primitives — a discipline worth flagging directly: **this is the same discipline a refinement-type checker needs.** If your compiler's function type is unconditionally total, then a function that might fail (division, partial pattern match) has to be *encoded* as total-but-returning-an-option/sum-type, exactly as HoTT does, and exactly as the thesis will formalize in Chapter 3's step-indexed Turing machine encoding and Chapter 5's exception-handling action.

## Where this leads

This section is the vocabulary the rest of the book assumes fluently: **judgments** distinguish syntactic validity from provable truth (a distinction the next article, on [[Propositions-as-Types|Propositions as Types]], needs immediately to explain why not every type gets to count as a "proposition"); **universes and typical ambiguity** resurface any time the thesis needs to quantify over "all types of a certain kind"; and **totality/continuity** set up the encoding problem Chapter 3 has to solve to talk about Turing machines (inherently partial, potentially non-halting) inside a theory where every function must be total.

**Connection to the standing project:** the judgment/proposition split here is the direct ancestor of the type-checking/proof-checking split your compiler needs — "is this term well-typed" (judgment 1, syntactic) has to be answered *before* "does this term prove the refinement obligation" (a genuinely propositional question, handled by the next article's Curry-Howard machinery) is even askable. And the universe hierarchy is not optional scaffolding to skip past — any elaborator with polymorphic types (generics, or dependent-type-level computation) needs a working universe-level unifier, modeled closely on what Lean's kernel already does.
