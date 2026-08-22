---
title: "Singleton and Dependent Kinds"
book: "Practical Foundations for Programming Languages (Robert Harper, 2012)"
chapter: "Chapter 24: Singleton Kinds"
pages: "227–237"
tags: [type-theory, kinds, singleton-kinds, dependent-types, module-systems, definitional-equality]
---

[[book-guidelines|↩ Back to guidelines]]

# Singleton and Dependent Kinds

## The problem: type abbreviation shouldn't be this hard

Start from something almost embarrassingly ordinary: `let x = e1 in e2`, binding a value to a variable. If you have function types, this is nothing special — it's just sugar for `(λ(x:τ) e2)(e1)`. Value-level `let` doesn't need to be a primitive; it falls out of what you already have.

So Harper asks the obvious next question: what about binding a *type* to a variable? Something like

$$\texttt{def } t \text{ is } \tau \text{ in } e$$

which should let you write `def t is nat × nat in λ(x:t) s(x·l)` — introduce an abbreviation `t` for `nat × nat`, then use `t` as if it *were* `nat × nat` inside `e`. This is exactly what a compiler's `type Point = (i32, i32)` or a Lean `abbrev`/`def` does at the type level: give a name to a type, then let the elaborator see through the name wherever it matters for typechecking.

The tempting guess: reuse polymorphism. If you already have System F-style type abstraction $\Lambda(t.e)$ and instantiation $e[\tau]$, define `def t is τ in e` as sugar for $\Lambda(t.e)[\tau]$ — bind `t` polymorphically, then instantiate it to `τ`.

**What breaks:** this gets the *[[Exceptions#Dynamics|dynamics]]* right (running the program does substitute `τ` for `t`) but gets the *[[Symbols-and-Dynamic-Binding#Statics|statics]]* wrong. Inside $\Lambda(t.e)$, the body `e` is typechecked knowing only that `t` has kind `T` (is *some* type) — it has no way to know `t` is *specifically* `nat × nat`. So `s(x·l)` — projecting the left component of something of type `t` and applying successor — fails to typecheck, because as far as the checker is concerned `t` could be any type at all, not specifically a pair of naturals. Polymorphism deliberately hides the identity of the instantiated type from the body; abbreviation needs the opposite — it needs the body to *know* the identity.

You could patch this by making `def...in` a new primitive construct with its own typing rule that substitutes eagerly:

$$\frac{\Gamma \vdash [\tau/t]e : \tau'}{\Gamma \vdash \texttt{def } t \text{ is } \tau \text{ in } e : \tau'}$$

This works, but it's ad hoc — a special-cased rule bolted onto the system rather than something that falls out of the type structure itself, violating the book's whole methodology of deriving language features from type/kind structure rather than inventing primitives to order.

## The real fix: make the *kind* carry the identity

Harper's move: instead of asking "how do we support abbreviations," ask "what kind structure would make abbreviations fall out for free?" Recall from Chapter 22 that constructors (types, and things that build types) are classified by **kinds** — `T` is the kind of all types, the way `nat` is the type of all natural numbers. Ordinarily, knowing `t :: T` tells you nothing about *which* type `t` is — kind `T` is maximally uninformative, just "some type."

The fix is a kind that *is* informative: the **singleton kind**.

$$S(\tau)$$

is the kind of constructors that are **definitionally equal to $\tau$**. Up to definitional equality, it has exactly one inhabitant — $\tau$ itself. So if you declare `u :: S(τ)`, then within `u`'s scope, `u` *is* `τ`, indistinguishably, for typechecking purposes. Now `def t is τ in e` can be represented as

$$\Lambda(t{::}S(\tau).\,e)[\tau]$$

— polymorphic abstraction, but over a kind that pins the bound variable's identity down to exactly `τ`. The body `e` typechecks knowing `t :: S(τ)`, which is enough to know `t ≡ τ`, so `s(x·l)` typechecks fine. Type abbreviation isn't a new primitive — it's ordinary polymorphism instantiated at a more precise kind. This is the payoff of the "no primitives without a type-structural justification" discipline that runs through the whole book.

If you've used Lean, TypeScript's `type` aliases, or Rust's `type Alias = Foo;`, you've used a system doing informal versions of exactly this — a name that the checker treats as fully transparent. Singleton kinds are the formal account of *why* that's sound: the alias lives at a kind (or its type-level analogue) that says "this identifier, definitionally, is that thing."

## Making singletons behave: subkinding

There's an immediate wrinkle. If `u :: S(τ)`, can you actually *use* `u` as a type — write `x : u` somewhere? A constructor of kind `S(τ)` had better also count as a constructor of kind `T` (a type), or singleton kinds would be useless: you could prove `u` is synonymous with `τ`, but never actually apply that fact anywhere a type is expected.

Harper fixes this with a **subkinding** relation $\kappa_1 <: \kappa_2$ (note: the book writes it $\kappa_1 : \! < \! : \kappa_2$), directly analogous to [[Subtyping|subtyping]] but one level up, at kinds. The load-bearing axiom is:

$$S(\tau) <: \text{T}$$

*Every constructor of singleton kind is a type.* Combined with a subsumption rule ("if $c :: \kappa_1$ and $\kappa_1 <: \kappa_2$ then $c :: \kappa_2$"), this lets `u :: S(τ)` be used anywhere a `T`-classified type is expected. Subkinding is a preorder (reflexive, transitive) and respects kind equivalence — the same shape of structural properties as ordinary subtyping in Chapter 23, just lifted a level.

Two more rules complete the picture:
- **Self-recognition**: if $c :: \text{T}$, then $c :: S(c)$ — every type recognizes itself as inhabiting its own singleton. This is essentially reflexivity of definitional equality, packaged as a kinding fact.
- If $c :: S(d)$, then $c \equiv d :: \text{T}$ — anything living in `d`'s singleton kind really is (definitionally) `d`.

**What breaks without subkinding:** without $S(\tau) <: T$, singleton kinds would be an isolated, useless annex — you could form them and prove membership facts, but never actually deploy that knowledge where ordinary types are expected. Subkinding is what lets a singleton-kinded variable slot seamlessly into any type-level position.

A concrete payoff: existential types (Chapter 21) get sharper. $\exists u{::}S(c).\tau$ is the type of a package whose hidden representation type is *specifically* `c`, not just "some type" — this is precisely the ML-module notion of a "transparent" or "manifest" type component (`type t = int` in a signature, versus an opaque `type t`). And because $S(c) <: T$, you can always widen $\exists u{::}S(c).\tau <: \exists u{::}T.\tau$ — forget the exposed identity and treat the package abstractly, the same forgetting-of-information move ordinary subtyping performs elsewhere.

```rust
// Rust doesn't have singleton kinds, but the "transparent vs opaque"
// distinction is exactly the difference between a type alias and a
// newtype/opaque associated type:
type Point = (i32, i32);          // ~ u :: S((i32,i32)) — fully transparent
trait Repr { type T; }             // ~ u :: T            — fully opaque
// impl Repr { type T = Point; }   // caller only knows Self::T : T, not what it is
```

```lean
-- Lean's `abbrev` vs `def` mirrors this almost exactly.
-- `abbrev` unfolds during unification/typechecking — its identity is exposed,
-- like a variable of singleton kind:
abbrev Pair := Nat × Nat
-- `def` is semi-opaque by default (won't unfold eagerly during isDefEq
-- unless reducibility settings say otherwise) — closer to an ordinary `T`-kinded type.
def OpaquePair := Nat × Nat
```

## Why singletons force you to go dependent

Look again at rule (24.2a)-style formation: $S(\tau)$ is only well-formed given that $\tau$ is a well-formed *constructor* of kind `T`. That means the kind `S(τ)` mentions — depends on — an actual constructor, not just another kind. This is new: previously (Chapter 22), kinds like `T × T` or `T → T` were built purely from other kinds, with constructors living in a cleanly separate layer below. Singleton kinds punch a hole between the layers: a kind can now refer to a specific piece of constructor-level data.

Once kinds can depend on constructors, the ordinary product and function kinds are no longer expressive enough, and this is where the chapter's title cashes out: **dependent kinds**.

**What breaks without dependent kinds.** With only non-dependent product/function kinds you can express "the kind of a pair whose first component is `int` and second is *some* type": $S(\text{int}) \times \text{T}$. But you *cannot* express "the kind of a pair whose second component is equivalent to whatever the first component turns out to be" — there's no way for the second component's kind to *look at* the first component. Same story for functions: $T \to S(\text{int})$ says "any type in, `int` out," but you can't say "whatever type comes in, that same type goes out" — the identity function at the type level — because the result kind can't mention the argument.

The fix is to let the second component's kind (or a function's result kind) be a kind-valued function of the first component (or argument):

$$\Sigma\, u{::}\kappa_1.\,\kappa_2 \qquad \Pi\, u{::}\kappa_1.\,\kappa_2$$

- **Dependent product kind** $\Sigma\, u{::}\kappa_1.\,\kappa_2$ classifies pairs $\langle c_1, c_2\rangle$ where $c_1 :: \kappa_1$ and $c_2 :: [c_1/u]\kappa_2$ — the kind of the *second* component is obtained by substituting the actual *first component* (not just its kind) into $\kappa_2$.
- **Dependent function kind** $\Pi\, u{::}\kappa_1.\,\kappa_2$ classifies functions $c$ such that applying $c$ to any $c_1 :: \kappa_1$ yields a result of kind $[c_1/u]\kappa_2$ — the *result's* kind depends on the actual argument supplied.

When there's no real dependency, these degenerate to the familiar non-dependent kinds: $\kappa_1 \times \kappa_2 := \Sigma\, \_{::}\kappa_1.\kappa_2$ and $\kappa_1 \to \kappa_2 := \Pi\, \_{::}\kappa_1.\kappa_2$ (blank/irrelevant bound variable).

Now the earlier gaps are fillable. The "pair whose second component matches the first" kind is $\Sigma\, u{::}\text{T}.\,S(u)$ — pairs $\langle c,c\rangle$ (up to equivalence). The "type-level identity function" kind is $\Pi\, u{::}\text{T}.\,S(u)$ — apply it to any `c`, get back something equivalent to `c`. You can even write a "swap" kind, $\Pi\, u{::}\text{T}\times\text{T}.\,S(u{\cdot}r)\times S(u{\cdot}l)$, precisely pinning down a constructor-level function that swaps a pair of types.

This is the exact mechanism a dependently-typed kernel calls **type-dependency**: `Πu:κ1.κ2` is a Pi-type/Pi-kind at the level of kinds, and it behaves under substitution exactly like the `Π` you already know from term-level dependent function types.

```lean
-- The dependent function KIND Π u::κ1.κ2 is one level up from Lean's ordinary
-- dependent function TYPE, but the substitution behavior is identical in shape:
-- applying `f : (a : α) → β a` to `x` gives something of type `β x` —
-- the codomain is *computed from the actual argument*, not just its type.
def idAt : (α : Type) → α → α := fun α x => x
-- Πu::T.S(u) is the kind-level analogue: "given a type u, produce
-- something *equivalent to u itself*" — u's IDENTITY threads through,
-- not just its classification as "a type."
```

Subkinding extends naturally, with the expected variances (mirroring the term-level function subtyping of Chapter 23):

$$\frac{\Delta \vdash \kappa_1 <: \kappa_1' \quad \Delta, u{::}\kappa_1 \vdash \kappa_2 <: \kappa_2'}{\Delta \vdash \Sigma\, u{::}\kappa_1.\kappa_2 <: \Sigma\, u{::}\kappa_1'.\kappa_2'} \qquad \Sigma \text{ covariant in both}$$

$$\frac{\Delta \vdash \kappa_1' <: \kappa_1 \quad \Delta, u{::}\kappa_1' \vdash \kappa_2 <: \kappa_2'}{\Delta \vdash \Pi\, u{::}\kappa_1.\kappa_2 <: \Pi\, u{::}\kappa_1'.\kappa_2'} \qquad \Pi \text{ contravariant in domain, covariant in range}$$

giving concrete facts like $\Sigma\,u{::}S(\text{int}).S(u) \equiv S(\text{int}) \times S(\text{int})$ (sharing propagates into the kind once you know the first component exactly), and $\Pi\,u{::}\text{T}.S(u) <: S(\text{int}) \to S(\text{int})$ (the identity-kind function, in particular, maps `int` to `int`).

**Extensionality.** Two more principles make $\Sigma$/$\Pi$ behave like honest products/functions rather than opaque boxes:

$$\Delta \vdash c :: \Sigma\,u{::}\kappa_1.\kappa_2 \implies \Delta \vdash c \equiv \langle c{\cdot}l, c{\cdot}r\rangle :: \Sigma\,u{::}\kappa_1.\kappa_2$$
$$\Delta \vdash c :: \Pi\,u{::}\kappa_1.\kappa_2 \implies \Delta \vdash c \equiv \lambda(u{::}\kappa_1)\,c[u] :: \Pi\,u{::}\kappa_1.\kappa_2$$

*Every* constructor of a $\Sigma$-kind is equivalent to the pair of its own projections; *every* constructor of a $\Pi$-kind is equivalent to the eta-expansion of applying it. These are eta-laws for kinds — the same principle a bidirectional elaborator applies when it eta-expands a metavariable of function type to make unification syntax-directed.

## Higher singletons: pinning down constructors of any kind

$S(\tau)$ as originally stated only makes sense for `τ` of kind `T`. But nothing about "the kind of things definitionally equal to `c`" is specific to types — you'd like a singleton for a constructor of *any* kind, including the $\Sigma$/$\Pi$ kinds just introduced. That's the higher singleton:

$$S(c{::}\kappa)$$

Rather than adding new primitive machinery, Harper *defines* $S(c::\kappa)$ by induction on the structure of $\kappa$, using exactly the $\Sigma$/$\Pi$ machinery already in hand — this is the chapter's payoff move: singletons at every kind fall out of singletons-at-T plus dependent kinds, nothing more is needed.

- Base case, $\kappa = T$: $S(c::T) := S(c)$, the ordinary singleton.
- Pair case, $\kappa = \kappa_1 \times \kappa_2$: given $c :: \kappa_1 \times \kappa_2$, extensionality says $c \equiv \langle c{\cdot}l, c{\cdot}r\rangle$. So define

$$S(c :: \kappa_1 \times \kappa_2) := S(c{\cdot}l :: \kappa_1) \times S(c{\cdot}r :: \kappa_2)$$

  — the kind of pairs whose left half matches $c$'s left half and whose right half matches $c$'s right half.
- Function case, $\kappa = \kappa_1 \to \kappa_2$: given $c :: \kappa_1 \to \kappa_2$, extensionality says $c \equiv \lambda(u{::}\kappa_1)\,c[u]$. So define

$$S(c :: \Pi\, u{::}\kappa_1.\kappa_2) := \Pi\, u{::}\kappa_1.\, S(c[u] :: \kappa_2)$$

  — the kind of functions that, applied to any argument $u$, produce something matching what $c$ itself would produce on that argument.

Both clauses are the same trick: use eta to decompose $c$ into its constituent behavior, then recursively demand equivalence at each constituent, one kind-level lower — genuine structural recursion on the kind, terminating because $\kappa$ strictly shrinks at each step.

This needs matching **self-recognition rules** at $\Sigma$ and $\Pi$ (generalizing the base self-recognition axiom $c::T \Rightarrow c::S(c)$):

$$\frac{\Delta \vdash c{\cdot}l :: \kappa_1 \quad \Delta \vdash c{\cdot}r :: [c{\cdot}l/u]\kappa_2}{\Delta \vdash c :: \Sigma\,u{::}\kappa_1.\kappa_2} \qquad \frac{\Delta, u{::}\kappa_1 \vdash c[u] :: \kappa_2}{\Delta \vdash c :: \Pi\,u{::}\kappa_1.\kappa_2}$$

and the reward is the theorem the whole chapter has been building toward:

> **Theorem 24.1.** If $\Delta \vdash c :: \kappa$, then $\Delta \vdash S(c{::}\kappa) <: \kappa$ and $\Delta \vdash c :: S(c{::}\kappa)$.

Every well-formed constructor, of *any* kind, has a *most precise* kind — its own higher singleton — which both (a) is a subkind of its original classification, and (b) it genuinely inhabits. In other words: nothing escapes precise classification. Any constructor, no matter how it's built, can be assigned a kind that pins down its definitional-equality class exactly. (Harper notes the proof is "surprisingly intricate" and defers to Stone and Harper's original paper — worth flagging honestly rather than hand-waving a claim the source itself calls non-trivial.)

## What breaks without any of this

Concretely: without singleton/dependent kinds, a module system has no clean way to express *sharing* — the ML-style situation where two abstract type components from different modules must be pinned to be the *same* type, or where a signature must expose that `type t = int` rather than leaving `t` fully opaque. Harper flags this explicitly: singleton kinds were invented by Stone and Harper (2006) specifically to formalize *type sharing* in the ML module system, and the book returns to this machinery in force in Chapters 45–46 (modules, signatures, functors) — see also Topic 34 in this book's own list, "Type classes as transparent constraints via singleton kinds."

## Where this leads

This chapter is the technical backbone under the book's treatment of ML-style modules: a signature component `type t = τ` *is* a singleton-kinded declaration `t :: S(τ)`, and an opaque component `type t` *is* an ordinary `t :: T`. Sealing a module (choosing which parts of its interface stay transparent vs. become abstract) becomes a subkinding move: quietly widening from `S(τ)` up to `T` along $S(\tau) <: T$ exactly forgets the identity information, which is precisely what abstraction requires.

**On the elaborator/unifier target**: this chapter is directly load-bearing. Self-recognition ($c :: S(c)$) is definitional equality doing double duty as a *classification* fact, not just an equivalence fact — this is close in spirit to how a bidirectional elaborator's `isDefEq` gets invoked not just to check two terms match, but to justify that a metavariable or local can stand in for a specific solution. And higher singletons — every constructor has a *most precise kind* determining it up to definitional equality — are the kind-level shadow of what a good unification algorithm wants at the term level: the tightest possible classification of "what this thing actually is," which is exactly the discipline Miller-pattern unification needs when deciding whether a metavariable's kind/type pins its solution down uniquely. If you build a module or signature layer for a Rust verifier that needs to track "this associated type is exactly `X`" vs. "this associated type is some opaque `Y`," singleton kinds are the formal vocabulary for that distinction — not an incidental one.
