---
title: The Coq Proof Assistant
source: A HoTT Approach to Computational Effects (Wells, 2019)
chapter: "4: The Coq Proof Assistant"
pages: "47–54"
tags: [coq, inductive-types, proof-assistant, tactics, records, hott-coq]
---

[[book-guidelines|↩ Back to guidelines]]

## Why the thesis needs a proof assistant at all

Everything in [[Foundations-of-Homotopy-Type-Theory|the earlier HoTT articles]] was informal, hand-written mathematics — real, but unchecked by any machine. **Coq**, a formal proof assistant and programming language dating to 1984 and built on Thierry Coquand's calculus of constructions, is the vehicle the thesis uses to turn that informal HoTT into something machine-verified. This chapter is deliberately narrow in scope: not a Coq tutorial, just enough vocabulary — inductive types, basic tactic proofs, record types, function definitions — to read the Coq code that appears later, especially Chapter 5's action-type formalization and Appendix A's Turing machine implementation. If you've written Lean or Agda, most of this will feel like a change of surface syntax over identical ideas; if you haven't, this is a genuinely good on-ramp because Coq's tactic style makes the "which piece of the proof am I building right now" bookkeeping unusually explicit.

## Inductive types: the `Inductive` keyword, worked via `nat`

An **inductive type** definition begins with the `Inductive` keyword, an identifier, and a list of constructors. The book's running example is the natural numbers:

```coq
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
```

Three things worth being precise about:

1. `nat : Set` — `Set` is Coq's name for the **smallest universe of types** (directly the $\mathcal{U}_0$ from [[Foundations-of-Homotopy-Type-Theory|the universe hierarchy article]] — same concept, Coq's own name for it).
2. Two constructors: `O : nat` (zero, the base case) and `S : nat -> nat` (successor — takes a `nat`, returns the next one). Every `nat` is either `O`, or `S` applied to some smaller `nat` — so `1` is `S O`, `3` is `S (S (S O))`, and so on; Coq lets you write decimal digits as sugar, but under the hood every large number really is a chain of nested successors.
3. **Coq automatically generates an induction principle and derived properties from the constructor list alone.** To prove any predicate $p$ holds for all `nat`, it suffices to prove $p$ holds for `O` and that $p$ is preserved by `S` — this is literally structural induction, generated for free from the shape of the type definition, not something you write by hand. Coq also guarantees **constructor distinctness**: `O` and `S _` are provably never equal, for *any* inductive type's constructors, automatically.

```rust
// The Rust analogue is an enum, minus the free induction principle —
// Rust gives you exhaustive match-checking, but proving a property
// holds for ALL Nat values by structural induction is something
// you'd write by hand, not something the compiler derives.
enum Nat {
    O,
    S(Box<Nat>),
}
```

```lean
-- Lean's own `Nat` is defined identically, and generates the same
-- automatic recursor (`Nat.rec`) — this is the SAME mechanism,
-- not an analogy. `induction n` in a Lean proof invokes exactly
-- this auto-derived principle.
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

## Basic proofs: tactics as an interactive proof-construction language

Coq proofs are written as sequences of **tactics** — commands that incrementally build a term of the goal type, rather than requiring you to write the whole proof term by hand. The book's simplest example:

```coq
Theorem FourIsFour : 4 = 4.
Proof.
  reflexivity.
Qed.
```

`Theorem` names a proposition; `Proof` opens tactic mode; `reflexivity` discharges the goal by [[Propositions-as-Types|the identity type's]] own reflexivity principle (`refl`); `Qed` seals the constructed proof term under that name. A slightly richer example, proving $A \times B \to A$:

```coq
Theorem AxBImpliesA : forall A B : Type, (A * B) -> A.
Proof.
  intros A B p.
  exact (fst p).
Qed.
```

This is worth reading tactic-by-tactic against its type-theoretic meaning, because the correspondence is exact, not loose:

- `forall A B : Type, (A * B) -> A` **is** $\prod_{A,B:\mathcal{U}} (A \times B) \to A$ — `forall` is Coq's spelling of $\Pi$, and `Type` is Coq's spelling of $\mathcal{U}$, exactly as introduced in the [[Type-Formers|type formers article]].
- `intros A B p` introduces three hypotheses into context: the types $A$, $B$, and an element $p : A \times B$ — the tactic-mode equivalent of writing "assume types $A, B$, and $p : A \times B$" in informal prose.
- `exact (fst p)` supplies the actual proof term directly: `fst p` projects the first component out of the pair `p`, which — since `p : A * B` — has exactly type $A$, the goal.

**The full English proof the book gives:** assume $A, B$ and $p : A \times B$; such a $p$ has the form $(a, b)$ for $a : A, b : B$, so we obtain $a : A$; therefore $A \times B$ implies $A$. Every tactic line above is a direct transliteration of one clause of that sentence.

```lean
-- The identical proof in Lean, for direct comparison:
theorem AxBImpliesA (A B : Type) (p : A × B) : A :=
  p.1
```

## Records: dependent sums, packaged more conveniently

$\Sigma$-types can, in principle, be constructed via raw induction — but doing so for anything beyond a bare pair gets tedious fast, especially once a component needs to carry a *proof obligation* alongside a value. **Record types** are Coq's convenience macro for exactly this: a labeled dependent sum. The book's worked example constructs the rationals:

```coq
Record rat : Set := {
    p : nat
  ; q : nat
  ; not_zero : (gt q 0)
}.
```

This is a $\Sigma$-type in disguise: a rational number is a numerator `p`, a denominator `q`, and — the genuinely dependent-typed part — a **proof** `not_zero : gt q 0` that the denominator is actually nonzero, bundled *into the value itself*. Note what this buys you over an ordinary pair-of-integers representation: it's **impossible to construct an ill-formed rational** — you cannot produce a `rat` with a zero denominator, because doing so requires supplying a proof term that doesn't exist. This is refinement typing, made completely concrete: $\mathrm{rat} :\equiv \sum_{p:\mathbb{N}}\sum_{q:\mathbb{N}} (q > 0)$.

(Practical detail the book flags: negative rationals aren't represented directly — instead, non-negative rationals stand in for the full set, since the negative and non-negative cases can be proven to correspond, and rationals that reduce to one another can be shown equivalent, even without that equivalence being baked into the definition itself.)

To build a specific rational — $\frac{1}{3}$ — you first discharge the proof obligation, then supply everything to the auto-generated constructor:

```coq
Theorem ThreeGreaterThanZero : (gt (S (S (S O))) O).
(* provable in one line, by unfolding the definition of "3" and gt *)

Definition third := (Build_rat 1 3 ThreeGreaterThanZero).
```

`Build_<Identifier>` is Coq's automatically-generated record constructor — you never need to write it by hand unless you explicitly override it. Notice the discipline this enforces: **you cannot construct `third` without first producing `ThreeGreaterThanZero`**. The type system has made "well-formedness" a precondition of existence, not a runtime check.

```lean
-- Lean's structure is the same idea, verbatim:
structure Rat where
  p : Nat
  q : Nat
  not_zero : q > 0
```

## Functions: `Definition` and pattern matching

Ordinary function definitions use `Definition` plus a `match`/`end` block for case analysis — this is the concrete syntax underneath every sum-type computation rule from [[Type-Formers|the type formers article]]. The book's example, Boolean `and`:

```coq
Definition and (p q : bool) :=
  match p, q with
    | true, true   => true
    | true, false  => false
    | false, true  => false
    | false, false => false
  end.
```

The requirement worth flagging: **all four cases must be handled, or Coq rejects the definition outright** — the same exhaustiveness discipline Rust's `match` enforces on `enum`s, here enforced because `bool` is itself just the two-constructor inductive type $2 :\equiv 1+1$ from [[Type-Formers|the type formers article]], and a function over a sum type must, by that type's own computation rule, cover every constructor.

## HoTT in Coq: why the rest of the thesis needs a special library

Vanilla Coq's standard library assumes classical, extensional-flavored mathematics in places, and doesn't include the Univalence Axiom. The **HoTT library for Coq** re-implements much of the standard library on top of HoTT-specific foundations, adding Univalence and the HoTT-specific structures ([[Equivalence-and-Univalence|equivalences, quasi-inverses, and so on]]) directly. Every subsequent code listing in the thesis — Chapter 5's action types, Appendix A's Turing machine — assumes this library is installed and in scope; none of it runs against plain, unmodified Coq.

## Where this leads

This chapter is pure tooling setup, but every subsequent formalized result in the book depends on it directly: Chapter 5's `Action` type is a **Record**, built exactly the way the rationals were built here — fields for `bind`, `eval`, `transform`, plus a proof-carrying field for the eval-bind law, the same "package a proof obligation as a field" move as `not_zero` above. Appendix A's Turing machine and busy beaver are **Inductive** types (state sets, move directions) glued together with pattern-matching **Definitions**, exactly the vocabulary introduced here.

**Connection to the standing project:** Coq's record-as-refinement-type pattern (`not_zero : gt q 0` bundled into the constructor) is the most direct, ready-made template in the entire thesis for how your own Rust-based dependent/refinement-type compiler should represent refined values internally — a refinement type `{q : Nat | q > 0}` compiles most naturally to exactly this shape: a struct/record whose constructor demands a proof term, making ill-formed values unrepresentable rather than merely runtime-checked. And the auto-derived induction principle for `Inductive` types is the concrete, working example your elaborator's own **inductive-type-to-eliminator** pipeline needs to replicate — Coq is quietly demonstrating, in miniature, exactly the "generate a recursor from a constructor list" logic a trusted kernel has to implement from scratch.
