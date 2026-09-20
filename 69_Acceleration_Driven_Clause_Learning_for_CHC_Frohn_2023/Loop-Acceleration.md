---
title: Loop Acceleration
source: "ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses (Frohn & Giesl, 2023)"
chapters: "Sect. 2 Preliminaries (pp. 5–6), Sect. 5 Related Work (pp. 20–21)"
tags: [acceleration, loop-closure, sat-smt-csp, static-analysis, invariant-generation, decidability]
---

[[book-guidelines|↩ Back to guidelines]]

## What problem acceleration actually solves

[[Constrained-Horn-Clauses-(CHCs)]] gave you the representation — a recursive rule like $\mathrm{Inv}(X_1,X_2)\wedge\psi \Rightarrow \mathrm{Inv}(X_1',X_2')$ stands for "one loop iteration." But a resolution proof that walks a loop 10000 times by resolving against that rule 10000 times is really just *interpreting the loop*, one step at a time, exactly the way a naive symbolic executor would. That's the failure mode acceleration exists to kill: **any technique whose cost scales with the loop's iteration count, rather than with its structural complexity, cannot scale to deep counterexamples.** If your invariant-generation or bug-finding pipeline needs 10000 iterations of unrolling to see a bug that only manifests on the 10000th step, unrolling has already lost before it starts.

The insight loop acceleration techniques exploit (originally developed for static program analysis, well before this paper repurposes them for resolution) is that a loop without internal branching is a single transition relation, and the *set of all states reachable after $N$ iterations, for every $N\ge 1$* is often expressible as a closed-form formula — no recursion, no fixpoint computation, just a formula with a free parameter $N$ ranging over the positive integers. Compute that formula once, and you've replaced "however many iterations the counterexample needs" with "one clause, plus one witness value for $N$."

## The formal contract: same ground instances, closed form

Definition 4 pins this down with the same semantic anchor as everything else in the paper — ground instances, not syntax:

$$\mathrm{accel}(\varphi) := \varphi' \text{ such that } \mathrm{grnd}(\varphi') = \bigcup_{n \in \mathbb{N}_{\ge 1}} \mathrm{grnd}(\varphi^n)$$

Read $\varphi^n$ as "the sequence consisting of $n$ back-to-back copies of $\varphi$" (so $\mathrm{grnd}(\varphi^n)$, via resolution's lifting to sequences, is the set of ground facts reachable by exactly $n$ iterations). The definition says: an acceleration technique is *any* function producing a new recursive conjunctive CHC $\varphi'$ whose ground instances are the union over **every** possible iteration count — one clause standing in for an unbounded family. Crucially, `accel` is a *contract*, not an algorithm: the paper never commits to one specific procedure. Any black-box function satisfying this ground-instance equality is a legal plug-in, which is exactly why Section 4 ([[Implementing-ADCL-in-LoAT]]) can treat acceleration as an oracle and swap in whatever concrete technique the target theory supports.

Two restrictions are baked into the domain of `accel`, and both matter for what comes later:

- **Recursive** — you can only accelerate a rule where the head and body predicate coincide ($F=G$). This is the syntactic signature of "this is a loop," and it's the only shape a self-composing transition relation can take.
- **Conjunctive** — the constraint $\psi$ must be a plain conjunction of literals, not a general Boolean formula. Most acceleration algorithms are built around a single deterministic-looking transition relation; disjunctions inside $\psi$ effectively encode *multiple different transitions*, which most acceleration machinery either can't handle or can only approximate. This is precisely why [[Syntactic-Implicants-and-Redundancy]]'s syntactic implicant projection exists in this pipeline at all — it's the mechanism that turns a disjunctive CHC into a finite set of conjunctive ones *before* acceleration ever sees it.

Applied to the paper's running example (see [[Constrained-Horn-Clauses-(CHCs)]] for the full setup), the rule
$$\mathrm{Inv}(X_1,X_2) \wedge X_1 < 5000 \Rightarrow \mathrm{Inv}(X_1+1, X_2)$$
accelerates to
$$\mathrm{Inv}(X_1,X_2) \wedge N>0 \wedge X_1+N < 5001 \Rightarrow \mathrm{Inv}(X_1+N, X_2)$$
— a fresh, existentially-flavored (but syntactically universal, per CHC convention) variable $N$ now carries "how many times" as data inside the clause, rather than as a meta-level iteration count in a proof. That's the entire trick: **turn a proof-length parameter into a term-level variable.**

## Why most theories resist this: the $N \cdot Y$ wall

The paper is upfront that acceleration is not free, illustrating it with a second, deliberately simpler loop:

$$F(X,Y) \Rightarrow F(X+Y,Y) \quad\longrightarrow\quad F(X,Y)\wedge N>0 \Rightarrow F(X+N\cdot Y, Y)$$

The accelerated clause needs $N\cdot Y$ — a product of two *variables*. Linear (integer/real) arithmetic, by definition, only allows a variable to be multiplied by a numeral constant, not by another variable. So the very act of accelerating pushed the formula outside the theory it started in. This is the acceleration analogue of a type system rejecting a term that's semantically fine but syntactically outside the fragment it can express — the *meaning* ("after $N$ steps, $X$ has grown by $N$ copies of $Y$") is perfectly well-defined, but the *decidable theory* $A$ you committed to for constraint-solving can't say it.

**What breaks without acknowledging this:** if you naively assumed every recursive CHC could be accelerated within its starting theory, you'd build a solver that either silently produces unsound closed forms or gets stuck. The paper's actual response is architectural, not just a caveat: it commits to **many-sorted first-order logic**, keeping the door open to switch theories mid-derivation (e.g. into nonlinear or Presburger-adjacent fragments) when acceleration demands it, and it requires an extra sort for $N$'s own range whenever the background theory has no native integer sort. In implementation terms (see [[Implementing-ADCL-in-LoAT]]), this is also *why* the abstract `accel` oracle is explicitly allowed to be incomplete — sometimes there's no legal accelerated formula in any theory the solver actually supports, and the calculus has to degrade gracefully (fall back to ordinary Step resolution) rather than assume acceleration always succeeds.

## The landscape of concrete acceleration techniques

The related-work discussion (Sect. 5) surveys what's actually implementable, and it splits into two philosophically different families:

**1. Decidable acceleration classes** — syntactic restrictions on the loop's transition relation guaranteeing the closed form stays inside a decidable theory (typically still linear arithmetic, sometimes with quantifier elimination). The named classes:

| Class | What it restricts | Buys you |
|---|---|---|
| **Difference Bounds** | updates of the shape $x' \le y + c$ (a single difference bounded by a constant) | exact closed form, stays in a decidable fragment |
| **Octagons** | updates of the shape $\pm x \pm y \le c$ | slightly richer than difference bounds, still decidable |
| **Finite Monoid Affine Relations** | affine updates whose iterated matrix powers stabilize into a finite monoid | exact closed form for a broad class of affine loops |
| **Vector Addition Systems with States (VASS)** | updates that only add/subtract fixed vectors, gated by states | decidable reachability and closed-form iteration, a classical automata-theoretic result, later extended to systems over the rationals |

The unifying theme: each of these classes is a **syntactic fragment identified in advance** as one where the transitive closure is *provably* expressible in a decidable theory — you get soundness and (within the fragment) completeness, at the cost of only working when the loop happens to fit the fragment.

**2. Monotonicity-based techniques** — an "orthogonal line of research" that gives up the decidability guarantee in exchange for generality: these apply to loops whose transitive closure is *not* definable in linear arithmetic at all (the $N\cdot Y$ problem above is exactly the kind of case a decidable-class technique would simply refuse). The tradeoff is explicit in the paper's own words — "fewer theoretical guarantees in terms of completeness and whether the result can be expressed in a decidable logic" — this is the acceleration equivalent of choosing an abstract-interpretation domain: precise-but-narrow (the decidable classes) vs. general-but-approximate (monotonicity-based). LoAT's own Boolean-variable acceleration (Sect. 4/5) is a direct instance of this second family — it only ever applies the theory-agnostic "monotonic increase" / "monotonic decrease" operators from prior work, deliberately avoiding a known over-approximating technique because ADCL's soundness requires *exact* ground-instance equality, not an over-approximation.

That last point is worth dwelling on, because it's easy to conflate acceleration with abstract interpretation and miss the distinction: **an abstract interpreter is allowed to over-approximate** (that's the whole point of a sound-for-safety analysis); **`accel` as defined here is not** — Definition 4 demands *exact* equality of ground-instance sets, because ADCL's soundness proof needs the accelerated clause to be truly redundant-equivalent to unbounded resolution, not merely an over-approximation of it. This is why the paper is careful to say LoAT "cannot use" a known over-approximating Boolean-acceleration technique from prior work, even though it would have been the more general option — over-approximation would silently make ADCL unsound.

```rust
// The `accel` contract as a trait: implementors are free to fail (return None)
// rather than produce anything unsound, but must never over-approximate.
trait Accelerate {
    // φ must be a recursive, conjunctive CHC. Returns a recursive conjunctive
    // CHC φ' with grnd(φ') == ⋃_{n≥1} grnd(φ^n), or None if this theory/shape
    // isn't in this technique's supported fragment.
    fn accelerate(&self, phi: &RecursiveConjunctiveChc) -> Option<Chc>;
}

struct DifferenceBounds;   // decidable class: exact, but only for this syntactic fragment
struct Vass;               // decidable class: exact, via automata-theoretic closure
struct MonotonicIncrease;  // monotonicity-based: broader domain, weaker guarantees
```

A dispatcher over several `Accelerate` impls, tried in some priority order, is essentially how LoAT's real acceleration layer has to be structured — decidable classes tried first because they're exact and cheap when applicable, monotonicity-based techniques as fallback for what the decidable classes reject.

## Where this leads

Loop acceleration is the mechanism; [[The-ADCL-Calculus]]'s **Accelerate rule** is where it gets embedded into a proof search — replacing an entire recursive suffix of the resolution trace with a single accelerated clause, and (per the calculus's soundness argument) collapsing the corresponding blocking-clause history along with it. [[Metatheoretic-Properties-of-ADCL]]'s refutational-completeness proof and its non-termination result both hinge on properties of `accel` established here (exactness, domain restriction to recursive-conjunctive clauses). And [[Implementing-ADCL-in-LoAT]] is the story of what happens when `accel` is realized as a real, necessarily incomplete oracle instead of the idealized total function this section defines.

For the standing project: this is close to the closest thing in the paper to a **ready-made invariant-generation primitive** for the compiler's abstract interpreter (`static-analysis`) — accelerating a loop body *is* computing an inductive loop invariant, without needing a separate widening/narrowing fixpoint iteration, whenever the loop happens to fall into a supported class. The decidable-vs-monotonicity split is also a direct preview of the tradeoff your CSP kernel's domain propagation will face (`sat-smt-csp`): exact-but-narrow decidable fragments (Difference Bounds, Octagons — both classical *abstract-lattice* shapes) vs. general-but-approximate techniques, mirroring the Galois-connection tradeoff between precision and decidability that abstract interpretation formalizes.
