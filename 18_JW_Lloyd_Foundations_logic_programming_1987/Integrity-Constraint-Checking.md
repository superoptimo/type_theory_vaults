---
title: Integrity Constraint Checking
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 5, §24 (pp. 158–169)
tags: [integrity-constraints, incremental-verification, simplification-theorem, model-difference, transactions]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem: re-verifying everything after every change is too slow

[[Deductive-Database-Theory]] established that a database **satisfies** an integrity constraint $W$ if $W$ is a logical consequence of $\mathrm{comp}(D)$ — checkable, in principle, by running $\leftarrow W$ as a query and seeing whether it refutes (via [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies]]'s SLDNF machinery). The problem is *when*: naively, you'd re-run this full check after *every* update — every fact added or deleted — even though most of a large deductive database's derived consequences are completely unaffected by any one small change. This chapter is a genuinely elegant piece of engineering theory: it proves you only ever need to check finitely many **instances** of each constraint, computed from *only the rules that could possibly be affected*, not the (potentially huge) fact base. If you've ever designed an incremental type checker, an incremental build system, or a CHC solver that re-verifies only the invariants touched by a code diff, you already understand the *motivation*; this chapter gives you the actual *theorem*.

## Framing the problem: transactions and what changes between models

A **transaction** is a batch of deletions followed by additions, applied atomically — you only need to check integrity *once*, at the end, not after each intermediate step. Given databases $D \subset D'$ (or the general case via an intermediate $D''$ after deletions), the key question becomes: **what is the precise difference between a model of $\mathrm{comp}(D)$ and the corresponding model of $\mathrm{comp}(D')$?** For a pure relational (fact-only) database this is trivial — the difference is exactly the added/deleted facts. For a database with **rules**, adding one fact can ripple through recursive definitions and change arbitrarily many *derived* facts too (add one `mother/2` fact, and potentially infinitely many `ancestor/2` facts change). The chapter's central technical machinery — the sets $\mathrm{pos}_{D,D'}$ and $\mathrm{neg}_{D,D'}$ — is a **closed-form syntactic characterization of exactly that ripple**, computed *without ever touching the fact base*, using only the rules.

## Computing the ripple: $\mathrm{pos}_{D,D'}$ and $\mathrm{neg}_{D,D'}$

Defined by induction, mirroring $T_P$-style forward chaining but tracking *which atoms newly become derivable* ($\mathrm{pos}$) versus *which newly stop being derivable* ($\mathrm{neg}$) as you move from $D$ to $D'$:
$$\mathrm{pos}^1_{D,D'} = \{A : A \leftarrow \in D' \setminus D\}, \qquad \mathrm{neg}^1_{D,D'} = \varnothing$$
and at each further level, $\mathrm{pos}^{n+1}$ picks up new head instances whenever a positive body atom unifies with something already in $\mathrm{pos}^n$, *or* a negative body atom unifies with something in $\mathrm{neg}^n$ (sign-flipping through negation, exactly the connectivity-tracking idea from [[Declarative-Error-Diagnosis]] and [[Negation-in-Logic-Programs]]'s stratification level-checking) — and symmetrically for $\mathrm{neg}^{n+1}$. $\mathrm{pos}_{D,D'} = \bigcup_n \mathrm{pos}^n_{D,D'}$, similarly for $\mathrm{neg}$.

**Lemma 24.3/24.4 is the theorem that makes this worth computing**: for stratified databases, these syntactically-computed sets provably *bound* the actual model difference — given any model $M'$ of $\mathrm{comp}(D')$, there's a corresponding model $M$ of $\mathrm{comp}(D)$ with $M' \setminus M \subseteq \mathrm{pos}_{D,D'}$ and $M \setminus M' \subseteq \mathrm{neg}_{D,D'}$ (and conversely). The proof is a careful transfinite induction stratum-by-stratum, essentially re-running the stratified-fixpoint-construction argument from [[Negation-in-Logic-Programs]]/[[Fixpoint-Theory]], but tracking a *difference* between two fixpoint computations instead of computing one fixpoint in isolation — the technique of **relating two fixpoint iterations by simultaneous induction** is a genuinely reusable proof pattern anywhere you need to bound how much an inductively-defined set can change in response to a perturbation of its generators.

## The Simplification Theorem: the actual payoff

**Theorem 24.5** delivers the engineering result: for an integrity constraint $W = \forall \vec x\, W'$ (prenex form) and the transaction from $D$ to $D'$, define $\Theta$ (resp. $\Psi$) as the finite set of substitutions obtained by unifying $W'$'s negative-occurring atoms against $\mathrm{pos}_{D'',D'}$ and positive-occurring atoms against $\mathrm{neg}_{D'',D'}$ (resp. the reverse pairing). Then:

- **(a)** $D'$ satisfies $W$ **iff** $D'$ satisfies $\forall(W'\phi)$ for every $\phi \in \Theta \cup \Psi$ — an *exact* equivalence, not an approximation.
- **(b)/(c)** give the practically usable one-directional versions: if every simplified instance succeeds (SLDNF-refutes), $D'$ satisfies $W$; if any simplified instance finitely fails, $D'$ *violates* $W$.

The magic is what $\Theta \cup \Psi$ *doesn't* contain: **only finitely many instances, generated purely from unifying the constraint's own literals against the (typically small) rule-derived difference sets** — never touching the (potentially enormous) fact base directly, and never re-deriving the *entire* consequence set of either database from scratch. If $\Theta \cup \Psi$ turns out empty, the constraint is *provably* unaffected and can be skipped entirely; this is exactly a **frame condition** in the Hoare-logic sense — a syntactic, sound-by-construction argument that a given assertion is untouched by a given state change, computed without re-verifying the assertion from first principles.

## Making it terminate: stopping rules

The na\"ive definitions of $\mathrm{pos}_{D,D'}$/$\mathrm{neg}_{D,D'}$ are unions over $\omega$-many stages — potentially infinite. Lloyd gives a practical **stopping rule**: compute $P^n, N^n$ the same way, but *discard any atom that is an instance of an atom already computed at an earlier stage* (subsumption pruning); when both $P^n$ and $N^n$ come up empty two stages running, stop and use the accumulated union. The worked ancestor/`no_male_descendant` example shows this converging after 4 iterations to a small, finite $P, N$ — and Lloyd is honest that this rule doesn't always terminate finitely (his `p(f(X),Y) :- p(X,Y).` example generates an infinite chain of "independent" instances `p(a,b), p(f(a),b), p(f(f(a)),b),...`), offering a second stopping rule — **replace an infinite family of ground instances by one more-general instance of the offending clause's head** — as a heuristic patch, explicitly flagged as an area needing further research.

**This subsumption-based termination heuristic is exactly the widening-operator problem from [[Fixpoint-Theory]], reappearing in a different guise**: an ascending sequence that doesn't naturally stabilize in finitely many concrete steps is forced to stabilize by *generalizing* (replacing concrete elements with a covering abstraction) rather than by exact computation — precisely the same trade of exactness for termination that a widening operator makes in an abstract-interpretation fixpoint loop. Recognizing "subsumption-based pruning of a growing atom set" and "widening on an unstable abstract domain" as instances of the same underlying idea is a genuinely transferable insight for your own CSP/abstract-interpretation kernel design.

## Grounding: this is incremental verification-condition re-checking

```rust
// pos/neg difference sets as a change-impact analysis — this is precisely
// what an incremental verifier needs: given a diff to the program/database,
// compute which derived facts/invariants COULD have changed, without
// re-deriving everything from scratch.
struct DiffSets { pos: HashSet<GroundAtom>, neg: HashSet<GroundAtom> }

fn compute_ripple(old_clauses: &[Clause], added: &[Clause], removed: &[Clause]) -> DiffSets {
    let mut pos: HashSet<GroundAtom> = added.iter()
        .filter(|c| c.body.is_empty())
        .map(|c| c.head.clone())
        .collect();
    let mut neg: HashSet<GroundAtom> = removed.iter()
        .filter(|c| c.body.is_empty())
        .map(|c| c.head.clone())
        .collect();
    loop {
        let (new_pos, new_neg) = one_step_ripple(&pos, &neg, old_clauses);
        if new_pos.is_subset(&pos) && new_neg.is_subset(&neg) { break; }
        pos.extend(new_pos);
        neg.extend(new_neg);
        // TODO: subsumption pruning per the chapter's stopping rule,
        // else this loop may never terminate for recursive rule chains.
    }
    DiffSets { pos, neg }
}

// The simplification theorem's actual use: instead of re-checking every
// integrity constraint against the WHOLE new database, unify each
// constraint's literals against only the (small) ripple set.
fn constraints_to_recheck(constraints: &[Formula], ripple: &DiffSets) -> Vec<Formula> {
    constraints.iter()
        .filter_map(|w| simplify_against_ripple(w, ripple)) // None if untouched
        .collect()
}
```

**In Lean**, the closest analogue is **incremental elaboration / the compiler's own dependency tracking** — when a definition changes, Lean (and any serious proof assistant) must determine which *downstream* theorems' proofs are still valid without literally re-type-checking the entire library, by tracking which declarations' elaborated terms actually *depend on* the changed one. The "difference sets computed purely from the rules, never the fact base" strategy here is the specification-level analogue of what a build system's dependency graph gives you at the artifact level — and the frame-condition reading of $\Theta \cup \Psi = \varnothing$ ("this constraint is provably untouched") is exactly the guarantee a sound incremental type checker needs before it's allowed to skip re-checking a theorem after an unrelated change.

## Where this leads

- **Directly load-bearing for your compiler's incremental-verification story:** the pos/neg ripple-set construction is a template for computing *frame conditions* automatically — given a program diff, which previously-proved Hoare triples or refinement-type obligations are guaranteed untouched, syntactically, without re-running the full verifier. This is a genuinely reusable algorithm, not just an analogy.
- The stopping-rule discussion is a second, independent worked example (alongside [[Fixpoint-Theory]]'s abstract-interpretation connection) of the general "widen to force termination when exact fixpoint computation may not terminate" pattern — worth keeping both examples in mind as calibration points when you design your own CSP kernel's convergence heuristics.
- This is the last piece of database-specific theory in the book; [[Semantics-of-Perpetual-Processes]] pivots entirely away from databases back to the pure computational-semantics question the book opened with — what a *non-terminating* definite program computes.
