---
title: Declarative Semantics of Definite Programs
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 2, §6 (pp. 35–40)
tags: [least-herbrand-model, immediate-consequence-operator, correct-answer, denotational-semantics]
---

[[book-guidelines|↩ Back to guidelines]]

## What is the "meaning" of a program, before you run it?

Every language needs a semantics independent of its evaluator — a specification of *what a program computes* against which the evaluator can be judged correct. For an imperative language this is usually a denotational function from states to states; for a definite logic program, Lloyd's answer is: **the set of all ground facts that logically follow from it** — its **least Herbrand model**. This article is the "what does this program mean" half of the story; [[SLD-Resolution]] is the "how do we compute it via search" half, and the pairing is proved sound and complete.

This declarative/procedural split is exactly the split between a language's **static/dynamic semantics specification** and its **type-checking/interpretation algorithm**. Get the specification right first, independent of any particular search strategy, and you get a stable target against which to prove the algorithm correct — this is precisely why Lloyd proves everything about $T_P$ and $M_P$ *before* ever defining SLD-resolution.

## The least Herbrand model, two ways

**Model-theoretically:** among all Herbrand interpretations (subsets of $B_P$, per [[First-Order-Logic-as-a-Foundation-for-Logic-Programming]]) that are models of $P$, take their intersection. The **Model Intersection Property** (Proposition 6.1) guarantees this intersection is *itself* a model — this is not automatic for arbitrary sets of formulas (it fails the moment you allow disjunction or negation freely, which is exactly why chapter 3's negation theory needs the extra machinery of *stratification*), but it holds for definite (Horn) clauses because a Horn clause has at most one positive literal, so "true in every $M_i$" propagates through conjunction cleanly. Call this intersection $M_P$, the **least Herbrand model**.

**Proof-theoretically (Theorem 6.2, van Emden–Kowalski):** $M_P = \{A \in B_P : A \text{ is a logical consequence of } P\}$. The proof is a one-line chain of the equivalences from [[First-Order-Logic-as-a-Foundation-for-Logic-Programming]] (Proposition 3.1, Herbrand-model restriction for clause sets):
$$A \text{ log. consequence of } P \iff P \cup \{\lnot A\} \text{ unsatisfiable} \iff \lnot A \text{ false in every Herbrand model of } P \iff A \in M_P.$$

This is the crux identity: **the model-theoretic object (smallest model) and the proof-theoretic object (everything provable) coincide.** It's the same phenomenon as a type system's soundness+completeness relative to a denotational semantics — "everything the type checker accepts is semantically well-behaved, and everything semantically well-behaved is accepted" — except here the "type checker" hasn't even been defined yet (that's SLD-resolution). This theorem alone already tells you *what a correct implementation must compute*, before you've committed to *how*.

## $T_P$: the immediate-consequence operator

To make $M_P$ *computable* rather than merely *defined*, Lloyd introduces the operator from [[Fixpoint-Theory]] specialized to $B_P$:

$$T_P(I) = \{A \in B_P : A \leftarrow A_1,\ldots,A_n \text{ is a ground instance of a clause in } P \text{ and } \{A_1,\ldots,A_n\} \subseteq I\}$$

— "one step of forward-chaining": given the facts you currently believe ($I$), what new facts do the program's rules immediately license? $T_P$ is **continuous** (Proposition 6.3, using exactly the directed-set characterization from [[Fixpoint-Theory]]), and Herbrand interpretations that are models are exactly the *pre-fixpoints* of $T_P$: $I$ is a model of $P$ iff $T_P(I) \subseteq I$ (Proposition 6.4) — a model is a set of facts *closed under* one-step forward chaining.

The **Fixpoint Characterisation Theorem (6.5)** then assembles the whole chapter's machinery into one line:

$$M_P = \mathrm{lfp}(T_P) = T_P{\uparrow}\omega$$

By Kleene's theorem ([[Fixpoint-Theory]]), this is not just an existence statement — it says $M_P$ is literally the union of $T_P{\uparrow}0 = \varnothing,\ T_P{\uparrow}1,\ T_P{\uparrow}2,\ldots$: **semi-naive bottom-up evaluation**, iterating forward-chaining from nothing until no new facts appear (at $\omega$ if infinitely many iterations are needed). If you've implemented a Datalog engine or a CHC (constrained Horn clause) fixpoint solver, this theorem is *exactly* what your evaluation loop is computing, with $T_P$ as the one-step-derivation function.

**Watch the $\mathrm{lfp}/\mathrm{gfp}$ asymmetry carefully** — Lloyd flags it immediately with a worked example: for `p(f(x)) :- p(x). q(a) :- p(x).`, $T_P{\downarrow}\omega = \{q(a)\}$ but $\mathrm{gfp}(T_P) = \varnothing$ (in fact $\mathrm{gfp}(T_P) = T_P{\downarrow}(\omega{+}1)$). This is the *first* place the book demonstrates that greatest fixpoints of $T_P$ don't behave as nicely as least fixpoints — a fact whose full resolution (via compactness of an *infinite*-term Herbrand universe) is deferred all the way to chapter 6 ([[Semantics-of-Perpetual-Processes]]).

## Correct answers: the declarative target for a query result

A goal $\leftarrow B_1,\ldots,B_n$ asks a program a question; an **answer** is a substitution $\theta$ for the goal's variables. $\theta$ is **correct** if $\forall(( B_1 \land \cdots \land B_n)\theta)$ is a logical consequence of $P$ — the declarative specification of "this is a right answer," defined *before any resolution procedure exists to compute it*. [[SLD-Resolution]] will define **computed answer** procedurally and prove the two notions coincide (soundness: every computed answer is correct; completeness: every correct answer is subsumed by some computed answer).

**A subtlety worth internalizing precisely** (Lloyd flags it with a sharp counterexample): you might expect "$\theta$ correct" to reduce cleanly to "$\forall((B_1\land\cdots\land B_n)\theta)$ true in $M_P$" — but this equivalence needs $(B_1\land\cdots\land B_n)\theta$ to be **ground**. If the goal has variables left unbound by $\theta$ (e.g. goal $\leftarrow p(x)$, $\theta = \varepsilon$, program `p(a) :-`), $\forall x\, p(x)$ can be *true in* $M_P$ (vacuously false here, but the general risk is real) without being a *logical consequence* of $P$ — because $\lnot \forall x\, p(x)$ is not a clause, so the Herbrand-restriction theorem (Proposition 3.1/3.3) doesn't apply to it. Theorem 6.6 gives the correct, careful statement: for **ground** instantiations, correctness, "true in every Herbrand model," and "true in $M_P$" all coincide. This is a small technical point with a large moral: **be careful conflating "true in the free/canonical model" with "provable," the moment quantifier alternation or non-ground reasoning enters** — exactly the discipline a bidirectional type checker needs when deciding whether a metavariable-containing goal is "solved" versus merely "consistent with the current model."

## Grounding

```rust
// T_P as a one-step forward-chaining closure — this is the evaluation
// core of a bottom-up Datalog / CHC least-fixpoint solver.
use std::collections::HashSet;

#[derive(Clone, Eq, PartialEq, Hash)]
struct GroundAtom(String, Vec<String>);

struct Clause {
    head: GroundAtom,             // for a *ground instance*; in practice
    body: Vec<GroundAtom>,        // you'd unify against non-ground clauses.
}

fn t_p(interp: &HashSet<GroundAtom>, clauses: &[Clause]) -> HashSet<GroundAtom> {
    clauses.iter()
        .filter(|c| c.body.iter().all(|b| interp.contains(b)))
        .map(|c| c.head.clone())
        .collect()
}

// Kleene iteration T_P↑0, T_P↑1, ... until a fixpoint — this loop's
// termination at some finite n (or omega, for infinite Herbrand bases)
// is exactly Theorem 6.5 + Kleene's theorem from Fixpoint Theory.
fn least_herbrand_model(clauses: &[Clause]) -> HashSet<GroundAtom> {
    let mut interp = HashSet::new();
    loop {
        let next: HashSet<_> = interp.union(&t_p(&interp, clauses)).cloned().collect();
        if next == interp { return interp; }
        interp = next;
    }
}
```

**In Lean**, the least Herbrand model is the "canonical" or "free" model construction you'd use to prove a set of Horn-clause axioms consistent — it's the model built purely from provability, with no outside interpretation imposed, and it plays the same role a term model plays in a completeness-theorem proof (build the canonical model out of the syntax itself, show it satisfies exactly what's provable). This construction pattern — *interpret the domain as the syntax itself, then show provability = truth-in-this-model* — is the same one used to prove decidability/completeness results for fragments of your refinement-type system's verification-condition logic.

## Where this leads

- **This is the fixed point your Horn-clause/CHC solver computes.** In your verification pipeline, program semantics get encoded as Horn clauses (`ensures`/`requires` become clause heads and bodies over abstract predicates), and finding the strongest inductive invariant satisfying them is *literally* computing $\mathrm{lfp}(T_P)$ for a $T_P$ built over an abstract (not Herbrand) domain — this section, not some later abstract-interpretation-specific theory, is the precise mathematical content underneath "run a CHC solver."
- [[SLD-Resolution]] proves that SLD-resolution's **success set** ($\{A : P \cup \{\leftarrow A\} \text{ has a refutation}\}$) equals $M_P$ exactly — the procedural (search) and declarative (model) characterizations coincide, mirroring soundness+completeness of a type checker against its declarative typing judgment.
- The **correct answer** definition here is the direct ancestor of a verification condition's own "correct answer" — a substitution/instantiation is a valid witness for an existential VC iff it makes the VC a logical consequence of the background theory, exactly this section's definition lifted from Herbrand logic to whatever theory (linear arithmetic, arrays, etc.) your SMT backend reasons in.
