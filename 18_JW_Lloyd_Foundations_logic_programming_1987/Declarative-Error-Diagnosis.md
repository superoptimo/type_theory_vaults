---
title: Declarative Error Diagnosis
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 4, §19–20 (pp. 119–140)
tags: [algorithmic-debugging, oracle-based-debugging, error-diagnosis, soundness, completeness]
---

[[book-guidelines|↩ Back to guidelines]]

## Debugging without understanding the machine

Here is a genuinely striking idea, and Lloyd states it as an explicit design goal: build a debugger for logic programs that the programmer can use **knowing nothing whatsoever about the underlying execution mechanism** — no understanding of SLD-resolution's search order, no understanding of cuts, control annotations, or coroutining delays — armed *only* with their own intended meaning of the predicates involved. This is only possible *because* of the declarative/procedural separation the whole book has been building: if a program's meaning is genuinely independent of how it's executed (soundness/completeness theorems throughout chapters 2–4), then a bug — a discrepancy between "what the program computes" and "what the programmer intended" — must be locatable using *only* the declarative layer, without ever asking "what did the interpreter do." This is exactly the standard you want from a **proof-producing, trusted-kernel verifier**: the end user should be able to trust a counterexample or an error report without having to audit the solver's internal search heuristics.

## Formalizing "correct" and "bug"

An **intended interpretation** $I$ is simply what the programmer *means* — a (normal Herbrand) model the programmer has in mind for $\mathrm{comp}(P)$. $P$ is **correct wrt $I$** if $I$ actually is a model of $\mathrm{comp}(P)$; otherwise **incorrect**. Proposition 19.1/19.2 pins down the operational consequence precisely: if $P$ is correct wrt $I$, every computed answer is valid in $I$, and (using soundness of negation-as-failure) every finitely-failed query is genuinely unsatisfiable in $I$ — so a **wrong answer** or a **missing answer** (finite failure where the query should have succeeded) is *proof* that $P$ is incorrect wrt $I$. Note carefully what this *doesn't* catch: a program that's correct-but-incomplete (its least/greatest fixpoint doesn't compute everything true in $I$, cf. the $\mathrm{lfp} \ne \mathrm{gfp}$ gap from [[Fixpoint-Theory]]) has a real bug (missing coverage) that this framework is explicitly not designed to find — a scoping decision worth noting, since your own verifier will face the identical question of which bug classes a given diagnostic technique is and isn't equipped to catch.

The two atomic error categories (Proposition 19.3 shows these are *exhaustive* — any incorrectness reduces to one or the other):

- **Uncovered atom**: $A$ is valid in $I$, but *every* matching clause's body is unsatisfiable in $I$ for the matching instantiation — the program has **too few** cases (a missing clause, or a clause whose condition is too narrow).
- **Incorrect (statement/clause) instance**: some instance $A \leftarrow W$ has $A$ *false* in $I$ but $W$ *true* — the program has a clause that's **too permissive** (fires when it shouldn't).

This dichotomy — "the specification says yes but the program's rules never fire" versus "the program's rules fire but the specification says no" — is *precisely* the false-negative/false-positive split that structures how you'd triage any verification-tool failure report: a rejected-but-actually-valid program (your type checker is too weak — an "uncovered" gap in the checking rules) versus an accepted-but-actually-invalid program (your checker is too permissive — an "incorrect" rule firing where it shouldn't).

## The diagnoser: `wrong` and `missing` as a meta-interpreter

The diagnoser is itself written as a logic program — a **meta-interpreter** operating over a symbolic (ground-term) encoding of formulas (`and`, `or`, `not`, `if`, `all(V,W)`, `some(V,W)`). Two mutually-recursive predicates, `wrong(Formula, X)` and `missing(Formula, X)`, walk the *structure of a goal's own formula*, decomposing it connective-by-connective until they bottom out at an atom, where they consult a `clause/valid/unsatisfiable` oracle interface:

```prolog
wrong(V and W, X) :- wrong(V, X).
wrong(V and W, X) :- wrong(W, X).
wrong(not W, X)   :- missing(W, X).      % ¬goal wrongly succeeded ⟺ goal wrongly missing
missing(not W, X) :- wrong(W, X).        % ¬goal wrongly failed    ⟺ goal wrongly succeeded
wrong(X, z) :- clause(X, X1, if Y), wrong(Y, z).
wrong(X, X if Y) :- unsatisfiable(X, X1), clause(X, X1, if Y), valid(Y, Y1).
```

The last clause is where the actual error gets *found*: an incorrect clause instance is exactly a clause whose head is unsatisfiable-in-$I$ while its (some instance of its) body is valid-in-$I$ — this is literally Proposition 19.3's definition, turned into a Horn clause. The negation-handling clauses (`wrong(not W, X) :- missing(W, X)`) are attributed to McCabe, and they express something worth internalizing precisely: **an error in "$\lnot G$" is, by definition, an error in $G$ read the opposite way** — if $\lnot G$ wrongly succeeded, $G$ must have wrongly *failed* (missing an answer it should have had), and vice versa. This symmetric flip is the same duality [[Negation-in-Logic-Programs]] relies on (negation as failure computed by literally swapping success/failure), now recruited for error *localization* instead of query evaluation.

**Soundness (Theorem 20.1)** is a clean structural induction on the number of `wrong`/`missing` calls in the diagnoser's own refutation — every answer the diagnoser returns really is an uncovered atom or incorrect clause instance. **Completeness (Theorem 20.5)** needs a genuinely non-trivial auxiliary notion — an atom $A$ is **connected positively/negatively to $W$ wrt $P$** if it's reachable from $W$ by repeatedly unfolding clause bodies, tracking sign flips through negation (the same connectivity idea underlying stratification's level-checking) — and shows every genuine wrong-answer or missing-answer situation has *some* connected atom witnessing an uncovered atom or incorrect instance, which the diagnoser is guaranteed to find.

## The oracle, and why it's the whole cost model

The declarative diagnoser as given is a **specification**, not yet an efficient debugger: naively it would ask the programmer ("the oracle," standing in for ground truth about $I$) about the validity of *every* subformula reachable by the connectivity relation, which is enormous. Lloyd's real engineering contribution is a **cost model for interactive proof-search-guided debugging**, comparing three strategies by their oracle-query complexity — a comparison directly relevant to designing any interactive proof assistant's counterexample/error-localization UX:

| Algorithm | Strategy | Worst-case queries (tree: $n$ nodes, branching $b$, height $h$) |
|---|---|---|
| **Single-stepping** (Shapiro) | post-order (bottom-up) traversal of the erroneous computation tree | $O(n)$ |
| **Divide-and-query** (Shapiro) | always query the node splitting remaining weight closest to in half | $O(b \log n)$ — optimal to within a constant |
| **Top-down** (Lloyd, this chapter) | query the root, then recurse into the first not-valid child | $O(bh)$ worst case, but flexible and exploits locality |

The top-down algorithm is *not* asymptotically optimal, and Lloyd is candid about this — a linear, unbalanced tree with the error at the bottom makes top-down query every node while divide-and-query needs only $O(\log n)$. But top-down has a genuinely different, practically important advantage: it exploits **locality**. If the error is confined to a small subtree, top-down finds it almost immediately by descending straight there, while divide-and-query — being a purely syntactic, error-location-agnostic strategy — wastes queries exploring the large, correct sibling subtree before ever reaching the small buggy one. **This tradeoff — worst-case-optimal-but-locality-blind versus locality-exploiting-but-not-worst-case-optimal — is exactly the tradeoff between binary search and a heuristic-guided search (e.g. `git bisect` versus a stack-trace-guided debugger), and it recurs precisely in CEGAR-style counterexample localization**: do you bisect the trace uniformly, or do you let a heuristic (e.g. an interpolant's syntactic support, or a taint-tracking signal) steer you toward the likely culprit first? Lloyd's explicit numeric comparison of these strategies is a template for reasoning about that same design choice in your own CEGAR refinement loop.

The **top-down version with metacalls `succeed`/`fail`** (using actual execution results as heuristics to *order* the oracle queries, rather than asking about everything blind) is the pragmatic compromise: it decouples the diagnosis from whatever compilation/control transformation was applied to the source program (recall [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies]]'s normal-form transformation — the diagnoser works on the *declarative* content, indifferent to how it was compiled down), while still using actual computed results to prune the oracle-query search intelligently.

## Grounding: this is proof-carrying error localization

```rust
// The uncovered-atom / incorrect-clause-instance dichotomy as an explicit
// error type — this is the shape a verifier's counterexample report should
// take: not just "failed," but WHICH of the two failure modes, and where.
enum DiagnosedError {
    UncoveredAtom { atom: GroundAtom },                       // spec says yes, no rule fires
    IncorrectClauseInstance { head: GroundAtom, body: Formula }, // a rule fires when spec says no
}

// Top-down localization over a computation/proof tree — directly analogous
// to walking a failed verification-condition's proof-search tree, querying
// an "oracle" (here: an SMT counterexample, or a user-supplied invariant)
// at each node to decide which subtree to descend into.
fn localize_error(tree: &ComputationTree, oracle: &impl Fn(&GroundAtom) -> bool) -> DiagnosedError {
    if !oracle(&tree.root) {
        for child in &tree.children {
            if oracle(&child.conclusion) {
                continue; // this child is fine, keep looking
            }
            return localize_error(child, oracle); // descend into first bad child
        }
        // no child was invalid, yet root is invalid: THIS clause instance is the bug
        return DiagnosedError::IncorrectClauseInstance {
            head: tree.root.clone(), body: tree.rule_body.clone(),
        };
    }
    unreachable!("localize_error called on a valid root")
}
```

**In Lean**, the closest analogue is **minimization/`#minimize`-style bisection over a failing proof script or a failing `simp` call**, or more precisely, the general pattern of **proof-term inspection to find the exact subgoal where a `sorry`-free tactic block first goes wrong** — walking a proof/elaboration tree, querying (via the kernel's own type-checking, playing the oracle's role) whether each subterm is well-typed/valid, and descending into the first ill-typed child. The oracle-cost-minimization discussion maps directly onto **which subgoals an interactive prover should ask the user to discharge first** when automation stalls — a top-down, locality-exploiting query order (ask about the most likely culprit first, informed by heuristics) versus a worst-case-optimal bisection order is a live UX design question for any semi-automated proof assistant, not just Lloyd's PROLOG debugger.

## Where this leads

- **Directly load-bearing:** this chapter is the closest thing in the book to a design document for your compiler's own **counterexample/error-localization subsystem** — the uncovered/incorrect dichotomy, the oracle-query-complexity comparison, and the "diagnose using only the declarative semantics, independent of compiled control flow" discipline are all principles you should carry into designing how your CHC solver or refinement-type checker reports *why* a verification attempt failed, and *where* in the source the fix belongs.
- This chapter's soundness/completeness theorems depend directly on [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies]]'s normal-form transformation machinery — the diagnoser is proved correct for *arbitrary* programs precisely by reducing to the literal-bodied case that chapter already handled.
- The `wrong`/`missing` duality via negation is a concrete instance of the more general **soundness-completeness duality** running through the whole book (SLD-resolution's Theorems 7.1/8.6, SLDNF's 15.4/15.6, 16.1/16.3) — worth noticing that Lloyd keeps proving *both directions* of every major result, and that discipline (never claim soundness without also asking about completeness, and vice versa) is exactly the discipline your own verifier's correctness argument will need.
