---
title: SLD-Resolution
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 2, §7–11 (pp. 40–66)
tags: [sld-resolution, soundness, completeness, proof-search, sld-trees, cut, computation-rule]
---

[[book-guidelines|↩ Back to guidelines]]

## From "what a program means" to "how you compute it"

[[Declarative-Semantics-of-Definite-Programs]] defined the least Herbrand model $M_P$ and correct answers — the *specification*. This article is the *algorithm*: SLD-resolution, the proof-search procedure a PROLOG engine actually runs, and the soundness/completeness theorems proving the algorithm computes exactly what the specification demands. The name is precise and worth unpacking: **SL**-resolution (Linear resolution with a **S**election function), specialized to **D**efinite clauses. Each piece of the name is a design decision you'd also face building any proof-search engine or clause-based SMT-adjacent solver:

- *Linear* — each derivation step resolves the *current goal* against one program clause, producing a new single goal; you never juggle a growing set of active clauses (contrast general resolution theorem proving).
- *Selection function* — you must choose *which* atom in the current goal to resolve on next; a whole section (§9) is devoted to proving this choice doesn't affect *what* you can prove, only *how efficiently*.
- *Definite* — restricted to Horn clauses with exactly one positive literal, which is exactly the restriction that made [[Declarative-Semantics-of-Definite-Programs]]'s Model Intersection Property hold.

## Derivations, refutations, and computed answers

A **resolution step**: given goal $\leftarrow A_1,\ldots,A_m,\ldots,A_k$ and clause $A \leftarrow B_1,\ldots,B_q$ (a *fresh variant* — "standardizing apart," renaming so the clause's variables never collide with the derivation-so-far's), select an atom $A_m$ (the **selected atom**), unify it with $A$ via mgu $\theta$ ([[Unification]]), and the resolvent is $\leftarrow (A_1,\ldots,A_{m-1},B_1,\ldots,B_q,A_{m+1},\ldots,A_k)\theta$.

An **SLD-derivation** is a sequence of such steps; an **SLD-refutation** is a *finite* derivation ending in the empty clause $\square$ — a literal contradiction, meaning the goal (negated) has been shown inconsistent with $P$, hence (via Proposition 3.1) provable. The **computed answer** is the composition of all the mgu's used, restricted to the original goal's variables.

```mermaid
graph TD
    G0["← sort(17.22.6.5.nil, Y)"] -->|unify with sort(x,y) :- sorted(y),perm(x,y), θ₁=y/Y,x/[...]| G1["← sorted(Y), perm([...],Y)"]
    G1 -->|...many steps...| GN["□ (empty clause)"]
    GN -.->|θ₁θ₂...θₙ restricted to Y| Answer["Y = 5.6.17.22.nil"]
```

**Success set** $= \{A \in B_P : P \cup \{\leftarrow A\} \text{ has a refutation}\}$ — the *procedural* counterpart of $M_P$.

## Soundness (Theorem 7.1): resolution never lies

Every computed answer is a correct answer. The proof is a clean induction on refutation length: length 1 forces $G$ to be $\leftarrow A$ matched against a *unit* clause $A \leftarrow$, so $A\theta_1$ is literally an instance of an axiom, hence a logical consequence trivially; the inductive step chains this through the resolvent using the fact that a clause instance $A\theta \leftarrow (B_1\wedge\cdots\wedge B_q)\theta$ being a logical consequence of $P$, plus $(B_1\wedge\cdots\wedge B_q)\theta$ a consequence, gives $A\theta$ a consequence, by ordinary modus ponens reasoning lifted through substitution.

**Where soundness silently depends on [[Unification]]:** the entire argument assumes the mgu computed is a *genuine* unifier producing a *finite, well-formed* substitution — Lloyd's occur-check discussion resurfaces here explicitly (§7): if you drop the occur check, you can derive `test` from `test :- p(X,X). p(X, f(X)).` even though `test` is **not** a logical consequence of the program. This is not a hypothetical edge case — it is a live counterexample to Theorem 7.1 the moment the occur check is dropped, which is exactly why every real PROLOG system that skips the occur check for performance is, strictly, running an *unsound* proof procedure and is relying on programmers to avoid the pathological cases (difference lists being the practically-relevant danger zone, per [[Unification]]).

## Completeness (Theorem 8.6): resolution finds everything

The converse direction needs two technical lemmas that are worth understanding on their own, because they recur as proof techniques throughout the book:

- **Mgu Lemma (8.1):** if an *unrestricted* refutation exists (using any unifiers, not necessarily most general ones), then a refutation using only mgu's exists too, and is "at least as general." This licenses always committing to mgu's without losing solutions — the same argument pattern underlies why a type inferencer using unification (rather than ad-hoc guessing) doesn't lose principal types.
- **Lifting Lemma (8.2):** a refutation of a *ground instance* $P \cup \{G\theta\}$ can be "lifted" to a refutation of $P \cup \{G\}$ itself, with the ground refutation recoverable as an instance. This is the technical engine that lets Theorem 8.3 (success set $=$ $M_P$, proved by induction on $T_P{\uparrow}n$-membership at the *ground* level) get promoted to a statement about the *non-ground* SLD-resolution procedure.

Chained together: Theorem 8.3 (success set $= M_P$), Theorem 8.4 (Hill: any unsatisfiable $P \cup \{G\}$ has *some* refutation), and finally **Theorem 8.6**, the full statement — every correct answer $\theta$ is subsumed by some computed answer $\sigma$ (i.e. $\theta$ and $\sigma\gamma$ agree on $G$'s variables, for some $\gamma$). Computed answers are always *maximally general*; that's why the theorem says "subsumed by," not "equal to."

## Independence of the computation rule (§9): a genuine "don't-care" degree of freedom

A **computation rule** picks which atom gets selected at each step. The **Switching Lemma (9.1)** shows that swapping the order of two adjacent selections in a refutation produces another valid refutation with a variant of the same computed answer. Iterating this, **Theorem 9.2** proves: *if a refutation exists for any computation rule, one exists for every computation rule.* This is a genuine, load-bearing "confluence"-style result — it says the choice of evaluation order is a **don't-care nondeterminism** with respect to *provability* (though very much a *don't-ignore* choice with respect to *efficiency* and *termination in practice*, as §10 immediately shows).

**Computational adequacy (Theorem 9.6)** is proved here too — every partial recursive function is computable by *some* definite program, via a structural encoding of composition/primitive-recursion/minimalization as clause schemas. This is Lloyd's Turing-completeness result for definite programs, and its real payoff is methodological: it justifies treating "definite program" as a genuine general-purpose computation model, not merely a restricted query language.

## SLD-trees and the gap between "provable" and "found by your PROLOG system" (§10)

An **SLD-tree** for $P \cup \{G\}$ (via a fixed computation rule $R$) is the full search tree: each node a goal, children generated by unifying the selected atom against every matching clause head. Branches are success (end in $\square$), failure (selected atom unifies with no clause head), or infinite.

Independence of the computation rule (§9) guarantees *some* branch of *some* tree succeeds when $P \cup \{G\}$ is unsatisfiable — but it says nothing about whether a **depth-first search with a fixed clause order** (exactly what standard PROLOG does) will *find* that branch. Lloyd's worked counterexample is devastating and precise:

```prolog
p(a,b).
p(c,b).
p(X,Z) :- p(X,Y), p(Y,Z).
p(X,Y) :- p(Y,X).
```
Every clause here is *needed* for `?- p(a,c)` to succeed, yet **no ordering** of these clauses lets depth-first search find the refutation — clauses 3 and 4 both have fully general heads, so whichever comes first in the program is tried first at every call, sending the leftmost branch into an infinite loop before the other clause is ever reached. This is the completeness gap that makes real PROLOG **procedurally incomplete** even though the underlying logic (Theorem 8.4) guarantees a proof exists. The fix requires either a **fair** search rule (breadth-first component — guaranteed to eventually try every branch, at the cost of efficiency) or smarter control (coroutining, e.g. NU-PROLOG's `when` declarations delaying a subgoal like `sorted(X)` until its argument is sufficiently instantiated — turning the `slowsort` program from "spectacularly inefficient generate-and-test" into genuine merge-style coroutining between generator and tester).

**This is precisely the same tension a proof-search-based SMT or Horn-clause solver has to manage:** a complete decision procedure (e.g. resolution + Herbrand's theorem) gives *existence* of a proof; a practical implementation (DPLL/CDCL-style search, or a depth-first Horn-clause solver) needs an explicit fairness or restart/backjumping strategy to actually *find* it within the search tree, or it can loop forever down one infinite, provably-doomed branch while a two-step proof sits in a sibling subtree. Your CEGAR loop's abstraction-refinement scheduling is solving exactly this problem in the CHC-solving setting.

## Cut (§11): a control annotation, not a logical connective

`!` succeeds immediately when first reached, but on backtracking it prunes the entire remaining search subtree back to the **parent goal** (the goal that invoked the clause containing the cut). Lloyd's key distinction:

- **Declaratively**, cut is inert — removing all cuts from a definite program doesn't change its logical reading at all.
- **Procedurally**, a cut is **safe** if the pruned subtree contained no success branch (pure efficiency gain, no lost answers) and **unsafe** if it did (correctness is compromised — a correct answer becomes unreachable). Cut thus introduces a form of incompleteness *orthogonal to* the depth-first-search incompleteness of §10: with an unsafe cut, the system doesn't merely loop — it confidently returns "no" when the correct answer is "yes."

Lloyd's sharpest example shows cut can be abused to *encode* an incomplete declarative reading, not just prune search:
```prolog
max(X, Y, Y) :- X < Y, !.
max(X, Y, X).
```
Procedurally this computes the maximum correctly. Declaratively, read as a definite program, the second clause says "$X$ is the max of $X$ and $Y$" *unconditionally* — false whenever $Y > X$ — and it is only the *cut* in the first clause (a control annotation with no declarative content) that prevents this false reading from ever being exercised. The program's stated logic and its actual behavior have silently diverged; Lloyd's recommendation — replace such cuts with genuine higher-level constructs (if-then-else, negation, `\=`) that are honestly declarative — is exactly the discipline "prefer a total, honestly-specified function to a partial one patched by control-flow tricks" that shows up in any verified-software methodology.

## Grounding: SLD-resolution as a proof-search loop

```rust
// A minimal SLD-interpreter skeleton: this loop, with the computation rule
// (which atom to select) and search rule (DFS vs BFS) as pluggable strategies,
// IS a resolution-based backward-chaining solver for Horn clauses / CHCs.
struct Goal { atoms: Vec<Atom> }

fn solve(goal: &Goal, program: &[Clause], subst: &Subst, depth_limit: usize) -> Vec<Subst> {
    if goal.atoms.is_empty() {
        return vec![subst.clone()]; // □ reached: this branch is a refutation
    }
    if depth_limit == 0 { return vec![]; } // guard against infinite branches (§10's problem!)
    let selected = &goal.atoms[0]; // fixed left-to-right computation rule (standard PROLOG)
    let mut results = vec![];
    for clause in program {
        let renamed = clause.rename_apart(); // "standardizing apart" (§7)
        if let Some(mgu) = unify(selected, &renamed.head, subst) {
            let new_goal = build_resolvent(goal, &renamed, &mgu);
            results.extend(solve(&new_goal, program, &mgu, depth_limit - 1));
        }
        // depth-first over clause order = exactly the incompleteness trap of §10
    }
    results
}
```

**In Lean**, the closest structural analogue is **backward-chaining tactic proof search** — `apply`/`exact?`/`aesop`-style automation resolving a goal against a database of lemmas by unifying the goal against a lemma's conclusion and recursing on the generated subgoals, exactly SLD-resolution's step with lemma "clauses" in place of program clauses. The Switching Lemma's confluence property is why the *order* in which `aesop` or a similar tactic tries subgoals affects **performance** but (for a sound tactic framework) never affects **which goals are ultimately provable** — the same don't-care/don't-ignore split as §9 versus §10 here.

## Where this leads

- **Directly load-bearing for your CHC/Horn-clause solver:** the soundness/completeness pairing (Theorems 7.1, 8.6) is the exact template your solver's correctness proof needs — "every model returned satisfies the constraints" (soundness) and "every satisfying instantiation is findable by the search" (completeness), and the §10 depth-first-incompleteness trap is precisely why practical CHC solvers need fairness/restart strategies, not naive DFS.
- The **cut** discussion is a direct precedent for why your compiler's refinement-type elaborator must keep proof-search control annotations (e.g. `first`/commit combinators in a tactic engine, or `!`-like exclusivity markers in pattern matching) strictly separated from the *specification* they're meant to accelerate — conflating them is exactly the `max/3` failure mode.
- [[Negation-in-Logic-Programs]] (chapter 3) builds directly on this machinery: negation as failure is defined by running SLD-resolution to check for a *finitely failed* SLD-tree, so every subtlety here (fairness, depth-first incompleteness, the occur-check caveat) propagates forward as a precondition for negation's own soundness/completeness theorems.
- The **occur-check unsoundness** loose end from [[Unification]] is fully resolved only in [[Semantics-of-Perpetual-Processes]] (chapter 6), where infinite terms get a legitimate topological semantics instead of being simply excluded by fiat.
