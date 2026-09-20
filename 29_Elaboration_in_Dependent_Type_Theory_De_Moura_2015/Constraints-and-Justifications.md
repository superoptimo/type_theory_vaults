---
title: Constraints and Justifications
source: "Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)"
chapter: "Section 3.2 (pp. 12-15)"
tags: [type-theory, elaboration, unification, lean, constraint-solving]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem: how do you remember *why* you believe something?

Picture the elaborator midway through solving a large term. It has generated dozens of pending obligations — "this metavariable's type must match that one," "this hole must resolve to one of these three overloaded symbols" — and it is about to start guessing: trying one branch of an ambiguous choice, seeing if the rest falls into place. Eventually a guess turns out wrong, three levels of case-splitting deep. Now what?

A naive backtracker throws away everything since the last choice point and retries the next alternative — *chronological* backtracking. But most of the work done since that choice point had nothing to do with the choice that failed. If the failure was actually caused by a decision made five choice points earlier, chronological backtracking will patiently re-explore an enormous, doomed search tree before it even gets back to the real culprit.

The fix requires the solver to know, for every fact it currently believes (every constraint, every metavariable assignment), *which assumptions that fact actually depends on*. Then, when something goes wrong, it can jump directly back to the assumption at fault instead of unwinding one step at a time. This is **non-chronological backtracking**, and the bookkeeping device that makes it possible is what this section introduces: **justifications**, attached to every **constraint** the elaborator manipulates.

This is a purely bookkeeping-layer topic — it doesn't say anything new about *what* the elaborator infers, only about how it tracks *why* it believes what it currently believes, so that later it can fail intelligently instead of thrashing.

## Two kinds of obligation: unification vs. choice

During preprocessing (covered in [[The-Preprocessing-Phase|The Preprocessing Phase]]), converting a preterm into a term-with-holes generates a list of obligations the metavariables must eventually satisfy. The paper splits these into two kinds:

- **Unification constraints** enforce *typing* facts — e.g., "the type of this argument must match the function's expected argument type." Written $t \approx s$.
- **Choice constraints** enforce *selection among alternatives* — e.g., "this inferred value must be one of a finite set of possible overloads," or "this metavariable must be resolved by type class search." Written $?m\,\ell : t \text{ in } f$.

The distinction matters because the two are solved differently. A unification constraint asks "make these two terms equal" — closer to an equation. A choice constraint asks "pick one of these ways of filling this hole" — closer to a search problem with backtracking built in. Both, however, need the same justification machinery layered on top, because both can turn out to be wrong and need to be retracted cleanly.

```python
# A sketch of the two constraint shapes, Python-side, for intuition only —
# the paper's actual representation is symbolic (t ≈ s) and (?m ℓ : t in f).

class UnificationConstraint:
    def __init__(self, lhs, rhs, justification):
        self.lhs = lhs                # term t
        self.rhs = rhs                # term s
        self.justification = justification

class ChoiceConstraint:
    def __init__(self, meta, locals_, expected_type, alternatives_fn, justification, ondemand=False):
        self.meta = meta                       # ?m
        self.locals = locals_                  # ℓ : the context ?m was created in
        self.expected_type = expected_type     # t
        self.alternatives_fn = alternatives_fn # f: produces a stream of alternative constraint-lists
        self.justification = justification
        self.ondemand = ondemand
```

## Justifications: a receipt for every belief

A unification constraint $t \approx s$ is never stored bare — it's always annotated as $\langle t \approx s, j\rangle$, where $j$ is a **justification**: a record of the facts and assumptions that gave rise to this constraint existing in the first place. Justifications serve two purposes at once:

1. **Better error messages.** When elaboration ultimately fails, the justification trail lets Lean explain *why* it believed the failing constraint should hold, tracing back through the assumptions and prior facts that produced it — rather than just reporting "these two terms don't unify" with no context.
2. **Non-chronological backtracking.** Because each fact carries the assumption(s) it rests on, the solver can identify precisely which choice point is responsible for a downstream failure and jump back there directly, pruning away the (possibly enormous) subtree of alternatives that don't even touch that assumption.

There are exactly three kinds of justification:

- **Asserted** — used to tag constraints generated during preprocessing itself. These are "given" facts, not the result of any choice; they simply record where in the source (or in the preprocessing logic) the constraint came from.
- **Assumption** — a fresh tag minted every time the solver performs a *case split* (a genuine choice among alternatives). Each branch of the split gets its own fresh assumption justification, so any fact derived within that branch can be traced back to "this happened because we chose alternative $k$ at case split $N$."
- **Join**, written $j_1 \bowtie j_2$ — represents the union of two justifications. This arises constantly: whenever a fact depends on *two* prior facts (e.g. it was produced by combining two constraints, or by applying a substitution derived from one justification to a constraint carrying another), the resulting justification must record dependence on *both* origins, not just one.

This is a small, closed algebra — three constructors, no more — which is exactly what keeps the tracking machinery tractable: joins compose without needing a fourth case, and every fact in the system reduces, transitively, to a finite set of assumption tags plus asserted origins.

```rust
// A justification, Rust-side, as a small closed algebra.
// (Illustrative — the paper leaves the internal representation implicit
// beyond "asserted / assumption / join".)
use std::rc::Rc;

#[derive(Clone)]
enum Justification {
    Asserted { site: SourceSite },
    Assumption { id: AssumptionId },          // fresh per case split
    Join(Rc<Justification>, Rc<Justification>), // j1 ⋈ j2
}

impl Justification {
    fn join(self, other: Justification) -> Justification {
        Justification::Join(Rc::new(self), Rc::new(other))
    }
}
```

## Substitutions: assignments with a paper trail

Solving a unification constraint $\langle ?m \approx t, j\rangle$ produces an **assignment**: $?m \mapsto \langle t, j\rangle$, pairing the closed term $t$ that $?m$ is now bound to with the justification $j$ that explains *why* this assignment was made. A **substitution** is just a finite collection of such assignments.

The crucial discipline is: *whenever you apply a substitution to a constraint, you must propagate justifications via a join.* Applying the assignment $?m \mapsto \langle t, j_m\rangle$ to a constraint $\langle r \approx s, j\rangle$ doesn't just rewrite $r$ and $s$ — it produces

$$\langle r[?m := t] \approx s[?m := t],\; j \bowtie j_m \rangle$$

The new constraint depends on *both* the original justification $j$ and the justification $j_m$ for the substitution that was just applied. Skip this step — apply the substitution but keep the old justification — and the dependency graph silently becomes wrong: a fact that actually depends on assumption $j_m$ would be misreported as depending only on $j$, and non-chronological backtracking would then fail to retract it when $j_m$'s assumption turns out to be false. The notation $\langle s \approx t, j_1\rangle \bowtie j_2$ is shorthand for $\langle s \approx t, j_1 \bowtie j_2\rangle$, and it extends pointwise to whole lists of constraints: if $\mathbf{a} = [c_1, \ldots, c_n]$, then $\mathbf{a} \bowtie j = [c_1 \bowtie j, \ldots, c_n \bowtie j]$.

```python
# The join-on-substitution discipline, made concrete.

def apply_assignment(meta, term, j_m, constraint):
    """Apply  meta ↦ (term, j_m)  to a unification constraint ⟨r ≈ s, j⟩."""
    r, s, j = constraint.lhs, constraint.rhs, constraint.justification
    new_lhs = substitute(r, meta, term)
    new_rhs = substitute(s, meta, term)
    new_justification = join(j, j_m)   # <-- never forget this
    return UnificationConstraint(new_lhs, new_rhs, new_justification)
```

The same discipline applies to choice constraints. Applying $?m \mapsto \langle s, j_m\rangle$ to a choice constraint $\langle ?n\,\ell : t \text{ in } f, j\rangle$ produces $\langle ?n\,\ell : t[?m := s] \text{ in } f, j \bowtie j_m\rangle$ — the expected type is rewritten, and again the justification is joined, not replaced.

## Choice constraints: regular vs. ondemand

A choice constraint $\langle ?m\,\ell : t \text{ in } f, j\rangle$ packages four things:

- $?m$, the metavariable being resolved,
- $\ell$, the free variables of the context $?m$ was created in (recall from [[Term-Representation-and-Core-Data-Structures|Term Representation and Core Data Structures]] that metavariables are applied to their creation context so only closed terms are ever assigned),
- $t$, the expected type of $?m\,\ell$,
- $f$, a procedure that — given the term $?m\,\ell$, its type $t$, and a substitution — produces a stream of *alternatives*, each alternative itself a whole list of constraints (not just one unification constraint) representing one possible way of resolving $?m$, together with a justification.

That "stream of alternatives, each a list of constraints" shape is exactly what powers overloading and type class search: each alternative is a candidate resolution (an overload, a candidate instance) together with whatever side-obligations picking that candidate entails, and the solver can try them one at a time, backtracking via the justification machinery if one doesn't pan out.

Not every choice constraint should be attempted immediately, though. A choice constraint can be marked **ondemand**. When it is, the solver will only invoke $f$ once *all* metavariables in $t$ (the expected type) have been instantiated — until then, the constraint just sits, gaining no benefit from being poked early since its own type isn't pinned down yet. The paper introduces precise vocabulary for this waiting state:

- An ondemand choice constraint is **ready** once $t$ contains no metavariables (so $f$ can finally be invoked).
- It is **postponed** otherwise.

Choice constraints *without* the ondemand flag are called **regular**, and these are used specifically to encode overloaded symbols: when a name could mean several different things, a regular choice constraint enumerates the candidates immediately, rather than waiting for more type information to arrive. (Ondemand constraints, by contrast, are exactly the mechanism [[Type-Classes-and-Class-Inference|Type Classes and Class Inference]] and [[Overloading-and-Coercions|Overloading and Coercions]] later build coercion insertion and instance search on top of — the paper explicitly flags this connection, promising to "later describe how this feature is used to implement the type class mechanism and coercions.")

## Why this is the right foundation to build on

Every other mechanical piece of the elaborator — the [[The-Constraint-Simplification-Procedure|simplification procedure]] that decomposes constraints into categories, the [[The-Constraint-Solving-Procedure|solving procedure]]'s priority queue and case-split stack, the [[Type-Classes-and-Class-Inference|type class search]] built on ondemand choice constraints — operates *on* the objects defined here: constraints carrying justifications, and substitutions that propagate them correctly via join. Get the justification discipline right, and non-chronological backtracking becomes a matter of walking the dependency structure already recorded on each fact; get it wrong (e.g. dropping a join somewhere), and the solver would either retract too little (leaving stale, invalid facts around after a backtrack) or too much (undoing correct work that never actually depended on the failed assumption).

In short: this section is the elaborator's *memory* — not what it infers, but the evidence trail attached to every inference, engineered specifically so that later, when something breaks, the system can figure out exactly how far back to go.
