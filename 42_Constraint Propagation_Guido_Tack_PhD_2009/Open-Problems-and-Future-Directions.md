---
title: "Open Problems and Future Directions"
source: "Constraint Propagation: Models, Techniques, Implementation (Guido Tack, PhD Dissertation, 2009)"
chapter: "Chapter 12, Conclusions — Section 12.2, Future Research"
pages: "169–172"
tags: [constraint-propagation, csp, sat-smt-csp, open-problems, gecode]
---

[[book-guidelines|↩ Back to guidelines]]

# Open Problems and Future Directions

## Why a dissertation ends with a "what's still broken" list

Every dissertation makes deliberate simplifying choices to get a tractable, provable model out the door. Tack's is no exception — Chapter 3 restricts propagators to *contracting and sound* (dropping monotonicity), Chapter 6 commits to *copying* over trailing, Chapter 11 restricts the Boolean-set-constraint language to *positive* constraints (plus a narrow negative extension), and the whole dissertation treats propagation as a strictly sequential process. Each of those choices bought something — a clean theorem, a simpler implementation, a tractable algorithm — at a cost the author was explicit about all along. Section 12.2 is the bill for those simplifications: five places where the dissertation's own results identify exactly what was left on the table, not vague hand-waving about "more work needed." That specificity is what makes this section worth reading closely rather than skimming as boilerplate — each of the five directions is a direct consequence of a design decision made chapters earlier.

```mermaid
mindmap
  root((Ch 12.2<br/>Future Research))
    Concurrent propagation
      Ch 6: copying enables cheap parallel search
      Unexplored: parallel propagator execution
    Relaxing monotonicity
      Ch 3: soundness + contraction suffice for correctness
      Monotonicity was never required
    Copying vs trailing
      Ch 6: copying wins in general, trailing wins for SAT-like problems
      Hybrid + bridge to dedicated SAT solvers
    Richer set propagators
      Ch 11: only positive (+ narrow negative) Boolean set constraints
      Mixed positive/negative, e.g. strict subset
    Cardinality reasoning
      Ch 11 related work: NP-hard in general
      Wanted: limited but effective derivable form
```

## 1. Concurrent and parallelized propagation

**What the book already established:** Gecode's copying architecture (Chapter 6) makes *search* embarrassingly parallel — cloning a space via forwarding pointers is cheap, so independent subtrees of the search tree can be explored on separate cores with minimal coordination. Tack notes this is already a "good position" to be in.

**What's still open:** parallelizing *propagation itself* — running several propagators for the *same* space concurrently, rather than parallelizing across spaces. This is a fundamentally harder problem, because propagators in the dissertation's model share mutable state (the domain $d$) and are scheduled precisely to avoid interleaving hazards — the agenda invariant (Chapter 5) assumes a single propagator runs to completion before the next is dequeued. Running propagators concurrently means either (a) proving a class of propagators is safe to interleave without violating soundness, or (b) introducing synchronization, which the text flags as the central cost to control ("low synchronization overhead between several concurrently running propagators").

**What breaks without addressing this:** naive concurrent propagation risks two propagators reading a domain mid-update from another, silently violating the contracting/sound contract that everything else in the model depends on — not a performance bug but a correctness bug, because the whole soundness argument (Theorem 3.13's termination proof, the fixed-point convergence argument) assumes propagation steps are linearizable.

**[[The-Denotational-and-Operational-Model-of-Constraint-Propagation#Grounding|Grounding]].** In Rust terms, a propagator today is essentially `fn propagate(&mut self, domain: &mut Domain) -> Status`, and safe concurrent execution would require something like a fine-grained lock or an actor-style message-passing scheme per variable, rather than shared-mutable-domain access:

```rust
// naive, unsafe interleaving — two propagators racing on shared domain state
trait Propagator {
    fn propagate(&mut self, domain: &mut Domain) -> Status;
}

// one direction toward safety: propagators only ever request domain
// operations through a channel, and a single actor owns the domain —
// concurrency moves from "shared memory" to "message passing"
enum DomainOp { Prune(VarId, Range), Fail, Fix }
trait ConcurrentPropagator {
    fn propagate(&mut self, ops: &Sender<DomainOp>) -> Status;
}
```

This is exactly the kind of design tension a CSP kernel in a Rust verification toolchain will hit directly: if the kernel is meant to search for counterexamples concurrently with the abstract interpreter's over-approximation pass, the propagation core needs an explicit concurrency story from day one rather than as a retrofit — Tack's own point that this is "largely unexplored" still holds.

## 2. Relaxing monotonicity: approximative, randomized, and heuristic propagators

**What the book already established:** Chapter 3's most consequential minimalism is defining propagators as merely *contracting and sound* — not idempotent, not monotonic. Theorem 3.17 shows monotonicity buys *confluence* (order-independent propagation), but the solver's soundness and completeness never required it. Non-monotonic propagation is still correct; it's just order-dependent (Example 3.16).

**What's still open:** if correctness never depended on monotonicity in the first place, the design space includes propagators that are deliberately non-monotonic — approximative, randomized, or heuristic algorithms that trade completeness-with-respect-to-a-domain-approximation for speed, useful precisely when the $\mathcal D$-complete propagator for a constraint is intractable (recall Chapter 4's NP-hardness results for domain completeness on linear equations and Chapter 11's NP-hardness of cardinality reasoning — both cases where a weaker, cheaper propagator might still be the right engineering trade-off).

**What breaks without addressing this:** without this relaxation, "propagation strength" (Chapter 4) is framed almost entirely as a *design-time* choice among fixed, deterministically-complete algorithms (bounds, range, set-interval consistency); randomized or heuristic pruning is a genuinely different axis — strength that varies *at run time*, potentially even probabilistically — that the dissertation's static domain-approximation framework doesn't model at all.

**Grounding.** This maps directly onto SAT-solver practice — VSIDS-style heuristics and restarts are exactly "randomized, non-monotonic decision procedures that are still sound because contraction was never required to be uniform." A sketch of what a heuristic propagator's contract might look like, still honoring soundness/contraction but dropping any guarantee of $\mathcal D$-completeness:

```python
def heuristic_propagate(domain, constraint, budget):
    # sound (never removes a solution) and contracting (result ⊆ domain),
    # but intentionally incomplete w.r.t. any fixed domain approximation —
    # spends a bounded "budget" of work and returns whatever it pruned
    pruned = domain.copy()
    for _ in range(budget):
        pruned = cheap_partial_prune(pruned, constraint)
        if pruned.is_failed():
            return pruned
    return pruned  # may be weaker than the D-canonical propagator — that's fine
```

For the automated-reasoning/CSP-kernel side of a verification toolchain, this is the theoretical license to build *cheap, incomplete* propagators for expensive domains (non-linear arithmetic, automaton-shaped abstract domains) without losing overall solver soundness — completeness is sacrificed locally and recovered globally by search, exactly as Chapter 3 already guarantees for any non-monotonic propagator.

## 3. Hybrid copying/trailing architectures

**What the book already established:** Chapter 6 makes and empirically defends a specific architectural bet — copying with (batch) recomputation over trailing — because it composes better with arbitrary search strategies and (per point 1 above) parallel search. But Section 6.9's own benchmarks (Table 6.8) show a SAT-clause-propagator case study where copying overhead *dominates* for degenerate, near-stateless problem classes, and dedicated SAT solvers still vastly outperform general CP solvers on SAT instances.

**What's still open:** rather than treating copying and trailing as a global, once-per-solver choice, investigate a *hybrid* — plausibly copying for the bulk of the space's variables/propagators, trailing (or some SAT-solver-style structure) for the parts of the problem that look SAT-like. Tack cites Reischuk (2008) as a first concrete step in this direction.

**What breaks without addressing this:** the dissertation's own evidence (6.9) shows the "one architecture for the whole solver" assumption is not free — it is a genuine trade-off, not a strictly dominant design, and the failure mode (SAT-shaped subproblems paying copying overhead they don't need to) is empirically demonstrated, not hypothetical.

**Grounding.** This is close to a CDCL/CP integration question: a CSP kernel embedding a SAT-style Boolean core (unit propagation, watched literals — which Chapter 5 already draws an explicit analogy to via dynamic dependencies, Example 5.13) could plausibly run that core under trailing while the rest of the space still uses copying, switching representations at the module boundary Chapter 6 already establishes between the domain-independent kernel and domain-specific modules. For a Rust CSP kernel meant to search for concrete counterexamples against refinement-type invariants, this bears directly on whether the Boolean-clause layer of the search (if the clause language ends up SAT-encoded) should live in a different backtracking substrate than the numeric/set-domain layer.

## 4. Extending set-interval completeness to richer constraint classes

**What the book already established:** Chapter 11's specification-to-propagator technique is powerful but linguistically narrow: the grammar $C ::= S{=}S \mid S{\subseteq}S \mid C{\wedge}C$ only covers *positive* Boolean set constraints, and Theorem 11.11 proves negation is a genuine expressivity increase that cannot be folded back into the positive language — which is exactly why negated constraints needed their own separate propagation rule (Section 11.3) rather than reuse of the positive machinery.

**What's still open:** constraints that mix positive and negative structure in the same formula — the book's own example is *strict subset* ($S \subsetneq S'$, i.e., $S \subseteq S' \wedge S \neq S'$) — fall entirely outside both the positive language and the standalone negation extension, and need dedicated propagators today. The open question is how far the systematic, specification-to-propagator generation technique of Chapter 11 can be pushed before it stops yielding automatically-derived, set-interval-complete algorithms.

**What breaks without addressing this:** every mixed positive/negative constraint currently requires going back to hand-writing a dedicated propagator — precisely the "implement each variant by hand" problem that both derivation techniques in Part II (views, and this specification language) were built to eliminate in the first place. This open problem is a direct crack in the dissertation's central "comprehensiveness without hand-writing" thesis.

**Grounding.** For the compiler project's automata/DFA-shaped abstract domains, this generalizes to: how much of a richer constraint language over such domains can still be compiled to complete propagators via a normal-form-and-Shannon-expansion-style technique, versus where negation-like operations (complement of a DFA language, say) force a structurally different, hand-derived propagation rule — a question with a very similar shape to Theorem 11.11's expressivity gap, just one level up in the domain hierarchy.

## 5. Cardinality reasoning for set constraints

**What the book already established:** the set-interval approximation (Section 4.5, used throughout Chapter 11) represents a set variable's domain purely by its lower and upper bound $[l, u]$ — it says nothing about how many elements the final set actually has. Constraints like $|x_i \cap x_j| \le k$ need cardinality information the set-interval representation doesn't carry, and Bessière et al. (2004) already established that complete cardinality-aware propagation is NP-hard in general.

**What's still open:** given that full cardinality reasoning is intractable, the concrete research question Tack poses is to find a "limited, but effective" derivable form of cardinality reasoning — something short of full completeness, but automatically generable (in the spirit of Chapter 11's technique) rather than requiring bespoke propagators for every cardinality-constrained problem.

**What breaks without addressing this:** without any cardinality reasoning layered on top of set-interval completeness, propagation is blind to a whole class of pruning opportunities — a set variable's bounds can be stable ($\mathcal D^{[\mathcal P(U)]}$-consistent) while still being inconsistent once cardinality is taken into account, so search does strictly more work than necessary on any cardinality-heavy problem (the dissertation's own benchmark suite includes several, e.g. Steiner Triples).

**Grounding.** This is the clearest of the five threads for the compiler's CSP kernel: cardinality constraints are a recurring shape in refinement-type and invariant-generation settings (e.g. "exactly $k$ of these $n$ flags are set," array-length bookkeeping under a DFA-shaped abstract domain), and the NP-hardness result is a warning that a general complete cardinality propagator is off the table — the design target should be, in Tack's own words, a "limited, but effective" propagator, i.e. a $\mathcal D$-complete-for-some-weaker-$\mathcal D$ approximation rather than full domain completeness, exactly the strength/tractability trade-off formalized back in Chapter 4.

## Where this leads

These five threads are not equally weighted for a solver-kernel project in the `sat-smt-csp` focus area. Direction 2 (relaxing monotonicity) is the most immediately load-bearing: it is the theoretical permission slip for building cheap, incomplete propagators over expensive abstract domains — automata-shaped, non-linear-arithmetic-shaped — without forfeiting the kernel's overall soundness, which matters directly for a CSP kernel meant to search for concrete counterexamples against dependent/refinement-type invariants. Direction 3 (hybrid copying/trailing, bridging to dedicated SAT solvers) matters just as directly if any part of the verification-condition discharge pipeline ends up SAT-encoded. Directions 4 and 5 (richer set-constraint classes, cardinality reasoning) are the concrete instances of "how far can specification-to-propagator generation be pushed" that a DFA/automaton-based abstract-domain layer will eventually need answered — not as background, but as an open research question the dissertation itself leaves unresolved, which is worth knowing going in rather than discovering by hitting the same wall Tack names here.
