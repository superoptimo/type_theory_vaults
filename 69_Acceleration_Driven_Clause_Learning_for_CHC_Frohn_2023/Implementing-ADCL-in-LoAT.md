---
title: Implementing ADCL in LoAT
source: "ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses (Frohn & Giesl, 2023)"
chapters: "Sect. 4 Implementing ADCL (pp. 15–19)"
tags: [chc, sat-smt-csp, solver-engineering, smt, automata, redundancy]
---

[[book-guidelines|↩ Back to guidelines]]

## From oracles to code

[[The-ADCL-Calculus]] is stated over three **oracles**: an exact redundancy check ($\sqsubseteq$), an exact SMT-satisfiability check, and an exact acceleration function. None of these exist as decidable, always-terminating procedures in practice — redundancy in a general many-sorted theory is undecidable, SMT solvers can time out or fail on nonlinear arithmetic, and acceleration techniques are inherently partial (some transition relations simply have no closed form in the target theory, as [[Loop-Acceleration]] already showed with the $N \cdot Y$ example). This section is the paper admitting that gap explicitly and then closing it with concrete, imperfect, engineered substitutes — implemented in the authors' tool **LoAT**, built on the SMT solvers Yices and Z3, the automata library libFAUDES, and the recurrence-relation solver PURRS.

What breaks without this section: a calculus with idealized oracles is a specification, not a program. Every one of the approximations below trades away *some* guarantee from the metatheory of [[Metatheoretic-Properties-of-ADCL]] — and the paper is unusually candid about exactly which guarantee each approximation costs. That's the throughline worth tracking here: not "how do you implement X" in isolation, but "what property of the idealized calculus does implementing X approximately cost you."

This is also, for a Rust-based CSP-kernel builder, the single most directly actionable section of the paper: everything here is systems engineering — an automata library call, an incremental solver stack, a scheduling heuristic — not abstract proof theory.

## Redundancy: from an equivalence check to a language-inclusion check

Recall from [[Syntactic-Implicants-and-Redundancy]] that $\varphi \sqsubseteq \pi$ means $\mathrm{grnd}(\varphi) \subseteq \mathrm{grnd}(\pi)$ — a semantic statement about (generally infinite) sets of ground clauses. You cannot check that directly. LoAT's answer reuses the regular-language mapping $L$ from the non-termination proof machinery (Def. 16, see [[Metatheoretic-Properties-of-ADCL]]): $L(\varphi)$ is a *finite automaton* whose language characterizes which resolution sequences a clause $\varphi$ stands in for.

For **Accelerate**, checking whether a freshly-accelerated clause is redundant reduces to a language-inclusion test:

$$L(\vec\varphi^\circlearrowleft)^+ \subseteq L(\varphi)$$

Language inclusion between finite automata is a classical, efficiently-decidable problem (complement one side, intersect, check emptiness) — exactly the kind of check `libFAUDES` exists to perform. This is the payoff of representing "what a clause covers" as a regular language rather than as a first-order formula: a question that's undecidable in general theories becomes decidable the moment you're only asking about resolution-sequence *shape* rather than resolution-sequence *semantics*.

**What this buys you, and what it doesn't.** $L(\vec\varphi^\circlearrowleft)^+ \subseteq L(\varphi)$ is only a **sufficient** condition for $\vec\varphi^\circlearrowleft \sqsubseteq \varphi$, never a complete one. The paper gives a sharp illustration of the gap: an *original* clause $\varphi$ has $|L(\varphi)| = 1$ (it stands for exactly one resolution step — itself), while a *learned* clause has $|L(\varphi)| = \infty$ (it stands for arbitrarily many ordinary steps). A learned clause can therefore be genuinely redundant with respect to an *original* clause in the ground-instance sense, yet the language-based check can never witness this, because the language-inclusion direction needed doesn't correspond to any automaton relationship the check inspects. This is a structural blind spot, not a tunable imprecision.

**Covered's asymmetric heuristic, re-derived from this machinery.** [[The-ADCL-Calculus]] already flagged that Covered treats single-clause suffixes more strictly (needs $\sqsubset$, not just $\sqsubseteq$) than multi-clause ones, for soundness reasons. Here's the automata-level reason the *heuristic* used to approximate that check works: if a singleton suffix $\varphi'$ (necessarily original, so $|L(\varphi')| = 1$) has $L(\varphi') \subseteq L(\varphi)$ for some other clause $\varphi \ne \varphi'$, that inclusion is only possible if $\varphi$ is a learned clause ($|L(\varphi)| = \infty > 1 = |L(\varphi')|$), which then *forces* $L(\varphi') \subset L(\varphi)$ strictly, by a pure cardinality argument. So checking automaton-language containment for singleton suffixes automatically gets you the strict form for free — no separate strictness check needed. But the paper is careful to show this doesn't fully close the gap: even $L(\varphi') \subset L(\varphi)$ only implies $\varphi' \sqsubseteq \varphi$, not $\varphi' \sqsubset \varphi$ (their concrete counterexample: $\varphi = (F(X) \Rightarrow F(0))$, where $\mathrm{accel}(\varphi) \equiv_A \varphi$ semantically but $L(\varphi) \subset L(\mathrm{accel}(\varphi))$ syntactically, so $\varphi \sqsubseteq \mathrm{accel}(\varphi)$ but not $\varphi \sqsubset \mathrm{accel}(\varphi)$). **This is precisely why LoAT cannot currently prove `sat`** — Prove's soundness for the satisfiable verdict depends on genuinely-exhausted search, and a heuristic that can misfire on the strict/weak boundary risks certifying `sat` on a problem that isn't. For `unsat`, this risk doesn't arise: an over-eager Covered just means some search branches get revisited unnecessarily (a completeness/performance cost, recoverable by trying another branch), never an unsound verdict, because Refute's soundness doesn't depend on Covered's precision at all.

In Rust, the shape of this is a finite-automaton wrapper with one operation you actually call from the hot path:

```rust
struct ClauseLanguage(Automaton);   // L(φ) as a finite automaton over the "resolution-step alphabet"

impl ClauseLanguage {
    /// Sufficient, not complete: true implies φ ⊑ π, but false doesn't imply ¬(φ ⊑ π).
    fn implies_redundant(&self, other: &ClauseLanguage) -> bool {
        self.language_included_in(other)   // complement + intersect + emptiness, via libFAUDES-equivalent
    }
}
```

The comment on `implies_redundant` is the important part of this design: any caller of this function has to be written knowing a `false` result is not evidence of anything, only a `true` result is actionable.

## Step–SMT: finding an active clause without an oracle

**Step** needs to find some $\varphi \in \mathrm{sip}(\Pi)$ that is *active* — not blocked, and extending the trace with it keeps the accumulated condition satisfiable. Rather than enumerating $\mathrm{sip}(\Pi)$ explicitly (which can be exponential, since $\mathrm{sip}$ ranges over every literal-selection from a constraint), LoAT searches for a witnessing model **on the fly**, directly via SMT. Given a candidate clause $\varphi$ that unifies (via mgu $\theta$) with the trace's current resolvent, the tool queries an SMT solver for satisfiability of:

$$\theta(\mathrm{cond}(\mathrm{res}(\vec\varphi))) \wedge \theta(\mathrm{cond}(\varphi)) \wedge \bigwedge_{\pi \in B \cap \mathrm{sip}(\varphi)} \neg\theta(\mathrm{cond}(\pi)) \tag{Step–SMT}$$

Read left to right: the trace-so-far's accumulated condition, conjoined with $\varphi$'s own condition, conjoined with the *negation* of every blocked clause's condition that could otherwise have been chosen instead. Any model $\sigma$ of this formula both witnesses satisfiability of the extended trace *and*, via $\mathrm{sip}(\mathrm{cond}(\varphi), \sigma)$, tells you exactly *which* syntactic implicant of $\varphi$ to actually push onto the trace — you never materialize the full $\mathrm{sip}(\varphi)$ set, you let the SMT model pick out one member of it lazily.

**Why only $\pi \in B \cap \mathrm{sip}(\varphi)$, not all of $B$?** This is a genuine subtlety worth sitting with, because the naive fix (conjoin negated conditions of every blocked clause, unconditionally) is *semantically wrong*, not just wasteful. The exact exclusion condition (⊑–equiv) needs an existentially-quantified check — $\models_A \psi_{\varphi'} \Rightarrow \exists \vec Y_\pi.\, \psi_\pi$ — and SMT solvers handle quantifiers poorly. So the paper substitutes a **sufficient** approximation (⊑–sufficient): drop the quantifier and just check $\models_A \psi_{\varphi'} \Rightarrow \psi_\pi$ directly, which only makes sense when $\pi$'s extra existential variables $\vec Y_\pi$ are already a subset of $\varphi$'s own variables $\vec Y_\varphi$ — precisely the case guaranteed when $\pi \in \mathrm{sip}(\varphi)$. Widen the check beyond $\mathrm{sip}(\varphi)$ and you'd be comparing conditions over mismatched variable sets, which the sufficient approximation isn't licensed to do. This is a small, very SMT-engineering-flavored lesson: **an approximation's validity is scoped exactly as far as the variable-hygiene argument that justified dropping the quantifier — no further.**

When several blocked clauses land in $B \cap \mathrm{sip}(\varphi)$ at once, the same quantifier-avoidance problem recurs one level up (⊑–sufficient⁺ needs a *disjunction* of implications, which is again awkward to encode directly), and the paper substitutes a **necessary-but-not-sufficient** stand-in (⊑–insufficient⁺) that excludes strictly more implicants than the ideal check would — proven safe by an equivalent-CHC-problem argument (excluding a few extra, already-redundant implicants can be simulated by having removed them from $\Pi$ in the first place, which changes nothing observable). This is the same craft pattern as the redundancy check above: **when the exact semantic condition isn't SMT-encodable, replace it with a directionally-safe approximation and prove which failure mode you've accepted (missed opportunities, never unsoundness).**

## Incremental SMT: don't re-derive what you already know

A naive implementation would build a fresh SMT query from scratch at every Step. LoAT instead keeps a **persistent SMT solver stack** and pushes/pops incrementally:

- On **Step**, construct $\theta$ so that it's a pure variable-renaming that leaves $\mathrm{cond}(\mathrm{res}(\vec\varphi))$ syntactically unchanged (always possible, since predicate arguments are duplicate-free disjoint variable vectors — see [[Constrained-Horn-Clauses-(CHCs)]]), then push only the *new* conjunct $\theta(\mathrm{cond}(\varphi)) \wedge \bigwedge \neg\theta(\mathrm{cond}(\pi))$ onto the solver. If the solver's *existing* model already happens to satisfy the new conjunct, it can often extend that model directly rather than re-searching. On backtrack, pop.
- On **Accelerate**, pop the old suffix's conditions and push the new accelerated clause's condition — same stack discipline, applied to a bulk replacement instead of a single extension.
- Two rules need **no SMT query at all**: once the trace's last element is a query, satisfiability of the whole trace is already an invariant of the calculus, so **Refute** applies for free; and once Step has been exhaustively tried and failed, **Backtrack**/**Prove** apply without a further check.

What breaks without incrementality: every Step or Accelerate would restart the SMT solver's internal search from nothing, discarding all the theory-lemma and clause-learning state the solver itself accumulated on the previous, closely-related query — turning a proof search that's already exponential in the worst case into one that also pays a full SMT-solve's constant factor at every single node, instead of amortizing it. This is the direct CHC-calculus analogue of why an incremental SAT solver's `push`/`pop` API exists at all.

```rust
struct IncrementalSolver {
    stack: Vec<Constraint>,       // one frame per trace position, mirrors the trace 1:1
}
impl IncrementalSolver {
    fn push_step(&mut self, theta_cond_phi: Constraint, blocked_negations: Constraint) {
        self.stack.push(theta_cond_phi.and(blocked_negations));   // solver internally reuses prior state
    }
    fn pop(&mut self) { self.stack.pop(); }   // mirrors Backtrack/Covered's bt()
}
```

## Living with incomplete oracles: the honest bill

The paper enumerates exactly which guarantees each approximation gives up — worth reading as a checklist for anyone building a similar solver:

1. **SMT failure → assumed inactive.** If the solver can't decide Step–SMT's satisfiability (times out, or the theory fragment is undecidable), LoAT treats the candidate clause as inactive rather than blocking. This can only cause **missed refutations** — the search space explored is a subset of what a perfect oracle would explore — never a false refutation, since a wrongly-accepted active clause would have had to pass a real SMT check to be used at all.
2. **Under-approximating acceleration.** LoAT's `accel` may return $\mathrm{grnd}(\mathrm{accel}(\varphi)) \subseteq \bigcup_n \mathrm{grnd}(\varphi^n)$ rather than equality. This is harmless for soundness by itself (a learned clause is still logically entailed by $\Phi$, so using it in a resolution proof stays valid) — but it *does* poison the redundancy heuristic above, since $L$'s exactness relied on $\mathrm{grnd}(\varphi) = \mathrm{grnd}(L(\varphi))$, which under-approximation breaks (you now only get $\subseteq$).
3. **Inconsistent-trace risk from under-approximation, and the guard against it.** If $\vec\varphi^\circlearrowleft \not\sqsubseteq \mathrm{accel}(\vec\varphi^\circlearrowleft)$ (possible precisely because acceleration under-approximates), naively swapping the suffix for its acceleration could leave the trace's accumulated condition unsatisfiable — a *broken invariant*, since satisfiability of the trace is supposed to hold at every reachable state. LoAT's guard: only actually apply Accelerate if doing so is checked to preserve consistency. This is a runtime safety check compensating for a static guarantee the idealized calculus assumed but the implementation can't fully deliver.

All three points share the same shape: **the idealized oracle assumed in [[The-ADCL-Calculus]] is replaced by a procedure that can only fail in one, characterized direction** — never spuriously succeed. This is exactly the discipline a Rust CSP-kernel's own approximate propagators or bounded solvers need: an "unknown" answer from a timed-out sub-solver must always be treated as "explore more," never silently coerced into an "impossible."

## Restarts: heavy-tail behavior and the Luby sequence

Empirically, the authors observed **"jiggling"** — the same instance solved on some runs, failing on others, purely from search-order sensitivity. This is the well-known **heavy-tail phenomenon** from SAT solving: a depth-first search can get pathologically stuck exploring one expensive subtree, even when an easy solution sits in a completely different, unvisited part of the search space — made worse here by the fact that ADCL derivations can be genuinely non-terminating (Theorem 18, see [[Metatheoretic-Properties-of-ADCL]]), so there's no guaranteed depth at which backtracking would eventually surface the easy branch on its own.

LoAT borrows SAT solving's standard countermeasure: **Luby-sequence restarts** [Luby, Sinclair, Zuckerman], with scaling parameter $u = 10$. The Luby sequence determines *how many events* (SAT solvers count conflicts; LoAT counts *learned clauses*, i.e. Accelerate applications) must occur before the next restart, growing in a specific non-monotonic pattern ($1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, \dots$) proven near-optimal for expected total search cost under heavy-tail assumptions, without needing to know in advance *how* heavy the tail is. On restart: clear the trace, reseed the SMT solver (so it may return different models and thus explore different syntactic implicants next time), and shuffle the clause-selection order — three independent sources of randomization, each aimed at making the *next* attempt structurally different from the one that got stuck, rather than replaying the same doomed trajectory.

**What breaks without restarts:** nothing about soundness or eventual completeness — refutational completeness (Theorem 15) holds regardless. What breaks is *practical, expected* solving time: without restarts, a single unlucky ordering choice near the root of the search can commit the depth-first strategy to an astronomically expensive subtree with no mechanism to abandon it short of that subtree's own (possibly non-existent) termination.

## Where this leads

This section is the bridge between [[The-ADCL-Calculus]]'s idealized transition system and [[Metatheoretic-Properties-of-ADCL]]'s theorems — it shows precisely which of those theorems' guarantees survive contact with real, incomplete SMT/automata/acceleration procedures (unsat-soundness survives fully; sat-soundness does not, which is the concrete, traceable reason LoAT only attempts `unsat`). It also directly sets up [[Empirical-Evaluation]]: the redundancy heuristics, incremental solving, and restart strategy described here are exactly the engineering choices that determine the wall-clock numbers reported against Spacer, Eldarica, Golem, and Z3 BMC — the benchmark results measure this section, not the abstract calculus.

For the standing project (`sat-smt-csp`), this section is close to a direct implementation checklist for the CSP kernel's solver backend: an incremental-SMT-backed constraint stack with push/pop mirroring search-tree structure, a language/automaton-based redundancy pre-filter ahead of expensive exact checks, an explicit and auditable list of "which failure mode does each approximation risk" for every non-exact sub-procedure, and a Luby-style restart schedule for any depth-first search over a domain (like Horn-clause resolution, or constraint propagation over abstract lattices) that can exhibit the same non-terminating-branch heavy-tail risk.
