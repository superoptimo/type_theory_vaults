# ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses — Guidelines

## Header

**Title:** ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses
**Author(s):** Florian Frohn, Jürgen Giesl (LuFG Informatik 2, RWTH Aachen University)
**Publication:** arXiv:2303.01827v3 [cs.LO], 2023 (extended version of a conference paper)

**Brief Summary:**
This paper introduces ADCL (Acceleration Driven Clause Learning), a calculus for (dis)proving satisfiability of Constrained Horn Clauses (CHCs) that integrates loop-acceleration techniques directly into a resolution-based proof search. Its central idea is that instead of unrolling recursive CHCs one resolution step at a time, ADCL can "learn" an accelerated clause characterizing the $N$-fold closure of a recursive derivation, collapsing what might be thousands of ordinary resolution steps into a handful of steps with the learned clause. The calculus is proven sound and refutationally complete, but not terminating in general, and is implemented in the tool LoAT, which the authors evaluate empirically against state-of-the-art CHC-SAT solvers (Spacer, Eldarica, Golem, Z3 BMC).

**Intent of the Author:**
The authors aim to show that loop acceleration — previously used mainly in static program analysis and for computing loop closures — can be repurposed as a first-class clause-learning mechanism inside a resolution calculus for CHC satisfiability, and to demonstrate via LoAT that this yields both competitive solving power and dramatically shorter refutation proofs on benchmarks with deep counterexamples.

---

## Topic List

1. **Constrained Horn Clauses (CHCs)** : [[Constrained-Horn-Clauses-(CHCs)|Link]]
   - Facts, rules, queries, and conditional empty clauses
   - Linear CHCs and recursive CHCs
   - CHC problems and $A$-interpretations : [[Constrained-Horn-Clauses-(CHCs)|Link]]
   - Ground instances of a CHC : [[Constrained-Horn-Clauses-(CHCs)|Link]]
   - CHC-SAT as a verification-condition formalism

2. **Resolution for CHCs** : [[Resolution-for-CHCs|Link]]
   - Most general unifiers and syntactic unification
   - Resolvents and resolution over sequences of CHCs : [[Resolution-for-CHCs|Link]]
   - Refutations as conditional empty clauses with satisfiable conditions : [[Resolution-for-CHCs|Link]]
   - Soundness and lifting lemmas for resolution : [[Resolution-for-CHCs|Link]]
   - Forward vs. backward reasoning : [[The-ADCL-Calculus|Link]]

3. **Syntactic Implicants and Redundancy** : [[Syntactic-Implicants-and-Redundancy|Link]]
   - Syntactic implicant projection : [[Syntactic-Implicants-and-Redundancy|Link]]
   - Computing implicants on the fly via SMT models : [[Syntactic-Implicants-and-Redundancy|Link]]
   - The redundancy relation between CHCs
   - Blocking clauses to prune the search space : [[Syntactic-Implicants-and-Redundancy|Link]]

4. **Loop Acceleration** : [[Loop-Acceleration|Link]]
   - The $N$-fold closure of a transition relation
   - Acceleration as a function on recursive conjunctive CHCs : [[Syntactic-Implicants-and-Redundancy|Link]]
   - Theories not closed under acceleration : [[Loop-Acceleration|Link]]
   - Monotonicity-based acceleration techniques : [[Loop-Acceleration|Link]]
   - Decidable acceleration classes (Difference Bounds, Octagons, Vector Addition Systems with States)

5. **The ADCL Calculus** : [[The-ADCL-Calculus|Link]]
   - States as CHC problem, trace, and blocking-clause sequence
   - The Init, Step, Accelerate, Covered, Backtrack, Refute, and Prove rules
   - The backtrack function : [[The-ADCL-Calculus|Link]]
   - Learned clauses vs. original clauses
   - Reasonable strategies for rule application : [[The-ADCL-Calculus|Link]]

6. **Metatheoretic Properties of ADCL** : [[Metatheoretic-Properties-of-ADCL|Link]]
   - Soundness of ADCL
   - Absence of stuck normal forms : [[Metatheoretic-Properties-of-ADCL|Link]]
   - Refutational completeness : [[Metatheoretic-Properties-of-ADCL|Link]]
   - Non-termination in general, even under a reasonable strategy
   - Regular-language characterization of ground instances via the mapping $L$

7. **Implementing ADCL in LoAT** : [[Implementing-ADCL-in-LoAT|Link]]
   - Redundancy checking via finite-automata language inclusion : [[Implementing-ADCL-in-LoAT|Link]]
   - Encoding activity checks as SMT queries (Step–SMT)
   - Incremental SMT solving for the proof search
   - Handling incompleteness of redundancy, SMT, and acceleration oracles
   - Restarts and heavy-tail behavior in the search : [[Implementing-ADCL-in-LoAT|Link]]

8. **Related Approaches to CHC-SAT and Loop Summarization** : [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Link]]
   - Accelerating interpolants and CEGAR-based acceleration : [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Link]]
   - Transition power abstraction : [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Link]]
   - IC3/Spacer/GPDR-style abstraction refinement : [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Link]]
   - Flat acceleration and flattable transition systems : [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Link]]
   - Acceleration for arrays and Boolean variables : [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Link]]

9. **Empirical Evaluation** : [[Empirical-Evaluation|Link]]
   - The CHC Competition benchmark set (LIA-Lin category) : [[Empirical-Evaluation|Link]]
   - Comparison with Spacer, Eldarica, Golem, and Z3 BMC
   - Refutation-length comparisons between accelerated and original proofs : [[Empirical-Evaluation|Link]]
   - Support for Boolean variables via deterministic closed-form acceleration : [[Empirical-Evaluation|Link]]

---

## Chapter Summaries

### Section 1: Introduction (pp. 1–3)

**Summary:** Motivates CHC-SAT as central to automated program verification and introduces the paper's core idea: using acceleration to collapse repeated recursive resolution steps, illustrated by an example where 10001 ordinary resolution steps are replaced by 3 steps using two learned clauses.

**Key Definitions & Concepts:**
- **Constrained Horn Clauses (CHCs)** — first-order formulas expressing verification conditions, built from facts, rules, and queries.
- **Acceleration technique** — a method for computing a formula characterizing the $N$-fold closure of a loop's transition relation.
- **Acceleration Driven Clause Learning (ADCL)** — the paper's novel calculus that learns accelerated clauses during resolution-based CHC-SAT proof search; refutationally complete but not guaranteed to terminate.
- **Counterexample witness** — a resolution proof ending in a conditional empty clause $\psi \Rightarrow \bot$, together with a model of $\psi$, instantiated to yield a concrete program run reaching an error state.

**Key Questions:**
1. Why does replacing repeated resolution steps with a single accelerated clause reduce proof length so drastically, and what property of the accelerated clause makes this valid?
2. In what sense is ADCL "refutationally complete but not necessarily terminating," and why are these two properties not in tension?

---

### Section 2: Preliminaries (pp. 3–6)

**Summary:** Formalizes CHCs, ground instances, $A$-interpretations, and ordinary resolution over CHCs, then defines acceleration abstractly as a function preserving the exact set of ground instances reachable by any positive number of repetitions of a recursive clause.

**Key Definitions & Concepts:**
- **CHC forms** — fact ($\psi \Rightarrow G(\vec Y)$), rule ($F(\vec X) \wedge \psi \Rightarrow G(\vec Y)$), query ($F(\vec X) \wedge \psi \Rightarrow \bot$), conditional empty clause ($\psi \Rightarrow \bot$).
- **Recursive / conjunctive CHC** — a rule is recursive if $F = G$; conjunctive if $\psi$ is a conjunction of literals.
- **$A$-interpretation, model, validity** — semantic apparatus over a many-sorted background theory $A$, assumed complete.
- **grnd($\varphi$)** — the set of ground instances of a CHC, obtained by instantiating variables according to models of its condition.
- **Resolution (Def. 2)** — resolvent of two CHCs via most general unifier $\theta$ on the shared predicate literal; lifted to sequences of CHCs.
- **Acceleration (Def. 4)** — a function `accel` mapping a recursive conjunctive CHC $\varphi$ to a CHC whose ground instances equal $\bigcup_{n \geq 1} \mathrm{grnd}(\varphi^n)$.
- **Closure under acceleration** — most theories are not closed under acceleration (e.g., linear arithmetic accelerates to formulas containing multiplication like $N \cdot Y$), which is why the paper commits to many-sorted logic and may need to switch theories mid-proof.

**Key Questions:**
1. Why must acceleration be restricted to conjunctive CHCs in this framework, and what role do syntactic implicants (Section 3.1) play in lifting this restriction to non-conjunctive CHCs?
2. Give an example of a theory that is not closed under acceleration, and explain the practical consequence this has for implementing ADCL.

---

### Section 3: Acceleration Driven Clause Learning (pp. 6–15)

**Summary:** The technical core of the paper: defines syntactic implicant projection and the redundancy relation (3.1), then presents the ADCL calculus itself as a set of inference rules over states consisting of a CHC problem, a resolution trace, and blocking-clause sets (3.2), and finally establishes ADCL's soundness, absence of stuck states, refutational completeness, and non-termination (3.3).

**Key Definitions & Concepts by Section:**
- **3.1 Syntactic Implicants and Redundancy** — `sip($\psi$, $\sigma$)` (the conjunction of literals of $\psi$ satisfied by model $\sigma$), `sip($\varphi$)` lifted to CHCs and CHC sets; the **redundancy relation** $\varphi \sqsubseteq \pi$ ($\mathrm{grnd}(\varphi) \subseteq \mathrm{grnd}(\pi)$) and its strict form $\varphi \sqsubset \pi$; oracles assumed for redundancy, satisfiability, and acceleration. : [[Syntactic-Implicants-and-Redundancy|Link]]
- **3.2 The ADCL Calculus** — **State** (Def. 9): a triple $(\Pi, [\varphi_i], [B_i])$ of CHC problem, trace, and blocking-clause sequence; **active** vs. **blocked** clauses; the rules **Init**, **Step** (extends the trace with an active clause), **Accelerate** (replaces a recursive trace suffix with its accelerated clause and collapses the corresponding blocking sets), **Covered** (backtracks a redundant trace suffix), **Backtrack** (backtracks when no clause is active), **Refute** (trace ends in a refutation $\Rightarrow$ unsat), **Prove** (all facts/conditional empty clauses blocked $\Rightarrow$ sat). : [[The-ADCL-Calculus|Link]]
- **3.3 Properties of ADCL** — **Theorem 12 (Soundness)**; **Theorem 13 (Normal Forms)** — the only normal forms are `sat`/`unsat`; **Definition 14 (Reasonable Strategy)** — four conditions (prefer Covered when applicable, prefer Accelerate over Step, accelerate shortest non-redundant recursive suffixes first, only Step from facts/conditional empty clauses when the trace is empty) that rule out pathological derivations; **Theorem 15 (Refutational Completeness)**; **Theorem 18 (Non-Termination)** — even under a reasonable strategy, ADCL need not terminate (proved via a Thue–Morse-sequence construction of square-free resolution sequences); the auxiliary **regular-language mapping $L$** used to characterize ground instances of learned clauses. : [[Metatheoretic-Properties-of-ADCL|Link]]

**Key Questions:**
1. Why does the Accelerate rule collapse the *entire* recursive suffix's blocking-clause history into a single set $\{\varphi\}$ rather than preserving it — what soundness/redundancy property (`res($\varphi$, $\varphi$) $\sqsubseteq$ $\varphi$`) justifies this?
2. What is the role of the Covered rule's asymmetric treatment of single-clause vs. multi-clause redundant suffixes, and why would omitting this distinction risk falsely "proving" satisfiability?
3. How does the non-termination proof (Thm. 18) use the Thue–Morse sequence, and why does non-termination for satisfiable problems not contradict refutational completeness for unsatisfiable ones?

---

### Section 4: Implementing ADCL (pp. 15–19)

**Summary:** Describes how the abstract ADCL calculus (which assumes oracles for redundancy, SMT, and acceleration) is realized concretely in the tool LoAT, including automata-based redundancy checks, SMT encodings for activity checking, incremental SMT solving, and restart strategies to counter heavy-tailed search behavior.

**Key Definitions & Concepts:**
- **Redundancy via $L$ and finite automata** — checks $L(\vec\varphi^\circlearrowleft)^+ \subseteq L(\varphi)$ using libFAUDES; a sufficient but incomplete criterion for redundancy.
- **Step–SMT encoding** — an SMT query combining the resolvent's condition, the candidate clause's condition, and negated conditions of blocked clauses, to find an active clause on the fly.
- **⊑–sufficient / ⊑–insufficient⁺** — practical (incomplete) sufficient conditions used in place of the full (quantifier-heavy) redundancy check `⊑–equiv`.
- **Incremental SMT solving** — pushing/popping condition formulas onto a persistent SMT solver stack across Step and Accelerate applications, reusing prior models where possible.
- **Incompleteness handling** — treating failed SMT queries as inactivity (risking missed refutations), and under-approximating acceleration (risking inconsistent traces, mitigated by only applying Accelerate when it preserves consistency).
- **Restarts** — a Luby-sequence-based restart strategy (as in SAT solving) to counter heavy-tail behavior in the depth-first search, counting learned clauses instead of conflicts.

**Key Questions:**
1. Why is the redundancy check based on $L$ only a *sufficient*, not complete, criterion, and what practical gap does this leave (e.g., redundancy of a learned clause w.r.t. an original clause)?
2. Why can LoAT's current implementation only prove unsatisfiability and not satisfiability — trace this limitation back to specific approximations described in this section.

---

### Section 5: Related Work and Experiments (pp. 19–23)

**Summary:** Surveys closely related CHC-SAT and loop-acceleration approaches (accelerating interpolants, transition power abstraction, IC3/Spacer/GPDR, flat acceleration, array/Boolean acceleration techniques) and reports an empirical comparison of LoAT against Spacer, Eldarica, Golem, and Z3 BMC on the CHC Competition's LIA-Lin benchmark set, showing LoAT is highly competitive for proving unsatisfiability and dramatically shortens refutation proofs on hard instances.

**Key Definitions & Concepts:**
- **Accelerating interpolants [Hojjat et al.]** — the most closely related prior work, using acceleration as preprocessing or to generalize interpolants in a CEGAR loop; contrasted with ADCL's "on the fly" acceleration of arbitrary (not just conjunctive) clauses.
- **Transition Power Abstraction (TPA)** — computes over-approximating sequences capturing $2^n$ steps, analogous in spirit to ADCL but relying on over-approximation.
- **IC3/GPDR/Spacer** — abstraction-based CHC-SAT algorithms generalizing IC3 from transition systems to CHCs over theories.
- **Flat acceleration / flattable systems** — analyzing sequences of loop flattenings; ADCL's relation to flattable-system termination is left as an open question.
- **CHC Competition LIA-Lin benchmark** — the evaluation suite (linear CHCs over linear integer arithmetic, some with Bool/div/mod), used to compare solved-instance counts, uniquely-solved instances, and runtime distributions.
- **Refutation-length comparison (Table 1)** — LoAT's accelerated refutations use single-digit to low-double-digit resolution steps versus hundreds of thousands to over $6\times10^8$ steps for original-clause-only refutations on the same instances.

**Key Questions:**
1. How does ADCL's approach to acceleration differ from Eldarica's "acceleration as preprocessing" and from the CEGAR-based interpolant generalization of [Hojjat et al.], and what capability does this difference unlock (e.g., for finding long counterexamples)?
2. What does Table 1's comparison of refutation lengths reveal about *why* LoAT solves certain instances that other tools cannot, beyond simply "it's faster"?

---

### Appendices A–C: Additional Definitions and Missing Proofs (pp. 26–38)

**Summary:** Provides the ground-instance formulation of resolution, auxiliary lemmas (distributivity of resolution over `grnd`, associativity of resolution, composition of ground instances, distributivity over $L$), and the full proofs of Soundness (Thm. 12), Normal Forms (Thm. 13), and Refutational Completeness (Thm. 15) that were only sketched in the main text.

**Key Definitions & Concepts:**
- **Resolution with ground instances (Def. 20)** and its lifting to sets/sequences (Def. 21).
- **Lemma 22 (Resolution Distributes over grnd)** and **Lemma 23 (Associativity of Resolution)** — the technical backbone used throughout the soundness and completeness proofs.
- **The relation $\succ_\Pi$ (Def. 27)** — a well-founded ordering on traces (Lemma 28) used to formalize "minimality" of a refutation trace in the soundness proof for `sat`.

**Key Questions:**
1. Why is a well-founded ordering ($\succ_\Pi$) needed to prove soundness of the `sat` verdict specifically, while `unsat` soundness follows directly from soundness of resolution?

---
