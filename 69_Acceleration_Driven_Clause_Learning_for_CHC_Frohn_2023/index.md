# ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses — Index

[[book-guidelines|↩ Back to guidelines]]

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
