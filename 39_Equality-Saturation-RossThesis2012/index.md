# Equality Saturation: Using Equational Reasoning to Optimize Imperative Functions — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Program Expression Graphs (PEGs)** : [[Program-Expression-Graphs-(PEGs)|Link]]
   - PEGs as referentially transparent algebraic representations of imperative code
   - Theta nodes for values that vary across loop iterations : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Phi nodes as executable gated-SSA selectors : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Eval and pass nodes for extracting post-loop values and termination iteration : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Loop lifting and bottom lifting of node semantics : [[Program-Expression-Graphs-(PEGs)|Link]]
   - PEG well-formedness conditions : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Parameter nodes and substitution : [[Program-Expression-Graphs-(PEGs)|Link]]
   - Built-in PEG axioms and the invariance predicate : [[Program-Expression-Graphs-(PEGs)|Link]]
   - E-PEGs as equivalence classes of equal PEG nodes : [[Program-Expression-Graphs-(PEGs)|Link]]

2. **Equality Saturation** : [[Equality-Saturation|Link]]
   - Optimizations as additive equality analyses rather than destructive rewrites : [[Equality-Saturation|Link]]
   - Equality analyses as trigger-and-callback rules
   - The Optimize pipeline of conversion, saturation, selection, and reversion : [[Equality-Saturation|Link]]
   - Monotonic equality analyses and the additivity property : [[Equality-Saturation|Link]]
   - Uniqueness of normal form and confluence of saturation : [[Equality-Saturation|Link]]
   - Non-termination of saturation and bounding the search : [[Equality-Saturation|Link]]
   - Elimination of the phase-ordering problem : [[Equality-Saturation|Link]]
   - Global profitability heuristics over saturated representations : [[Equality-Saturation|Link]]

3. **Converting Between Imperative Code and PEGs** : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - The SIMPLE imperative language and its typing rules : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - Type-directed translation from imperative programs to PEGs : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - Semantics preservation of the translation : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - Abstract PEGs and forward flow graphs for translating arbitrary control-flow graphs
   - CFG-like PEGs as the target form for reversion
   - Reversion of PEGs back into loops, branches, and sequenced statements
   - Loop fusion and branch fusion during reversion : [[Converting-Between-Imperative-Code-and-PEGs|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]]
   - Hoisting redundancies and loop-invariant code motion during reversion : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link1]], [[Converting-Between-Imperative-Code-and-PEGs|Link2]]
   - Guarded PEG contexts and CFG nodes for break and continue : [[Converting-Between-Imperative-Code-and-PEGs|Link]]

4. **Representing Effects in PEGs** : [[Representing-Effects-in-PEGs|Link]]
   - Heap-summary values threaded through load and store : [[Representing-Effects-in-PEGs|Link]]
   - Effect witnesses for exceptions and non-termination : [[Converting-Between-Imperative-Code-and-PEGs|Link]]
   - PEGs as string diagrams with multiple outputs
   - Premonoidal and monoidal categories as the semantic model of effects : [[Representing-Effects-in-PEGs|Link]]
   - The center of a premonoidal category
   - Partially monoidal categories for effect witnesses : [[Representing-Effects-in-PEGs|Link]]

5. **Loop and Branch Optimizations Discovered by Saturation** : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - Loop-induction-variable strength reduction : [[Learning-Optimizations-from-Proofs|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]]
   - Inter-loop strength reduction : [[Evaluation-of-Learning|Link1]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link2]]
   - Loop-based code motion via distributing through eval and theta : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - CFG restructuring from local PEG rewrites : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - Loop peeling : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]
   - Branch hoisting : [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link]]

6. **The Peggy Implementation** : [[The-Peggy-Implementation|Link]]
   - Representing the heap and method calls with sigma and invoke nodes : [[The-Peggy-Implementation|Link]]
   - The linearization problem for effect witnesses : [[The-Peggy-Implementation|Link]]
   - The Rete algorithm for efficient trigger matching : [[The-Peggy-Implementation|Link]]
   - The pseudo-boolean solver for global profitability : [[The-Peggy-Implementation|Link]]
   - The cost model based on operation cost and loop depth
   - Rationale for keeping eval and pass as separate nodes : [[The-Peggy-Implementation|Link]]

7. **Empirical Evaluation of Optimization** : [[Empirical-Evaluation-of-Optimization|Link]]
   - Time and space overhead of saturation on Java benchmarks : [[Empirical-Evaluation-of-Optimization|Link]]
   - Emergent optimizations arising from simple built-in axioms : [[Evaluation-of-Learning|Link1]], [[Empirical-Evaluation-of-Optimization|Link2]], [[Loop-and-Branch-Optimizations-Discovered-by-Saturation|Link3]]
   - Domain-specific axioms and their optimizations : [[Empirical-Evaluation-of-Optimization|Link]]
   - Safety of additive axioms compared to destructive rewrite rules

8. **Translation Validation** : [[Translation-Validation|Link]]
   - Proving program equivalence by saturating a combined E-PEG
   - Alias-dependent load and store axioms : [[Translation-Validation|Link]]
   - Proof generation as a byproduct of validation : [[Translation-Validation|Link]]
   - Validation results against Soot and LLVM : [[Translation-Validation|Link]]
   - Discovery of a real compiler bug through translation validation : [[Translation-Validation|Link]]

9. **Learning Optimizations from Proofs** : [[Learning-Optimizations-from-Proofs|Link]]
   - Generalizing a concrete optimization instance into a general rule
   - The splitting problem in naive generalization
   - Working backward through a proof to generalize correctly : [[Learning-Optimizations-from-Proofs|Link]]
   - Decomposition of an overly specific learned rule : [[Learning-Optimizations-from-Proofs|Link]]
   - Sequencing versus parallelizing axiom applications : [[Learning-Optimizations-from-Proofs|Link]]
   - Removing irrelevant axiom applications automatically : [[Learning-Optimizations-from-Proofs|Link]]

10. **Category-Theoretic Foundations of Proof Generalization** : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Categories, morphisms, and commuting diagrams : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Axioms encoded as identity-carried morphisms : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Pushouts as the formal model of applying an axiom : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Pullbacks as the formal model of isolating shared structure : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Pushout completions and subpushout completions : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - The proof of maximal generality of a learned rule : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Instantiating the categorical framework for E-PEGs : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]
    - Coproducts and the encoding of parallel axiom applications : [[Category-Theoretic-Foundations-of-Proof-Generalization|Link]]

11. **Domain-Independent Applications of Generalization** : [[Domain-Independent-Applications-of-Generalization|Link]]
    - Database query optimization via conjunctive queries and the chase : [[Domain-Independent-Applications-of-Generalization|Link1]], [[Equality-Saturation|Link2]]
    - Functional and multi-valued dependencies
    - Type debugging by generalizing backward through a typing proof : [[Domain-Independent-Applications-of-Generalization|Link]]
    - Automatic type polymorphization : [[Domain-Independent-Applications-of-Generalization|Link]]

12. **Evaluation of Learning** : [[Evaluation-of-Learning|Link]]
    - Learning new optimizations from single before-and-after examples : [[Evaluation-of-Learning|Link]]
    - Amortizing superoptimizer cost by learning rules from one run : [[Evaluation-of-Learning|Link]]
    - Partial inlining as a byproduct of learning : [[Evaluation-of-Learning|Link]]
    - Cross-training learned rules on unseen code : [[Evaluation-of-Learning|Link]]

13. **Related Work and Positioning** : [[Related-Work-and-Positioning|Link]]
    - Superoptimizers as inspiration for additive equality reasoning : [[Equality-Saturation|Link]]
    - Destructive rewrite-based optimizers and the phase-ordering problem : [[Related-Work-and-Positioning|Link]]
    - Value Dependence Graphs and the problem of intermediate variables : [[Related-Work-and-Positioning|Link]]
    - Program Dependence Graphs, Dependence Flow Graphs, and Lucid : [[Related-Work-and-Positioning|Link]]
    - Theorem proving and E-graphs as ancestors of E-PEGs : [[Related-Work-and-Positioning|Link]]
    - Explanation-based learning and machine-learned compiler heuristics : [[Related-Work-and-Positioning|Link]]
    - Open challenges in interprocedural optimization

---
