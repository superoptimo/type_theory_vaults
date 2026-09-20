# Pseudo-Boolean Reasoning and Compilation — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Propositional Logic Foundations** : [[Propositional-Logic-Foundations|Link]]
   - Formulae literals clauses and CNF : [[Propositional-Logic-Foundations|Link]]
   - Boolean functions and interpretations : [[Propositional-Logic-Foundations|Link]]
   - Logical entailment equivalence and validity : [[Propositional-Logic-Foundations|Link]]
   - Negation normal form circuits : [[Knowledge-Compilation|Link]]
   - Decomposability and determinism DNNF and d-DNNF : [[Propositional-Logic-Foundations|Link1]], [[Knowledge-Compilation|Link2]]
   - Binary decision diagrams and their ordered and free variants : [[Knowledge-Compilation|Link1]], [[Propositional-Logic-Foundations|Link2]]

2. **Pseudo-Boolean and Cardinality Constraints** : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Pseudo-Boolean constraints as weighted linear inequalities over literals : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Normalized form of a pseudo-Boolean constraint : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Cardinality constraints as unit-coefficient pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Size of a pseudo-Boolean constraint : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Non-uniqueness of normalized representations and the increasible-degree problem : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - CNF representation versus CNF encoding of a pseudo-Boolean constraint : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Equisatisfiability and auxiliary variables : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]

3. **Computational Complexity Preliminaries** : [[Computational-Complexity-Preliminaries|Link]]
   - Running time and worst-case complexity of an algorithm : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
   - Big-O big-Omega and big-Theta notation
   - Complexity classes P NP and coNP : [[Computational-Complexity-Preliminaries|Link]]
   - Polynomial reduction hardness and completeness : [[Computational-Complexity-Preliminaries|Link]]
   - NP-completeness of propositional satisfiability

4. **Knowledge Compilation** : [[Knowledge-Compilation|Link]]
   - Compiling a representation offline to support efficient online queries
   - The knowledge compilation map and its criteria : [[Knowledge-Compilation|Link1]], [[Propositional-Logic-Foundations|Link2]]
   - Expressiveness and succinctness of a representation language : [[Knowledge-Compilation|Link]]
   - Polynomial-time queries consistency validity and entailment
   - Polynomial-time transformations conditioning forgetting and closure

5. **Succinctness and Tractability of Pseudo-Boolean Languages** : [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link]]
   - Single-constraint languages 1-PBC and 1-CARD : [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link]]
   - PBC and CARD as conjunctions of pseudo-Boolean or cardinality constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Succinctness of pseudo-Boolean languages relative to CNF and other compilation languages : [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link]]
   - Tractable queries preserved from CNF to pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Intractability of forgetting and of bounded disjunction for pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
   - Hardness of counting models of a pseudo-Boolean constraint : [[Pseudo-Boolean-and-Cardinality-Constraints|Link1]], [[Resolution-Based-Pseudo-Boolean-Solving|Link2]], [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link3]]

6. **Graph Width Measures for CNF Formulae and Encodings** : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
   - Primal and incidence graphs of a CNF formula : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
   - Treewidth and tree decompositions : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
   - Modular treewidth and cliquewidth : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
   - Signed incidence cliquewidth and special treewidth
   - Dependent auxiliary variables in a CNF encoding
   - Effect of auxiliary variables on the treewidth of an encoding : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
   - Equivalence of width measures for optimal encodings up to logarithmic factors

7. **Communication Complexity and Lower Bounds on Compilation** : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]
   - Combinatorial rectangles and rectangle covers : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]
   - Non-deterministic communication complexity of a Boolean function : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link1]], [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link2]]
   - Structured deterministic DNNF and v-trees : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]
   - Width of a structured DNNF as a bound on rectangle cover size : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]
   - Communication complexity lower bounds on width measures of CNF encodings : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]
   - Treewidth bounds for the at-most-one and permutation functions : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]

8. **Practical SAT Solving and the CDCL Architecture** : [[Practical-SAT-Solving-and-the-CDCL-Architecture|Link]]
   - Decisions propagations and unit propagation : [[Practical-SAT-Solving-and-the-CDCL-Architecture|Link]]
   - Pure literals and unit clauses
   - Watched literals and lazy data structures for propagation : [[Practical-SAT-Solving-and-the-CDCL-Architecture|Link]]
   - Implication graphs decision levels and conflicts
   - Conflict-driven clause learning and the unique implication point
   - Non-chronological backtracking and backjumping
   - The Davis-Putnam and DPLL algorithms

9. **Guiding the Search in CDCL SAT Solvers** : [[Guiding-the-Search-in-CDCL-SAT-Solvers|Link]]
   - The VSIDS and EVSIDS branching heuristics
   - Phase saving for choosing a variable's truth value : [[Guiding-the-Search-in-CDCL-SAT-Solvers|Link]]
   - Learned clause deletion and the literal block distance
   - Restart policies static Luby-based and dynamic
   - The resolution proof system soundness and refutation completeness : [[Computational-Complexity-Preliminaries|Link]]

10. **The Cutting Planes Proof System** : [[The-Cutting-Planes-Proof-System|Link]]
    - Axioms and inference rules addition multiplication and division
    - The generalized resolution subsystem saturation and cancellation : [[The-Cutting-Planes-Proof-System|Link]]
    - The weakening and partial weakening rules : [[The-Cutting-Planes-Proof-System|Link]]
    - p-simulation of resolution by cutting planes : [[The-Cutting-Planes-Proof-System|Link]]
    - Short cutting-planes proofs for pigeonhole-principle formulae : [[The-Cutting-Planes-Proof-System|Link]]

11. **Pseudo-Boolean Solving via Cutting Planes** : [[Pseudo-Boolean-Solving-via-Cutting-Planes|Link]]
    - Slack of a pseudo-Boolean constraint under a partial assignment : [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link1]], [[Pseudo-Boolean-and-Cardinality-Constraints|Link2]], [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link3]]
    - Assertivity and propagation detection in pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link1]], [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link2]], [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link3]], [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link4]]
    - Watched literal schemes generalized to cardinality and pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link1]], [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link2]], [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link3]]
    - Conflict analysis by cancellation and the subadditivity of the slack : [[Pseudo-Boolean-Solving-via-Cutting-Planes|Link]]
    - Coefficient growth and reduction to cardinality constraints : [[Pseudo-Boolean-Solving-via-Cutting-Planes|Link1]], [[Pseudo-Boolean-and-Cardinality-Constraints|Link2]]
    - The RoundingSat reduction and division-based conflict analysis
    - Assertion level computation for pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link1]], [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link2]], [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link3]], [[Experimental-Evaluation-of-Pseudo-Boolean-Solvers|Link4]]

12. **Resolution-Based Pseudo-Boolean Solving** : [[Resolution-Based-Pseudo-Boolean-Solving|Link]]
    - CNF encodings equisatisfiable to a pseudo-Boolean formula : [[Pseudo-Boolean-and-Cardinality-Constraints|Link1]], [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link2]]
    - Arc-consistent encodings and their preservation of propagations : [[Resolution-Based-Pseudo-Boolean-Solving|Link]]
    - Lazy clause inference from a pseudo-Boolean constraint during conflict analysis : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
    - Complementarity of resolution-based and cutting-planes-based solving : [[Resolution-Based-Pseudo-Boolean-Solving|Link]]

13. **Irrelevant Literals in Pseudo-Boolean Constraint Learning** : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
    - Irrelevant literals as literals whose value does not affect a constraint's truth : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
    - Monotonicity of literal relevance with respect to coefficients
    - Introduction of irrelevant literals by cutting-planes rules : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
    - Artificially relevant literals produced during conflict analysis : [[Resolution-Based-Pseudo-Boolean-Solving|Link1]], [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link2]]
    - Removal of irrelevant literals by weakening or by simple removal : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
    - Slack-based choice between removal strategies
    - NP-hardness of the relevance check
    - SAT-based and dynamic-programming-based detection of irrelevant literals

14. **Weakening Strategies for Pseudo-Boolean Solvers** : [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link]]
    - Effective and ineffective literals during conflict analysis : [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link]]
    - Weakening ineffective literals as a route to clause-only learning
    - Applying weakening on the conflict side versus the reason side
    - PartialRoundingSat and the partial weakening rule : [[The-Cutting-Planes-Proof-System|Link1]], [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link2]]
    - The Multiply and Weaken strategy : [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link]]
    - Tradeoffs between constraint strength and constraint size

15. **Adapting CDCL Strategies to Pseudo-Boolean Solving** : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]
    - Coefficient and degree-based variable bumping strategies : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]
    - Assignment-based and effectiveness-based variable bumping strategies : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]
    - Generalized definitions of literal block distance for pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
    - Degree and degree-size as learned-constraint quality measures : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]
    - Quality-measure-driven learned constraint deletion : [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Link1]], [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link2]]
    - Quality-measure-driven adaptive restarts : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]
    - Combining branching heuristics deletion and restart strategies : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]

16. **Experimental Evaluation of Pseudo-Boolean Solvers** : [[Experimental-Evaluation-of-Pseudo-Boolean-Solvers|Link]]
    - Sat4j as an experimental platform for cutting-planes and resolution-based solving : [[Experimental-Evaluation-of-Pseudo-Boolean-Solvers|Link]]
    - RoundingSat and its variants as a division-based reference solver : [[Experimental-Evaluation-of-Pseudo-Boolean-Solvers|Link]]
    - Cactus plots and scatter plots for comparing solver runtimes
    - The virtual best solver as an upper bound on strategy combination : [[Experimental-Evaluation-of-Pseudo-Boolean-Solvers|Link]]
    - Benchmark families used in pseudo-Boolean solver competitions : [[Resolution-Based-Pseudo-Boolean-Solving|Link1]], [[Pseudo-Boolean-and-Cardinality-Constraints|Link2]], [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link3]], [[Experimental-Evaluation-of-Pseudo-Boolean-Solvers|Link4]]

---
