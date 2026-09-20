# Handbook of Satisfiability (Second Edition) — Index

[[book-guidelines|↩ Back to guidelines]]

1. **History and Foundations of Satisfiability** : [[History-and-Foundations-of-Satisfiability|Link]]
   - Satisfiability as the semantic counterpart of syntactic consistency : [[History-and-Foundations-of-Satisfiability|Link]]
   - Syllogistic and Boolean algebraic roots of propositional logic : [[History-and-Foundations-of-Satisfiability|Link]]
   - Gödel's incompleteness theorem and the birth of computability : [[History-and-Foundations-of-Satisfiability|Link]]
   - Herbrand's theorem and Tarski's satisfaction relation : [[History-and-Foundations-of-Satisfiability|Link]]
   - The Davis-Putnam procedure and its refinement into DPLL : [[History-and-Foundations-of-Satisfiability|Link]]

2. **CNF Encodings** : [[CNF-Encodings|Link]]
   - The Tseitin encoding and subformula polarity : [[CNF-Encodings|Link]]
   - Direct, support, log, and order encodings from CSP to SAT : [[CNF-Encodings|Link]]
   - At-most-one, cardinality, and parity constraint encodings : [[CNF-Encodings|Link]]
   - The DIMACS file format : [[CNF-Encodings|Link]]
   - Encoding choices and their effect on solver performance

3. **Complete Search Algorithms for SAT** : [[Complete-Search-Algorithms-for-SAT|Link]]
   - Resolution and unit resolution : [[Complete-Search-Algorithms-for-SAT|Link]]
   - Existential quantification and directional resolution : [[Complete-Search-Algorithms-for-SAT|Link]]
   - Symbolic SAT solving via binary decision diagrams : [[Complete-Search-Algorithms-for-SAT|Link]]
   - Stålmarck's algorithm and HeerHugo : [[Complete-Search-Algorithms-for-SAT|Link]]
   - The DPLL algorithm and termination trees : [[Complete-Search-Algorithms-for-SAT|Link]]

4. **Conflict-Driven Clause Learning** : [[Conflict-Driven-Clause-Learning|Link]]
   - The implication graph and decision levels : [[Conflict-Driven-Clause-Learning|Link]]
   - Conflict analysis and asserting clauses : [[Conflict-Driven-Clause-Learning|Link]]
   - Non-chronological backtracking : [[Conflict-Driven-Clause-Learning|Link]]
   - Branching heuristics and watched literals : [[Conflict-Driven-Clause-Learning|Link]]
   - Restart policies and clause deletion : [[Conflict-Driven-Clause-Learning|Link]]

5. **Look-Ahead Solving** : [[Look-Ahead-Solving|Link]]
   - The look-ahead architecture versus conflict-driven search : [[Look-Ahead-Solving|Link]]
   - Diff and MixDiff decision heuristics
   - Failed literal detection : [[Look-Ahead-Solving|Link]]
   - Density and diameter as predictors of solver strength : [[Look-Ahead-Solving|Link]]

6. **Stochastic Local Search for SAT** : [[Stochastic-Local-Search-for-SAT|Link]]
   - GSAT and greedy descent on the clause-violation landscape
   - Walksat and the focusing strategy : [[Stochastic-Local-Search-for-SAT|Link]]
   - Clause reweighting and the Discrete Lagrangian Method : [[Stochastic-Local-Search-for-SAT|Link]]
   - Depth, mobility, and coverage as measures of search effectiveness : [[Stochastic-Local-Search-for-SAT|Link]]

7. **Proof Complexity** : [[Proof-Complexity|Link]]
   - Proof systems, soundness, and completeness : [[Proof-Complexity|Link]]
   - Resolution width and size lower bounds
   - Algebraic proof systems: Nullstellensatz and polynomial calculus : [[Proof-Complexity|Link]]
   - Cutting planes and pseudo-Boolean proof systems : [[Proof-Complexity|Link]]
   - Extended resolution, Frege, and bounded-depth Frege systems : [[Proof-Complexity|Link]]

8. **Branching Heuristic Theory** : [[Branching-Heuristic-Theory|Link]]
   - Branching tuples and the canonical projection function
   - The product rule versus the sum rule : [[Branching-Heuristic-Theory|Link]]
   - Estimating enumeration tree size : [[Branching-Heuristic-Theory|Link]]

9. **Preprocessing and Inprocessing** : [[Preprocessing-and-Inprocessing|Link]]
   - Unit propagation and failed literal detection : [[Preprocessing-and-Inprocessing|Link]]
   - Bounded variable elimination : [[Preprocessing-and-Inprocessing|Link]]
   - Blocked clause elimination and other redundancy techniques : [[Preprocessing-and-Inprocessing|Link]]
   - Solution reconstruction : [[Preprocessing-and-Inprocessing|Link]]
   - The risk of preprocessing removing resolution-critical structure : [[Preprocessing-and-Inprocessing|Link]]

10. **Random Satisfiability and Phase Transitions** : [[Random-Satisfiability-and-Phase-Transitions|Link]]
    - Random k-CNF formulas and the clause-to-variable ratio : [[Random-Satisfiability-and-Phase-Transitions|Link]]
    - The satisfiability threshold conjecture : [[Random-Satisfiability-and-Phase-Transitions|Link]]
    - The second moment method and balanced satisfying assignments : [[Random-Satisfiability-and-Phase-Transitions|Link]]
    - The algorithmic barrier below the satisfiability threshold : [[Random-Satisfiability-and-Phase-Transitions|Link]]

11. **Runtime Variation and Solver Engineering** : [[Runtime-Variation-and-Solver-Engineering|Link]]
    - Heavy-tailed and fat-tailed runtime distributions : [[Runtime-Variation-and-Solver-Engineering|Link]]
    - Backdoor sets : [[Runtime-Variation-and-Solver-Engineering|Link1]], [[Worst-Case-Complexity-and-Tractability|Link2]]
    - Restart strategies as an exploitation of runtime variance
    - Automated algorithm configuration and per-instance selection : [[Runtime-Variation-and-Solver-Engineering|Link]]

12. **Symmetry, Minimal Unsatisfiability, and Autarkies** : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]
    - Symmetry groups of Boolean functions and CNF formulas : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]
    - Symmetry breaking predicates and graph automorphism detection : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]
    - Minimally unsatisfiable formulas and formula deficiency
    - Autarkies as satisfiability-preserving partial assignments : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]

13. **Proofs of Unsatisfiability** : [[Proofs-of-Unsatisfiability|Link]]
    - Clausal proofs and the empty clause
    - Reverse unit propagation clauses
    - Hints, witnesses, and proof checking complexity : [[Proof-Complexity|Link]]
    - DRAT and formally verified proof checkers

14. **Worst-Case Complexity and Tractability** : [[Worst-Case-Complexity-and-Tractability|Link]]
    - Schaefer's dichotomy theorem : [[Worst-Case-Complexity-and-Tractability|Link]]
    - Best known upper bounds for k-SAT and general SAT : [[Worst-Case-Complexity-and-Tractability|Link]]
    - Fixed-parameter tractability and satisfiability parameters : [[Worst-Case-Complexity-and-Tractability|Link]]
    - Backdoor-based and treewidth-based parameterizations

15. **Statistical Physics of Random Constraint Satisfaction** : [[Statistical-Physics-of-Random-Constraint-Satisfaction|Link]]
    - Phase transitions and the cavity method : [[Stochastic-Local-Search-for-SAT|Link]]
    - The continuous perceptron as a solvable toy model : [[Statistical-Physics-of-Random-Constraint-Satisfaction|Link]]
    - Clustering and condensation in the solution space : [[Statistical-Physics-of-Random-Constraint-Satisfaction|Link]]
    - Survey propagation : [[Statistical-Physics-of-Random-Constraint-Satisfaction|Link1]], [[Stochastic-Local-Search-for-SAT|Link2]]

16. **Bounded Model Checking and Formal Verification** : [[Bounded-Model-Checking-and-Formal-Verification|Link]]
    - Linear temporal logic and Kripke structures
    - Bounded semantics and the (k,l)-lasso : [[Bounded-Model-Checking-and-Formal-Verification|Link]]
    - Completeness extensions to bounded model checking : [[Bounded-Model-Checking-and-Formal-Verification|Link]]
    - SAT-based software verification and predicate abstraction

17. **Planning as Satisfiability** : [[Planning-as-Satisfiability|Link]]
    - Bounded plan existence and time-indexed encodings : [[Planning-as-Satisfiability|Link]]
    - Parallel plans : [[Planning-as-Satisfiability|Link]]
    - Temporal and nondeterministic planning extensions

18. **Combinatorial Applications of SAT** : [[Combinatorial-Applications-of-SAT|Link]]
    - Quasigroups, Latin squares, and combinatorial design theory : [[Combinatorial-Applications-of-SAT|Link]]
    - Ramsey and van der Waerden numbers : [[Combinatorial-Applications-of-SAT|Link]]
    - Model generators and the encoder-solver-decoder pipeline : [[Combinatorial-Applications-of-SAT|Link]]

19. **Maximum Satisfiability** : [[Maximum-Satisfiability|Link]]
    - Weighted, partial, and weighted partial MaxSAT
    - Branch-and-bound MaxSAT algorithms : [[Maximum-Satisfiability|Link]]
    - Core-guided and implicit hitting set algorithms : [[Maximum-Satisfiability|Link]]
    - MinSAT as the dual problem : [[Maximum-Satisfiability|Link]]

20. **Model Counting** : [[Model-Counting|Link]]
    - The complexity class #P and counting reductions : [[Model-Counting|Link]]
    - Exact counting via DPLL extensions and knowledge compilation : [[Model-Counting|Link]]
    - Approximate counting via universal hashing : [[Model-Counting|Link]]
    - Toda's theorem and the relation of #P to the polynomial hierarchy : [[Model-Counting|Link]]

21. **Non-Clausal and Circuit-Based Satisfiability** : [[Non-Clausal-and-Circuit-Based-Satisfiability|Link]]
    - Boolean circuits as gates and equations : [[Non-Clausal-and-Circuit-Based-Satisfiability|Link]]
    - Observability don't cares : [[Non-Clausal-and-Circuit-Based-Satisfiability|Link]]
    - Automatic test pattern generation : [[Non-Clausal-and-Circuit-Based-Satisfiability|Link]]

22. **Pseudo-Boolean and Cardinality Constraints** : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
    - Linear and non-linear pseudo-Boolean constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
    - Atleast, atmost, and exactly cardinality constraints : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
    - Cutting-planes-style inference rules for pseudo-Boolean solving : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]

23. **Quantified Boolean Formulas** : [[Quantified-Boolean-Formulas|Link]]
    - Syntax, semantics, and prenex normal form : [[Quantified-Boolean-Formulas|Link]]
    - The satisfiability threshold theorem's QBF analogue: PSPACE-completeness : [[Quantified-Boolean-Formulas|Link]]
    - Q-resolution and the QCDCL solving paradigm : [[Quantified-Boolean-Formulas|Link]]
    - Expansion-based solving and the forall-Exp+Res proof system : [[Quantified-Boolean-Formulas|Link]]
    - Skolem and Herbrand functions as winning strategies : [[Quantified-Boolean-Formulas|Link]]
    - QRAT and preprocessing-aware certification : [[Quantified-Boolean-Formulas|Link]]

24. **SAT Techniques for Richer Logics** : [[SAT-Techniques-for-Richer-Logics|Link]]
    - Modal logic Km and the description logic ALC : [[SAT-Techniques-for-Richer-Logics|Link]]
    - Tableau-based, DPLL-based, and eager approaches to modal satisfiability
    - Satisfiability Modulo Theories : [[SAT-Techniques-for-Richer-Logics|Link]]
    - The eager and lazy approaches to SMT : [[SAT-Techniques-for-Richer-Logics|Link]]
    - Combining theory solvers : [[SAT-Techniques-for-Richer-Logics|Link]]

25. **Stochastic Boolean Satisfiability** : [[Stochastic-Boolean-Satisfiability|Link]]
    - Existential and randomized quantifiers : [[Stochastic-Boolean-Satisfiability|Link]]
    - The maximum probability of satisfaction : [[Stochastic-Boolean-Satisfiability|Link]]
    - MAJSAT, E-MAJSAT, and Extended SSAT : [[Stochastic-Boolean-Satisfiability|Link]]
    - SSAT as a unifying generalization of SAT and QBF : [[Stochastic-Boolean-Satisfiability|Link]]

---
