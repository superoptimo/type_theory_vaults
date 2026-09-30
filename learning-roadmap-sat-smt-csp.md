# Learning Roadmap — SAT/SMT/CSP

The `sat-smt-csp` Focus Area builds the *search* half of the verifier: a CSP kernel that looks for concrete counterexamples (proving bug **presence**) using domain/lattice propagation over integers, non-linear constraints and automata-shaped domains, plus the SAT/SMT backend that discharges verification conditions. The sequence starts from propositional SAT (encodings, CDCL, proofs), extends to richer logics and SMT, then turns to CSP proper — modelling, consistency, propagation, search, propagator engineering — before the specialized material the project needs (abstract-domain-based solving, integer/non-linear/continuous constraints, tractability theory, automata domains) and finally the CEGAR/CHC/symbolic-execution loop that connects the solver to the abstract interpreter. Prerequisites in other areas are cross-referenced to [[learning-roadmap-type-theory|type-theory]], [[learning-roadmap-automated-reasoning|automated-reasoning]] and [[learning-roadmap-static-analysis|static-analysis]].

---

## 1. Propositional Logic, CNF, and Encodings (Core Topic)

#### Pre-requisites
Discrete mathematics; [[learning-roadmap-automated-reasoning|automated-reasoning]] topic 1 (classical logic) is the companion.

#### Why this topic is important
SAT is the substrate of everything downstream: bounded checks, CHC/BMC back-ends and Boolean structure inside SMT. How a verification condition is *encoded* (Tseitin, cardinality, arithmetic-to-bits) determines whether the solver succeeds. Later: 2–6, 16–17.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/History-and-Foundations-of-Satisfiability|History and Foundations of Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/CNF-Encodings|CNF Encodings]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Non-Clausal-and-Circuit-Based-Satisfiability|Non-Clausal and Circuit-Based Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Worst-Case-Complexity-and-Tractability|Worst-Case Complexity and Tractability]]
2. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Sentential-Propositional-Logic|Sentential (Propositional) Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Sentential-Connectives-and-Their-Completeness|Sentential Connectives and Their Completeness]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Compactness-for-Sentential-Logic|Compactness for Sentential Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Switching-Circuits|Switching Circuits]]
3. [[15_handbook_logic_automated_reasoning_harrison_2009/Propositional-Logic|Harrison — Propositional Logic]]
4. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Propositional-Logic-Foundations|Wallon — Propositional Logic Foundations]]
5. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Computational-Complexity-Preliminaries|Wallon — Computational Complexity Preliminaries]]

#### Key Concepts and Definitions
1. CNF/DNF, satisfiability, Boolean functions; Tseitin (equisatisfiable, linear-size) vs. naive distribution.
2. Cardinality/arithmetic encodings (sequential counter, totalizer, adders).
3. NP-completeness of SAT; tractable classes (2-SAT, Horn, XOR).
4. Compactness ⇒ finite approximations of infinite theories.

#### Relevant Questions
1. Why is a Tseitin encoding equisatisfiable rather than equivalent, and what does that imply for model extraction?
2. How do you encode a bounded-integer constraint so unit propagation does most of the work?
3. Which tractable classes appear in verification conditions in practice?

---

## 2. Complete SAT Search: DPLL, CDCL, Heuristics, Preprocessing (Core Topic)

#### Pre-requisites
1. Propositional logic and CNF.

#### Why this topic is important
CDCL is the engine inside every modern SMT/CHC/PB solver; it is also the archetype for the CSP kernel's conflict analysis and learning. Understanding watched literals, 1-UIP learning, restarts and phase saving lets you build (or embed) a competitive Rust core. Later: 3, 4, 6, 9.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Complete-Search-Algorithms-for-SAT|Complete Search Algorithms for SAT]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Conflict-Driven-Clause-Learning|Conflict-Driven Clause Learning]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Branching-Heuristic-Theory|Branching Heuristic Theory]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Look-Ahead-Solving|Look-Ahead Solving]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Preprocessing-and-Inprocessing|Preprocessing and Inprocessing]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Runtime-Variation-and-Solver-Engineering|Runtime Variation and Solver Engineering]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Symmetry-Minimal-Unsatisfiability-and-Autarkies|Symmetry, Minimal Unsatisfiability and Autarkies]]
2. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/book-guidelines|Pseudo-Boolean Reasoning and Compilation]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Practical-SAT-Solving-and-the-CDCL-Architecture|Practical SAT Solving and the CDCL Architecture]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Guiding-the-Search-in-CDCL-SAT-Solvers|Guiding the Search in CDCL SAT Solvers]]
3. [[15_handbook_logic_automated_reasoning_harrison_2009/Propositional-Satisfiability-Algorithms|Harrison — Propositional Satisfiability Algorithms]]
4. [[18_JW_Lloyd_Foundations_logic_programming_1987/SLD-Resolution|Lloyd — SLD-Resolution]] (resolution and search, background)

#### Additional external sources
- Marques-Silva & Sakallah, "GRASP" (1996); Moskewicz et al., "Chaff" (DAC 2001); Eén & Sörensson, "An Extensible SAT-solver" (MiniSat, 2003); Biere's CaDiCaL/Kissat system descriptions for modern engineering.

#### Key Concepts and Definitions
1. DPLL: unit propagation, pure literal, branching; CDCL: implication graph, 1-UIP learned clause, non-chronological backjumping.
2. Two-watched-literal scheme; VSIDS/VMTF; restarts; phase saving; clause deletion (LBD).
3. Preprocessing/inprocessing: bounded variable elimination, subsumption, failed-literal probing.
4. Look-ahead vs. look-back solvers.

#### Relevant Questions
1. Why does 1-UIP learning give a clause that is asserting after a backjump?
2. What does preprocessing gain, and why must model reconstruction be tracked?
3. Where do CDCL techniques transfer to a CSP kernel with integer variables (lazy clause generation)?

---

## 3. Proofs of Unsatisfiability and Proof Complexity (Core Topic)

#### Pre-requisites
2. CDCL; [[learning-roadmap-automated-reasoning|automated-reasoning]] topic 15 (SAT proof systems) is the deeper treatment.

#### Why this topic is important
Untrusted solver results must be certifiable by the trusted kernel; proof formats and lower bounds tell you which encodings are hopeless (pigeonhole) and when stronger systems (cutting planes) are worth using.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/Proof-Complexity|Handbook of Satisfiability — Proof Complexity]]
2. [[25_Handbook_Satisfiability_Armin_Biere_2021/Proofs-of-Unsatisfiability|Handbook of Satisfiability — Proofs of Unsatisfiability]]
3. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/The-Cutting-Planes-Proof-System|Wallon — The Cutting Planes Proof System]]
4. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Communication-Complexity-and-Lower-Bounds-on-Compilation|Wallon — Communication Complexity and Lower Bounds on Compilation]]
5. [[15_handbook_logic_automated_reasoning_harrison_2009/Limits-of-Automated-Reasoning|Harrison — Limits of Automated Reasoning]] (via [[learning-roadmap-automated-reasoning|automated-reasoning]])

#### Key Concepts and Definitions
1. Resolution refutations; width/size lower bounds; pigeonhole principle.
2. Clausal proof formats (RUP/DRAT); proof checking.
3. Cutting planes as a stronger proof system.

#### Relevant Questions
1. What makes a proof format cheap to check yet cheap to produce?
2. For which encodings is exponential resolution proof size unavoidable?
3. When should a solver switch to pseudo-Boolean reasoning?

---

## 4. Pseudo-Boolean, Cardinality, MaxSAT, QBF and Richer Logics (Core Topic)

#### Pre-requisites
2. CDCL; 3. Proof complexity (helpful).

#### Why this topic is important
Linear integer constraints over Boolean variables are the natural target for bounded-integer verification conditions and for optimization/soft-constraint search. QBF handles $\forall\exists$ alternation relevant to quantified refinement predicates; MaxSAT/model counting provide optimization and quantitative analyses.

#### Sources to Study
1. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/book-guidelines|Pseudo-Boolean Reasoning and Compilation]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Pseudo-Boolean-and-Cardinality-Constraints|Pseudo-Boolean and Cardinality Constraints]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Pseudo-Boolean-Solving-via-Cutting-Planes|Pseudo-Boolean Solving via Cutting Planes]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Resolution-Based-Pseudo-Boolean-Solving|Resolution-Based Pseudo-Boolean Solving]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Adapting CDCL Strategies to Pseudo-Boolean Solving]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Irrelevant Literals in Pseudo-Boolean Constraint Learning]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Weakening-Strategies-for-Pseudo-Boolean-Solvers|Weakening Strategies for Pseudo-Boolean Solvers]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Experimental-Evaluation-of-Pseudo-Boolean-Solvers|Experimental Evaluation of Pseudo-Boolean Solvers]]
2. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Pseudo-Boolean-and-Cardinality-Constraints|Pseudo-Boolean and Cardinality Constraints]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Maximum-Satisfiability|Maximum Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Quantified-Boolean-Formulas|Quantified Boolean Formulas]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Model-Counting|Model Counting]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Stochastic-Boolean-Satisfiability|Stochastic Boolean Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/SAT-Techniques-for-Richer-Logics|SAT Techniques for Richer Logics]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Combinatorial-Applications-of-SAT|Combinatorial Applications of SAT]]
3. [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Quantified-CSP|CSP Complexity — Quantified CSP]]

#### Key Concepts and Definitions
1. Pseudo-Boolean constraint $\sum a_i \ell_i \ge k$; cardinality as special case; slack-based propagation.
2. Cutting-planes derivation rules (addition, division, saturation) and weakening.
3. MaxSAT (core-guided, model-improving); #SAT; QBF ($\forall\exists$ solving, expansion/CEGAR).

#### Relevant Questions
1. Why is a linear-constraint learner stronger than clause learning, and what breaks (overflow, coefficient growth)?
2. How does QBF CEGAR structurally resemble the verification CEGAR loop of topic 17?
3. When is MaxSAT the right encoding for soft properties?

---

## 5. Local Search, Random SAT, and Solver Behaviour (Optional / Extension)

#### Pre-requisites
2. CDCL.

#### Why this topic is important
Incomplete search finds satisfying assignments quickly on satisfiable instances — exactly the counterexample-finding mode of the CSP kernel. Phase-transition and runtime-variation results guide portfolio/restart design.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/Stochastic-Local-Search-for-SAT|Handbook of Satisfiability — Stochastic Local Search for SAT]]
2. [[25_Handbook_Satisfiability_Armin_Biere_2021/Random-Satisfiability-and-Phase-Transitions|Random Satisfiability and Phase Transitions]]
3. [[25_Handbook_Satisfiability_Armin_Biere_2021/Statistical-Physics-of-Random-Constraint-Satisfaction|Statistical Physics of Random Constraint Satisfaction]]
4. [[25_Handbook_Satisfiability_Armin_Biere_2021/Runtime-Variation-and-Solver-Engineering|Runtime Variation and Solver Engineering]]
5. [[24_Handbook_Constraint_Programming_Elsevier_2006/Local-Search-Methods|Handbook of CP — Local Search Methods]]
6. [[24_Handbook_Constraint_Programming_Elsevier_2006/Randomness-and-Phase-Transitions|Handbook of CP — Randomness and Phase Transitions]]

#### Key Concepts and Definitions
1. WalkSAT/probSAT; noise; restarts; plateau moves.
2. Satisfiability threshold ($\approx 4.26$ for random 3-SAT); heavy-tailed run times.
3. Portfolio and restart strategies.

#### Relevant Questions
1. When does local search beat CDCL for counterexample discovery?
2. What does the phase transition say about benchmark selection for your solver?

---

## 6. Decision Procedures, Theories, and SMT (Core Topic)

#### Pre-requisites
1–2. SAT/CDCL; [[learning-roadmap-automated-reasoning|automated-reasoning]] topics 5, 9, 14 (decidable fragments, equality reasoning, theory combination).

#### Why this topic is important
Verification conditions live in theories (linear/integer arithmetic, uninterpreted functions, arrays, bit-vectors). SMT = CDCL + theory solvers (DPLL(T)) + combination; it is the solver backend feeding VC discharge, and the reference architecture for embedding a CSP kernel as one more theory solver. **This is the thinnest area in the vault: no dedicated SMT book is on hand.**

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Decidable-Theories-and-Quantifier-Elimination|Decidable Theories and Quantifier Elimination]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Equality-Reasoning|Equality Reasoning]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Combining-Decision-Procedures|Combining Decision Procedures]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Algebraic-Decision-Procedures|Algebraic Decision Procedures]]
2. [[25_Handbook_Satisfiability_Armin_Biere_2021/SAT-Techniques-for-Richer-Logics|Handbook of Satisfiability — SAT Techniques for Richer Logics]]
3. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic]]
   - [[10_boolos_burgess_computability_logic_2007/Decidable-Fragments-of-Arithmetic|Decidable Fragments of Arithmetic]]
   - [[10_boolos_burgess_computability_logic_2007/Nonstandard-Models-of-Arithmetic|Nonstandard Models of Arithmetic]]
   - [[10_boolos_burgess_computability_logic_2007/Definability-in-Arithmetic-and-Forcing|Definability in Arithmetic and Forcing]]
   - [[10_boolos_burgess_computability_logic_2007/Recursive-Semirecursive-and-Arithmetical-Sets-and-Relations|Recursive, Semirecursive, and Arithmetical Sets and Relations]]
   - [[10_boolos_burgess_computability_logic_2007/Arithmetization-of-Syntax-and-Representability|Arithmetization of Syntax and Representability]]
   - [[10_boolos_burgess_computability_logic_2007/Recursive-Function-Theory|Recursive Function Theory]]
4. [[16_ENDERTON_Mathematical_Introduction_Logic/Models-of-Theories|Enderton — Models of Theories]], [[16_ENDERTON_Mathematical_Introduction_Logic/Weak-Fragments-of-Number-Theory|Weak Fragments of Number Theory]]
5. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Order-Minimal-Structures-and-Definability|Tabuada — Order-Minimal Structures and Definability]] (decidability of real arithmetic / o-minimality)
6. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Unification-for-Units-of-Measure|Gundry — Unification for Units of Measure]] (a small equational-theory solver, as a worked example)
7. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Tree-Set-Automata-and-Set-Constraints|TATA — Tree Set Automata and Set Constraints]]

#### Additional external sources
Not covered by an on-hand book — **gap**: Kroening & Strichman, *Decision Procedures: An Algorithmic Point of View* (Springer); Bradley & Manna, *The Calculus of Computation*; Nieuwenhuis, Oliveras & Tinelli, "Solving SAT and SAT Modulo Theories: From an Abstract Davis–Putnam–Logemann–Loveland Procedure to DPLL(T)" (JACM 2006); de Moura & Bjørner, "Z3: An Efficient SMT Solver" (TACAS 2008); Barrett et al., "Satisfiability Modulo Theories" (Handbook of Satisfiability ch. 26 — not in the on-hand copy's tagged chapters); Dutertre & de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)" (CAV 2006); Nelson & Oppen (1979); Jovanović & de Moura, NLSat (IJCAR 2012); Kremer/Ábrahám on CAD-based non-linear real arithmetic.

#### Key Concepts and Definitions
1. First-order theory $T$; $T$-satisfiability of quantifier-free formulas; decidable fragments (LIA, LRA, EUF, arrays, bit-vectors, NRA).
2. DPLL(T): Boolean skeleton + theory solver + explanations (T-lemmas).
3. Nelson–Oppen combination (stably infinite, convex); congruence closure for EUF; simplex for LRA.
4. Non-linear arithmetic: CAD, incremental linearization, NLSat.
5. Quantifier elimination and its cost.

#### Relevant Questions
1. What must a theory solver provide to a DPLL(T) core (propagation, conflict explanation, backtracking)?
2. Why is non-linear integer arithmetic undecidable while non-linear real arithmetic is decidable, and what does the CSP kernel do in the undecidable case?
3. How can the CSP kernel's propagators be wrapped as a theory solver, and what conflict explanations must they return?

---

## 7. CSP Foundations: Modelling, Formalism, and Complexity (Core Topic)

#### Pre-requisites
1. Propositional logic (helpful); basic complexity.

#### Why this topic is important
The counterexample search is a CSP: variables are program inputs/states, constraints are guards and negated invariants. Modelling choices (variables, domains, global constraints) decide tractability; this topic is the vocabulary and complexity baseline for topics 8–15.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Foundations-and-History-of-Constraint-Satisfaction|Foundations and History of Constraint Satisfaction]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Modelling-Constraint-Satisfaction-Problems|Modelling Constraint Satisfaction Problems]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Tractability-and-Computational-Complexity-of-CSPs|Tractability and Computational Complexity of CSPs]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Soft-Constraints-and-Preferences|Soft Constraints and Preferences]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Temporal-Constraint-Satisfaction|Temporal Constraint Satisfaction]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Constraints-over-Structured-Domains|Constraints over Structured Domains]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Constraint-Satisfaction-Problem-Foundations|Pelleau et al. — Constraint Satisfaction Problem Foundations]]
3. [[42_Constraint Propagation_Guido_Tack_PhD_2009/Constraint-Satisfaction-and-Propagation-Based-Solving|Tack — Constraint Satisfaction and Propagation-Based Solving]]
4. [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/book-guidelines|The Constraint Satisfaction Problem: Complexity and Approximability]] (theoretical view; see topic 13)
5. [[16_ENDERTON_Mathematical_Introduction_Logic/Models-of-Theories|Enderton — Models of Theories]] (CSP as model-finding)

#### Key Concepts and Definitions
1. CSP $(X, D, C)$; solution, consistency, optimization variant (COP); CSP as homomorphism/model finding.
2. Modelling: variable/value choice, redundant constraints, channeling.
3. Complexity: NP-completeness, tractable classes (tree-structured, bounded width).
4. Soft/valued constraints, temporal constraints (difference constraints).

#### Relevant Questions
1. How does a program guard/negated postcondition map into a CSP, and which modelling choices affect propagation strength?
2. What structural conditions (tree-width, acyclicity) make a generated CSP tractable?
3. How does CSP relate to SAT/SMT (same problem, different representation of domains)?

---

## 8. Local Consistency and Constraint Propagation (Core Topic)

#### Pre-requisites
7. CSP foundations; [[learning-roadmap-static-analysis|static-analysis]] topic 2 (fixpoints and lattices).

#### Why this topic is important
Domain propagation is *the* mechanism of the CSP kernel: propagators prune domains to a fixpoint (arc/bounds/path consistency). Formulated as monotone operators on a domain lattice, propagation is chaotic iteration — the same object as abstract interpretation (topic 11).

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/Constraint-Propagation-and-Local-Consistency|Handbook of CP — Constraint Propagation and Local Consistency]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Consistency-and-Propagation-in-Constraint-Programming|Pelleau et al. — Consistency and Propagation in Constraint Programming]]
3. [[42_Constraint Propagation_Guido_Tack_PhD_2009/book-guidelines|Constraint Propagation — Models, Techniques, Implementation (Tack)]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/The-Denotational-and-Operational-Model-of-Constraint-Propagation|The Denotational and Operational Model of Constraint Propagation]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Propagation-Strength-and-Domain-Approximations|Propagation Strength and Domain Approximations]]
4. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Number-Theoretic-and-Interval-Abstract-Domains|Cousot — Number-Theoretic and Interval Abstract Domains]]
5. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Graph-Theory-and-Path-Problems|Cousot — Graph Theory and Path Problems]]
6. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Abstract-Domains-For-Constraint-Programming|Talbot — Abstract Domains for Constraint Programming]]

#### Additional external sources
- Mackworth (1977) on arc consistency; Bessière, "Constraint Propagation" (Handbook of CP ch. 3 — on-hand as the chapter above); Apt, *Principles of Constraint Programming* (CUP 2003) for the chaotic-iteration formulation.

#### Key Concepts and Definitions
1. Arc consistency (AC-3/AC-2001), bounds consistency, path consistency, $k$-consistency.
2. Propagator: monotone, contracting, idempotent (optionally) function on domains; propagation as fixpoint computation.
3. Propagation strength and domain approximations (bounds vs. sets vs. holes).
4. Denotational (fixpoint) vs. operational (scheduling) models.

#### Relevant Questions
1. When does local consistency imply global consistency, and what does it cost to enforce?
2. In what sense is propagation-to-fixpoint the greatest fixpoint of a family of propagators?
3. How do bounds-consistent integer propagators relate to the interval abstract domain?

---

## 9. Search, Global Constraints, and Symmetry (Core Topic)

#### Pre-requisites
8. Propagation; 2. CDCL (for learning).

#### Why this topic is important
Propagation alone is incomplete; the kernel needs branching, heuristics, restarts and global constraints (all-different, cumulative, etc.) to search efficiently for a satisfying assignment, and symmetry breaking to avoid redundant work over structured inputs.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Backtracking-Search|Backtracking Search]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Global-Constraints|Global Constraints]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Symmetry-in-Constraint-Programming|Symmetry in Constraint Programming]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Finite-Domain-Constraint-Programming-Systems|Finite Domain Constraint Programming Systems]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Integration-of-Constraint-Programming-and-Operations-Research|Integration of Constraint Programming and Operations Research]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Distributed-Constraint-Programming|Distributed Constraint Programming]]
   - [[24_Handbook_Constraint_Programming_Elsevier_2006/Uncertainty-and-Change-in-Constraint-Problems|Uncertainty and Change in Constraint Problems]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Exploration-and-Search-in-Constraint-Programming|Pelleau et al. — Exploration and Search in Constraint Programming]]
3. [[25_Handbook_Satisfiability_Armin_Biere_2021/Symmetry-Minimal-Unsatisfiability-and-Autarkies|Handbook of Satisfiability — Symmetry, Minimal Unsatisfiability and Autarkies]]
4. [[25_Handbook_Satisfiability_Armin_Biere_2021/Branching-Heuristic-Theory|Handbook of Satisfiability — Branching Heuristic Theory]]

#### Additional external sources
- Ohrimenko, Stuckey & Codish, "Propagation via Lazy Clause Generation" (Constraints 2009) — the bridge between topics 2 and 8–9; Régin on global constraint filtering algorithms; van Hoeve & Katriel, "Global Constraints" (Handbook of CP).

#### Key Concepts and Definitions
1. Backtracking with propagation (MAC), variable/value ordering, dom/wdeg, restarts.
2. Global constraints with dedicated propagators (all-different/matching, cumulative).
3. Symmetry breaking (static lex-leader, dynamic).
4. Lazy clause generation: explanations from propagators feed a CDCL core.

#### Relevant Questions
1. Which variable-ordering heuristic transfers from SAT (VSIDS) to CSP, and which do not?
2. How much of program-input symmetry (permuting array elements) can be broken automatically?
3. When does a global constraint pay for itself over its decomposition?

---

## 10. Propagator Engineering: Scheduling, Views, and Set Domains (Core Topic)

#### Pre-requisites
8. Propagation; Rust systems experience.

#### Why this topic is important
This is the implementation blueprint of a propagation kernel: propagator scheduling, views/derived propagators (reduce code by composing), set-valued domains, and efficient data structures. Directly usable for the CSP kernel's Rust architecture.

#### Sources to Study
1. [[42_Constraint Propagation_Guido_Tack_PhD_2009/book-guidelines|Constraint Propagation — Models, Techniques, Implementation (Tack)]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Implementation-Architecture-of-a-Propagation-Kernel|Implementation Architecture of a Propagation Kernel]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Efficient-Propagator-Scheduling|Efficient Propagator Scheduling]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Views-and-Derived-Propagators|Views and Derived Propagators]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Implementing-Views-Efficiently|Implementing Views Efficiently]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Range-Iterators-for-Set-Valued-Domain-Operations|Range Iterators for Set-Valued Domain Operations]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Deriving-Propagators-for-Boolean-Set-Constraints|Deriving Propagators for Boolean Set Constraints]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Empirical-Evaluation-and-Benchmarking|Empirical Evaluation and Benchmarking]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Open-Problems-and-Future-Directions|Open Problems and Future Directions]]
2. [[24_Handbook_Constraint_Programming_Elsevier_2006/Finite-Domain-Constraint-Programming-Systems|Handbook of CP — Finite Domain Constraint Programming Systems]]
3. [[39_Equality-Saturation-RossThesis2012/The-Peggy-Implementation|Ross — The Peggy Implementation]] (fixpoint-engine implementation notes; peripheral)

#### Additional external sources
- Schulte & Stuckey, "Efficient Constraint Propagation Engines" (TOPLAS 2008); Gecode documentation; Stuckey et al. on Chuffed (lazy clause generation implementation).

#### Key Concepts and Definitions
1. Propagator queue with priorities; idempotence and subsumption; event-based wake-up.
2. Views: $x \mapsto ax+b$, negation, offsets — one propagator, many uses.
3. Set-domain representation by range lists and iterator-based operations.
4. Trail-based or copying-based state restoration.

#### Relevant Questions
1. What are the trade-offs between trailing and copying for backtracking state in Rust?
2. How do views reduce the propagator zoo while preserving propagation strength?
3. How would you represent interval and set domains to make propagation cache-friendly?

---

## 11. Abstract Domains for Constraint Solving and Solver Cooperation (Core Topic)

#### Pre-requisites
8. Propagation; [[learning-roadmap-static-analysis|static-analysis]] topics 4 and 6 (Galois connections, numeric domains).

#### Why this topic is important
The project's key architectural idea: the CSP kernel *and* the abstract interpreter share domains (intervals, octagons, polyhedra) and can cooperate through products. Abstract-interpretation-based CP explains propagators as abstract transformers and provides modular composition of solvers (delayed/shared products).

#### Sources to Study
1. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Links-Between-Abstract-Interpretation-and-Constraint-Programming|Links Between Abstract Interpretation and Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Abstract-Interpretation-Reformulation-of-Constraint-Programming|Abstract Interpretation Reformulation of Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Unified-Abstract-Domains-for-Constraint-Programming|Unified Abstract Domains for Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/The-Octagon-Abstract-Domain|The Octagon Abstract Domain]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Octagonal-Constraint-Solving|Octagonal Constraint Solving]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/The-AbSolute-Solver|The AbSolute Solver]]
2. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/book-guidelines|Modular Constraint Solver Cooperation via Abstract Interpretation]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Abstract Interpretation as a Foundation for Constraint Solving]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Domain-Transformers|Domain Transformers]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Interval-Propagators-Completion-IPC|Interval Propagators Completion (IPC)]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Delayed-Product-DP|Delayed Product (DP)]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Shared-Product-and-Modular-Composition|Shared Product and Modular Composition]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Case-Study-Flexible-Job-Shop-Scheduling|Case Study: Flexible Job Shop Scheduling]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Implementation-and-Empirical-Evaluation|Implementation and Empirical Evaluation]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Relation-to-Other-Cooperation-Frameworks|Relation to Other Cooperation Frameworks]]
3. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Number-Theoretic-and-Interval-Abstract-Domains|Cousot — Number-Theoretic and Interval Abstract Domains]]
4. [[24_Handbook_Constraint_Programming_Elsevier_2006/Continuous-and-Interval-Constraints|Handbook of CP — Continuous and Interval Constraints]]

#### Key Concepts and Definitions
1. Constraint solving as iteration of abstract transformers in an abstract domain; solutions as concrete elements of $\gamma(a)$.
2. Octagon/interval domains as CP domains; AbSolute solver (abstract domain + split).
3. Domain transformers, delayed product, shared product: composing solvers modularly.
4. Sound but incomplete propagators vs. complete search by splitting.

#### Relevant Questions
1. How does a reduced product of interval and octagon domains improve propagation, and what does it cost?
2. Which parts of the abstract interpreter's transfer functions can be reused as propagators?
3. What does modular solver cooperation buy when one solver is over-approximating (AI) and one is exact (search)?

---

## 12. Integer, Non-Linear and Continuous Constraints (Core Topic)

#### Pre-requisites
8. Propagation; 11. Abstract domains; real analysis and basic linear algebra.

#### Why this topic is important
The project explicitly requires integer and non-linear equation handling. This topic covers interval/continuous constraint solving, relaxations, spatial branch-and-bound and polynomial bounding (Bernstein), which give sound pruning for non-linear constraints where SMT non-linear arithmetic is too expensive or incomplete.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/Continuous-and-Interval-Constraints|Handbook of CP — Continuous and Interval Constraints]]
2. [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/book-guidelines|Reformulation and Convex Relaxation in Global Optimization]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Global-Optimization-and-the-Branch-and-Select-Framework|Global Optimization and the Branch-and-Select Framework]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Spatial-Branch-and-Bound-sBB-Algorithms|Spatial Branch-and-Bound (sBB) Algorithms]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Convex-and-Linear-Relaxation-Techniques|Convex and Linear Relaxation Techniques]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Reformulation-to-Standard-Forms|Reformulation to Standard Forms]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Exact-Problem-Reformulations|Exact Problem Reformulations]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Convex-Envelopes-for-Monomials-of-Odd-Degree|Convex Envelopes for Monomials of Odd Degree]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Reduction-Constraints-for-Sparse-Bilinear-Programs|Reduction Constraints for Sparse Bilinear Programs]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Classification-of-Optimization-Problems|Classification of Optimization Problems]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Convexity-and-Function-Set-Classification|Convexity and Function/Set Classification]]
   - [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/The-OS-Software-Framework|The OS Software Framework]]
3. [[74_Reachability_Analysis_Bernstein expansion_2012/book-guidelines|Reachability Analysis via Bernstein Expansion]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/The-Bernstein-Expansion-of-Polynomials|The Bernstein Expansion of Polynomials]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Computing Affine Bound Functions from Bernstein Coefficients]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Mapping-General-Polyhedra-to-the-Unit-Box|Mapping General Polyhedra to the Unit Box]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Approximation-Error-and-Computational-Complexity|Approximation Error and Computational Complexity]]
4. [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/Multi-Affine-Zonotope-Optimization|Huang — Multi-Affine Zonotope Optimization]]
5. [[59_Grimstad_Global_Spline_Optimization/book-guidelines|Global Spline Optimization]] — B-spline surrogates and spatial B&B ([[59_Grimstad_Global_Spline_Optimization/book-guidelines|application-heavy; use only the optimization chapters]])
6. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Octagonal-Constraint-Solving|Pelleau et al. — Octagonal Constraint Solving]]
7. [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/CSP-over-Infinite-and-Numeric-Domains|CSP Complexity — CSP over Infinite and Numeric Domains]]
8. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Number-Theoretic-and-Interval-Abstract-Domains|Cousot — Number-Theoretic and Interval Abstract Domains]]
9. [[10_boolos_burgess_computability_logic_2007/Decidable-Fragments-of-Arithmetic|Boolos–Burgess — Decidable Fragments of Arithmetic]] (why non-linear integer constraints are undecidable)

#### Additional external sources
Not covered by an on-hand book — **gap**: Benhamou & Granvilliers, "Continuous and Interval Constraints" (Handbook of CP ch. 16 — on hand); Hansen & Walster, *Global Optimization Using Interval Analysis*; Jaulin et al., *Applied Interval Analysis*; Tawarmalani & Sahinidis, *Convexification and Global Optimization in Continuous and Mixed-Integer Nonlinear Programming*; Fränzle et al., "Efficient Solving of Large Non-linear Arithmetic Constraint Systems with Complex Boolean Structure" (iSAT, JSAT 2007); Gao et al., dReal (CADE 2013).

#### Key Concepts and Definitions
1. Interval arithmetic and HC4/box consistency; interval Newton; dependency (wrapping) problem.
2. Convex/linear relaxation, McCormick envelopes; spatial branch-and-bound with bounds tightening.
3. Bernstein expansion: range enclosure of polynomials over a box; affine bounding.
4. Undecidability of Diophantine constraints (Hilbert's 10th) vs. decidability of real closed fields.

#### Relevant Questions
1. How does a McCormick envelope give a sound linear relaxation of a bilinear term?
2. When does Bernstein bounding beat plain interval arithmetic, and what does it cost in dimension?
3. What should the CSP kernel return when a non-linear constraint is only shown *possibly* satisfiable by a relaxation?

---

## 13. CSP Tractability: Algebraic, Structural, and Parameterized Theory (Optional / Extension)

#### Pre-requisites
7. CSP foundations; algebra background (universal algebra is developed in the sources).

#### Why this topic is important
The project lists Structural Tractability and Algebraic Graph Theory as conceptual connections. This theory identifies *which* constraint languages and graph structures admit polynomial-time solving (the Feder–Vardi / dichotomy programme), guiding decisions about when generated CSPs are provably easy and when to expect hardness.

#### Sources to Study
1. [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/book-guidelines|The Constraint Satisfaction Problem: Complexity and Approximability]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/The-Algebraic-Approach-to-CSP|The Algebraic Approach to CSP]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Absorption-Theory|Absorption Theory]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Hybrid-Tractability|Hybrid Tractability]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Backdoor-Sets-and-Fixed-Parameter-Tractability|Backdoor Sets and Fixed-Parameter Tractability]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Digraph-CSP|Digraph CSP]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Valued-CSP|Valued CSP]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Counting-CSP|Counting CSP]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Holant-Problems|Holant Problems]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Approximation-Algorithms-for-CSP|Approximation Algorithms for CSP]]
   - [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Counting, Parameterization, and Optimization Variants of CSP]]
2. [[24_Handbook_Constraint_Programming_Elsevier_2006/Tractability-and-Computational-Complexity-of-CSPs|Handbook of CP — Tractability and Computational Complexity of CSPs]]
3. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/book-guidelines|Pseudo-Boolean Reasoning and Compilation]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Graph Width Measures for CNF Formulae and Encodings]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Knowledge-Compilation|Knowledge Compilation]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Succinctness-and-Tractability-of-Pseudo-Boolean-Languages|Succinctness and Tractability of Pseudo-Boolean Languages]]
4. [[25_Handbook_Satisfiability_Armin_Biere_2021/Worst-Case-Complexity-and-Tractability|Handbook of Satisfiability — Worst-Case Complexity and Tractability]]
5. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Order-Minimal-Structures-and-Definability|Tabuada — Order-Minimal Structures and Definability]] (definability and decidability of numeric structures)

#### Key Concepts and Definitions
1. Constraint language $\Gamma$ and $\mathrm{CSP}(\Gamma)$; polymorphisms and the algebraic dichotomy conjecture (Bulatov/Zhuk).
2. Structural tractability: tree-width/hypertree width bounded ⇒ polynomial CSP.
3. Backdoor sets and fixed-parameter tractability; hybrid tractability.
4. Valued/counting/Holant generalizations; approximability.

#### Relevant Questions
1. What does a polymorphism tell us about a constraint language's tractability?
2. When is bounded tree-width of the constraint graph decisive, and can the compiler compute it cheaply for generated CSPs?
3. Which of your verification constraint languages fall in known tractable classes (e.g. difference constraints, 2-SAT, Horn)?

---

## 14. Constraint Logic Programming and Constraints in Languages (Optional / Extension)

#### Pre-requisites
[[learning-roadmap-automated-reasoning|automated-reasoning]] topics 7–8 (unification and resolution, logic programming as proof search); 8. Propagation.

#### Why this topic is important
CLP generalizes SLD resolution to constraint solving over a domain — the model for a prover whose search calls a constraint store, and for CHC solvers built on Horn clauses with constraints. Integrity constraints and multiset specification give further logic-programming angles.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/Constraint-Logic-Programming|Handbook of CP — Constraint Logic Programming]]
2. [[24_Handbook_Constraint_Programming_Elsevier_2006/Constraints-in-Procedural-Concurrent-and-Rule-Based-Languages|Handbook of CP — Constraints in Procedural, Concurrent, and Rule-Based Languages]]
3. [[18_JW_Lloyd_Foundations_logic_programming_1987/SLD-Resolution|Lloyd — SLD-Resolution]], [[18_JW_Lloyd_Foundations_logic_programming_1987/Integrity-Constraint-Checking|Integrity Constraint Checking]]
4. [[09_proof_theory_logic_programming_dale_miller_2025/Specifying-Computations-with-Multisets-and-Automata|Miller — Specifying Computations with Multisets and Automata]]
5. [[76_ThetaSubsumption_article/Search-Methods-Over-the-Hypothesis-Space|ILP article — Search Methods Over the Hypothesis Space]] (constraint-guided search over clause space)

#### Additional external sources
- Jaffar & Lassez, "Constraint Logic Programming" (POPL 1987); Jaffar & Maher, "CLP: A Survey" (JLP 1994); Marriott & Stuckey, *Programming with Constraints* (MIT Press 1998); Frühwirth, *Constraint Handling Rules*.

#### Key Concepts and Definitions
1. CLP$(\mathcal X)$ scheme: constraint store, resolution + constraint solving, entailment checking.
2. Constraint store operations (tell/ask), incremental solving, and backtracking.
3. Constraint Handling Rules (CHR) as a rule-based propagation language.

#### Relevant Questions
1. How does CLP resolution differ from SLD, and what obligation does it place on the constraint solver?
2. Why are CHCs (constrained Horn clauses) a natural CLP-shaped encoding of verification conditions?

---

## 15. Automata and Symbolic-Automata Domains for Structured Data (Core Topic)

#### Pre-requisites
7–8. CSP/propagation; [[learning-roadmap-type-theory|type-theory]] topic 15 and [[learning-roadmap-static-analysis|static-analysis]] topic 10.

#### Why this topic is important
The CSP kernel must support abstract data structures as *complex domains* represented by automata/grammars (DFA-style). Symbolic automata (labelled by predicates over an effective Boolean algebra, e.g. integer intervals) let one domain constrain both the structure and the numeric content of strings/lists/trees; set constraints and constraint-carrying tree automata bridge to propagation.

#### Sources to Study
1. [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/book-guidelines|The Power of Symbolic Automata and Transducers]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Effective-Boolean-Algebras|Effective Boolean Algebras]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Finite-Automata|Symbolic Finite Automata]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Minterms-and-Alphabet-Equivalence-Classes|Minterms and Alphabet Equivalence Classes]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Parametric-Complexity-of-Symbolic-Algorithms|Parametric Complexity of Symbolic Algorithms]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Variants-of-Symbolic-Automata|Variants of Symbolic Automata]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Automata-in-Practice|Symbolic Automata in Practice]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Finite-Transducers|Symbolic Finite Transducers]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Transducers-in-Practice|Symbolic Transducers in Practice]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Variants-of-Symbolic-Transducers|Variants of Symbolic Transducers]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Open-Problems-in-Symbolic-Models|Open Problems in Symbolic Models]]
2. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Automata-with-Constraints|Automata with Constraints]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Tree-Set-Automata-and-Set-Constraints|Tree Set Automata and Set Constraints]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Alternating-Tree-Automata|Alternating Tree Automata]]
3. [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/book-guidelines|Pushdown Automata Inclusion Problems]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Antichain-Based-Decision-Procedures|Antichain-Based Decision Procedures]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Extensions-of-Visibly-Pushdown-Automata-and-Their-Limits|Extensions of Visibly Pushdown Automata and Their Limits]]
4. [[67_Principles_of_Model_Checking_2008/Automata-over-Finite-and-Infinite-Words|Baier–Katoen — Automata over Finite and Infinite Words]]
5. [[24_Handbook_Constraint_Programming_Elsevier_2006/Constraints-over-Structured-Domains|Handbook of CP — Constraints over Structured Domains]]
6. [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/book-guidelines|D'Antoni thesis — Automata and Transducers]] (untagged for this area; related background)

#### Additional external sources
- Pesant, "A Regular Language Membership Constraint for Finite Sequences of Variables" (CP 2004) and Beldiceanu et al. on the `regular`/automaton global constraint; Bjørner et al. on Z3's string/sequence theory; Gervet on set constraints.

#### Key Concepts and Definitions
1. Effective Boolean algebra $\mathcal A$; SFA transitions $q \xrightarrow{\varphi} q'$; minterms for determinization/minimization.
2. `regular` global constraint: sequence of variables must be accepted by an automaton.
3. Set constraints and tree set automata; alternating automata; constraint-carrying automata.
4. Antichain-based inclusion checking.

#### Relevant Questions
1. How can a DFA/symbolic automaton be encoded as a propagating constraint on a sequence of integer variables?
2. Which operations (intersection, complement, emptiness, model extraction) must an automata domain support to be used inside a CSP kernel, and at what cost?
3. How does the propagation strength of the `regular` constraint compare with decomposing it into transition clauses?

---

## 16. Bounded and Symbolic Model Checking, BDDs, and Knowledge Compilation (Optional / Extension)

#### Pre-requisites
1–2. SAT; [[learning-roadmap-static-analysis|static-analysis]] topic 17 (model checking).

#### Why this topic is important
Symbolic representations (BDDs, other compiled forms) and bounded model checking are how SAT/CP technology is applied to reachability: unrolling a transition relation into a formula is the simplest counterexample-search architecture and the baseline for the CSP kernel.

#### Sources to Study
1. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking]]
   - [[67_Principles_of_Model_Checking_2008/Model-Checking-Fundamentals|Model Checking Fundamentals]]
   - [[67_Principles_of_Model_Checking_2008/Transition-Systems-as-System-Models|Transition Systems as System Models]]
   - [[67_Principles_of_Model_Checking_2008/State-Space-Explosion|State-Space Explosion]]
   - [[67_Principles_of_Model_Checking_2008/Safety-Properties-and-Invariants|Safety Properties and Invariants]]
   - [[67_Principles_of_Model_Checking_2008/Automata-Based-LTL-Model-Checking|Automata-Based LTL Model Checking]]
   - [[67_Principles_of_Model_Checking_2008/Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Symbolic Model Checking with Binary Decision Diagrams]]
   - [[67_Principles_of_Model_Checking_2008/Markov-Chains-and-Probabilistic-Verification|Markov Chains and Probabilistic Verification]]
   - [[67_Principles_of_Model_Checking_2008/Markov-Decision-Processes|Markov Decision Processes]]
2. [[25_Handbook_Satisfiability_Armin_Biere_2021/Bounded-Model-Checking-and-Formal-Verification|Handbook of Satisfiability — Bounded Model Checking and Formal Verification]]
3. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Knowledge-Compilation|Wallon — Knowledge Compilation]]
4. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/book-guidelines|Verification and Control of Hybrid Systems]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Timed-Automata-and-Quotient-Based-Abstraction|Timed Automata and Quotient-Based Abstraction]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Barrier-Certificates-and-Reachable-Set-Computation|Barrier Certificates and Reachable Set Computation]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Exact-Symbolic-Models-for-Control|Exact Symbolic Models for Control]]
5. [[74_Reachability_Analysis_Bernstein expansion_2012/Reachability-Analysis-for-Hybrid-and-Polynomial-Dynamical-Systems|Reachability Analysis for Hybrid and Polynomial Dynamical Systems]]
6. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Graph-Theory-and-Path-Problems|Cousot — Graph Theory and Path Problems]]

#### Additional external sources
- Biere et al., "Symbolic Model Checking without BDDs" (TACAS 1999); Sheeran, Singh & Stålmarck, "Checking Safety Properties Using Induction and a SAT-Solver" (FMCAD 2000; $k$-induction); Bryant (1986) on ROBDDs; Darwiche & Marquis, "A Knowledge Compilation Map" (JAIR 2002).

#### Key Concepts and Definitions
1. Bounded model checking: unroll $I(s_0)\wedge\bigwedge T(s_i,s_{i+1})\wedge\lnot P(s_k)$.
2. $k$-induction and completeness thresholds.
3. BDDs: canonical form, variable ordering; knowledge compilation languages and their succinctness.
4. State-space explosion and reduction techniques.

#### Relevant Questions
1. How does BMC's unrolled formula compare with a path-based CSP over program states?
2. When are BDDs (canonical forms) preferable to CDCL, and when do they blow up?
3. What is the relation between $k$-induction and finding an inductive invariant?

---

## 17. CEGAR, CHC Solving, and Loop Acceleration (Core Topic)

#### Pre-requisites
6. SMT; 11. Abstract domains; 16. BMC; [[learning-roadmap-static-analysis|static-analysis]] topic 16 (CEGAR).

#### Why this topic is important
This is where the two halves meet: constrained Horn clauses are a solver-friendly encoding of verification conditions; CEGAR uses the counterexample search to refine the abstraction (proving absence) or confirm the bug (proving presence). Loop acceleration and clause learning add strength beyond plain unrolling/widening.

#### Sources to Study
1. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/book-guidelines|Acceleration Driven Clause Learning for CHC]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Constrained-Horn-Clauses-(CHCs)|Constrained Horn Clauses (CHCs)]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Loop-Acceleration|Loop Acceleration]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/The-ADCL-Calculus|The ADCL Calculus]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Implementing-ADCL-in-LoAT|Implementing ADCL in LoAT]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Related Approaches to CHC-SAT and Loop Summarization]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Empirical-Evaluation|Empirical Evaluation]]
2. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|Minkowski-Sum Domain Dissertation]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Counterexample-Guided Abstraction Refinement (CEGAR)]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Elimination-of-Spurious-Transitions|Elimination of Spurious Transitions]]
3. [[76_ThetaSubsumption_article/book-guidelines|Theta-Subsumption / ILP article]] — ILP system features and search (clause/hypothesis learning): [[76_ThetaSubsumption_article/Representative-ILP-Systems|Representative ILP Systems]], [[76_ThetaSubsumption_article/Building-an-ILP-System|Building an ILP System]], [[76_ThetaSubsumption_article/Applications-of-ILP|Applications of ILP]], [[76_ThetaSubsumption_article/ILP-System-Features|ILP System Features]], [[76_ThetaSubsumption_article/Open-Limitations-and-Future-Directions|Open Limitations and Future Directions]]
4. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Related-Work-and-Positioning|Calcagno et al. — Related Work and Positioning]]
5. [[39_Equality-Saturation-RossThesis2012/Loop-and-Branch-Optimizations-Discovered-by-Saturation|Ross — Loop and Branch Optimizations Discovered by Saturation]] (loop reasoning by rewriting; peripheral)
6. [[09_proof_theory_logic_programming_dale_miller_2025/Specifying-Computations-with-Multisets-and-Automata|Miller — Specifying Computations with Multisets and Automata]]

#### Additional external sources
Not covered by an on-hand book — **gap**: Clarke et al., "Counterexample-Guided Abstraction Refinement" (CAV 2000); Bjørner, Gurfinkel, McMillan & Rybalchenko, "Horn Clause Solvers for Program Verification" (2015); Hoder, Bjørner & de Moura, "μZ" (CADE 2011); Gurfinkel et al., SeaHorn/Spacer ("Solving Constrained Horn Clauses using IC3", FMCAD 2011 / CAV 2014); McMillan, "Lazy Abstraction with Interpolants" (CAV 2006); Bradley, "SAT-Based Model Checking without Unrolling" (IC3/PDR, VMCAI 2011).

#### Key Concepts and Definitions
1. Constrained Horn clause: $\varphi \wedge P_1(\vec t_1)\wedge\dots \Rightarrow H(\vec t)$; solution = interpretation of predicates; unsat = derivation of `false`.
2. CEGAR loop: abstract, check, concretize counterexample, refine on spuriousness.
3. Loop acceleration: replace iterated transition by a closed-form summary; ADCL learns accelerated clauses.
4. Property-directed reachability (IC3/PDR) as an alternative fixpoint-by-SAT.

#### Relevant Questions
1. How do CHC satisfiability (an inductive invariant exists) and CHC unsatisfiability (a counterexample derivation exists) correspond to the two proof modes of your compiler?
2. What makes acceleration exact where widening over-approximates, and what class of loops qualifies?
3. What information must the CSP kernel return so the abstraction can be refined (unsat core, path, interpolant)?

---

## 18. Symbolic Execution and the Counterexample-Search Architecture (Core Topic — external sources needed)

#### Pre-requisites
6. SMT; 9. Search; 15. Automata domains; 17. CEGAR; [[learning-roadmap-static-analysis|static-analysis]] topics 1 and 9.

#### Why this topic is important
Symbolic execution turns each program path into a path condition solved by the backend, giving path coverage and concrete counterexamples ("counterfacts"). It is the operational glue between the abstract interpreter (which prunes infeasible paths), the constraint kernel (which solves path conditions) and the type/refinement checker (which supplies the properties). **No book in `vaults/` covers symbolic execution directly**; the topics above supply the solver-side machinery.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Forward-Reachability-Semantics|Cousot — Forward Reachability Semantics]] and [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Trace-Semantics-of-Programs|Trace Semantics of Programs]] (paths as concrete semantics)
2. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Path-Programs-and-Loop-Invariants|Greitschus — Path Programs and Loop Invariants]]
3. [[39_Equality-Saturation-RossThesis2012/Translation-Validation|Ross — Translation Validation]] (equivalence checking by solver)
4. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Unification-for-Units-of-Measure|Gundry — Unification for Units of Measure]]

#### Additional external sources
**Gap — recommended additions to `sources/`:** King, "Symbolic Execution and Program Testing" (CACM 1976); Cadar & Sen, "Symbolic Execution for Software Testing: Three Decades Later" (CACM 2013); Godefroid, Klarlund & Sen, "DART" (PLDI 2005) and Cadar et al., "KLEE" (OSDI 2008); Baldoni et al., "A Survey of Symbolic Execution Techniques" (ACM CSUR 2018); Pasareanu & Visser on symbolic PathFinder; Torlak & Bodik, Rosette ("Growing Solver-Aided Languages with Rosette", Onward! 2013); de Moura & Bjørner on Z3 as a backend; Leino, Dafny/Boogie verification-condition pipeline.

#### Key Concepts and Definitions
1. Symbolic state $(\sigma, \pi)$: symbolic store and path condition; forking at branches; feasibility by solver.
2. Path explosion mitigation: state merging, subsumption via abstraction, search strategies.
3. Concolic execution; concretization.
4. Solver-aided languages and verification-condition generation.

#### Relevant Questions
1. How does abstract-interpretation-derived invariant information prune the symbolic execution tree?
2. Which path constraints should go to the SMT solver and which to the CSP kernel (non-linear, structured domains)?
3. How does a counterexample from symbolic execution translate into a refinement-type failure witness?

---

## Summary of gaps and pruning notes

Explicit external-source recommendations are attached to topics **6 (SMT — the biggest gap: DPLL(T), simplex, Nelson–Oppen, non-linear arithmetic)**, **9 (lazy clause generation, global constraint filtering)**, **10 (propagation-engine papers)**, **12 (interval/global-optimization textbooks and non-linear SAT solvers)**, **15 (regular constraint)**, **16 (BMC, $k$-induction)**, **17 (CEGAR, Horn clause solvers, IC3)** and **18 (symbolic execution — no on-hand book)**. Books carrying a stray or peripheral `sat-smt-csp` tag and used only lightly: [[59_Grimstad_Global_Spline_Optimization/book-guidelines|Global Spline Optimization]], [[39_Equality-Saturation-RossThesis2012/book-guidelines|Equality Saturation]], [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/book-guidelines|Bi-Abduction]] and [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference, Haskell and Dependent Types]].
