# Handbook of Satisfiability — Guidelines

## Header

**Title:** Handbook of Satisfiability (Second Edition)
**Author(s):** Armin Biere, Marijn Heule, Hans van Maaren, Toby Walsh (Editors); 60+ contributing chapter authors
**Publication:** IOS Press, Frontiers in Artificial Intelligence and Applications vol. 336, 2021 (ISBN 978-1-64368-160-3)

**Brief Summary:**
This handbook is an encyclopedic, survey-style reference on propositional satisfiability (SAT) and its extensions, spanning theory, algorithms, and applications. Part I covers the foundational algorithmics of SAT — its history, CNF encodings, complete algorithms (existential quantification, inference rules, search, CDCL), look-ahead and incomplete (local search) solvers, proof complexity, branching heuristics, preprocessing, random satisfiability and phase transitions, runtime variation, automated solver configuration, symmetry, minimal unsatisfiability and autarkies, proof logging, worst-case upper bounds, and fixed-parameter tractability. Part II covers extensions and applications: bounded model checking, planning, software verification, combinatorial designs, statistical-physics connections, MaxSAT, model counting (exact and approximate), non-clausal SAT and automatic test pattern generation, pseudo-Boolean and cardinality constraints, quantified Boolean formulas (theory, solving, and proof systems), SAT techniques for modal/description logics, satisfiability modulo theories (SMT), and stochastic Boolean satisfiability.

**Intent of the Author:**
The editors aim to capture the full breadth and depth of SAT — from N P-completeness theory to industrial-scale solving — in a single encyclopedic reference for researchers, graduate students, upper-year undergraduates, and practitioners, requiring only limited prior knowledge of the field. The second edition updates roughly half the chapters and adds entirely new chapters (proof complexity, preprocessing, automated configuration, proofs of unsatisfiability, approximate model counting, and QBF proof systems) to reflect two decades of what the preface calls the "SAT Revolution," in which practical SAT solving moved from an academic curiosity to a foundational technology underlying SMT, verification, and automated reasoning broadly.

---

## Topic List

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

## Chapter Summaries

### Chapter 1: A History of Satisfiability (pp. 3–55)

**Summary:** A multi-author history tracing the concept of satisfiability from Aristotle's syllogistic logic through medieval and Renaissance logic, Boole/Jevons/Venn, Frege/Russell/Gödel, to the birth of automated deduction (Davis-Putnam, DPLL), and on to modern SAT-solving technology (resolution complexity, BDDs, probabilistic/threshold analysis, stochastic local search, MaxSAT, nonlinear/SDP formulations, pseudo-Boolean forms, and QBF). : [[History-and-Foundations-of-Satisfiability|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Preface** — validity vs. consistency as syntactic (derivability) vs. semantic (satisfiability) mirror images; a structure $A = \langle D,R\rangle$; satisfiability as the semantic version of consistency; completeness as the coincidence of derivability with validity.
- **1.2–1.4 Ancients to Renaissance** — Aristotle's categorical propositions (A, E, I, O) and syllogistic logic; the law of excluded middle; Leibniz's concept inclusion $\sqsubseteq$ and "real addition" $\oplus$.
- **1.6 Boolean algebra** — the Boolean algebra $\langle B,\vee,\wedge,\neg,0,1\rangle$; Jevons' method of indirect inference; Venn diagrams as an isomorphic diagrammatic method for Boolean class algebra. : [[CNF-Encodings|Link]]
- **1.7–1.13 Frege to completeness** — logicism (Frege), Russell's paradox, Principia Mathematica, Gödel's incompleteness theorem, recursive functions and Church's thesis, Herbrand's theorem and Herbrand models, Tarski's satisfaction relation $A\models_s p$, Henkin's completeness proof via maximally consistent saturated sets.
- **1.14–1.15 Circuits and resolution** — Shannon's application of Boolean algebra to relay circuits, the Shannon expansion $f=x_1\cdot f(1,x_2,\dots)+\overline{x_1}\cdot f(0,x_2,\dots)$; consensus and prime implicants (Blake, Quine-McCluskey); the Davis-Putnam Procedure (unit-clause rule, pure-literal rule, atomic formula elimination, splitting rule) and its refinement into DPLL by Loveland and Logemann; Tseitin's extension variables ($z\Leftrightarrow f(a,b,\dots)$) and the linear CNF translation.
- **1.16 Complexity of resolution** — tree resolution vs. general resolution; regularity of a resolution proof; width $w(\Sigma)$ of a clause set; the Ben-Sasson–Wigderson width-size lower bound $S(\Sigma)=\exp\Omega\!\left(\frac{(w(\Sigma\vdash 0)-w(\Sigma))^2}{|V|}\right)$; exponential separations between tree and general resolution. : [[Complete-Search-Algorithms-for-SAT|Link1]], [[Model-Counting|Link2]]
- **1.17–1.18 Refinements and upper bounds** — VSIDS/DLIS branching heuristics, lookahead, non-chronological backtracking and clause learning turning tree-like search into DAG-like search; worst-case deterministic $k$-SAT upper bounds via case splitting and autarkies.
- **1.19 Classes of easy expressions** — 2-SAT via implication graphs; Horn expressions and their unique minimum model; renameable Horn; extended Horn and CC-balanced classes (via $(0,\pm1)$ matrix / LP relaxation); SLUR (Single Lookahead Unit Resolution); q-Horn; linear autarkies (a partial assignment satisfying every clause it touches); matched expressions; nested satisfiability; minimally unsatisfiable expressions.
- **1.20 Binary Decision Diagrams** — BDD as a DAG representation of a Boolean function's truth table; reduced ordered BDDs (ROBDDs); operations (restrict, constrain/generalized cofactor); variants (ZDD, BMD, ADD, XDD). : [[Complete-Search-Algorithms-for-SAT|Link]]
- **1.21–1.22 Probabilistic analysis and thresholds** — variable-width vs. constant-width random CNF distributions; monotone property $A_X$; sharp vs. coarse threshold; the satisfiability threshold $r_k$; Friedgut's proof that sharp thresholds exist; backbones and the phase-transition analogy with spin glasses.
- **1.23 Stochastic local search** — GSAT, HSAT, GWSAT, WalkSAT/SKC, Novelty+/Adaptive Novelty+, Discrete Lagrangian Method, SAPS. : [[Stochastic-Local-Search-for-SAT|Link]]
- **1.24 Maximum Satisfiability** — MAX-SAT and MAX-2-SAT decision/branch-and-bound algorithms; worst-case bounds parametrized by literals $L$, clauses $m$, variables $n$. : [[Maximum-Satisfiability|Link]]
- **1.25 Nonlinear formulations** — lift-and-project hierarchies (Sherali-Adams, Lovász-Schrijver, Lasserre) over semidefinite programming (SDP); $\sigma$-approximation algorithms; Goemans-Williamson's 0.87856-approximation for MAX-2-SAT via hyperplane rounding; the Gap relaxation and sum-of-squares (SOS) relaxations. : [[Maximum-Satisfiability|Link1]], [[Quantified-Boolean-Formulas|Link2]]
- **1.26 Pseudo-Boolean forms** — pseudo-Boolean functions $f:B^n\to\mathbb{R}$; multilinear polynomial and posiform representations; reduction of general pseudo-Boolean optimization to quadratic form. : [[Proof-Complexity|Link1]], [[Pseudo-Boolean-and-Cardinality-Constraints|Link2]], [[Quantified-Boolean-Formulas|Link3]]
- **1.27 Quantified Boolean formulas** — QBF syntax $Q_1x_1\dots Q_nx_n\varphi$ (prenex form), QCNF/Q3-CNF; QSAT as PSPACE-complete; the polynomial-time hierarchy $\Sigma_k^P,\Pi_k^P,\Delta_k^P$; prefix type of a QBF. : [[Quantified-Boolean-Formulas|Link]]

**Key Questions:**
1. In what precise sense are satisfiability, validity, consistency, and derivability "mutually characterizable," and why did it take over 2000 years (from Aristotle to Tarski) for the syntax/semantics distinction underlying this to be made precise?
2. Why does a lower bound on resolution *width* (Ben-Sasson–Wigderson) translate into a lower bound on resolution *size*, and what does this reveal about why tree resolution (and hence naive DPLL) can be exponentially worse than general resolution with clause learning?
3. Among the "easy" polynomial-time solvable classes (Horn, q-Horn, SLUR, matched, nested, linear-autarky-free), why does the chapter argue that most are "vulnerable to cyclic clause structures" and hence cover a vanishingly small fraction of random formulas — what does this say about the practical relevance of these tractability results?

---
### Chapter 2: CNF Encodings (pp. 75–94)

**Summary:** A survey of how combinatorial problems are transformed into conjunctive normal form (CNF) before being handed to a SAT solver, covering general-purpose CNF transformation techniques, encodings from constraint satisfaction problems (CSPs) to SAT, encodings of common intensional constraints (at-most-one, cardinality, parity), the DIMACS file format, worked case studies, and what makes one encoding "better" than another. : [[CNF-Encodings|Link]]

**Key Definitions & Concepts by Section:**
- **2.2 Transformation to CNF** — CNF as $\bigwedge_i c_i$ of clauses $\bigvee_j l_j$; transformation by pure Boolean algebra (can blow up exponentially) vs. the Tseitin encoding, which introduces one new variable $f\leftrightarrow(\text{subformula})$ per subformula for a linear-size, equisatisfiable CNF; don't-care/unobservable variables arising from encoding choices; CNF-to-3-CNF transformation via auxiliary variables. : [[CNF-Encodings|Link]]
- **2.2.4 Extensional (CSP) encodings** — the direct/sparse encoding ($x_{v,i}$ true iff CSP variable $v=i$, with at-least-one, at-most-one, and conflict clauses); the support encoding (conflict clauses replaced by support clauses over supporting values); the log encoding (bit-indexed SAT variables, exponentially fewer variables); hierarchical, representative-sparse, log-support, and binary-transform variants; the order encoding ($v_{x,a}$ represents $x\le a$) for integer linear constraints, proved to preserve CSP tractability. : [[CNF-Encodings|Link]]
- **2.2.5 Intensional encodings** — at-most-one via pairwise ($O(n^2)$ clauses), ladder ($O(n)$ auxiliary variables and clauses), binary/bitwise ($O(\log n)$ variables), commander, product, and bimander encodings; cardinality constraints (sequential/parallel counter, sorting-network-based encodings); pseudo-Boolean/integer-linear constraints $\sum_i w_ix_i\le k$; the parity constraint $(\bigoplus_i v_i)\leftrightarrow p$ via chained auxiliary variables. : [[CNF-Encodings|Link]]
- **2.2.6 DIMACS format** — the `p cnf variables clauses` preamble and integer-literal clause representation that standardized SAT benchmarking. : [[CNF-Encodings|Link]]
- **2.3 Case studies** — N-queens (Nadel's Q1–Q9 models illustrating variable-choice tradeoffs, implied clauses, and symmetry-breaking clauses); all-interval series (Tseitin variables exploiting subformula *polarity* to halve clause count, conditional symmetry); stable marriages (non-obvious "positional" variable definitions $x_{i,p}$ avoiding a direct man–woman variable, and the pitfall of omitting common-sense axioms); modelling differences required for local search vs. DPLL solvers. : [[CNF-Encodings|Link]]

**Key Questions:**
1. Why does exploiting the *polarity* of a subformula (as in the all-interval-series Tseitin encoding) let one drop half of the biconditional's clauses, and under what condition would this optimization be unsound?
2. The order encoding is proved to transform a tractable CSP into a tractable SAT instance — what structural property of the direct/log encodings can fail to preserve, and why does representing primitive comparisons $x\le a$ rather than domain-value assignments make the difference?
3. Why might a SAT encoding that is compact and effective for DPLL-style backtracking search perform poorly under stochastic local search (and vice versa), as illustrated by the minimal-disagreement-parity-learning example?

---
### Chapter 3: Complete Algorithms (pp. 101–128)

**Summary:** A unified treatment of sound-and-complete SAT algorithms organized into four families — existential quantification, inference rules, systematic search, and the combination of search with inference — culminating in the implication-graph/conflict-driven-clause-learning view of modern solvers. : [[Complete-Search-Algorithms-for-SAT|Link]]

**Key Definitions & Concepts by Section:**
- **3.2 Preliminaries** — a clause as a set of literals over distinct variables; CNF as a set of clauses; $\Delta$ valid iff $\Delta=\emptyset$, inconsistent iff $\emptyset\in\Delta$; clause subsumption; conditioning $\Delta|L$ (removing satisfied clauses, shrinking clauses containing $\neg L$).
- **3.2.1 Resolution** — the resolution rule deriving $(C_i-\{P\})\cup(C_j-\{\neg P\})$; refutation completeness of resolution on CNF; unit resolution as an incomplete but linear-time special case. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **3.3 Existential quantification** — $\exists P\Delta := (\Delta|P)\vee(\Delta|\neg P)$; the DP (Davis-Putnam) algorithm / directional resolution via bucket elimination, with $O(n\exp(w))$ complexity where $w$ is the treewidth of the CNF's connectivity graph; symbolic SAT solving via (ordered, reduced) BDDs and early quantification. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **3.4 Inference rules** — Stålmarck's algorithm (triplet form $p\Leftrightarrow(q\otimes r)$, simple/propagation rules, 0-saturation, the dilemma rule and $n$-saturation as increasingly deep case-splitting with shared-conclusion extraction); HeerHugo (CNF-based analogue with unit resolution, subsumption, restricted resolution, and a branch/merge rule). : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
- **3.5 Search: DPLL** — the search tree over truth assignments explored depth-first via conditioning; the termination tree (the actually-explored subtree) as a complexity/difficulty measure; unit resolution (a.k.a. Boolean constraint propagation) pruning the search tree. : [[CNF-Encodings|Link]]
- **3.6 Combining search and inference** — chronological vs. non-chronological backtracking; the implication graph recording how decisions and unit propagations lead to a conflict; deriving a conflict-driven (learned) clause by cutting the implication graph; asserting clauses and backtracking to the assertion level; clause learning's relationship to resolution proof complexity; clause deletion policies; restarts; certifying SAT algorithms (proof-producing solvers).

**Key Questions:**
1. In directional resolution (the DP algorithm via bucket elimination), why does the *variable order* alone determine whether the algorithm runs in polynomial or exponential time on the same formula, and how does this connect to treewidth of the connectivity graph?
2. How does Stålmarck's $n$-saturation (retaining only conclusions common to both branches of a case split) differ in character from DPLL's search, and why does the author frame it as "oriented toward finding short proofs"?
3. What precisely is a conflict-driven clause derived from the implication graph, and why does adding such clauses turn what would otherwise be a tree-shaped DPLL search into a DAG-shaped search space?

---
### Chapter 4: CDCL SAT Solving (pp. 133–182)

**Summary:** The core chapter of the handbook, giving a modern, rewritten account of Conflict-Driven Clause Learning (CDCL) — the technique the authors credit as "the sole reason" SAT solvers scaled from a few hundred to millions of variables — covering its formal machinery, implementation, practical uses, and historical development. : [[Complete-Search-Algorithms-for-SAT|Link1]], [[Maximum-Satisfiability|Link2]]

**Key Definitions & Concepts by Section:**
- **4.2 Preliminaries** — CNF as a set of clauses of literals; assignment function $\nu:V\to\{0,u,1\}$ (partial vs. complete assignments); clause status (falsified/satisfied/unit/unresolved); the unit clause rule and its iteration as unit propagation / Boolean constraint propagation (BCP); for each variable $x_i$: value $\nu(x_i)$, antecedent $\alpha(x_i)$ (the unit clause that implied it, or $d$ for decisions, or $n$ if unassigned), and decision level $\delta(x_i)$; the implication graph $I=(V_I,E_I)$ built from antecedents, with a special conflict vertex $\bot$ when a clause is falsified; the classical DPLL algorithm restated in this notation.
- **4.3.1 CDCL organization** — differences from DPLL: non-chronological backtracking driven by learned clauses, backtracking after *every* conflict, periodic restarts, clause deletion, lazy data structures.
- **4.3.1.1 Clause learning / conflict analysis** — tracing antecedents of current-decision-level variables in FIFO order via the implication graph until only lower-decision-level literals remain, yielding a learned (conflict-driven) asserting clause; worst-case linear-time conflict analysis. : [[Conflict-Driven-Clause-Learning|Link]]
- **(4.3 continued, by known structure)** — branching heuristics (e.g. VSIDS-style activity scores), watched-literal data structures for efficient BCP, clause-deletion/activity-based learnt-clause management, restart policies, and preprocessing/inprocessing integration.
- **4.4 Using CDCL solvers** — CDCL as an NP-oracle underlying MaxSAT, enumeration, quantified extensions, and minimal-set (MUS/MCS) algorithms. : [[Proofs-of-Unsatisfiability|Link]]
- **4.5–4.6 Impact and historical perspective** — CDCL's role in propositional proof complexity (its proof system is essentially resolution) and the historical lineage GRASP → SATO → Chaff → modern solvers, driven by ATPG, timing analysis, planning, and SAT-based model checking applications.

**Key Questions:**
1. In the implication-graph model, why is the antecedent of an *implied* variable defined only for unit-propagated variables (never for decision variables), and how does the recursive decision-level formula (Eq. 4.3) use this to compute a literal's decision level from its antecedent's other literals?
2. Walk through why the conflict-analysis procedure (tracing the implication graph FIFO from the conflict vertex $\bot$ back to a single decision-level-4 variable) is guaranteed to terminate with an *asserting* clause containing exactly one current-decision-level literal — what would go wrong if it didn't stop there?
3. The chapter states CDCL's underlying proof system is resolution, yet CDCL solvers vastly outperform naive Davis-Putnam resolution in practice — what does this imply about the role of *search* (branching, restarts, learnt-clause activity) versus the proof system itself in CDCL's practical success?

---
### Chapter 5: Look-Ahead Based SAT Solvers (pp. 183–210)

**Summary:** Presents the look-ahead architecture as a complementary alternative to conflict-driven (CDCL) search — strong specifically on low-density or small-diameter (random and structured unsatisfiable) instances — built on DPLL but replacing cheap heuristics with an expensive per-node "look-ahead" that tentatively assigns and propagates each candidate variable before branching. : [[Look-Ahead-Solving|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Domain of application** — the density (clause/variable ratio) vs. diameter (longest shortest path in the resolution graph, where clauses are vertices connected if they share exactly one clashing literal) characterization of where look-ahead beats conflict-driven solving; local clusters as the structural reason conflict-driven solvers win on structured problems with large diameter. : [[Combinatorial-Applications-of-SAT|Link]]
- **5.2.1 The look-ahead architecture** — DPLL with unit propagation $F[x=B]$; the `LookAhead` procedure, which both selects the decision variable and simplifies $F$; the `Diff`/`MixDiff` decision heuristics measuring formula reduction under tentative assignment (product of reductions on both branches, e.g. $1024\cdot LR+L+R$, favoring a balanced search tree); direction heuristics for branch order; failed-literal detection (a look-ahead on $x$ reaching a conflict forces $\neg x$); the `PreSelect` procedure restricting look-aheads to a variable subset $P$ for efficiency. : [[Look-Ahead-Solving|Link]]
- **5.2.2 History** — the Böhm solver (first look-ahead-adjacent solver, eager two-dimensional linked-list data structures) through csat and posit (first true `LookAhead` procedures, MixDiff heuristic, direction heuristics, principled preselection).
- **(5.3–5.5, by known structure)** — heuristics for preselection and direction; additional look-ahead reasoning (e.g. detecting equivalent/forced literals, adding binary clauses); eager data structures for reducing unit-propagation cost within look-ahead.

**Key Questions:**
1. Why does high formula *density* penalize look-ahead solvers specifically (via the cost of unit propagation) while large *diameter* penalizes conflict-driven solvers specifically (via the locality of learned clauses) — and what does this predict about which architecture wins on random vs. structured industrial instances?
2. In the `MixDiff` heuristic $1024\cdot LR+L+R$, why is the *product* $LR$ (not the sum) the primary term, and what search-tree property is this designed to optimize for?
3. How does failed-literal detection during look-ahead effectively fold a form of unit propagation *and* limited resolution reasoning into variable selection itself, rather than treating branching and inference as separate phases the way CDCL does?

---
### Chapter 6: Incomplete Algorithms (pp. 213–226)

**Summary:** Surveys stochastic local search (SLS) and other incomplete methods for SAT — algorithms with one-sided error that can find solutions but never prove unsatisfiability — from the foundational GSAT and Walksat through clause-reweighting extensions, the Discrete Lagrangian Method, phase transitions in random $k$-SAT, and survey propagation. : [[Complete-Search-Algorithms-for-SAT|Link]]

**Key Definitions & Concepts by Section:**
- **Introduction** — the search landscape view: a formula $F$ defines a height function on $\{0,1\}^n$ (number of violated clauses), turning SAT into a search for a global minimum (height 0), and MAX-SAT into a search for the (possibly nonzero-height) global minimum.
- **6.1 GSAT and Walksat** — GSAT: greedy descent that flips the variable maximizing the decrease in unsatisfied clauses per step, with observed "plateaus" (sideways-move-connected regions) rather than true local-minimum traps; Walksat: focuses on a randomly chosen *unsatisfied* clause and picks a freebie move (zero break-count), else with noise probability $p$ a random-walk move or else the minimum-break-count greedy move; Papadimitriou's $O(n^2)$-expected-time randomized 2-SAT algorithm as the theoretical ancestor of the focusing idea; Cohen's construction showing the "freebie" rule can in principle cycle (rare in practice).
- **6.2 Extensions** — clause (re-)weighting / "flooding" local minima by increasing weights of currently-unsatisfied clauses; SAPS/RSAPS (scaling and probabilistic smoothing) and PAWS (pure additive weighting); Schuurmans–Southey's depth/mobility/coverage framework for evaluating SLS effectiveness.
- **6.3 Discrete Lagrangian Method (DLM)** — casting SAT as constrained optimization $\min N(x)=\sum_iU_i(x)$ s.t. $U_i(x)=0$; the discrete Lagrangian $L_d(x,\lambda)=N(x)+\sum_i\lambda_iU_i(x)$; saddle points $(x^*,\lambda^*)$ corresponding to locally optimal SAT solutions; search via a difference gradient $\Delta_xL_d$ performing descent in $x$ and ascent in $\lambda$. : [[Stochastic-Local-Search-for-SAT|Link]]
- **(6.4–6.6, by known structure)** — the phase-transition phenomenon in random $k$-SAT as a driver of 1990s incomplete-method research, and survey propagation as a message-passing technique inspired by statistical physics for solving formulas near the satisfiability threshold.

**Key Questions:**
1. Why do GSAT's "plateaus" rarely trap the search in genuine local minima on high-dimensional formulas, and how does this explain why GSAT succeeds despite being a purely greedy method?
2. In Walksat, what specific role does *focusing* the flip choice on variables from a randomly-selected unsatisfied clause play in making the algorithm scale to formulas with thousands of variables, as opposed to flipping any variable in the formula?
3. How does casting SAT as a constrained optimization problem with a redundant per-clause constraint $U_i(x)=0$ (Discrete Lagrangian Method) give a principled derivation for what earlier local-search work did with ad-hoc clause-reweighting heuristics?

---
### Chapter 7: Proof Complexity and SAT Solving (pp. 233–350)

**Summary:** A survey connecting proof complexity (the mathematical study of how large proofs must be in a given proof system) to practical SAT solving, explaining how CDCL, algebraic, pseudo-Boolean, and preprocessing-augmented solvers each correspond to an underlying proof system, and reviewing known lower/upper bounds on proof size for these systems — focused almost entirely on unsatisfiable formulas, since proof complexity has essentially nothing rigorous to say about satisfiable ones. : [[Proof-Complexity|Link]]

**Key Definitions & Concepts by Section:**
- **7.2 Preliminaries** — literal $x^\sigma$; clause/CNF-as-sets convention; clause subsumption; width of a clause/formula; the standard width-preserving-ish conversion of a wide clause into a chain of 3-clauses via auxiliary variables; a proof system as a poly-time-checkable predicate $P(x,\pi)$ satisfying completeness and soundness; polynomial boundedness; one system *polynomially simulating* another; refutation systems (for unsatisfiable CNFs) vs. proof systems for tautologies, related by the DNF-negation duality.
- **7.3–7.4 Resolution** — the resolution proof system as the formal counterpart of CDCL search; tree-like vs. general (DAG-like) resolution; width and space measures of resolution proofs; known exponential lower bounds (pigeonhole principle, Tseitin formulas, random $k$-CNF) via the width-size and size-space trade-off methods.
- **7.5 Algebraic proof systems** — Nullstellensatz (certifying unsatisfiability via a polynomial identity $\sum h_ip_i=1$ over clause-derived polynomials) and polynomial calculus (a dynamic, Gröbner-basis-style refinement); their correspondence to algebraic SAT-solving approaches. : [[Proof-Complexity|Link]]
- **7.6–7.7 Cutting planes** — the cutting-planes proof system operating on linear inequalities over $\{0,1\}$ variables, corresponding to conflict-driven pseudo-Boolean solving; complexity results distinguishing general cutting planes from resolution-derived special cases.
- **7.8 Extended resolution and DRAT** — extended resolution (allowing definition of new variables for subformulas, exponentially stronger than plain resolution in the worst case) and the DRAT proof format used to certify modern CDCL solvers with pre-/inprocessing. : [[Proof-Complexity|Link1]], [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link2]]
- **7.9–7.10 Frege systems** — Frege and extended Frege systems (line-based proofs over arbitrary Boolean connectives with modus-ponens-style rules) and bounded-depth Frege as a restriction relevant to circuit complexity.

**Key Questions:**
1. Why does the chapter restrict almost all of its rigorous results to *unsatisfiable* formulas, and what makes proof complexity fundamentally ill-suited to explaining solver performance on satisfiable instances?
2. What is the precise correspondence between resolution refutations and CDCL search traces, and why does a resolution *width* lower bound translate into a *size* lower bound that limits what any CDCL-based solver can achieve on formulas like the pigeonhole principle?
3. Why is extended resolution believed to be exponentially more powerful than plain resolution, and what practical role does the DRAT proof format play in letting modern CDCL solvers (which use inprocessing techniques resolution alone cannot justify) still produce checkable unsatisfiability certificates?

---
### Chapter 8: Fundaments of Branching Heuristics (pp. 351–386)

**Summary:** Develops a rigorous mathematical theory of branching heuristics for backtracking (mainly look-ahead) SAT solvers, showing that comparing candidate branchings reduces to comparing "branching tuples" via a canonical projection function $\tau$, and using this theory to justify (rather than merely empirically observe) standard practices like the product rule for combining branch distances. : [[Branching-Heuristic-Theory|Link1]], [[Conflict-Driven-Clause-Learning|Link2]]

**Key Definitions & Concepts by Section:**
- **8.2 General framework** — a branching $B_i=(b_1,\dots,b_k)$ splits a problem into subproblems; a measure $\mu(F)$ of problem complexity (e.g. number of variables, viewed as a logarithm of true complexity); a distance $d(F,F')>0$ estimating branch progress; the homogeneity assumption (a branching situation recurs elsewhere in the tree) and the "mathematical running time" abstraction (search-tree node count).
- **8.3 Branching tuples and $\tau$** — a branching tuple $t=(t_1,\dots,t_k)\in(\mathbb{R}_{>0})^k$; the canonical projection $\tau(t)$, the unique positive root of $\sum_ix^{-t_i}=1$; smaller $\tau$-value means a better branching; $\tau$ as inducing a generalized mean $T$. : [[Branching-Heuristic-Theory|Link]]
- **8.4 Estimating tree sizes** — bounding enumeration-tree size via probability distributions on branching tuples derived through $\tau$; an optimality result justifying the "logarithmic" complexity-measure viewpoint. : [[Branching-Heuristic-Theory|Link]]
- **8.5 Canonicity of $\tau$** — proof that $\tau$'s induced linear quasi-order on branching tuples is (in general) the *only* consistent way to project a tuple to a single comparable number.
- **8.6 Alternative projections** — for binary branching tuples $(t_1,t_2)$, relating the sum rule $t_1+t_2$ and product rule $t_1\cdot t_2$ to $\tau$, giving an analytical (not just empirical) argument for why the product rule outperforms the sum rule in practice.
- **8.7–8.9 Concrete distances and orders** — known distance functions used in practical look-ahead SAT solving (cf. Chapter 5's Diff/MixDiff), methods for improving distance functions, and choosing the order in which branches are explored.
- **8.10 Outlook** — applicability of the general theory beyond Boolean CNF-SAT.

**Key Questions:**
1. Why is a branching's quality reducible to a single tuple of positive real "distances," and in what precise sense does the $\tau$-function's root of $\sum_ix^{-t_i}=1$ serve as the canonical way to compare two such tuples?
2. What does it mean for $\tau$'s induced ordering to be the *only* general-purpose projection (Section 8.5), and how does this rule out ad hoc alternatives to $\tau$ except under special circumstances?
3. For binary branchings, why does the analytical relationship between $\tau$ and the product rule $t_1\cdot t_2$ (versus the sum rule $t_1+t_2$) explain — rather than merely correlate with — the empirical superiority of product-based heuristics like MixDiff in look-ahead solvers?

---
### Chapter 9: Preprocessing in SAT Solving (pp. 391–419)

**Summary:** Surveys the simplification techniques applied to CNF formulas between encoding and solving — from classical unit propagation and pure-literal elimination to bounded variable elimination and clause-elimination techniques — that became, alongside CDCL, a decisive driver of SAT solver performance, while also covering solution reconstruction and the risks preprocessing poses to solver completeness/efficiency guarantees. : [[Preprocessing-and-Inprocessing|Link1]], [[Complete-Search-Algorithms-for-SAT|Link2]], [[Maximum-Satisfiability|Link3]]

**Key Definitions & Concepts by Section:**
- **9.1 Introduction** — preprocessing situated between encoding and solving; inprocessing (interleaving preprocessing with search, dominant since ~2013); bounded variable elimination (BVE, via SatELite) as the single biggest performance jump in SAT-competition history; the tension that preprocessing removing clauses can be catastrophic in the worst case (Haken's exponential resolution lower bound for the pigeonhole principle becomes polynomial once "definition clauses" are added — but preprocessing techniques like BVE or blocked-clause elimination can strip exactly these clauses back out); the two broad categories of technique: resolution-rule-based (unit propagation, BVE, hyper binary resolution, distillation, vivification) vs. redundancy-elimination-based (subsumption, hidden literal elimination, equivalent-literal substitution, blocked clause elimination). : [[Complete-Search-Algorithms-for-SAT|Link]]
- **9.2 Classical techniques** — unit propagation / Boolean constraint propagation (BCP) as repeated unit resolution; pure literal elimination; basic clause elimination; connected-component detection for splitting formulas into independent subparts; failed-literal detection (probing).
- **9.3 Resolution-based preprocessing** — bounded variable elimination: replacing all clauses mentioning a variable $v$ with all resolvents on $v$, bounded to avoid blow-up; hyper binary resolution; distillation and vivification as more expensive probing-based simplifications. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **9.4 Beyond resolution** — clause elimination techniques including blocked clause elimination (removing clauses that cannot participate in any resolution refutation) and its generalizations. : [[Proofs-of-Unsatisfiability|Link]]
- **9.5 Solution reconstruction** — since many techniques preserve only equisatisfiability (not logical equivalence), a satisfying assignment for the preprocessed formula must be mapped back to one for the original formula. : [[Preprocessing-and-Inprocessing|Link]]
- **9.6 Structure-based preprocessing** — analogous simplifications on Boolean-circuit-level representations (e.g. cone-of-influence reduction). : [[Non-Clausal-and-Circuit-Based-Satisfiability|Link1]], [[Preprocessing-and-Inprocessing|Link2]]

**Key Questions:**
1. Why can a preprocessing technique that only shrinks a formula (fewer variables/clauses) actually make it *harder* to solve, as illustrated by the pigeonhole-principle example where removing "definition clauses" turns a polynomial-size resolution refutation back into an exponential one?
2. What is the difference between a formula being reduced to an *equisatisfiable* vs. a *logically equivalent* one, and why does this distinction force preprocessing techniques to carry along a solution-reconstruction procedure?
3. Why did the shift from standalone preprocessing to *inprocessing* (interleaving simplification with CDCL search) require extra care regarding soundness, given that clause learning and clause forgetting are themselves already modifying the formula during search?

---
### Chapter 10: Random Satisfiability (pp. 437–458)

**Summary:** A rigorous-mathematics survey of random $k$-SAT — the study of formulas $F_k(n,m)$ with $m$ uniformly random $k$-clauses over $n$ variables — covering the (still-open) Satisfiability Threshold Conjecture, current bounds on the threshold location, generative/geometric models of the solution space, and the performance limits of known algorithms on sparse random instances. : [[Random-Satisfiability-and-Phase-Transitions|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 Introduction** — $F_k(n,m)$: $m$ clauses chosen uniformly without replacement from all non-trivial $k$-clauses; "with high probability" (w.h.p., probability $\to1$) vs. "with uniformly positive probability" (w.u.p.p.); early bounds ($r\ge2^k\ln2\Rightarrow$ unsatisfiable w.h.p.; $r<2^k/k\Rightarrow$ satisfiable w.u.p.p.) fixing $m=\Theta(n)$ as the interesting density regime; Chvátal–Szemerédi's exponential resolution-complexity result for random $k$-CNF; the experimentally observed hardness peak near the empirical crossover density, linked to statistical-physics phase transitions. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **10.2.1 The Satisfiability Threshold Conjecture** — the conjecture that $\Pr[F_k(n,rn)\text{ sat}]\to\mathbf{1}_{r<r_k}$ for a critical density $r_k$; Friedgut's theorem establishing a sharp threshold *sequence* $r_k(n)$ (existence of $r_k$ itself remains open); best rigorous bounds $2^k\ln2-\Theta(k)\le r_k\le2^k\ln2-\Theta(1)$; the second moment method (used for the lower bound, via *balanced* satisfying assignments) vs. simple union-bound/local-maximality arguments (upper bound); "presults" — statements combining rigorous math with unproven statistical-physics assumptions. : [[Random-Satisfiability-and-Phase-Transitions|Link]]
- **(10.3–10.10, by known structure)** — random MAX-$k$-SAT; physical predictions for solution-space geometry (clustering/condensation phenomena); generative models beyond uniform random $k$-CNF; algorithmic results (unit-clause and related heuristics, belief/survey propagation) and the gap between the satisfiability threshold and the largest density at which any known efficient algorithm succeeds; backtracking algorithm analyses; exponential running time results for $k>3$.

**Key Questions:**
1. Why does the chapter emphasize that random-$k$-SAT hardness (to the extent it exists) comes from phase transitions in *solution-space geometry* rather than from the threshold in the *probability of satisfiability* itself — what is the distinction being drawn?
2. The second-moment-method lower bound on $r_k$ works only by restricting attention to "balanced" satisfying assignments — why is this restriction a technical necessity of the method rather than a meaningful restriction on the formulas themselves?
3. Given that the best known upper bound on $r_k$ and the largest density at which any efficient algorithm is proven to find solutions (the "algorithmic lower bound") diverge sharply for larger $k$ (Table 10.1), what does this gap suggest about the existence of an "algorithmic barrier" distinct from the satisfiability threshold itself?

---
### Chapter 11: Exploiting Runtime Variation in Complete Solvers (pp. 463–477)

**Summary:** Explains why backtrack-style complete SAT solvers show dramatic, sometimes unbounded-variance runtime variation across heuristic choices and random seeds, formalizes this via heavy/fat-tailed distribution theory, and shows how randomized restarts exploit this variation (together with the existence of small "backdoor" variable sets) to dramatically improve practical performance. : [[Runtime-Variation-and-Solver-Engineering|Link1]], [[Branching-Heuristic-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **Introduction** — "exceptionally hard" instances (Hogg-Williams, Gent-Walsh): instances in the *under-constrained* region that are harder than even critically-constrained instances for a *particular* solver/variable-naming, later shown to be an artifact of the search method rather than the instance itself — hence researchers report the *median*, not the mean, running time; backdoor sets: a small subset of variables whose correct assignment collapses the rest of the problem to easy reasoning, explaining occasional "lucky" fast solves.
- **11.1.1 Fat and heavy tailed behavior** — kurtosis $\mu_4/\mu_2^2$ distinguishing fat-tailed (leptokurtic, kurtosis $>3$) distributions; heavy-tailed distributions with Pareto-like tail decay $\Pr[X>x]\sim Cx^{-\alpha}$, having some infinite moments (possibly infinite mean/variance) unlike the Gaussian; the index of stability $\alpha$ determining which moments are finite. : [[Runtime-Variation-and-Solver-Engineering|Link]]
- **11.2 Exploiting runtime variation** — randomization of variable/value-selection heuristics (even simple random tie-breaking) inducing heavy-tailed per-instance runtime distributions; restart strategies as a direct exploitation of heavy tails: since many independent randomized runs are individually likely to be short, periodically abandoning and restarting a run (with a different random seed) sharply reduces expected time to solution compared to running one long randomized search to completion. : [[Runtime-Variation-and-Solver-Engineering|Link]]
- **11.3 Conclusion** — the interplay between backdoor-set size, heavy-tailed runtime, and the practical effectiveness of restart policies in modern solvers.

**Key Questions:**
1. Why did the discovery of "exceptionally hard" instances turn out not to be a property of the instance itself, and what does this imply about using the mean (rather than the median) to characterize search difficulty?
2. What is the mathematical content of a heavy-tailed runtime distribution (Pareto-like decay, possibly infinite mean), and why does this directly justify restart strategies as an algorithmic exploit rather than a discretionary tuning heuristic?
3. How does the existence of small backdoor sets in structured real-world instances explain both occasional extremely fast "lucky" solves and the heavy-tailed nature of the overall runtime distribution?

---
### Chapter 12: Automated Configuration and Selection of SAT Solvers (pp. 481–500)

**Summary:** Surveys meta-algorithmic techniques for optimizing SAT solving in practice: automated algorithm configuration (tuning a solver's exposed parameters to a distribution of instances) and per-instance algorithm selection (choosing among a portfolio of solvers per instance), plus hybrids that combine configuration, selection, and scheduling. : [[Runtime-Variation-and-Solver-Engineering|Link]]

**Key Definitions & Concepts by Section:**
- **12.1 Introduction** — no single best SAT solver exists because heuristic performance is highly instance-sensitive; algorithm configuration and algorithm selection as meta-algorithmic design techniques. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **12.2 Algorithm configuration** — formal statement: given algorithm $A$ with parameter space $\Theta=\Theta_1\times\cdots\times\Theta_n$, an instance distribution $D$, and cost metric $c:\Theta\times\Pi\to\mathbb{R}$, find $\theta$ minimizing expected cost; the blackbox function $f(\theta)$ (only evaluable by running $A$, not analyzable); categorical/conditional/forbidden parameter combinations; Programming by Optimization (PbO) — designing algorithms with many exposed parametric design choices and leaving evaluation to automated configuration rather than manual tuning; ParamILS (iterated local search over configuration space, with an incumbent, random restarts, and the BasicILS vs. FocusedILS variants trading off evaluation-budget allocation) and adaptive capping (early termination of clearly-losing runs). : [[Runtime-Variation-and-Solver-Engineering|Link]]
- **12.3 Per-instance algorithm selection** — choosing a solver from a small portfolio per instance, typically via cheap instance-feature extraction and a learned performance-prediction model (e.g. SATzilla-style approaches). : [[Runtime-Variation-and-Solver-Engineering|Link]]
- **12.4 Related approaches** — combining configuration and selection; algorithm schedules (running several solvers/configurations in sequence or parallel rather than picking one); parameter-importance analysis; dynamic/reactive parameter control; using configuration techniques to find solver bugs. : [[SAT-Techniques-for-Richer-Logics|Link]]
- **12.5 Conclusions and open challenges.**

**Key Questions:**
1. Why is the algorithm-configuration objective function $f(\theta)$ described as a "blackbox function," and what does this imply about why configuration must be done by repeated empirical evaluation rather than analytical optimization?
2. How does FocusedILS's strategy of starting with a single run per new configuration and only gradually matching the incumbent's evaluation budget address the tension between evaluation cost and statistical reliability that BasicILS does not?
3. Why does Programming by Optimization propose that developers expose *more* parameters (encoding every plausible design idea) rather than fewer, when conventional software engineering wisdom favors minimizing configuration surface?

---
### Chapter 13: Symmetry and Satisfiability (pp. 509–566)

**Summary:** Develops the theory of symmetries of Boolean functions and their CNF representations using group theory, shows how to detect these symmetries by reduction to colored-graph automorphism, and covers symmetry-breaking predicates (SBPs) that prune symmetric regions of the search space — including a SAT-search-inspired graph automorphism algorithm (saucy) that emerged from this line of work. : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 Motivating example** — a symmetry of a Boolean function $f$ is an input transformation leaving $f$ invariant; symmetries form a group under composition (illustrated via a symmetry composition table); a function's solution space partitions into equivalence classes under its symmetry group; a symmetry-breaking predicate (SBP) is a filter selecting one representative per equivalence class.
- **13.2–13.3 Boolean algebra, partitions, and group theory** — the 2-valued Boolean algebra; minterms/maxterms; implicants/implicates and prime implicants/implicates; DNF/CNF and minimal DNF/CNF; partitions of a set and the lattice of partitions; group $\langle G,*\rangle$, group order, group isomorphism, subgroup, proper/trivial subgroups, cosets, generators and cyclic groups, permutations, and the symmetric group.
- **13.4 CNF symmetry** — symmetries specifically of a CNF formula's literal/clause structure. : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]
- **13.5–13.6 Graph automorphism reduction** — the colored graph automorphism problem; encoding a CNF formula's symmetry-detection problem as automorphism-finding on an associated colored graph.
- **13.7 Symmetry breaking** — constructing SBPs from detected symmetry generators so that a SAT solver's search only needs to explore one representative per symmetric equivalence class. : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]
- **13.8 The saucy algorithm** — a graph automorphism algorithm inspired directly by the backtrack-search architecture of SAT solvers, achieving high scalability on the graphs arising from CNF symmetry detection. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **13.9–13.10 Summary and bibliographic notes** — the full symmetry detection → breaking pipeline, and its applications and history.

**Key Questions:**
1. Why does the set of symmetries of a Boolean function always form a group under composition, and what does the closure of the composition table (Table 13.2 in the chapter) demonstrate about the completeness of a proposed set of symmetries?
2. How does reducing CNF symmetry detection to *colored* graph automorphism (rather than plain graph automorphism) correctly capture the distinction between variables, their negations, and clauses?
3. In what sense is saucy's graph automorphism algorithm "inspired by" SAT backtrack search, and why would techniques honed for CNF search (e.g. pruning, refinement) transfer usefully to the seemingly different problem of finding graph automorphisms?

---
### Chapter 14: Minimal Unsatisfiability and Autarkies (pp. 571–627)

**Summary:** Studies two dual notions of redundancy in CNF formulas — minimal unsatisfiability (unsatisfiable formulas that become satisfiable if any clause is removed) and autarkies (partial assignments that satisfy every clause they touch, hence can be safely applied without affecting overall satisfiability) — as tools for understanding formula structure and improving solvers. : [[Symmetry-Minimal-Unsatisfiability-and-Autarkies|Link]]

**Key Definitions & Concepts by Section:**
- **14.1 Introduction** — minimal unsatisfiable formulas (MU): unsatisfiable, but removing any single clause makes the remainder satisfiable; MU is $DP$-complete (the class of differences of two NP problems), shown via reduction from UNSAT-SAT. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **14.2 Deficiency** — deficiency $d(F)=n-k$ (clauses minus variables) and maximal deficiency $d^*(F)=\max\{d(G):G\subseteq F\}$; every $F\in$ MU has $d(F)>0$; MU($k$) (fixed deficiency $k$) is solvable in polynomial time, while sup-MU($k$) (containing an MU($k$) subformula) is NP-complete; the variable-clause matrix representation; splitting a formula $F\in$ MU on a variable $x$ into two smaller MU-formulas $F_x,F_{\neg x}$.
- **14.3–14.4 Resolution/homomorphism and special classes** — structural characterizations and homomorphism-based reasoning about MU formulas; special tractable subclasses.
- **14.5–14.7 Extensions** — extension of MU concepts to non-clausal formulas; minimal falsity for QBF; applications and experimental results.
- **14.8–14.9 Autarkies** — an autarky for CNF $\varphi$ is a partial assignment satisfying every clause of $\varphi$ it touches (a pure literal is a trivial autarky); applying an autarky to $\varphi$ preserves satisfiability status; the autarky monoid structure.
- **14.10–14.13 Finding and generalizing autarkies** — algorithms for finding/using autarkies; autarky systems using weaker forms of autarkies; connections to combinatorics; generalizations and extensions.
- **14.14 Conclusion** — open problems in both areas.

**Key Questions:**
1. Why must every minimally unsatisfiable formula have positive deficiency (more clauses than variables), and how does the splitting operation on a variable $x$ preserve membership in MU while producing two strictly smaller MU formulas?
2. Why is deciding membership in MU($k$) for *fixed* $k$ polynomial-time, while deciding whether a formula merely *contains* an MU($k$) subformula (sup-MU($k$)) is NP-complete — what does this reveal about the difference between recognizing a global structural property and detecting its local presence?
3. Why does applying an autarky to a formula never change its satisfiability status, and how does this let a solver safely simplify a formula by discovering and eliminating autarkies without any risk of losing solutions?

---
### Chapter 15: Proofs of Unsatisfiability (pp. 635–661)

**Summary:** Covers the practical engineering of unsatisfiability proofs (as opposed to Chapter 7's theoretical proof complexity) — clausal proof formats, how they let modern solvers' results be checked efficiently and even by formally verified checkers, and their role in validating both SAT-competition results and machine-checked mathematical theorems. : [[Proofs-of-Unsatisfiability|Link]]

**Key Definitions & Concepts by Section:**
- **15.1 Introduction** — a clausal proof of unsatisfiability is a sequence of clauses each claimed redundant (its addition preserves satisfiability), ending in the empty clause; hints as optional information (e.g. resolution antecedents) that speed up per-step validity checking at the cost of larger proofs; witnesses as *mandatory* hint-like information for strong proof systems where checking validity without them is NP-complete; the tradeoff driving industry practice toward hint-free proofs (e.g. DRAT) since 2013, when SAT Competition made unsatisfiability proofs mandatory. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **15.2 Proof systems** — satisfiability-preservation as the most general (but not efficiently checkable) redundancy notion, motivating syntactic proof systems; formal preliminaries: literal/clause/formula-as-sets, assignment restriction $C\,|\,\alpha$ and $F\,|\,\alpha$, a clause "blocking" an assignment; unit propagation and conflict derivation; logical equivalence vs. equisatisfiability; $F\models_1F'$ (implication via unit propagation); resolution (the resolvent $C=C_1\otimes C_2$, resolution chains, non-associativity of the resolution operator); RUP (reverse unit propagation) clauses — a clause $C$ is RUP w.r.t. $F$ if $F\models_1\overline{C}$ derives a conflict, which is exactly the property learned CDCL clauses satisfy. : [[Proof-Complexity|Link1]], [[Quantified-Boolean-Formulas|Link2]]
- **(15.3–15.7, by known structure)** — proof search strategies; proof formats (DRUP, DRAT, LRAT, etc.) and their tradeoffs; how solvers produce proofs during practical solving (as a byproduct of conflict analysis and inprocessing); proof validation/processing (including formally verified checkers); applications (interpolation, MUS extraction, verifying results like the Boolean Pythagorean Triples problem and Erdős Discrepancy Theorem).

**Key Questions:**
1. Why is "satisfiability preservation" the most general notion of clause redundancy but unusable directly as a proof system, and how do syntactic criteria like RUP restore efficient checkability while still capturing what CDCL solvers actually learn?
2. What is the fundamental tradeoff between hint-included and hint-free (e.g. DRAT-style) proof formats, and why has the SAT community converged on hint-free formats for competition validation despite the extra checker-side search they require?
3. Why does verifying certain strong proof-system steps (beyond resolution) require a *witness* rather than an optional hint — what does "NP-complete to check without it" mean operationally for a proof checker?

---
### Chapter 16: Worst-Case Upper Bounds (pp. 669–688)

**Summary:** Surveys deterministic algorithms with the best-known worst-case time bounds for SAT and $k$-SAT, the tractable/intractable dichotomy for restricted classes, and how $k$-SAT bounds are lifted to bounds for general SAT.

**Key Definitions & Concepts by Section:**
- **16.1 Preliminaries** — parameters $n$ (variables), $m$ (clauses), $l$ (literal occurrences), clause density $m/n$; formula restriction $F[A]$; the languages SAT, $k$-SAT, SAT-$f$/$k$-SAT-$f$ (bounded variable occurrence), Unique $k$-SAT (promise problem: at most one satisfying assignment); the binary entropy function $H(x)=-x\log x-(1-x)\log(1-x)$; transformation rules preserving satisfiability: unit clause elimination, subsumption, resolution (including resolution-with-subsumption, DP-style variable elimination $DP_a(F)$, and bounded resolution).
- **16.2 Tractable and intractable classes** — Schaefer's dichotomy theorem: for constraint language $C$, SAT($C$) is in P if the induced formula class is trivially-true-satisfiable, trivially-false-satisfiable, Horn, dual-Horn, 2-CNF, or affine — otherwise NP-complete; linear-time Horn-SAT via unit propagation to a trivially satisfiable residual; linear-time 2-SAT via the implication graph and strongly connected components (unsatisfiable iff some variable and its negation lie in a common cycle).
- **16.3–16.4 Upper bounds for $k$-SAT and General SAT** — the fastest known deterministic/randomized algorithms for $k$-SAT (building on the case-splitting/autarky ideas summarized in Chapter 1 §1.18) and how these translate into the best current bounds for unrestricted SAT via clause-length reduction.
- **16.5–16.6 Structural questions and summary** — implications of hypothetical faster $k$-SAT algorithms (e.g. on the Exponential Time Hypothesis); a summary table of best current bounds across SAT variants; the Addendum on connections to circuit complexity.

**Key Questions:**
1. What precisely are the six structural properties in Schaefer's dichotomy theorem, and why does the theorem guarantee that *every* constraint language falls into either P or NP-complete with no intermediate cases?
2. Why does 2-SAT reduce to a linear-time graph algorithm (strongly connected components of the implication graph) while 3-SAT does not admit an analogous polynomial method — what breaks when clause length increases from 2 to 3?
3. How does the chapter's DP-style variable elimination transformation $DP_a(F)$ relate to the bucket-elimination/directional-resolution algorithm of Chapter 3, and why is it only applied when it does not increase formula size?

---
### Chapter 17: Fixed-Parameter Tractability (pp. 693–727)

**Summary:** Applies parameterized complexity theory to SAT to explain the gap between the trivial $2^n$ worst-case bound and solvers' actual empirical performance, by identifying "hidden structure" parameters $\pi(F)$ (backdoor sets, tree-likeness/treewidth, and others) under which SAT and even model counting (#SAT) become fixed-parameter tractable. : [[Worst-Case-Complexity-and-Tractability|Link]]

**Key Definitions & Concepts by Section:**
- **17.1 Introduction** — a satisfiability parameter $\pi$ maps a formula $F$ to a non-negative integer (or $\infty$), inducing a hierarchy of classes $C_0^\pi\subseteq C_1^\pi\subseteq\cdots$; the crucial distinction between non-uniform polynomial time ($O(n^k)$, practically infeasible even for small $k$) and uniform polynomial/fixed-parameter time ($O(f(k)n^c)$, practically feasible while $k$ stays small); the historical origin of parameterized complexity in Downey and Fellows's observation that vertex cover (parameterized by solution size) is FPT while independent set (same parameterization) apparently is not. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **17.2 Preliminaries** — a parameterized problem instance $(I,k)$; fixed-parameter tractability ($O(f(k)|I|^c)$ solvability, class FPT); the parameterized vertex cover problem (VC) as the canonical illustrative example; graphs/hypergraphs associated with CNF formulas (e.g. primal, dual, incidence graphs).
- **17.3 Parameterized SAT** — a general framework casting satisfiability parameters as the object of study, plus parameterized optimization problems related to SAT.
- **17.4 Backdoor sets** — parameters based on the size of a smallest backdoor set relative to a polynomial-time-solvable base class (e.g. Horn or 2-CNF), directly connecting to Chapter 11's backdoor concept but now studied as a formal tractability parameter. : [[Runtime-Variation-and-Solver-Engineering|Link1]], [[Worst-Case-Complexity-and-Tractability|Link2]]
- **17.5 Treewidth** — parameters measuring the "tree-likeness" of a formula's associated graph, connecting to the tractable structural methods of Chapter 3 (bucket elimination/directional resolution).
- **17.6 Further parameters** — parameters based on graph matchings and on the community structure of formulas.
- **17.7 Concluding remarks.**

**Key Questions:**
1. Why is a running time of $O(n^k)$ ("non-uniform polynomial") practically useless for even moderate $k$, while $O(2^k n^3)$ ("fixed-parameter tractable") remains practical as long as $k$ stays small — what exactly does moving $k$ out of the exponent's base buy you?
2. Why does SAT, unlike problems such as vertex cover, lack a single "natural" parameter, and what does this imply about the research strategy of proposing and comparing many different satisfiability parameters (backdoor size, treewidth, etc.)?
3. How does formalizing "hidden structure" as a fixed-parameter-tractability question let theorists explain why real-world SAT instances are solvable in practice despite the $2^n$ worst-case bound, without contradicting NP-completeness?

---
### Chapter 18: Bounded Model Checking (pp. 739–757)

**Summary:** Introduces Bounded Model Checking (BMC) — encoding a bounded-length counterexample trace of a symbolic system as a propositional formula and checking it with a SAT solver — as SAT's most important application in hardware verification alongside equivalence checking, covering LTL specification, the bounded semantics, and complete ("unbounded") extensions that let BMC prove properties rather than only falsify them. : [[Bounded-Model-Checking-and-Formal-Verification|Link]]

**Key Definitions & Concepts by Section:**
- **18.1 Model checking** — BDD-based vs. SAT-based symbolic model checking (BMC sacrifices BDD's variable-elimination completeness for scalability, biasing toward falsification); Kripke structure $K=(S,I,T,L)$ (states, initial states, transition relation, labelling function); LTL syntax/semantics over infinite paths $\pi=(s_0,s_1,\dots)$: $X$ (next), $F$ (finally/eventually), $G$ (globally), with safety ($G\lnot(a\wedge b)$) vs. liveness ($G(a\to Fb)$) properties; negation normal form (NNF) via the duality axioms $\lnot Fg\equiv G\lnot g$, $\lnot Gg\equiv F\lnot g$; the model checking problem $K\models f$ reduced to searching for a *witness* path for $\lnot f$; LTL vs. CTL (branching-time) as competing specification formalisms, both PSPACE-complete for symbolic representations. : [[Bounded-Model-Checking-and-Formal-Verification|Link]]
- **18.2 Bounded semantics** — a $(k,l)$-lasso: a bounded path of length $k$ that loops back to state $l$, used to give finite witnesses to infinite-path properties like $Fg$/$Gg$. : [[Bounded-Model-Checking-and-Formal-Verification|Link]]
- **(18.3–18.10, by known structure)** — propositional encodings of the bounded transition relation and property unrolled to depth $k$; completeness (determining a sufficient bound $k$ beyond which no counterexample exists); induction-based and interpolation-based techniques for achieving completeness without unrolling to the full completeness bound; invariant strengthening; related work and applications (test-case generation, redundancy detection).

**Key Questions:**
1. Why did SAT-based BMC have to explicitly abandon completeness (focusing on falsification) in order to be practically competitive with BDD-based model checking, and what specific operation available to BDDs (but not SAT solvers) is responsible?
2. What does a $(k,l)$-lasso structurally represent, and why is looping back to an earlier state within a bounded-length path necessary to give a finite witness for a formula like $Gg$ or $Fg$ that quantifies over an infinite path?
3. How does reducing "does $K\models f$ hold" to "does $\lnot f$ have a witness path" let BMC's falsification-oriented SAT search be used for the (more naturally existential) model checking question at all?

---
### Chapter 19: Planning and SAT (pp. 765–785)

**Summary:** Covers "planning as satisfiability" (Kautz and Selman), one of the earliest and most influential SAT applications: encoding the bounded plan-existence problem — does a plan of length $n$ reaching the goal exist? — as a propositional formula, and the representational and search techniques (parallel plans, bound-selection strategies, temporal and nondeterministic extensions) that make this practical despite classical planning being PSPACE-complete. : [[Planning-as-Satisfiability|Link]]

**Key Definitions & Concepts by Section:**
- **19.1 Introduction** — classical planning as PSPACE-complete, so no polynomial general translation to SAT can exist, but plan length (the practically relevant parameter) tends to stay polynomial, keeping the resulting formulas tractable in size; the three orthogonal efficiency drivers: encoding quality, SAT-solving efficiency, and the strategy for choosing which plan lengths $n$ to test. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **19.2 Classical planning** — an action $\langle p,e\rangle$ with precondition $p$ and conditional effects $f\Rightarrow d$; active effects $[a]_s$ of an action in state $s$; executability requiring the precondition holds and effects are consistent; $\mathrm{exec}_a(s)$ and its extension to sequences/sets of simultaneous actions; the effect precondition $EPC_l(a)$ (the condition under which literal $l$ becomes an active effect of $a$); a plan $\sigma=a_1;\dots;a_n$ satisfying $\mathrm{exec}_\sigma(I)\models G$. : [[Planning-as-Satisfiability|Link]]
- **19.3 Sequential plans** — the time-indexed variable set $X@t$ (one copy of each state variable per time step) encoding the bounded plan-existence formula $\varphi_n$, satisfiable iff a length-$n$ plan exists. : [[Planning-as-Satisfiability|Link]]
- **19.4 Parallel plans** — allowing multiple actions per time point (bounding time points, not action count) to shrink the search relative to purely sequential plans, while preserving polynomial-time interconvertibility with sequential plans. : [[Planning-as-Satisfiability|Link]]
- **19.5 Finding a satisfiable formula** — strategies for iterating/choosing plan-length values $n$ to test. : [[Planning-as-Satisfiability|Link1]], [[Quantified-Boolean-Formulas|Link2]]
- **19.6–19.7 Extensions** — temporal planning (real/rational-valued action durations, overlapping actions) and nondeterministic/sensing planning reduced to SAT or its quantified extensions (QBF).

**Key Questions:**
1. Given that classical planning is PSPACE-complete, why doesn't the SAT encoding of bounded plan existence contradict this — what role does bounding by plan length $n$ play in keeping $\varphi_n$ polynomial-size for practically relevant problem classes?
2. What is the effect precondition $EPC_l(a)$ doing structurally, and how does Lemma 19.2.1 ($l\in[a]_s\iff s\models EPC_l(a)$) let this be compiled directly into a propositional clause over time-indexed variables?
3. Why does allowing multiple actions per time step (parallel plans) — while still requiring polynomial-time interconvertibility with sequential plans — meaningfully shrink the search space compared to a purely sequential encoding?

---
### Chapter 20: Software Verification (pp. 791–815)

**Summary:** Extends SAT-based verification from hardware to software, motivated by the observation that programming languages' basic data types have bit-vector (not unbounded integer) semantics, matching exactly what a SAT solver can accurately and efficiently model; covers extracting formal transition-system models from program source, encoding program expressions propositionally, extending Bounded Model Checking to software, and predicate abstraction as a SAT-based technique for proving control-flow properties. : [[Quantified-Boolean-Formulas|Link]]

**Key Definitions & Concepts by Section:**
- **20.1 Programs use bit-vectors** — bit-vector semantics (bounded range $0,\dots,2^n-1$, arithmetic wraps modulo $2^n$); many program analyzers are unsound because they model bit-wise operators (efficient in hardware, ubiquitous in performance-critical code) using unbounded/non-linear integer arithmetic instead; propositional SAT as an accurate decision engine because bit-vectors map directly to Boolean variables and bit-vector operators to Boolean functions.
- **20.2 Formal models of software** — a transition system $(S,S_0,R)$; a program state $s\in S$ = program location $\times$ variable valuation $\times$ call stack ($S=L\times(V\to D)\times(\mathbb{N}\to(D\cup L))$, allowing recursion via an unbounded stack); the entry location $\ell_0$; the transition relation $R$ partitioned per-location as $R(s,s')\iff\bigwedge_{l\in L}(s.\ell=l\to R_l(s,s'))$; translating sequential source code (e.g. ANSI-C) directly into this transition-system form, including auxiliary variables to eliminate expression side-effects. : [[Bounded-Model-Checking-and-Formal-Verification|Link1]], [[Runtime-Variation-and-Solver-Engineering|Link2]], [[Stochastic-Boolean-Satisfiability|Link3]]
- **20.3 Turning bit-vector arithmetic into CNF** — encoding program expressions (bit-vector arithmetic, bit-wise operators) as propositional formulas.
- **20.4 Bounded Model Checking for software** — extending Chapter 18's hardware BMC to software, unrolling the transition system to a bounded depth, typically limited to refutation (finding bugs) rather than proving correctness. : [[Bounded-Model-Checking-and-Formal-Verification|Link]]
- **20.5 Predicate abstraction using SAT** — a SAT-based technique geared toward *proving* control-flow-dominated properties, complementing BMC's refutation focus. : [[Bounded-Model-Checking-and-Formal-Verification|Link]]

**Key Questions:**
1. Why does the chapter argue that reasoning about program variables as unbounded integers is often *unsound*, given that this is the traditional mathematical model used in program analysis — what specifically goes wrong with bit-wise operators under that model?
2. How does partitioning the transition relation $R$ into per-location relations $R_l$ via a case-split on the program counter directly mirror the control-flow structure of the source program?
3. Why is Bounded Model Checking for software, like its hardware counterpart, naturally suited to refutation (finding bugs) rather than proving correctness, and what role does predicate abstraction play in addressing that gap?

---
### Chapter 21: Combinatorial Designs by SAT Solvers (pp. 819–853)

**Summary:** Surveys how general-purpose SAT solvers (and related "model generators") have been used since the early 1990s to solve open problems in combinatorial design theory — quasigroups/Latin squares, Ramsey and van der Waerden numbers, covering/orthogonal arrays, Steiner systems, Mendelsohn designs, and magic squares — often outperforming special-purpose search programs. : [[Combinatorial-Applications-of-SAT|Link]]

**Key Definitions & Concepts by Section:**
- **21.1 Introduction** — the historical narrative: Zhang's FALCON (1991), Fujita's MGTP, Slaney's FINDER, and the rise of dedicated SAT solvers (Stickel's DDPP/LDPP, Zhang's SATO, McCune's MACE) all solving previously-open quasigroup problems in the early-to-mid 1990s, establishing SAT/model-generation as competitive with (or superior to) special-purpose design-theory search software; a Mace-style model generator's three components: encoder (problem $\to$ propositional formula, model-preserving), SAT solver, decoder (interpreting the solver's output back into the original problem's terms); the tradeoff of uniform representation (redundancy/inefficiency risk) vs. accumulated decades of generic-solver-engine improvements. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **21.2 Combinatorial design problems (catalogue)** — quasigroups and Latin squares (an $|S|\times|S|$ matrix where every row/column is a permutation of $S$, algebraically a cancellative groupoid/quasigroup $(S,*)$, the multiplication table of a binary operator); Ramsey numbers; van der Waerden numbers; covering arrays; orthogonal arrays; covering array numbers of small strength; Steiner systems; Mendelsohn designs; magic squares. : [[Combinatorial-Applications-of-SAT|Link]]
- **21.3 Encoding design theory problems** — techniques for building effective, efficient SAT encoders for these highly symmetric, combinatorially structured problems. : [[Combinatorial-Applications-of-SAT|Link]]
- **21.4 Conclusions and open problems.**

**Key Questions:**
1. Why did the quasigroup-problem successes of the early 1990s (FALCON, MGTP, FINDER, then SAT solvers) mark a turning point in convincing researchers that general-purpose search could outperform special-purpose design-theory software, given the seemingly generic and redundant nature of a uniform clausal representation?
2. What is the algebraic relationship between a Latin square and a quasigroup, and why does this relationship make quasigroup existence/property questions naturally expressible as finite-model-finding problems amenable to a SAT encoder/solver/decoder pipeline?
3. Given that design-theory problems are typically saturated with symmetry (e.g. relabeling the underlying set $S$), what encoding considerations does the chapter suggest are needed to keep SAT-based approaches to these problems tractable in practice?

---
### Chapter 22: Connections to Statistical Physics (pp. 859–895)

**Summary:** Introduces the statistical-physics viewpoint on random constraint satisfaction (especially random $k$-SAT and the syntactically similar but simpler $k$-XORSAT) to computer scientists — phase transitions, the refined "clustering" picture of the satisfiable phase, and how this physical picture inspired the Survey Propagation message-passing algorithm. : [[Statistical-Physics-of-Random-Constraint-Satisfaction|Link]]

**Key Definitions & Concepts by Section:**
- **22.1 Introduction** — the historical link between spin-glass statistical physics (Parisi et al., early 1980s) and combinatorial optimization; the key methodological difference between physicists (statistical statements about instance distributions) and computer scientists (efficient algorithms for arbitrary instances); random $k$-SAT's empirically observed critical density and the associated algorithmic hardness peak as the trigger for renewed physics/CS cross-fertilization; $k$-XORSAT (random linear systems over $\mathbb{F}_2$) as a technically simpler cousin of $k$-SAT with related but distinct computational properties, and ties to error-correcting codes. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **22.2 Phase transitions: basic concepts** — illustrated via the continuous perceptron problem: given $M$ random points in $\mathbb{R}^N$, does a vector $\sigma$ exist with positive dot product with all of them; the probability $P(N,M)$ of a solution existing has an exact closed form (Cover's formula) and exhibits a sharp threshold at critical ratio $\alpha_s=M/N=2$ as $N\to\infty$, with a computable scaling-window description near the transition — the prototypical clean example of a satisfiability-type phase transition. : [[Stochastic-Local-Search-for-SAT|Link]]
- **22.3 Phase transitions in random CSPs** — the fuller phase-transition scenario for random $k$-SAT, including finer structure beyond the sat/unsat threshold (e.g. clustering/condensation of the solution space) as revealed by physics techniques (the "cavity method" / replica-symmetry-breaking analysis). : [[Random-Satisfiability-and-Phase-Transitions|Link]]
- **22.4–22.5 Algorithmic techniques** — analysis of local search and backtracking algorithms via physics methods, and message-passing algorithms — in particular Survey Propagation, an extension of Belief Propagation (from communication theory / statistical inference) designed around the clustered solution-space picture, which proved effective near the satisfiability threshold where standard local search struggles.
- **22.6 Conclusion.**

**Key Questions:**
1. In the continuous perceptron example, what does it mean that the transition probability $P(N,M)$ has an exact closed form with a sharp threshold at $\alpha_s=2$, and how does this clean, fully solved example foreshadow the (much harder, only partly rigorous) picture physicists later proposed for random $k$-SAT?
2. Why is $k$-XORSAT studied alongside $k$-SAT despite being a "different" problem (linear equations over $\mathbb{F}_2$ rather than clausal constraints) — what does its technical simplicity let physicists establish that remains only conjectural for $k$-SAT?
3. How does the clustering/condensation picture of the random-$k$-SAT solution space (beyond the simple sat/unsat threshold) motivate Survey Propagation as an algorithm, and why would standard local search or belief propagation struggle precisely in the regime where the solution space becomes clustered?

---
### Chapter 23: MaxSAT, Hard and Soft Constraints (pp. 903–920)

**Summary:** Introduces MaxSAT (finding an assignment maximizing satisfied clauses) and its weighted/partial variants as the natural way to handle over-constrained problems where plain SAT gives no useful output on unsatisfiable instances, focusing on branch-and-bound exact algorithms, complete logical calculi, and approximation methods (SAT-based exact algorithms are covered in a separate chapter).

**Key Definitions & Concepts by Section:**
- **23.2 Preliminaries** — CNF formulas as *multisets* of clauses (duplicates matter for MaxSAT, unlike plain SAT); a weighted clause $(C_i,w_i)$; MaxSAT $\equiv$ MinUNSAT (maximizing satisfied clauses = minimizing unsatisfied ones) for exact computation; Max-$k$SAT (clause length $\le k$); MaxSAT-instance equivalence (same unsatisfied-clause count under every complete assignment); the three key extensions — Weighted MaxSAT (maximize sum of weights of satisfied clauses), Partial MaxSAT (hard clauses must all be satisfied, soft clauses maximized), and Weighted Partial MaxSAT (combination); the ILP formulation of weighted MaxSAT using indicator variables $y_i$ (variable truth values) and $z_j$ (clause satisfaction), with constraint $\sum_{i\in I_j^+}y_i+\sum_{i\in I_j^-}(1-y_i)\ge z_j$, used to derive lower/upper bounds.
- **23.3 Branch and bound algorithms** — the core B&B scheme for exact MaxSAT solving, improved via strong lower bounds, variable-selection heuristics, and specialized data structures adapted from SAT solving (lazy structures, unsatisfiable-core extraction, non-chronological backtracking, clause learning). : [[Maximum-Satisfiability|Link]]
- **23.4 Complete inference in MaxSAT** — logical calculi for MaxSAT based on resolution and tableaux, generalizing SAT's proof systems to the optimization setting. : [[Maximum-Satisfiability|Link]]
- **23.5 Approximation algorithms** — algorithms giving quality-guaranteed (but not necessarily fast) near-optimal solutions, contrasted with fast-but-unguaranteed heuristics.
- **23.6–23.8** — the annual MaxSAT Evaluation (since 2006) driving solver development; other contributions; MinSAT as MaxSAT's dual problem (minimizing satisfied, rather than maximizing, clauses).

**Key Questions:**
1. Why must MaxSAT formulas be treated as *multisets* rather than sets of clauses, and what would go wrong (in terms of the optimization objective) if duplicate clauses were collapsed as they are in plain SAT?
2. In the ILP formulation, why does the constraint $\sum_{i\in I_j^+}y_i+\sum_{i\in I_j^-}(1-y_i)\ge z_j$ correctly force $z_j=0$ whenever clause $C_j$ is unsatisfied, while still allowing $z_j=0$ even when $C_j$ happens to be satisfied (making it valid for computing bounds via relaxation)?
3. Why does Partial MaxSAT (hard clauses must all hold; soft clauses maximized) generalize both plain SAT (all clauses hard) and plain MaxSAT (all clauses soft), and what practical over-constrained-problem scenarios does this generalization capture that plain MaxSAT cannot?

---
### Chapter 24: Maximum Satisfiability (pp. 929–972)

**Summary:** A modern complement to Chapter 23 focused on the SAT-solver-call-based algorithmic approaches (model-improving, core-guided, and implicit hitting set) that made MaxSAT solving practical for large real-world optimization problems, plus applications, encodings, and further developments (preprocessing, parallel and incomplete solving). : [[Maximum-Satisfiability|Link]]

**Key Definitions & Concepts by Section:**
- **24.2 The MaxSAT formalism** — a MaxSAT formula $F=\mathrm{hard}(F)\cup\mathrm{soft}(F)$: hard clauses must be satisfied, each soft clause $c$ carries a positive weight $wt(c)$ (cost of falsifying it); truth assignment $\pi$, restriction $\pi|_A$; the objective is to minimize total falsified-soft-clause weight (equivalently maximize satisfied-soft-clause weight) subject to satisfying all hard clauses.
- **24.3 Encodings and applications** — techniques for encoding NP-hard optimization problems (combinatorics, planning/scheduling, verification, security, data analysis/ML, bioinformatics) into MaxSAT, often outperforming integer programming on these instances. : [[Combinatorial-Applications-of-SAT|Link]]
- **24.4 Modern MaxSAT algorithms** — the model-improving approach (repeatedly querying a SAT solver for a strictly lower-cost solution, using cardinality constraints to force improvement); the core-guided approach (iteratively extracting an unsatisfiable core — a subset of soft clauses of which some must be falsified — via assumption-based SAT solving, then adding a cardinality constraint permitting exactly one falsified clause per discovered core, until the formula becomes satisfiable; soundness follows because every solution must falsify at least one clause per core); the implicit hitting set approach (computing a minimum-cost hitting set over accumulated cores as a lower bound, then asking SAT to satisfy everything outside that hitting set — optimal when it succeeds, otherwise yielding a new core), which avoids cardinality constraints for faster SAT calls. : [[Maximum-Satisfiability|Link]]
- **24.5 Further developments** — preprocessing, parallel solving, algorithm portfolios, partitioning-based solving, incomplete (fast but non-optimal) solving.
- **24.6 Summary.**

**Key Questions:**
1. In the core-guided approach, why does allowing exactly "one, but no more than one" falsified soft clause per discovered unsatisfiable core guarantee that once the formula becomes satisfiable, the returned solution is provably *optimal* (not merely feasible)?
2. What is the essential algorithmic difference between the core-guided approach (using cardinality constraints on cores) and the implicit hitting set approach (computing a minimum-cost hitting set over cores), and why does the latter's avoidance of cardinality constraints make its SAT calls faster in practice?
3. Why does the chapter report that MaxSAT is often more effective than integer programming for problems with natural propositional encodings — what does this suggest about the fit between a solving paradigm's underlying representation and a problem's native structure?

---
### Chapter 25: Model Counting (pp. 993–1011)

**Summary:** Covers propositional model counting (#SAT) — computing the number of satisfying assignments of a formula — its #P-complete worst-case complexity (surprisingly hard even for some polynomial-time-solvable SAT restrictions), and the exact and approximate practical counting techniques built by extending DPLL and local search. : [[Model-Counting|Link]]

**Key Definitions & Concepts by Section:**
- **Introduction** — #SAT as the canonical #P-complete problem, generalizing SAT and relevant to Bayesian-network/probabilistic reasoning and combinatorial-design solution-counting; the scalability gap between SAT solvers (hundreds of thousands of variables) and model counters (hundreds exactly, ~1000 approximately); the tension that #SAT algorithms must remain aware of *all* solutions, undermining SAT heuristics designed to prune toward a single solution quickly.
- **25.1 Computational complexity** — the complexity class #P (counting problems for polynomial-time-decidable, polynomially-balanced relations $Q$); #P-completeness via polynomial-time *counting reductions* (a pair of functions $R,S$ translating instances and recovering counts) as opposed to standard decision reductions; parsimonious reductions (solution-count-preserving) giving an easy route to #P-completeness, e.g. a parsimonious Cook-Levin construction showing #SAT is #P-complete; Valiant's theorem that counting variants of polynomial-time-solvable problems (2-SAT, Horn-SAT, DNF-SAT, bipartite matching) can still be #P-complete, illustrated by PERM/#BIP-MATCHING (computing the permanent, #P-complete) versus finding *one* perfect matching (polynomial via network flow); Toda's theorem placing #P above the polynomial hierarchy, meaning #SAT is at least as hard as constant-quantifier-depth QBF. : [[Proof-Complexity|Link]]
- **25.2 Exact model counting** — DPLL-style exhaustive-search extensions (systematically enumerating/counting rather than stopping at the first solution) vs. knowledge-compilation approaches (converting the formula into a tractable normal form, e.g. d-DNNF, from which counting is cheap). : [[Model-Counting|Link]]
- **25.3 Approximate model counting** — fast heuristic estimators with no guarantees vs. methods giving statistically/probabilistically guaranteed lower/upper bounds. : [[Model-Counting|Link]]
- **25.4 Conclusion.**

**Key Questions:**
1. Why is it "surprising" that the solution-counting variant of a polynomial-time-solvable decision problem like 2-SAT or bipartite matching (Valiant's PERM/#BIP-MATCHING result) can be #P-complete — what does this reveal about the relationship between "finding a solution" and "counting all solutions" as computational tasks?
2. What is the structural difference between a standard (decision) polynomial-time reduction and a *counting* reduction (the pair $R,S$), and why does the existence of parsimonious reductions make proving #P-completeness comparatively easy?
3. Why does the requirement that a #SAT algorithm "be aware of all solutions in the search space" undermine the effectiveness of standard SAT branching heuristics (which are designed to prune quickly toward a single satisfying assignment)?

---
### Chapter 26: Approximate Model Counting (pp. 1015–1039)

**Summary:** A new-to-the-2nd-edition chapter surveying the practical and theoretical breakthroughs (roughly 2006–2019) that made approximate #SAT counting scale to formulas with hundreds of thousands of variables while still giving strong $(1+\varepsilon)$-factor, $(1-\delta)$-confidence guarantees, centered on universal-hash-function ("random parity constraint") techniques built on top of CNF SAT solvers. : [[Model-Counting|Link]]

**Key Definitions & Concepts by Section:**
- **26.1.1 Historical perspective** — early theoretical results (Stockmeyer 1983: approximate counting via universal hash functions and polynomially many NP-oracle calls, elegant but impractical; Jerrum-Valiant-Vazirani 1986: inter-reducibility of approximate counting and almost-uniform sampling); the 2006 breakthrough by Gomes, Sabharwal, and Selman using random *parity* (XOR) constraints as universal hash functions layered on a CNF SAT solver backend, later refined (2013) into parameter-free $(1+\varepsilon,1-\delta)$-guaranteed algorithms, aided by solvers like CryptoMiniSat that natively handle parity constraints; the separate, earlier-successful trajectory of DNF approximate counting via Karp–Luby (1983) Monte Carlo sampling, later matched (not surpassed) by hashing-based approaches.
- **26.1.2 Complexity landscape** — #P as the class of counting problems for NP decision problems; Toda's theorem $PH\subseteq P^{\#P}$ (a single #P-oracle call solves any polynomial-hierarchy problem efficiently), implying #SAT is computationally at least as hard as the entire polynomial hierarchy. : [[Model-Counting|Link1]], [[Proof-Complexity|Link2]]
- **(26.2–26.6, by known structure)** — approximate model counting for CNF via universal hashing (partitioning the solution space into roughly equal "cells" using random XOR constraints, then counting within one cell and scaling); handling CNF+XOR constraints; approximate counting for DNF; weighted counting extensions; conclusion.

**Key Questions:**
1. Why did Stockmeyer's 1983 universal-hashing approach to approximate counting remain "theoretically elegant but impractical," and what specifically changed by 2006 (Gomes–Sabharwal–Selman) and 2013 to make hashing-based approximate counting practically scalable?
2. Why did DNF approximate counting (Karp–Luby, 1983) succeed early using Monte Carlo sampling while the analogous problem for CNF formulas resisted a comparable approach for decades — what property of DNF does Karp–Luby's method exploit that CNF lacks?
3. What does Toda's theorem ($PH\subseteq P^{\#P}$) imply about the inherent difficulty of #SAT relative to problems like QBF validity, and how does this motivate accepting *approximate* rather than exact counts for large-scale applications?

---
### Chapter 27: Non-Clausal SAT and ATPG (pp. 1047–1080)

**Summary:** Surveys satisfiability checking directly on non-clausal (structural, circuit-level) representations rather than CNF — motivated by CNF translation's potential exponential blowup and loss of structural information — covering tableau/Stålmarck/BDD/local-search extensions to non-clausal SAT, Boolean-circuit-based DPLL-style techniques, and the closely related field of Automatic Test Pattern Generation (ATPG) for digital circuits. : [[Non-Clausal-and-Circuit-Based-Satisfiability|Link]]

**Key Definitions & Concepts by Section:**
- **27.1 Introduction** — CNF-to-general-formula tradeoff: CNF is easy to build efficient data structures/algorithms for but cumbersome to model in directly, and while general-to-CNF translation is polynomial-time (via auxiliary variables, cf. Chapter 2's Tseitin encoding), it can still exponentially affect solver performance and discards structural information; prior non-clausal approaches: tableau calculi (weak in classical propositional logic, unable to polynomially simulate even truth tables without extensions like the KE system's explicit cut rule), Stålmarck's proof procedure (commercialized as Prover), BDD-based manipulation (better suited to equivalence checking than satisfiability), and local search extended to non-clausal formulas; circuit representations preserve structure, enable sub-expression sharing, support efficient Boolean propagation, and expose *observability don't-cares* useful for pruning. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **27.2 Basic definitions** — a Boolean circuit $C=(G,E)$: gates $G$, acyclic equations $g:=f(g_1,\dots,g_n)$; primary input/output gates; fan-in/fan-out; descendant/ancestor via transitive closure; standard gate functions (`false`, `true`, `not`, `and`, `or`, `ite`, `odd`/parity/xor, `equiv`); worked full-adder circuit example. : [[Stochastic-Boolean-Satisfiability|Link]]
- **27.3 Satisfiability checking for Boolean circuits** — generalizing DPLL-style clausal techniques (unit propagation, decision, conflict analysis) to operate directly on circuit structure, exploiting observability don't-cares and structural sharing. : [[Random-Satisfiability-and-Phase-Transitions|Link]]
- **27.4 Automatic Test Pattern Generation** — classical ATPG algorithms, formulating ATPG as a SAT problem, and advanced SAT-based ATPG techniques. : [[Non-Clausal-and-Circuit-Based-Satisfiability|Link]]
- **27.5 Conclusions.**

**Key Questions:**
1. Why can converting a general propositional formula to CNF be safe in the worst case (polynomial-time, satisfiability-preserving) yet still hurt practical solver performance — what specifically is lost when auxiliary Tseitin-style variables replace the original circuit structure?
2. What is an "observability don't-care," and why can only a circuit-level (not clausal) representation expose it for use in pruning the satisfiability search?
3. Why have tableau-based approaches to classical propositional satisfiability historically been much less successful than DPLL-based clausal techniques, given that tableaux work directly on the non-clausal formula DPLL must first flatten away?

---
### Chapter 28: Pseudo-Boolean and Cardinality Constraints (pp. 1087–1125)

**Summary:** Covers pseudo-Boolean (PB) constraints — linear/nonlinear integer-coefficient generalizations of clauses rooted in 1960s Operations Research — as a more expressive middle ground between CNF and full 0-1 integer programming, including their decision/optimization problems, inference rules, adaptation of SAT algorithms to PB, and translation of PB back into SAT. : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]

**Key Definitions & Concepts by Section:**
- **28.1 Introduction** — a pseudo-Boolean function maps $n$ Boolean values to a real (here, restricted to integer-coefficient) number; PB constraints are more expressive than clauses yet close enough to SAT to reuse SAT-solving advances, while also benefiting from decades of 0-1/Integer-Linear-Programming experience; some problems are solvable in polynomial time via PB inference rules despite requiring exponentially many resolution steps when encoded as clauses. : [[Complete-Search-Algorithms-for-SAT|Link]]
- **28.2 Basic definitions** — a literal $l_j$ with integer coefficient $a_j$; a linear pseudo-Boolean (LPB) constraint $\sum_ja_jl_j\rhd b$ ($\rhd\in\{=,>,\ge,<,\le\}$), with $b$ called the constraint's degree; non-linear PB constraints $\sum_ja_j(\prod_kl_{j,k})\rhd b$ (products of literals as logical AND); cardinality constraints atleast($k$,·), atmost($k$,·), exactly($k$,·) as PB special cases, with the identity $\mathrm{atmost}(k,S)\equiv\mathrm{atleast}(|S|-k,S)$. : [[Stochastic-Boolean-Satisfiability|Link]]
- **(28.3–28.7, by known structure)** — the decision problem (PB-SAT) versus the optimization problem (minimize/maximize an objective subject to PB constraints); expressive power of cardinality/PB constraints relative to CNF; inference rules generalizing resolution (e.g. cutting-planes-style addition/division/saturation of PB constraints) that can be exponentially stronger than resolution on the clausal encoding; current algorithms adapting CDCL-style search (conflict-driven learning of PB constraints, watched-literal-like propagation) to PB; encodings translating PB constraints down into CNF when a native PB solver is unavailable.

**Key Questions:**
1. Why can a problem that requires exponentially many resolution steps to solve when encoded as CNF sometimes be solved in polynomially many steps using PB inference rules — what extra reasoning power do PB constraints (via their arithmetic structure) provide that clausal resolution lacks?
2. How does the identity $\mathrm{atmost}(k,S)\equiv\mathrm{atleast}(|S|-k,S)$ illustrate the redundancy among the three cardinality-constraint forms, and why does the chapter still define all three rather than picking one canonical form?
3. What is the fundamental tradeoff PB constraints strike between clausal SAT and full 0-1 Integer Linear Programming, and why does the chapter frame this as "a nice compromise between expressive power and difficulty to solve"?

---
### Chapter 29: Theory of Quantified Boolean Formulas (pp. 1131–1154)

**Summary:** Lays out the syntax, semantics, complexity, expressive power, and proof theory (Q-resolution) of quantified Boolean formulas (QBF) — the natural extension of propositional logic with $\exists$/$\forall$ quantifiers that captures satisfiability as $\exists x_1\dots\exists x_n\varphi$ and logical equivalence as $\forall x_1\dots\forall x_n(\alpha\leftrightarrow\beta)$. : [[Quantified-Boolean-Formulas|Link]]

**Key Definitions & Concepts by Section:**
- **29.2 Syntax and semantics** — inductive definition of QBF$^*$ (propositional formulas/constants as base case, closed under $\exists x\Phi$, $\forall x\Phi$, $\neg$, $\vee$, $\wedge$); quantified vs. bound vs. free occurrences of a variable; the scope of a quantified variable; a formula is closed iff it has no free variables; recursive evaluation $\mathcal{I}$: $\mathcal{I}(\exists y\Phi)=1\iff\mathcal{I}(\Phi[y/0])=1$ or $\mathcal{I}(\Phi[y/1])=1$; $\mathcal{I}(\forall x\Phi)=1\iff\mathcal{I}(\Phi[x/0])=\mathcal{I}(\Phi[x/1])=1$; satisfiability/truth/falsity/unsatisfiability for QBF; logical consequence $\Phi_1\models\Phi_2$ and logical equivalence $\Phi_1\approx\Phi_2$ vs. the weaker satisfiability-equivalence $\approx_{sat}$ (coincide for closed formulas); satisfiability of an open formula reduced to truth of its existential closure. : [[Quantified-Boolean-Formulas|Link]]
- **(29.3–29.6, by known structure)** — complexity results for QBF satisfiability/equivalence and tractable subclasses; expressive power via a functional (Skolem/Herbrand-function) view of formula valuation; Q-resolution as an extension of propositional resolution to quantified formulas, respecting quantifier dependencies; quantified Horn formulas and the Q2-CNF class as tractable special cases.

**Key Questions:**
1. Why does the recursive evaluation rule for $\forall x\Phi$ require checking *both* substitutions $\Phi[x/0]$ and $\Phi[x/1]$ while $\exists x\Phi$ only requires *one* to hold, and how does this asymmetry drive QBF's higher (PSPACE-complete, vs. SAT's NP-complete) worst-case complexity?
2. Why do logical equivalence and satisfiability-equivalence coincide for closed QBFs but not necessarily for formulas with free variables, and what does the distinction reveal about how free variables interact with quantifier semantics?
3. How does Q-resolution have to depart from ordinary propositional resolution to correctly respect the *order* of quantifier dependencies, rather than treating all variables as freely resolvable?

---
### Chapter 30: Reasoning with Quantified Boolean Formulas (pp. 1157–1172)

**Summary:** A practically-oriented companion to Chapter 29, reviewing applications of QBF reasoning (planning, knowledge representation, formal methods) and the two main algorithmic paradigms — search-based and variable-elimination-based — underlying solvers for prenex CNF QBFs. : [[Quantified-Boolean-Formulas|Link]]

**Key Definitions & Concepts by Section:**
- **30.2 Quantified Boolean logic** — an alternative but equivalent QBF syntax built from variables, $n$-ary $\wedge/\vee$, $\neg$, and $\forall z\varphi$/$\exists z\varphi$; scope, free/bound occurrence, closed formula; a valuation $I$ extended recursively, notably $I(\exists x\psi)=$True iff $I(\psi_x)=$True or $I(\psi_{\neg x})=$True (substitution notation $\varphi_z$/$\varphi_{\neg z}$ for substituting True/False for free occurrences of $z$); logical equivalence vs. equisatisfiability, which coincide for closed QBFs (paralleling Chapter 29's $\approx$ vs. $\approx_{sat}$ distinction). : [[Quantified-Boolean-Formulas|Link]]
- **30.3 Applications** — QBF as the prototypical PSPACE-complete problem, making it a natural target language for reducing many PSPACE problems: conformant/conditional planning, knowledge representation tasks (autoepistemic logic, default logic, disjunctive logic programming, circumscription, modal logic K, abduction, belief revision, paraconsistent reasoning, answer-set-program equivalence), and formal methods (equivalence checking of partial implementations, protocol verification, vertex eccentricity, model checking, pipeline processor verification, FPGA logic synthesis). : [[Combinatorial-Applications-of-SAT|Link]]
- **30.4 QBF solvers** — the two dominant algorithmic families for prenex CNF QBF solving: search-based approaches (extending DPLL/CDCL-style backtracking to respect quantifier ordering) and variable-elimination approaches (analogous to Chapter 3's DP algorithm, eliminating variables in quantifier-respecting order).
- **30.5 Other approaches, extensions, and conclusions** — techniques for non-prenex, non-CNF QBFs.

**Key Questions:**
1. Why does QBF's status as the prototypical PSPACE-complete problem make it such a natural and widely-used target for encoding diverse reasoning tasks (planning, knowledge representation, formal verification) that are not obviously about quantified logic at all?
2. What must a search-based QBF solver do differently from a plain SAT/CDCL solver to respect the *order* in which existential and universal variables are quantified, rather than branching on variables in an arbitrary order?
3. Why do logical equivalence and equisatisfiability coincide for *closed* QBFs but require the more careful "equivalent" definition (via $(\neg\varphi_1\vee\varphi_2)\wedge(\varphi_1\vee\neg\varphi_2)$ holding under every valuation) for QBFs with free variables?

---
### Chapter 31: Quantified Boolean Formulas (pp. 1177–1215)

**Summary:** A new-to-the-2nd-edition survey of the proof-theoretic foundations of modern QBF solving, connecting the two dominant solving paradigms — search-based QCDCL (built on Q-resolution) and expansion-based solving (built on the $\forall$Exp+Res proof system) — to formal proof systems, and covering proof-based certification, strategy extraction, and preprocessing-aware proof systems like QRAT. : [[Quantified-Boolean-Formulas|Link]]

**Key Definitions & Concepts by Section:**
- **31.2 Preliminaries** — closed prenex conjunctive normal form (PCNF): a QBF $\Pi\psi$ with matrix $\psi$ and prefix $\Pi=Q_1X_1\dots Q_kX_k$ of alternating quantifier blocks; level $lv(x)=i$ for $x\in X_i$; the variable order $\le_\Pi$ induced by quantifier level; the game-theoretic semantics (existential/universal players alternately assign their block's variables; existential wins iff the matrix evaluates true); a strategy for a variable as a Boolean function over same-or-outer-scope opposite-type variables; Skolem functions (existential player's winning strategy) vs. Herbrand functions (universal player's); exactly one player always has a winning strategy; a proof system as a poly-time-computable surjection onto the target language (TQBF for QBF proof systems); one proof system (p‑)simulating another via a polynomial(-time-computable) size-preserving translation.
- **31.3 Q-resolution** — lifting propositional resolution to QBF, respecting quantifier order/level, as the formal underpinning of QCDCL (the QBF analogue of CDCL). : [[Quantified-Boolean-Formulas|Link]]
- **31.4 Expansion-based proof systems** — $\forall$Exp+Res: instead of resolving on quantifier structure directly, expands universal variables via ground instantiation before applying propositional resolution; empirically orthogonal in strength to Q-resolution-based solving. : [[Quantified-Boolean-Formulas|Link]]
- **31.5 Preprocessing** — QRAT, a QBF generalization of the RAT (resolution asymmetric tautology) proof system underlying modern SAT certificates (Chapter 15), needed to certify results when preprocessing has been applied. : [[Preprocessing-and-Inprocessing|Link]]
- **31.6 Strategy extraction** — deriving Skolem/Herbrand functions from a solver's proof, usable directly as e.g. a synthesized implementation or a plan.
- **31.7 Connections between proof systems** — simulation/separation results comparing Q-resolution variants and $\forall$Exp+Res, requiring QBF-specific (not just propositional) separation techniques such as strategy-extraction-based arguments. : [[Proof-Complexity|Link]]

**Key Questions:**
1. Why does the game-theoretic semantics of a QBF (alternating existential/universal players assigning their quantifier block in order) guarantee that *exactly one* player always has a winning strategy, and how does this relate back to the formula being simply true or false?
2. Why are Q-resolution-based (search/QCDCL) and $\forall$Exp+Res-based (expansion) solvers empirically "orthogonal" in which instances they solve efficiently, and what does the existence of separation results between these proof systems formally explain about this orthogonality?
3. Why do purely propositional techniques for comparing proof system strength turn out to be insufficient for QBF, requiring new tools like strategy-extraction-based separation arguments — what is fundamentally different about reasoning over quantifier structure?

---
### Chapter 32: SAT Techniques for Modal and Description Logics (pp. 1223–1261)

**Summary:** Surveys how efficient propositional (SAT/DPLL) reasoning techniques have been imported into satisfiability procedures for modal logics (chiefly $K_m$) and the notationally-equivalent description logic $\mathcal{ALC}$ (Schild's correspondence merged the two research communities), covering tableau-based, DPLL-based, CSP-based, translational, inverse-method, automata-theoretic/OBDD-based, and "eager" SAT-encoding approaches. : [[SAT-Techniques-for-Richer-Logics|Link]]

**Key Definitions & Concepts by Section:**
- **32.1 Introduction** — modal operators $\Box,\Diamond,\Box_i$ representing necessity/possibility/agent knowledge; description logic concepts (unary relations) and roles (binary relations), e.g. "male $\wedge\exists$Children(¬male∧teen)"; Schild's theorem that core modal logic $K_m$ and core description logic $\mathcal{ALC}$ are notational variants, unifying the two research traditions; the taxonomy of solving approaches: classic tableau-based (recursively expanding propositional-tableau branches into a candidate Kripke model), DPLL-based (DPLL treats modal subformulas as opaque propositions, then recursively checks modal consistency of the resulting assignment — tools Ksat, *SAT, Fact, Dlp, Racer), CSP-based (KCSP), translational (encoding into first-order logic, tool MSpass), inverse-method (inverted sequent calculus, tool KK), automata-theoretic/OBDD-based (implicit tree-automaton emptiness check, tool KBDD; also an encoding of $K$-satisfiability into QBF), and eager (encoding $K_m$/$\mathcal{ALC}$ formulas directly into SAT for a state-of-the-art SAT solver, tool $K_m$2SAT). : [[Complete-Search-Algorithms-for-SAT|Link]]
- **32.2 Background** — the modal logic $K_m$: language $\Lambda_m$ over primitive propositions $A$ and modal operators $\{\Box_1,\dots,\Box_m\}$, closed under $\{\neg,\wedge\}$ and the modal operators; standard abbreviations ($\Diamond_r\varphi_1:=\neg\Box_r\neg\varphi_1$, etc.).
- **32.3–32.4 Basic and optimized DPLL-based techniques** — the core theoretical framework treating modal subformulas as DPLL-level propositions and recursively verifying modal consistency; optimizations (e.g. caching, early pruning of the modal-consistency checks).
- **32.5 The OBDD-based approach** — symbolic tree-automaton representation and emptiness checking.
- **32.6 The eager DPLL-based approach** — direct SAT encodings of modal/description-logic satisfiability.

**Key Questions:**
1. What did Schild's discovery that $K_m$ and $\mathcal{ALC}$ are notational variants of each other make possible for the previously separate modal-logic and description-logic research communities, and why does the chapter treat results about one as transferable to the other?
2. In the DPLL-based approach, what does it mean to "treat modal subformulas as propositions" at the Boolean engine level, and why is a *recursive* modal-consistency check of the resulting assignment still necessary afterward?
3. Why does the chapter distinguish an "eager" approach (encoding directly into SAT once) from the DPLL-based approach (interleaving a DPLL engine with recursive modal-consistency checks), and what tradeoff between encoding complexity and solver reuse does this distinction reflect?

---
### Chapter 33: Satisfiability Modulo Theories (pp. 1267–1316)

**Summary:** Introduces SMT — deciding satisfiability of quantifier-free first-order formulas *with respect to a fixed background theory* (e.g. linear arithmetic, arrays, bit-vectors) rather than general first-order validity — and its two dominant implementation paradigms, the eager approach (translate directly to an equisatisfiable SAT formula) and the lazy approach (a SAT solver orchestrating a theory-specific decision procedure), plus theory-combination methods. : [[SAT-Techniques-for-Richer-Logics|Link]]

**Key Definitions & Concepts by Section:**
- **33.1 Introduction** — general first-order theorem provers are typically unusable directly because applications care about satisfiability *relative to a background theory* $T$ (fixing the interpretation of symbols like $<,+,0$), not arbitrary nonstandard models; explicitly axiomatizing $T$ is often impossible (undecidable/non-finitely-axiomatizable theories) or too slow; specialized decision procedures exist for many practically important theories (linear real/integer arithmetic, arrays, strings, sets, trees, bit-vectors); SMT's historical roots (Nelson-Oppen, Shostak, Boyer-Moore, late 1970s–80s) and its modern revival (SAT-based decision procedures from the late 1990s onward, widely integrated into interactive theorem provers, extended static checkers, model checkers, certifying compilers, and test generators). : [[Complete-Search-Algorithms-for-SAT|Link]]
- **33.2 Background** — formal preliminaries: a signature $\Sigma$ (function/predicate symbols with arities; 0-arity function symbols are constants, 0-arity predicate symbols are propositional symbols); ground (variable-free) $\Sigma$-terms/formulas, treating a quantifier-free formula's free variables as constants in an expanded signature; atomic formulas (atoms).
- **33.3 Eager encodings to SAT** — translating the input formula directly into an equisatisfiable propositional formula that upfront encodes enough theory-specific consequences, applicable in principle to any theory with decidable ground satisfiability, at the risk of significant size blow-up, but able to reuse any off-the-shelf SAT solver. : [[CNF-Encodings|Link]]
- **33.4 Integrating theory solvers into SAT engines (the lazy approach)** — a SAT solver treats each theory atom as an opaque Boolean literal, finds a propositionally satisfying assignment, and hands the corresponding conjunction of literals to a theory solver for consistency-checking; theory solvers are typically built just for conjunctions of literals and embedded as submodules (the "DPLL(T)" architecture), letting the joint system handle arbitrary quantifier-free Boolean structure.
- **33.5 Theory solvers** — general methods for building decision procedures for conjunctions of literals in a given theory. : [[SAT-Techniques-for-Richer-Logics|Link]]
- **33.6 Combining theories** — techniques (e.g. Nelson-Oppen) for combining solvers for individual theories into a solver for their combination.
- **33.7 Extensions and enhancements.**

**Key Questions:**
1. Why is it insufficient (or even impossible) for many practically important background theories to explicitly encode the theory's axioms into a first-order formula and hand it to a general-purpose prover — what makes the theory-specific decision-procedure approach necessary rather than merely more efficient?
2. What is the essential architectural difference between the eager approach (translate the whole formula to SAT upfront) and the lazy approach (SAT solver + theory solver operating on abstracted Boolean literals), and what does each trade off in terms of translation blow-up versus solver-integration complexity?
3. Why do lazy-approach theory solvers typically only need to handle *conjunctions* of literals (not arbitrary Boolean structure), and how does embedding such a solver as a submodule inside a SAT engine let the combined system still handle formulas with arbitrary Boolean structure?

---
### Chapter 34: Stochastic Boolean Satisfiability (pp. 1331–1363)

**Summary:** The handbook's final chapter, on Stochastic Boolean Satisfiability (SSAT) — Papadimitriou's "game against nature" merging logic with probabilistic reasoning by adding randomized-quantifier variables to SAT — covering its definitions, PSPACE-complete complexity, special cases (MAJSAT, E-MAJSAT), the further generalization XSSAT (adding universal quantifiers, subsuming SAT/QBF/SSAT), analytical and algorithmic results, and its use in probabilistic planning. : [[Stochastic-Boolean-Satisfiability|Link]]

**Key Definitions & Concepts by Section:**
- **34.2 Definitions and notation** — an SSAT instance $\Phi=Q_1v_1\dots Q_nv_n\varphi$: a prefix ordering variables with quantifiers $Q_i\in\{\exists,R_{\pi_i}\}$ (existential or randomized-with-probability-$\pi_i$) and a CNF matrix $\varphi$; blocks/sub-blocks of similarly-quantified adjacent variables; $\Phi(\alpha)$/$\varphi(\alpha)$ (the residual problem/matrix after applying partial assignment $\alpha$, with prefix renumbering); an assignment tree specifying each existential variable's value contingent on preceding randomized-variable outcomes; the maximum probability of satisfaction $\Pr^*[\Phi]$, defined recursively: $0$ if $\varphi$ has an empty clause, $1$ if $\varphi$ is empty, $\max(\Pr[\Phi(v)],\Pr[\Phi(\bar v)])$ for a leading existential $v$, and the probability-weighted average $\Pr[\Phi(v)]\Pr[v]+\Pr[\Phi(\bar v)]\Pr[\bar v]$ for a leading randomized $v$. : [[Model-Counting|Link]]
- **34.2.1 Special cases and extensions** — MAJSAT (all variables randomized; solution is just $\Pr^*[\Phi]$, no assignment tree needed); E-MAJSAT (one existential block then one randomized block; solution is the existential assignment maximizing the resulting MAJSAT probability); Alternating SSAT (ASSAT, strictly alternating $\exists$/random quantifiers); Extended SSAT (XSSAT), adding universal quantifiers $\forall$ and a sixth recursive rule $\Pr^*[\Phi]=\min(\Pr[\Phi(v)],\Pr[\Phi(\bar v)])$ for a leading universal $v$ — general enough to encompass SAT, QBF, SSAT, MAJSAT, and E-MAJSAT as special cases; QBF reducible to SSAT by replacing $\forall$ with strictly-between-0-and-1 randomized quantifiers and checking $\Pr^*[\Phi]=1$. : [[Conflict-Driven-Clause-Learning|Link]]
- **34.3 Complexity** — SAT (NP-complete, also equivalent to belief-network most-probable-explanation/MPE), MAJSAT, E-MAJSAT, SSAT, and QBF each complete for successively harder complexity classes, showing how adding randomized then universal quantifiers to plain SAT tracks increasing computational difficulty and richer classes of probabilistic-planning/belief-network problems. : [[Proof-Complexity|Link]]
- **(34.4–34.8, by known structure)** — applications (probabilistic contingent planning); analytical results; algorithms (DPLL-style extensions with expectation computation) and empirical results; stochastic constraint programming; future directions.

**Key Questions:**
1. Why does the maximum-probability-of-satisfaction recursion use $\max$ for an existential variable but a probability-weighted *average* for a randomized variable — what does each operator represent about the two kinds of "choice" being modeled?
2. How does adding universal quantifiers (XSSAT's fifth rule, using $\min$) let SSAT subsume QBF as a special case, and why does replacing $\forall$ with strictly-interior-probability randomized quantifiers plus checking $\Pr^*[\Phi]=1$ correctly recover QBF satisfiability?
3. Why is E-MAJSAT's solution structurally simpler than general SSAT's (a single existential assignment rather than a full assignment tree), and what does this simplification reflect about the "one existential block then one randomized block" restriction on the quantifier prefix?

---
