# Pseudo-Boolean Reasoning and Compilation — Guidelines

## Header

**Title:** Pseudo-Boolean Reasoning and Compilation
**Author(s):** Romain Wallon (doctoral advisors: Daniel Le Berre, Pierre Marquis; supervisor: Stefan Mengel)
**Publication:** Doctoral thesis, Artois University (Centre de Recherche en Informatique de Lens, CNRS UMR 8188), defended December 14, 2020

**Brief Summary:**
This doctoral thesis studies pseudo-Boolean (PB) constraints — linear (in)equations $\sum_i \alpha_i \ell_i \ge \delta$ over Boolean literals — as a generalization of CNF clauses. Part I takes a knowledge-representation and knowledge-compilation perspective, showing that PB constraints are strictly more succinct than CNF but offer no extra tractable queries or transformations, and that bounding the width of CNF encodings (with auxiliary variables) sharply restricts expressiveness, with all standard width measures being tightly related via communication complexity. Part II takes a solving perspective, extending the CDCL architecture of modern SAT solvers to PB constraints via the cutting-planes proof system: it characterizes the harmful phenomenon of "irrelevant literals" produced by cutting-planes inference, studies weakening strategies to mitigate it, and adapts CDCL components (branching heuristics, learned-constraint deletion, restarts) to the specifics of PB constraints, with all strategies implemented and empirically evaluated in the solver Sat4j.

**Intent of the Author:**
The author aims to determine, both theoretically and empirically, whether pseudo-Boolean constraints deliver on their theoretical promise (succinctness over CNF, a strictly stronger cutting-planes proof system) as a practical representation and reasoning framework, and to identify concrete algorithmic obstacles and improvements — irrelevant literals, weakening tradeoffs, CDCL-strategy adaptation — that explain the gap between cutting-planes theory and pseudo-Boolean solver practice.

**Note on structure:** This document is a PhD thesis rather than a textbook; "chapters" below are thesis chapters, organized into Part I (Chapters 1–3, knowledge representation/compilation) and Part II (Chapters 4–7, solving).

---

## Topic List

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

## Chapter Summaries

### Chapter 1: Formal Preliminaries (pp. 7–35)

**Summary:** This chapter establishes the formal machinery used throughout the thesis: propositional logic and its normal forms, pseudo-Boolean constraints as a numerical generalization of clauses, elementary complexity theory, and the languages and criteria of knowledge compilation, culminating in the knowledge compilation map used to compare representation languages. : [[Computational-Complexity-Preliminaries|Link]]

**Key Definitions & Concepts by Section:**
- **1.1.1 Propositional Logic** — propositional formula (Def. 1), size of a formula (Def. 2), Boolean function (Def. 3), interpretation/assignment (Def. 4), semantics of a formula (Def. 6), model/counter-model (Def. 7), logical entailment $\models$ (Def. 8), logical equivalence $\equiv$ (Def. 9), literal (Def. 10), clause (Def. 11), Conjunctive Normal Form (Def. 12), term/cube (Def. 13), Disjunctive Normal Form (Def. 14), consistency/contradiction (Def. 15), validity (Def. 17). : [[Propositional-Logic-Foundations|Link]]
- **1.1.2 Pseudo-Boolean Constraints** — pseudo-Boolean constraint $\sum_i \alpha_i \ell_i \triangle \delta$ (Def. 19), size of a pseudo-Boolean constraint (Def. 20), model of a pseudo-Boolean constraint (Def. 21), normalized pseudo-Boolean constraint (Def. 22), cardinality constraint (Def. 23), a clause as a degree-1 pseudo-Boolean constraint with unit coefficients (Obs. 1). : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link1]], [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link2]], [[Pseudo-Boolean-Solving-via-Cutting-Planes|Link3]], [[Pseudo-Boolean-and-Cardinality-Constraints|Link4]]
- **1.1.3 Pseudo-Boolean Constraints and CNF Formulae** — CNF representation (Def. 24), the (possibly exponential) CNF representation of a pseudo-Boolean/cardinality constraint (Props. 2–3), CNF encoding with auxiliary variables (Def. 25), equisatisfiability (Def. 26). : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
- **1.2 Complexity Theory** — running time and worst-case running time (Defs. 27–28), big-O (Def. 29), complexity of an algorithm/problem (Defs. 30–31), complexity classes P, NP, coNP (Defs. 32–34), polynomial reduction, hardness, completeness (Defs. 35–37), NP-completeness of SAT (Theorem 2, Cook 1971). : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]
- **1.3.1 Some Compilation Languages** — circuit (Def. 38), Negation Normal Form (Def. 40), prime implicant/implicate and languages IP/PI (Defs. 41–43), decomposability and determinism (Defs. 44–45), DNNF and d-DNNF (Def. 46), Binary Decision Diagram, FBDD, OBDD, OBDD$_<$ (Defs. 47–50). : [[Propositional-Logic-Foundations|Link1]], [[Knowledge-Compilation|Link2]]
- **1.3.2 A Knowledge Compilation Map** — expressiveness $\le_e$ (Def. 51), succinctness $\le_s$ (Def. 52), the queries CO, VA, CE, IM, EQ, SE, CT, ME (Defs. 53–58), the transformations CD, FO, SFO, $\land$C, $\land$BC, $\lor$C, $\lor$BC, $\neg$C (Defs. 59–65). : [[Propositional-Logic-Foundations|Link]]

**Key Questions:**
1. Why does normalizing a pseudo-Boolean constraint not yield a unique canonical form, and what does this imply for reasoning about equivalence?
2. In what sense is a CNF *encoding* (with auxiliary variables) fundamentally different from a CNF *representation*, and why does this distinction matter for succinctness?
3. What is the difference between a query being satisfied by a language "in polynomial time" versus a transformation being satisfied, and why does the knowledge compilation map track both separately?

---

### Chapter 2: Pseudo-Boolean Constraints from a Knowledge Representation Perspective (pp. 37–58)

**Summary:** Using the criteria of the knowledge compilation map, this chapter shows that pseudo-Boolean and cardinality constraints (as the languages PBC/CARD) are strictly more succinct than CNF but incomparable in succinctness to most compilation languages, and — crucially — that most of the polynomial-time transformations offered by CNF (forgetting, bounded disjunction, closure under negation) become intractable for pseudo-Boolean constraints, while the tractable queries of CNF remain tractable. : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Some Properties of Pseudo-Boolean Constraints** — languages 1-PBC and 1-CARD of single constraints (Def. 66), the increasible-degree problem and its coNP-hardness (Prop. 4), the maximum-degree problem (Cor. 1), consistency/validity/entailment of a single constraint checkable in polynomial time (Props. 5–9), coNP-hardness of checking equivalence of two pseudo-Boolean constraints (Prop. 10), NP-hardness of counting models of a pseudo-Boolean constraint via reduction from subset-sum (Prop. 13), non-representability of conjunction/disjunction as a single pseudo-Boolean constraint (Props. 15–16). : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
- **2.2 Succinctness of Pseudo-Boolean Constraints** — languages PBC and CARD as conjunctions of constraints (Def. 67), PBC strictly more succinct than CARD (Prop. 17), CARD/PBC strictly more succinct than CNF (Prop. 19, Cor. 16), incomparability of CARD/PBC with OBDD$_<$, NNF, DNNF, IP, and DNF (Props. 20–21 and corollaries), summarized in the succinctness diagram (Fig. 2.1). : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
- **2.3 Querying and Transforming Pseudo-Boolean Constraints** — CARD/PBC satisfy VA and CD but not CO, CE, EQ, SE, CT, ME (Props. 22–24, Cor. 23), CARD/PBC satisfy $\land$C/$\land$BC but not $\lor$C/$\lor$BC/$\neg$C (Props. 25–27, Cors. 25–26), CARD/PBC do not satisfy SFO or FO (Props. 28–29). : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]

**Key Questions:**
1. Why is the "increasible-degree" problem coNP-hard, and what does its hardness reveal about the difficulty of finding a canonical/strongest form for a pseudo-Boolean constraint?
2. Given that CNF satisfies more transformations than pseudo-Boolean formulae, in what precise sense can pseudo-Boolean constraints still be said to be a "better" representation language, and for what?
3. What is the significance of the fact that CARD/PBC satisfy $\land$C (conjunction) but not $\lor$C (disjunction), and how does this asymmetry connect to the failure of forgetting (FO)?

---

### Chapter 3: Graph Width Measures for CNF Encodings with Auxiliary Variables (pp. 59–84)

**Summary:** This chapter asks what Boolean functions can actually be represented by CNF formulae (or encodings) of bounded graph width, using tools from knowledge compilation and communication complexity; it shows that bounding width severely restricts expressiveness to functions of low communication complexity, but that — once auxiliary variables are allowed — all the standard width measures (primal/incidence/dual treewidth, modular treewidth, cliquewidth, signed incidence cliquewidth, mim-width) are equivalent up to a logarithmic factor in the number of variables, which is shown to be tight via the at-most-one and permutation functions. : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]

**Key Definitions & Concepts by Section:**
- **3.1.1 Graphs Associated to CNF Formulae** — dependent auxiliary variable (Def. 68), primal graph (Def. 69), incidence graph (Def. 70). : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
- **3.1.2 Graph Width Measures** — tree decomposition (Def. 71), treewidth (Def. 72), modular treewidth (Def. 73), cliquewidth (Def. 74), signed incidence graph and signed cliquewidth (Defs. 75–76). : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
- **3.1.3 Communication Complexity** — combinatorial rectangle (Def. 77), rectangle cover (Def. 78), non-deterministic communication complexity $cc(f,\Pi)$ (Def. 79), best-case $\frac13$-balanced communication complexity $cc_{best}^{1/3}(f)$ (Def. 80). : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link1]], [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link2]]
- **3.1.4 Structured Deterministic DNNF** — v-tree (Def. 81), complete structured DNNF (Def. 82), width of a complete structured DNNF (Def. 83), proof tree of a DNNF (Def. 84). : [[Communication-Complexity-and-Lower-Bounds-on-Compilation|Link]]
- **3.2 The Effect of Auxiliary Variables** — the at-most-one function requires treewidth $n-1$ without auxiliary variables but treewidth 2 with the ladder encoding (Theorem 3). : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
- **3.3 Width and Communication Complexity** — rectangle covers bound structured DNNF width (Theorem 4), $\log(\text{width}) \ge cc(f,(Y,Z))$ (Prop. 30), lower bounds on treewidth/cliquewidth/mim-width via best-case communication complexity (Theorem 5, Cors. 29–31). : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
- **3.4 Relations between Different Width Measures of Encodings** — primal treewidth bounds imply modular treewidth/cliquewidth bounds within a $\log(n)$ factor and vice versa (Theorems 6–9), special tree decomposition and special treewidth (Defs. 87–88). : [[Graph-Width-Measures-for-CNF-Formulae-and-Encodings|Link]]
- **3.5 Some Applications** — asymptotically tight treewidth $\Theta(\log(\min(\delta,n-\delta)))$ for cardinality constraints (Cor. 33); treewidth $\Theta(n)$ for the permutation function, improving prior bounds by a logarithmic factor (Cor. 34).

**Key Questions:**
1. Why does bounding the *treewidth* of a CNF formula without auxiliary variables not meaningfully restrict expressiveness for functions with exponentially large CNF representations, and how does allowing auxiliary variables change this picture?
2. What is the intuitive connection between the width of a structured DNNF and the size of a rectangle cover in communication complexity, and why does this connection yield lower bounds on encoding width?
3. What is the practical implication of showing that all the width measures considered are equivalent up to a $\log(n)$ factor once auxiliary variables are allowed?

---

### Chapter 4: State of Pseudo-Boolean Solving (pp. 91–140)

**Summary:** This chapter surveys the CDCL architecture for SAT solving and its extension to pseudo-Boolean solving via the cutting planes proof system, covering propagation detection (slack, watched literals), conflict analysis (cancellation, coefficient-growth control via RoundingSat's reduction or reduction to cardinality constraints), branching/restart/deletion strategies, and the alternative approach of resolution-based pseudo-Boolean solving via CNF encodings or lazy clause inference, closing with an empirical comparison of state-of-the-art solvers. : [[Resolution-Based-Pseudo-Boolean-Solving|Link1]], [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link2]], [[Pseudo-Boolean-Solving-via-Cutting-Planes|Link3]]

**Key Definitions & Concepts by Section:**
- **4.1.1 Exploring the Search Space** — decision (Def. 91), pure literal (Def. 92), unit clause and unit propagation/BCP (Defs. 93–94), decision level (Def. 95), unit clause under a partial assignment (Def. 96), the watched literals data structure (Algorithm 1). : [[Practical-SAT-Solving-and-the-CDCL-Architecture|Link]]
- **4.1.2 Intelligent Backtracking** — the resolution and merge rules (Notation 13), soundness and refutation completeness (Defs. 97–98), the DP and DPLL algorithms (Algorithms 2–3), implication graph (Def. 99), assertive clause (Def. 100), unique implication point / 1-UIP (Def. 101), the CDCL algorithm and backjumping (Algorithms 4–5). : [[Practical-SAT-Solving-and-the-CDCL-Architecture|Link]]
- **4.1.3 Guiding the Search** — VSIDS and EVSIDS branching heuristics, variable bumping, phase saving, learned clause deletion strategies, literal block distance (Def. 102), restart policies (static geometric, Luby, dynamic Glucose-style with restart blocking). : [[Guiding-the-Search-in-CDCL-SAT-Solvers|Link]]
- **4.2.1 Detecting Propagations** — slack of a pseudo-Boolean constraint (Def. 103), assertive constraint (Def. 104), watched literal generalizations for cardinality (Obs. 6) and pseudo-Boolean (Obs. 7, Algorithm 6) constraints.
- **4.2.2 Analyzing Conflicts with Cutting Planes** — the cutting planes axioms and rules: addition, multiplication, division (with Remark 30 on why division breaks equivalence but strengthens cutting planes over resolution), the generalized resolution subsystem's saturation and cancellation rules, subadditivity of the slack under cancellation (Prop. 32), the reduction algorithm to preserve conflicts (Algorithm 7, Prop. 33), reduction to cardinality constraints (Algorithm 10), RoundingSat's weakening-and-division reduction (Algorithm 11), assertion level computation (Algorithm 9). : [[Pseudo-Boolean-Solving-via-Cutting-Planes|Link]]
- **4.2.3 Guiding the Search in a Pseudo-Boolean Solver** — coefficient/degree-aware bumping variants (bump-degree, bump-coefficient, bump-ratio-coefficient-degree from Pueblo), learned constraint deletion adapted from SAT solvers, restart policies in Sat4j/RoundingSat. : [[Guiding-the-Search-in-CDCL-SAT-Solvers|Link1]], [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link2]], [[Resolution-Based-Pseudo-Boolean-Solving|Link3]], [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link4]]
- **4.3 Pseudo-Boolean Solving Based on Resolution** — CNF encoding with dependent auxiliary variables, arc-consistent encodings (BDD-based, ladder, sequential, cardinality network), lazy clause inference from a pseudo-Boolean constraint during conflict analysis (Algorithm 12). : [[Resolution-Based-Pseudo-Boolean-Solving|Link]]

**Key Questions:**
1. Why is the notion of assertivity for a pseudo-Boolean constraint (based on slack) fundamentally more complex than for a clause, and what practical consequence does this have for watched-literal schemes?
2. Why does the division rule of cutting planes not preserve logical equivalence, and how does this property make cutting planes strictly stronger than resolution (p-simulation)?
3. What is the key tradeoff between RoundingSat's aggressive weakening-and-division approach and generalized resolution's saturation-and-cancellation approach, in terms of coefficient growth versus constraint strength?

---

### Chapter 5: On Irrelevant Literals in Pseudo-Boolean Constraint Learning (pp. 141–170)

**Summary:** This chapter identifies and characterizes a phenomenon specific to pseudo-Boolean (as opposed to clausal) reasoning — the presence of "irrelevant" literals that do not affect a constraint's truth value but can become "artificially relevant" after cutting-planes inference, thereby weakening the constraints a solver learns; it develops both a semantics-preserving removal strategy (weakening or simple removal, chosen via slack) and practical (incomplete) detection algorithms based on SAT solving or modular subset-sum via dynamic programming. : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Characterization of Irrelevant Literals** — irrelevant literal (Def. 105: $\chi|\ell \equiv \chi|\bar\ell$), the flip-invariance characterization (Theorem 10), monotonicity of relevance with respect to coefficients (Prop. 35), a propagated literal in an assertive constraint is always relevant (Prop. 36). : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
- **5.2 Irrelevant Literals in Pseudo-Boolean Solvers** — introduction of irrelevant literals by weakening, division, addition, and cancellation; artificially relevant literal (Def. 106), examples of artificial relevance arising in generalized-resolution-based and RoundingSat-based solvers (Prop. 38 on RoundingSat's division always making weakened irrelevant literals artificially relevant). : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
- **5.3 Removing Irrelevant Literals** — removal by weakening (5.3.1, may trigger saturation but can also weaken the result), simple removal (5.3.2, assigns the literal to 0, strengthens over the reals), slack-based choice between the two strategies (5.3.3, minimizing the resulting slack). : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
- **5.4.1 When to Detect Irrelevant Literals** — timing constraints from Prop. 37 (weakening cannot make an irrelevant literal artificially relevant) and Prop. 38 (division in RoundingSat does). : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
- **5.4.2 SAT-Based Relevance Check** — reducing the relevance check to the unsatisfiability of a two-constraint pseudo-Boolean formula, solved with a timeout by a pseudo-Boolean solver (sound but incomplete). : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]
- **5.4.3 Relevance Check Based on Dynamic Programming** — relevance check reduced to subset-sum, solved exactly via $O(n\delta)$ dynamic programming in principle but approximated by solving subset-sum modulo small primes (with multiple moduli, in the spirit of the Chinese remainder theorem) for tractability on large instances. : [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link]]

**Key Questions:**
1. What is the precise mechanism by which cutting-planes rules can turn an irrelevant literal into an "artificially relevant" one, and why does this matter for the strength of learned constraints?
2. Why is checking literal relevance NP-complete, and how do the SAT-based and modular-subset-sum-based detection algorithms trade completeness for tractability in different ways?
3. Given that irrelevant literals can lead to exponentially longer unsatisfiability proofs (as shown empirically on the vertexcover-completegraph family), why does the author conclude that removing them is still not a fully satisfactory counter-measure in practice?

---

### Chapter 6: On Weakening Strategies for Pseudo-Boolean Solvers (pp. 171–192)

**Summary:** This chapter studies how a pseudo-Boolean solver should apply the weakening rule when it is needed to guarantee that cancellation preserves a conflict, showing that different strategies — weakening all "ineffective" literals (yielding only clauses), RoundingSat-style full weakening, partial weakening, or a hybrid "Multiply and Weaken" approach — trade off constraint strength against constraint size and coefficient growth, with no single strategy dominating across benchmarks, though applying weakening on the conflict side (rather than the traditional reason side) tends to help. : [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Weakening Ineffective Literals for Shorter Constraints** — effective literal (Def. 107: a falsified literal whose satisfaction would not preserve the conflict/propagation), weakening away all ineffective literals always yields a clause (Prop. 39), every irrelevant literal is ineffective (Prop. 40), applying the strategy on the conflict side outperforms the reason side empirically, and applying it on both sides collapses cutting planes to plain resolution. : [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link]]
- **6.2 Stronger Constraints in RoundingSat-Based Solvers** — applying RoundingSat's weakening/division on only one side of cancellation to derive stronger constraints; the partial weakening rule and the PartialRoundingSat variant (Algorithm 13), which reduces a literal's coefficient by its remainder modulo the pivot's coefficient rather than removing it outright, yielding stronger constraints at comparable cost. : [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link]]
- **6.3 The Need for Tradeoffs** — the Multiply and Weaken strategy (multiplying the reason to align pivot coefficients via lcm-like bounds, then weakening down); empirical confirmation that the virtual best solver (VBS) over all weakening strategies substantially outperforms any single strategy, with PartialRoundingSat (both sides) the strongest individual variant. : [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link]]

**Key Questions:**
1. Why does weakening away all ineffective literals necessarily reduce a pseudo-Boolean constraint to a clause, and what does Proposition 40 (every irrelevant literal is ineffective) imply about using this as a cheap heuristic for removing irrelevant literals?
2. Why might weakening on the conflict side of the cancellation rule outperform the traditional reason-side weakening, contrary to the historical convention followed by most cutting-planes solvers?
3. What does the fact that no single weakening strategy dominates across all benchmark families (while the VBS substantially outperforms each) suggest about the underlying difficulty of choosing a weakening policy a priori?

---

### Chapter 7: Evaluating the Impact of CDCL Strategies in Pseudo-Boolean Solvers (pp. 193–232)

**Summary:** This chapter systematically adapts three pillars of the CDCL architecture — branching heuristics, learned-constraint-quality measures (for deletion and restarts), and their combination — to account for the coefficients, degrees, and partial-assignment structure specific to pseudo-Boolean constraints, and empirically shows that assignment/effectiveness-aware bumping strategies and size/degree-aware quality measures yield significant, though benchmark-dependent, performance gains when implemented in Sat4j. : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link1]], [[Weakening-Strategies-for-Pseudo-Boolean-Solvers|Link2]]

**Key Definitions & Concepts by Section:**
- **7.1 Adapting (E)VSIDS for Pseudo-Boolean Constraints** — coefficient/degree-based bumping strategies (bump-degree, bump-coefficient, bump-ratio-coefficient-degree, bump-ratio-degree-coefficient); assignment/effectiveness-based bumping strategies (bump-assigned, bump-falsified, bump-falsified-propagated, bump-effective, bump-effective-propagated); empirically, bump-ratio-coefficient-degree (Pueblo's heuristic) is best among coefficient-based strategies, while bump-effective or bump-assigned are best among assignment-based strategies, depending on the underlying proof system. : [[Pseudo-Boolean-and-Cardinality-Constraints|Link]]
- **7.2.1 Introducing New Quality Measures** — degree and degree-size quality measures (Def.-like list); five generalized definitions of literal block distance for pseudo-Boolean constraints accounting for unassigned literals: $LBD_a$ (Def. 108, assigned literals only), $LBD_s$ (Def. 109, unassigned literals as one "same" dummy level), $LBD_d$ (Def. 110, each unassigned literal its own "different" level), $LBD_f$ (Def. 111, falsified literals only), $LBD_e$ (Def. 112, effective literals only).
- **7.2.2 Application to Learned Constraint Deletion** — deletion strategies delete-slack, delete-degree, delete-degree-size, and the five delete-lbd-* variants; empirically, size/degree-based measures often outperform LBD-based ones in RoundingSat-based solvers, and all outperform the SAT-solver-inherited activity-based default. : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link1]], [[Pseudo-Boolean-Solving-via-Cutting-Planes|Link2]], [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning|Link3]]
- **7.2.3 Application to Restarts** — analogous restart-* strategies mirroring the quality measures; empirically these adaptive restarts underperform established SAT-solver restart policies (e.g., PicoSAT's), suggesting the new quality measures are better suited to deletion than to restart triggering. : [[Practical-SAT-Solving-and-the-CDCL-Architecture|Link1]], [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link2]]
- **7.3.1 Combining Learned Constraint Deletion and Restarts** — using the same quality measure for both simultaneously; gains are dominated by the deletion strategy rather than the restart policy. : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]
- **7.3.2 Combining All "Best" Strategies** — best-combination configurations (per proof system) of bumping, deletion, and restart strategies solve more instances than any single strategy or the default configuration, though a virtual-best-solver gap remains, indicating room for further tuning. : [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving|Link]]

**Key Questions:**
1. Why do assignment/effectiveness-aware bumping strategies (bump-effective, bump-assigned) outperform naive coefficient/degree-based generalizations of pbChaff's original heuristic, and how does this connect to the notion of effective/ineffective literals from Chapter 6?
2. Why is literal block distance not well-defined for a general pseudo-Boolean constraint, and what tradeoffs distinguish the five proposed generalizations ($LBD_a$, $LBD_s$, $LBD_d$, $LBD_f$, $LBD_e$)?
3. Why might quality measures effective for learned-constraint deletion perform poorly when reused to drive adaptive restarts, given that both nominally measure "constraint quality"?
