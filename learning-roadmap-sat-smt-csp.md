# Learning Roadmap — SAT/SMT/CSP

This is the decision-procedure backbone of the compiler: the CSP kernel that
searches for concrete counterexamples (bug *presence*), the SMT-style
decision procedures that discharge verification conditions, and the
constraint-propagation machinery that the CSP kernel shares with the
abstract-interpretation pass. The sequence starts from propositional
satisfiability and its complexity limits, builds up through CDCL, proof
certification, and pseudo-Boolean/cutting-planes reasoning, moves into
first-order decidable theories and their combination (Nelson–Oppen/SMT),
then pivots to constraint satisfaction proper — propagation, search, the
algebraic complexity theory, and soft/continuous extensions — before closing
with the three areas where this Focus Area is thickest with `static-analysis`
and `automated-reasoning`: abstract-interpretation/CP unification, CEGAR and
Constrained-Horn-Clause solving, and abduction/interpolation-based invariant
generation.

---

## 1. Propositional Logic, CNF, and Classical SAT Algorithms (Core Topic)

#### Pre-requisites
None — this is the entry point of the whole Focus Area.

#### Why this topic is important
Every later layer (CDCL, pseudo-Boolean solving, SMT, CSP propagation) is
built on the same substrate: formulas in conjunctive normal form and the
Davis–Putnam/DPLL search-and-inference loop. The Tseitin/definitional-CNF
transformation here is exactly the encoding step the CSP kernel will need
whenever it hands a candidate counterexample obligation to a SAT/SMT
backend.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Foundations-of-Symbolic-Logic-in-OCaml]]
   - [[Propositional-Logic]]
   - [[Propositional-Satisfiability-Algorithms]]
2. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability (Biere, Heule, van Maaren, Walsh, eds.)]]
   - [[History-and-Foundations-of-Satisfiability]]
   - [[CNF-Encodings]]
   - [[Complete-Search-Algorithms-for-SAT]]
3. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic (Enderton)]]
   - [[Sentential-Propositional-Logic]]
   - [[Switching-Circuits]]

#### Key Concepts and Definitions
1. Negation/disjunctive/conjunctive normal form, and the Tseitin definitional-CNF transformation, which introduces one auxiliary variable per subformula to get a linear-size, *equisatisfiable* (not logically equivalent) CNF.
2. The Davis–Putnam procedure (unit propagation, pure-literal rule, resolution) and its refinement into DPLL (splitting rather than resolution-based elimination).
3. Resolution as a refutation-complete proof system for CNF; width–size trade-offs (Ben-Sasson–Wigderson) that already hint at why plain DPLL/resolution is exponential on hard families (pigeonhole, Tseitin formulas).

#### Relevant Questions
1. Why does exploiting equisatisfiability (Tseitin) rather than insisting on logical equivalence avoid the exponential blowup that naive CNF conversion or NNF-then-distribute DNF/CNF conversion incurs?
2. DP, DPLL, and Stålmarck's method all decide propositional satisfiability via different core mechanisms (resolution, splitting+unit-propagation, dilemma+saturation) — what does each exploit to avoid exhaustive valuation enumeration?
3. Why is a resolution *width* lower bound already enough to prove a resolution *size* lower bound, and what does this predict about the ceiling on naive DPLL/CDCL performance for structured hard formulas?

---

## 2. Computability and the Boundary of Decidability (Core Topic)

#### Pre-requisites
[[#1. Propositional Logic, CNF, and Classical SAT Algorithms (Core Topic)|Topic 1]] (contrast: propositional SAT is NP-complete but *decidable*; first-order/arithmetic validity is not even that).

#### Why this topic is important
The CSP kernel and the theorem prover both live inside a hard boundary: SAT
is decidable-but-intractable, first-order validity is undecidable, and even
restricted arithmetic fragments split sharply into decidable (Presburger,
i.e. linear integer arithmetic without multiplication) and undecidable
(once multiplication or general divisibility is added) — this is exactly
the line the refinement-type contract language and its non-linear
constraint handling will have to respect.

#### Sources to Study
1. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic (Boolos, Burgess, Jeffrey)]]
   - [[Turing-and-Abacus-Computability]]
   - [[Recursive-Function-Theory]]
   - [[Recursive-Semirecursive-and-Arithmetical-Sets-and-Relations]]
   - [[Arithmetization-of-Syntax-and-Representability]]
   - [[Decidable-Fragments-of-Arithmetic]]
   - [[Nonstandard-Models-of-Arithmetic]]
   - [[Definability-in-Arithmetic-and-Forcing]]
2. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic (Enderton)]]
   - [[Weak-Fragments-of-Number-Theory]]
   - [[Representability-and-Recursive-Functions]]

#### Key Concepts and Definitions
1. Turing/abacus/recursive computability as three independently-motivated, provably equivalent formalizations of "effectively computable" (Church/Turing's thesis).
2. The arithmetical hierarchy (recursive, semirecursive/r.e., arithmetically definable) and Kleene's complementation principle — the general shape every later undecidability result (halting problem, Church's theorem, Gödel) instantiates.
3. Presburger arithmetic (linear arithmetic, no multiplication) is decidable via quantifier elimination; adding multiplication (or general divisibility predicates) makes the theory undecidable — the precise dividing line an SMT-style linear-arithmetic theory solver must stay on the right side of.

#### Relevant Questions
1. Why does "effectively computable" require three independent formalizations (Turing machines, abacus machines, recursive functions) rather than one, and why does their agreement count as evidence rather than proof for Church's thesis?
2. What exactly separates Presburger arithmetic's decidability from the undecidability of full arithmetic, and why is quantifier elimination the mechanism that makes that boundary constructive rather than merely a complexity-class statement?
3. How does the arithmetical hierarchy give a graded notion of "how undecidable" a set is, and why does that graded structure matter more to a solver-builder than the flat decidable/undecidable dichotomy?

---

## 3. Conflict-Driven Clause Learning (CDCL) and Modern SAT Architecture (Core Topic)

#### Pre-requisites
[[#1. Propositional Logic, CNF, and Classical SAT Algorithms (Core Topic)|Topic 1]].

#### Why this topic is important
CDCL is "the sole reason" (per the Handbook of Satisfiability) SAT scaled
from hundreds to millions of variables, and it is the direct ancestor of
every practical technique the CSP kernel and any embedded SMT backend will
actually run: the implication graph, non-chronological backtracking, and
conflict-driven learned clauses generalize almost unchanged into the
pseudo-Boolean (Topic 4) and lazy-clause-generation CSP (Topic 9) settings.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[Conflict-Driven-Clause-Learning]]
2. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/book-guidelines|Pseudo-Boolean Reasoning and Compilation (Wallon)]]
   - [[Practical-SAT-Solving-and-the-CDCL-Architecture]]
   - [[Guiding-the-Search-in-CDCL-SAT-Solvers]]

#### Key Concepts and Definitions
1. The implication graph (decisions, unit-propagated variables, antecedents, decision levels) and the conflict vertex $\bot$ produced when a clause is falsified.
2. Conflict analysis: tracing antecedents FIFO from $\bot$ back to a single current-decision-level literal yields an *asserting* learned clause, enabling non-chronological backjumping.
3. Branching heuristics (VSIDS-style activity scores), watched-literal data structures for efficient unit propagation, and restart/clause-deletion policies as the remaining engineering levers.

#### Relevant Questions
1. Why is the antecedent of a variable defined only for unit-propagated variables (never decisions), and how does that asymmetry drive the recursive decision-level computation used during conflict analysis?
2. Why does conflict analysis terminate with an asserting clause containing exactly one current-decision-level literal, and what would break if it stopped earlier or later in the trace?
3. CDCL's underlying proof system is plain resolution, yet CDCL vastly outperforms naive Davis–Putnam resolution in practice — what does this say about the relative contribution of search (branching/restarts/clause activity) versus the proof system itself?

---

## 4. Proof Complexity, Certification, and Pseudo-Boolean/Cutting-Planes Reasoning (Core Topic)

#### Pre-requisites
[[#3. Conflict-Driven Clause Learning (CDCL) and Modern SAT Architecture (Core Topic)|Topic 3]].

#### Why this topic is important
This is the theory that explains *why* a given CDCL/pseudo-Boolean search
can or cannot find a short refutation, and it supplies the proof-producing
discipline (RUP/DRAT-style checkable certificates) the theorem prover's
trusted kernel needs if the CSP kernel's counterexample search is to
produce a checkable certificate rather than a black-box "no" answer.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[Proof-Complexity]]
   - [[Proofs-of-Unsatisfiability]]
   - [[Worst-Case-Complexity-and-Tractability]]
   - [[Symmetry-Minimal-Unsatisfiability-and-Autarkies]]
2. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/book-guidelines|Pseudo-Boolean Reasoning and Compilation (Wallon)]]
   - [[The-Cutting-Planes-Proof-System]]
   - [[Pseudo-Boolean-Solving-via-Cutting-Planes]]
   - [[Irrelevant-Literals-in-Pseudo-Boolean-Constraint-Learning]]
   - [[Weakening-Strategies-for-Pseudo-Boolean-Solvers]]
   - [[Adapting-CDCL-Strategies-to-Pseudo-Boolean-Solving]]
   - [[Knowledge-Compilation]]
   - [[Succinctness-and-Tractability-of-Pseudo-Boolean-Languages]]

#### Key Concepts and Definitions
1. Proof systems as poly-time-checkable predicates satisfying soundness and completeness; polynomial simulation between systems (resolution ⊆ cutting planes ⊆ extended resolution in known-power terms).
2. Pseudo-Boolean constraints $\sum_i\alpha_i\ell_i \ge \delta$ generalize CNF clauses; the cutting-planes proof system (addition, multiplication, division/rounding) strictly generalizes resolution and can be exponentially more succinct, at the cost of introducing "irrelevant literals" during learned-constraint derivation that must be weakened away.
3. RUP (reverse unit propagation) clauses as exactly the property CDCL-learned clauses satisfy — the mechanism that lets a proof be hint-free (DRAT-style) yet still efficiently checkable.

#### Relevant Questions
1. Why does a resolution width lower bound (Ben-Sasson–Wigderson) translate into a size lower bound, and why does this explain why extended resolution/cutting-planes can be exponentially stronger?
2. Why can cutting-planes-style pseudo-Boolean inference introduce "irrelevant literals" that plain resolution never would, and why does removing them (weakening) trade constraint strength against constraint size?
3. Why is "satisfiability preservation" the most general notion of clause/constraint redundancy but unusable directly as a checkable proof system, and how does a syntactic criterion like RUP restore efficient checkability while still matching what CDCL/PB solvers actually learn?

---

## 5. Look-Ahead, Local Search, and the Statistical Physics of Random SAT (Core Topic)

#### Pre-requisites
[[#3. Conflict-Driven Clause Learning (CDCL) and Modern SAT Architecture (Core Topic)|Topic 3]].

#### Why this topic is important
CDCL is not universally dominant: look-ahead solvers win on low-density/
small-diameter instances, and local search gives fast *satisfying*
witnesses (useful for the CSP kernel's "prove bug presence" mode) at the
cost of never proving unsatisfiability. Knowing which architecture fits
which instance shape is a direct design input for the CSP kernel's own
search-strategy selection.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[Look-Ahead-Solving]]
   - [[Stochastic-Local-Search-for-SAT]]
   - [[Branching-Heuristic-Theory]]
   - [[Random-Satisfiability-and-Phase-Transitions]]
   - [[Runtime-Variation-and-Solver-Engineering]]
   - [[Statistical-Physics-of-Random-Constraint-Satisfaction]]
2. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming (Rossi, van Beek, Walsh, eds.)]]
   - [[Local-Search-Methods]]

#### Key Concepts and Definitions
1. Density (clause/variable ratio) vs. diameter (resolution-graph locality) as the axis separating where look-ahead (low density, small diameter) beats CDCL (large diameter, local clusters) and vice versa.
2. Stochastic local search: GSAT (greedy descent, plateaus rather than true traps), WalkSAT (focus on a random *unsatisfied* clause, then a freebie/noise/greedy move) — one-sided error, cannot prove UNSAT.
3. The satisfiability threshold conjecture for random $k$-SAT, backdoor sets, and heavy-tailed runtime distributions as the theoretical basis for randomized restarts.

#### Relevant Questions
1. Why does high formula density penalize look-ahead (via propagation cost) while large diameter penalizes CDCL (via locality of learned clauses) specifically?
2. Why does a heavy-tailed runtime distribution (rather than mere high variance) directly justify restarts as an algorithmic exploit rather than a discretionary tuning knob?
3. What does the gap between the best known upper bound on the satisfiability threshold and the largest density any known efficient algorithm actually solves ("the algorithmic barrier") suggest about hardness that isn't captured by the threshold itself?

---

## 6. First-Order Decision Procedures and Quantifier Elimination (Core Topic)

#### Pre-requisites
[[#2. Computability and the Boundary of Decidability (Core Topic)|Topic 2]], [[#1. Propositional Logic, CNF, and Classical SAT Algorithms (Core Topic)|Topic 1]].

#### Why this topic is important
This is the direct ancestor of the theory solvers an SMT backend needs for
the refinement-type contract language's arithmetic and array reasoning:
Presburger arithmetic, linear/nonlinear real arithmetic, and algebraic
decision procedures (Gröbner bases) are exactly the decidable fragments a
verification-condition discharge engine dispatches to.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[First-Order-Logic-Syntax-and-Semantics]]
   - [[Automated-First-Order-Theorem-Proving]]
   - [[Decidable-Theories-and-Quantifier-Elimination]]
   - [[Algebraic-Decision-Procedures]]
2. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic]]
   - [[Decidable-Fragments-of-Arithmetic]]
3. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic]]
   - [[Weak-Fragments-of-Number-Theory]]

#### Key Concepts and Definitions
1. Skolemization, Herbrand's theorem, and the ground-instance-enumeration lineage (Gilmore → Davis–Putnam → Prawitz/tableaux → resolution → model elimination) as successive attacks on the same "explosion of ground instances."
2. Quantifier elimination as an algorithmic route to decidability: Cooper's algorithm for Presburger arithmetic, cylindrical algebraic decomposition / Tarski–Seidenberg for real closed fields, and quantifier elimination for algebraically closed fields via the Fundamental Theorem of Algebra.
3. Gröbner bases and Buchberger's algorithm as a rewriting/completion procedure deciding polynomial ideal membership, used both for algebraic word problems and (via Rabinowitsch's trick) as a fast alternative to real quantifier elimination for algebraic identities.

#### Relevant Questions
1. Why do the AE (∀*∃*) prefix fragment and Presburger arithmetic both admit decidability, yet only the AE fragment gets it "for free" from Herbrand's theorem while Presburger genuinely needs an infinite family of divisibility predicates and a dedicated elimination algorithm?
2. Wu's method and Tarski/Seidenberg real quantifier elimination both decide geometric theorems — in what sense is Wu's triangularization a genuinely weaker (sufficient, not necessary non-degeneracy) notion of proof, and why does that weakness buy efficiency?
3. Why does Newman's lemma (termination + local confluence ⇒ confluence) let Knuth–Bendix-style completion (and, in the algebraic setting, Buchberger's algorithm via S-polynomials) get away with checking only finitely many critical/overlap pairs?

---

## 7. Equality Reasoning, Term Rewriting, and Congruence Closure (Core Topic)

#### Pre-requisites
[[#6. First-Order Decision Procedures and Quantifier Elimination (Core Topic)|Topic 6]].

#### Why this topic is important
Congruence closure is the decision procedure for the ground equality
fragment every SMT solver's core relies on, and rewriting/completion is the
same machinery the elaborator's definitional-equality checker (`isDefEq`)
needs — this topic is the direct bridge between the `type-theory` unifier
and the `sat-smt-csp` decision-procedure stack.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Equality-Reasoning]]
2. [[39_Equality-Saturation-RossThesis2012/book-guidelines|Equality Saturation: Using Equational Reasoning to Optimize Imperative Functions (Tate)]]
   - [[Equality-Saturation]]
   - [[The-Peggy-Implementation]]
   - [[Loop-and-Branch-Optimizations-Discovered-by-Saturation]]

#### Key Concepts and Definitions
1. Congruence closure of a ground equation set, decided via union-find with a predecessor function; Ackermann's reduction eliminating function symbols in favor of new variables, reducing further to propositional tautology checking.
2. Termination orderings (lexicographic path order), confluence/local confluence (Newman's lemma), and Knuth–Bendix completion turning an equation set into a canonical (terminating, confluent) rewrite system via critical-pair analysis.
3. Equality saturation: rather than destructively rewriting, add equalities monotonically to an e-graph until saturation, representing exponentially many equal programs at once and eliminating the phase-ordering problem that plagues sequential rewrite-based optimizers.

#### Relevant Questions
1. What is the essential difference between congruence closure (deciding ground equational validity) and paramodulation (a general first-order-with-equality inference rule), and why does the latter need functional-reflexivity axioms or restrictions (e.g. no paramodulation into variables) to stay refutation-complete?
2. Why does treating optimizations as *additive* equality analyses (equality saturation) rather than destructive rewrites eliminate the phase-ordering problem that ordinary term-rewriting-based compiler optimization suffers from?
3. In what sense is Newman's lemma the same mathematical fact underlying both Knuth–Bendix completion (Topic 6) and equality saturation's confluence/uniqueness-of-normal-form guarantees?

---

## 8. Combining Decision Procedures: Nelson–Oppen, Shostak, and SMT (Core Topic)

#### Pre-requisites
[[#6. First-Order Decision Procedures and Quantifier Elimination (Core Topic)|Topic 6]], [[#7. Equality Reasoning, Term Rewriting, and Congruence Closure (Core Topic)|Topic 7]].

#### Why this topic is important
No single decidable theory covers a real refinement-type contract language
(it needs linear arithmetic, uninterpreted functions, and often arrays or
bit-vectors together); this topic is exactly the theory of how to combine
independently-sound, independently-complete decision procedures into one
SMT engine without re-deriving soundness from scratch.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Combining-Decision-Procedures]]
2. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[SAT-Techniques-for-Richer-Logics]]
3. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/book-guidelines|Modular Constraint Solver Cooperation via Abstract Interpretation (Talbot, Monfroy, Truchet)]]
   - [[Relation-to-Other-Cooperation-Frameworks]]

#### Key Concepts and Definitions
1. Craig's interpolation theorem, proved constructively via propositional interpolation lifted through Herbrand's theorem and Skolemization — the technical engine behind theory combination and (later) interpolation-based invariant generation (Topic 18).
2. The Nelson–Oppen combination method: theories with disjoint signatures, purification/homogenization of "alien" subterms, and (for efficiency) the stably-infinite and convex conditions that avoid enumerating all possible equalities between shared variables.
3. Shostak's method (canonizer + solver) as a more efficient, less general alternative to Nelson–Oppen; the lazy vs. eager architectural split in modern SMT, and Nelson–Oppen recast as a *reduced product* of abstract domains under abstract interpretation.

#### Relevant Questions
1. Why does convexity fail for both linear integer arithmetic and real arithmetic with multiplication, and what does the resulting need for case-splitting cost Nelson–Oppen in practice?
2. In what sense is Nelson–Oppen theory combination a special case of the reduced-product construction from abstract interpretation (Topic 14), and what does that reframing buy over treating SMT combination as sui generis?
3. Why does Shostak's method trade generality for efficiency compared to Nelson–Oppen, and under what conditions on the component theories does that trade actually pay off?

---

## 9. Constraint Satisfaction Foundations: Representation, Local Consistency, and Propagation (Core Topic)

#### Pre-requisites
[[#1. Propositional Logic, CNF, and Classical SAT Algorithms (Core Topic)|Topic 1]] (propagation is the CSP analogue of unit propagation).

#### Why this topic is important
This is the direct foundation of the project's CSP kernel: a CSP as
$\langle X,D,C\rangle$, arc/path/$k$-consistency, and the propagator model
(contracting, sound, monotone functions on domains, iterated to a least
fixpoint) is exactly the abstraction the kernel's domain/lattice
propagation over integer, non-linear, and automaton-shaped domains needs to
be built on.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming]]
   - [[Foundations-and-History-of-Constraint-Satisfaction]]
   - [[Constraint-Propagation-and-Local-Consistency]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[Constraint-Satisfaction-Problem-Foundations]]
   - [[Consistency-and-Propagation-in-Constraint-Programming]]
3. [[42_Constraint Propagation_Guido_Tack_PhD_2009/book-guidelines|Constraint Propagation: Models, Techniques, Implementation (Tack)]]
   - [[Constraint-Satisfaction-and-Propagation-Based-Solving]]
   - [[The-Denotational-and-Operational-Model-of-Constraint-Propagation]]
   - [[Propagation-Strength-and-Domain-Approximations]]
   - [[Efficient-Propagator-Scheduling]]
   - [[Implementation-Architecture-of-a-Propagation-Kernel]]

#### Key Concepts and Definitions
1. CSP $P=\langle X,D,C\rangle$; (generalized) arc consistency, path/$k$-consistency, and the observation that local consistency with non-empty domains does not guarantee a global solution — inference alone is never enough.
2. Propagators as contracting, sound, monotone functions on domains; the induced constraint of a propagator; propagation as iteration to a mutual least fixpoint, formalized via a preorder of domain "tightenings."
3. Propagation *strength* as a graded notion (domain completeness vs. bounds(Z)/bounds(D)/bounds(R)/range consistency) — a strictly weaker-but-cheaper consistency can occasionally be *more* expensive to decide than full arc consistency, so strength and tractability are not monotonically linked.

#### Relevant Questions
1. Why does achieving arc or path consistency with non-empty domains not by itself guarantee a globally consistent solution, and what does this imply about the limits of inference alone versus search?
2. Why can bound(Z) consistency sometimes be exponentially *harder* to decide than full arc consistency despite being a nominally "weaker" notion, and what does this say about when weakening a consistency level is actually a useful compromise?
3. What does formalizing propagation as iteration to a "mutual fixpoint" of monotone propagators buy over an ad hoc propagation-loop implementation — specifically for proving termination and confluence?

---

## 10. Backtracking Search, Global Constraints, and Symmetry Breaking (Core Topic)

#### Pre-requisites
[[#9. Constraint Satisfaction Foundations: Representation, Local Consistency, and Propagation (Core Topic)|Topic 9]].

#### Why this topic is important
This is where propagation (Topic 9) meets search: backjumping and nogood
recording are the CSP analogue of CDCL's implication-graph learning
(Topic 3), and global constraints (`alldifferent`, `regular`, `cumulative`)
are exactly the abstract-data-structure/automaton-shaped domains the CSP
kernel needs for reasoning about complex program invariants rather than
just scalar bounds.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming]]
   - [[Backtracking-Search]]
   - [[Global-Constraints]]
   - [[Symmetry-in-Constraint-Programming]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[Exploration-and-Search-in-Constraint-Programming]]

#### Key Concepts and Definitions
1. Conflict-directed backjumping (CBJ) and jumpback nogoods as the CSP-search analogue of CDCL's asserting clauses; maintaining arc consistency (MAC) during search versus forward checking versus DPLL-style unit propagation — three points on the same propagation/search trade-off curve.
2. Global constraints as filtering algorithms exploiting graph/matching/flow theory: `alldifferent` via maximum-cardinality matching (Régin), the `regular` constraint via a layered DFA-transition digraph — the direct precedent for automaton/DFA-shaped abstract domains.
3. Symmetry-breaking as a group-theoretic problem: lex-leader constraints, and dynamic methods (SBDS, SBDD) that add symmetry-breaking information only conditionally, respecting the search heuristic rather than statically ruling out branches.

#### Relevant Questions
1. Why are CBJ and MC$_k$-CBJ (constraint-propagation-augmented conflict-directed backjumping at different consistency levels $k$) incomparable — each exponentially better than the other on some instances — despite CBJ seeming like a strict improvement over chronological backtracking?
2. How does Régin's matching-based `alldifferent` filtering (edges in a matching, on even alternating paths, or on even alternating circuits) generalize to the `regular` constraint's DFA-digraph filtering, and what is the common structural principle?
3. Why must dynamic symmetry-breaking methods (SBDS/SBDD) add symmetry-related pruning *conditionally* rather than statically ruling out symmetric branches outright?

---

## 11. The Algebraic Theory of CSP: Polymorphisms, Dichotomy, and Structural Tractability (Core Topic)

#### Pre-requisites
[[#10. Backtracking Search, Global Constraints, and Symmetry Breaking (Core Topic)|Topic 10]].

#### Why this topic is important
This is the theoretical ceiling on what the CSP kernel can hope to solve in
polynomial time: the complexity of $\mathrm{CSP}(\Gamma)$ over a fixed
constraint language depends *only* on the language's polymorphisms, and
graph-theoretic structural parameters (treewidth, hypertree width) give an
orthogonal, instance-shape-based route to tractability independent of the
constraint language itself.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming]]
   - [[Tractability-and-Computational-Complexity-of-CSPs]]
2. [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/book-guidelines|The Constraint Satisfaction Problem: Complexity and Approximability (Krokhin & Živný, eds.)]]
   - [[The-Algebraic-Approach-to-CSP]]
   - [[Absorption-Theory]]
   - [[CSP-over-Infinite-and-Numeric-Domains]]
   - [[Hybrid-Tractability]]
   - [[Backdoor-Sets-and-Fixed-Parameter-Tractability]]
   - [[Digraph-CSP]]
   - [[Approximation-Algorithms-for-CSP]]
   - [[Quantified-CSP]]

#### Key Concepts and Definitions
1. Relational clones, polymorphisms, and the Galois connection $\langle\Gamma\rangle = Inv(Pol(\Gamma))$: tractability/NP-completeness of a constraint language is entirely a property of its polymorphism algebra, not of any particular relation in it.
2. Sufficient tractability conditions from specific polymorphism shapes: semilattice operations (tractable via arc consistency alone), near-unanimity operations (tractable because $k$-consistency = global consistency), Mal'tsev operations (tractable via generalized Gaussian elimination) — and the Bulatov–Jeavons–Krokhin dichotomy conjecture these instantiate.
3. Structural tractability orthogonal to the algebraic route: induced width/treewidth bounding inference-algorithm (bucket-elimination) complexity exactly, versus hypertree width as a strictly more general (arity-sensitive) tractable class.

#### Relevant Questions
1. Why does reducing tractability classification to relational clones, then to polymorphisms, make the classification problem more tractable rather than merely relabeling it?
2. What is the intuitive reason a near-unanimity polymorphism of arity $k$ guarantees that enforcing $k$-consistency achieves *global* consistency, while a semilattice or Mal'tsev polymorphism achieves tractability by an entirely different mechanism?
3. What kind of problem instance separates treewidth from hypertree width (bounded hypertree width but unbounded treewidth), and why does this matter for choosing which structural parameter to exploit in the CSP kernel's own solver?

---

## 12. Soft Constraints, Modelling, and Constraint Logic Programming (Core Topic)

#### Pre-requisites
[[#9. Constraint Satisfaction Foundations: Representation, Local Consistency, and Propagation (Core Topic)|Topic 9]].

#### Why this topic is important
Refinement-type checking is rarely a pure satisfy/fail problem — the
CSP kernel needs graded, over-constrained reasoning (soft constraints) for
ranking candidate counterexamples or repairs, and the modelling-choice
lessons here (auxiliary variables, implied constraints, channelling between
viewpoints) apply directly to how the compiler should encode Hoare/Horn
verification conditions as CSPs in the first place.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming]]
   - [[Soft-Constraints-and-Preferences]]
   - [[Modelling-Constraint-Satisfaction-Problems]]
   - [[Constraint-Logic-Programming]]
   - [[Integration-of-Constraint-Programming-and-Operations-Research]]
2. [[18_JW_Lloyd_Foundations_logic_programming_1987/book-guidelines|Foundations of Logic Programming (Lloyd)]]
   - [[SLD-Resolution]]
   - [[Integrity-Constraint-Checking]]

#### Key Concepts and Definitions
1. The c-semiring and valued-CSP frameworks as dual, equally-expressive generalizations of hard constraints to graded preferences; fuzzy constraints as the unique idempotent ($\min$-combination) case, uniquely well-behaved under local consistency.
2. The CLP($C$) scheme (Jaffar–Lassez): operational, algebraic, and (fixpoint) logical semantics of a constraint logic program, unifying SLD-resolution-style logic programming with constraint solving.
3. Modelling craft: auxiliary variables, implied (redundant) constraints, and channelling constraints between multiple viewpoints frequently *improve* propagation-based search despite adding variables/constraints — directly contradicting "minimize the model" folklore.

#### Relevant Questions
1. Why does the min-operator's idempotency make fuzzy constraints uniquely well-behaved (equivalence-preserving local consistency, decomposition into classical CSPs via $\alpha$-cuts) compared to non-idempotent frameworks like weighted CSP?
2. Why can adding more variables/constraints to a CSP model (auxiliary variables, redundant viewpoints, implied constraints) reduce total search effort, and under what condition does one viewpoint's own constraints become entirely propagation-redundant with another's?
3. How does the CLP schema's separation of operational/algebraic/logical semantics let a naive disjunctive constraint definition and a highly optimized propagator-based one carry the *same* declarative meaning — and why is this simultaneously a strength (modularity) and a weakness (no way to compare models for efficiency)?

---

## 13. Continuous, Interval, and Nonlinear Constraint Solving (Core Topic)

#### Pre-requisites
[[#9. Constraint Satisfaction Foundations: Representation, Local Consistency, and Propagation (Core Topic)|Topic 9]], [[#6. First-Order Decision Procedures and Quantifier Elimination (Core Topic)|Topic 6]] (real quantifier elimination as the exact-decision-procedure baseline this topic trades against).

#### Why this topic is important
The stated CSP kernel goal explicitly includes handling integer *and*
non-linear equations, not just Boolean/finite-domain constraints — interval
arithmetic, the octagon abstract domain, and spatial branch-and-bound are
the concrete techniques for over-approximating and searching continuous
constraint spaces without paying quantifier-elimination's doubly-exponential
worst case.

#### Sources to Study
1. [[24_Handbook_Constraint_Programming_Elsevier_2006/book-guidelines|Handbook of Constraint Programming]]
   - [[Continuous-and-Interval-Constraints]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[The-Octagon-Abstract-Domain]]
   - [[Octagonal-Constraint-Solving]]
3. [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/book-guidelines|Reformulation and Convex Relaxation Techniques for Global Optimization (Liberti)]]
   - Convexity and Function/Set Classification; Spatial Branch-and-Bound (sBB) Algorithms; Convex and Linear Relaxation Techniques; Reduction Constraints for Sparse Bilinear Programs (topic-list entries — no generated article yet)

#### Additional external sources
For the spatial branch-and-bound / MINLP material, Liberti's thesis and
Grimstad's B-spline-surrogate thesis ([[59_Grimstad_Global_Spline_Optimization/book-guidelines|Daily Production Optimization for Subsea Production Systems]]) are applied/engineering-flavored rather than foundational; a
standard reference such as Belotti et al.'s survey on mixed-integer
nonlinear programming would round out the theoretical picture if deeper
non-linear CSP solving becomes load-bearing for the compiler's contract
language.

#### Key Concepts and Definitions
1. Interval arithmetic and hull/box/bound consistency as the continuous-domain analogue of arc consistency; the HC4-Revise propagation algorithm.
2. The octagon abstract domain: octagonal constraints $\pm x_i \pm x_j \le c$, represented via difference-bound matrices and closed under intersection by a modified Floyd–Warshall algorithm — a concrete instance of a "richer-than-box" abstract domain usable as a CSP domain representation.
3. Spatial branch-and-bound (sBB): region selection, convex/linear relaxation (McCormick envelopes for bilinear terms, $\alpha$BB for general nonconvex terms) as lower-bounding steps, and bounds tightening — the generic algorithmic skeleton for globally solving non-convex NLPs/MINLPs.

#### Relevant Questions
1. Why does the octagon domain's closure algorithm reduce to a modified Floyd–Warshall shortest-path computation, and what does that reveal about the relationship between difference-bound-matrix domains and graph algorithms generally?
2. McCormick envelopes and $\alpha$BB underestimation both produce convex relaxations of nonconvex terms — what is the structural difference between a *bilinear-term* relaxation and a *general nonconvex-term* relaxation that explains why one needs a diagonal-shift parameter ($\alpha$) and the other does not?
3. Given real quantifier elimination's doubly-exponential worst case (Topic 6), what accuracy/completeness is actually given up by using interval/octagon propagation or sBB relaxation instead — and under what circumstances would falling back to exact QE be worth the cost?

---

## 14. Abstract Interpretation as a Unifying Theory for Constraint Solver Cooperation (Core Topic)

#### Pre-requisites
[[#9. Constraint Satisfaction Foundations: Representation, Local Consistency, and Propagation (Core Topic)|Topic 9]], [[#13. Continuous, Interval, and Nonlinear Constraint Solving (Core Topic)|Topic 13]]; also draws on Galois connections and fixpoint theory from the `static-analysis` Focus Area (see [[learning-roadmap-static-analysis|↪ focused roadmap]], Topics 2–3).

#### Why this topic is important
This is the topic that most directly fuses `sat-smt-csp` with
`static-analysis`: the thesis (Pelleau, Talbot) is that CP's propagation-
and-search and AI's Galois-connection-based abstraction are *the same
mathematical framework* — which is exactly the architecture the project
needs, since the CSP kernel (proving bug presence) and the abstract
interpreter (proving bug absence) must share a domain/lattice vocabulary
rather than being built as two unrelated engines.

#### Sources to Study
1. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[Links-Between-Abstract-Interpretation-and-Constraint-Programming]]
   - [[Unified-Abstract-Domains-for-Constraint-Programming]]
   - [[Abstract-Interpretation-Reformulation-of-Constraint-Programming]]
   - [[The-AbSolute-Solver]]
2. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/book-guidelines|Modular Constraint Solver Cooperation via Abstract Interpretation (Talbot, Monfroy, Truchet)]]
   - [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving]]
   - [[Abstract-Domains-For-Constraint-Programming]]
   - [[Domain-Transformers]]
   - [[Interval-Propagators-Completion-IPC]]
   - [[Delayed-Product-DP]]
   - [[Shared-Product-and-Modular-Composition]]

#### Key Concepts and Definitions
1. Consistency (in CP) recast as a form of *narrowing* (in AI); a CSP's domain representation (boxes, octagons) recast directly as an AI abstract domain with a Galois connection to the concrete solution set — the "unified abstract domain for CP" that generalizes both fields' solving processes into one algorithm.
2. Domain transformers as functors building new abstract domains from existing ones: the *direct product* (no information exchange between components) versus *interval propagators completion* (lets domains exchange bound constraints) versus the *delayed product* (defers handing a constraint to a specialized domain until variables are sufficiently instantiated, inspired by delayed goals in logic programming).
3. The *shared product*: combining domain transformers that share underlying abstract domains without duplicating state, via projection/join functions and Knaster–Tarski fixpoint merging — the mechanism that keeps modular composition sound.

#### Relevant Questions
1. In what precise sense does recasting a CSP's own consistency-enforcement as narrowing (rather than as a bespoke CP notion) let the "unified abstract solving algorithm" recover classical CP solvers as one instance among many?
2. Why does the direct product of abstract domains fail to let components exchange information, and how does interval propagators completion (IPC) fix this while remaining sound over an over-approximating product?
3. What does the delayed product's borrowing from logic-programming "delayed goals" buy operationally — i.e., why is deferring a constraint's transfer to a specialized domain until partial instantiation better than either an immediate or a never transfer?

---

## 15. CEGAR, Model Checking, and Constrained Horn Clause Solving (Core Topic)

#### Pre-requisites
[[#8. Combining Decision Procedures: Nelson–Oppen, Shostak, and SMT (Core Topic)|Topic 8]], [[#14. Abstract Interpretation as a Unifying Theory for Constraint Solver Cooperation (Core Topic)|Topic 14]].

#### Why this topic is important
This is where the compiler's two halves meet operationally: CEGAR is the
loop that lets an over-approximating abstract-interpretation pass and a
concrete SMT/CSP counterexample search refine each other, and CHC-SAT
solving is precisely the verification-condition formalism the automated
invariant generator (Hoare/Horn contracts) will target — this topic and
`static-analysis`'s CEGAR/model-checking topics should be read together.

#### Sources to Study
1. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|New Techniques for Abstraction Refinement (Greitschus)]]
   - [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)]]
   - [[Abstract-Interpretation]]
   - [[Path-Programs-and-Loop-Invariants]]
   - [[ULTIMATE-and-ULTIMATE-TAIPAN]]
2. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking (Baier & Katoen)]]
   - [[Model-Checking-Fundamentals]]
   - [[Automata-over-Finite-and-Infinite-Words]]
   - [[Automata-Based-LTL-Model-Checking]]
   - [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams]]
   - [[Markov-Decision-Processes]]
3. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/book-guidelines|ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses (Frohn & Giesl)]]
   - [[Constrained-Horn-Clauses-(CHCs)]]
   - [[Loop-Acceleration]]
   - [[The-ADCL-Calculus]]
   - [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization]]

#### Key Concepts and Definitions
1. The CEGAR loop: abstract, model-check, and — on a spurious counterexample — refine the abstraction; classical CEGAR (SMT-based loop unwinding) lacks termination guarantees, motivating trace-abstraction-plus-abstract-interpretation hybrids (ULTIMATE TAIPAN) that are guaranteed to find loop invariants from path programs.
2. Constrained Horn Clauses (CHCs) as the standard verification-condition formalism: facts, rules, queries; CHC-SAT as "does a model exist" versus proof search for a conditional empty clause.
3. Loop acceleration inside a resolution calculus (ADCL): computing the $N$-fold closure of a recursive derivation in one step (over decidable acceleration classes — difference bounds, octagons, VASS) rather than unrolling thousands of ordinary resolution steps — sound and refutationally complete, though not terminating in general.

#### Relevant Questions
1. Why do classical SMT-based CEGAR loops lack termination guarantees, and what specifically does combining abstract-interpretation fixpoints with SMT-based trace analysis (ULTIMATE TAIPAN) add to guarantee loop-invariant discovery?
2. How does the CHC resolution calculus's redundancy relation (blocking clauses) interact with loop acceleration to keep the search space from re-deriving already-subsumed facts, and why is completeness preserved despite this pruning?
3. What decidable classes of transition relations (difference bounds, octagons, vector addition systems with states) admit closed-form $N$-fold acceleration, and why does the CSP kernel's own domain choices (octagons already appear in Topic 13) matter for which loops ADCL-style acceleration can actually close in one step?

---

## 16. Automata-Based and Symbolic Domains for Verification and Constraint Solving (Core Topic)

#### Pre-requisites
[[#10. Backtracking Search, Global Constraints, and Symmetry Breaking (Core Topic)|Topic 10]] (the `regular` global constraint is the entry point into this topic).

#### Why this topic is important
This is the direct source material for the CSP kernel's requirement to
represent abstract data structures as complex domains "like automata
grammars (DFA)" — tree automata and symbolic (predicate-labeled) automata
are the two concrete formalisms for reasoning about unbounded/infinite-
alphabet structured domains that finite-domain CSP propagation alone cannot
express.

#### Sources to Study
1. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications (Comon et al.)]]
   - [[Automata-with-Constraints]]
   - [[Tree-Set-Automata-and-Set-Constraints]]
   - [[Alternating-Tree-Automata]]
2. [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/book-guidelines|The Power of Symbolic Automata and Transducers (D'Antoni & Veanes)]]
   - [[Effective-Boolean-Algebras]]
   - [[Symbolic-Finite-Automata]]
   - [[Minterms-and-Alphabet-Equivalence-Classes]]
   - [[Parametric-Complexity-of-Symbolic-Algorithms]]
   - [[Variants-of-Symbolic-Automata]]
   - [[Symbolic-Automata-in-Practice]]
   - [[Symbolic-Finite-Transducers]]

#### Key Concepts and Definitions
1. Tree automata with equality/disequality constraints between subtrees, needed for non-linear pattern recognition; emptiness becomes undecidable for the fully general constrained class, forcing restricted subclasses (reduction automata, bounded equality depth) to keep decision procedures effective.
2. Alternating tree automata: positive Boolean transition formulas enable complementation without determinization, and correspond directly to Horn clauses / definite set constraints — a structural bridge to CHC-solving (Topic 15).
3. Symbolic (predicate-labeled) finite automata over an *effective Boolean algebra*: complexity now depends jointly on state-space size and alphabet-theory (predicate satisfiability) cost; minterms as maximal satisfiable predicate combinations compile an s-FA down to a classic automaton at the cost of potential predicate-space explosion.

#### Relevant Questions
1. Why does allowing equality/disequality constraints between sibling subtrees push emptiness from decidable to undecidable in the general case, and what structural restriction (bounded equality depth, reduction automata) recovers decidability?
2. How does the correspondence between alternating tree automata and Horn clauses / definite set constraints let CHC-style verification-condition solving borrow automata-theoretic decision procedures?
3. Why does complexity in the symbolic-automata setting depend on *both* the state/transition count and the alphabet theory's satisfiability cost, and how does the minterm construction trade one against the other?

---

## 17. Reachability Analysis for Hybrid and Continuous Dynamical Systems (Core Topic)

#### Pre-requisites
[[#13. Continuous, Interval, and Nonlinear Constraint Solving (Core Topic)|Topic 13]], [[#14. Abstract Interpretation as a Unifying Theory for Constraint Solver Cooperation (Core Topic)|Topic 14]].

#### Why this topic is important
This is the specialized, geometry-heavy corner of the CSP kernel's brief —
proving absence/presence of bugs for programs whose invariants involve
continuous or hybrid (discrete+continuous) dynamics needs reachable-set
over-approximation techniques (template polyhedra, zonotopes, barrier
certificates) that generalize the octagon/interval domains from Topic 13 to
genuinely non-convex or time-evolving state spaces.

#### Sources to Study
1. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/book-guidelines|Verification and Control of Hybrid Systems: A Symbolic Approach (Tabuada)]]
   - [[Timed-Automata-and-Quotient-Based-Abstraction]]
   - [[Order-Minimal-Structures-and-Definability]]
   - [[Barrier-Certificates-and-Reachable-Set-Computation]]
   - [[Exact-Symbolic-Models-for-Control]]
2. [[74_Reachability_Analysis_Bernstein expansion_2012/book-guidelines|Reachability Analysis for Polynomial Dynamical Systems Using the Bernstein Expansion (Dang & Testylier)]]
   - [[Template-Polyhedra-as-an-Abstract-Domain]]
   - [[The-Bernstein-Expansion-of-Polynomials]]
   - [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients]]
   - [[The-Reachable-Set-Computation-Algorithm]]
3. [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/book-guidelines|Reachability Analysis for Linear Systems with Uncertain Parameters using Polynomial Zonotopes (Huang, Luo, Bak, Sun)]]
   - [[Polynomial-Zonotopes-as-a-Set-Representation]]
   - [[Multi-Affine-Zonotope-Optimization]]

#### Key Concepts and Definitions
1. Template polyhedra (fixed-shape convex over-approximations) combined with the Bernstein expansion of a polynomial map: control points from the Bernstein basis give affine lower/upper bound functions per polynomial component, reducing per-step polynomial optimization to linear programming.
2. Polynomial zonotopes (center plus dependent/independent generators with an exponent structure) as a *non-convex* set representation that preserves dependencies between homogeneous and particular solutions across time steps — where a standard (convex) zonotope would over-approximate via a convex hull and lose precision.
3. Barrier certificates as a direct, Lyapunov-like safety proof (no explicit reachable-set computation needed), found via sum-of-squares search for a polynomial certificate.

#### Relevant Questions
1. Why does using the Bernstein basis (rather than the power basis) let per-step polynomial-image computation reduce to a linear program, and what is lost in tightness compared to solving the polynomial optimization exactly?
2. What specifically does a polynomial zonotope preserve that a standard (linear/convex) zonotope discards, and why does that extra structure matter for accuracy across multiple composed time steps rather than just at a single step?
3. How does a barrier certificate's Lyapunov-like argument let a safety property be proved *without* ever computing an explicit reachable set, and what is the corresponding cost (e.g., restriction to polynomial dynamics, reliance on sum-of-squares solvability)?

---

## 18. Abduction, Craig Interpolation, and Clause/Invariant Generation (Core Topic)

#### Pre-requisites
[[#7. Equality Reasoning, Term Rewriting, and Congruence Closure (Core Topic)|Topic 7]], [[#8. Combining Decision Procedures: Nelson–Oppen, Shostak, and SMT (Core Topic)|Topic 8]].

#### Why this topic is important
This is the closing topic tying the whole area back to the project's
verification goal directly: bi-abduction is precisely the mechanism for
automatically inferring a procedure's Hoare-triple precondition/postcondition
(its "footprint") compositionally, Craig interpolation is the standard route
from a refutation to an inductive invariant, and $\theta$-subsumption /
clause generalization is the same generality-ordering machinery refinement-
type inference needs when generalizing a discovered constraint into a
reusable contract.

#### Sources to Study
1. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/book-guidelines|Compositional Shape Analysis by means of Bi-Abduction (Calcagno, Distefano, O'Hearn, Yang)]]
   - [[Abductive-Inference]]
   - [[Bi-Abduction]]
   - [[Proof-Systems-and-Algorithms-for-Abduction]]
   - [[Quality-and-Ordering-of-Abduction-Solutions]]
   - [[Compositional-Program-Analysis-Algorithms]]
   - [[Soundness-and-Semantic-Models]]
2. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic]]
   - [[Interpolation-and-Definability]]
3. [[09_proof_theory_logic_programming_dale_miller_2025/book-guidelines|Proof Theory and Logic Programming: Computation as Proof Search (Miller)]]
   - [[Specifying-Computations-with-Multisets-and-Automata]]
4. [[76_ThetaSubsumption_article/book-guidelines|Inductive Logic Programming At 30: A New Introduction (Cropper & Dumančić)]]
   - [[Generality-and-Theta-Subsumption]]
   - [[Search-Methods-Over-the-Hypothesis-Space]]
   - [[Representative-ILP-Systems]]

#### Key Concepts and Definitions
1. Bi-abduction: given $\Delta$ and $H$, jointly infer an anti-frame and a frame satisfying $\Delta * ?\mathrm{anti\text{-}frame} \vdash H * ?\mathrm{frame}$ — letting each procedure's precondition/postcondition be inferred independently of its callers, the mechanism behind compositional (whole-codebase-scaling) shape analysis.
2. The Craig interpolation theorem (if $A\Rightarrow C$, an interpolant $B$ exists using only symbols common to $A,C$, with $A\Rightarrow B\Rightarrow C$) as the standard bridge from a resolution/SMT refutation to a candidate inductive loop invariant, and as the technical engine behind both Robinson's joint consistency theorem and Beth's definability theorem.
3. $\theta$-subsumption (Plotkin's syntactic generality order over clauses) as a decidable proxy for the (undecidable) semantic entailment order; least general generalization (LGG) and refinement operators as the concrete generalization/specialization moves a clause-learning search performs — directly analogous to generalizing an inferred constraint into a reusable contract.

#### Relevant Questions
1. Why is bi-abduction framed as an *inverse* to the frame-rule problem, and how does jointly searching for an anti-frame and a frame let heap-manipulating procedure verification become compositional (independent of the call graph) rather than whole-program?
2. Why must the interpolant in Craig's theorem be restricted to symbols common to both $A$ and $C$, and what does this restriction cost in the degenerate cases (e.g. when identity is needed but present in neither $A$ nor $C$ syntactically)?
3. Why is $\theta$-subsumption decidable while semantic clause entailment is not, and what generalization/specialization search does this decidable syntactic proxy actually license — including where it under- or over-generalizes relative to true entailment?

---
