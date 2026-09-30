# Learning Roadmap — Static Analysis & Abstract Interpretation

The `static-analysis` Focus Area supplies the *over-approximating* half of the compiler's verification story: sound abstract semantics that prove the absence of bugs, and automated generation of Hoare-contract / Horn-clause invariants that feed the type-level verification conditions. The sequence starts with concrete semantics and order/fixpoint theory, builds the core abstract-interpretation apparatus (Galois connections, abstract domains, widening), then moves through classical analyses (dataflow, control-flow, effects), relational numeric domains, data-structure and automata-based domains, shape analysis, and backward/predicate-transformer reasoning, and finally to reachability, CEGAR and model checking — where the abstract side hands off to the `sat-smt-csp` counterexample kernel. Cross-area prerequisites are referenced to [[learning-roadmap-type-theory|type-theory]], [[learning-roadmap-automated-reasoning|automated-reasoning]] and the `sat-smt-csp` roadmap rather than restated.

---

## 1. Concrete Program Semantics: Operational Semantics, Transition Systems, and Traces (Core Topic)

#### Pre-requisites
General compiler background. Type-theory roadmap topic 2 (judgments and inductive definitions).

#### Why this topic is important
An abstract interpreter is defined as an approximation of a *concrete* semantics; without a precise collecting/trace semantics there is nothing to be sound about. This is the semantic ground truth for the compiler's analyses and for the Hoare-triple soundness argument. Later: 2–19.

#### Sources to Study
1. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/The-Landscape-of-Program-Analysis-Techniques|The Landscape of Program Analysis Techniques]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Mathematical-Foundations-for-Static-Analysis|Mathematical Foundations for Static Analysis]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Concrete-Semantics-of-Programs|Concrete Semantics of Programs]]
2. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Stateful-and-Operational-Program-Semantics|Stateful and Operational Program Semantics]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Trace-Semantics-of-Programs|Trace Semantics of Programs]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Forward-Reachability-Semantics|Forward Reachability Semantics]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Backward-Accessibility-Semantics|Backward Accessibility Semantics]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Syntax-and-Parsing-of-Programming-Languages|Syntax and Parsing of Programming Languages]]
3. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/The-WHILE-and-FUN-Model-Languages|The WHILE and FUN Model Languages]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/The-Nature-and-Scope-of-Program-Analysis|The Nature and Scope of Program Analysis]]
4. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages]]
   - [[07_practical_foundations_robert_harper_2012/Control-Stacks-and-Abstract-Machines|Control Stacks and Abstract Machines]]
   - [[07_practical_foundations_robert_harper_2012/State-and-Assignables|State and Assignables]]
   - [[07_practical_foundations_robert_harper_2012/Exceptions|Exceptions]]
   - [[07_practical_foundations_robert_harper_2012/Continuations|Continuations]]
5. [[43_Modeling_in_Event-B_JR_Abrial_2010/Discrete-Transition-Systems|Abrial — Discrete Transition Systems]]
6. [[09_proof_theory_logic_programming_dale_miller_2025/Formalizing-Operational-Semantics|Miller — Formalizing Operational Semantics]]
7. [[13_introduction_bisimulation_coinduction_sangiorgi/Processes-and-Labelled-Transition-Systems|Sangiorgi — Processes and Labelled Transition Systems]]

#### Key Concepts and Definitions
1. Small-step/big-step semantics; states, environments, stores; transition systems.
2. Trace semantics and the collecting semantics as the set of reachable states $\mathrm{lfp}\,\lambda X.\,I\cup \mathrm{post}(X)$.
3. Forward (post) vs. backward (pre) accessibility.
4. Non-determinism, exceptions, continuations, abstract machines as concrete semantics for control features.

#### Relevant Questions
1. Why is the collecting semantics the right "most precise" concrete property to abstract, and how does it relate to trace semantics?
2. How do you choose the concrete semantics level (traces, states, relations) so that the desired property is expressible?
3. How does your language's semantics for exceptions/continuations complicate a state-based collecting semantics?

---

## 2. Order Theory and Fixpoints: Posets, Lattices, Knaster–Tarski (Core Topic)

#### Pre-requisites
1. Concrete semantics; basic set theory.

#### Why this topic is important
Every analysis is a least fixpoint of a monotone operator in a complete lattice; termination and precision arguments (Kleene iteration, ascending chains, widening) are lattice arguments. This is also the shared vocabulary with logic-programming fixpoints and Datalog-style analyses. Later: 3–8.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Set-Theory-and-Proof-Techniques-Prerequisites|Set Theory and Proof Techniques Prerequisites]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Order-Theory-of-Posets-Lattices-and-Complete-Lattices|Order Theory of Posets, Lattices and Complete Lattices]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Fixpoint-Theory|Fixpoint Theory]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Deductive-Inductive-and-Coinductive-Definitions|Deductive, Inductive and Coinductive Definitions]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Fixpoint-Abstraction|Fixpoint Abstraction]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Graph-Theory-and-Path-Problems|Graph Theory and Path Problems]]
2. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Partially-Ordered-Sets-and-Complete-Lattices|Partially Ordered Sets and Complete Lattices]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Graphs-and-Regular-Expressions|Graphs and Regular Expressions]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Induction-and-Coinduction|Induction and Coinduction]]
3. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/book-guidelines|Verification and Control of Hybrid Systems]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Lattice-and-Fixed-Point-Theory|Lattice and Fixed-Point Theory]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Fixed-Point-Methods-for-Verification|Fixed-Point Methods for Verification]]
4. [[18_JW_Lloyd_Foundations_logic_programming_1987/Fixpoint-Theory|Lloyd — Fixpoint Theory]]
5. [[27_The_B_Book_Abrial_2005/Fixpoint-Construction-and-Induction|Abrial — Fixpoint Construction and Induction]]
6. [[12_proof_theory_algebra_logic_hiroakira_ono/Lattices-and-Boolean-Algebras|Ono — Lattices and Boolean Algebras]] and [[12_proof_theory_algebra_logic_hiroakira_ono/Residuated-Lattices-and-FL-Algebras|Residuated Lattices and FL-Algebras]] (algebraic view; optional)
7. [[44_Introduction_to_Static_Analysis_Xavier_Rival/Mathematical-Foundations-for-Static-Analysis|Rival — Mathematical Foundations for Static Analysis]]

#### Key Concepts and Definitions
1. Partial orders, lattices, complete lattices, chain conditions (ACC/DCC).
2. Monotone and continuous functions; Knaster–Tarski; Kleene iteration.
3. Least/greatest fixpoints; induction and coinduction as fixpoint principles.
4. Lattice-theoretic view of programs as graphs and path problems.

#### Relevant Questions
1. When does Kleene iteration reach the least fixpoint in finite steps, and what breaks for infinite-height lattices?
2. How do lfp/gfp choices correspond to safety vs. liveness-flavored properties?
3. What is the relationship between Datalog/logic-programming fixpoints and dataflow fixpoints?

---

## 3. Program Properties, Safety/Liveness, and the Limits of Analysis (Core Topic)

#### Pre-requisites
1. Concrete semantics; 2. Fixpoints.

#### Why this topic is important
Tells you which properties an over-approximation can prove (invariance/safety) and why analyses must be sound-but-incomplete (Rice). It fixes what "absence of bugs" means as a collecting-semantics inclusion $\mathrm{lfp} \subseteq \mathcal{S}$, the property the compiler's verification conditions ultimately express.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Undecidability-and-the-Limits-of-Static-Analysis|Undecidability and the Limits of Static Analysis]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Program-Properties-and-Their-Hierarchy|Program Properties and Their Hierarchy]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Safety-and-Liveness-Properties|Safety and Liveness Properties]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Soundness-Completeness-and-the-Practice-of-Static-Analysis|Soundness, Completeness and the Practice of Static Analysis]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/Classes-of-Semantic-Properties-and-Their-Verification|Rival — Classes of Semantic Properties and Their Verification]]
3. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking]]
   - [[67_Principles_of_Model_Checking_2008/Safety-Properties-and-Invariants|Safety Properties and Invariants]]
   - [[67_Principles_of_Model_Checking_2008/Linear-Time-Properties|Linear-Time Properties]]
   - [[67_Principles_of_Model_Checking_2008/Liveness-Properties-and-the-Safety-Liveness-Decomposition|Liveness Properties and the Safety-Liveness Decomposition]]
4. [[19_TLAplus_Lesle_Lamport/book-guidelines|Specifying Systems (TLA+)]]
   - [[19_TLAplus_Lesle_Lamport/Specifying-Safety-Properties|Specifying Safety Properties]]
   - [[19_TLAplus_Lesle_Lamport/Temporal-Logic-and-Liveness|Temporal Logic and Liveness]]
   - [[19_TLAplus_Lesle_Lamport/States-Actions-and-Behaviors|States, Actions, and Behaviors]]
5. [[10_boolos_burgess_computability_logic_2007/Uncomputability|Boolos–Burgess — Uncomputability]]

#### Key Concepts and Definitions
1. Safety (bad thing never happens) vs. liveness; safety–liveness decomposition.
2. Invariants and inductive invariants; the gap between them.
3. Rice's theorem; soundness vs. completeness of analyses; false alarms.
4. Property hierarchy: reachability, trace properties, hyperproperties (information flow).

#### Relevant Questions
1. Why is every safety property refutable by a finite prefix, and why does that matter for counterexample search (the CSP kernel)?
2. What is the difference between an invariant and an *inductive* invariant, and who has to supply the latter?
3. What false-alarm rate is acceptable, and how do false alarms interact with a counterexample-search backend?

---

## 4. Galois Connections and Abstraction (Core Topic)

#### Pre-requisites
2. Fixpoints; 3. Program properties.

#### Why this topic is important
The soundness argument for the whole over-approximating analysis is a Galois-connection argument: abstract fixpoint $\gamma$-covers concrete fixpoint. It also provides the systematic derivation of abstract operators (best abstraction) and the vocabulary for domain refinement and combination — needed by every later topic here and by the CP–AI bridge (topic 14).

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Abstract-Interpretation-as-a-Unifying-Theory|Abstract Interpretation as a Unifying Theory]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Galois-Connections-and-Abstraction|Galois Connections and Abstraction]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Domain-Abstraction-and-the-Best-Abstract-Interpreter|Domain Abstraction and the Best Abstract Interpreter]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Cartesian-Abstraction|Cartesian Abstraction]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Combining-and-Refining-Abstract-Domains|Combining and Refining Abstract Domains]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/The-Generic-Abstract-Interpreter|The Generic Abstract Interpreter]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Abstraction-and-Abstract-Domains|Abstraction and Abstract Domains]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Sound-Abstract-Semantics-and-Analysis-Algorithms|Sound Abstract Semantics and Analysis Algorithms]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Design-Methodology-for-Static-Analyzers|Design Methodology for Static Analyzers]]
3. [[46_Principles_of_Program_Analysis-Springer_2005/Abstract-Interpretation|Nielson et al. — Abstract Interpretation]]
4. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Abstract-Interpretation-Foundations|Pelleau et al. — Abstract Interpretation Foundations]] and [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Abstract-Domains-in-Abstract-Interpretation|Abstract Domains in Abstract Interpretation]]
5. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Abstract-Interpretation|Greitschus — Abstract Interpretation]]
6. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Talbot — Abstract Interpretation as a Foundation for Constraint Solving]]
7. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Sign-Based-Abstractions|Tabuada — Sign-Based Abstractions]] (abstraction by simulation; optional)

#### Additional external sources
- Cousot & Cousot, "Abstract Interpretation: A Unified Lattice Model…" (POPL 1977) and "Systematic Design of Program Analysis Frameworks" (POPL 1979); Nielson–Nielson–Hankin chap. 4 for the "correctness relation" alternative.

#### Key Concepts and Definitions
1. Galois connection $(\alpha,\gamma)$: $\alpha(c)\sqsubseteq a \iff c \subseteq \gamma(a)$; Galois insertion; best abstraction $\alpha\circ f\circ\gamma$.
2. Soundness: $f\circ\gamma \sqsubseteq \gamma\circ f^\#$; fixpoint transfer.
3. Reduced products, Cartesian abstraction, disjunctive completion.
4. Concretization-only abstractions when no $\alpha$ exists (polyhedra).

#### Relevant Questions
1. Why is a $\gamma$-based soundness condition sufficient when no best abstraction exists?
2. What does the reduced product buy, and why is computing it expensive?
3. How does abstract-interpretation soundness compare to type soundness (progress/preservation)? (cf. type-theory topic 2, and Cousot's "Type Systems as Abstract Interpretation")

---

## 5. Dataflow Analysis and Monotone Frameworks (Core Topic)

#### Pre-requisites
2. Fixpoints; 4. Galois connections (light).

#### Why this topic is important
The classical analyses (reaching definitions, available expressions, live variables, constant propagation) are the working examples where lattices and fixpoints become algorithms; monotone frameworks are the generic engine on which a Rust analysis library would be built.

#### Sources to Study
1. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Data-Flow-Analysis|Data Flow Analysis]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Monotone-Frameworks|Monotone Frameworks]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Algorithms-for-Solving-Analysis-Equations|Algorithms for Solving Analysis Equations]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Interprocedural-Data-Flow-Analysis|Interprocedural Data Flow Analysis]]
2. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Dataflow-Analysis-as-Abstract-Interpretation|Dataflow Analysis as Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Chaotic-Iteration-and-Equational-Semantics|Chaotic Iteration and Equational Semantics]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Flow-Sensitivity-and-Insensitivity|Flow Sensitivity and Insensitivity]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Dependency-Analysis-and-Information-Flow|Dependency Analysis and Information Flow]]
3. [[44_Introduction_to_Static_Analysis_Xavier_Rival/Static-Analyzer-Implementation|Rival — Static Analyzer Implementation]]

#### Key Concepts and Definitions
1. Control-flow graph; transfer functions; join (may) vs. meet (must) analyses.
2. Monotone framework $(L,\mathcal F,\mathcal E,\iota)$; distributive frameworks (MOP = MFP).
3. Worklist algorithm; chaotic iteration; iteration ordering.
4. Flow-sensitive vs. flow-insensitive; dependency/information-flow analysis.

#### Relevant Questions
1. When is the maximal-fixed-point solution equal to the meet-over-all-paths solution, and what does non-distributivity cost?
2. How does worklist ordering (reverse post-order, weak topological order) affect convergence speed?
3. Where does flow insensitivity buy scalability at the cost of precision?

---

## 6. Numeric Abstract Domains: Intervals, Octagons, Polyhedra (Core Topic)

#### Pre-requisites
4. Galois connections; 5. Dataflow analysis.

#### Why this topic is important
These are the domains for integer and non-linear invariants (requires/ensures over arithmetic) and the same lattices the CSP kernel propagates over; relational domains (zones, octagons, polyhedra) determine which inequalities a generated Horn-clause invariant can express. Cross-reference: `sat-smt-csp` roadmap (domain propagation).

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Number-Theoretic-and-Interval-Abstract-Domains|Number-Theoretic and Interval Abstract Domains]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Zone-and-Octagon-Relational-Domains|Zone and Octagon Relational Domains]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Linear-Algebra-and-Affine-Static-Analysis|Linear Algebra and Affine Static Analysis]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/The-Octagon-Abstract-Domain|The Octagon Abstract Domain]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Octagonal-Constraint-Solving|Octagonal Constraint Solving]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Unified-Abstract-Domains-for-Constraint-Programming|Unified Abstract Domains for Constraint Programming]]
3. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Location-Merging-Abstraction-and-Convex-Hull|Greitschus — Location Merging, Abstraction and Convex Hull]] (convex polyhedra / Minkowski-sum domain)
4. [[74_Reachability_Analysis_Bernstein expansion_2012/Template-Polyhedra-as-an-Abstract-Domain|Template Polyhedra as an Abstract Domain]]
5. [[44_Introduction_to_Static_Analysis_Xavier_Rival/Abstraction-and-Abstract-Domains|Rival — Abstraction and Abstract Domains]]
6. [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Convex-and-Linear-Relaxation-Techniques|Liberti — Convex and Linear Relaxation Techniques]] (non-linear over-approximation; optional)
7. [[63_Rings_Fields_Vector_Spaces_Sethuraman/book-guidelines|Rings, Fields, and Vector Spaces]] — background for affine/polynomial domains only (tag looks peripheral)

#### Additional external sources
Not covered by an on-hand book — **gap**: Miné, "The Octagon Abstract Domain" (HOSC 2006) and his weakly-relational-domain thesis; Cousot & Halbwachs, "Automatic Discovery of Linear Restraints among Variables" (POPL 1978) for polyhedra; Bagnara et al., PPL / Singh et al., ELINA (numeric-domain implementations); Miné on floating-point domains.

#### Key Concepts and Definitions
1. Interval $[a,b]$; zones (difference constraints $x-y\le c$); octagons ($\pm x\pm y\le c$); convex polyhedra.
2. Closure/normal form (Floyd–Warshall on DBMs) as the enabling operation for precise join/inclusion.
3. Non-relational vs. weakly-relational vs. fully relational cost/precision trade-offs.
4. Template polyhedra and support functions for non-linear expressions.

#### Relevant Questions
1. Why does an octagon need closure before comparison, and what does it cost?
2. Which invariants (e.g. $x \le y+1$, $x+y=n$) are representable in intervals vs. octagons vs. polyhedra?
3. How can a non-linear constraint be soundly linearized to fit a polyhedral domain?

---

## 7. Widening, Narrowing, and Convergence Acceleration (Core Topic)

#### Pre-requisites
2. Fixpoints; 5–6.

#### Why this topic is important
Infinite-height domains (intervals, polyhedra) need widening to terminate; narrowing and threshold/delayed widening recover precision. This is the practical mechanism for *invariant generation* at loops, complementing loop acceleration on the CHC side.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Convergence-Acceleration-by-Widening-and-Narrowing|Cousot — Convergence Acceleration by Widening and Narrowing]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/Sound-Abstract-Semantics-and-Analysis-Algorithms|Rival — Sound Abstract Semantics and Analysis Algorithms]], [[44_Introduction_to_Static_Analysis_Xavier_Rival/Scalability-Techniques-for-Static-Analysis|Scalability Techniques]]
3. [[46_Principles_of_Program_Analysis-Springer_2005/Algorithms-for-Solving-Analysis-Equations|Nielson et al. — Algorithms for Solving Analysis Equations]]
4. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Loop-Acceleration|Frohn — Loop Acceleration]] (exact acceleration as the alternative to widening)
5. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Links-Between-Abstract-Interpretation-and-Constraint-Programming|Links Between Abstract Interpretation and Constraint Programming]]

#### Additional external sources
- Bourdoncle, "Efficient chaotic iteration strategies with widenings" (FMPA 1993); Halbwachs et al. on widening with thresholds/"up-to"; Gopan & Reps on lookahead widening; Gange et al., "Interval analysis and abstract-domain acceleration".

#### Key Concepts and Definitions
1. Widening operator $\nabla$: upper bound + finite ascending chains; narrowing $\Delta$.
2. Widening points (loop heads), thresholds, delayed widening.
3. Acceleration: exact closed-form summarization of loops vs. over-approximation.
4. Decreasing iterations after stabilization.

#### Relevant Questions
1. Why is widening not monotone, and what does that imply for its use in combined analyses?
2. How do thresholds and narrowing recover precision lost at a loop exit?
3. When is loop acceleration preferable to widening for invariant generation?

---

## 8. Type-Based and Constraint-Based Analysis: Control Flow, Effects, and Types as Abstract Interpretation (Core Topic)

#### Pre-requisites
5. Dataflow analysis; type-theory roadmap topics 3 and 13 (typing, inference/constraint generation).

#### Why this topic is important
Effect systems and constraint-based control-flow analysis are the bridge between "types" and "analyses": both produce constraints solved over lattices. This is the theoretical link between your refinement-type inference (constraint generation) and abstract interpretation (constraint solving over abstract domains).

#### Sources to Study
1. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Control Flow Analysis (0-CFA and Constraint-Based Analysis)]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Context-Sensitivity-in-Control-Flow-Analysis|Context Sensitivity in Control Flow Analysis]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Combining-Control-Flow-and-Data-Flow-Analysis|Combining Control Flow and Data Flow Analysis]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Type-and-Effect-Systems|Type and Effect Systems]]
   - [[46_Principles_of_Program_Analysis-Springer_2005/Effects-Beyond-Control-Flow|Effects Beyond Control Flow]]
2. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Type-Systems-as-Abstract-Interpretation|Cousot — Type Systems as Abstract Interpretation]]
3. [[05_ATAPL_Pierce_2004/Effect-Types-and-Region-Based-Memory-Management|ATAPL — Effect Types and Region-Based Memory Management]]
4. [[05_ATAPL_Pierce_2004/Substructural-Type-Systems|ATAPL — Substructural Type Systems]] (ownership)
5. [[07_practical_foundations_robert_harper_2012/Inductive-and-Coinductive-Types|PFPL — Inductive and Coinductive Types]], [[07_practical_foundations_robert_harper_2012/Recursive-Types|Recursive Types]], [[07_practical_foundations_robert_harper_2012/Laziness-and-Polarization|Laziness and Polarization]], [[07_practical_foundations_robert_harper_2012/Parallelism|Parallelism]]

#### Key Concepts and Definitions
1. 0-CFA as constraint solving; context sensitivity ($k$-CFA, call strings).
2. Type-and-effect systems annotate types with sets solved by constraints.
3. Typing as an abstract interpretation with a coarse domain.
4. Region/ownership analysis as an effect discipline.

#### Relevant Questions
1. Where exactly do the "constraint generation" and "constraint solving" phases of 0-CFA line up with those of HM(X)-style refinement inference?
2. In what precise sense is a type system an abstract interpretation, and what does that suggest for combining types with numeric domains?
3. What does context sensitivity cost, and when is it needed?

---

## 9. Backward Analysis, Predicate Transformers, and Invariance Verification (Core Topic)

#### Pre-requisites
3. Properties; 4. Galois connections; automated-reasoning roadmap topic 12 (Hoare logic, wp).

#### Why this topic is important
This is the source of the requires/ensures side: forward analysis proves invariants, backward analysis derives necessary preconditions, and Hoare-logic soundness is proved via fixpoint/predicate-transformer semantics. It connects invariant generation to verification-condition generation and to weakest preconditions.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Relational-and-Predicate-Transformer-Semantics|Relational and Predicate Transformer Semantics]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Fixpoint-Based-Verification-Proof-Methods|Fixpoint-Based Verification Proof Methods]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Invariance-Verification-and-Hoare-Logic|Invariance Verification and Hoare Logic]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/Backward-Analysis|Rival — Backward Analysis]]
3. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book]]
   - [[27_The_B_Book_Abrial_2005/Semantics-of-Generalized-Substitutions|Semantics of Generalized Substitutions]]
   - [[27_The_B_Book_Abrial_2005/Sequencing-Loops-and-Termination-Proofs|Sequencing, Loops and Termination Proofs]]
   - [[27_The_B_Book_Abrial_2005/Refinement-Theory|Refinement Theory]]
4. [[43_Modeling_in_Event-B_JR_Abrial_2010/Proof-Obligation-Rules|Abrial — Event-B Proof Obligation Rules]]
5. [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Hoare-Logic-Foundations|Reynolds — Hoare Logic Foundations]], [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Hoare-Triples-And-Specifications|Hoare Triples and Specifications]], [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Annotated-Specifications|Annotated Specifications]]
6. [[19_TLAplus_Lesle_Lamport/Refinement-and-Implementation|TLA+ — Refinement and Implementation]]

#### Key Concepts and Definitions
1. Predicate transformers $\mathrm{pre}$, $\mathrm{post}$, wp/wlp; forward vs. backward abstract semantics.
2. Inductive-invariant proof rule; Floyd–Hoare as fixpoint proof methods.
3. Necessary vs. sufficient preconditions.
4. Termination via ranking functions/variants.

#### Relevant Questions
1. How is a Hoare triple the same statement as a fixpoint inclusion in a lattice of predicates?
2. What does combining forward invariants and backward preconditions (forward–backward iteration) buy?
3. How do B/Event-B proof obligations relate to inductive-invariant checking?

---

## 10. Abstract Domains for Data Structures: Symbolic Automata, Tree Automata, and Transducers (Core Topic)

#### Pre-requisites
4. Galois connections; 6. Numeric domains; type-theory roadmap topic 15 (symbolic/tree automata).

#### Why this topic is important
The project wants abstract data structures (strings, trees, lists) represented as automata/grammar (DFA-style) domains inside the abstract interpreter and CSP kernel. Symbolic automata and transducers over effective Boolean algebras give a domain whose elements combine regular structure with numeric/predicate labels; tree automata handle inductive data; transducers model string/tree transformations for program analysis.

#### Sources to Study
1. [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/book-guidelines|D'Antoni thesis — Automata and Transducers]]
   - [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/Symbolic-Automata-and-Transducers-over-Infinite-Alphabets|Symbolic Automata and Transducers over Infinite Alphabets]]
   - [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/String-Coder-Verification-with-BEX|String Coder Verification with BEX]]
   - [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/Symbolic-Tree-Transducers-and-the-FAST-Language|Symbolic Tree Transducers and the FAST Language]]
   - [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/Symbolic-Visibly-Pushdown-Automata-for-Hierarchical-Data|Symbolic Visibly Pushdown Automata for Hierarchical Data]]
   - [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/Streaming-Tree-Transducers|Streaming Tree Transducers]]
   - [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/Program-Analysis-Applications-of-Transducer-Based-Languages|Program Analysis Applications of Transducer-Based Languages]]
   - [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/Future-Directions-in-Automata-Based-Programming|Future Directions in Automata-Based Programming]]
2. [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/book-guidelines|The Power of Symbolic Automata and Transducers]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Automata-in-Practice|Symbolic Automata in Practice]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Transducers-in-Practice|Symbolic Transducers in Practice]]
3. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Terms-Trees-and-Contexts|Terms, Trees, and Contexts]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Recognizable-Tree-Languages-and-Finite-Tree-Automata|Recognizable Tree Languages and Finite Tree Automata]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Regular-Tree-Grammars-and-Expressions|Regular Tree Grammars and Expressions]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Tree-Transducers|Tree Transducers]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Automata-with-Constraints|Automata with Constraints]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Weak Monadic Second-Order Logic and Tree Automata]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Applications-of-Tree-Automata-to-Term-Rewriting|Applications of Tree Automata to Term Rewriting]]
4. [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/book-guidelines|Pushdown Automata Inclusion Problems]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Pushdown-Automata-Foundations|Pushdown Automata Foundations]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Visibly-Pushdown-Automata|Visibly Pushdown Automata]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Antichain-Based-Decision-Procedures|Antichain-Based Decision Procedures]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Model-Checking-via-the-Automata-Theoretic-Approach|Model Checking via the Automata-Theoretic Approach]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Superdeterministic-Pushdown-Automata|Superdeterministic Pushdown Automata]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Timed-Automata-and-Their-Pushdown-Extensions|Timed Automata and Their Pushdown Extensions]]
5. [[67_Principles_of_Model_Checking_2008/Automata-over-Finite-and-Infinite-Words|Baier–Katoen — Automata over Finite and Infinite Words]]

#### Additional external sources
- Cousot, Cousot & Logozzo, "A Parametric Segmentation Functor for Fully Automatic and Scalable Array Content Analysis" (POPL 2011); Christodorescu/Minamide on string analysis with regular languages; D'Antoni & Veanes, "The Power of Symbolic Automata and Transducers" (CAV 2017) — the on-hand short version.

#### Key Concepts and Definitions
1. Symbolic finite automata: transitions labelled by predicates from an effective Boolean algebra; minterms for determinization.
2. Regular tree languages; bottom-up tree automata as abstractions of inductive data.
3. Visibly pushdown languages: closure under Boolean operations and determinizability.
4. Antichain inclusion algorithms as domain ordering tests.
5. Widening for automata domains: state merging / $k$-bounded equivalence quotients.

#### Relevant Questions
1. What is the abstract-domain lattice for a set of strings/trees represented by automata, and what serves as its widening?
2. Why do symbolic labels (predicates) rather than explicit alphabets matter for a numeric-valued data structure?
3. Which decision problems (inclusion, emptiness) give the abstract order and join, and what are their complexities?

---

## 11. Shape Analysis, Separation Logic, and Bi-Abduction (Core Topic)

#### Pre-requisites
4. Galois connections; 9. Hoare logic; automated-reasoning roadmap topics 12–13 (separation logic and abduction).

#### Why this topic is important
Heap-manipulating programs need domains beyond numeric values; separation-logic-based shape analysis with bi-abduction shows how compositional (bottom-up) analysis can *infer* pre/postconditions — invariant generation for contracts. Optional for a first functional/refinement-typed compiler, essential for a Rust-like ownership language.

#### Sources to Study
1. [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/book-guidelines|An Introduction to Separation Logic]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/The-Separation-Logic-Assertion-Language|The Separation Logic Assertion Language]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Semantics-Of-Assertions|Semantics of Assertions]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Special-Classes-Of-Assertions|Special Classes of Assertions]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/The-Frame-Rule-and-Local-Reasoning|The Frame Rule and Local Reasoning]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Inference-Rules-for-Heap-Manipulating-Commands|Inference Rules for Heap-Manipulating Commands]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Abstract-Data-Types-Via-Inductive-Predicates|Abstract Data Types via Inductive Predicates]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Trees-Dags-And-Sharing|Trees, Dags, and Sharing]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Doubly-Linked-and-Xor-Linked-List-Segments|Doubly-Linked and Xor-Linked List Segments]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Procedures-And-Hypothetical-Specifications|Procedures and Hypothetical Specifications]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Shared-Variable-Concurrency|Shared-Variable Concurrency]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/The-Iterated-Separating-Conjunction|The Iterated Separating Conjunction]]
2. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/book-guidelines|Compositional Shape Analysis by means of Bi-Abduction]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Separation-Logic-Foundations|Separation Logic Foundations]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Compositional-Program-Analysis-Algorithms|Compositional Program Analysis Algorithms]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Soundness-and-Semantic-Models|Soundness and Semantic Models]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/The-Abductor-Tool-and-Case-Studies|The Abductor Tool and Case Studies]]
3. [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/book-guidelines|Interprocedural Shape Analysis Using Separation Logic]]
   - [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Separation-Logic-for-Shape-Analysis|Separation Logic for Shape Analysis]]
   - [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Relational-Shape-Abstraction-Transformation-Domain|Relational Shape Abstraction (Transformation Domain)]]
   - [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Intraprocedural-Transformation-Analysis|Intraprocedural Transformation Analysis]]
   - [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Abstract-Intersection-and-Composition-Algorithms|Abstract Intersection and Composition Algorithms]]
   - [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Interprocedural-Analysis-via-Procedure-Summaries|Interprocedural Analysis via Procedure Summaries]]
   - [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Modular-Interprocedural-Call-Analysis|Modular Interprocedural Call Analysis]]
   - [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Experimental-Evaluation-of-Summary-Based-Shape-Analysis|Experimental Evaluation]]
4. [[46_Principles_of_Program_Analysis-Springer_2005/Shape-Analysis|Nielson et al. — Shape Analysis]]
5. [[05_ATAPL_Pierce_2004/Substructural-Type-Systems|ATAPL — Substructural Type Systems]] (linear/ownership view)

#### Key Concepts and Definitions
1. Separating conjunction, frame rule; inductive predicates for lists/trees (list segments).
2. Abduction $A * ?M \vdash G$ and bi-abduction (frame + anti-frame).
3. Compositional summaries and procedure specifications.
4. Transformation (relational) domain for interprocedural summaries; abstract composition.

#### Relevant Questions
1. How does the frame rule make an analysis compositional, and what is the soundness side condition?
2. What makes bi-abduction infer specs bottom-up without a caller context?
3. What is lost when summaries are relational versus purely input-output shape specs?

---

## 12. Pointer, Points-To, and Datalog-Style Analyses; Equality-Based Analysis (Core Topic)

#### Pre-requisites
5. Dataflow analysis; automated-reasoning roadmap topics 7, 9 (unification, e-graphs).

#### Why this topic is important
Points-to analysis via unification (Steensgaard) and via Datalog/Horn clauses shows how logic-programming machinery *is* a static analyzer, connecting Horn-clause invariant generation to the analysis engine. e-graph-based analyses extend this with equality reasoning.

#### Sources to Study
1. [[71_Unifying_Datalog_and_Equality_Saturation/book-guidelines|Better Together: Unifying Datalog and Equality Saturation]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Case-Study-Unification-Based-Points-to-Analysis|Case Study: Unification-Based Points-to Analysis]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Case-Study-Sound-Floating-Point-Rewriting|Case Study: Sound Floating-Point Rewriting]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Incremental-Evaluation|Incremental Evaluation]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Fixpoint-Reasoning-Frameworks|Fixpoint Reasoning Frameworks]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Query-Evaluation-and-E-Matching|Query Evaluation and E-Matching]]
2. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Points-To-Analysis|Cousot — Points-To Analysis]]
3. [[09_proof_theory_logic_programming_dale_miller_2025/Collection-Analysis-for-Horn-Clauses|Miller — Collection Analysis for Horn Clauses]]
4. [[18_JW_Lloyd_Foundations_logic_programming_1987/Declarative-Semantics-of-Definite-Programs|Lloyd — Declarative Semantics of Definite Programs]] and [[18_JW_Lloyd_Foundations_logic_programming_1987/Declarative-Error-Diagnosis|Declarative Error Diagnosis]]
5. [[39_Equality-Saturation-RossThesis2012/book-guidelines|Equality Saturation]]
   - [[39_Equality-Saturation-RossThesis2012/Program-Expression-Graphs-(PEGs)|Program Expression Graphs (PEGs)]]
   - [[39_Equality-Saturation-RossThesis2012/Equality-Saturation|Equality Saturation]]
   - [[39_Equality-Saturation-RossThesis2012/Representing-Effects-in-PEGs|Representing Effects in PEGs]]
   - [[39_Equality-Saturation-RossThesis2012/Converting-Between-Imperative-Code-and-PEGs|Converting Between Imperative Code and PEGs]]
   - [[39_Equality-Saturation-RossThesis2012/Loop-and-Branch-Optimizations-Discovered-by-Saturation|Loop and Branch Optimizations Discovered by Saturation]]
   - [[39_Equality-Saturation-RossThesis2012/Translation-Validation|Translation Validation]]

#### Additional external sources
- Andersen (1994) & Steensgaard (POPL 1996) points-to analyses; Whaley & Lam, "Cloning-Based Context-Sensitive Pointer Alias Analysis Using BDDs" (PLDI 2004); Soufflé documentation (Datalog for program analysis).

#### Key Concepts and Definitions
1. Andersen (subset-based, inclusion constraints) vs. Steensgaard (unification-based) points-to.
2. Datalog rules as monotone analysis equations; semi-naive evaluation.
3. e-graphs with lattice-valued analyses ("e-class analysis").
4. Program-expression graphs and translation validation.

#### Relevant Questions
1. Why does unification-based points-to analysis run in near-linear time, and what precision does it give up?
2. How does an e-graph with a merge function subsume both union-find and lattice joins?
3. When should analyses be written in Datalog rather than as a hand-coded worklist in Rust?

---

## 13. Interprocedural, Modular Analysis, and Scalable Analyzer Design (Core Topic)

#### Pre-requisites
5. Dataflow; 6–7; 11 (for summaries).

#### Why this topic is important
The analyzer engine must be modular (function summaries ↔ dependent-type function contracts) and scalable; design methodology (choose domain, prove soundness, then engineer) is the process for every analysis in the compiler.

#### Sources to Study
1. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Design-Methodology-for-Static-Analyzers|Design Methodology for Static Analyzers]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Scalability-Techniques-for-Static-Analysis|Scalability Techniques for Static Analysis]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Static-Analyzer-Implementation|Static Analyzer Implementation]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Practical-Use-and-Deployment-of-Static-Analysis-Tools|Practical Use and Deployment of Static Analysis Tools]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Static-Analysis-for-Advanced-Programming-Language-Features|Static Analysis for Advanced Programming Language Features]]
   - [[44_Introduction_to_Static_Analysis_Xavier_Rival/Specialized-Static-Analysis-Frameworks|Specialized Static Analysis Frameworks]]
2. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Engineering-and-Adoption-of-Static-Analysis-Tools|Cousot — Engineering and Adoption of Static Analysis Tools]]
3. [[46_Principles_of_Program_Analysis-Springer_2005/Interprocedural-Data-Flow-Analysis|Nielson et al. — Interprocedural Data Flow Analysis]] and [[46_Principles_of_Program_Analysis-Springer_2005/Context-Sensitivity-in-Control-Flow-Analysis|Context Sensitivity]]
4. [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/Modular-Interprocedural-Call-Analysis|Illous–Rival — Modular Interprocedural Call Analysis]]
5. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Compositional-Program-Analysis-Algorithms|Calcagno et al. — Compositional Program Analysis Algorithms]]

#### Key Concepts and Definitions
1. Context-insensitive vs. call-string vs. functional (summary) approaches.
2. Top-down vs. bottom-up interprocedural analysis.
3. Design method: concrete semantics → abstraction → abstract transfer → iteration strategy.
4. Scalability: packing, sparse analysis, modularity.

#### Relevant Questions
1. How do function summaries relate to refinement-typed function signatures (dependent function contracts)?
2. When does bottom-up analysis beat top-down, and what does it need (bi-abduction)?
3. Which soundness assumptions leak when analyzing open programs/libraries?

---

## 14. Abstract Domains Meet Constraint Programming: Propagation and Solver Cooperation (Core Topic)

#### Pre-requisites
4. Galois connections; 6. Numeric domains. Cross-reference `sat-smt-csp` roadmap (CSP fundamentals, domain propagation).

#### Why this topic is important
The CSP kernel must share lattices/propagators with the abstract interpreter: abstract interpretation over-approximates to prove absence, CP search finds concrete counterexamples. The AI-as-foundation view of constraint solving unifies propagators, abstract domains, and modular solver composition.

#### Sources to Study
1. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Links-Between-Abstract-Interpretation-and-Constraint-Programming|Links Between Abstract Interpretation and Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Abstract-Interpretation-Reformulation-of-Constraint-Programming|Abstract Interpretation Reformulation of Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Consistency-and-Propagation-in-Constraint-Programming|Consistency and Propagation in Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Constraint-Satisfaction-Problem-Foundations|Constraint Satisfaction Problem Foundations]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/Exploration-and-Search-in-Constraint-Programming|Exploration and Search in Constraint Programming]]
   - [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/The-AbSolute-Solver|The AbSolute Solver]]
2. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/book-guidelines|Modular Constraint Solver Cooperation via Abstract Interpretation]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Abstract-Domains-For-Constraint-Programming|Abstract Domains for Constraint Programming]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Domain-Transformers|Domain Transformers]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Interval-Propagators-Completion-IPC|Interval Propagators Completion (IPC)]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Shared-Product-and-Modular-Composition|Shared Product and Modular Composition]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Delayed-Product-DP|Delayed Product (DP)]]
   - [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Relation-to-Other-Cooperation-Frameworks|Relation to Other Cooperation Frameworks]]
3. [[42_Constraint Propagation_Guido_Tack_PhD_2009/book-guidelines|Constraint Propagation — Models, Techniques, Implementation (Tack)]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Propagation-Strength-and-Domain-Approximations|Propagation Strength and Domain Approximations]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/The-Denotational-and-Operational-Model-of-Constraint-Propagation|The Denotational and Operational Model of Constraint Propagation]]
   - [[42_Constraint Propagation_Guido_Tack_PhD_2009/Range-Iterators-for-Set-Valued-Domain-Operations|Range Iterators for Set-Valued Domain Operations]]
4. [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/Spatial-Branch-and-Bound-sBB-Algorithms|Liberti — Spatial Branch-and-Bound Algorithms]] (non-linear global search; optional)

#### Key Concepts and Definitions
1. Propagator = abstract transformer (sound, monotone, contracting); propagation = chaotic iteration.
2. Domain approximations of sets/integers; propagation strength.
3. Domain products: shared (reduced) vs. delayed product for solver cooperation.
4. Search as disjunctive completion refinement (branching).

#### Relevant Questions
1. In what sense is a propagator an abstract transformer, and what does its fixpoint compute?
2. What does a reduced product between an interval solver and an octagon solver require of the propagators?
3. How can the abstract interpreter's invariants prune the CSP counterexample search (and vice versa)?

---

## 15. Reachability Analysis for Continuous and Hybrid Systems (Optional / Extension)

#### Pre-requisites
2. Fixpoints; 6. Numeric domains (polyhedra); basic linear algebra and real analysis.

#### Why this topic is important
Reachable-set computation with set representations (zonotopes, polynomial zonotopes, template polyhedra) is abstract interpretation for dynamical systems and provides the non-linear numeric machinery (Bernstein expansion, support functions) relevant to non-linear constraint domains. It is off the critical path for a discrete-program compiler but instructive for non-linear bounds.

#### Sources to Study
1. [[74_Reachability_Analysis_Bernstein expansion_2012/book-guidelines|Reachability Analysis for Hybrid and Polynomial Dynamical Systems (Bernstein expansion)]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Reachability-Analysis-for-Hybrid-and-Polynomial-Dynamical-Systems|Reachability Analysis for Hybrid and Polynomial Dynamical Systems]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/The-Bernstein-Expansion-of-Polynomials|The Bernstein Expansion of Polynomials]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Computing Affine Bound Functions from Bernstein Coefficients]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Template-Polyhedra-as-an-Abstract-Domain|Template Polyhedra as an Abstract Domain]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/The-Reachable-Set-Computation-Algorithm|The Reachable Set Computation Algorithm]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Approximation-Error-and-Computational-Complexity|Approximation Error and Computational Complexity]]
   - [[74_Reachability_Analysis_Bernstein expansion_2012/Related-Approaches-to-Nonlinear-Reachability|Related Approaches to Nonlinear Reachability]]
2. [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/book-guidelines|Reachability Analysis of Linear Systems with Uncertain Parameters (Polynomial Zonotopes)]]
   - [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/Polynomial-Zonotopes-as-a-Set-Representation|Polynomial Zonotopes as a Set Representation]]
   - [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/Dependency-Preserving-Set-Operations|Dependency-Preserving Set Operations]]
   - [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/Matrix-Exponential-Propagation|Matrix Exponential Propagation]]
   - [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/Reachability-Analysis-for-Linear-Systems-with-Uncertain-Parameters|Reachability Analysis for Linear Systems with Uncertain Parameters]]
   - [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/Extensions-of-the-Core-Reachability-Algorithm|Extensions of the Core Reachability Algorithm]]
   - [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/Multi-Affine-Zonotope-Optimization|Multi-Affine Zonotope Optimization]]
3. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/book-guidelines|Verification and Control of Hybrid Systems]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Hybrid-Dynamical-Systems|Hybrid Dynamical Systems]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Barrier-Certificates-and-Reachable-Set-Computation|Barrier Certificates and Reachable Set Computation]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Exact-System-Relationships|Exact System Relationships]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Approximate-System-Relationships|Approximate System Relationships]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Systems-as-the-Common-Mathematical-Model|Systems as the Common Mathematical Model]]
   - [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Verification-and-Control-Problems|Verification and Control Problems]]
4. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|Minkowski-Sum Domain Dissertation]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Hybrid-Automata-and-Their-Semantics|Hybrid Automata and Their Semantics]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Flowpipe-Approximation-and-Support-Functions|Flowpipe Approximation and Support Functions]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Assume-Guarantee-Reasoning-for-Hybrid-Systems|Assume-Guarantee Reasoning for Hybrid Systems]]
5. [[66_Reformulation_ConvexRelaxation_Global_Optimization_Segio_Liberty_2004/book-guidelines|Reformulation and Convex Relaxation in Global Optimization]]
6. [[59_Grimstad_Global_Spline_Optimization/book-guidelines|Global Spline Optimization]] — tagged for this area, but its subject (subsea production systems) is application-specific; use only its B-spline/global-optimization chapters if needed.

#### Additional external sources
- Girard, "Reachability of Uncertain Linear Systems Using Zonotopes" (HSCC 2005); Althoff's CORA tool papers; Frehse's SpaceEx (CAV 2011).

#### Key Concepts and Definitions
1. Reachable set, flowpipe; set representations (zonotope, polynomial zonotope, template polyhedron, support function).
2. Bernstein expansion for polynomial range bounds.
3. Over-approximation error control; wrapping effect; dependency preservation.
4. Barrier certificates as inductive invariants for continuous dynamics.

#### Relevant Questions
1. How does a Bernstein-coefficient bound compare to interval arithmetic on a polynomial, and to a convex relaxation?
2. Why do zonotope-based representations avoid the wrapping effect?
3. How does a barrier certificate correspond to an inductive invariant in the discrete setting?

---

## 16. CEGAR, Path Programs, and Refinement of Abstractions (Core Topic)

#### Pre-requisites
4. Galois connections; 9. Invariance verification; automated-reasoning roadmap topics 14–15 (interpolation, SAT proofs); `sat-smt-csp` roadmap (SMT-based feasibility).

#### Why this topic is important
CEGAR is the handshake between the two verification halves: abstraction proves absence; a counterexample from the concrete/CSP side either confirms a bug or is spurious and drives refinement of the abstract domain (via interpolants or path programs). This closes the loop between topics 6–7 and the counterexample kernel.

#### Sources to Study
1. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|Minkowski-Sum Domain Dissertation]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Counterexample-Guided Abstraction Refinement (CEGAR)]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Elimination-of-Spurious-Transitions|Elimination of Spurious Transitions]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/Path-Programs-and-Loop-Invariants|Path Programs and Loop Invariants]]
   - [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/ULTIMATE-and-ULTIMATE-TAIPAN|ULTIMATE and ULTIMATE TAIPAN]]
2. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/book-guidelines|Acceleration Driven Clause Learning for CHC]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Loop-Acceleration|Loop Acceleration]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Related-Approaches-to-CHC-SAT-and-Loop-Summarization|Related Approaches to CHC-SAT and Loop Summarization]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Constrained-Horn-Clauses-(CHCs)|Constrained Horn Clauses (CHCs)]]
3. [[25_Handbook_Satisfiability_Armin_Biere_2021/Bounded-Model-Checking-and-Formal-Verification|Handbook of Satisfiability — Bounded Model Checking and Formal Verification]]
4. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Model-Checking-as-Abstract-Interpretation|Cousot — Model Checking as Abstract Interpretation]]
5. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Approximate-Symbolic-Models-for-Verification-and-Control|Tabuada — Approximate Symbolic Models for Verification and Control]] (abstraction refinement by simulation)
6. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Abductive-Inference|Calcagno et al. — Abductive Inference]] (abduction for missing preconditions)

#### Additional external sources
Not covered by an on-hand book — **gap**: Clarke et al., "Counterexample-Guided Abstraction Refinement" (CAV 2000); Henzinger et al., "Lazy Abstraction" (POPL 2002) and "Abstractions from Proofs" (POPL 2004); McMillan, "Lazy Abstraction with Interpolants" (CAV 2006); Bjørner, Gurfinkel et al., "Horn Clause Solvers for Program Verification"; Beyer & Keremoglu, CPAchecker; Heizmann et al., "Software Model Checking for People Who Love Automata" (CAV 2013).

#### Key Concepts and Definitions
1. Abstract counterexample; spurious counterexample; refinement loop.
2. Path programs as slices of the CFG focusing infeasibility.
3. Interpolants / predicate discovery for refining predicate abstraction; lazy abstraction.
4. Constrained Horn clauses as a uniform verification-condition format; loop acceleration in CHC solving.

#### Relevant Questions
1. How is a spurious counterexample detected and what information does the refinement extract (interpolants, path invariants)?
2. What does a path-program view buy over unrolling for loop-heavy counterexamples?
3. How would the CSP kernel plug in as the feasibility oracle and abstraction refiner?

---

## 17. Model Checking, Automata-Theoretic Verification, and Temporal Properties (Optional / Extension)

#### Pre-requisites
3. Program properties; 10. Automata domains; 16. CEGAR.

#### Why this topic is important
Model checking is the "reachability analysis" cousin of abstract interpretation: explicit/symbolic (BDD, SAT) state-space exploration with temporal properties. It explains state-space explosion, partial-order reduction and symbolic representation — techniques you might borrow for the counterexample kernel.

#### Sources to Study
1. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking]]
   - [[67_Principles_of_Model_Checking_2008/Model-Checking-Fundamentals|Model Checking Fundamentals]]
   - [[67_Principles_of_Model_Checking_2008/Transition-Systems-as-System-Models|Transition Systems as System Models]]
   - [[67_Principles_of_Model_Checking_2008/State-Space-Explosion|State-Space Explosion]]
   - [[67_Principles_of_Model_Checking_2008/Automata-Based-Verification-of-Properties|Automata-Based Verification of Properties]]
   - [[67_Principles_of_Model_Checking_2008/Automata-Based-LTL-Model-Checking|Automata-Based LTL Model Checking]]
   - [[67_Principles_of_Model_Checking_2008/Computation-Tree-Logic|Computation Tree Logic]]
   - [[67_Principles_of_Model_Checking_2008/CTL-Model-Checking|CTL Model Checking]]
   - [[67_Principles_of_Model_Checking_2008/Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Symbolic Model Checking with Binary Decision Diagrams]]
   - [[67_Principles_of_Model_Checking_2008/Partial-Order-Reduction|Partial Order Reduction]]
   - [[67_Principles_of_Model_Checking_2008/Partition-Refinement-Algorithms|Partition Refinement Algorithms]]
   - [[67_Principles_of_Model_Checking_2008/Real-Time-Systems-and-Timed-Automata|Real-Time Systems and Timed Automata]]
2. [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/book-guidelines|Pushdown Automata Inclusion Problems]] — automata-theoretic model checking and timed pushdown automata
3. [[19_TLAplus_Lesle_Lamport/book-guidelines|Specifying Systems (TLA+)]]
   - [[19_TLAplus_Lesle_Lamport/The-TLA+-Tools|The TLA+ Tools]]
   - [[19_TLAplus_Lesle_Lamport/The-Syntax-of-TLA+|The Syntax of TLA+]]
4. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Model-Checking-as-Abstract-Interpretation|Cousot — Model Checking as Abstract Interpretation]]
5. [[25_Handbook_Satisfiability_Armin_Biere_2021/Bounded-Model-Checking-and-Formal-Verification|Handbook of Satisfiability — Bounded Model Checking]]
6. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/Timed-Automata-and-Quotient-Based-Abstraction|Tabuada — Timed Automata and Quotient-Based Abstraction]]

#### Key Concepts and Definitions
1. Kripke structures/transition systems; LTL/CTL semantics; Büchi automata product construction.
2. Symbolic model checking with BDDs/SAT (BMC, $k$-induction).
3. State-space explosion mitigations: partial-order reduction, symmetry, abstraction, bisimulation quotient.
4. Timed automata and regions (optional).

#### Relevant Questions
1. How does bounded model checking relate to CSP-based counterexample search for safety properties?
2. Which model-checking reductions (partial order, symmetry) transfer to a symbolic-execution-style search?
3. Is model checking a special case of abstract interpretation, and what does that view buy?

---

## 18. Refinement, Simulation, and Behavioural Equivalence (Optional / Extension)

#### Pre-requisites
1. Concrete semantics; 9. Predicate transformers.

#### Why this topic is important
Abstraction soundness is a simulation relation; refinement (data refinement, behavioural refinement) is the stepwise development discipline behind B/Event-B and the notion of "implementation satisfies contract." Bisimulation provides the equivalence notions used to argue analysis/compilation preserves behaviour.

#### Sources to Study
1. [[23_Refinement_Semantics_Derrick_Boiten_2018/book-guidelines|Refinement: Semantics, Languages and Applications]]
   - [[23_Refinement_Semantics_Derrick_Boiten_2018/State-Based-and-Relational-Models-of-Refinement|State-Based and Relational Models of Refinement]]
   - [[23_Refinement_Semantics_Derrick_Boiten_2018/Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency|Refinement as Reduction of Non-Determinism and Behavioural Consistency]]
   - [[23_Refinement_Semantics_Derrick_Boiten_2018/Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement|Labelled Transition Systems and the Spectrum of Observational Refinement]]
   - [[23_Refinement_Semantics_Derrick_Boiten_2018/Automata-and-Simulations|Automata and Simulations]]
   - [[23_Refinement_Semantics_Derrick_Boiten_2018/State-Based-Specification-Languages-Z-and-B|State-Based Specification Languages: Z and B]]
   - [[23_Refinement_Semantics_Derrick_Boiten_2018/Event-B-and-Abstract-State-Machines-ASM|Event-B and Abstract State Machines (ASM)]]
2. [[13_introduction_bisimulation_coinduction_sangiorgi/book-guidelines|Introduction to Bisimulation and Coinduction]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/Alternative-Notions-of-Equality-on-Behaviour|Alternative Notions of Equality on Behaviour]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/Weak-Bisimulation-and-Internal-Activity|Weak Bisimulation and Internal Activity]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/Testing-and-Trace-Based-Behavioural-Equivalences|Testing and Trace-Based Behavioural Equivalences]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/Refinements-of-Simulation|Refinements of Simulation]]
3. [[43_Modeling_in_Event-B_JR_Abrial_2010/book-guidelines|Modeling in Event-B]]
   - [[43_Modeling_in_Event-B_JR_Abrial_2010/Refinement-Theory|Refinement Theory]]
   - [[43_Modeling_in_Event-B_JR_Abrial_2010/The-Event-B-Notation|The Event-B Notation]]
   - [[43_Modeling_in_Event-B_JR_Abrial_2010/Formal-Methods-and-the-Modeling-Philosophy|Formal Methods and the Modeling Philosophy]]
   - [[43_Modeling_in_Event-B_JR_Abrial_2010/Design-Patterns-for-Reactive-Controllers|Design Patterns for Reactive Controllers]]
4. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book]] — Abstract Machines, Composing Large Specifications, Implementation and Modular Architecture, Case Studies (see [[27_The_B_Book_Abrial_2005/Abstract-Machines-and-the-Generalized-Substitution-Language|Abstract Machines and the Generalized Substitution Language]], [[27_The_B_Book_Abrial_2005/Composing-Large-Specifications|Composing Large Specifications]], [[27_The_B_Book_Abrial_2005/Implementation-and-Modular-Architecture|Implementation and Modular Architecture]])
5. [[19_TLAplus_Lesle_Lamport/Refinement-and-Implementation|TLA+ — Refinement and Implementation]]

#### Key Concepts and Definitions
1. Simulation and bisimulation; forward vs. backward simulation; data refinement (simulation between abstract and concrete state).
2. Refinement as reduction of non-determinism; observational refinement (traces/failures/divergences).
3. Abstract machines (B) and events (Event-B): invariants, refinement proof obligations.
4. Coinduction as the proof technique for bisimilarity.

#### Relevant Questions
1. Why does an abstract interpretation's soundness resemble a simulation of the concrete system by the abstract one?
2. When is forward simulation complete for data refinement and when are backward simulations needed?
3. What proof obligations follow from refining an abstract machine?

---

## 19. Soundness Proofs, Certified Analysis, and Proof-Carrying Code (Optional / Extension)

#### Pre-requisites
4. Galois connections; type-theory roadmap topics 2, 5, 7 (soundness, kernel); automated-reasoning roadmap topic 17 (certificates).

#### Why this topic is important
The soundness argument for over-approximating passes is what lets the compiler trust its analyses without putting them in the trusted kernel: either prove the analyzer sound (once), or check per-run certificates (PCC, translation validation). This topic ties `static-analysis` back to the trusted-kernel architecture.

#### Sources to Study
1. [[44_Introduction_to_Static_Analysis_Xavier_Rival/Foundational-Soundness-Proofs|Rival — Foundational Soundness Proofs]]
2. [[05_ATAPL_Pierce_2004/book-guidelines|Advanced Topics in Types and Programming Languages]]
   - [[05_ATAPL_Pierce_2004/Proof-Carrying-Code|Proof-Carrying Code]]
   - [[05_ATAPL_Pierce_2004/Typed-Assembly-Language|Typed Assembly Language]]
3. [[39_Equality-Saturation-RossThesis2012/Translation-Validation|Ross — Translation Validation]]
4. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Soundness-Completeness-and-the-Practice-of-Static-Analysis|Cousot — Soundness, Completeness and the Practice of Static Analysis]]
5. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Soundness-and-Semantic-Models|Calcagno et al. — Soundness and Semantic Models]]
6. [[46_Principles_of_Program_Analysis-Springer_2005/Type-and-Effect-Systems|Nielson et al. — Type and Effect Systems]] (soundness via subject reduction)

#### Additional external sources
- Necula, "Proof-Carrying Code" (POPL 1997); Jourdan et al., "A Formally-Verified C Static Analyzer" (POPL 2015, Verasco); Pichardie's work on certified abstract interpretation in Coq.

#### Key Concepts and Definitions
1. Analyzer soundness as a theorem (mechanized) vs. certificate checking.
2. Proof-carrying code: producer ships a proof, consumer checks with a small checker.
3. Translation validation: check each compilation/optimization instance.
4. Type-based certificates (TAL) vs. logic-based certificates (PCC).

#### Relevant Questions
1. What do you gain by verifying the analyzer once versus validating each run's result?
2. Which parts of an abstract interpreter must be in the trusted computing base if results are certified?
3. How does the soundness proof for an abstract domain decompose (operator-by-operator vs. whole-analyzer)?

---

## Summary of gaps and pruning notes

Where on-hand material is thin, the topics above carry "Additional external sources": **6. numeric domains** (Miné, Cousot–Halbwachs, PPL/ELINA), **7. widening** (Bourdoncle, thresholds), **12. points-to/Datalog analyses** (Andersen, Steensgaard, Soufflé), **16. CEGAR/lazy abstraction/Horn solvers** (Clarke et al., McMillan, Bjørner–Gurfinkel), **19. certified analysis** (Verasco, PCC), and **10** (array/string/segmentation abstractions). Session-type books ([[22_wadler_2012_propositions_as_sessions/book-guidelines|Propositions as Sessions]], [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/book-guidelines|Domain-Aware Session Types]]) and the concurrency chapters of PFPL carry a stray `static-analysis` tag: they are treated as type-theory/automated-reasoning material and omitted here.
