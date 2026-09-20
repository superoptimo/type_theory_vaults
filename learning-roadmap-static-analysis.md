# Learning Roadmap — Static Analysis & Abstract Interpretation

Static Analysis is where the compiler's soundness argument actually gets made:
abstract interpretation is the mathematical theory that lets an
over-approximating analysis prove the *absence* of bugs (invariant
generation, Hoare/Horn-clause contracts), the dual of what the project's CSP
kernel does by searching for concrete counterexamples. This sequence follows
Cousot's own calculational method — trace semantics → order theory →
Galois connections → fixpoint abstraction → the generic abstract
interpreter → specific abstract domains → widening/narrowing → derived
verification methods (Hoare logic, dataflow analysis, model checking, type
systems) — as its spine, since one source (*Principles of Abstract
Interpretation*) already covers most of the area coherently and in the right
order. It then branches into the applied and adjacent material the
compiler's abstract-interpretation pass actually needs: shape/separation-
logic analysis, CEGAR, constraint propagation, model checking and process
equivalence, formal refinement, hybrid-system reachability, symbolic
automata, and two more specialized closing threads (session-typed process
calculi, equality saturation) that connect this area back to
`automated-reasoning`, `sat-smt-csp`, and `type-theory`.

---

## 1. Program Properties, Trace Semantics, and the Limits of Static Analysis (Core Topic)

#### Pre-requisites
None — this is the entry point of the whole Focus Area.

#### Why this topic is important
This sets the vocabulary (trace semantics, collecting semantics, property
hierarchy) and the hard limit (Rice's theorem) that every later abstraction
in this roadmap has to work within: no sound analysis can be both precise
and always-terminating, which is exactly why the project needs abstract
domains and widening (Topics 8–11), not just "a better algorithm."

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Abstract-Interpretation-as-a-Unifying-Theory]]
   - [[Trace-Semantics-of-Programs]]
   - [[Program-Properties-and-Their-Hierarchy]]
   - [[Undecidability-and-the-Limits-of-Static-Analysis]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[The-Landscape-of-Program-Analysis-Techniques]]

#### Key Concepts and Definitions
1. Stateless structural prefix trace semantics and the maximal finite+infinite trace semantics as a limit of prefixes.
2. The property hierarchy: trace property (strictly less expressive) vs. semantic property vs. invariance/reachability property, each a further Galois abstraction of the last.
3. Rice's theorem: every nontrivial extensional semantic property is undecidable, so any sound algorithm must fail (terminate without an answer, or answer imprecisely) on infinitely many inputs.

#### Relevant Questions
1. Why is a trace property strictly less expressive than a semantic property, even though both describe "the same" executions?
2. How does Rice's theorem's proof reduce to the halting problem, and what does the reduction imply about static-analyzer design (a forced choice between termination and precision, not a fixable gap)?
3. Why must decidable/testing/model-checking/static-analysis/bug-finding techniques each trade soundness and completeness differently, given the same underlying undecidability?

---

## 2. Order Theory, Lattices, and Fixpoint Theory (Core Topic)

#### Pre-requisites
[[#1. Program Properties, Trace Semantics, and the Limits of Static Analysis (Core Topic)|Topic 1]].

#### Why this topic is important
Every abstract domain in this roadmap (Topics 8–12) is a complete lattice,
and every analysis result (reachable states, invariants, typing judgments)
is a fixpoint — Tarski's theorem is the single piece of mathematics that
makes "compute the least fixpoint" a well-defined, terminating-when-finite
procedure across all of them.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Order-Theory-of-Posets-Lattices-and-Complete-Lattices]]
   - [[Fixpoint-Theory]]
2. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Partially-Ordered-Sets-and-Complete-Lattices]]
   - [[Induction-and-Coinduction]]
3. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/book-guidelines|Verification and Control of Hybrid Systems (Tabuada)]]
   - [[Lattice-and-Fixed-Point-Theory]]
4. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[Mathematical-Foundations-for-Static-Analysis]]
5. [[12_proof_theory_algebra_logic_hiroakira_ono/book-guidelines|Proof Theory and Algebra in Logic (Ono)]]
   - [[Lattices-and-Boolean-Algebras]]
   - [[Heyting-Algebras-and-Algebraic-Logic]]

#### Key Concepts and Definitions
1. Tarski's fixpoint theorem: $\mathrm{lfp}^\sqsubseteq f=\sqcap\{x\mid f(x)\sqsubseteq x\}$ — existence via glb, independent of any constructive iteration.
2. Tarski–Kantorovich / Scott–Kleene iterative theorems (constructive fixpoint computation), and Park's conjugate theorem for computing a greatest fixpoint via a least one.
3. Least fixpoint = induction, greatest fixpoint = coinduction — the coinduction proof rule as "assuming the result to prove it" non-circularly.
4. Complete lattices, ACC/DCC, and Moore families as the recurring structural vocabulary for abstract domains.

#### Relevant Questions
1. Why does Tarski's theorem separate *existence* of a least fixpoint (via glb) from its *construction* (via iteration), and why are both needed in practice?
2. How does Park's conjugate fixpoint theorem let a greatest fixpoint be computed via a least fixpoint on a complemented operator?
3. What does it mean to "assume the result to prove it" non-circularly under the coinduction proof rule?

---

## 3. Galois Connections and the Theory of Abstraction (Core Topic)

#### Pre-requisites
[[#2. Order Theory, Lattices, and Fixpoint Theory (Core Topic)|Topic 2]].

#### Why this topic is important
This is the mechanism that turns "an abstract domain" from an ad hoc data
structure into a mathematically justified approximation with a provable
soundness (and, when possible, best-precision) guarantee — the calculational
method (derive the analysis from the Galois connection, don't postulate it)
that Cousot uses throughout is exactly the discipline the project's own
abstract-interpretation pass should follow.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Galois-Connections-and-Abstraction]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[Abstraction-and-Abstract-Domains]]
3. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Abstract-Interpretation]]
4. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[Abstract-Interpretation-Foundations]]
5. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/book-guidelines|Modular Constraint Solver Cooperation via Abstract Interpretation (Talbot, Monfroy & Truchet)]]
   - [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving]]

#### Key Concepts and Definitions
1. Galois connection $\langle\alpha,\gamma\rangle$, and the Best Abstraction Theorem: a Galois connection exists exactly when a best sound abstraction does.
2. Closure operators (Ward's theorem) as an equivalent, hierarchy-organizing formalization of abstraction, alongside Moore families and logical/soundness relations.
3. Non-existence of a best abstraction for some meaningful domains (e.g. convex polyhedra admit $\gamma$ but no best $\alpha$) — abstraction without a Galois connection.

#### Relevant Questions
1. In what precise sense is "a Galois connection exists" equivalent to "a best sound abstraction exists"?
2. Why do closure operators, Moore families, and logical relations all encode "the same" notion of abstraction, and why does the Galois-connection formulation stay primary in practice?
3. Why do meaningful abstract domains like convex polyhedra sometimes admit a concretization but no best abstraction function?

---

## 4. Relational and Predicate-Transformer Semantics (Core Topic)

#### Pre-requisites
[[#3. Galois Connections and the Theory of Abstraction (Core Topic)|Topic 3]].

#### Why this topic is important
Forward (post) and backward (pre/wp/wlp) transformers are the two dual
readings of program semantics the project's Hoare-contract checker needs —
this is the semantic layer underneath both invariant generation (forward)
and precondition inference/weakest-precondition verification (backward).

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Relational-and-Predicate-Transformer-Semantics]]
2. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book (Abrial)]]
   - [[Semantics-of-Generalized-Substitutions]]

#### Key Concepts and Definitions
1. Relational semantics $\mathcal S_R$, and forward transformers (post/its dual) vs. backward transformers (pre/its dual).
2. Dijkstra's weakest precondition (wp) and weakest liberal precondition (wlp), and the strongest postcondition.
3. The B-Book's normalized-form theorem for generalized substitutions, unifying a WP reading with a relational (set-transformer) reading of the same construct.

#### Relevant Questions
1. Why does adding wlp (which tolerates nontermination) alongside wp recover Dijkstra's full classification of correctness properties?
2. In what sense are forward and backward property transformers "essentially equivalent," and where does that equivalence break down in practice?

---

## 5. Safety, Liveness, and Their Decomposition (Core Topic)

#### Pre-requisites
[[#1. Program Properties, Trace Semantics, and the Limits of Static Analysis (Core Topic)|Topic 1]].

#### Why this topic is important
This is the classification that determines *which proof technique applies*:
safety properties are checkable on a finite prefix (the project's invariant
generation targets these directly), while liveness needs a fundamentally
different argument (ranking functions, fairness) — getting this
distinction right up front avoids trying to "invariant-generate" a
termination guarantee.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Safety-and-Liveness-Properties]]
2. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking (Baier & Katoen)]]
   - [[Safety-Properties-and-Invariants]]
   - [[Liveness-Properties-and-the-Safety-Liveness-Decomposition]]
3. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[Classes-of-Semantic-Properties-and-Their-Verification]]

#### Key Concepts and Definitions
1. Safety = closed (topologically) trace properties, checkable via a bad/minimal-bad prefix; liveness = dense properties.
2. The Alpern–Schneider-style safety/liveness decomposition theorem: every property is the conjunction of a safety and a liveness property.
3. Guarantee properties as a strict subclass of liveness, and the Floyd decomposition $T=T_{safe}\wedge T_{live}$ used for verification-condition instrumentation.
4. Hyperproperties (e.g. non-interference) as properties of *sets* of traces, not expressible as ordinary trace properties.

#### Relevant Questions
1. Why is "never divides by zero" a safety property but "always terminates" is not?
2. Why is every guarantee property a liveness property, but not conversely?
3. Why does non-interference fail to be an ordinary trace property, requiring the hyperproperty/self-composition machinery instead?

---

## 6. Fixpoint Abstraction and the Generic Abstract Interpreter (Core Topic)

#### Pre-requisites
[[#3. Galois Connections and the Theory of Abstraction (Core Topic)|Topic 3]].

#### Why this topic is important
This is where the theory becomes an algorithm: soundly abstracting a
concrete fixpoint computation (rather than the semantics as a whole) is the
calculational recipe behind *every* concrete analysis in Topics 10–22, and
the generic abstract interpreter is the parameterized template the
project's own analyzer should be architected around.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Fixpoint-Abstraction]]
   - [[Forward-Reachability-Semantics]]
   - [[The-Generic-Abstract-Interpreter]]
   - [[Chaotic-Iteration-and-Equational-Semantics]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[Abstract-Interpretation-Foundations]] (Jacobi vs. Gauss-Seidel iteration)

#### Key Concepts and Definitions
1. Sound transformer abstraction $\alpha\circ f\circ\gamma$; soundness ($\alpha\circ f\sqsubseteq\dot f\circ\alpha$) vs. the strictly stronger exact/complete abstraction (commutation).
2. The generic abstract interpreter: an abstract domain (poset + joins + primitive transformers for assignment/test/negated-test) parameterizing one uniform forward-analysis algorithm; finitary (ACC) domains turn well-definedness into guaranteed termination.
3. Chaotic iteration (Jacobi vs. Gauss–Seidel, with a fairness condition) and its convergence theorem: any fair schedule of a continuous operator on a CPO reaches the same least fixpoint.
4. Equational/dataflow-equation semantics as equivalent to functional (fixpoint) semantics — equations reduce to inequations/constraints (Tarski).

#### Relevant Questions
1. What is gained by unifying trace semantics and reachability semantics as two instances of one generic abstract interpreter?
2. Why can Jacobi and Gauss–Seidel iteration diverge for a non-continuous operator, yet always agree when the operator is continuous?
3. In what sense are equational, inequational/constraint, and structural (fixpoint) semantics all "the same" computation?

---

## 7. Fixpoint-Based Verification: Invariance and Hoare Logic (Core Topic)

#### Pre-requisites
[[#6. Fixpoint Abstraction and the Generic Abstract Interpreter (Core Topic)|Topic 6]], [[#5. Safety, Liveness, and Their Decomposition (Core Topic)|Topic 5]].

#### Why this topic is important
This is the direct theoretical justification for the project's
requires/ensures contract layer: Cousot derives Hoare logic's own inference
rules *from* the invariance semantics via calculational design, rather than
postulating them — showing precisely that Hoare logic is itself an abstract
interpretation, which is the exact framing the project's Hoare-triple
checker should adopt. Complements the automated-reasoning roadmap's
separation-logic treatment with the abstract-interpretation view of the
same problem.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Fixpoint-Based-Verification-Proof-Methods]]
   - [[Invariance-Verification-and-Hoare-Logic]]

#### Key Concepts and Definitions
1. Fixpoint induction: $\mathrm{lfp}^\sqsubseteq f\sqsubseteq P$ iff there exists an inductive invariant $I$ — the distinction between a mere invariant and an *inductive* invariant.
2. Iteration induction (dual to fixpoint induction, arguing from ⊥ upward through the iterates) as a complementary, equally sound-and-complete proof method.
3. Hoare triples extended with an escape component for non-local exits (`break`), and the sound-and-complete abstract invariance proof method with one verification condition per language construct.
4. Automation failure modes: undecidable implication checking, invariants too weak to be inductive, and abstract domains too inexpressive (e.g. Presburger arithmetic can't state multiplicative facts) — each with a distinct remedy.

#### Relevant Questions
1. Why must an invariant be *inductive*, not merely true, to be usable in fixpoint induction — and when is strengthening a true invariant to an inductive one impossible within a given logic?
2. In what sense is Hoare logic itself "an abstract interpretation" of the invariance semantics, rather than an independently axiomatized system?
3. What are the three distinct ways automatic invariant/Hoare-proof generation can fail, and why does each need a different fix?

---

## 8. Domain Abstraction, Best Abstract Interpreters, and Cartesian Abstraction (Core Topic)

#### Pre-requisites
[[#6. Fixpoint Abstraction and the Generic Abstract Interpreter (Core Topic)|Topic 6]].

#### Why this topic is important
This supplies the local-to-global soundness argument (checking soundness
per-primitive suffices for the whole analysis) that makes building a new
abstract domain from scratch tractable, and identifies exactly why
non-relational (Cartesian) domains lose precision — the gap the project's
CSP kernel needs to close with relational or automata-based domains.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Domain-Abstraction-and-the-Best-Abstract-Interpreter]]
   - [[Cartesian-Abstraction]]

#### Key Concepts and Definitions
1. Sound-approximate vs. exact domain abstraction, and the theorem that local (per-primitive) soundness/exactness conditions imply global soundness/exactness.
2. Best abstraction via a Galois connection, with predicate abstraction (SLAM-style) as a concrete instance.
3. Cartesian (non-relational, variable-independent) abstraction as structurally incomplete — relational facts like $z=x-y$ are lost by construction, not by a fixable implementation choice.

#### Relevant Questions
1. Why does checking soundness locally, per primitive transformer, suffice for global analysis soundness without a separate whole-program proof?
2. Why is structural Cartesian reachability necessarily incomplete even when the Cartesian abstraction of the exact semantics is itself sound?
3. What breaks in a naive sign-lattice domain that lacks a best abstraction, and how does adding an explicit zero element fix it?

---

## 9. Combining and Refining Abstract Domains: Reduced Products and Modular Cooperation (Core Topic)

#### Pre-requisites
[[#8. Domain Abstraction, Best Abstract Interpreters, and Cartesian Abstraction (Core Topic)|Topic 8]].

#### Why this topic is important
The project's plan to combine an interval/octagon-style numeric domain with
an automata-based structural domain is exactly a reduced-product
construction — this topic supplies both the theory (why the true $n$-ary
reduced product can beat naive pairwise combination) and two independent
engineering realizations (Talbot's shared product, Pelleau's unified CP/AI
domains) worth reusing directly.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Combining-and-Refining-Abstract-Domains]]
2. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/book-guidelines|Modular Constraint Solver Cooperation via Abstract Interpretation (Talbot, Monfroy & Truchet)]]
   - [[Domain-Transformers]]
   - [[Interval-Propagators-Completion-IPC]]
   - [[Shared-Product-and-Modular-Composition]]
3. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[Links-Between-Abstract-Interpretation-and-Constraint-Programming]]
   - [[Unified-Abstract-Domains-for-Constraint-Programming]]

#### Key Concepts and Definitions
1. Reduced product as the glb of two abstract domains (three equivalent characterizations), and why glb-ness requires closure under finite intersection.
2. Iterated pairwise reduction (Nelson–Oppen as an instance) proved strictly less precise, in general, than the true $n$-ary reduced product — yet still widely used.
3. Talbot's shared product: named declarations/dependencies with a `project`/`embed`/reduction-operator interleaving that reaches the least fixed point of the composed reduction, letting some domains stay separate (octagons) while others (boxes) are shared.
4. $E$-consistency (Pelleau) as a single formal notion generalizing GAC/BC/HC, letting classical CP solvers be recovered as special cases of one abstract-domain-for-CP framework.

#### Relevant Questions
1. Why does the reduced product's glb characterization require closure under finite intersection, and what fails without it?
2. Why is iterated pairwise reduction accepted in practice despite a proof that it can be strictly less precise than the full reduced product?
3. Why must Talbot's `embed` function check variable-set containment before joining two domains into the shared product, and what does the dependency mechanism buy over a naive full product?

---

## 10. Numeric and Relational Abstract Domains: Intervals, Congruences, Zones, and Octagons (Core Topic)

#### Pre-requisites
[[#9. Combining and Refining Abstract Domains: Reduced Products and Modular Cooperation (Core Topic)|Topic 9]].

#### Why this topic is important
These are the concrete, implementable numeric domains the project's
abstract-interpretation pass needs for integer/non-linear invariant
generation — non-relational (intervals, congruences) for cheap coverage,
relational (zones, octagons, polyhedra) for the correlations the Cartesian
abstraction of Topic 8 provably loses.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Number-Theoretic-and-Interval-Abstract-Domains]]
   - [[Linear-Algebra-and-Affine-Static-Analysis]]
   - [[Zone-and-Octagon-Relational-Domains]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[The-Octagon-Abstract-Domain]]
   - [[Abstract-Domains-in-Abstract-Interpretation]]
3. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[Abstraction-and-Abstract-Domains]] (non-relational vs. relational taxonomy)

#### Key Concepts and Definitions
1. The Cartesian congruence lattice (ACC but not DCC — needs narrowing, not just widening, to stabilize downward), and interval arithmetic's sub-distributivity relative to real arithmetic.
2. Karr's linear-equality (affine) domain: invertible assignments handled by substitution, non-invertible ones by variable elimination — with no widening/narrowing needed at all, since it has no infinite ascending/descending chains.
3. Zones ($x_i-x_j\le c$) via difference-bound-matrix (DBM) encoding normalized by Roy–Floyd–Warshall saturation; octagons via Miné's doubled-variable trick, reusing the zone machinery wholesale.
4. Re-normalization after widening can silently reintroduce eliminated constraints, defeating termination — fixed by history widening (Cousot); the same octagon domain independently realized via a rotated-basis/box-intersection representation (Pelleau), proven equivalent to the DBM view.

#### Relevant Questions
1. Why does Karr's affine-equality domain need neither widening nor narrowing, and what does that imply about its precision/expressiveness tradeoff versus intervals?
2. Why can re-normalizing a zone/octagon domain after a widening step silently undo the widening's termination guarantee, and how does history widening fix it?
3. How does the octagon domain's doubled-variable encoding let it reuse the zone domain's Floyd–Warshall closure machinery essentially unchanged?

---

## 11. Convergence Acceleration: Widening and Narrowing (Core Topic)

#### Pre-requisites
[[#6. Fixpoint Abstraction and the Generic Abstract Interpreter (Core Topic)|Topic 6]], [[#10. Numeric and Relational Abstract Domains: Intervals, Congruences, Zones, and Octagons (Core Topic)|Topic 10]].

#### Why this topic is important
Widening is the mechanism that makes analysis over infinite-height domains
(unbounded integers, in particular) terminate at all — a hard requirement
for the project's invariant generator, which must handle the actual integer
and non-linear domains named in the standing goals, not just finite-lattice
toy domains.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Convergence-Acceleration-by-Widening-and-Narrowing]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[Sound-Abstract-Semantics-and-Analysis-Algorithms]]
3. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Abstract-Interpretation]] (widening/narrowing within systematic design methods)
4. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|New Techniques for Abstraction Refinement (Greitschus)]]
   - [[Abstract-Interpretation]] (widening strategies)

#### Key Concepts and Definitions
1. Sound widening operators (guarantee ascending-chain termination); Cousot's theorem that a *terminating* widening cannot be increasing in its first argument.
2. Thresholds, delayed widening, and history widening as refinements that recover precision the naive operator would otherwise sacrifice.
3. The finitary-vs-infinitary argument: restricting to Noetherian (ACC) domains is not a general substitute for widening, since an infinite parameterized family of Noetherian domains can still defeat any single termination bound, where widening/narrowing succeeds uniformly.

#### Relevant Questions
1. Why can a terminating widening operator not also be increasing (monotone) in its first argument?
2. Why is restricting analysis to Noetherian abstract domains not a viable general alternative to widening?
3. Why does plain iteration with the domain's join suffice for finite-height domains but fail to terminate for infinite-height ones — and at what precision cost does widening restore termination?

---

## 12. Graph-Theoretic Path Problems and Their Fixpoint Characterization (Core Topic)

#### Pre-requisites
[[#2. Order Theory, Lattices, and Fixpoint Theory (Core Topic)|Topic 2]].

#### Why this topic is important
Reachability itself — the concrete question the project's over-approximating
analysis and under-approximating CSP search are both, in their own ways,
trying to answer — is a path problem, and Cousot's Galois-abstraction-of-
paths theorem explains why the zone/octagon closure operators of Topic 10
and classical shortest-path algorithms are, underneath, the same
computation.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Graph-Theory-and-Path-Problems]]
2. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Graphs-and-Regular-Expressions]]

#### Key Concepts and Definitions
1. The fixpoint characterization of all paths $\Pi(G)$ via Tarski–Kantorovich, and the Galois-abstraction-of-paths theorem explaining why many path algorithms share one underlying algebraic structure.
2. Calculational (not postulated) derivation of Roy–Floyd–Warshall via elementary-path over-approximation — sound specifically because shortest paths are elementary in the absence of negative cycles.
3. Dominators, strongly connected components, reducible graphs, and loop-connectedness as the graph-theoretic vocabulary underlying dataflow-analysis complexity bounds (Topic 13).

#### Relevant Questions
1. How does the Galois-abstraction-of-paths theorem unify what otherwise looks like disparate path-algorithm literature?
2. Why is dropping the elementary-path concatenation check sound for computing shortest distances but not sound for other path problems in general?

---

## 13. Dataflow Analysis and Monotone Frameworks (Core Topic)

#### Pre-requisites
[[#12. Graph-Theoretic Path Problems and Their Fixpoint Characterization (Core Topic)|Topic 12]].

#### Why this topic is important
This is the classical, industrially-proven analysis architecture (available
expressions, live variables, reaching definitions) the project's simpler
dataflow-style checks (e.g. definite-initialization, basic liveness for
refinement contracts) should be built on, including the exact soundness
argument distinguishing correct from merely-traditional formulations.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Dataflow-Analysis-as-Abstract-Interpretation]]
2. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Data-Flow-Analysis]]
   - [[Monotone-Frameworks]]
   - [[Algorithms-for-Solving-Analysis-Equations]]

#### Key Concepts and Definitions
1. Available Expressions/Reaching Definitions/Very Busy/Live Variables as the four canonical may/must, forward/backward analyses, each needing largest or smallest solution depending on direction.
2. Monotone frameworks: property space (lattice + ACC), transfer functions, distributive vs. merely monotone frameworks, and the MFP (maximal fixed point) worklist algorithm vs. the (generally uncomputable) MOP (meet-over-all-paths) — MFP $\sqsupseteq$ MOP, equal for distributive frameworks.
3. Cousot's "semantico-syntactic" correction to classical potential-liveness: the textbook syntactic definition (semantic use, syntactic mod) is neither sound nor complete relative to the true semantic definition, fixed with a mixed criterion.
4. Worklist algorithms (LIFO/FIFO, reverse postorder, round robin, strong-component iteration) and their loop-connectedness-based complexity bound.

#### Relevant Questions
1. Why does Available Expressions need the *largest* fixpoint solution while Reaching Definitions needs the *smallest*?
2. What exactly is unsound about the classical syntactic definition of potential liveness, and how does Cousot's semantico-syntactic criterion fix it without changing the underlying algorithm?
3. Why does MFP coincide with MOP exactly when the framework is distributive, and not in general?

---

## 14. Interprocedural and Context-Sensitive Analysis (Core Topic)

#### Pre-requisites
[[#13. Dataflow Analysis and Monotone Frameworks (Core Topic)|Topic 13]].

#### Why this topic is important
A compiler analyzing real programs must handle procedure calls without
losing all precision at every call site — this is the machinery (call
strings, summaries, context sensitivity) that scales the project's analysis
beyond single-function verification conditions to a whole-program contract
check.

#### Sources to Study
1. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Interprocedural-Data-Flow-Analysis]]
   - [[Context-Sensitivity-in-Control-Flow-Analysis]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[Scalability-Techniques-for-Static-Analysis]]

#### Key Concepts and Definitions
1. Call/return matching and valid paths; the embellished-monotone-framework treatment of interprocedural analysis via call strings and assumption sets.
2. Monovariant vs. polyvariant analysis, $k$-CFA context sensitivity, and the Cartesian Product Algorithm as an alternative context abstraction.
3. Sparse analysis (via safe def-use pre-analysis) and modular analysis via procedure parameterization/summaries as scalability techniques.

#### Relevant Questions
1. What breaks if procedure calls and returns are treated as naive goto edges in a monotone framework, and what does the embellished-framework fix (call strings) restore?
2. What precision/cost tradeoff separates monovariant, $k$-CFA polyvariant, and Cartesian-Product-Algorithm context sensitivity?

---

## 15. Control-Flow Analysis: 0-CFA, k-CFA, and Constraint-Based Methods (Core Topic)

#### Pre-requisites
[[#14. Interprocedural and Context-Sensitive Analysis (Core Topic)|Topic 14]].

#### Why this topic is important
Once the elaborator/compiler deals with higher-order or dynamically
dispatched constructs, ordinary control-flow-graph reachability isn't
enough — 0-CFA and its refinements are the standard technique for
statically approximating "what closures/functions can flow here," directly
relevant if the compiler's refinement-type layer ever needs to reason about
higher-order function arguments.

#### Sources to Study
1. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)]]
   - [[Combining-Control-Flow-and-Data-Flow-Analysis]]

#### Key Concepts and Definitions
1. Abstract cache/environment and the acceptability relation, defined by **coinduction** (a greatest, not least, fixed point) — an unusual and easy-to-misremember direction.
2. Syntax-directed vs. constraint-based presentations of the same analysis, and staging CFA before dataflow analysis to resolve indirect control flow first.

#### Relevant Questions
1. Why does 0-CFA's acceptability relation need a *greatest* fixed point rather than a least one, unlike almost every other analysis in this roadmap?

---

## 16. Shape Analysis and Separation-Logic-Based Compositional Reasoning (Core Topic)

#### Pre-requisites
[[#9. Combining and Refining Abstract Domains: Reduced Products and Modular Cooperation (Core Topic)|Topic 9]]; [[#13. Constrained Horn Clauses and Clause Learning for Verification|Topic 13 of the automated-reasoning roadmap]] (bi-abduction).

#### Why this topic is important
This is the abstract-interpretation-side counterpart to the
automated-reasoning roadmap's separation-logic/bi-abduction material: shape
analysis is how a static analyzer represents and reasons about heap-
manipulating code at all, and compositional (bi-abduction-driven)
interprocedural shape analysis is exactly the scalability model the
project's whole-program contract checker needs for heap-allocated data
structures.

#### Sources to Study
1. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Shape-Analysis]]
2. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/book-guidelines|Compositional Shape Analysis by Means of Bi-Abduction (Calcagno, Distefano, O'Hearn & Yang)]]
   - [[Separation-Logic-Foundations]]
   - [[Compositional-Program-Analysis-Algorithms]]
   - [[Soundness-and-Semantic-Models]]
   - [[The-Abductor-Tool-and-Case-Studies]]
3. [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/book-guidelines|Interprocedural Shape Analysis Using Separation Logic (Illous, Lemerre & Rival)]]
   - Interprocedural Analysis via Procedure Summaries, Relational Shape Abstraction, Intraprocedural Transformation Analysis, Modular Interprocedural Call Analysis (no articles yet)

#### Key Concepts and Definitions
1. Heap-extended abstract state, shape graphs, abstract/summary locations, and sharing information as the classical (Nielson et al.) shape-analysis representation.
2. Symbolic heaps, points-to predicates, and inductive summary predicates ($lseg$, $list$) as the separation-logic-based representation, with `PreGen`/`PostGen`/`InferSpecs` as the compositional (bi-abduction-driven) per-procedure analysis algorithm.
3. Transformation-domain (relational, state-to-state) shape abstraction — abstract transformations as identity/input-output-pair/separating-conjunction forms — as a generalization letting summaries compose across procedure calls without tabulating whole reachable-state sets.

#### Relevant Questions
1. Why is a single abstract location insufficient for shape analysis, and what role does the sharing component play in fixing it?
2. Why must `InferSpecs` run a separate `PostGen` pass rather than trust the preconditions `PreGen` already abduced?
3. Why does composing two abstract transformations sometimes require weakening one side before a matching composition rule applies, and what precision cost results?

---

## 17. Counterexample-Guided Abstraction Refinement and Path-Program Analysis (Core Topic)

#### Pre-requisites
[[#11. Convergence Acceleration: Widening and Narrowing (Core Topic)|Topic 11]].

#### Why this topic is important
CEGAR is the standard loop for reconciling an over-approximating static
analysis with SMT-backed precision on demand — directly the architecture
the project's combined abstract-interpretation/CSP-kernel pipeline should
follow: analyze coarsely, refine only where a spurious counterexample
demands it.

#### Sources to Study
1. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|New Techniques for Abstraction Refinement (Greitschus)]]
   - [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)]]
   - [[Path-Programs-and-Loop-Invariants]]
   - [[ULTIMATE-and-ULTIMATE-TAIPAN]]
2. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/book-guidelines|Acceleration Driven Clause Learning for CHCs (Frohn & Giesl)]]
   - [[Loop-Acceleration]]
   - [[Related-Approaches-to-CHC-SAT-and-Loop-Summarization]]

#### Key Concepts and Definitions
1. The CEGAR refinement loop, spurious counterexamples, and the termination-guarantee gaps of the classical loop.
2. Path programs as trace projections, trace abstraction/Floyd–Hoare automata, and deriving loop invariants directly from abstract-interpretation fixpoints; `htc#`, an abstract-transformer-based Hoare-triple checker that avoids SMT calls at a bounded precision cost.
3. ULTIMATE TAIPAN's hybrid workflow (SMTInterpol → abstract-interpretation fallback → Z3/CVC4) as a concrete instance of combining AI and SMT in one CEGAR loop.
4. Loop acceleration ($N$-fold closure of a transition relation) as an alternative or complement to widening/CEGAR, restricted to theories closed under acceleration (Difference Bounds, Octagons, VASS).

#### Relevant Questions
1. Why must abstract interpretation be applied specifically to *path programs* (trace projections), not the whole program, in trace-abstraction-based CEGAR?
2. How does `htc#` let a CEGAR loop avoid expensive SMT calls, and what precision is traded away for that?
3. What practical consequence follows when a theory is not closed under the $N$-fold acceleration operator?

---

## 18. Constraint Propagation and Domain Consistency (Core Topic)

#### Pre-requisites
[[#9. Combining and Refining Abstract Domains: Reduced Products and Modular Cooperation (Core Topic)|Topic 9]].

#### Why this topic is important
This is the CSP-kernel side of the same lattice/fixpoint machinery this
roadmap has been building: propagators are exactly abstract-interpretation
transfer functions restricted to a finite domain, and this topic supplies
the formal denotational model (soundness, contraction, confluence) the
project's own domain/lattice propagation needs to get right from the start.

#### Sources to Study
1. [[42_Constraint Propagation_Guido_Tack_PhD_2009/book-guidelines|Constraint Propagation (Tack)]]
   - [[The-Denotational-and-Operational-Model-of-Constraint-Propagation]]
   - [[Propagation-Strength-and-Domain-Approximations]]
   - [[Range-Iterators-for-Set-Valued-Domain-Operations]]
2. [[36_Abstract_Domain_In_Constrain_Programming_2015_Wiley/book-guidelines|Abstract Domains in Constraint Programming (Pelleau)]]
   - [[Unified-Abstract-Domains-for-Constraint-Programming]]
   - [[Abstract-Interpretation-Reformulation-of-Constraint-Programming]]
   - [[The-AbSolute-Solver]]

#### Key Concepts and Definitions
1. Propagators as contracting ($p(d)\subseteq d$) and sound functions; propagation as a non-deterministic transition system; termination and confluence theorems (monotonicity $\Rightarrow$ confluence).
2. Domain systems and $\mathcal D$-completeness as a *lower bound* on a propagator's pruning power (not a full specification), with bounds(Z)/bounds(D)/bounds(R)/range consistency as concrete instances.
3. Abstract-interpretation reformulation of CSP solving: solutions as a greatest fixpoint of composed lower-closure-operator propagators, with novel Split/Choice operators that have no classical AI counterpart, and generic solving-algorithm termination via König's lemma.
4. Range iterators as the right interface abstraction for domain operations, adapting classical filtering algorithms (Régin's all-different, the regular constraint) without committing to one concrete set representation.

#### Relevant Questions
1. Why do soundness and contraction alone (without idempotency or monotonicity) already suffice for a sound and complete solver, and what is lost in practice when a propagator is non-monotonic?
2. Why does $\mathcal D$-completeness only give a lower bound on pruning power, and what does that mean in practice for idempotency of a propagator?
3. Why does reformulating CSP solving as abstract interpretation need a genuinely new Split/Choice operator, and what three conditions make a split operator sound?

---

## 19. Model Checking as Abstract Interpretation: Temporal Logics and Automata-Based Verification (Core Topic)

#### Pre-requisites
[[#12. Graph-Theoretic Path Problems and Their Fixpoint Characterization (Core Topic)|Topic 12]].

#### Why this topic is important
Model checking is reachability/invariance analysis specialized to a finite
(or automata-reducible) state space — Cousot's framing of it as literally an
instance of abstract interpretation ties this whole topic back into the
roadmap's main thread, while Baier–Katoen supplies the full algorithmic
depth (LTL/CTL, BDD-based symbolic checking, partial-order reduction) a
from-scratch implementation needs.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Model-Checking-as-Abstract-Interpretation]]
2. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking (Baier & Katoen)]]
   - [[Model-Checking-Fundamentals]]
   - [[Transition-Systems-as-System-Models]]
   - [[Linear-Time-Properties]]
   - [[Automata-Based-Verification-of-Properties]]
   - [[Linear-Temporal-Logic]]
   - [[Automata-Based-LTL-Model-Checking]]
   - [[Computation-Tree-Logic]]
   - [[CTL-Model-Checking]]
   - [[LTL-versus-CTL-Expressiveness]]
   - [[CTL-Star]]
   - [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams]]
   - [[Partial-Order-Reduction]]
   - [[Fairness]]

#### Key Concepts and Definitions
1. Regular expressions (not temporal logic) as Cousot's specification language, with the model-checking function reconstructed as the lower adjoint of a Galois connection, soundness+completeness proved as a theorem rather than assumed.
2. Transition systems, LTL semantics via the expansion law (until = least fixpoint, weak-until = greatest fixpoint), and CTL's fixpoint characterizations ($\exists U$ = lfp, $\exists\Box$ = gfp).
3. The automata-based LTL model-checking pipeline (Büchi automaton construction, product with $A_{\neg\varphi}$, PSPACE-completeness via Savitch), and why CTL model checking is PTIME despite CTL* (which subsumes both LTL and CTL) being PSPACE-complete.
4. Symbolic model checking via BDDs (Shannon expansion, ROBDD canonicity) and partial-order reduction's ample-set conditions (A1–A4), with dependency (A2) as the crux of soundness.

#### Relevant Questions
1. In what sense is model checking here "an abstract interpretation" rather than an independently designed algorithm, and what expressivity tradeoff comes from using regular expressions instead of full temporal logic?
2. Why is CTL model checking PTIME while LTL and CTL* model checking are PSPACE-complete, even though CTL* strictly subsumes CTL?
3. Why is condition A2 (dependency) the crux of partial-order reduction's soundness, and why do the linear-time ample-set conditions fail for branching-time (CTL) properties?

---

## 20. Bisimulation, Simulation, and Process Equivalences (Core Topic)

#### Pre-requisites
[[#19. Model Checking as Abstract Interpretation: Temporal Logics and Automata-Based Verification (Core Topic)|Topic 19]].

#### Why this topic is important
Process equivalence is the theory behind "does my abstraction preserve the
properties I care about" for concurrent/reactive systems, and behind
refinement's own correctness notion (Topic 24) — bisimulation-up-to and
its impredicative definition are also a direct model for coinductive proof
techniques the project's trusted kernel might reuse.

#### Sources to Study
1. [[13_introduction_bisimulation_coinduction_sangiorgi/book-guidelines|Introduction to Bisimulation and Coinduction (Sangiorgi)]]
   - [[Coinduction-and-the-Duality-with-Induction]]
   - [[Bisimulation-and-Bisimilarity]]
   - [[Weak-Bisimulation-and-Internal-Activity]]
   - [[Refinements-of-Simulation]]
2. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking (Baier & Katoen)]]
   - [[Bisimulation-Equivalence]]
   - [[Simulation-Preorders-and-Equivalence]]
   - [[Partition-Refinement-Algorithms]]
   - [[Stutter-Equivalences]]
3. [[23_Refinement_Semantics_Derrick_Boiten_2018/book-guidelines|Refinement: Semantics, Languages and Applications (Derrick & Boiten)]]
   - [[Automata-and-Simulations]]
   - [[Labelled-Transition-Systems-and-the-Spectrum-of-Observational-Refinement]]

#### Key Concepts and Definitions
1. Bisimilarity's impredicative definition (the largest bisimulation, or union of all bisimulations) and the coinductive proof technique it motivates.
2. The linear-time/branching-time equivalence spectrum: trace ⊂ completed-trace ⊂ failures ⊂ ready ⊂ simulation ⊂ bisimulation, with each step distinguishing strictly more processes.
3. Weak bisimilarity, fair abstraction of $\tau$-cycles, and why rooting is needed to restore preservation under choice.
4. Partition-refinement algorithms (Hopcroft-style smaller-half splitting) for computing bisimulation quotients in $O(|S|\log|S|)$.

#### Relevant Questions
1. Why does bisimilarity's impredicative (largest-fixpoint) definition suggest a coinductive proof technique rather than an inductive one?
2. Why is trace equivalence too coarse to distinguish some intuitively different processes, and how does failures/ready equivalence repair this?
3. Why does plain weak bisimilarity fail to be preserved by the choice operator, and how does "rooting" the definition fix it?

---

## 21. Flow (In)Sensitivity, Points-To, and Dependency/Information-Flow Analysis (Core Topic)

#### Pre-requisites
[[#14. Interprocedural and Context-Sensitive Analysis (Core Topic)|Topic 14]].

#### Why this topic is important
Points-to and dependency analysis are the two analyses a Rust-targeting
compiler's own alias/ownership reasoning would have to reconcile with — and
Cousot's reconstruction of both as instances of one Cartesian abstract-
domain interpreter (rather than bespoke constraint-solving algorithms) is
directly reusable engineering guidance.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Flow-Sensitivity-and-Insensitivity]]
   - [[Points-To-Analysis]]
   - [[Dependency-Analysis-and-Information-Flow]]

#### Key Concepts and Definitions
1. Flow-insensitive abstraction as a Galois retraction joining all per-program-point properties into one global property — a sound abstraction of the flow-sensitive analysis, not a separate technique.
2. Andersen's points-to analysis reconstructed as a Cartesian abstract-domain instance; Steensgaard's analysis as Andersen's plus one additional location-collapsing widening.
3. Semantic (not syntactic) dependency: $y$ depends on $x$'s initial value at $\ell$ iff two executions differing only in $x$ yield different $y$-traces at $\ell$; noninterference as a hyperproperty built from this definition.

#### Relevant Questions
1. Why is flow-insensitivity provably just a joining abstraction of flow-sensitive analysis, rather than an independent technique — and why is it usually not the right precision/cost tradeoff?
2. In what sense are Andersen's and Steensgaard's points-to analyses "the same" Cartesian interpreter differing only by one widening choice?
3. Why are timing channels deliberately excluded from the semantic dependency definition, and how do taint analysis, binding-time analysis, and noninterference collapse into one dualistic tracking abstraction?

---

## 22. Type Systems as Abstract Interpretation, and the Herbrand Domain (Core Topic)

#### Pre-requisites
[[#8. Domain Abstraction, Best Abstract Interpreters, and Cartesian Abstraction (Core Topic)|Topic 8]]; [[#9. Higher-Order Unification and Miller's Pattern Fragment|Topic 9 of the automated-reasoning roadmap]] (unification).

#### Why this topic is important
This is a second, independent derivation of typing rules and unification —
this time from abstract-interpretation first principles rather than proof
theory — that directly cross-validates the project's type-checker/unifier
design: soundness ("typable ⟹ can't go wrong") proved from the semantics of
types, and unification/least-common-generalization proved to be exactly the
meet/join of a subsumption lattice.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Type-Systems-as-Abstract-Interpretation]]
   - [[The-Herbrand-Domain-and-Unification]]
2. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis (Nielson, Nielson & Hankin)]]
   - [[Type-and-Effect-Systems]]
   - [[Specialized-Static-Analysis-Frameworks]] (unification-based inference)

#### Key Concepts and Definitions
1. Monomorphic (Hindley–Milner-style) typing reconstructed as an abstract interpretation of the collecting semantics of expressions, with typing rules *derived* by calculational design rather than postulated and proved sound by induction.
2. The Herbrand universe of ground/symbolic terms, the occurs check, and a relational symbolic abstraction requiring repeated variable occurrences to take the same ground value.
3. Unification as the meet, and least-common-generalization as the join, of the subsumption lattice on terms-with-variables — both proved correct as ordinary lattice operations.

#### Relevant Questions
1. What is gained by deriving typing rules from a semantics-first (abstract-interpretation) presentation, versus the classical postulate-then-prove-sound approach?
2. Why must the symbolic (Herbrand) abstraction be relational, not Cartesian, to correctly model unification?
3. How do unification and least-common-generalization arise as exactly the meet and join of the subsumption lattice, rather than as independently invented algorithms?

---

## 23. Backward Accessibility Semantics, Soundness, and the Practice of Static Analysis (Core Topic)

#### Pre-requisites
[[#6. Fixpoint Abstraction and the Generic Abstract Interpreter (Core Topic)|Topic 6]].

#### Why this topic is important
This closes the loop on what "sound" concretely means for a shipped tool
(soundness relative to an explicit undefined-behavior semantics, not an
idealized one) and on the backward-analysis techniques (impossible-failure
accessibility) that complement forward reachability for proving the
*absence* of a bad outcome — directly the shape of the project's Hoare-
contract discharge problem.

#### Sources to Study
1. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation (Cousot)]]
   - [[Backward-Accessibility-Semantics]]
   - [[Soundness-Completeness-and-the-Practice-of-Static-Analysis]]
   - [[Engineering-and-Adoption-of-Static-Analysis-Tools]]
2. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis (Rival & Yi)]]
   - [[Backward-Analysis]]
   - [[Practical-Use-and-Deployment-of-Static-Analysis-Tools]]
   - [[Static-Analysis-for-Advanced-Programming-Language-Features]]
   - [[Foundational-Soundness-Proofs]]

#### Key Concepts and Definitions
1. Impossible-failure accessibility (the Galois-connection adjoint of forward reachability) vs. possible-success accessibility (its dual via complementation), and the "magic transformation" recovering one from the other.
2. Extremal (endpoints-only) vs. intermediate (every-program-point) reduced forward–backward analysis, the latter strictly more precise but costlier.
3. Soundness defined precisely relative to a formal semantics that explicitly models undefined behavior (e.g. "sound up to the first undefined behavior" for C) — and why static analysis is strictly harder to make sound than interactive verification for infinite domains.
4. Strong vs. weak update, sound only when the abstract target denotes a single concrete address — the precise condition under which mutation can be modeled precisely rather than merely joined.

#### Relevant Questions
1. Why are impossible-failure and possible-success accessibility dual rather than identical, and what different question does each answer?
2. Why must "soundness" be defined relative to an explicit undefined-behavior semantic element, rather than an idealized total semantics?
3. Why is strong update sound only when the abstract target provably denotes a single concrete memory location?

---

## 24. Refinement: State-Based Specification, Event-B/ASM, TLA+, and Process-Algebraic Models (Core Topic)

#### Pre-requisites
[[#7. Fixpoint-Based Verification: Invariance and Hoare Logic (Core Topic)|Topic 7]], [[#20. Bisimulation, Simulation, and Process Equivalences (Core Topic)|Topic 20]].

#### Why this topic is important
Refinement is the formal-methods analogue of a compiler's own elaborate-
then-lower pipeline, and it's where the project's requires/ensures
contracts meet a fully worked mechanized proof-obligation methodology
(Event-B's INV/GRD/SIM/VAR schema) that a from-scratch verification-
condition generator can lift almost directly.

#### Sources to Study
1. [[23_Refinement_Semantics_Derrick_Boiten_2018/book-guidelines|Refinement: Semantics, Languages and Applications (Derrick & Boiten)]]
   - [[Refinement-as-Reduction-of-Non-Determinism-and-Behavioural-Consistency]]
   - [[Process-Algebras-CSP-LOTOS-and-CCS]]
   - [[Process-Data-Types-A-General-Model-of-Concurrent-Refinement]]
   - [[State-Based-Specification-Languages-Z-and-B]]
   - [[Event-B-and-Abstract-State-Machines-ASM]]
   - [[Beyond-This-Book-Related-Refinement-Theories]]
2. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book (Abrial)]]
   - [[Refinement-Theory]]
   - [[Composing-Large-Specifications]]
   - [[Case-Studies-in-Specification]]
   - [[Implementation-and-Modular-Architecture]]
3. [[43_Modeling_in_Event-B_JR_Abrial_2010/book-guidelines|Modeling in Event-B (Abrial)]]
   - [[Proof-Obligation-Rules]]
   - [[Refinement-Theory]]
   - [[Design-Patterns-for-Reactive-Controllers]]
4. [[19_TLAplus_Lesle_Lamport/book-guidelines|Specifying Systems: The TLA+ Language and Tools (Lamport)]]
   - [[Specifying-Safety-Properties]] (or equivalent States-Actions-Behaviors article)
   - [[Temporal-Logic-and-Liveness]]
   - [[Refinement-and-Implementation]]

#### Key Concepts and Definitions
1. Refinement as reduction of non-determinism, and the LTS-based spectrum of observational refinement (trace/failures/ready/simulation) directly paralleling Topic 20's equivalence spectrum.
2. Forward vs. backward simulation, neither individually complete, jointly complete via an intermediate specification; Event-B's generalized $m$:$n$ simulation needed once conformality (strict 1:1 event correspondence) is dropped for event splitting/merging.
3. Event-B's proof-obligation schema — INV, FIS, GRD, MRG, SIM, VAR, WFIS — with INV differing structurally between a plain event and a refining event (witness predicates only in the refining case).
4. TLA+'s treatment of implementation as logical implication, with fairness (weak/strong) strengthening a safety specification into a complete liveness-inclusive one.

#### Relevant Questions
1. Why is neither forward nor backward simulation individually complete for proving refinement, and what does "jointly complete via an intermediate specification" mean concretely?
2. Why does Event-B's willingness to split and merge events force a generalized $m$:$n$ simulation instead of a strict 1:1 correspondence?
3. How does casting a liveness property as refinement of a maximally non-deterministic operation (the B-Book's lift example) eliminate the need for bespoke liveness theory?

---

## 25. Timed, Real-Time, and Probabilistic Model Checking (Core Topic)

#### Pre-requisites
[[#19. Model Checking as Abstract Interpretation: Temporal Logics and Automata-Based Verification (Core Topic)|Topic 19]].

#### Why this topic is important
Real-time and probabilistic extensions are the natural next step once the
compiler's verification targets go beyond purely functional correctness
(e.g. timing-sensitive contracts, or probabilistic reliability
requirements) — this topic supplies the region-construction and
Markov-chain machinery that makes both decidable.

#### Sources to Study
1. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking (Baier & Katoen)]]
   - [[Real-Time-Systems-and-Timed-Automata]]
   - [[Timed-CTL-and-TCTL-Model-Checking]]
   - [[Markov-Chains-and-Probabilistic-Verification]]
   - [[Probabilistic-Computation-Tree-Logic]]
   - [[Probabilistic-Bisimulation-and-Markov-Reward-Models]]
   - [[Markov-Decision-Processes]]

#### Key Concepts and Definitions
1. Timed automata (clocks, invariants, guards), timelocks, and Zeno paths as the pathological behaviors real-time model checking must rule out.
2. Clock regions and the region transition system: a finite bisimulation quotient of an uncountable timed state space, reducing TCTL model checking to ordinary CTL model checking (PSPACE-complete).
3. Markov chains, bottom strongly-connected components (BSCCs), and reachability-probability computation via linear equations; the $P_J(\varphi)$ operator of Probabilistic CTL and its qualitative fragment.
4. Markov Decision Processes: schedulers, extremal reachability probabilities via linear programming, and end components.

#### Relevant Questions
1. How does the region-construction technique reduce an uncountable timed state space to a finite bisimulation quotient, and why does that make TCTL model checking decidable?
2. Why must fairness be built directly into CTL's semantics (fair-path quantification) rather than assumed as an external premise the way LTL treats it?

---

## 26. Reachability Analysis for Hybrid and Continuous Dynamical Systems (Core Topic)

#### Pre-requisites
[[#11. Convergence Acceleration: Widening and Narrowing (Core Topic)|Topic 11]], [[#17. Counterexample-Guided Abstraction Refinement and Path-Program Analysis (Core Topic)|Topic 17]].

#### Why this topic is important
This is the abstract-domain machinery for the project's stated interest in
non-linear and continuous constraint domains: template polyhedra,
Bernstein-expansion bound functions, and polynomial zonotopes are all
concrete, algorithmic answers to "how do I over-approximate the reachable
set of a system with real-valued, non-linear dynamics" — directly
applicable to any refinement-type domain that needs to reason about
numeric program state as a continuous quantity.

#### Sources to Study
1. [[45_Paulo_Tabuada_Verification_and_Control_Hybrid_Systems_2009/book-guidelines|Verification and Control of Hybrid Systems (Tabuada)]]
   - [[Hybrid-Dynamical-Systems]]
   - [[Sign-Based-Abstractions]]
   - [[Barrier-Certificates-and-Reachable-Set-Computation]]
   - [[Approximate-System-Relationships]]
   - [[Stability-Theory-for-Approximate-Abstraction]]
   - [[Approximate-Symbolic-Models-for-Verification-and-Control]]
2. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|New Techniques for Abstraction Refinement (Greitschus)]]
   - [[Hybrid-Automata-and-Their-Semantics]]
   - [[Assume-Guarantee-Reasoning-for-Hybrid-Systems]]
   - [[Flowpipe-Approximation-and-Support-Functions]]
   - [[Elimination-of-Spurious-Transitions]]
3. [[74_Reachability_Analysis_Bernstein expansion_2012/book-guidelines|Reachability Analysis for Polynomial Dynamical Systems Using the Bernstein Expansion (Dang & Testylier)]]
   - [[Template-Polyhedra-as-an-Abstract-Domain]]
   - [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients]]
   - [[The-Reachable-Set-Computation-Algorithm]]
4. [[78_Reachability_Analysis_Linear_Systems_with_Uncertain_Parameters_Polynomial_Zonotopes_Huang_2024/book-guidelines|Reachability Analysis for Linear Systems with Uncertain Parameters using Polynomial Zonotopes (Huang, Luo, Bak & Sun)]]
   - [[Polynomial-Zonotopes-as-a-Set-Representation]]
   - [[Dependency-Preserving-Set-Operations]]
   - [[Reachability-Analysis-for-Linear-Systems-with-Uncertain-Parameters]]

#### Key Concepts and Definitions
1. Sign-based abstraction of continuous dynamics via Lie derivatives, and barrier certificates as a direct (Lyapunov-like) safety proof avoiding explicit reachable-set computation.
2. Template polyhedra: fixing the constraint-matrix template in advance turns an intractable nonlinear reachable-set optimization into a tractable per-row linear program, with the template ordering forming a lattice enabling recurrence-based iteration.
3. Polynomial zonotopes as a non-convex generalization of zonotopes, with dependency-preserving (exact, not Minkowski) sums keeping correlated uncertainty from being lossily over-approximated.
4. Assume-guarantee CEGAR for hybrid systems via stratified location merging (convex hull) — sound but only *relatively* complete, since reachability is undecidable for affine hybrid automata in general.

#### Relevant Questions
1. Why does fixing the template constraint matrix in advance make an otherwise intractable polynomial optimization problem solvable via linear programming?
2. Why does exact (dependency-preserving) summation of polynomial zonotopes produce a tighter reachable-set over-approximation than a naive Minkowski sum?
3. Why can assume-guarantee reasoning for hybrid systems achieve only *relative* completeness, and what undecidability result forces this limit?

---

## 27. Symbolic and Tree Automata for Program Analysis (Core Topic)

#### Pre-requisites
[[#19. Symbolic and Tree Automata for Program Analysis|Topic 19 of the automated-reasoning roadmap]] (tree automata/MSO foundations).

#### Why this topic is important
This directly answers the standing project goal of representing abstract
data structures as automata/DFA-based domains: symbolic automata generalize
classical automata to infinite/structured alphabets via decision procedures
over an effective Boolean algebra, exactly what's needed to make an
automata-based abstract domain practical over real program data (strings,
trees, structured heap regions) instead of only toy finite alphabets.

#### Sources to Study
1. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications (Comon et al.)]]
   - [[Automata-with-Constraints]]
   - [[Tree-Set-Automata-and-Set-Constraints]]
   - [[Tree-Transducers]]
   - [[Automata-for-Unranked-Trees]]
   - [[XML-Schema-Formalisms]]
2. [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/book-guidelines|Programming using Automata and Transducers (D'Antoni)]]
   - [[String-Coder-Verification-with-BEX]] (or equivalent)
   - [[Symbolic-Tree-Transducers-and-the-FAST-Language]]
   - [[Symbolic-Visibly-Pushdown-Automata-for-Hierarchical-Data]]
   - [[Streaming-Tree-Transducers]]
3. [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/book-guidelines|The Power of Symbolic Automata and Transducers (D'Antoni & Veanes)]]
   - [[Symbolic-Automata-in-Practice]]
   - [[Symbolic-Transducers-in-Practice]]

#### Key Concepts and Definitions
1. Automata with equality/disequality constraints for non-linear patterns, and the sharp decidability boundary: general constrained automata are undecidable (PCP reduction) while sibling-only-constrained (AWCBB) automata are decidable in PTIME/EXPTIME.
2. Symbolic automata parameterized by an effective Boolean algebra over the alphabet, letting UTF16's $2^{16}$-symbol alphabet (or a program's abstract-heap-region "alphabet") be modeled via BDDs/SMT rather than a blown-up explicit transition table.
3. Symbolic visibly pushdown automata (s-VPAs), restricting binary predicates to call/return pairs specifically to retain full Boolean closure and decidability that general adjacency predicates would break.
4. Streaming tree transducers with a single-use restriction plus regular look-ahead, proved exactly MSO-definable — an automata class expressive enough for real structural transformations yet still decidably equivalence-checkable.

#### Relevant Questions
1. What structural property distinguishes decidable sibling-only constrained tree automata from the undecidable general constrained case?
2. Why does UTF16's alphabet size specifically make classical (non-symbolic) automata impractical, and how does symbolic modeling via BDDs/SMT solve it?
3. Why does restricting binary predicates to call/return pairs (s-VPAs) preserve decidability and Boolean closure where an unrestricted binary predicate would break both?

---

## 28. Domain-Aware and Session-Typed Process Calculi as Program Models (Core Topic)

#### Pre-requisites
[[#20. Bisimulation, Simulation, and Process Equivalences (Core Topic)|Topic 20]]; [[#18. Linear Logic and the Curry–Howard Correspondence for Concurrency|Topic 18 of the automated-reasoning roadmap]].

#### Why this topic is important
Domain-aware session types extend the Curry–Howard-for-concurrency picture
with an explicit notion of "location" (world/domain) governed by an
accessibility relation — directly relevant if the project's verification
target ever needs to reason about distributed or resource-partitioned
program state, not just single-machine control flow.

#### Sources to Study
1. [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/book-guidelines|Domain-Aware Session Types (Caires, Pérez, Pfenning & Toninho)]]
   - [[The-Domain-Aware-Session-Pi-Calculus]]
   - [[Multiparty-Session-Types]]
   - [[Medium-Processes]]
2. [[22_wadler_2012_propositions_as_sessions/book-guidelines|Propositions as Sessions (Wadler)]]
   - [[GV-a-Session-Typed-Functional-Language]] (or equivalent title)
   - [[Translating-GV-into-CP]]
   - [[Related-Work-and-Extensions-to-CP]]

#### Key Concepts and Definitions
1. Domain-migration and domain-communication prefixes in the domain-aware session $\pi$-calculus, with untyped reduction permitting cross-domain synchronization while the type system alone enforces domain discipline.
2. Multiparty session types with a merge operator for projection and a local-type fusion operator, extended with a domain-migration global-type construct.
3. GV as a linear functional session-typed language, and its CPS translation into CP, transferring CP's proof-theoretic race/deadlock-freedom guarantee to a source language with ordinary function types.

#### Relevant Questions
1. Why does untyped reduction in the domain-aware calculus ignore domain discipline entirely, deferring all of it to typing?
2. Why does GV's translation into CP invert an output type into a $\parr$-connective, and what does the translation's type-preservation theorem transfer to GV as a consequence?

---

## 29. Equality Saturation and Effect-Aware Intermediate Representations (Core Topic)

#### Pre-requisites
[[#17. Equality Saturation, E-Graphs, and Proof-Term Generalization|Topic 17 of the automated-reasoning roadmap]].

#### Why this topic is important
This is the compiler-optimization-specific payoff of equality saturation:
Program Expression Graphs give a referentially-transparent, effect-aware
intermediate representation that lets a Rust compiler discover
loop/branch optimizations no single traditional pass explicitly searches
for, while staying within the same congruence-closure theory this roadmap
already covers (Topic 12's graph-path fixpoints, Topic 9's domain
combination).

#### Sources to Study
1. [[39_Equality-Saturation-RossThesis2012/book-guidelines|Program Expression Graphs and Equality Saturation (Tate)]]
   - [[Program-Expression-Graphs-(PEGs)]]
   - [[Representing-Effects-in-PEGs]]
   - [[Loop-and-Branch-Optimizations-Discovered-by-Saturation]]
   - [[Empirical-Evaluation-of-Optimization]]
   - [[Related-Work-and-Positioning]]

#### Key Concepts and Definitions
1. Theta/phi/eval/pass nodes and the well-formedness conditions (loop-lifting, bottom-lifting) that give PEGs referentially-transparent, order-independent semantics.
2. Effect witnesses generalizing the heap-summary threading technique to exceptions and non-termination, formalized via premonoidal categories and the center of a premonoidal category.
3. Inter-loop strength reduction and branch hoisting as optimizations equality saturation discovers "for free," by keeping all equivalent rewrites simultaneously present rather than committing to one destructive rewrite order.

#### Relevant Questions
1. Why must a value be both bottom-lifted and loop-lifted for a PEG's semantics to be well-defined, and what does each well-formedness condition individually rule out?
2. Why can't the heap-summary justification for representing side effects extend directly to effects like exceptions, and what problem does the "center of a premonoidal category" solve instead?
3. Why are lambda-based loop representations (Value Dependence Graphs) fundamentally at odds with efficient equality saturation, motivating the PEG representation instead?

---

## 30. Type-and-Effect Systems, Region-Based Memory, and Certified Low-Level Code (Core Topic)

#### Pre-requisites
[[#22. Type Systems as Abstract Interpretation, and the Herbrand Domain (Core Topic)|Topic 22]].

#### Why this topic is important
This is the closest existing material to what the project's Rust-targeted
compiler backend needs directly: region-based memory typing is a
statically-checked alternative to garbage collection with strong
Rust-ownership parallels, and Typed Assembly Language plus Proof-Carrying
Code together are the concrete precedent for shipping a compiled artifact
with a machine-checkable safety certificate attached.

#### Sources to Study
1. [[05_ATAPL_Pierce_2004/book-guidelines|Advanced Topics in Types and Programming Languages (ed. Pierce)]]
   - Effect Types and Region-Based Memory Management
   - Typed Assembly Language
   - Proof-Carrying Code

#### Key Concepts and Definitions
1. Effect judgments $\Gamma\vdash t:^\phi T$, and Tofte–Talpin region typing splitting correctness into a conditional-correctness result plus a separate soundness argument for region-stack discipline.
2. Typed Assembly Language's register-file/heap-type judgments, and the shared-vs-unique pointer split (`ptr`/`uptr`) that avoids the aliasing problem without full alias types.
3. Proof-Carrying Code's VCGen+Checker+Policy architecture: symbolic evaluation recovers syntax-directedness for low-level code, and Edinburgh LF (with an implicit-LF compression layer) serves as a logic-independent, checkable proof representation.

#### Relevant Questions
1. Why is naive lexically-scoped region deallocation unsound, and how does an explicit effect system repair it?
2. Why does the shared/unique pointer split in Typed Assembly Language avoid the aliasing problem at the cost of giving up full alias-type generality?
3. Why does low-level type checking need symbolic evaluation to become syntax-directed again, and what problem does implicit LF solve for proof size?

---

## Topics Without Dedicated Book Coverage

No gaps were found requiring purely-external sourcing: every fundamental
identified in the preliminary background sketch — trace/collecting
semantics, lattice/fixpoint theory, Galois connections, the generic
abstract interpreter, widening/narrowing, the major abstract-domain
families, dataflow/interprocedural/control-flow analysis, shape analysis,
CEGAR, constraint propagation, model checking, refinement, hybrid-system
reachability, symbolic automata — has at least one strong source already
processed in `vaults/`, with *Principles of Abstract Interpretation*
(Cousot) alone covering the great majority of the theoretical spine
coherently. The main gap is *depth of extraction*, not absence of sources:
book 73 (Illous, Lemerre & Rival, interprocedural shape analysis) has no
generated topic articles yet — running `book-topic-batch` on it would
convert this roadmap's guidelines-only citations for Topic 16 into full
deep-dive notes. One book from the candidate pruning list, 87
(Saillard, *Typechecking in the λΠ-Calculus Modulo*), was tag-listed as
`static-analysis` in an earlier internal scan but its actual
`.learning-goals.md` only tags `type-theory` and `automated-reasoning` —
it was correctly excluded from this roadmap on direct verification.
