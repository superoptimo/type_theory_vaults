# New Techniques for Abstraction Refinement — Guidelines

## Header

**Title:** New Techniques for Abstraction Refinement
**Author(s):** Marius Greitschus
**Publication:** PhD Dissertation, Albert-Ludwigs-Universität Freiburg, 2018 (Advisor: Prof. Dr. Andreas Podelski)

**Brief Summary:**
This dissertation develops new counterexample-guided abstraction refinement (CEGAR) techniques for two very different classes of systems: software programs and cyber-physical (hybrid) systems. For software, it combines abstract interpretation with trace abstraction so that a CEGAR loop is guaranteed to find loop invariants from path programs, implemented in the tool ULTIMATE TAIPAN. For hybrid systems, it presents (1) an assume-guarantee abstraction refinement scheme that abstracts a stratified controller by merging automaton locations and refines by splitting them, and (2) a technique that uses support functions to detect and eliminate spuriously enabled transitions caused by over-coarse flowpipe approximations. All three techniques are implemented (in ULTIMATE and SpaceEx) and evaluated experimentally.

**Intent of the Author:**
The author's motivating observation is that the success of any model-checking technique hinges on the quality of the abstract model construction step; when abstractions are too coarse, refinement is needed, and existing CEGAR schemes either lack termination guarantees (SMT-based loop unwinding) or scale poorly for hybrid systems. The thesis aims to give abstraction-refinement techniques that combine precision with stronger guarantees (termination, guaranteed loop-invariant discovery, soundness/relative completeness) across software and cyber-physical domains, and to validate them with practical implementations and benchmarks.

---

## Topic List

1. **Counterexample-Guided Abstraction Refinement (CEGAR)** : [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link]]
   - The CEGAR refinement loop : [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link]]
   - Spurious counterexamples and abstraction refinement : [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link]]
   - Termination guarantees and their absence in classical CEGAR : [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link]]
   - Assume-guarantee abstraction refinement as a compositional variant of CEGAR : [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link]]

2. **Abstract Interpretation** : [[Abstract-Interpretation|Link]]
   - Partial orders, complete lattices, and fixpoints
   - Galois connections between concrete and abstract domains : [[Abstract-Interpretation|Link1]], [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link2]]
   - Widening operators and ascending chain stabilization
   - The fixpoint computation algorithm : [[Abstract-Interpretation|Link]]
   - Abstract domains: intervals, congruences, octagons, compound domains
   - Reduced product of abstract domains : [[Abstract-Interpretation|Link]]
   - Widening strategies (simple, exponential, literal) : [[Abstract-Interpretation|Link]]

3. **Path Programs and Loop Invariants** : [[Path-Programs-and-Loop-Invariants|Link]]
   - Path programs as projections of a program to a trace : [[Path-Programs-and-Loop-Invariants|Link]]
   - Trace abstraction and Floyd-Hoare automata : [[Path-Programs-and-Loop-Invariants|Link]]
   - Deriving loop invariants from abstract interpretation fixpoints : [[Path-Programs-and-Loop-Invariants|Link]]
   - Generalization of proofs via Hoare triple checkers : [[Path-Programs-and-Loop-Invariants|Link]]
   - Weakening of state assertions to reduce conjunct count : [[Path-Programs-and-Loop-Invariants|Link1]], [[Abstract-Interpretation|Link2]]
   - Combining abstract interpretation and SMT-based trace analysis in one CEGAR loop : [[Path-Programs-and-Loop-Invariants|Link]]

4. **ULTIMATE and ULTIMATE TAIPAN** : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
   - The ULTIMATE program analysis framework and its plug-in architecture : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
   - The ULTIMATE ABSTRACT INTERPRETATION plug-in and disjunctive abstract states : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
   - ULTIMATE TAIPAN workflow combining SMTInterpol, abstract interpretation, and fallback SMT solvers : [[Path-Programs-and-Loop-Invariants|Link]]
   - Large block encoding : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
   - Dynamic block encoding and expressibility of transition formula conjuncts : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
   - Experimental comparison with ULTIMATE AUTOMIZER on SV-COMP benchmarks

5. **Hybrid Automata and Their Semantics** : [[Hybrid-Automata-and-Their-Semantics|Link]]
   - Affine hybrid automata : [[Hybrid-Automata-and-Their-Semantics|Link]]
   - Continuous and discrete update functions : [[Hybrid-Automata-and-Their-Semantics|Link]]
   - Traces, paths, and reachability of hybrid automata : [[Hybrid-Automata-and-Their-Semantics|Link1]], [[ULTIMATE-and-ULTIMATE-TAIPAN|Link2]]
   - Safety of hybrid automata and bad locations : [[Location-Merging-Abstraction-and-Convex-Hull|Link1]], [[Hybrid-Automata-and-Their-Semantics|Link2]]
   - Symbolic states and convex regions : [[Hybrid-Automata-and-Their-Semantics|Link]]
   - Parallel composition of hybrid automata : [[Hybrid-Automata-and-Their-Semantics|Link]]

6. **Assume-Guarantee Reasoning for Hybrid Systems** : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
   - The ASym assume-guarantee rule : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
   - Stratified controllers and location merging : [[Location-Merging-Abstraction-and-Convex-Hull|Link]]
   - Location abstraction and concretization functions : [[Location-Merging-Abstraction-and-Convex-Hull|Link]]
   - Location-merging abstraction and convex hull of invariants and evolutions : [[Location-Merging-Abstraction-and-Convex-Hull|Link]]
   - Compositional analysis algorithm : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
   - Spuriousness analysis of abstract error paths : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
   - Refinement by selectively splitting merged locations : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
   - Soundness and relative completeness theorems : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
   - Switched buffer network benchmark class : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]

7. **Flowpipe Approximation and Support Functions** : [[Flowpipe-Approximation-and-Support-Functions|Link]]
   - Half-spaces, polyhedra, and support functions : [[Flowpipe-Approximation-and-Support-Functions|Link]]
   - Approximate support functions and accuracy bounds : [[Flowpipe-Approximation-and-Support-Functions|Link]]
   - Outer approximations and facet slabs : [[Flowpipe-Approximation-and-Support-Functions|Link]]
   - Inner approximation of a convex set via analytic and Chebyshev centers
   - Flowpipe definition and flowpipe approximation algorithm : [[Elimination-of-Spurious-Transitions|Link1]], [[Flowpipe-Approximation-and-Support-Functions|Link2]]

8. **Elimination of Spurious Transitions** : [[Elimination-of-Spurious-Transitions|Link]]
   - Spurious transitions from over-coarse flowpipe over-approximation
   - Image of a region for a transition : [[Elimination-of-Spurious-Transitions|Link]]
   - Separation of convex sets via the Minkowski sum : [[Elimination-of-Spurious-Transitions|Link]]
   - The Directed Approximation algorithm : [[Elimination-of-Spurious-Transitions|Link]]
   - The adapted GJK algorithm : [[Elimination-of-Spurious-Transitions|Link]]
   - Timed flowpipe separation via convexification : [[Elimination-of-Spurious-Transitions|Link]]
   - Point-wise separation over time with fixed and dynamic direction vectors
   - Sphere and circle benchmarks for flowpipe separation : [[Elimination-of-Spurious-Transitions|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–6)

**Summary:** Introduces model checking and the CEGAR scheme, motivates the thesis by the observation that abstraction quality is the pivotal factor in model checking, and previews the thesis's three contributions: a software model checking technique using abstract interpretation and path programs (ULTIMATE TAIPAN), an assume-guarantee abstraction refinement technique for hybrid systems based on location merging (SpaceEx), and a technique for eliminating spuriously enabled transitions in hybrid systems via support-function-based separation.

**Key Definitions & Concepts:**
- Abstraction refinement — automatic construction of an abstract model satisfying a correctness property by iteratively refining from spurious counterexamples.
- CEGAR (counterexample-guided abstraction refinement) — the standard loop refining an abstraction using spurious counterexamples until the property is proven or a real counterexample is found.
- Spurious counterexample — an execution admitted by the abstract model but not by the original model.

**Key Questions:**
1. Why does classical SMT-based CEGAR for software model checking risk making only infinitesimally small progress (one loop unwinding at a time), and how does the thesis's use of abstract interpretation avoid this?
2. What is the difference between the discrete abstraction (Chapter 3) and continuous abstraction (Chapter 4) problems for cyber-physical systems that the thesis addresses separately?

---

### Chapter 2: Loop Invariants from Counterexamples (pp. 7–74)

**Summary:** Presents a CEGAR-based software model checking technique that unifies abstract interpretation and SMT-based trace abstraction: infeasible traces are turned into path programs, abstract interpretation computes fixpoints of these path programs (guaranteeing termination and yielding loop invariants when successful), and the proof is generalized into a data automaton; when abstract interpretation is inconclusive, the algorithm falls back to interpolation-based SMT analysis of the single trace. The approach is implemented as ULTIMATE TAIPAN within the ULTIMATE framework and evaluated against ULTIMATE AUTOMIZER on SV-COMP benchmarks. : [[Path-Programs-and-Loop-Invariants|Link1]], [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link2]]

**Key Definitions & Concepts by Section:**
- **2.1 Context** — Motivating example showing that a plain interpolating SMT solver cannot find a relational loop invariant an abstract interpreter (e.g., using octagons) can.
- **2.2.1 Programs and Traces** — Expressions/Boolean expressions (Def. 1), statements (Def. 2), program as a labeled graph (Def. 3), traces (Def. 4), program states and successor relation (Def. 5), program execution (Def. 6), feasibility of traces (Def. 7), path program as the projection of a program to a trace (Def. 8, Beyer et al.), Lemma 1 (finitely many distinct path programs). : [[Path-Programs-and-Loop-Invariants|Link]]
- **2.2.2 Abstract Interpretation** — Partial order, partially ordered set, upper/lower bounds, chains, ascending chain and stabilization, join/meet operators, monotone functions, complete lattice (Defs. 9–16), fixpoint (Def. 17), widening operator (Def. 18), Galois connection (Def. 19), abstract domain (Def. 20), abstract program state (Def. 21), the fixpoint computation algorithm (Algorithm 1) using widening at loop heads. : [[Abstract-Interpretation|Link]]
- **2.2.3 Trace Abstraction** — Program automaton (Def. 22) encoding a program's correctness property via error states; Floyd-Hoare automaton (Def. 23), where each state carries a state assertion forming valid Hoare triples; the trace abstraction algorithm iteratively builds a data automaton of infeasible traces and generalizes proofs (Algorithm 2, `generalize`). : [[Path-Programs-and-Loop-Invariants|Link]]
- **2.3 Algorithm** — The thesis's CEGAR scheme: pick a trace, try SMTInterpol first, else build a path program and run abstract interpretation to prove it correct; combines precision of trace abstraction with abstract interpretation's termination guarantee. : [[Elimination-of-Spurious-Transitions|Link]]
- **2.3.1 Proofs from Fixpoints** — Converting an abstract interpretation fixpoint into a proof (set of Hoare triples) usable by `generalize`, using an abstract-transformer-based Hoare triple checker `htc#` instead of an SMT solver for speed.
- **2.3.2 Weakening of State Assertions** — `weaken` function (Algorithm 3) that removes irrelevant variable conjuncts from state assertions in reverse trace order while preserving inductiveness, reducing conjunct count and hence the cost of validity checks. : [[Abstract-Interpretation|Link1]], [[ULTIMATE-and-ULTIMATE-TAIPAN|Link2]]
- **2.4.1 ULTIMATE** — Plug-in-based (Eclipse RCP) program analysis framework; controller/source/analysis/generator/output/library plug-ins; toolchains; recursive control-flow graphs (RCFGs).
- **2.4.2 ULTIMATE ABSTRACT INTERPRETATION** — `FixpointEngine` implementing Algorithm 1; `LoopDetector`; disjunctive abstract states (`maxParallel` parameter) to reduce join-induced imprecision. : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
- **2.4.3 Abstract Domains** — Non-relational vs. relational domains; expression-evaluation algorithm for assume statements over multiple variables; interval domain (three-valued comparisons, arithmetic and join/meet operators); congruence domain (Granger's divisibility congruences); octagon domain (difference bound matrices, strong/tight closure algorithms); Boolean-variable handling; compound domain (Cartesian product of domains, Def. 24 Reduced Product). : [[Abstract-Interpretation|Link]]
- **2.4.4 Widening Strategies** — Simple widening (immediate ⊤), exponential widening (bounded exponential growth toward ∞), literal widening (widen toward program literals first), congruence-domain widening via join. : [[Abstract-Interpretation|Link]]
- **2.4.5 ULTIMATE TAIPAN** — Full workflow (Fig. 18): SMTInterpol first for perfect interpolant sequences; fallback to path-program analysis via abstract interpretation; fallback further to Z3/CVC4; caching of analyzed path programs. : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
- **2.4.6 Dynamic Block Encoding** — Large block encoding merges transitions to reduce automaton state count; transition formulas $\psi = (\phi, \mathrm{IN}, \mathrm{OUT}, \mathrm{AUX}, pv)$; expressibility predicate `ex` orders evaluation of DNF conjuncts to avoid precision loss from conjunct ordering. : [[ULTIMATE-and-ULTIMATE-TAIPAN|Link]]
- **2.5 Evaluation** — ULTIMATE SIMPLE TAIPAN vs. ULTIMATE ABSTRACT INTERPRETATION on SV-COMP ReachSafety-ECA/Loops; ULTIMATE TAIPAN vs. ULTIMATE AUTOMIZER, showing up to 40% more benchmarks solved; SV-COMP 2017 competition results (2nd place in Software Systems, 5th overall). : [[Abstract-Interpretation|Link]]
- **2.6 Related Work** — Comparison with Frama-C/CegarMC, Craig Interpretation (Albarghouthi et al.), Gulavani et al.'s SMT-guided precision recovery, and Beyer et al.'s path-program invariant synthesis.

**Key Questions:**
1. Why is it essential that abstract interpretation is applied to *path programs* rather than the whole program, and how does this control the loss of precision from join operations?
2. How does the `htc#` Hoare-triple checker (based on the abstract transformer `post#`) let ULTIMATE TAIPAN avoid expensive SMT queries during proof generalization, and what precision trade-off does this represent?
3. What problem does dynamic block encoding solve that large block encoding alone cannot, and why does conjunct ordering matter for domains like intervals that cannot express relations like $b' = a'$?

---

### Chapter 3: Assume-Guarantee Abstraction Refinement for Hybrid Systems (pp. 75–106)

**Summary:** Introduces a CEGAR-style, assume-guarantee-based abstraction refinement technique for hybrid systems composed of a plant and a stratified controller: the controller is abstracted by merging locations within a stratum (using convex hulls of invariants and continuous evolutions), and the abstraction is iteratively refined by splitting merged locations when a spurious abstract counterexample is found. The technique is proven sound and relatively complete and implemented in SpaceEx, evaluated on an extended switched buffer network benchmark class. : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link1]], [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link2]]

**Key Definitions & Concepts by Section:**
- **3.1 Context** — The ASym assume-guarantee rule (given assumption $A$ about controller $\mathcal{H}_2$, if $\mathcal{H}_1 \| A \models P$ and $\mathcal{H}_2 \models A$ then $\mathcal{H}_1 \| \mathcal{H}_2 \models P$); motivating tank-controller example showing location merging reduces exponential branching to linear.
- **3.2 Preliminaries** — Affine hybrid automaton (Def. 25: locations, variables, initial condition, differential-equation flow, discrete transitions with affine guards/updates, invariants); hybrid automaton state (Def. 26); continuous update (Def. 27); discrete update (Def. 28); trace of a hybrid automaton (Def. 29); reachability of states (Def. 30); bad location and safety of hybrid automata (Def. 31); symbolic states, regions, and convex-hull assumption; path of a hybrid automaton (Def. 32); parallel composition of hybrid automata with shared/synchronization variables.
- **3.3.1 Abstraction Algorithm** — Location abstraction function $\alpha$ (Def. 33) and concretization function $\alpha^{-1}$ (Def. 34); location-merging abstraction (Def. 35) computing merged invariants and evolutions as convex hulls (via differential inclusion); Proposition 1 (location-merging abstraction preserves safety). : [[Elimination-of-Spurious-Transitions|Link]]
- **3.3.2 Compositional Analysis** — Algorithm 4: construct abstraction of controller, analyze $\mathcal{H}_1 \| \mathcal{H}_2^{\#}$, check spuriousness, refine, repeat. : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
- **3.3.3 Spuriousness Analysis** — Algorithm 5 enumerates concrete paths corresponding to an abstract error path to determine whether the bad location is truly reachable or the counterexample is spurious. : [[Assume-Guarantee-Reasoning-for-Hybrid-Systems|Link]]
- **3.3.4 Refinement Algorithm** — Three cases for choosing which merged location to split based on the longest spurious concrete path; Proposition 2 (progress: each refinement increases location count by one); Theorem 1 (Soundness); Theorem 2 (Relative Completeness, since full reachability of affine hybrid automata is undecidable). : [[Counterexample-Guided-Abstraction-Refinement-(CEGAR)|Link]]
- **3.4 Benchmarks and Evaluation** — Switched buffer network extended with a stratified controller (channels, tanks, phases/options); benchmark generator producing SpaceEx XML models; experiments across "no dynamics," "constant dynamics," and "affine dynamics" controller modes showing generally reduced iteration counts and runtime versus unmerged analysis, with a documented worst-case blow-up (instance 30) when refinement must split all merged locations.
- **3.5 Related Work** — Comparison with Păsăreanu et al.'s L*-based assumption learning, Alur et al. and Tiwari's predicate-abstraction approaches, Jha et al.'s linear hybrid automata restriction, Prabhakar et al.'s initialized rectangular automata, Doyen et al.'s hybridization, and Roohi et al.'s rectangular-automaton CEGAR.

**Key Questions:**
1. How does the ASym assume-guarantee rule justify that abstracting only the controller (not the plant) is sound, and why is over-approximation of the controller essential for premise 2 to hold by construction?
2. Why does merging locations *only within the same stratum* make sense for a stratified controller, and what would go wrong if plant locations were merged instead?
3. In what precise sense is the compositional analysis algorithm only "relatively complete" rather than fully complete, and how does this connect to the undecidability of hybrid automaton reachability?

---

### Chapter 4: Elimination of Spurious Transitions with Support Functions (pp. 107–142)

**Summary:** Addresses the continuous-dynamics counterpart to Chapter 3's discrete abstraction: transitions in a hybrid automaton can become spuriously enabled because flowpipes (over-approximations of ODE solutions) are represented too coarsely. This chapter reduces the problem of proving a transition spurious to separating two convex sets (the flowpipe and the transition's guard set) via support functions, and presents two convex separation algorithms (Directed Approximation and an adapted GJK) plus two ways to lift separation to whole time intervals (convexification and point-wise separation with fixed/dynamic direction vectors), all implemented in SpaceEx. : [[Elimination-of-Spurious-Transitions|Link]]

**Key Definitions & Concepts by Section:**
- **4.2 Preliminaries** — Half-space (Def. 36), polyhedron/polytope (Def. 37), support function and support vectors (Def. 38), approximate support function with accuracy $\varepsilon$ (Def. 39).
- **4.2.1 Approximate Support Functions** — Outer approximation (Def. 40), facet slab (Def. 41), support function bounds (Def. 42) and Lemma 2 (bounds sandwich the exact support function); inner approximation of a convex set via analytic/Chebyshev centers of facet slabs (Proposition 3). : [[Flowpipe-Approximation-and-Support-Functions|Link]]
- **4.3.1 Flowpipe Approximation** — Flowpipe (Def. 43) as the union of reachable regions over a time interval; flowpipe approximation algorithm (Def. 44, from Frehse et al.) constructing piecewise-linear support-function bounds. : [[Flowpipe-Approximation-and-Support-Functions|Link]]
- **4.3.2 Elimination of Spurious Transitions** — Spurious transition illustrated via octagon over-approximation admitting a guard that is unreachable in the concrete system; image of a region for a transition (Def. 45); reduction of spuriousness-checking to separating the flowpipe from the (back-transformed) guard set $\mathcal{G}^*$. : [[Elimination-of-Spurious-Transitions|Link]]
- **4.4 Separation of Convex Sets Using Support Functions** — Lemma 3 (two convex sets are separated iff $0 \notin \mathcal{Q} = \mathcal{R} \oplus (-\mathcal{S})$, the Minkowski sum); Section 4.4.1 Directed Approximation algorithm (Algorithm 7, based on the Mutually Converging Polytopes / MCP algorithm) with Lemma 4 (soundness, with a bounded-distance guarantee on "unknown" results); Section 4.4.2 Adapted GJK Algorithm as an alternative convex separation procedure. : [[Elimination-of-Spurious-Transitions|Link1]], [[Location-Merging-Abstraction-and-Convex-Hull|Link2]], [[Flowpipe-Approximation-and-Support-Functions|Link3]]
- **4.5 Timed Flowpipe Separation** — Separating time domain (Def. 46); Section 4.5.1 separation using convexification (splitting the flowpipe into convex time-slices and applying convex separation to each); Section 4.5.2 point-wise separation over time (Lemma 5) with fixed direction vectors (Lemma 6, reducible to separating the convex hull of the flowpipe) and dynamic direction vectors that evolve with the system dynamics $d_t = d_0^T e^{-At}$ (Lemma 7, Corollary 1 on when dynamic vectors help). : [[Elimination-of-Spurious-Transitions|Link]]
- **4.6 Experimental Results** — Sphere benchmark comparing GJK vs. Directed Approximation across dimensions and distances (GJK generally needs fewer direction evaluations but can fail to terminate); circle benchmark comparing convexification vs. point-wise and fixed vs. dynamic vs. combined direction vectors, showing the combination of fixed and dynamic directions is always most efficient.
- **4.7 Related Work** — Comparison with Alur et al.'s predicate abstraction for hybrid systems, Duggirala and Tiwari's eigenform-based abstractions, Mitchell's forward/backward reachability, and Bogomolov et al./Frehse et al.'s interpolant-based template-direction refinement.

**Key Questions:**
1. Why does reducing "is this transition spurious?" to a convex-set separation problem (via the Minkowski sum) make the check both efficient and directly usable to refine the flowpipe's template directions?
2. What is the key difference between separation with a fixed direction vector versus a dynamic direction vector, and why can a system exist where only one of the two methods succeeds over an unbounded time horizon?
3. What does it mean for the Directed Approximation algorithm to terminate with "unknown," and why is this outcome unavoidable in general (rather than a limitation that could be engineered away)?

---

### Chapter 5: Conclusion and Future Research (pp. 143–146)

**Summary:** Summarizes the three abstraction refinement contributions (ULTIMATE TAIPAN for software; location-merging AGAR for hybrid systems; support-function-based spurious transition elimination) and lays out future research directions: lasso programs and different path-program projection strategies for TAIPAN, logical-lattice-based abstract domains as an alternative to dynamic block encoding, integrating hybrid-system analysis directly into ULTIMATE, applying the location-merging technique to FMI co-simulation, connections to temporal planning as model checking, and using flowpipe/support-function techniques to build polyhedral abstract domains for ULTIMATE ABSTRACT INTERPRETATION.

**Key Definitions & Concepts:**
- Lasso programs — path programs restricted to a single loop with no branches, proposed as a way to reduce the number of join/widen operations abstract interpretation must perform.
- Logical interpretation — an alternative to dynamic block encoding where the abstract domain is a lattice of logical formulas rather than variable valuations.

**Key Questions:**
1. Why might restricting path programs to lasso programs *worsen* convergence in some cases even though it increases per-iteration precision, according to the author's own trade-off analysis?
2. How could the location-merging abstraction refinement technique from Chapter 3 plausibly improve FMI co-simulation performance, based on what that technique reduces (branching factor via merged locations)?
