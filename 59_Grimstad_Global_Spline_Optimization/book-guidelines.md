# Daily Production Optimization for Subsea Production Systems — Guidelines

## Header

**Title:** Daily Production Optimization for Subsea Production Systems: Methods based on mathematical programming and surrogate modelling
**Author(s):** Bjarne Grimstad
**Publication:** Doctoral thesis (Philosophiae Doctor), Norwegian University of Science and Technology (NTNU), Department of Engineering Cybernetics, Doctoral theses at NTNU 2015:275, Trondheim, October 2015.

**Brief Summary:**
This PhD thesis develops fast, reliable mathematical-programming methods for daily, real-time optimization of subsea oil and gas production systems. Its central technical contribution is a novel spatial branch-and-bound (sBB) algorithm — implemented in the open-source solver CENSO (Convex ENvelopes for Spline Optimization) — for globally solving mixed-integer nonlinear programs (MINLPs) whose nonlinear constraints are represented by multivariate B-splines. B-splines are used as smooth, differentiable surrogate models that replace expensive or black-box process-simulator calls, and their convex-hull property yields tractable polyhedral relaxations for global optimization. The method is combined with a graph-based modelling framework for multiphase flow networks (wells, manifolds, risers, routing, energy balances) and applied to real subsea production systems from BP, to virtual flow metering, and is contextualized by an industry-based study of why model-based production optimization is organizationally and technically difficult in the upstream sector.

**Intent of the Author:**
Grimstad set out to enhance real-time, model-based decision-support tools for subsea production optimization by developing formulations and algorithms that are both computationally fast enough for daily use and reliable/global enough to be trusted, addressing the practical obstacle that production system models are typically proprietary, black-box, non-smooth simulators unsuited to gradient-based or exact optimization.

---

## Topic List

1. **Subsea Production Systems and Their Operation** : [[Subsea-Production-Systems-and-Their-Operation|Link]]
   - Subsea production system architecture (wells, Christmas tree, manifolds, risers, topside facilities)
   - History of subsea technology generations on the Norwegian continental shelf
   - The daily production optimization control loop and production engineer workflow
   - Real-time optimization versus advanced process control and regulatory control
   - Existing commercial and in-house RTO software products

2. **Surrogate Modelling for Optimization** : [[Surrogate-Modelling-for-Optimization|Link]]
   - Motivation for surrogate models in simulation-based optimization : [[Surrogate-Modelling-for-Optimization|Link]]
   - Desirable surrogate model properties (accuracy, cost, smoothness, derivatives, convexity)
   - Comparison of surrogate model families (least squares, radial basis functions, Kriging, neural networks, piecewise linear, splines, wavelets)
   - Function approximation error and Runge's phenomenon

3. **The B-Spline: Theory and Construction** : [[The-B-Spline-Theory-and-Construction|Link]]
   - Univariate B-spline basis functions and the recurrence relation : [[The-B-Spline-Theory-and-Construction|Link]]
   - Regular knot vectors
   - Nonnegativity, local support, and partition of unity properties
   - Multivariate (tensor product) B-splines and the Kronecker product : [[The-B-Spline-Theory-and-Construction|Link]]
   - Control points, control structure, and the control polygon : [[The-B-Spline-Theory-and-Construction|Link]]
   - Convex hull property and minimum bounding box property
   - Knot insertion and the Oslo algorithm
   - Knot refinement and quadratic convergence of the control structure : [[The-B-Spline-Theory-and-Construction|Link]]
   - Representing polynomials exactly in B-spline form : [[The-B-Spline-Theory-and-Construction|Link]]
   - Cubic spline interpolation and the B-spline collocation matrix
   - Schoenberg-Whitney nesting conditions

4. **Global Optimization with Spline Constraints** : [[Global-Optimization-with-Spline-Constraints|Link]]
   - Mixed-integer nonlinear programming (MINLP) and its computational hardness
   - Reformulation-convexification for global optimization
   - Bounding box relaxation of a B-spline constraint : [[Global-Optimization-with-Spline-Constraints|Link]]
   - Convex hull (lifted polyhedral) relaxation of a B-spline constraint : [[Global-Optimization-with-Spline-Constraints|Link]]
   - Equivalence of the B-spline convex hull relaxation to the McCormick relaxation of bilinear terms
   - Tightness trade-offs between generality and relaxation quality

5. **The Spatial Branch-and-Bound Algorithm (CENSO)** : [[The-Spatial-Branch-and-Bound-Algorithm-CENSO|Link]]
   - The generic spatial branch-and-bound (sBB) framework : [[The-Spatial-Branch-and-Bound-Algorithm-CENSO|Link]]
   - Best-bound-first node selection : [[The-Spatial-Branch-and-Bound-Algorithm-CENSO|Link]]
   - Branching variable and branching point selection rules
   - B-spline subdivision under branching : [[The-Spatial-Branch-and-Bound-Algorithm-CENSO|Link]]
   - Bounds tightening techniques (reduced-cost BT, feasibility-based BT, optimality-based BT)
   - Upper bounding via local NLP/MINLP heuristics
   - Convergence criteria for sBB algorithms
   - The CENSO software architecture and its solver dependencies (SPLINTER, GUROBI, IPOPT, BONMIN)

6. **Multiphase Flow Network Modelling** : [[Multiphase-Flow-Network-Modelling|Link]]
   - Graph-based representation of a production network (nodes, edges, discrete edges)
   - Mass, momentum, and energy conservation laws for a control-volume network : [[Multiphase-Flow-Network-Modelling|Link]]
   - Big-M relaxation of disjunctive on/off valve logic
   - Manifold routing constraints : [[Multiphase-Flow-Network-Modelling|Link]]
   - Upstream boundary conditions: inflow performance relationships (IPR) and well performance curves (WPC)
   - Downstream boundary conditions and capacity/draw-down operational constraints
   - Degree-of-freedom analysis of a flow network formulation
   - The complete MINLP formulation for daily production optimization : [[Organizational-and-Industry-Barriers-to-Model-Based-Production-Optimization|Link]]

7. **Virtual Flow Metering and Data Reconciliation** : [[Virtual-Flow-Metering-and-Data-Reconciliation|Link]]
   - Flow estimation as a weighted least-squares data reconciliation problem
   - Model error and measurement error weighting
   - Gross error detection via model error variables
   - B-spline surrogate models for pressure and temperature drop correlations in metering

8. **Computational Validation and Case Studies** : [[Computational-Validation-and-Case-Studies|Link]]
   - Benchmarking CENSO against BARON, COUENNE, and LINDOGLOBAL on polynomial NLP test problems : [[Computational-Validation-and-Case-Studies|Link]]
   - The pump network synthesis problem (PNSP) : [[Computational-Validation-and-Case-Studies|Link]]
   - Real BP subsea production system case studies (production optimization with routing, lift gas, riser velocity constraints)
   - Comparison of local (IPOPT, BONMIN) and global (CENSO) solution methods
   - Validation of optimal solutions against the GAP reference simulator

9. **Organizational and Industry Barriers to Model-Based Production Optimization** : [[Organizational-and-Industry-Barriers-to-Model-Based-Production-Optimization|Link]]
   - The technology stack from process to real-time optimization to advanced process control
   - Instrumentation and data availability constraints
   - Model uncertainty and the calibration bottleneck
   - Disruptive operational events and their effect on optimization value
   - Software interface limitations between process simulators and optimization solvers
   - Trust, KPIs, incentives, and organizational deployment challenges

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–34)

**Summary:** Introduces subsea production systems and their components, surveys existing simulation and optimization technologies for real-time production optimization, frames daily production optimization as a mathematical programming problem, and motivates the use of B-spline surrogate models by comparing surrogate model families and demonstrating spline approximation on the Rosenbrock function. States the thesis's research objective, scope, and outline.

**Key Definitions & Concepts by Section:**
- **1.1 Subsea production systems** — Christmas tree, chokes, manifolds, risers, slugging, subsea processing (separation, boosting, compression), topside facilities. : [[Subsea-Production-Systems-and-Their-Operation|Link]]
- **1.2 Simulation and optimization technologies** — Asset management, reservoir management, real-time optimization (RTO), advanced process control (APC), regulatory control; virtual flow metering (VFM), flow assurance systems (FAS), condition and performance monitoring (CPM). : [[Surrogate-Modelling-for-Optimization|Link]]
- **1.3 Methods for daily production optimization** — Unconstrained and constrained optimization problems (1.1)–(1.3), derivative-free vs. derivative-based methods, mixed-integer nonlinear programming (MINLP), spatial branch-and-bound, disaggregation of black-box simulators, surrogate modelling properties, B-spline definition and local support, Rosenbrock approximation example. : [[Organizational-and-Industry-Barriers-to-Model-Based-Production-Optimization|Link1]], [[Subsea-Production-Systems-and-Their-Operation|Link2]]
- **1.4 Research objective and scope** — Research objective statement; scope limited to subsea production systems, steady-state models.
- **1.5 Outline and contributions of thesis** — Chapter-by-chapter roadmap and list of publications forming the thesis. : [[The-B-Spline-Theory-and-Construction|Link]]

**Key Questions:**
1. Why does the presence of black-box process simulators as constraint functions make simulation-based production optimization fundamentally harder than optimization with algebraic constraints?
2. What properties of the B-spline (as opposed to radial basis functions, Kriging, or piecewise linear models) make it particularly attractive as a surrogate model for global optimization?
3. Why is disaggregation of a MINLP into smaller simulation units advantageous when integer variables would otherwise need to parametrize a black-box simulator?

---

### Chapter 2: Global optimization with spline constraints (pp. 35–77)

**Summary:** Presents the thesis's core theoretical contribution: a reformulation-convexification technique that turns B-spline-constrained MINLPs into lifted polyhedral relaxations solvable by LP, embedded in a novel spatial branch-and-bound algorithm implemented in the solver CENSO. Validates the method against state-of-the-art global solvers (BARON, COUENNE, LINDOGLOBAL) on polynomial test problems and a pump network synthesis case. : [[Global-Optimization-with-Spline-Constraints|Link]]

**Key Definitions & Concepts by Section:**
- **2.2 Background on B-splines** — Univariate B-spline definition (2.1)–(2.2), regular knot vector (Definition 2.1), nonnegativity/local support/partition of unity (Properties 2.1–2.3), Bernstein polynomials as a special case (Property 2.4), multivariate (tensor product) B-splines via the Kronecker product, affine invariance, control points and the control polygon, convex hull property (Lemma 2.1) and minimum bounding box property (Corollary 2.1), knot refinement (Definition 2.2, Lemma 2.2), the knot insertion procedure and Oslo algorithm, representing polynomials exactly as B-splines, cubic spline interpolation and the Schoenberg-Whitney nesting conditions. : [[Surrogate-Modelling-for-Optimization|Link1]], [[The-B-Spline-Theory-and-Construction|Link2]], [[The-Spatial-Branch-and-Bound-Algorithm-CENSO|Link3]]
- **2.3 Global optimization with B-spline constraints** — Reformulation of $P$ into an equivalent MINLP with auxiliary variables, convexification into a relaxed problem $R$, bounding box relaxation and convex hull (lifted polyhedral) relaxation of a B-spline constraint (2.23)–(2.24), equivalence to McCormick's relaxation for bilinear terms, comparison examples (odd-degree monomials, six-hump camelback function). : [[Global-Optimization-with-Spline-Constraints|Link]]
- **2.4 A spatial branch-and-bound for spline-constrained MINLP problems** — The sBB algorithm (Algorithm 3), best-bound-first selection, branching variable/point selection rules (2.28)–(2.29), B-spline subdivision under branching (Algorithm 4), bounds tightening (reduced-cost BT and feasibility-based BT), upper bounding via BONMIN/IPOPT, convergence criteria. : [[The-Spatial-Branch-and-Bound-Algorithm-CENSO|Link]]
- **2.5 Computational results** — Benchmark against BARON, COUENNE, LINDOGLOBAL, SparsePOP on 13 nonconvex polynomial NLP problems; pump network synthesis problem (PNSP) with exact vs. approximated pump characteristics. : [[Computational-Validation-and-Case-Studies|Link]]
- **2.6 Conclusion** — Suggested extensions: Lipschitz-based optimality gaps, additional bounds tightening, decomposition to reduce auxiliary variable growth.
- **2.A/2.B** — Test problem library; proof that the B-spline convex hull relaxation of a bilinear term is equivalent to the McCormick relaxation (Proposition 2.1).

**Key Questions:**
1. How does the convex hull property of the B-spline (Lemma 2.1) translate directly into a valid convex relaxation usable inside a spatial branch-and-bound lower-bounding step?
2. Why is knot insertion at the branching point necessary (rather than optional) to guarantee that child-node relaxations are tighter than the parent's, ensuring sBB convergence?
3. What is the practical trade-off exposed by Table 2.1 between the number of auxiliary variables introduced by knot refinement and the tightness of the resulting relaxation?

---

### Chapter 3: Global optimization of multiphase flow networks using spline surrogate models (pp. 79–120)

**Summary:** Develops a graph-based mathematical programming framework for multiphase flow networks — encoding mass, momentum, and energy balances, routing logic, and boundary conditions as a MINLP — and combines it with B-spline surrogate models and the CENSO solver from Chapter 2 to globally solve realistic subsea production optimization cases supplied by BP. : [[Global-Optimization-with-Spline-Constraints|Link1]], [[Multiphase-Flow-Network-Modelling|Link2]]

**Key Definitions & Concepts by Section:**
- **3.2/3.3 Problem description and previous work** — Daily production optimization as valve-setting search under physical laws and operational constraints; prior piecewise-linear MILP approaches to well routing and rate allocation.
- **3.4 Multiphase flow network modelling** — Directed graph representation ($N$, $E$, $E_d$), source/sink/internal node requirements (R1–R3), mass balances (3.1), momentum balances and the big-M relaxation of the on/off valve disjunction (3.3)–(3.5), energy balances and enthalpy modelling under simplifying assumptions (3.6)–(3.8), flow routing via binary edge variables (3.9), the manifold as a special routing structure (3.10), upstream boundary conditions (linear IPR, Vogel's quadratic IPR) and downstream constant-pressure conditions, capacity and draw-down operational constraints, the complete MINLP formulation $P$. : [[Multiphase-Flow-Network-Modelling|Link]]
- **3.5 Spline surrogate models** — Univariate/multivariate B-spline recap, cubic spline interpolation, worked example approximating the Beggs and Brill pressure drop correlation. : [[Surrogate-Modelling-for-Optimization|Link1]], [[Virtual-Flow-Metering-and-Data-Reconciliation|Link2]]
- **3.6 Solution method** — CENSO's sBB loop applied to $P$; branching variable reduction via degree-of-freedom (DOF) analysis; optimality-based bounds tightening (OBBT) (3.21); BONMIN as a primal heuristic. : [[Computational-Validation-and-Case-Studies|Link]]
- **3.7 Case studies** — Three BP subsea production system cases comparing a proprietary NLP solver, IPOPT, BONMIN, and CENSO; effects of linear vs. cubic spline interpolation, well routing, and energy balances/riser velocity constraints on solution quality and time; validation against the GAP simulator. : [[Computational-Validation-and-Case-Studies|Link]]
- **3.8 Concluding remarks** — Framework flexibility, spline surrogate accuracy, exponential scaling of global solution time, complementary roles of local and global solvers, a demonstrated 3.12% production increase.
- **3.A/3.B** — Degree-of-freedom analysis showing $D = 2|E_d|$; tables of active constraints at case optima.

**Key Questions:**
1. Why does restricting integer (routing) variables to participate only in linear constraints — via the graph-based disaggregation — make the resulting MINLP more tractable for spatial branch-and-bound?
2. How does a degree-of-freedom analysis reduce the number of continuous branching variables from $O((|S|+3)|E|)$ down to $|E_d|$, and why does this matter for sBB tree size?
3. What do the case study results suggest about when a local solver (IPOPT/BONMIN) is likely to already find the global optimum of a spline-surrogate production optimization problem, versus when a certified global solve with CENSO is needed?

---

### Chapter 4: Virtual Flow Metering using B-spline Surrogate Models (pp. 121–134)

**Summary:** Formulates real-time virtual flow metering as a weighted least-squares data reconciliation problem in which black-box pressure-drop process models are replaced by smooth B-spline surrogates, demonstrating that this preserves accuracy while enabling fast, gradient-based, real-time-capable solution and gross error detection. : [[Virtual-Flow-Metering-and-Data-Reconciliation|Link]]

**Key Definitions & Concepts by Section:**
- **4.2 Flow estimation** — The data reconciliation problem $P$ (weighted least squares over measurement error $v$ and model error $w$), inflow performance relationship (IPR), well performance curve (WPC), and choke pressure-drop model formulations for a two-well subsea template.
- **4.3 B-spline surrogate models** — Univariate/multivariate B-spline recap, cubic spline interpolation and the collocation matrix, approximation error analysis for a WPC across sample densities.
- **4.4 Results and discussion** — OLGA reference simulation; single-model versus multi-model (uniform-weight and heterogeneous-weight) estimation cases; qualitative gross error detection via model error magnitudes; solution times well within the real-time budget.
- **4.5 Concluding remarks** — B-spline surrogates preserve accuracy, IPOPT solves the reconciliation series reliably, poorly calibrated models can be identified from error variables.

**Key Questions:**
1. Why does using multiple redundant pressure-drop models (IPR, WPC, choke) in a single weighted reconciliation problem, rather than one model per well, improve robustness against a poorly calibrated individual model?
2. How do the model error weights $\nu$ function as an implicit trust indicator for each physical sub-model, and what happens qualitatively when a sub-model (e.g., the flowline VLP) is systematically inconsistent with the others?
3. Why is B-spline smoothness and analytical-derivative availability specifically important for a *repeatedly solved, real-time* NLP, as opposed to a one-off offline optimization?

---

### Chapter 5: On Why Model-Based Production Optimization is Difficult in the Upstream Industry (pp. 135–153)

**Summary:** An empirical, interview-based study contrasting the upstream (oil and gas) and downstream (refining/chemical process) industries' use of real-time optimization, identifying data, technology, and people-related obstacles — instrumentation gaps, model uncertainty, black-box simulator interfaces, trust erosion, organizational deployment friction, and misaligned incentives — that limit adoption of model-based production optimization tools. : [[Organizational-and-Industry-Barriers-to-Model-Based-Production-Optimization|Link]]

**Key Definitions & Concepts by Section:**
- **5.3 The Context of Production Optimization** — The technology pyramid (production system, data acquisition, production system model, production optimization); the production engineer's role and the production/injection (PI) plan workflow. : [[Organizational-and-Industry-Barriers-to-Model-Based-Production-Optimization|Link1]], [[Surrogate-Modelling-for-Optimization|Link2]]
- **5.4 Observations** — Instrumentation and data availability; uncertainty and model calibration (well inflow uncertainty dominating measurement uncertainty); disruptive operational events (well testing, pigging); software limitations (black-box simulator interfaces lacking gradients/structural information); trust in models and the "cascade of events leading to loss of trust" (Figure 5.4); organization-wide deployment tension between standardization and field-specific tailoring; the need for integrated (cross-disciplinary) competence; limited information sharing across company boundaries; misaligned KPIs and incentives.
- **5.5 Discussion** — Synthesis along three axes: data, technology, people.
- **5.6 Conclusion** — Production optimization is genuinely difficult upstream due to instrumentation/data asymmetries relative to downstream, but the gap is expected to narrow.

**Key Questions:**
1. Why does the report argue that model *uncertainty* (poor calibration from infrequent well testing) is a more fundamental obstacle to upstream RTO than measurement noise?
2. What is the self-reinforcing "cascade" by which poor model maintenance leads to loss of user trust, and why does breaking this cycle require management support rather than purely technical fixes?
3. Why do black-box process simulator interfaces — rather than a lack of capable optimization solvers — represent the chapter's identified core software bottleneck?

---

### Chapter 6: Concluding remarks (pp. 155–162)

**Summary:** Synthesizes the thesis's contributions (the B-spline-based CENSO solver, the graph-based flow network framework, virtual flow metering results, and the industry barriers study), revisits the research objective, and proposes three directions for further research: comparing surrogate model families, systematically handling uncertainty, and integrating reservoir/production/topside models.

**Key Definitions & Concepts (flat list, no formal subsections):**
- Contrast between algebraic-constraint surrogate optimization and unpredictable black-box simulation-based optimization.
- Summary observations: B-spline suitability, framework flexibility, solver consistency requiring good (smooth, derivative-bearing) formulations, exponential scaling of global solution time with model complexity, poor model maintenance as a limiting organizational factor.
- **6.1.1 Comparison of surrogate models** — Open question of piecewise linear (integer branching) vs. nonlinear (spatial branching) surrogate models as optimization technology matures. : [[Surrogate-Modelling-for-Optimization|Link1]], [[Virtual-Flow-Metering-and-Data-Reconciliation|Link2]]
- **6.1.2 Handling of uncertainties** — Chance constraints and conditional value-at-risk for uncertain operational constraints; model uncertainty, calibration automation, and a proposed trust-region-based optimization-under-uncertainty algorithm.
- **6.1.3 Integrating models** — Motivation and challenges (time-scale coupling, computational cost, cross-disciplinary effort, incompatible software) for integrating reservoir, production system, and topside facility models; the short-term/long-term Pareto trade-off.

**Key Questions:**
1. What distinguishes the thesis's proposed algorithm sketch for "optimization under model uncertainty" (local step, feasibility adjustment, recalibration, repeat) from a standard trust-region SQP method, and why does the author draw this parallel?
2. Why does the author conjecture that piecewise-linear (integer-branching) and B-spline (spatial-branching) surrogate approaches might scale similarly "in the limit" as optimization technology matures, despite MIP technology currently being more mature?

---

### Appendix A: Notes related to optimization with splines (pp. 163–167)

**Summary:** Unpublished supplementary notes presenting two refinements to the Chapter 2 theory — bounds tightening exploiting B-spline basis-function properties directly, and a strengthened piecewise convex hull relaxation — plus an outline computational complexity analysis of the sBB algorithm.

**Key Definitions & Concepts by Section:**
- **A.1 Bounds tightening with B-spline constraints** — Domain reduction by scanning knot spans and checking control-point signs against nonnegativity/partition-of-unity properties.
- **A.2 Piecewise convex hull relaxation of B-spline constraints** — Disjunctive, per-segment convex hull relaxation (A.2)–(A.3) proven tighter than the global convex hull relaxation of Lemma 2.1 (Lemma A.1), expressible as a MIP via binary disjunction variables.
- **A.3 Outline of a computational complexity analysis for Algorithm 3** — Polynomial-time bound for the LP relaxation via interior-point methods; complexity of the Oslo knot-insertion algorithm and Kronecker product construction, $O(\tilde{n}^{2d} + dp^2\tilde{n})$; overall per-iteration bound $O(n^{3.5}L^2 + \tilde{n}^{2d} + dp^2\tilde{n})$ and its implications for high-dimensional B-splines.

**Key Questions:**
1. Why is the piecewise convex hull relaxation (Lemma A.1) provably tighter than the single global convex hull relaxation, and what does this cost in terms of added binary variables?
2. Why does the complexity analysis suggest that Algorithm 1 (knot insertion) becomes computationally intractable for B-splines with roughly $d = 10$ or more dimensions, and what does this imply about scaling the spline-constrained sBB method to high-dimensional constraints?

---

### Appendix B: Software (pp. 169–170)

**Summary:** Documents the three C++ software artifacts produced during the thesis — SPLINTER, CENSO, and the Graph Problem Builder — including their capabilities, licensing, and role in the reported case studies.

**Key Definitions & Concepts (flat list):**
- **SPLINTER** — C++ multivariate function approximation library (tensor product B-splines, ordinary least squares, radial basis function interpolation); released under the Mozilla Public License 2.0.
- **CENSO** (Convex ENvelopes for Spline Optimization) — C++ global optimization framework for spline-constrained MINLPs, interfacing IPOPT, BONMIN, and GUROBI; released under the Mozilla Public License 2.0.
- **Graph Problem Builder** — C++ tool for automatically constructing production optimization problem formulations (per Chapter 3) from network topology, fluid data, constraints, and surrogate models; not publicly released.

**Key Questions:**
1. Why does automatically generating the mathematical programming formulation from a graph description (rather than hand-coding constraints) reduce the risk of modelling errors in production optimization studies?
