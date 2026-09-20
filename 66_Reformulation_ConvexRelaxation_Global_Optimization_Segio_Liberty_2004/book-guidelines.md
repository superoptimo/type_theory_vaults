# Reformulation and Convex Relaxation Techniques for Global Optimization — Guidelines

## Header

**Title:** Reformulation and Convex Relaxation Techniques for Global Optimization
**Author(s):** Leo Sergio Liberti
**Publication:** PhD thesis, Department of Chemical Engineering and Chemical Technology, Imperial College London, 15th March 2004

**Brief Summary:**
This thesis addresses the global solution of nonconvex nonlinear programming problems (NLPs) via spatial Branch-and-Bound (sBB) algorithms, arguing that mathematical formulation is as important to computational tractability as the algorithm itself. It surveys and classifies the landscape of problem reformulation and convex-relaxation techniques, then contributes two novel results: an automatic graph-theoretical method ("reduction constraints") for reformulating sparse bilinear NLPs to have fewer bilinear terms and tighter relaxations, and a tight convex/concave envelope for monomials of odd degree when the variable range includes zero — a case with no prior satisfactory envelope. The thesis closes with the design of $\mathcal{OS}$, an object-oriented C++ software framework for building and solving MINLPs, within which a variant of Smith's sBB algorithm is implemented.

**Intent of the Author:**
Liberti aims to show that automatic, formulation-level reformulation of nonconvex NLPs — rather than only better algorithms — can substantially reduce the computational cost of global optimization, and to provide both the theory (reduction constraints, odd-degree envelopes) and a reusable software architecture ($\mathcal{OS}$) that make such automatic reformulation practical for large, sparse problems.

---

## Topic List

1. **Convexity and Function/Set Classification** : [[Convexity-and-Function-Set-Classification|Link]]
   - Convex and concave sets and functions : [[Convexity-and-Function-Set-Classification|Link]]
   - Convex hull of a set : [[Convexity-and-Function-Set-Classification|Link]]
   - Pseudo-convex and quasi-convex functions : [[Convexity-and-Function-Set-Classification|Link]]
   - Difference-of-convex (d.c.) functions and sets : [[Convexity-and-Function-Set-Classification|Link]]
   - Convex and concave relaxations of a function : [[Convexity-and-Function-Set-Classification|Link]]
   - Convex and concave envelopes of a function : [[Convexity-and-Function-Set-Classification|Link]]
   - Convex inequalities : [[Convexity-and-Function-Set-Classification|Link]]
2. **Classification of Optimization Problems** : [[Classification-of-Optimization-Problems|Link]]
   - Continuous, integer and mixed-integer optimization : [[Classification-of-Optimization-Problems|Link]]
   - Constrained and unconstrained optimization
   - Linear and nonlinear optimization : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Convex, concave, d.c. and nonconvex optimization : [[Convexity-and-Function-Set-Classification|Link]]
   - Local versus global optimality : [[Classification-of-Optimization-Problems|Link]]
   - Nonlinear programs (NLPs) as the central problem class : [[Classification-of-Optimization-Problems|Link]]
3. **Global Optimization and the Branch-and-Select Framework** : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
   - History of deterministic global optimization
   - Deterministic versus stochastic global optimization : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
   - Two-phase global search and local search : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
   - Nets, refinements and filters for a feasible region : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
   - The generic Branch-and-Select algorithm : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
   - Exact selection rules and convergence of Branch-and-Select : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
   - Fathoming via upper bound computation
   - Epsilon-optimality
   - NP-hardness of local and global nonconvex optimization : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
4. **Spatial Branch-and-Bound (sBB) Algorithms** : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
   - The generic sBB algorithmic loop : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
   - Smith's sBB algorithm : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
   - Region selection, lower bounding and upper bounding steps
   - Branching point and branching variable selection : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
   - Optimization-based bounds tightening : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
   - Feasibility-based bounds tightening
   - Avoiding slack variables in standardization : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
   - Avoiding redundant local optimizations during branching : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
   - Storing the region list as a tree : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
   - Named sBB variants ($\alpha$BB, Branch-and-Reduce, reduced-space Branch-and-Bound, Branch-and-Cut, BARON)
5. **Reformulation to Standard Forms** : [[Reformulation-to-Standard-Forms|Link]]
   - Box-constrained problems : [[Reformulation-to-Standard-Forms|Link]]
   - Penalty and barrier function reformulations : [[Reformulation-to-Standard-Forms|Link]]
   - The Lagrangian function and Lagrangian duality : [[Reformulation-to-Standard-Forms|Link]]
   - Separable problems and semi-separable functions : [[Reformulation-to-Standard-Forms|Link]]
   - Separation of bilinear and quadratic forms : [[Reformulation-to-Standard-Forms|Link]]
   - Global solution of separable box-constrained problems : [[Reformulation-to-Standard-Forms|Link]]
   - Linear problems and simplex solution : [[Reformulation-to-Standard-Forms|Link]]
   - Reformulating quadratic binary problems to linear binary problems : [[Reformulation-to-Standard-Forms|Link]]
   - Convex problems and nonlinear change-of-variable convexification : [[Reformulation-to-Standard-Forms|Link]]
   - Binary problems : [[Reformulation-to-Standard-Forms|Link]]
   - Reformulating discrete problems to binary problems : [[Reformulation-to-Standard-Forms|Link]]
   - Reformulating binary problems to continuous problems via integrality-enforcing constraints : [[Reformulation-to-Standard-Forms|Link]]
   - Concave problems and their reformulation from binary, bilinear, complementarity and max-min problems : [[Reformulation-to-Standard-Forms|Link]]
   - D.c. problems and reformulation of continuous functions to d.c. functions : [[Reformulation-to-Standard-Forms|Link]]
   - Factorable problems and their recursive structure : [[Reformulation-to-Standard-Forms|Link]]
   - Reformulation of factorable problems to separable form : [[Reformulation-to-Standard-Forms|Link]]
   - Smith's standard form : [[Reformulation-to-Standard-Forms|Link]]
6. **Exact Problem Reformulations** : [[Exact-Problem-Reformulations|Link]]
   - Exact versus convenient reformulations : [[Exact-Problem-Reformulations|Link]]
   - Relaxations as a special case of non-exact reformulation : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Liftings that add new variables to a problem : [[Exact-Problem-Reformulations|Link]]
   - Interchanging equality and inequality constraints via slack variables : [[Exact-Problem-Reformulations|Link]]
   - Dimensionality reduction via space-filling curves : [[Exact-Problem-Reformulations|Link]]
7. **Convex and Linear Relaxation Techniques** : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Convex relaxation as a substitute objective and feasible region
   - $\alpha$BB convex relaxation of general nonconvex terms : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - McCormick envelopes for bilinear terms : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Convex relaxation of trilinear and fractional terms : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Chord underestimation of concave univariate functions : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Diagonal shift matrices and the $\alpha$-parameter underestimator : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Smith's convex relaxation built on Smith's standard form : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link1]], [[Convex-and-Linear-Relaxation-Techniques|Link2]], [[Reformulation-to-Standard-Forms|Link3]]
   - BARON's convex relaxation and concavoconvex univariate terms : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Branching on the curvature turning point of a concavoconvex term : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Linear relaxations versus nonlinear convex relaxations : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - The Reformulation-Linearization Technique (RLT) : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Bound factors and constraint factors in RLT : [[Convex-and-Linear-Relaxation-Techniques|Link]]
8. **Reduction Constraints for Sparse Bilinear Programs** : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
   - Reduction constraints as redundant linear constraints derived by multiplication : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
   - Linearity embedded in a bilinear hypersurface
   - Valid reduction constraint sets : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
   - Bipartite graph representation of linear constraints and variables
   - Dilations in bipartite graphs : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
   - Output set assignments and augmenting paths
   - The AugmentPath and ValidReductionConstraints procedures : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
   - Application to pooling and blending problems : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link1]], [[Classification-of-Optimization-Problems|Link2]]
   - Generalization to simultaneous multiplication by all variables : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
   - Tightening versus size trade-off compared to RLT
9. **Convex Envelopes for Monomials of Odd Degree** : [[Convex-Envelopes-for-Monomials-of-Odd-Degree|Link]]
   - Piecewise convex/concave behavior of an odd-degree monomial spanning zero
   - Tangent line construction and the tangent equation
   - The polynomial $Q_n$ and its unique real root
   - Nonlinear convex and concave envelopes of $x^n$ : [[Convexity-and-Function-Set-Classification|Link]]
   - Tight linear relaxation of the nonlinear envelope : [[Convex-and-Linear-Relaxation-Techniques|Link]]
   - Comparison with the bilinear-product reformulation relaxation : [[Convex-Envelopes-for-Monomials-of-Odd-Degree|Link]]
   - Comparison with the $\alpha$BB underestimation approach : [[Convex-Envelopes-for-Monomials-of-Odd-Degree|Link]]
10. **The $\mathcal{OS}$ Software Framework** : [[The-OS-Software-Framework|Link]]
    - Numerical, structural and symbolic information requirements of sBB codes
    - Object-oriented design in C++ : [[The-OS-Software-Framework|Link]]
    - Structured multidimensional variables and constraints : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
    - The ops object representing an NLP
    - The opssystem and opssolvermanager objects
    - The convexifiermanager object and on-the-fly relaxation updates : [[Convex-and-Linear-Relaxation-Techniques|Link]]
    - Flat and standard-form representations of an NLP : [[The-OS-Software-Framework|Link1]], [[Reformulation-to-Standard-Forms|Link2]]
    - Symbolic differentiation and expression evaluation
    - CAPE-OPEN standardization influence
    - An sBB solver implemented within $\mathcal{OS}$

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 17–30)

**Summary:** Introduces optimization terminology and problem classification, surveys the history of deterministic and stochastic global optimization, and formally develops the Branch-and-Select algorithmic framework (including a convergence theorem and the notion of fathoming and $\varepsilon$-optimality), before outlining the thesis's two central themes — mathematical formulation and convex relaxation — and previewing the remaining chapters.

**Key Definitions & Concepts by Section:**
- **1.1 Basic definitions** — convex set, convex hull, convex/concave function, pseudo-convex function, quasi-convex function, d.c. function and d.c. set, convex/concave relaxation of a function, convex/concave envelope, convex inequality.
- **1.2 Classification of optimization problems** — continuous/integer/mixed-integer optimization, constrained/unconstrained optimization, linear/nonlinear/convex/concave/d.c./nonconvex optimization, local vs. global optimizer, nonlinear programs (NLPs). : [[Classification-of-Optimization-Problems|Link]]
- **1.3 Algorithms for global optimization of NLPs** — deterministic vs. stochastic (nondeterministic) optimization, the standard NLP formulation (1.1), a historical survey from Lagrange through Branch-and-Bound, Interval Optimization, Branch-and-Reduce and $\alpha$BB, to modern stochastic methods; two-phase (global + local search) algorithms; NP-hardness of local and global nonconvex optimization. : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
- **1.4 The branch-and-select strategy** — net, refinement of a net, filter and its limit; the generic Branch-and-Select algorithm (Initialization, Evaluation, Incumbent, Screening, Termination, Selection); exact selection rule; Theorem 1.4.1 (convergence under an exact selection rule); fathoming; $\varepsilon$-global optimality. : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
- **1.5 Mathematical formulation and convex relaxation for nonconvex NLPs** — spatial Branch-and-Bound (sBB) as the NLP analogue of MILP Branch-and-Bound; the LP relaxation analogy; the non-uniqueness of convex relaxations for nonconvex NLPs.
- **1.6 Outline of this thesis** — roadmap of Chapters 2–6.

**Key Questions:**
1. Why does an exact selection rule guarantee convergence of a Branch-and-Select algorithm, and what role does fathoming play in accelerating (but not guaranteeing) this convergence?
2. In what sense is the "convex relaxation" of a nonconvex NLP fundamentally different from the LP relaxation of an MILP, and why does this make formulation choice more consequential for sBB than for MILP Branch-and-Bound?
3. Why is $\varepsilon$-optimality used in practice instead of exact optimality in Branch-and-Select algorithms for global optimization?

---

### Chapter 2: Overview of reformulation techniques in optimization (pp. 31–59)

**Summary:** A systematic literature review that classifies automatic reformulation techniques for optimization problems into reformulations to standard forms, other exact reformulations, and relaxations (convex and linear), concluding by identifying two open gaps — tight relaxation of bilinear terms in large sparse problems, and convex envelopes for odd-degree monomials — that the rest of the thesis addresses. : [[Convex-and-Linear-Relaxation-Techniques|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Reformulations to standard forms** — reformulation and exact reformulation of a problem; standard form; box-constrained problems and penalty/barrier function reformulation; the Lagrangian and Lagrangian dual, duality gap; separable and semi-separable problems, separation of bilinear/quadratic forms (positive definite and semidefinite forms), generalized bilinear form; global solution of separable box-constrained problems via interval analysis; linear problems and the simplex method; reformulating quadratic binary to linear binary problems (a lifting); convex problems and convexifying nonlinear changes of variable; binary problems; reformulating discrete to binary problems and binary to continuous problems (integrality-enforcing constraints); concave problems and their construction from binary, bilinear, complementarity and max-min problems; d.c. problems, density of d.c. functions among continuous functions, reformulating continuous separable functions to d.c. form; factorable problems and their recursive definition, reformulation to separable form; Smith's standard form. : [[Reformulation-to-Standard-Forms|Link1]], [[Spatial-Branch-and-Bound-sBB-Algorithms|Link2]]
- **2.2 Exact reformulations** — interchanging equality/inequality constraints via slack variables; dimensionality reduction via space-filling curves (Peano/Hilbert curves). : [[Exact-Problem-Reformulations|Link]]
- **2.3 Convex relaxations** — convex relaxation of a feasible region and objective; $\alpha$BB convex relaxation (McCormick bilinear envelopes, trilinear and fractional term underestimators, chord underestimator for concave univariate terms, the $\alpha$-parameter/diagonal-shift-matrix underestimator for general nonconvex terms); Smith's convex relaxation (built on Smith's standard form); BARON's convex relaxation (concavoconvex terms, branching on the curvature turning point, fractional-term envelopes via convex extensions). : [[Convex-and-Linear-Relaxation-Techniques|Link1]], [[Convexity-and-Function-Set-Classification|Link2]], [[The-OS-Software-Framework|Link3]]
- **2.4 Linear relaxations** — the Reformulation-Linearization Technique (RLT): bound factor set, constraint factor set, generation and linearization steps, and its combinatorial blow-up in constraint count. : [[Convex-and-Linear-Relaxation-Techniques|Link]]
- **2.5 Other reformulations** — brief survey of REFORM, bilevel-to-MILP reformulation, complementarity-to-minimization reformulation, maximum clique as standard quadratic programming, disjunctive constraint reformulation, and pooling problem reformulations. : [[Exact-Problem-Reformulations|Link1]], [[Convex-Envelopes-for-Monomials-of-Odd-Degree|Link2]], [[Reformulation-to-Standard-Forms|Link3]]
- **2.6 Conclusion** — identifies the two open problems (tight sparse bilinear relaxation; odd-degree monomial envelopes) taken up in Chapters 3 and 4.

**Key Questions:**
1. What distinguishes an "exact" reformulation from a "relaxation," and why does this distinction matter when choosing a technique for a given NLP?
2. Why do liftings (such as the binary-to-continuous or discrete-to-binary reformulations) trade off problem size against tractability, and when is this trade-off worthwhile?
3. How do $\alpha$BB, Smith's, and BARON's convex relaxations differ in what classes of nonconvex terms they can handle, and what does each sacrifice in tightness or generality?

---

### Chapter 3: Reduction constraints for sparse bilinear programs (pp. 60–89)

**Summary:** Presents the thesis's first major contribution — an automatic, graph-theoretical algorithm that identifies which linear constraints of a sparse bilinear NLP, when multiplied by which variables, yield "reduction constraints": redundant linear constraints that can replace bilinear constraints without changing the feasible region while tightening its convex relaxation, validated on pooling and blending problems. : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Basic concepts** — the standard form $[P]$ for sparse bilinear NLPs; reduction constraint (a redundant linear constraint obtained by multiplying an existing linear constraint by a variable, used to eliminate a bilinear constraint); the geometric idea that a bilinear hypersurface intersected with a hyperplane can itself be a hyperplane.
- **3.2 Fundamental properties** — Theorem 3.2.1, proving that for a full-row-rank linear system, multiplying by any variable yields a set of reduction constraints capable of recovering the discarded bilinear constraints; invariance of the recoverable index set with respect to the choice of multiplier variable. : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
- **3.3 An algorithm for the identification of valid reduction constraints** — valid reduction constraint set (one that eliminates more bilinear constraints than it introduces); bipartite graph of constraint nodes and variable nodes; dilation in a bipartite graph; output set assignment (OSA) and complete OSA; augmenting path; the AugmentPath and ValidReductionConstraints procedures and their complexity. : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
- **3.4 A detailed example** — worked application of the algorithm to a 6-variable, 4-constraint bilinear problem, producing valid reduction constraints for several multiplier variables. : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
- **3.5 Computational results** — application to the pooling and blending problem, showing reduced bilinear term counts and tighter relaxations translating into faster sBB solution. : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]
- **3.6 Generalization of the graph-theoretical algorithm** — a unified bipartite graph over all (constraint, variable) multiplication pairs and bilinear-term nodes, capturing beneficial simultaneous multiplications that the per-variable algorithm of Section 3.3 misses; complexity and memory trade-offs versus the original algorithm. : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
- **3.7 Concluding remarks** — reduction constraints tighten the convex relaxation (via Gaussian elimination argument) while reducing its size, contrasted favorably with RLT's unselective constraint generation; acknowledges that structurally non-singular but numerically singular systems can defeat the graph-theoretical detection.

**Key Questions:**
1. Why can a reduction constraint eliminate a bilinear constraint from the original NLP without changing its feasible region, yet still tighten the feasible region of the NLP's convex relaxation?
2. How does casting the search for valid reduction constraints as a dilation-finding problem in a bipartite graph make the algorithm tractable for large sparse NLPs, where brute-force subset search would not be?
3. What specific limitation of the per-variable algorithm (Section 3.3) motivates the generalized, unified bipartite graph algorithm (Section 3.6), and what does the generalization cost in complexity?

---

### Chapter 4: A convex relaxation for monomials of odd degree (pp. 90–104)

**Summary:** Develops the thesis's second major contribution — a tight, continuously differentiable convex/concave envelope for $x^n$ ($n$ odd) on ranges spanning zero, plus a tight linear relaxation of that envelope, and shows both are tighter than prior alternatives (bilinear-product reformulation and $\alpha$BB-style underestimation). : [[Convex-Envelopes-for-Monomials-of-Odd-Degree|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Statement of the problem** — the piecewise convex/concave shape of $x^n$ ($n$ odd) over $[\ell, u]$ with $\ell < 0 < u$; tangent-point construction of the convex underestimator and concave overestimator depending on the relative magnitudes of $|\ell|$ and $u$. : [[Global-Optimization-and-the-Branch-and-Select-Framework|Link]]
- **4.2 The tangent equations** — the tangency condition and the associated polynomial $Q_n$ whose roots give the tangent points; unsolvability by radicals for $n \geq 5$ (Galois-theoretic obstruction).
- **4.3 The roots of $Q_n$ and their uniqueness** — Proposition 4.3.1 and Lemma 4.3.2 bounding the roots; Theorem 4.3.3 proving $Q_n$ has exactly one real root in $(-1, -1/2)$ for all $n$, computable numerically to arbitrary precision.
- **4.4 Nonlinear convex envelopes** — closed-form convex underestimator and concave overestimator of $x^n$ built from the tangent lines and the curve itself; Theorem 4.4.1 proving these are the tightest possible envelopes. : [[Convex-Envelopes-for-Monomials-of-Odd-Degree|Link1]], [[Convex-and-Linear-Relaxation-Techniques|Link2]], [[Convexity-and-Function-Set-Classification|Link3]]
- **4.5 Tight linear relaxation** — linearizing the nonlinear envelope by dropping the "follow the curve" segments, using only the tangent lines (and, additionally, tangents at the endpoints for a tighter version). : [[Convex-and-Linear-Relaxation-Techniques|Link1]], [[Convex-Envelopes-for-Monomials-of-Odd-Degree|Link2]]
- **4.6 Comparison to other relaxations** — comparison with (i) reformulating $x^n$ as a bilinear product of $x$ and $x^{n-1}$ relaxed via McCormick envelopes, and (ii) the $\alpha$BB-style underestimation via a quadratic perturbation; the proposed envelope dominates both.
- **4.7 Computational results** — sBB runs on a test problem showing fewer iterations with the tight linear relaxation versus the bilinear-product relaxation. : [[Reduction-Constraints-for-Sparse-Bilinear-Programs|Link]]

**Key Questions:**
1. Why does the shape of the tightest convex underestimator of $x^n$ over a range spanning zero depend on whether $|\ell|$ or $u$ is larger, and what are the two resulting cases?
2. Why can the tangent points not be found analytically for $n \geq 5$, and how does the thesis nonetheless guarantee their existence, uniqueness, and computability?
3. In what precise sense is the envelope of Chapter 4 provably tighter than both the bilinear-product reformulation and the $\alpha$BB-style underestimation, and why does tightness translate into fewer sBB iterations?

---

### Chapter 5: Spatial Branch-and-Bound algorithm with symbolic reformulation (pp. 105–126)

**Summary:** Reviews Smith's symbolic-reformulation sBB algorithm in detail, proposes efficiency improvements to it, and presents $\mathcal{OS}$, an object-oriented C++ software framework designed to supply the numerical, structural, and symbolic information that sBB algorithms require, within which an sBB solver implementing Smith's algorithm (with the proposed improvements) is built. : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Overview of spatial Branch-and-Bound algorithms** — the generic sBB loop (Initialization, Choice of Region, Lower Bound, Upper Bound, Pruning, Check Region, Branching); brief comparison of Branch-and-Reduce, $\alpha$BB, reduced-space Branch-and-Bound, and Branch-and-Cut. : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
- **5.2 Smith's sBB algorithm** — automatic construction of the convex relaxation via symbolic reformulation; Smith's standard form (linear constraints plus "defining constraints" for bilinear, fractional, power, and univariate-function terms); the convexification rules mapping each nonconvex term type to McCormick or secant/tangent envelopes; region choice, branching point and branch variable selection; optimization-based and feasibility-based bounds tightening. : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
- **5.3 Improvements to Smith's sBB algorithm** — avoiding slack variables in standardization by operating directly on the constraint expression; avoiding redundant local optimizations by distinguishing "original" from "added" (standardization-introduced) variables when branching. : [[Spatial-Branch-and-Bound-sBB-Algorithms|Link]]
- **5.4 The $\mathcal{OS}$ software framework for optimization** — motivation (numerical, structural, and symbolic information requirements); the ops, opssystem, opssolvermanager, and convexifiermanager object classes; typical client usage scenario; requirements for a compliant numerical solver. : [[The-OS-Software-Framework|Link]]
- **5.5 An sBB solver for the $\mathcal{OS}$ framework** — the sBB solver's use of two sub-solvers (a local NLP solver for upper bounds, an LP/NLP solver for lower bounds) plus a convexifier; the convexifier's dependency-link mechanism for on-the-fly relaxation updates; storing the region list as a tree to avoid $O(n)$ per-region memory. : [[The-OS-Software-Framework|Link]]
- **5.6 Concluding remarks** — links $\mathcal{OS}$'s design (separation of problem object from solver object) to the CAPE-OPEN process-engineering software standardization initiative.

**Key Questions:**
1. Why does Smith's standard form isolate nonlinear terms into "defining constraints," and how does this structure make automatic symbolic convexification tractable?
2. What specific inefficiencies in Smith's original algorithm do the "avoiding slack variables" and "avoiding unnecessary local optimizations" improvements address, and why do they preserve convergence while reducing cost?
3. How does the separation of the `ops` (problem) object from the `opssolvermanager` (solver) object in $\mathcal{OS}$ enable both local and global solvers, and multiple simultaneous NLPs, to be supported within one framework?

---

### Chapter 6: Concluding remarks (pp. 127–129)

**Summary:** Synthesizes the thesis's contributions — reduction constraints, odd-degree monomial envelopes, and the $\mathcal{OS}$ software framework — around the unifying theme that mathematical formulation is as central to global optimization performance as algorithmic sophistication, and situates the $\mathcal{OS}$-based sBB implementation's competitive (though not state-of-the-art) numerical performance relative to BARON.

**Key Definitions & Concepts:**
- Traces the origin of the reduction-constraints idea to an empirical observation by Smith about distillation column models.
- Reiterates that reduction constraints are more selective (fewer added constraints/variables) than RLT, aiding scalability to non-trivial problem sizes.
- Frames the odd-degree monomial envelope as filling a previously "sporadic and superficial" gap in the literature.
- Notes that $\mathcal{OS}$'s sBB implementation lacks advanced acceleration features (range reduction, improved branching) present in BARON, yet performs comparably on pooling/blending benchmarks — attributed to the strength of automatic reformulation.

**Key Questions:**
1. According to the author, why is good mathematical formulation argued to be at least as important as sophisticated algorithmic implementation details for sBB performance?
2. What does the comparison with BARON's performance suggest about the relative contribution of formulation-level reformulation versus implementation-level acceleration techniques?

---

### Appendix A: Reference Manual (pp. 142–204)

**Summary:** A software API reference for $\mathcal{OS}$ (object-oriented OPtimization System), documenting its object classes and methods for constructing, modifying, querying, solving, and convexifying MINLPs in structured, flat, and standard-form representations, closing with a worked end-to-end usage example.

**Key Definitions & Concepts:**
- The MINLP object class and its instantiation (`NewMINLP`), construction methods (variables, constraints, constants, nonlinear expressions, objective function), and modification methods (bounds, values).
- Structured, flat, and standard-form information-access methods for querying an MINLP's variables, constraints, and derivatives.
- MINLP solver managers and MINLP systems (`NewMINLPSolverManager`, `Solve`, `GetSolutionStatus`) as the software realization of the `opssolvermanager`/`opssystem` split described in Chapter 5.
- The convexification module (`NewConvexifierManager`, `GetConvexMINLP`, `UpdateConvexVarBounds`) and the `FlatExpression` interface for traversing symbolic expressions.
- A worked example walking through creating variables and constraints, assigning nonlinear expressions, solving the MINLP, and retrieving the solution.

**Key Questions:**
1. How do the flat and standard-form MINLP representations documented here correspond to the theoretical standard form and convexification procedure described in Chapter 5?

---
