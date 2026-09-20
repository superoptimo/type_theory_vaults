# Reachability Analysis for Linear Systems with Uncertain Parameters using Polynomial Zonotopes — Guidelines

## Header

**Title:** Reachability Analysis for Linear Systems with Uncertain Parameters using Polynomial Zonotopes
**Author(s):** Yushen Huang, Ertai Luo, Stanley Bak, Yifan Sun (Stony Brook University)
**Publication:** Preprint (extended journal version submitted to *Nonlinear Analysis: Hybrid Systems*, June 2024; arXiv:2406.11056), extending the HSCC 2023 conference paper by Luo, Kochdumper, and Bak

**Brief Summary:**
This paper presents an algorithm for computing tight, non-convex reachable sets of linear systems whose parameters (system matrices) and inputs are uncertain, using the set representation of polynomial zonotopes. The central idea is that propagating the reachable set via polynomial zonotopes — rather than convex representations like standard zonotopes — lets the algorithm preserve dependencies between the homogeneous and particular solutions and between consecutive time steps, so the non-convexity of the true reachable set is captured tightly instead of being over-approximated by a convex hull. The core algorithm for constant uncertain parameters is then extended to time-varying parameters, linear time-varying systems, linear time-invariant systems, nonlinear systems (via linearization), and hybrid systems (via guard-set intersection). The journal extension adds a scalable optimization algorithm for a structurally special subclass of polynomial zonotopes called multi-affine zonotopes, exploiting a factor-dependency graph to avoid the NP-complete brute-force optimization otherwise required.

**Intent of the Author:**
The authors aim to give reachability analysis practitioners a set-propagation method that is both more accurate (tighter, non-convex enclosures) and, for the multi-affine special case, computationally more scalable than the state-of-the-art splitting-based approach implemented in the CORA toolbox — demonstrating this on autonomous-vehicle-relevant benchmarks (Dubins car, vehicle platooning).

---

## Topic List

1. **Polynomial Zonotopes as a Set Representation** : [[Polynomial-Zonotopes-as-a-Set-Representation|Link]]
   - Zonotopes as centers plus interval-scaled generators
   - Polynomial zonotopes and non-convex set representation : [[Polynomial-Zonotopes-as-a-Set-Representation|Link]]
   - Sparse representation with dependent and independent generators : [[Empirical-Evaluation-and-Benchmarks|Link]]
   - Exponent matrices and dependent factor identifiers
   - Multi-affine zonotopes as a structurally restricted polynomial zonotope : [[Polynomial-Zonotopes-as-a-Set-Representation|Link]]
   - Matrix zonotopes and interval matrices for parametric uncertainty : [[Polynomial-Zonotopes-as-a-Set-Representation|Link]]

2. **Dependency-Preserving Set Operations** : [[Dependency-Preserving-Set-Operations|Link]]
   - mergeID for aligning exponent matrices and identifiers : [[Dependency-Preserving-Set-Operations|Link]]
   - fresh and eval for destroying or instantiating dependent factors : [[Dependency-Preserving-Set-Operations|Link]]
   - Minkowski sum versus exact sum : [[Dependency-Preserving-Set-Operations|Link]]
   - Linear maps with numerical matrices and matrix sets
   - Matrix zonotope multiplication with a polynomial zonotope : [[Dependency-Preserving-Set-Operations|Link]]
   - Multiplication with powers of a matrix set
   - Zonotope enclosure and order reduction of a polynomial zonotope : [[Dependency-Preserving-Set-Operations|Link]]

3. **Matrix Exponential Propagation** : [[Matrix-Exponential-Propagation|Link]]
   - Truncated Taylor series enclosure of the matrix exponential : [[Matrix-Exponential-Propagation|Link]]
   - Interval matrix remainder bounding the truncation error
   - Multiplication with the matrix exponential of two matrix sets : [[Matrix-Exponential-Propagation|Link]]
   - Convex hull of a matrix set via the L1/L2 decomposition : [[Matrix-Exponential-Propagation|Link]]
   - Linear growth of representation size with time step size

4. **Reachability Analysis for Linear Systems with Uncertain Parameters** : [[Reachability-Analysis-for-Linear-Systems-with-Uncertain-Parameters|Link]]
   - Reachable set as the union of solutions over uncertain matrices, initial states, and inputs
   - Homogeneous solution and particular solution decomposition
   - Time interval representation as a matrix zonotope : [[Matrix-Exponential-Propagation|Link1]], [[Polynomial-Zonotopes-as-a-Set-Representation|Link2]]
   - Propagation of the homogeneous solution across time steps
   - Propagation scheme for the particular solution : [[Reachability-Analysis-for-Linear-Systems-with-Uncertain-Parameters|Link]]
   - Combining homogeneous and particular solutions with the exact sum
   - Time preservation enabling extraction of a time-point reachable set
   - Reachability algorithm for constant uncertain parameters : [[Reachability-Analysis-for-Linear-Systems-with-Uncertain-Parameters|Link]]

5. **Extensions of the Core Reachability Algorithm** : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
   - Time-varying uncertain parameters via an enclosure of the state transition matrix : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
   - Linear time-varying systems via per-step abstraction into a parametric system : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
   - Linear time-invariant systems and single-set representation of the whole time horizon : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
   - Nonlinear systems via linearization and abstraction error as uncertain parameters : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
   - Mutual dependence between the abstraction error and the reachable set estimate : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
   - Hybrid systems and guard-set intersection : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
   - Constrained polynomial zonotopes for exact guard intersection : [[Polynomial-Zonotopes-as-a-Set-Representation|Link]]

6. **Multi-Affine Zonotope Optimization** : [[Multi-Affine-Zonotope-Optimization|Link]]
   - Multi-affine polynomial and the multi-affine optimization problem : [[Multi-Affine-Zonotope-Optimization|Link]]
   - Restriction of a polynomial to a subset of factors
   - Support computation and the Kamenev method for convex over-approximation : [[Multi-Affine-Zonotope-Optimization|Link]]
   - NP-completeness of bilinear and multi-affine polynomial optimization : [[Multi-Affine-Zonotope-Optimization|Link]]
   - Brute-force minimization over box-corner candidate solutions
   - Factor dependency graph : [[Multi-Affine-Zonotope-Optimization|Link]]
   - Decomposition over connected components
   - Minimum vertex cut for near-disconnected graphs
   - Splitting-based minimization algorithm exploiting graph structure

7. **Empirical Evaluation and Benchmarks** : [[Empirical-Evaluation-and-Benchmarks|Link]]
   - Dubins car with constant and time-varying parameters
   - Vehicle platooning benchmark and scalability : [[Empirical-Evaluation-and-Benchmarks|Link]]
   - Comparison against the CORA toolbox's zonotope and splitting methods
   - Relative error and running time trade-off across split counts

---

## Chapter Summaries

### Section 1: Introduction (pp. 1–3)

**Summary:** Motivates reachability analysis for safety-critical cyber-physical systems, surveys prior approaches for linear time-invariant systems, linear systems with constant uncertain parameters, and time-varying uncertain parameters, and positions the paper's polynomial-zonotope approach as the first to tightly capture non-convexity across all these cases.

**Key Definitions & Concepts:**
- Reachability analysis — computing a tight enclosure of a system's reachable set to prove or refute safety against unsafe regions.
- Four cases of linear systems (Fig. 1) — time-invariant, constant uncertain parameters, time-varying uncertain parameters, time-varying systems.
- Prior set representations for reachable sets — support functions, polytopes, ellipsoids, zonotopes, star sets.
- Matrix set representations for parametric uncertainty — interval matrices, linear matrix equations, matrix zonotopes, matrix polytopes.

**Key Questions:**
1. Why do convex set representations necessarily over-approximate the reachable set of a linear system with uncertain parameters, even when the true reachable set is non-convex?
2. What distinguishes the "constant uncertain parameters" case from the "time-varying uncertain parameters" case, and why do fewer prior methods address the latter?

---

### Section 2: Preliminaries (pp. 3–7)

**Summary:** Introduces the notation and formal definitions needed throughout the paper: zonotopes, polynomial zonotopes (in sparse representation), interval matrices, matrix zonotopes, the mergeID/fresh/eval operations for managing dependent-factor identifiers, and the core set operations (linear map, Minkowski sum, exact sum) used to build the reachability algorithm.

**Key Definitions & Concepts by Section:**
- **2.1 Notation** — vector/matrix/set notation conventions; infinity norm of a matrix set $\|\mathcal{A}\|_\infty = \max(\|A\|_\infty \mid A \in \mathcal{A})$.
- **2.2 Definition** — Zonotope $\mathcal{Z} = \langle c, G \rangle_Z$ (center plus interval-scaled generators); Polynomial Zonotope $\mathcal{PZ} = \langle c, G, G_I, E, id \rangle_{PZ}$ (dependent generators raised to exponents in $E$, plus independent generators, capturing non-convexity); Interval Matrix $\mathcal{A} = \langle \underline{A}, \overline{A} \rangle_{IM}$; Matrix Zonotope $\mathcal{A} = \langle A^{(0)}, A^{(1)}, \dots, A^{(w)}, id \rangle_{MZ}$; mergeID (aligns two exponent matrices/identifier lists into a common format); fresh (assigns new unique identifiers, destroying dependencies); eval (substitutes a constant value for a dependent factor); Multi-Affine Zonotope (a polynomial zonotope whose exponent matrix contains only 0s and 1s); set operations linear map ($A\mathcal{S}$, $\mathcal{A}\mathcal{S}$) and Minkowski sum ($\mathcal{S}_1 \oplus \mathcal{S}_2$); Minkowski sum vs. exact sum ($\boxplus$) for combining polynomial zonotopes.

**Key Questions:**
1. What is the structural difference between a zonotope and a polynomial zonotope that allows the latter to represent non-convex sets?
2. Why does the exact sum $\boxplus$ produce a tighter result than the Minkowski sum $\oplus$ when combining two polynomial zonotopes that share dependent factors, and when is each operation appropriate?
3. What role do the identifier lists (`id`) play, and why is the `mergeID` operation necessary before combining two polynomial or matrix zonotopes?

---

### Section 3: Set Operations (pp. 6–8)

**Summary:** Derives the additional polynomial-zonotope operations required for the reachability algorithm: multiplying a matrix zonotope with a polynomial zonotope (exactly, and with a tight enclosure when independent generators are present), and multiplying with the matrix exponential of two matrix sets via a truncated Taylor series with a bounded interval-matrix remainder.

**Key Definitions & Concepts:**
- Matrix Zonotope Multiplication (Prop. 1) — exact product $\mathcal{A}\,\mathcal{PZ}$ for a polynomial zonotope without independent generators, built by aligning exponent matrices via mergeID.
- Higher Order Multiplication (Corollary 1) — computing $\mathcal{A}^k\,\mathcal{PZ}$ via repeated application of Prop. 1.
- Matrix Zonotope Multiplication with independent generators (Prop. 2) — tight enclosure treating independent generators as a zero-centered zonotope combined via Minkowski sum.
- Multiplication with Matrix Exponential (Prop. 3) — enclosing $e^{\mathcal{AB}}\,\mathcal{PZ}$ using a Taylor order $\kappa$, an exact sum of the first $\kappa$ terms, and an interval-matrix remainder $E$ added via zonotope enclosure.

**Key Questions:**
1. Why must the exact sum (rather than Minkowski sum) be used when combining the $\kappa$ Taylor-series terms in Prop. 3, and what would be lost if Minkowski sum were used instead?
2. Under what convergence condition ($\epsilon < 1$) is the truncated Taylor series enclosure of the matrix exponential guaranteed to be valid, and what does this condition depend on?

---

### Section 4: Reachability Analysis (pp. 8–11)

**Summary:** Presents the paper's core contribution: an algorithm (Alg. 1) for computing the reachable set of a linear system with constant uncertain parameters by separately computing a homogeneous solution and a particular solution as polynomial zonotopes, then combining and propagating them forward in time while preserving dependency on the time variable.

**Key Definitions & Concepts by Section:**
- **4.1 Problem Definition** — Reachable Set $\mathcal{R}(t)$ (Def. 4.1): the set of all solutions $\xi(A,B,t,x(0),u(\cdot))$ over $A \in \mathcal{A}$, $B \in \mathcal{B}$, $x(0) \in \mathcal{X}_0$, $u(s) \in \mathcal{U}$; time-interval decomposition $\tau_k = [k\Delta t, (k+1)\Delta t]$.
- **4.2 Homogeneous Solution** — $\mathcal{H}(\tau_0) = e^{\mathcal{A}\mathcal{T}}\mathcal{X}_0$ using the time interval represented as a matrix zonotope $\mathcal{T}$; forward propagation via multiplication with $e^{\mathcal{A}\Delta t}$. : [[Reachability-Analysis-for-Linear-Systems-with-Uncertain-Parameters|Link]]
- **4.3 Particular Solution** — enclosure of $\int_0^t e^{A(t-s)}Bu(s)\,ds$ via truncated Taylor series; propagation scheme $\mathcal{P}(\tau_k) \subseteq e^{\mathcal{A}\Delta t}\,\mathcal{P}(\tau_{k-1}) \boxplus \text{fresh}(\mathcal{P}(\Delta t), \mathcal{A}, \mathcal{B})$. : [[Reachability-Analysis-for-Linear-Systems-with-Uncertain-Parameters|Link]]
- **4.4 Reachability Algorithm** — Algorithm 1 combining homogeneous and particular solutions with exact sum; the `eval` operation for extracting a time-point reachable set $\mathcal{R}(t)$ from an interval's reachable set $\mathcal{R}(\tau_k)$. : [[Empirical-Evaluation-and-Benchmarks|Link1]], [[Extensions-of-the-Core-Reachability-Algorithm|Link2]]

**Key Questions:**
1. Why is it important that both the homogeneous and particular solutions "preserve dependency on time," and what tighter result does this dependency preservation enable compared to prior methods (e.g. Althoff et al., 2011a)?
2. How does the algorithm extract the reachable set at a single time point $t \in \tau_k$ from the reachable set representing the whole interval $\tau_k$, and why does this only work because time dependency was preserved?

---

### Section 5: Applications and Reachability Evaluation (pp. 11–18)

**Summary:** Extends the core algorithm to five further settings — time-varying parameters, time-varying linear systems, time-invariant systems, hybrid systems, and nonlinear systems — and evaluates the resulting algorithms on the Dubins car and a 9-dimensional vehicle platooning benchmark, showing tighter and often faster enclosures than the CORA toolbox.

**Key Definitions & Concepts by Section:**
- **5.1 Time-Varying Parameters** — enclosure $\mathcal{M}(t)$ of the time-varying state transition matrix via Taylor terms and convex hulls of matrix sets; Multiplication with Convex Hull (Prop. 4); Algorithm 2 for time-varying parameters. : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
- **5.2 Linear Time-Varying Systems** — abstracting a time-varying system $\dot{x}(t) = A(t)x(t) + B(t)u(t)$ into a linear parametric system per time step using range bounding via affine arithmetic. : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
- **5.3 Linear Time-Invariant Systems** — Lemma 1: the number of Taylor terms $\kappa$ needed for a fixed error bound $\psi$ grows only linearly with the time step $\Delta t$, enabling a single polynomial zonotope to represent the reachable set over the entire time horizon (Example 3). : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
- **5.4 Hybrid Systems** — guard sets, guard intersection as the main challenge in hybrid reachability, constrained polynomial zonotopes enabling exact intersection with (even nonlinear) guard sets. : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
- **5.5 Nonlinear Systems** — first-order Taylor linearization of $\dot{x}(t) = f(x(t), u(t))$ around expansion points, treating the linearization error as uncertain matrix sets $\mathcal{A}, \mathcal{B}$; resolving the mutual dependence between the abstraction error and the interval reachable set via iterative bloating (Example 4, Lotka-Volterra system). : [[Extensions-of-the-Core-Reachability-Algorithm|Link]]
- **5.6–5.7 Benchmarks** — Dubins car (constant and time-varying parameter cases) and the 9-dimensional PLAA01-BND42 vehicle platoon benchmark, compared against CORA's zonotope method.

**Key Questions:**
1. Why does representing the entire time horizon with a single polynomial zonotope (Sec. 5.3) let this approach avoid the "unification step" that other hybrid-system reachability methods require when handling guard intersections (Sec. 5.4)?
2. In the nonlinear-system extension, why is there a mutual dependence between computing the abstraction error matrices $A, B$ and computing the time-interval reachable set $\mathcal{R}(\tau_k)$, and how does the iterative bloating strategy resolve it?
3. On the Dubins car and platoon benchmarks, what trade-offs (accuracy vs. computation time) are observed between this approach and CORA's zonotope method?

---

### Section 6: Scalable Optimization for Multi-Affine Zonotopes (pp. 18–24)

**Summary:** Observes that under a mild independence assumption, the reachable sets produced by Algorithm 2 are multi-affine zonotopes (exponents at most 1), and exploits this structure to design a scalable optimization algorithm — based on decomposing a factor dependency graph into connected components via minimum vertex cuts — that outperforms the existing splitting-based approach (used in CORA) for tasks like 2-D plotting, support function computation, and intersection checking.

**Key Definitions & Concepts by Section:**
- **6.1 Reachability sets are multi-affine zonotopes** — under independence of $\mathcal{A}, \mathcal{B}, \mathcal{X}_0, \mathcal{U}$, the reachable set (with time factor substituted numerically) is a multi-affine zonotope. : [[Multi-Affine-Zonotope-Optimization|Link1]], [[Polynomial-Zonotopes-as-a-Set-Representation|Link2]]
- **6.2 Splitting methods for polynomial zonotopes** — representing a non-convex set as a union of zonotopes via splitting; drawbacks of exponential/unbounded growth in the number of zonotopes. : [[Dependency-Preserving-Set-Operations|Link]]
- **6.3 Improved splitting methods for multiaffine zonotopes** — Multi-Affine Polynomial and Multi-Affine Polynomial Optimization Problem (Def. 6.1); restriction $p|_C$ of a polynomial to a subset $C$ of factors (Def. 6.2 context); supporting hyperplane computation and the Kamenev method for incremental direction selection; Theorem 1 (NP-completeness of bilinear/multi-affine polynomial optimization, from Huang et al. 2023); Brute Force Minimization (Alg. 3) over box corners $\alpha_i \in \{-1,1\}$; Factor Dependency Graph (Def. 6.2); decomposition of the optimization problem over connected components; minimum vertex cut for near-disconnected graphs (Examples 5–6); SplitMin and MinOneComponent (Algs. 4–5).
- **6.4 Evaluation** — comparison against CORA v2024.1.3's splitting-based approach on the Dubins car and a 5-D time-varying benchmark, showing this method finds the exact optimum with far less computation time than increasing the split count.

**Key Questions:**
1. Why does the factor dependency graph's connectivity structure determine how much the multi-affine optimization problem's exponential worst case can be reduced, and how does a minimum vertex cut help even when the graph is only "almost disconnected"?
2. Why is multi-affine polynomial optimization guaranteed to attain its optimum at a corner of the $[-1,1]^n$ box, and how does this fact justify the brute-force baseline algorithm?
3. What does the evaluation in Table 1 reveal about the relationship between the number of splits used by CORA's approach and the marginal improvement in accuracy, and why does this favor the graph-decomposition approach?

---

### Section 7: Conclusion (pp. 25–26)

**Summary:** Summarizes the contributions — a dependency-preserving reachability algorithm for four flavors of linear systems, using polynomial zonotopes to achieve tight non-convex enclosures, plus a scalable multi-affine zonotope optimization algorithm — and identifies limitations (uneven vertex cuts slow the splitting algorithm) and future work (balanced or randomized splitting strategies, avoiding exhaustive per-factor checking).

**Key Definitions & Concepts:**
- No new definitions; recaps the four "flavors" of linear systems addressed (time-invariant, constant uncertain parameters, time-varying uncertain parameters, time-varying systems) and the multi-affine zonotope optimization contribution.

**Key Questions:**
1. What specific limitation of the minimum-vertex-cut-based splitting algorithm (Sec. 6.3) does the conclusion identify, and why does an uneven cut hurt runtime?

---
