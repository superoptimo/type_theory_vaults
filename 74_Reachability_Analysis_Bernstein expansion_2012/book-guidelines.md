# Reachability Analysis for Polynomial Dynamical Systems Using the Bernstein Expansion — Guidelines

## Header

**Title:** Reachability Analysis for Polynomial Dynamical Systems Using the Bernstein Expansion
**Author(s):** Thao Dang and Romain Testylier (Laboratory VERIMAG, CNRS, Grenoble, France)
**Publication:** Accepted for publication in *Reliable Computing Journal*, Special issue on Bernstein Polynomials, December 2012 (25-page research paper, not a book — treated here as a single-document unit with numbered sections in place of chapters)

**Brief Summary:**
This paper addresses the computation of reachable sets for discrete-time dynamical systems whose evolution is governed by a multivariate polynomial map $x[k+1] = \pi(x[k])$, a problem central to safety verification of hybrid systems and embedded software with nonlinear dynamics. The authors combine two ingredients: template polyhedra (fixed-shape convex polyhedra used as a computationally cheap over-approximation representation) and the Bernstein expansion of polynomials (a technique from Computer-Aided Geometric Design that produces control points bounding a polynomial's range over a box). By using Bernstein coefficients to derive affine (linear) lower/upper bound functions for each polynomial component, the authors reduce a per-step polynomial optimization problem to a linear program, making the method tractable in higher dimensions than the earlier Bézier-simplex approach it improves on. Two techniques for mapping an arbitrary polyhedron onto the unit box (where the Bernstein machinery applies) are presented — an oriented box approximation and an exact change of variables — and the tradeoffs between them are evaluated experimentally on control and biological systems.

**Intent of the Author:**
The authors aim to make polynomial reachability computation practical at dimensions beyond the 3–4 variable ceiling imposed by their earlier Bézier-simplex-mesh method, by replacing expensive polynomial/mesh optimization with linear programming, while quantifying the resulting accuracy/cost tradeoff between two competing ways of handling non-unit-box domains.

---

## Topic List

1. **Reachability Analysis for Hybrid and Polynomial Dynamical Systems** : [[Reachability-Analysis-for-Hybrid-and-Polynomial-Dynamical-Systems|Link]]
   - Discrete-time dynamical systems and reachable sets : [[Reachability-Analysis-for-Hybrid-and-Polynomial-Dynamical-Systems|Link]]
   - Safety verification via reachable set over-approximation : [[Reachability-Analysis-for-Hybrid-and-Polynomial-Dynamical-Systems|Link]]
   - Sources of non-determinism in hybrid system behavior : [[Reachability-Analysis-for-Hybrid-and-Polynomial-Dynamical-Systems|Link]]
   - Discretization of continuous-time dynamics into difference equations
   - The wrapping effect and enclosure methods

2. **Template Polyhedra as an Abstract Domain** : [[Template-Polyhedra-as-an-Abstract-Domain|Link]]
   - Convex polyhedra and their vertex/inequality representations : [[Template-Polyhedra-as-an-Abstract-Domain|Link]]
   - Template matrices and polyhedral coefficient vectors : [[Template-Polyhedra-as-an-Abstract-Domain|Link]]
   - Ordering and inclusion of template polyhedra : [[Template-Polyhedra-as-an-Abstract-Domain|Link]]
   - Boolean and geometric operations on polyhedra : [[Template-Polyhedra-as-an-Abstract-Domain|Link]]
   - Template polyhedra versus general convex polyhedra and named special cases : [[Template-Polyhedra-as-an-Abstract-Domain|Link]]

3. **The Bernstein Expansion of Polynomials** : [[The-Bernstein-Expansion-of-Polynomials|Link]]
   - Power-base versus Bernstein-base representation of a polynomial : [[The-Bernstein-Expansion-of-Polynomials|Link]]
   - Bernstein polynomials and Bernstein coefficients : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link1]], [[Related-Approaches-to-Nonlinear-Reachability|Link2]], [[The-Bernstein-Expansion-of-Polynomials|Link3]]
   - The convex-hull property and control points
   - Sharpness of Bernstein coefficients at vertices : [[Related-Approaches-to-Nonlinear-Reachability|Link]]
   - Validity of the Bernstein expansion restricted to the unit box

4. **Computing Affine Bound Functions from Bernstein Coefficients** : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]
   - Upper and lower bound functions : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]
   - Constant bound functions from the minimum control point : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]
   - The convex-hull lower facet method : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]
   - The linear least squares approximation method : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]
   - Comparative complexity of the two bound-function methods : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]

5. **Mapping General Polyhedra to the Unit Box** : [[Mapping-General-Polyhedra-to-the-Unit-Box|Link]]
   - Oriented and axis-aligned box approximation
   - Composition of the polynomial with an affine transformation
   - Principal Component Analysis for oriented bounding boxes
   - Change of variables via convex combination of polyhedron vertices
   - Exactness of the change-of-variables mapping versus box-approximation error

6. **The Reachable Set Computation Algorithm** : [[The-Reachable-Set-Computation-Algorithm|Link]]
   - Formulating the image-of-a-polyhedron problem as polynomial optimization : [[The-Reachable-Set-Computation-Algorithm|Link]]
   - Reducing polynomial optimization to linear programming via bound functions
   - Per-template-row optimization and the correctness theorem
   - The overall iterative algorithm structure

7. **Approximation Error and Computational Complexity** : [[Approximation-Error-and-Computational-Complexity|Link]]
   - Quadratic convergence of the Bernstein bound-function error : [[Approximation-Error-and-Computational-Complexity|Link1]], [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link2]]
   - Box subdivision for improved accuracy : [[Approximation-Error-and-Computational-Complexity|Link]]
   - Complexity of box approximation versus change of variables : [[Approximation-Error-and-Computational-Complexity|Link]]
   - Complexity of the convex-hull-facet method versus least-squares method : [[Approximation-Error-and-Computational-Complexity|Link]]

8. **Experimental Evaluation on Control and Biological Systems** : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
   - The Duffing oscillator as a hybrid switched-control benchmark : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
   - Michaelis-Menten enzyme kinetics as a biochemical network benchmark : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
   - The FitzHugh-Nagumo neuron model and limit-cycle observation : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
   - Scalability experiments on randomly generated polynomial systems : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
   - Template-direction count as an accuracy/cost knob : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]

9. **Related Approaches to Nonlinear Reachability** : [[Related-Approaches-to-Nonlinear-Reachability|Link]]
   - Piecewise-linear hybridization methods : [[Related-Approaches-to-Nonlinear-Reachability|Link]]
   - The predecessor Bézier-simplex method and its mesh-computation bottleneck : [[Related-Approaches-to-Nonlinear-Reachability|Link]]
   - Other applications of the Bernstein expansion (control, program analysis, barrier certificates, polynomial invariants)

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 3–4)

**Summary:** Introduces hybrid systems as combinations of continuous vector-field dynamics and discrete mode transitions, frames safety verification as proving unreachability of unsafe states, and identifies computing the reachable set of the continuous dynamics — here restricted to a discrete-time polynomial map $x[k+1] = \pi(x[k])$ — as the central technical obstacle the paper addresses, motivated by applications in embedded control and discrete-time biochemical network models. : [[Mapping-General-Polyhedra-to-the-Unit-Box|Link]]

**Key Definitions & Concepts:**
- **Hybrid system** — a system combining continuous modes (each with a vector field active on a staying set $X \subseteq \mathbb{R}^n$) and discrete transitions triggered by guard conditions.
- **Reachable set** — the set of all states visited by all trajectories starting from an initial set $X_0$.
- **Non-determinism sources** — uncertain continuous input, simultaneously enabled discrete transitions, and uncertain/set-valued initial conditions.
- **Polynomial dynamical system** — $x[k+1] = \pi(x[k])$ where $\pi : \mathbb{R}^n \to \mathbb{R}^n$ is multivariate polynomial (Eq. 1).
- **Predecessor Bézier-simplex method** — the authors' earlier approach, limited to dimension 3–4 by expensive mesh computation, which this paper's template-polyhedra approach supersedes.

**Key Questions:**
1. Why does safety verification of a hybrid system require reasoning about *sets* of trajectories rather than single solutions, even when uncertainty enters only through the initial state?
2. What specifically made the earlier Bézier-simplex-based method computationally infeasible beyond dimension 3–4, and what design choice in this paper's approach avoids that bottleneck?

---

### Chapter 2: Preliminaries (pp. 5–6)

**Summary:** Fixes notation (multi-indices, vector/matrix conventions, the unit box $B = [0,1]^n$), formally defines the reachable-set recurrence $X_{k+1} = \pi(X_k)$, and introduces template polyhedra $\langle H, c \rangle$ as the fixed-shape convex representation used to over-approximate reachable sets, noting their computational advantage over general convex polyhedra for Boolean and geometric operations.

**Key Definitions & Concepts by Section:**
- **2.1 Reachable sets** — image of a set under $\pi$: $\pi(X) = \{(\pi_1(x), \ldots, \pi_n(x)) \mid x \in X\}$; the reachable-set recurrence $X_{k+1} = \pi(X_k)$.
- **2.2 Template polyhedra** — convex polyhedron as $Ax \leq b$; template matrix $H$ (rows $H^i$ are linear functionals); polyhedral coefficient vector $c$; template polyhedron $\langle H, c \rangle = \bigwedge_i H^i x \leq c_i$; the order $c \preceq c'$ inducing inclusion $\langle H, c\rangle \subseteq \langle H, c'\rangle$; ranges and octagon domains as special-case templates. : [[Template-Polyhedra-as-an-Abstract-Domain|Link]]

**Key Questions:**
1. Why does fixing the template matrix $H$ in advance (rather than allowing arbitrary facet normals, as in general convex polyhedra) make the subsequent optimization problem tractable?
2. In what sense is the ordering $c \preceq c'$ on polyhedral coefficient vectors a lattice structure on the abstract domain of template polyhedra, and why does that matter for iterating the reachability recurrence?

---

### Chapter 3: Reachable Set Approximation Using Template Polyhedra (pp. 5–8)

**Summary:** States the core computational problem — finding a coefficient vector $c$ such that $\pi(P) \subseteq \langle H, c\rangle$ — as a polynomial optimization problem (maximizing $\sum_k H^i_k \pi_k(x)$ over $x \in P$ for each template row), and motivates replacing this with a linear program via affine bound functions, introducing the Bernstein expansion as the tool for constructing such bounds. : [[Template-Polyhedra-as-an-Abstract-Domain|Link1]], [[The-Reachable-Set-Computation-Algorithm|Link2]]

**Key Definitions & Concepts by Section:**
- **3.1 The Bernstein expansion** — polynomial in power base $\pi(x) = \sum_{i \in I_d} a_i x^i$; Bernstein polynomial $B_{d,i}(x) = \beta_{d_1,i_1}(x_1)\cdots\beta_{d_n,i_n}(x_n)$; Bernstein-form representation $\pi(x) = \sum_{i \in I_d} b_i B_{d,i}(x)$ on $B = [0,1]^n$; Bernstein coefficients $b_i = \sum_{j \le i} \binom{j}{i}\big/\binom{d}{i}\, a_j$ (Eq. 6); **Lemma 1** — the convex-hull property ($\text{Conv}\{(x,\pi(x))\} \subseteq \text{Conv}\{(i/d, b_i)\}$), the bounding-box enclosure corollary, and sharpness of Bernstein coefficients at the vertices of $I_d$ ($b_i = \pi(i/d)$ there). : [[The-Bernstein-Expansion-of-Polynomials|Link]]

**Key Questions:**
1. Why is the convex-hull property (Lemma 1, part 1) exactly the fact that licenses using Bernstein control points as an *over-approximation* device rather than an exact one?
2. The Bernstein expansion (Eq. 5) is stated as valid only for $x \in B = [0,1]^n$ — what problem does this restriction create for iterating the reachability recurrence beyond the first step, and how does the paper flag this as needing a separate solution (addressed in Chapter 5)?

---

### Chapter 4: Computing Bound Functions Over the Unit Box Domain (pp. 7–10)

**Summary:** Defines upper/lower affine bound functions for a polynomial with respect to a set, and presents two concrete methods — using a convex-hull lower facet, and using linear least squares — for deriving a tight affine lower bound from the Bernstein control points, restricted to the case where the domain is exactly the unit box. : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Using a convex hull lower facet** — trivial constant bound $l(x) = b_0 = \min_i b_i$; iterative construction of a sequence of affine lower bounds $l_1, \ldots, l_n$, each hyperplane pivoting through a chosen control point in a direction orthogonal to prior directions, terminating at $l_n$ passing through a lower facet of the control-point convex hull. : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]
- **4.2 Using a linear least squares approximation** — fits a "median" hyperplane $\tilde{l}(x) = \sum_k \zeta_k x_k + \zeta_{n+1}$ to all control points via the normal equations $A^TA\zeta = A^Tb$, then shifts it downward by $\delta = \max_j(\tilde{l}(i^j/d) - b_j)$ to guarantee it is a valid lower bound. : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]
- **Lemma 2** — bound functions are monotone under subset inclusion of the reference domain ($Y \subseteq X$ preserves bound validity).

**Key Questions:**
1. Why does computing an *upper* bound function reduce to computing a *lower* bound function of $-\pi$ and negating — what symmetry of the Bernstein coefficients makes this valid?
2. What is the essential tradeoff between the convex-hull-facet method (Section 4.1) and the least-squares method (Section 4.2) in terms of tightness of the resulting bound versus computational cost, and how is this later confirmed empirically in Chapter 8?

---

### Chapter 5: Computing Affine Bound Functions Over Polyhedral Domains (pp. 10–12)

**Summary:** Extends the unit-box-only bound-function machinery of Chapter 4 to arbitrary bounded convex polyhedra by two competing transformations: approximating the polyhedron by an (oriented) bounding box composed with the polynomial, versus an exact change of variables expressing points as convex combinations of the polyhedron's vertices. : [[Computing-Affine-Bound-Functions-from-Bernstein-Coefficients|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Using a box approximation** — affine map $\tau(x) = \text{diag}(\lambda)x + g$ sending the unit box to a bounding box $\overline{B}$ of $P$; composed polynomial $\gamma = \pi \circ \tau$; **Lemma 3** — $\pi(P) \subseteq \gamma(B)$, proved via $\tau(B) = \overline{B}$ and $P \subseteq \overline{B}$; oriented (non-axis-aligned) bounding boxes computed via Principal Component Analysis for tighter approximation. : [[Approximation-Error-and-Computational-Complexity|Link]]
- **5.2 Using a change of variables** — expressing $x \in P$ as $x = \sum_j \alpha_j v^j$ over the vertex set $V$ subject to $\alpha_j \geq 0, \sum_j \alpha_j = 1$; substituted polynomial $\mu = \pi \circ \nu$; elimination of the redundant $\alpha_l$ to obtain $\xi(\tilde\alpha)$ over $(l-1)$ variables in a genuine unit box $B_{\tilde\alpha}$, so that bound functions computed there introduce *no additional approximation error* beyond what template polyhedra already induce. : [[Approximation-Error-and-Computational-Complexity|Link]]

**Key Questions:**
1. Why does the box-approximation route (5.1) necessarily introduce error beyond that of the Bernstein bound functions themselves, while the change-of-variables route (5.2) does not — what is the source of that extra error in Lemma 3's proof?
2. The change-of-variables method requires the polyhedron's vertex set $V$ explicitly — what does this imply for its scalability compared to box approximation, and how does this connect to the complexity discussion in Chapter 7 and the experimental results in Chapter 8?

---

### Chapter 6: Reachable Set Computation (pp. 11–14)

**Summary:** Assembles the previous machinery into the full per-step reachability algorithm: derives the linear-programming reformulation of the template-coefficient optimization (bounding each polynomial component separately rather than composing them into $H$-weighted sums), states the overall algorithm and its correctness theorem, and notes a refinement using the mapped-back domain $\tau^{-1}(X_k)$ for improved accuracy. : [[The-Reachable-Set-Computation-Algorithm|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Image computation** — reformulating each template optimization $c_i = \max s_i(x)$ (Eq. 9, with $s_i = \sum_k H^i_k \pi_k$) as a per-component sum $c_i = \sum_k H^i_k \omega_k$ (Eq. 10) using per-component upper/lower bound functions $u_k, l_k$, with sign of $H^i_k$ selecting which bound applies; **Lemma 4** — a coefficient vector satisfying (10) also satisfies (3)/(4), i.e. still yields a valid over-approximation, at the cost of looser bounds than direct composition. : [[Mapping-General-Polyhedra-to-the-Unit-Box|Link]]
- **6.2 Reachable set computation algorithm** — **Algorithm 1**: per iteration, compute the unit-box map $\beta$ (`UnitBoxMap`), compose $\gamma = \pi \circ \beta$, compute bound functions $(u,l)$ (`BoundFunctions`), solve for coefficients $\bar c$ via LP (`PolyApp`), and update $X_{k+1} = \langle H, \bar c\rangle$; **Theorem 1** — correctness ($\pi(P) \subseteq \langle H, \bar c\rangle$); the remark that bound functions computed w.r.t. $B$ remain valid (and can be resolved more tightly) w.r.t. the smaller domain $\tau^{-1}(X_k)$. : [[The-Reachable-Set-Computation-Algorithm|Link]]

**Key Questions:**
1. Why is bounding each $\pi_k$ separately (Eq. 10) sound but generally *looser* than directly bounding the composed sum $s_i$ (Eq. 9) — what is lost by decoupling the per-row weighted sum from the per-component bound functions?
2. How does Algorithm 1's use of $2n$ linear programs (per Lemma 4's remark) versus $m$ polynomial optimizations (the naive formulation, Eq. 4) change the asymptotic character of each reachability step?

---

### Chapter 7: Approximation Error and Computation Cost (pp. 13–14)

**Summary:** Analyzes the sources of over-approximation error (bound-function looseness, template-polyhedra abstraction, and box-approximation slack) and states a quadratic-convergence result for the Bernstein-based bound functions in box size, then compares the asymptotic linear-algebra cost of the box-approximation and change-of-variables routes and of the two bound-function methods. : [[Approximation-Error-and-Computational-Complexity|Link]]

**Key Definitions & Concepts:**
- **Lemma 5** — the piecewise-linear interpolant $C_{\pi,B}$ of the Bernstein control points satisfies $|\pi(x) - C_{\pi,B}(x)| \leq K\rho^2(B)$ for $x \in B$, where $\rho(B)$ is the box's largest side length and $K$ bounds second partial derivatives of $\pi$ on $B$ — i.e. approximation error is quadratic in box size.
- **Box subdivision** — dividing $B$ into non-overlapping sub-boxes, computing per-sub-box bound functions, and taking the tightest resulting coefficient per template row, trading computation for accuracy.
- Complexity comparison: change-of-variables solves LPs in dimension $(l-1)$ (vertex count) versus box approximation's dimension $n$; convex-hull-facet method costs roughly $O((n-1)^2n^2/4)$ versus least-squares' $O((n+1)^2)$ for the underlying linear solves, though least squares pays extra for large control-point-count matrix multiplication.

**Key Questions:**
1. What does the quadratic-convergence result of Lemma 5 predict about the payoff of box subdivision, and why would this predict diminishing but still worthwhile returns as sub-boxes shrink?
2. Given the asymptotic complexity figures for convex-hull-facet versus least-squares bound-function methods, why does the paper still find (per Chapter 8's Table 2) that least squares becomes *less* efficient at high dimension despite comparable formula-level complexity?

---

### Chapter 8: Experimental Results (pp. 14–21)

**Summary:** Validates the two unit-box-mapping methods (box approximation, BA, versus change of variables, CV) and the two bound-function methods (CHF versus LSA) on three concrete dynamical systems — a switched Duffing oscillator, Michaelis-Menten enzyme kinetics, and the FitzHugh-Nagumo neuron model — plus a scalability study on randomly generated polynomial systems, consistently finding CV more accurate but more expensive than BA, and CHF competitive with or faster than LSA at higher dimension. : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Duffing oscillator** — a switched hybrid model with a 3-mode predictive control law and cubic nonlinearity $\ddot y + 2\zeta\dot y + y + y^3 = u$; CV achieves tighter reachable sets than BA at higher time cost (1.25s vs. 3.96s over 80 steps). : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
- **8.2 Michaelis-Menten enzyme kinetics** — a 4-variate polynomial system from a Runge-Kutta discretization of enzyme-substrate reaction ODEs; CV again more precise but far more expensive (153.5s vs. 11.7s for 20 steps) due to many monomial terms inflating Bernstein-coefficient count. : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
- **8.3 FitzHugh-Nagumo neuron model** — a 2D polynomial system from Euler-discretized neuron ODEs; CV recovers a limit cycle that BA misses at comparable template count; increasing template directions from 8 to 20 sharply improves precision at roughly linear extra cost. : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]
- **8.4 Randomly generated systems** — scalability tables (Table 1: BA vs. CV computation time by dimension/degree; Table 2: LSA vs. CHF bound-function time by dimension) showing computation time grows linearly in step count and exponentially harder for CV/LSA as dimension and monomial count grow; testing capped near dimension 9 due to symbolic polynomial-composition cost. : [[Experimental-Evaluation-on-Control-and-Biological-Systems|Link]]

**Key Questions:**
1. Across all three case studies, why does the accuracy advantage of the change-of-variables method scale worse with the number of monomial terms (as in Michaelis-Menten) than with state-space dimension alone?
2. What does the observed "roughly linear in step count" growth of computation time (Section 8.4) reveal about where the real cost bottleneck sits — is it the LP solves, the bound-function computation, or the polyhedral bookkeeping — and how is this consistent with the complexity analysis in Chapter 7?

---

### Chapter 9: Related Work and Conclusion (pp. 21–23)

**Summary:** Situates the paper's approach among hybridization-based reachability methods (which require nonlinear optimization) and its own Bézier-simplex predecessor (which requires expensive triangulation with growing geometric complexity), argues that combining template polyhedra with Bernstein-derived bound functions strikes a favorable accuracy/cost tradeoff, surveys other applications of the Bernstein expansion (control, program analysis, barrier certificates, polynomial invariants), and closes by identifying open directions: sparse-polynomial composition via blossoming, and extension to embedded control software verification. : [[Related-Approaches-to-Nonlinear-Reachability|Link]]

**Key Definitions & Concepts:**
- **Hybridization methods** — approximate nonlinear dynamics by a piecewise-linear model, generally requiring nonlinear optimization to construct, contrasted with this paper's LP-only approach.
- **Bézier-simplex method** (the authors' prior work) — same convex-hull idea via Bézier simplices, but requiring expensive triangulation with reachable-set geometric complexity that can grow over iterations, unlike the fixed-shape template polyhedra used here.
- Other Bernstein-expansion applications noted: robust control, symbolic program-analysis range computation, barrier certificates for hybrid safety verification, and polynomial invariant generation.

**Key Questions:**
1. In what precise sense do the authors claim their method and the Bézier-simplex method have the "same" quadratic convergence rate when using enough templates — and what, then, is the actual argument for preferring template polyhedra if not asymptotic accuracy?
2. Which of the paper's stated future directions (sparse polynomial composition via blossoming, symbolic Bernstein-coefficient computation via interpolation, embedded-control-software verification) most directly addresses the scalability limit exposed by the dimension-9 ceiling in the random-systems experiments (Section 8.4)?

---
