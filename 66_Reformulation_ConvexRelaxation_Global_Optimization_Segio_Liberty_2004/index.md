# Reformulation and Convex Relaxation Techniques for Global Optimization — Index

[[book-guidelines|↩ Back to guidelines]]

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
