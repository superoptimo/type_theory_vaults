# Reachability Analysis for Linear Systems with Uncertain Parameters using Polynomial Zonotopes — Index

[[book-guidelines|↩ Back to guidelines]]

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
