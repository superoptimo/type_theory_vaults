# Daily Production Optimization for Subsea Production Systems: Methods based on mathematical programming and surrogate modelling — Index

[[book-guidelines|↩ Back to guidelines]]

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
