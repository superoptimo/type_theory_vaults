# Reachability Analysis for Polynomial Dynamical Systems Using the Bernstein Expansion — Index

[[book-guidelines|↩ Back to guidelines]]

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
