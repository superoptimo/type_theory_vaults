# Abstract Domains in Constraint Programming — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Abstract Interpretation Foundations** : [[Abstract-Interpretation-Foundations|Link]]
   - Posets lattices and complete lattices : [[Abstract-Interpretation-Foundations|Link1]], [[The-Octagon-Abstract-Domain|Link2]]
   - Galois connections between concrete and abstract domains : [[The-Octagon-Abstract-Domain_alt|Link1]], [[Abstract-Interpretation-Foundations|Link2]]
   - Concrete versus abstract semantics : [[Abstract-Interpretation-Foundations|Link]]
   - Transfer functions for program instructions : [[Abstract-Interpretation-Foundations|Link]]
   - Fixpoints and iterative computation schemes : [[Abstract-Interpretation-Foundations|Link]]
   - Jacobi and Gauss-Seidel iteration strategies
   - Widening operators for accelerating fixpoint convergence
   - Narrowing operators for refining over-approximations : [[Abstract-Interpretation-Foundations|Link]]
   - Local iterations and lower closure operators : [[Abstract-Interpretation-Foundations|Link]]
   - Static program analysis and runtime error proving

2. **Abstract Domains in Abstract Interpretation** : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - Non-relational relational and weakly relational domain families : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - The intervals abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]
   - The polyhedra abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - The ellipsoids abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - The octahedra and zonotopes abstract domains : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - Required operators of an abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - Disjunctive completion : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link2]]
   - Reduced products and domain combination : [[Abstract-Domains-in-Abstract-Interpretation|Link]]

3. **Constraint Satisfaction Problem Foundations** : [[Constraint-Satisfaction-Problem-Foundations|Link]]
   - Definition of a constraint satisfaction problem : [[Constraint-Satisfaction-Problem-Foundations|Link]]
   - Discrete versus continuous domains : [[Constraint-Satisfaction-Problem-Foundations|Link1]], [[Exploration-and-Search-in-Constraint-Programming|Link2]]
   - Domain representations as integer Cartesian products integer boxes and boxes : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Interval arithmetic for continuous constraints : [[Constraint-Satisfaction-Problem-Foundations|Link1]], [[The-AbSolute-Solver|Link2]], [[Consistency-and-Propagation-in-Constraint-Programming|Link3]]
   - True false and maybe constraint evaluation
   - Soundness and completeness of approximations : [[Constraint-Satisfaction-Problem-Foundations|Link]]
   - Over-approximation and under-approximation : [[Constraint-Satisfaction-Problem-Foundations|Link]]

4. **Consistency and Propagation in Constraint Programming** : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Support for a value with respect to a constraint : [[Octagonal-Constraint-Solving|Link]]
   - Generalized arc-consistency : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Bound-consistency : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Hull-consistency : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - The HC4-Revise propagation algorithm : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Propagators and the propagation loop : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Arc-consistency algorithm family AC1 through AC2001
   - Complexity of consistency algorithms

5. **Exploration and Search in Constraint Programming** : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Choice points and the search tree : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Backtracking and backjumping : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Variable choice heuristics including first-fail and dom over wdeg : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Value choice heuristics : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Domain splitting heuristics for continuous variables : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Discrete versus continuous resolution schemes : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Solving mixed discrete-continuous problems : [[Exploration-and-Search-in-Constraint-Programming|Link]]

6. **Links Between Abstract Interpretation and Constraint Programming** : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Shared lattice and fixpoint theoretical framework : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Consistency as a form of narrowing : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Differences in accuracy and completeness philosophy : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Differences in domain representation richness : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Connections to satisfiability solving : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]

7. **Unified Abstract Domains for Constraint Programming** : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - E-consistency as a generalization of existing consistencies
   - The generic splitting operator : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - Formal definition of an abstract domain for constraint programming : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - The unified abstract solving algorithm : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - Termination and completeness conditions for the unified solver : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - Recovering classical CP solvers as instances of the unified framework : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]

8. **The Octagon Abstract Domain** : [[The-Octagon-Abstract-Domain|Link]]
   - Octagonal constraints and their geometric shape : [[The-Octagon-Abstract-Domain_alt|Link]]
   - Closure of octagons under intersection : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The difference bound matrix representation : [[The-Octagon-Abstract-Domain|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]
   - The modified Floyd-Warshall algorithm for octagons : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The intersection of boxes representation : [[The-Octagon-Abstract-Domain|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]
   - Rotated bases and rotated variables : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The octagonal splitting operator : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The octagonal precision function : [[The-Octagon-Abstract-Domain_alt|Link]]
   - Partial octagons : [[The-Octagon-Abstract-Domain|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]

9. **Octagonal Constraint Solving** : [[Octagonal-Constraint-Solving|Link]]
   - Construction of an octagonal CSP from a CSP : [[Octagonal-Constraint-Solving|Link]]
   - Rotated constraints : [[Octagonal-Constraint-Solving|Link]]
   - Oct-consistency : [[Octagonal-Constraint-Solving|Link]]
   - The combined propagation scheme for octagonal and rotated constraints
   - Variable choice heuristics LargestFirst LargestCanFirst LargestOctFirst and Oct-Split
   - Octagonalization heuristics ConstraintBased Random StrongestLink and Promising
   - Experimental comparison of octagons versus intervals on continuous benchmarks : [[Octagonal-Constraint-Solving|Link]]

10. **Abstract Interpretation Reformulation of Constraint Programming** : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - Constraint solving as concrete semantics : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - CP domain representations recast as abstract domains : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - The disjunctive completion of an abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[The-Octagon-Abstract-Domain|Link2]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link3]], [[The-Octagon-Abstract-Domain_alt|Link4]]
    - The split operator and the choice operator : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - Compatibility of the precision function and the splitting operator : [[The-Octagon-Abstract-Domain|Link1]], [[The-AbSolute-Solver|Link2]], [[The-Octagon-Abstract-Domain_alt|Link3]]
    - The generic abstract solving algorithm and its termination proof : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]

11. **The AbSolute Solver** : [[The-AbSolute-Solver|Link]]
    - Implementation on top of the Apron abstract domain library : [[The-AbSolute-Solver|Link]]
    - Problem modelization with mixed integer and real environments : [[The-AbSolute-Solver|Link]]
    - Abstraction and consistency via Apron transfer functions : [[The-AbSolute-Solver|Link]]
    - Linearization of non-linear constraints : [[The-AbSolute-Solver|Link]]
    - The naive splitting operator : [[The-AbSolute-Solver|Link]]
    - Handling the polyhedron abstract domain in practice : [[The-AbSolute-Solver|Link]]
    - Experimental results on continuous and mixed benchmarks : [[The-AbSolute-Solver|Link]]

---
