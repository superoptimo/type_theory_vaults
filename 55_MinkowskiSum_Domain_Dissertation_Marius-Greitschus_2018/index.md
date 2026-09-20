# New Techniques for Abstraction Refinement — Index

[[book-guidelines|↩ Back to guidelines]]

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
