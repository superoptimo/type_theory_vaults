# Modular Constraint Solver Cooperation via Abstract Interpretation — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Abstract Interpretation as a Foundation for Constraint Solving** : [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link]]
   - Concrete domain vs abstract domain vs syntax (the $\Phi$, $D^\flat$, $D^\sharp$ triangle)
   - Concretization function $\gamma$ and the abstraction relationship
   - Under-approximation vs over-approximation of solution sets : [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link]]
   - Soundness of an abstract computation w.r.t. the concrete semantics

2. **Abstract Domains for Constraint Programming** : [[Abstract-Domains-For-Constraint-Programming|Link]]
   - Lattice-based definition of an abstract domain (bottom, top, join) : [[Abstract-Domains-For-Constraint-Programming|Link]]
   - The state function and Kleene logic (true, false, unknown)
   - The interpretation function mapping formulas into an abstract domain : [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link]]
   - Closure as an extensive fixpoint operator eliminating inconsistent values
   - Split as branching/case division of an abstract element
   - The generic propagate-and-search solving algorithm : [[Abstract-Domains-For-Constraint-Programming|Link1]], [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link2]]
   - The box abstract domain over interval lattices : [[Abstract-Domains-For-Constraint-Programming|Link1]], [[Domain-Transformers|Link2]]
   - The octagon abstract domain and difference-bound matrices : [[Abstract-Domains-For-Constraint-Programming|Link1]], [[Domain-Transformers|Link2]]
   - Complexity of closure operators (Floyd-Warshall, incremental variants)

3. **Domain Transformers** : [[Domain-Transformers|Link]]
   - Domain transformers as functors constructing new abstract domains from existing ones
   - Logic completion for adding logical connectors to a constraint language
   - Direct product and coordinatewise combination of abstract domains
   - Formula annotation to route sub-formulas to specific product components
   - Limitation of the direct product: no information exchange between components

4. **Interval Propagators Completion (IPC)** : [[Interval-Propagators-Completion-IPC|Link]]
   - Propagators as extensive, sound functions implementing a single constraint : [[Interval-Propagators-Completion-IPC|Link]]
   - The projection function mapping abstract elements to variable intervals
   - The embed function to avoid spuriously adding variables to unrelated domains
   - Propagator completion as pairing an abstract domain with a set of propagators
   - Soundness of IPC over a direct product of over-approximating domains

5. **Delayed Product (DP)** : [[Delayed-Product-DP|Link]]
   - Delayed goals in logic programming as the inspiration for the delayed product : [[Delayed-Product-DP|Link]]
   - Variable instantiation and constraint rewriting under a fixed value
   - Transferring a constraint from a general domain to a more efficient specialized domain
   - Over-approximated early transfer before full instantiation : [[Delayed-Product-DP|Link]]
   - Partial vs full transfer of a constraint between domains

6. **Shared Product and Modular Composition** : [[Shared-Product-and-Modular-Composition|Link]]
   - Motivation: sharing vs duplicating underlying abstract domains across transformers
   - Named abstract domain declarations and dependencies : [[Domain-Transformers|Link1]], [[Abstract-Domains-For-Constraint-Programming|Link2]], [[Shared-Product-and-Modular-Composition|Link3]]
   - Projection and join functions for dependencies ($\pi$ and $\kappa$)
   - The reduction operator interleaved with closure
   - Fixed-point merging of shared components and the Knaster-Tarski theorem
   - Pointer-based implementation of sharing

7. **Case Study: Flexible Job Shop Scheduling** : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Job shop scheduling as an NP-hard combinatorial problem : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Precedence, non-overlap, and machine-alternative constraints
   - Flexible job shop as a generalization with decision variables for machine assignment : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Crafting abstract domains (FJS1, FJS2) by distributing constraints across components : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Static vs dynamic dispatch of constraints via the delayed product

8. **Implementation and Empirical Evaluation** : [[Implementation-and-Empirical-Evaluation|Link]]
   - The AbSolute solver implemented in OCaml using functors
   - Comparison against GeCode and Chuffed on scheduling benchmarks
   - The dms (domain-min-size / first-fail) search strategy
   - Interpreting $\Delta LB$ bound-quality results across edata and rdata instance sets
   - Trade-offs between cooperation granularity and solving efficiency

9. **Relation to Other Cooperation Frameworks** : [[Relation-to-Other-Cooperation-Frameworks|Link]]
   - Nelson-Oppen theory combination in SMT as a reduced product : [[Relation-to-Other-Cooperation-Frameworks|Link]]
   - Abstract conflict driven clause learning (ACDCL) as fixpoint computation over abstract domains
   - Constraint logic programming (CLP) bridges between uninterpreted-function and arithmetic domains
   - Lazy clause generation as a SAT/propagation hybrid cooperation scheme : [[Relation-to-Other-Cooperation-Frameworks|Link]]

---
