# Constraint Propagation: Models, Techniques, Implementation — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Constraint Satisfaction and Propagation-Based Solving** : [[Constraint-Satisfaction-and-Propagation-Based-Solving|Link]]
   - Constraint satisfaction problems as variables, domains, and constraints : [[Constraint-Satisfaction-and-Propagation-Based-Solving|Link]]
   - Modeling combinatorial problems (Sudoku, social golfers, scheduling)
   - Constraint propagation and search as complementary inference methods : [[Constraint-Satisfaction-and-Propagation-Based-Solving|Link]]
   - The generate-and-test baseline and its inefficiency
   - Set constraints and their symmetry-avoidance advantage : [[Constraint-Satisfaction-and-Propagation-Based-Solving|Link]]

2. **The Denotational and Operational Model of Constraint Propagation** : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - Assignments, constraints, and domains : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - Constraint satisfaction problems (CSPs) versus propagation problems (PPs) : [[Constraint-Satisfaction-and-Propagation-Based-Solving|Link1]], [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link2]]
   - Propagators as contracting and sound functions on domains : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - The induced constraint of a propagator : [[Deriving-Propagators-for-Boolean-Set-Constraints|Link1]], [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link2]]
   - Propagation as a non-deterministic transition system : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - Termination and mutual fixed points
   - Idempotency and monotonicity of propagators : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - Confluence and non-confluence of non-monotonic propagation : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - The propagator lattice : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - Many-sorted extension of the model : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]

3. **Propagation Strength and Domain Approximations** : [[Propagation-Strength-and-Domain-Approximations|Link]]
   - Unique weakest and strongest propagators for a constraint : [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|Link]]
   - Domain completeness and domain relaxation : [[Propagation-Strength-and-Domain-Approximations|Link]]
   - Domain systems as approximations of the full domain lattice : [[Propagation-Strength-and-Domain-Approximations|Link]]
   - Completeness and consistency with respect to a domain system
   - $\mathcal D$-Dom and Dom-$\mathcal D$ completeness : [[Propagation-Strength-and-Domain-Approximations|Link]]
   - Bounds(Z), bounds(D), bounds(R), and range consistency for integers
   - The set interval approximation for set variables : [[Propagation-Strength-and-Domain-Approximations|Link1]], [[Range-Iterators-for-Set-Valued-Domain-Operations|Link2]]
   - Trade-offs between propagation strength and algorithmic tractability

4. **Efficient Propagator Scheduling** : [[Efficient-Propagator-Scheduling|Link]]
   - Propagator-centered propagation and the agenda : [[Efficient-Propagator-Scheduling|Link]]
   - Admissible spaces and the agenda invariant : [[Efficient-Propagator-Scheduling|Link]]
   - Priority queues and FIFO fairness versus starvation : [[Efficient-Propagator-Scheduling|Link]]
   - Event-directed scheduling and the dependency invariant : [[Efficient-Propagator-Scheduling|Link]]
   - Dynamic dependencies, subsumption, and propagator rewriting : [[Efficient-Propagator-Scheduling|Link]]
   - Watched literals and losing interest in variables : [[Efficient-Propagator-Scheduling|Link1]], [[Range-Iterators-for-Set-Valued-Domain-Operations|Link2]]
   - Self-rescheduling propagators and fixed-point detection : [[Efficient-Propagator-Scheduling|Link]]
   - Staged propagators combining multiple propagation algorithms : [[Efficient-Propagator-Scheduling|Link]]
   - Propagation conditions and modification events : [[Efficient-Propagator-Scheduling|Link]]
   - Variable-centered versus propagator-centered propagation : [[Efficient-Propagator-Scheduling|Link]]

5. **Implementation Architecture of a Propagation Kernel** : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]
   - Copying with recomputation versus trailing for backtracking : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]
   - Batch recomputation and non-monotonicity : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]
   - The kernel/domain-module boundary : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]
   - Contracts between propagators, variables, and the kernel
   - Dependency arrays and the bucket priority queue : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]
   - Efficient subsumption detection and propagator disposal : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]
   - Copying spaces via forwarding pointers : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]
   - The Gecode constraint solver as a validating implementation : [[Implementation-Architecture-of-a-Propagation-Kernel|Link]]

6. **Views and Derived Propagators** : [[Views-and-Derived-Propagators|Link]]
   - Views as input/output transformations on propagators : [[Views-and-Derived-Propagators|Link]]
   - Correctness and completeness preservation of derived propagators
   - $\mathcal D$-injective, $\mathcal D$-surjective, and $\mathcal D$-bijective views
   - Composability, fixed-point preservation, and subsumption of derived propagators : [[Views-and-Derived-Propagators|Link]]
   - Transformation via negation, minus, and complement views : [[Views-and-Derived-Propagators|Link]]
   - Generalization via offset and scale views : [[Views-and-Derived-Propagators|Link]]
   - Specialization via constant views : [[Views-and-Derived-Propagators|Link]]
   - Type conversion between variable representations : [[Views-and-Derived-Propagators|Link]]
   - Limitations of the views approach : [[Views-and-Derived-Propagators|Link]]

7. **Implementing Views Efficiently** : [[Implementing-Views-Efficiently|Link]]
   - Parametricity via functional, dynamic-binding, and parametric-polymorphism styles
   - Parametric propagators and monomorphization in C++
   - Event handling and modification-event translation under views : [[Implementing-Views-Efficiently|Link]]
   - Empirical code-reuse and performance evaluation of views in Gecode

8. **Range Iterators for Set-Valued Domain Operations** : [[Range-Iterators-for-Set-Valued-Domain-Operations|Link]]
   - Range sequences and the range iterator interface : [[Range-Iterators-for-Set-Valued-Domain-Operations|Link]]
   - Computing directly with iterators (intersection, union, difference, complement) : [[Range-Iterators-for-Set-Valued-Domain-Operations|Link]]
   - Cache iterators and value-versus-range iterators
   - Set-valued operations for integer and set views : [[Range-Iterators-for-Set-Valued-Domain-Operations|Link]]
   - Iterators as adaptors between propagator data structures and variable domains : [[Range-Iterators-for-Set-Valued-Domain-Operations|Link]]
   - Limits of compiler optimization for chained set-valued views

9. **Deriving Propagators for Boolean Set Constraints** : [[Deriving-Propagators-for-Boolean-Set-Constraints|Link]]
   - The Boolean set constraint specification language : [[Deriving-Propagators-for-Boolean-Set-Constraints|Link]]
   - Equation normal form and variable isolation via Shannon expansion : [[Deriving-Propagators-for-Boolean-Set-Constraints|Link]]
   - Interval normal forms and set-interval-complete propagation
   - Negation of Boolean set constraints and its added expressivity : [[Deriving-Propagators-for-Boolean-Set-Constraints|Link]]
   - Subsumption, entailment, and reification of set constraints : [[Deriving-Propagators-for-Boolean-Set-Constraints|Link]]
   - Common subexpression elimination for linear-time n-ary propagation : [[Deriving-Propagators-for-Boolean-Set-Constraints|Link]]
   - Reduced Ordered Binary Decision Diagrams (ROBDDs) for constraint compilation
   - Interpreted versus compiled propagator implementation : [[Efficient-Propagator-Scheduling|Link1]], [[Deriving-Propagators-for-Boolean-Set-Constraints|Link2]], [[Empirical-Evaluation-and-Benchmarking|Link3]]

10. **Empirical Evaluation and Benchmarking** : [[Empirical-Evaluation-and-Benchmarking|Link]]
    - Gecode as the empirical validation platform : [[Empirical-Evaluation-and-Benchmarking|Link]]
    - Benchmark problem classes (integer/Boolean, set, SAT, stress tests)
    - Comparative performance against ILOG Solver and SICStus Prolog
    - Design-decision experiments (subsumption, suspension lists, staging)

11. **Open Problems and Future Directions** : [[Open-Problems-and-Future-Directions|Link]]
    - Concurrent and parallelized constraint propagation : [[Open-Problems-and-Future-Directions|Link]]
    - Approximative, randomized, or heuristic non-monotonic propagators : [[Open-Problems-and-Future-Directions|Link]]
    - Hybrid copying/trailing solver architectures : [[Open-Problems-and-Future-Directions|Link]]
    - Extending set-interval completeness to richer constraint classes : [[Open-Problems-and-Future-Directions|Link]]
    - Cardinality reasoning for set constraints : [[Open-Problems-and-Future-Directions|Link]]

---
