# Handbook of Constraint Programming — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Foundations and History of Constraint Satisfaction** : [[Foundations-and-History-of-Constraint-Satisfaction|Link]]
   - The language stream and the algorithm stream
   - Constraint satisfaction problems as declarative representation and reasoning : [[Modelling-Constraint-Satisfaction-Problems|Link]]
   - NP-hardness of general CSPs

2. **Constraint Propagation and Local Consistency** : [[Constraint-Propagation-and-Local-Consistency|Link]]
   - Arc consistency : [[Constraint-Propagation-and-Local-Consistency|Link1]], [[Continuous-and-Interval-Constraints|Link2]]
   - Higher-order consistencies : [[Constraint-Propagation-and-Local-Consistency|Link]]
   - Domain-based consistencies stronger than arc consistency : [[Constraint-Propagation-and-Local-Consistency|Link]]
   - Domain-based consistencies weaker than arc consistency : [[Constraint-Propagation-and-Local-Consistency|Link]]
   - Constraint propagation as iteration of reduction rules : [[Constraint-Propagation-and-Local-Consistency|Link]]

3. **Backtracking Search** : [[Backtracking-Search|Link]]
   - Branching strategies : [[Backtracking-Search|Link]]
   - Constraint propagation during search : [[Backtracking-Search|Link]]
   - Nogood recording : [[Backtracking-Search|Link]]
   - Non-chronological backtracking and backjumping : [[Backtracking-Search|Link]]
   - Variable and value ordering heuristics : [[Backtracking-Search|Link]]
   - Randomization and restart strategies : [[Backtracking-Search|Link]]
   - Best-first search and branch and bound optimization : [[Backtracking-Search|Link]]

4. **Local Search Methods** : [[Local-Search-Methods|Link]]
   - Randomised iterative improvement algorithms : [[Local-Search-Methods|Link]]
   - Tabu search and related algorithms : [[Global-Constraints|Link]]
   - Penalty-based local search algorithms : [[Local-Search-Methods|Link]]
   - Local search for constraint optimisation problems : [[Local-Search-Methods|Link]]
   - Frameworks and toolkits for local search : [[Local-Search-Methods|Link]]

5. **Global Constraints** : [[Global-Constraints|Link]]
   - The all-different constraint : [[Global-Constraints|Link1]], [[Soft-Constraints-and-Preferences|Link2]], [[Symmetry-in-Constraint-Programming|Link3]], [[Modelling-Constraint-Satisfaction-Problems|Link4]]
   - Complete filtering algorithms via graph, flow, and matching theory
   - Optimization constraints : [[Applications-Scheduling-Planning-and-Vehicle-Routing|Link1]], [[Global-Constraints|Link2]]
   - Partial filtering algorithms : [[Global-Constraints|Link1]], [[Integration-of-Constraint-Programming-and-Operations-Research|Link2]], [[Backtracking-Search|Link3]]
   - Global variables : [[Global-Constraints|Link]]

6. **Tractability and Computational Complexity of CSPs** : [[Tractability-and-Computational-Complexity-of-CSPs|Link]]
   - Structure-based tractability and tree-width : [[Tractability-and-Computational-Complexity-of-CSPs|Link]]
   - Hybrids of search and inference : [[Soft-Constraints-and-Preferences|Link1]], [[Tractability-and-Computational-Complexity-of-CSPs|Link2]]
   - The algebraic theory of constraint languages : [[Tractability-and-Computational-Complexity-of-CSPs|Link]]
   - Dichotomy results for constraint satisfaction complexity : [[Randomness-and-Phase-Transitions|Link1]], [[Modelling-Constraint-Satisfaction-Problems|Link2]], [[Temporal-Constraint-Satisfaction|Link3]], [[Foundations-and-History-of-Constraint-Satisfaction|Link4]]
   - Constraint languages over infinite or multi-sorted domains : [[Constraints-over-Structured-Domains|Link]]

7. **Soft Constraints and Preferences** : [[Soft-Constraints-and-Preferences|Link]]
   - Specific soft constraint frameworks (fuzzy, weighted, probabilistic)
   - Generic soft constraint frameworks (semiring- and valued-CSP-based)
   - Relations among soft constraint frameworks : [[Soft-Constraints-and-Preferences|Link1]], [[Integration-of-Constraint-Programming-and-Operations-Research|Link2]]
   - Search and inference for soft constraints : [[Integration-of-Constraint-Programming-and-Operations-Research|Link1]], [[Continuous-and-Interval-Constraints|Link2]], [[Modelling-Constraint-Satisfaction-Problems|Link3]], [[Temporal-Constraint-Satisfaction|Link4]]

8. **Symmetry in Constraint Programming** : [[Symmetry-in-Constraint-Programming|Link]]
   - Symmetry and group theory : [[Symmetry-in-Constraint-Programming|Link]]
   - Reformulation to remove symmetry : [[Symmetry-in-Constraint-Programming|Link]]
   - Symmetry-breaking constraints added before search : [[Symmetry-in-Constraint-Programming|Link]]
   - Dynamic symmetry breaking during search : [[Symmetry-in-Constraint-Programming|Link]]

9. **Modelling Constraint Satisfaction Problems** : [[Modelling-Constraint-Satisfaction-Problems|Link]]
   - Choosing a problem viewpoint : [[Modelling-Constraint-Satisfaction-Problems|Link]]
   - Auxiliary variables : [[Modelling-Constraint-Satisfaction-Problems|Link]]
   - Implied constraints : [[Modelling-Constraint-Satisfaction-Problems|Link]]
   - Reformulation of CSPs : [[Modelling-Constraint-Satisfaction-Problems|Link]]
   - Combining viewpoints : [[Modelling-Constraint-Satisfaction-Problems|Link]]
   - Symmetry and modelling : [[Modelling-Constraint-Satisfaction-Problems|Link]]

10. **Constraint Logic Programming** : [[Constraint-Logic-Programming|Link]]
    - History and semantics of CLP : [[Constraint-Logic-Programming|Link]]
    - CLP for conceptual and design modeling : [[Constraint-Logic-Programming|Link]]
    - Search strategies in CLP : [[Constraint-Logic-Programming|Link1]], [[Backtracking-Search|Link2]]

11. **Constraints in Procedural, Concurrent, and Rule-Based Languages** : [[Constraints-in-Procedural-Concurrent-and-Rule-Based-Languages|Link]]
    - Constraints in procedural and object-oriented languages : [[Constraints-in-Procedural-Concurrent-and-Rule-Based-Languages|Link]]
    - Concurrent constraint programming : [[Constraints-in-Procedural-Concurrent-and-Rule-Based-Languages|Link]]
    - Rule-based constraint languages : [[Constraints-in-Procedural-Concurrent-and-Rule-Based-Languages|Link]]

12. **Finite Domain Constraint Programming Systems** : [[Finite-Domain-Constraint-Programming-Systems|Link]]
    - Architecture of a constraint programming system : [[Finite-Domain-Constraint-Programming-Systems|Link1]], [[Constraints-in-Procedural-Concurrent-and-Rule-Based-Languages|Link2]], [[Distributed-Constraint-Programming|Link3]]
    - Implementing constraint propagation : [[Applications-Scheduling-Planning-and-Vehicle-Routing|Link1]], [[Backtracking-Search|Link2]], [[Constraint-Propagation-and-Local-Consistency|Link3]], [[Finite-Domain-Constraint-Programming-Systems|Link4]]
    - Implementing search : [[Finite-Domain-Constraint-Programming-Systems|Link]]
    - Overview of finite domain solvers : [[Tractability-and-Computational-Complexity-of-CSPs|Link1]], [[Constraints-over-Structured-Domains|Link2]]

13. **Integration of Constraint Programming and Operations Research** : [[Integration-of-Constraint-Programming-and-Operations-Research|Link]]
    - Linear and mixed integer/linear modeling : [[Integration-of-Constraint-Programming-and-Operations-Research|Link]]
    - Cutting planes : [[Integration-of-Constraint-Programming-and-Operations-Research|Link]]
    - Relaxation of global and disjunctive constraints : [[Integration-of-Constraint-Programming-and-Operations-Research|Link]]
    - Lagrangean relaxation : [[Integration-of-Constraint-Programming-and-Operations-Research|Link]]
    - Dynamic programming and branch-and-price : [[Integration-of-Constraint-Programming-and-Operations-Research|Link]]
    - Benders decomposition : [[Integration-of-Constraint-Programming-and-Operations-Research|Link]]

14. **Continuous and Interval Constraints** : [[Continuous-and-Interval-Constraints|Link]]
    - From discrete to continuous constraints : [[Continuous-and-Interval-Constraints|Link]]
    - The branch-and-reduce framework : [[Continuous-and-Interval-Constraints|Link]]
    - Consistency techniques over intervals : [[Continuous-and-Interval-Constraints|Link]]
    - Hybrid symbolic-numeric techniques : [[Continuous-and-Interval-Constraints|Link]]
    - First order constraints : [[Continuous-and-Interval-Constraints|Link1]], [[Temporal-Constraint-Satisfaction|Link2]]

15. **Constraints over Structured Domains** : [[Constraints-over-Structured-Domains|Link]]
    - Constraints over sets and constructed sets : [[Constraints-over-Structured-Domains|Link]]
    - Finite set interval solvers
    - Constraints over maps, relations, and graphs : [[Backtracking-Search|Link1]], [[Constraints-over-Structured-Domains|Link2]]
    - Constraints over lattices and hierarchical trees

16. **Randomness and Phase Transitions** : [[Randomness-and-Phase-Transitions|Link]]
    - Random constraint satisfaction models : [[Randomness-and-Phase-Transitions|Link]]
    - Random satisfiability : [[Randomness-and-Phase-Transitions|Link]]
    - Random problems with structure : [[Randomness-and-Phase-Transitions|Link]]
    - Runtime variability : [[Randomness-and-Phase-Transitions|Link]]

17. **Temporal Constraint Satisfaction** : [[Temporal-Constraint-Satisfaction|Link]]
    - Qualitative and metric temporal formalisms : [[Temporal-Constraint-Satisfaction|Link]]
    - Efficient algorithms for temporal CSPs
    - First-order temporal constraint languages : [[Temporal-Constraint-Satisfaction|Link]]
    - Indefinite constraint databases : [[Temporal-Constraint-Satisfaction|Link]]

18. **Distributed Constraint Programming** : [[Distributed-Constraint-Programming|Link]]
    - Synchronous distributed backtracking : [[Distributed-Constraint-Programming|Link]]
    - Asynchronous distributed backtracking : [[Distributed-Constraint-Programming|Link]]
    - Distributed local search : [[Distributed-Constraint-Programming|Link]]
    - Open constraint programming : [[Distributed-Constraint-Programming|Link]]

19. **Uncertainty and Change in Constraint Problems** : [[Uncertainty-and-Change-in-Constraint-Problems|Link]]
    - Formalisms for uncertain problems (fuzzy, stochastic, mixed CSPs)
    - Problems that change over time : [[Uncertainty-and-Change-in-Constraint-Problems|Link]]
    - Robust solutions and pseudo-dynamic formalisms : [[Uncertainty-and-Change-in-Constraint-Problems|Link]]

20. **Applications: Scheduling, Planning, and Vehicle Routing** : [[Applications-Scheduling-Planning-and-Vehicle-Routing|Link]]
    - Constraint programming models for scheduling : [[Applications-Scheduling-Planning-and-Vehicle-Routing|Link]]
    - Constraint programming models for planning : [[Applications-Scheduling-Planning-and-Vehicle-Routing|Link]]
    - Resource constraint propagation and edge-finding : [[Applications-Scheduling-Planning-and-Vehicle-Routing|Link]]
    - Constraint programming approaches to vehicle routing : [[Applications-Scheduling-Planning-and-Vehicle-Routing|Link]]

21. **Applications: Configuration, Networks, and Bioinformatics** : [[Applications-Configuration-Networks-and-Bioinformatics|Link]]
    - Configuration knowledge and constraint models : [[Continuous-and-Interval-Constraints|Link]]
    - Constraint applications in electricity, water, and data networks
    - Sequence, structure, and function problems in bioinformatics

---
