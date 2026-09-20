# Principles of Model Checking — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Model Checking Fundamentals** : [[Model-Checking-Fundamentals|Link]]
   - Model checking as automated exhaustive state exploration : [[Model-Checking-Fundamentals|Link1]], [[Timed-CTL-and-TCTL-Model-Checking|Link2]]
   - The modeling running and analysis phases of the model-checking process : [[Model-Checking-Fundamentals|Link]]
   - Verification versus validation : [[Model-Checking-Fundamentals|Link]]
   - Counterexamples as debugging information : [[Model-Checking-Fundamentals|Link]]
   - Strengths and weaknesses of model checking : [[Automata-Based-LTL-Model-Checking|Link1]], [[CTL-Model-Checking|Link2]], [[Timed-CTL-and-TCTL-Model-Checking|Link3]], [[Model-Checking-Fundamentals|Link4]]
   - Alternative verification techniques such as peer review testing simulation and emulation : [[Model-Checking-Fundamentals|Link]]

2. **Transition Systems as System Models** : [[Transition-Systems-as-System-Models|Link]]
   - Transition system definition : [[Bisimulation-Equivalence|Link1]], [[Transition-Systems-as-System-Models|Link2]]
   - Executions and execution fragments : [[Linear-Time-Properties|Link1]], [[Transition-Systems-as-System-Models|Link2]]
   - Reachable states : [[Safety-Properties-and-Invariants|Link1]], [[Transition-Systems-as-System-Models|Link2]]
   - Determinism in transition systems : [[Transition-Systems-as-System-Models|Link]]
   - Modeling sequential hardware circuits as transition systems : [[Transition-Systems-as-System-Models|Link1]], [[Simulation-Preorders-and-Equivalence|Link2]]
   - Program graphs and guarded conditional transitions : [[Concurrency-and-Communication-Modeling|Link1]], [[Transition-Systems-as-System-Models|Link2]]
   - Unfolding a program graph into a transition system : [[Transition-Systems-as-System-Models|Link]]
   - Structured operational semantics : [[Real-Time-Systems-and-Timed-Automata|Link]]

3. **Concurrency and Communication Modeling** : [[Concurrency-and-Communication-Modeling|Link]]
   - Interleaving as a model of concurrency : [[Concurrency-and-Communication-Modeling|Link]]
   - Shared variable communication and mutual exclusion : [[Concurrency-and-Communication-Modeling|Link]]
   - Handshaking and synchronous message passing : [[Concurrency-and-Communication-Modeling|Link]]
   - Channel systems and asynchronous message passing : [[Concurrency-and-Communication-Modeling|Link]]
   - Synchronous parallel composition : [[Concurrency-and-Communication-Modeling|Link]]
   - Associativity of parallel composition operators : [[State-Space-Explosion|Link]]
   - NanoPromela as a compact process specification language : [[Linear-Time-Properties|Link]]

4. **State-Space Explosion** : [[State-Space-Explosion|Link]]
   - Exponential growth of state spaces in variables and components
   - State-space explosion as the central obstacle to model checking : [[Timed-CTL-and-TCTL-Model-Checking|Link1]], [[State-Space-Explosion|Link2]]
   - Deadlock as a terminal state of the composite system : [[State-Space-Explosion|Link1]], [[Simulation-Preorders-and-Equivalence|Link2]]

5. **Linear-Time Properties** : [[Linear-Time-Properties|Link]]
   - Paths traces and the state graph of a transition system : [[Simulation-Preorders-and-Equivalence|Link1]], [[Concurrency-and-Communication-Modeling|Link2]], [[Linear-Time-Properties|Link3]]
   - Linear-time properties as languages over sets of atomic propositions : [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link1]], [[Linear-Time-Properties|Link2]], [[Markov-Decision-Processes|Link3]]
   - Trace equivalence trace inclusion and their correspondence to property preservation : [[Linear-Time-Properties|Link]]
   - Image-finite transition systems : [[Simulation-Preorders-and-Equivalence|Link1]], [[Transition-Systems-as-System-Models|Link2]]

6. **Safety Properties and Invariants** : [[Safety-Properties-and-Invariants|Link]]
   - Invariants as reachable-state conditions : [[Safety-Properties-and-Invariants|Link]]
   - Bad prefixes and minimal bad prefixes : [[Safety-Properties-and-Invariants|Link]]
   - Prefix closure and the closure characterization of safety : [[Safety-Properties-and-Invariants|Link]]
   - Invariant checking by depth-first search : [[Safety-Properties-and-Invariants|Link]]
   - Regular versus nonregular safety properties : [[Safety-Properties-and-Invariants|Link]]

7. **Liveness Properties and the Safety-Liveness Decomposition** : [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link]]
   - Liveness as unconstrained finite behavior : [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link]]
   - Repeated eventually and starvation freedom : [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link]]
   - The decomposition theorem for linear-time properties : [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link]]
   - Almost disjointness of safety and liveness : [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link]]

8. **Fairness** : [[Fairness|Link]]
   - Unconditional strong and weak fairness constraints : [[Fairness|Link]]
   - Fairness assumptions over sets of actions : [[Fairness|Link]]
   - The fairness implication hierarchy : [[Fairness|Link]]
   - Fair satisfaction and realizable fairness assumptions : [[Fairness|Link]]
   - Fairness in LTL as an implication premise : [[Fairness|Link]]
   - Fairness in CTL via quantification over fair paths : [[Fairness|Link]]
   - Fair schedulers and fairness in Markov decision processes : [[Fairness|Link]]

9. **Automata over Finite and Infinite Words** : [[Automata-over-Finite-and-Infinite-Words|Link]]
   - Nondeterministic and deterministic finite automata : [[Automata-over-Finite-and-Infinite-Words|Link]]
   - The powerset construction and its exponential blowup : [[Automata-over-Finite-and-Infinite-Words|Link]]
   - Closure properties of regular languages : [[Linear-Time-Properties|Link1]], [[Automata-over-Finite-and-Infinite-Words|Link2]], [[Automata-Based-Verification-of-Properties|Link3]], [[Safety-Properties-and-Invariants|Link4]]
   - DFA minimization : [[Automata-over-Finite-and-Infinite-Words|Link]]
   - Omega-regular expressions and languages : [[Automata-over-Finite-and-Infinite-Words|Link]]
   - Nondeterministic Büchi automata and Büchi acceptance : [[Automata-over-Finite-and-Infinite-Words|Link]]
   - Deterministic Büchi automata are strictly less expressive : [[Automata-over-Finite-and-Infinite-Words|Link]]
   - Generalized Büchi automata : [[Automata-over-Finite-and-Infinite-Words|Link]]

10. **Automata-Based Verification of Properties** : [[Automata-Based-Verification-of-Properties|Link]]
    - The product of a transition system and an automaton : [[Automata-Based-LTL-Model-Checking|Link]]
    - Reducing regular safety verification to invariant checking : [[Automata-Based-Verification-of-Properties|Link]]
    - Persistence properties : [[Automata-Based-Verification-of-Properties|Link]]
    - Nested depth-first search for cycle detection and automaton emptiness

11. **Linear Temporal Logic** : [[Linear-Temporal-Logic|Link]]
    - LTL syntax and the next and until operators : [[CTL-Star|Link]]
    - Derived eventually and always modalities : [[Linear-Temporal-Logic|Link]]
    - LTL semantics as a language of infinite words : [[Linear-Temporal-Logic|Link]]
    - Equivalence laws and the expansion law for until : [[Linear-Temporal-Logic|Link]]
    - Weak until release and positive normal form : [[Linear-Temporal-Logic|Link]]
    - Specifying safety liveness and real-time properties in LTL : [[Stutter-Equivalences|Link1]], [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link2]], [[Linear-Temporal-Logic|Link3]]

12. **Automata-Based LTL Model Checking** : [[Automata-Based-LTL-Model-Checking|Link]]
    - Translating an LTL formula into a generalized Büchi automaton : [[Automata-Based-LTL-Model-Checking|Link]]
    - Closure and elementary sets of formulae : [[Automata-Based-LTL-Model-Checking|Link]]
    - The product of a transition system and a Büchi automaton : [[Automata-Based-LTL-Model-Checking|Link]]
    - On-the-fly model checking : [[Automata-Based-LTL-Model-Checking|Link1]], [[Automata-Based-Verification-of-Properties|Link2]]
    - Complexity of LTL model checking : [[Automata-Based-LTL-Model-Checking|Link]]
    - LTL satisfiability and validity checking : [[Automata-Based-LTL-Model-Checking|Link]]

13. **Computation Tree Logic** : [[Computation-Tree-Logic|Link]]
    - Branching time versus linear time : [[Partial-Order-Reduction|Link]]
    - CTL state formulae and path formulae : [[Computation-Tree-Logic|Link]]
    - Existential and universal path quantification : [[Computation-Tree-Logic|Link]]
    - CTL semantics and satisfaction sets : [[Computation-Tree-Logic|Link]]
    - Equivalence laws and normal forms for CTL : [[CTL-Star|Link]]
    - Existential normal form : [[Computation-Tree-Logic|Link]]

14. **LTL versus CTL Expressiveness** : [[LTL-versus-CTL-Expressiveness|Link]]
    - Incomparable expressiveness of linear-time and branching-time logics
    - Criterion for transforming a CTL formula into an equivalent LTL formula
    - Properties expressible only in CTL
    - Properties expressible only in LTL : [[LTL-versus-CTL-Expressiveness|Link]]

15. **CTL Model Checking** : [[CTL-Model-Checking|Link]]
    - Recursive computation of satisfaction sets : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
    - Least and greatest fixed point characterizations : [[Safety-Properties-and-Invariants|Link]]
    - Time complexity of CTL model checking : [[Timed-CTL-and-TCTL-Model-Checking|Link1]], [[Automata-Based-LTL-Model-Checking|Link2]]
    - Counterexamples and witnesses in CTL : [[CTL-Model-Checking|Link]]

16. **Symbolic Model Checking with Binary Decision Diagrams** : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
    - Encoding transition systems as switching functions : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
    - Cofactors and the Shannon expansion : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
    - Ordered binary decision diagrams : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
    - Reduced OBDDs as a canonical data structure : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
    - Shared OBDDs and the if-then-else operator : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
    - Symbolic computation of satisfaction sets : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]

17. **CTL\***
    - Unifying linear and branching time
    - Embedding LTL and CTL into CTL star : [[CTL-Star|Link]]
    - CTL star model checking : [[CTL-Model-Checking|Link]]

18. **Bisimulation Equivalence** : [[Bisimulation-Equivalence|Link]]
    - Bisimulation as a relation between transition systems : [[Simulation-Preorders-and-Equivalence|Link1]], [[Bisimulation-Equivalence|Link2]]
    - Bisimulation as a relation on states of a single system : [[Bisimulation-Equivalence|Link]]
    - The bisimulation quotient system : [[Bisimulation-Equivalence|Link]]
    - Bisimulation as the coarsest equivalence preserving CTL and CTL star : [[Bisimulation-Equivalence|Link]]
    - Action-based bisimulation and its congruence for parallel composition : [[Bisimulation-Equivalence|Link]]
    - Master formulae characterizing bisimulation equivalence classes : [[Simulation-Preorders-and-Equivalence|Link1]], [[Bisimulation-Equivalence|Link2]]

19. **Simulation Preorders and Equivalence** : [[Simulation-Preorders-and-Equivalence|Link]]
    - The simulation order between transition systems : [[Simulation-Preorders-and-Equivalence|Link]]
    - Abstraction functions and abstract transition systems : [[Simulation-Preorders-and-Equivalence|Link]]
    - Simulation equivalence versus bisimulation equivalence : [[Simulation-Preorders-and-Equivalence|Link]]
    - AP-deterministic transition systems : [[Simulation-Preorders-and-Equivalence|Link]]
    - The universal fragment forall CTL star and its existential dual : [[Simulation-Preorders-and-Equivalence|Link]]
    - Simulation preserves safety properties and trace inclusion : [[Simulation-Preorders-and-Equivalence|Link]]

20. **Partition Refinement Algorithms** : [[Partition-Refinement-Algorithms|Link]]
    - The atomic-proposition partition as initial partition : [[Partition-Refinement-Algorithms|Link]]
    - Splitters and stability of a partition : [[Partition-Refinement-Algorithms|Link]]
    - The refinement operator : [[Partition-Refinement-Algorithms|Link]]
    - Logarithmic-time partition refinement via smaller-half splitting : [[Partition-Refinement-Algorithms|Link]]
    - Computing quotients versus checking trace equivalence complexity : [[Partition-Refinement-Algorithms|Link]]

21. **Stutter Equivalences** : [[Stutter-Equivalences|Link]]
    - Stutter steps and stutter actions : [[Stutter-Equivalences|Link]]
    - Stutter equivalence of paths and traces : [[Stutter-Equivalences|Link]]
    - Stutter trace equivalence of transition systems : [[Stutter-Equivalences|Link1]], [[Simulation-Preorders-and-Equivalence|Link2]], [[Timed-CTL-and-TCTL-Model-Checking|Link3]], [[Linear-Time-Properties|Link4]]
    - LTL without the next operator : [[Stutter-Equivalences|Link]]
    - Stutter-insensitive linear-time properties : [[Stutter-Equivalences|Link]]
    - Stutter bisimulation and divergence sensitivity : [[Stutter-Equivalences|Link]]
    - Normed bisimulation : [[Stutter-Equivalences|Link]]

22. **Partial Order Reduction** : [[Partial-Order-Reduction|Link]]
    - Independence of actions : [[Partial-Order-Reduction|Link]]
    - Permuting and adding independent actions in executions : [[Partial-Order-Reduction|Link]]
    - The ample set approach : [[Partial-Order-Reduction|Link]]
    - The nonemptiness dependency stutter and cycle conditions : [[Partial-Order-Reduction|Link]]
    - Dynamic partial order reduction : [[Partial-Order-Reduction|Link]]
    - Static partial order reduction : [[Partial-Order-Reduction|Link]]
    - Branching-time ample sets for CTL and CTL star : [[Partial-Order-Reduction|Link]]

23. **Real-Time Systems and Timed Automata** : [[Real-Time-Systems-and-Timed-Automata|Link]]
    - Clocks and clock constraints : [[Real-Time-Systems-and-Timed-Automata|Link]]
    - Timed automata as program graphs with clocks : [[Real-Time-Systems-and-Timed-Automata|Link]]
    - Guards versus location invariants : [[Real-Time-Systems-and-Timed-Automata|Link]]
    - Parallel composition of timed automata : [[State-Space-Explosion|Link]]
    - Transition system semantics via discrete and delay transitions : [[Transition-Systems-as-System-Models|Link]]
    - Time divergence and time-convergent paths
    - Timelock freedom
    - Zeno paths and non-zenoness

24. **Timed CTL and TCTL Model Checking** : [[Timed-CTL-and-TCTL-Model-Checking|Link]]
    - Syntax and semantics of Timed CTL : [[Concurrency-and-Communication-Modeling|Link]]
    - Path quantification restricted to time-divergent paths : [[Timed-CTL-and-TCTL-Model-Checking|Link]]
    - Clock equivalence and clock regions : [[Timed-CTL-and-TCTL-Model-Checking|Link]]
    - The region transition system as a finite quotient : [[Transition-Systems-as-System-Models|Link1]], [[Timed-CTL-and-TCTL-Model-Checking|Link2]], [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link3]], [[Fairness|Link4]]
    - Reducing TCTL model checking to CTL model checking : [[Timed-CTL-and-TCTL-Model-Checking|Link]]
    - PSPACE-completeness of TCTL model checking : [[Timed-CTL-and-TCTL-Model-Checking|Link1]], [[Automata-Based-LTL-Model-Checking|Link2]], [[Automata-Based-Verification-of-Properties|Link3]], [[CTL-Model-Checking|Link4]]

25. **Markov Chains and Probabilistic Verification** : [[Markov-Chains-and-Probabilistic-Verification|Link]]
    - Discrete-time Markov chains and the memoryless property : [[Markov-Chains-and-Probabilistic-Verification|Link]]
    - Probability spaces cylinder sets and sigma-algebras
    - Reachability probabilities via linear equation systems : [[Markov-Chains-and-Probabilistic-Verification|Link]]
    - Bottom strongly connected components and long-run behavior : [[Markov-Chains-and-Probabilistic-Verification|Link]]
    - Qualitative versus quantitative probabilistic properties : [[Markov-Chains-and-Probabilistic-Verification|Link]]

26. **Probabilistic Computation Tree Logic** : [[Probabilistic-Computation-Tree-Logic|Link]]
    - Syntax and semantics of PCTL : [[Concurrency-and-Communication-Modeling|Link]]
    - The probabilistic operator as a quantitative path quantifier : [[Probabilistic-Computation-Tree-Logic|Link]]
    - PCTL model checking algorithm and complexity : [[Markov-Decision-Processes|Link1]], [[CTL-Model-Checking|Link2]], [[Timed-CTL-and-TCTL-Model-Checking|Link3]], [[Automata-Based-LTL-Model-Checking|Link4]]
    - The qualitative fragment of PCTL : [[Probabilistic-Computation-Tree-Logic|Link]]
    - Expressiveness of PCTL versus CTL : [[LTL-versus-CTL-Expressiveness|Link]]
    - Witnesses and counterexamples for PCTL properties : [[Probabilistic-Computation-Tree-Logic|Link]]
    - Computing probabilities of LTL properties via deterministic Rabin automata : [[Probabilistic-Computation-Tree-Logic|Link]]
    - PCTL star and its model-checking complexity : [[CTL-Model-Checking|Link1]], [[Markov-Decision-Processes|Link2]], [[Timed-CTL-and-TCTL-Model-Checking|Link3]], [[Automata-Based-LTL-Model-Checking|Link4]]

27. **Probabilistic Bisimulation and Markov Reward Models** : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
    - Probabilistic bisimulation for Markov chains : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link1]], [[Markov-Chains-and-Probabilistic-Verification|Link2]]
    - Bisimulation quotients of Markov chains : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
    - Logical characterization of probabilistic bisimulation by PCTL equivalence : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link1]], [[Simulation-Preorders-and-Equivalence|Link2]]
    - Markov reward models and cumulative reward : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
    - Expected reward until reaching a target set : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
    - Long-run average reward

28. **Markov Decision Processes** : [[Markov-Decision-Processes|Link]]
    - Nondeterministic and probabilistic choice in MDPs : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
    - Schedulers resolving nondeterminism : [[Markov-Decision-Processes|Link]]
    - The Markov chain induced by a scheduler : [[Markov-Decision-Processes|Link]]
    - Maximal and minimal reachability probabilities : [[Markov-Decision-Processes|Link]]
    - Linear programming approach to extremal probabilities
    - Sub-MDPs and end components
    - Long-run behavior via end components : [[Markov-Decision-Processes|Link]]
    - Probmela as a probabilistic modeling language : [[Markov-Decision-Processes|Link]]

29. **Mathematical Preliminaries** : [[Mathematical-Preliminaries|Link]]
    - Relations equivalences and partitions : [[Mathematical-Preliminaries|Link]]
    - Regular languages and regular expressions : [[Automata-over-Finite-and-Infinite-Words|Link]]
    - Syntax and semantics of propositional logic : [[Mathematical-Preliminaries|Link1]], [[Concurrency-and-Communication-Modeling|Link2]]
    - Graph traversal by depth-first and breadth-first search : [[Automata-Based-Verification-of-Properties|Link]]
    - Strongly connected components : [[Markov-Chains-and-Probabilistic-Verification|Link]]
    - Deterministic and nondeterministic algorithms : [[CTL-Model-Checking|Link1]], [[Concurrency-and-Communication-Modeling|Link2]]
    - Complexity classes PTIME NP and PSPACE

---
