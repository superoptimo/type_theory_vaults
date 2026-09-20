# Principles of Model Checking — Guidelines

## Header

**Title:** Principles of Model Checking
**Author(s):** Christel Baier and Joost-Pieter Katoen (Foreword by Kim Guldstrand Larsen)
**Publication:** The MIT Press, 2008

**Brief Summary:**
A comprehensive textbook on model checking, the automated technique for verifying that a finite-state model of a system satisfies a desired temporal-logic property. It builds up from transition systems and concurrency modeling, through the classification of properties into safety and liveness with fairness, to automata-based verification of regular and $\omega$-regular properties, the temporal logics LTL and CTL/CTL$^*$ and their model-checking algorithms (explicit and symbolic/BDD-based), equivalence- and simulation-based abstraction, partial order reduction, real-time verification via timed automata and TCTL, and probabilistic verification via Markov chains, PCTL, and Markov decision processes.

**Intent of the Author:**
The authors set out to introduce model checking "from first principles" as a textbook for bachelor's and master's students and as an entry point for researchers from other areas of computer science, using an extensive set of running examples and complete proofs of all basic results, with each chapter ending in a summary, bibliographic notes, and exercises of both theoretical and practical nature.

---

## Topic List

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

## Chapter Summaries

### Chapter 1: System Verification (pp. 1–17)

**Summary:** Motivates formal verification by surveying the cost of software/hardware defects and the limits of peer review, testing, simulation, and emulation, then introduces model checking as an automated, exhaustive state-exploration technique, walking through its process (modeling, running, analysis) and weighing its strengths against its weaknesses.

**Key Definitions & Concepts by Section:**
- **1.1 Model Checking** — Model checking (an automated technique that, given a finite-state model of a system and a formal property, systematically checks whether the property holds for that model); verification vs. validation ("building the thing right" vs. "building the right thing"); counterexample (an execution path from the initial state to a state violating the property, used for debugging); property specification language / temporal logic (extension of propositional logic with operators referring to system behavior over time); the observation that "any verification using model-based techniques is only as good as the model of the system." : [[Automata-Based-LTL-Model-Checking|Link1]], [[Automata-Based-Verification-of-Properties|Link2]], [[CTL-Model-Checking|Link3]], [[CTL-Star|Link4]]
- **1.2 Characteristics of Model Checking** — The three phases of the model-checking process: modeling phase (system model + property formalization + sanity-check simulation), running phase, and analysis phase (property satisfied / violated + counterexample analysis / out-of-memory → abstraction or reduction); verification organization (documentation and configuration management of the verification effort). : [[CTL-Model-Checking|Link1]], [[Automata-Based-LTL-Model-Checking|Link2]], [[Automata-Based-Verification-of-Properties|Link3]], [[CTL-Star|Link4]]
  - **1.2.1 The Model-Checking Process** — distinguishes modeling errors, design errors, and property errors as causes of a failed check, each requiring a different corrective action. : [[Model-Checking-Fundamentals|Link]]
  - **1.2.2 Strengths and Weaknesses** — strengths: general applicability, partial/incremental verification, insensitivity to error likelihood, diagnostic counterexamples, push-button automation, sound mathematical basis; weaknesses: poor fit for data-intensive systems, decidability limits for infinite-state systems, verifies the model not the system, no completeness guarantee beyond stated properties, state-space explosion, requires abstraction expertise, tool correctness is itself unverified, cannot handle arbitrary/parameterized system generalizations. : [[Model-Checking-Fundamentals|Link]]
- **1.3 Bibliographic Notes** — origin of model checking in the independent work of Clarke & Emerson and Queille & Sifakis in the early 1980s.

**Key Questions:**
1. Why does the book insist that "correctness is always relative to a specification," and what does this imply about what a successful model-checking run actually proves?
2. What is the practical difference between verification and validation, and why can model checking address the former but not fully guarantee the latter?
3. Model checking is described as both a strength (exhaustive, unbiased toward likely errors) and a source of its central weakness (state-space explosion) — how do these two facts follow from the same underlying "explore all states" strategy?

---

### Chapter 2: Modelling Concurrent Systems (pp. 19–87)

**Summary:** Introduces transition systems as the book's core operational model for hardware and software, shows how to derive them from sequential circuits and data-dependent programs (via program graphs), then builds up a hierarchy of parallel-composition operators — pure interleaving, shared-variable composition, handshaking, channel systems, and synchronous parallelism — before closing with a quantitative account of the state-space explosion problem.

**Key Definitions & Concepts by Section:**
- **2.1 Transition Systems** — Transition system $TS = (S, Act, \rightarrow, I, AP, L)$ (states, actions, transition relation $\rightarrow \subseteq S \times Act \times S$, initial states, atomic propositions, labeling function $L: S \to 2^{AP}$); $\text{Post}(s,\alpha)$/$\text{Pre}(s,\alpha)$ (direct successor/predecessor sets); terminal state (no outgoing transitions); action-deterministic vs. AP-deterministic transition systems; nondeterminism as the mechanism for modeling interleaving, underspecification, and unknown environments. : [[Automata-Based-LTL-Model-Checking|Link1]], [[Bisimulation-Equivalence|Link2]], [[Concurrency-and-Communication-Modeling|Link3]], [[Fairness|Link4]]
  - **2.1.1 Executions** — execution fragment (alternating state/action sequence respecting $\rightarrow$), maximal execution fragment (ends in a terminal state, or is infinite), execution (initial + maximal fragment), reachable state, $\text{Reach}(TS)$.
  - **2.1.2 Modeling Hardware and Software Systems** — modeling sequential hardware circuits as transition systems via register/input evaluations and switching functions; program graph $PG = (Loc, Act, \text{Effect}, \rightarrow, Loc_0, g_0)$ over typed variables, guarded conditional transitions $\ell \xrightarrow{g:\alpha} \ell'$; unfolding a program graph into its transition system semantics $TS(PG)$; Structured Operational Semantics (SOS) notation (premise/conclusion inference rules). : [[Transition-Systems-as-System-Models|Link]]
- **2.2 Parallelism and Communication** — parallel composition operator $\|$ (commutative, and associativity depends on the communication scheme). : [[State-Space-Explosion|Link1]], [[Concurrency-and-Communication-Modeling|Link2]]
  - **2.2.1 Concurrency and Interleaving** — interleaving operator $|||$ (nondeterministic weaving of independent actions); justification that $\text{Effect}(\alpha \| \beta, \eta) = \text{Effect}((\alpha;\beta)+(\beta;\alpha), \eta)$ for independent actions. : [[Concurrency-and-Communication-Modeling|Link]]
  - **2.2.2 Communication via Shared Variables** — interleaving of program graphs with shared variables; mutual exclusion via semaphores; Peterson's mutual exclusion algorithm as a running example. : [[Concurrency-and-Communication-Modeling|Link]]
  - **2.2.3 Handshaking** — synchronous message passing $TS_1 \|_H TS_2$ over a handshake action set $H$ (commutative but generally not associative unless $H$ is fixed across all components); multiway handshaking for broadcasting.
  - **2.2.4 Channel Systems** — channel system $CS = [PG_1 | \ldots | PG_n]$ over (Var, Chan); communication actions $c!v$ (send) / $c?x$ (receive); channel capacity $\text{cap}(c)$, where capacity 0 reduces to handshaking and capacity $>0$ gives asynchronous message passing; the Alternating Bit Protocol (ABP) as a running example. : [[Concurrency-and-Communication-Modeling|Link]]
  - **2.2.5 NanoPromela** — a small guarded-command-style programming language used to specify process behavior compactly (illustrated via Peterson's algorithm and a vending-machine example).
  - **2.2.6 Synchronous Parallelism** — synchronous product $TS_1 \otimes TS_2$, where all components take a step in lockstep (as opposed to interleaving). : [[Concurrency-and-Communication-Modeling|Link]]
- **2.3 The State-Space Explosion Problem** — exponential growth of $|S|$ in the number of program-graph variables ($|Loc| \cdot \prod_x |\text{dom}(x)|$), in the number of parallel components ($\prod_i |S_i|$), and in channel capacities; the state-space explosion problem as the central practical obstacle motivating later reduction techniques (Chapters 6–8). : [[State-Space-Explosion|Link]]

**Key Questions:**
1. Why does composing program graphs (rather than their unfolded transition systems) matter for correctly modeling shared-variable communication — what would go wrong if you interleaved the transition systems directly?
2. How does the choice of handshake set $H$ determine whether parallel composition via handshaking is associative, and why does fixing $H$ across all components restore associativity?
3. The chapter shows state-space size growing as $L^n \cdot m^M \cdot 2^{K \cdot k}$ for channel systems — which of these factors (locations, variables, or channel capacity/count) is typically the fastest-growing in practice, and why does this matter for choosing a modeling style?

---

### Chapter 3: Linear-Time Properties (pp. 89–149)

**Summary:** This chapter introduces the state-based (as opposed to action-based) semantic framework for reasoning about system behavior — paths, traces, and linear-time (LT) properties over $2^{AP}$ — and uses it to define the two fundamental classes of requirements, safety and liveness, together with the notion of fairness needed to rule out unrealistic executions when verifying liveness. : [[Linear-Time-Properties|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Deadlock** — deadlock (a terminal state of the composite system while some component is still in a nonterminal, i.e. non-blocked, local state); illustrated via the dining philosophers (Dijkstra) and its deadlock-free/starvation-free/fault-tolerant refinements.
- **3.2 Linear-Time Behavior** — state graph $G(TS)$ (digraph obtained from a transition system by dropping action/initial-state information); path fragment, maximal/initial path fragment, path; trace and trace fragment (the word over $2^{AP}$ induced by a path's state labels); linear-time (LT) property (a subset of $(2^{AP})^\omega$); satisfaction relation $TS \models P$ iff $\mathit{Traces}(TS) \subseteq P$; trace inclusion and trace equivalence, and their exact correspondence with preservation/coincidence of LT properties (Theorem 3.15, Corollary 3.18); image-finiteness as the condition under which finite-trace inclusion coincides with (infinite-)trace inclusion (Theorem 3.30). : [[Linear-Time-Properties|Link1]], [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link2]], [[Markov-Decision-Processes|Link3]], [[Probabilistic-Computation-Tree-Logic|Link4]]
- **3.3 Safety Properties and Invariants** — invariant (an LT property pinned to a propositional state condition $\Phi$ required on all reachable states); invariant checking via forward DFS with a counterexample extracted from the DFS stack (Algorithms 3–4), linear time $O(N(1+|\Phi|)+M)$; safety property and bad prefix / minimal bad prefix (any infinite word violating $P_{safe}$ has a finite "bad" prefix that already dooms it); prefix, closure of a property, and the characterization $P$ is safety iff $\mathrm{closure}(P)=P$; the correspondence between finite-trace inclusion/equivalence and preservation/coincidence of safety properties (Theorem 3.28, Corollary 3.29). : [[Safety-Properties-and-Invariants|Link]]
- **3.4 Liveness Properties** — liveness property (an LT property that rules out no finite prefix, i.e. $\mathrm{pref}(P_{live})=(2^{AP})^*$); the "eventually" / "repeated eventually (infinitely often)" / "starvation freedom" trio as canonical liveness properties; Decomposition Theorem (every LT property is equivalent to the conjunction of a safety and a liveness property); safety and liveness properties are almost disjoint — only $(2^{AP})^\omega$ is both. : [[Liveness-Properties-and-the-Safety-Liveness-Decomposition|Link]]
- **3.5 Fairness** — fairness constraint (rules out "unrealistic" resolutions of nondeterminism); unconditional fairness (impartiality), strong fairness (compassion), weak fairness (justice), defined action-wise via $\mathrm{Act}(s)$ and the "infinitely often enabled" / "continuously enabled" premises; fairness assumption $\mathcal{F}=(F_{ucond},F_{strong},F_{weak})$ and $\mathcal{F}$-fair execution/path/trace; the strict implication chain unconditional $\Rightarrow$ strong $\Rightarrow$ weak fairness; fair satisfaction relation $TS \models_{\mathcal{F}} P$ (only $\mathcal{F}$-fair paths need satisfy $P$); realizable fairness assumption (every finite path can be extended to a fair one) — needed so fairness assumptions don't vacuously satisfy every property. : [[Fairness|Link]]

**Key Questions:**
1. Why does the theorem "$\mathrm{Traces}(TS)\subseteq\mathrm{Traces}(TS')$ iff every LT property satisfied by $TS'$ is satisfied by $TS$" make trace inclusion the right notion of "correct refinement" in stepwise system design, and why does the analogous statement for *safety* properties only need *finite* trace inclusion?
2. Why is starvation freedom for a semaphore-based mutual exclusion algorithm unprovable without a fairness assumption, and why must the assumption be phrased per-process (e.g. $\{\{\mathrm{enter}_1\},\{\mathrm{enter}_2\}\}$) rather than as a single set $\{\{\mathrm{enter}_1,\mathrm{enter}_2\}\}$?
3. In what precise sense is every LT property decomposable into a safety part and a liveness part, and why does this decomposition make the safety/liveness dichotomy an exhaustive classification of requirements rather than just two special cases among many?

---

### Chapter 4: Regular Properties (pp. 151–227)

**Summary:** This chapter develops automata-based verification: nondeterministic finite automata (NFA) are used to check regular safety properties by reducing them to invariant checking on a product transition system, and this is then generalized to the full class of $\omega$-regular properties via nondeterministic Büchi automata (NBA) and a reduction to persistence checking (cycle detection) via nested depth-first search. : [[Automata-Based-Verification-of-Properties|Link1]], [[Safety-Properties-and-Invariants|Link2]]

**Key Definitions & Concepts by Section:**
- **4.1 Automata on Finite Words** — NFA $(Q,\Sigma,\delta,Q_0,F)$, run, accepted language $L(A)$; DFA / total DFA; powerset (subset) construction turning an NFA into an equivalent total DFA (exponential blow-up in general, tight for $E_k=(A+B)^*B(A+B)^k$); synchronous product $A_1\otimes A_2$ realizing language intersection; closure of regular languages under union, concatenation, Kleene star, intersection, complementation; DFA minimization (unique minimal DFA up to isomorphism). : [[Automata-over-Finite-and-Infinite-Words|Link]]
- **4.2 Model-Checking Regular Safety Properties** — regular safety property (its bad-prefix language is regular); every invariant is a regular safety property, with bad prefixes given by $\Phi^*(\neg\Phi)\mathrm{true}^*$; regularity is equivalent whether stated for all bad prefixes or just minimal ones (Lemma 4.12); product of a transition system and an NFA $TS\otimes A$; verification reduces to invariant checking on $TS\otimes A$ (Tracesfin$(TS)\cap L(A)=\emptyset$ iff $TS\otimes A\models$ "always $\Phi$"); example of a *nonregular* safety property (context-free "coins $\geq$ drinks"). : [[Automata-Based-Verification-of-Properties|Link]]
- **4.3 Automata on Infinite Words** — $\omega$-regular expression $E_1.F_1^\omega+\dots+E_n.F_n^\omega$ and $\omega$-regular language; nondeterministic Büchi automaton (NBA) — same syntax as NFA, but a run is accepting iff it visits the accept set $F$ infinitely often; closure of NBA-recognizable languages under union/concatenation-with-$\omega$/$\omega$-operator, giving the equivalence of NBAs and $\omega$-regular languages (Theorem 4.32); deterministic Büchi automaton (DBA) — strictly less expressive than NBA (Theorem 4.50: no DBA for $(A+B)^*B^\omega$, i.e. "eventually forever a" needs genuine nondeterminism, unlike an "oracle"-free powerset construction which fails for Büchi acceptance); generalized NBA (GNBA) — acceptance requires visiting *each* of several sets $F_1,\dots,F_k$ infinitely often, a conjunction of Büchi conditions, used later for LTL-to-automaton translation. : [[Automata-over-Finite-and-Infinite-Words|Link]]
- **4.4 Model-Checking $\omega$-Regular Properties** — persistence property "eventually forever $\Phi$" ($\Phi$ holds from some point on); product $TS\otimes A$ for an NBA $A$ recognizing the bad traces, and the equivalence $TS\models P \Leftrightarrow \mathrm{Traces}(TS)\cap L^\omega(A)=\emptyset \Leftrightarrow TS\otimes A \models P_{pers}(A)$ (Theorem 4.63); persistence checking reduces to cycle detection: $TS\models P_{pers}$ iff no reachable $\neg\Phi$-state lies on a cycle (Theorem 4.65); nested depth-first search (Algorithm 6/7 family) as the standard on-the-fly algorithm for persistence/NBA-emptiness checking, contrasted with the (asymptotically optimal but less on-the-fly-friendly) SCC-based approach. : [[Automata-Based-Verification-of-Properties|Link1]], [[Model-Checking-Fundamentals|Link2]], [[Timed-CTL-and-TCTL-Model-Checking|Link3]]

**Key Questions:**
1. Why does the powerset (subset) construction, which turns any NFA into an equivalent DFA, fail to produce an equivalent *deterministic* Büchi automaton — and what does this failure reveal about the extra expressive power nondeterminism gives Büchi acceptance (e.g. for "eventually forever a")?
2. How does the automata-theoretic verification pattern for $\omega$-regular properties (build $TS\otimes A$ for an NBA representing the *bad* behaviors, then check for a reachable accepting cycle) directly generalize the pattern used for regular safety properties (build $TS\otimes A$ for an NFA of bad prefixes, then check an invariant) — and why does persistence/cycle detection replace invariant/reachability checking as the correspondingly more general algorithmic core?
3. Why is regularity of the set of *minimal* bad prefixes equivalent to regularity of the set of *all* bad prefixes for a safety property (Lemma 4.12), and why does this equivalence matter for the choice of automaton used in verification?

---

### Chapter 5: Linear Temporal Logic (pp. 229–311)

**Summary:** Introduces LTL, a linear-time propositional temporal logic built from atomic propositions, Boolean connectives, and the next ($\bigcirc$) and until ($U$) modalities, then presents the automata-based algorithm that model-checks LTL formulae against finite transition systems and proves the problem PSPACE-complete. : [[Linear-Temporal-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Linear Temporal Logic** — LTL syntax: $\varphi ::= \text{true} \mid a \mid \varphi_1 \land \varphi_2 \mid \neg\varphi \mid \bigcirc\varphi \mid \varphi_1 U \varphi_2$; derived modalities $\Diamond\varphi \stackrel{\text{def}}{=} \text{true } U\, \varphi$ ("eventually") and $\Box\varphi \stackrel{\text{def}}{=} \neg\Diamond\neg\varphi$ ("always"); $\Box\Diamond\varphi$ ("infinitely often") and $\Diamond\Box\varphi$ ("eventually forever"); semantics defined as a language $\mathit{Words}(\varphi)\subseteq(2^{AP})^\omega$, then lifted to $\mathrm{TS}\models\varphi$ iff $\mathit{Traces}(\mathrm{TS})\subseteq \mathit{Words}(\varphi)$; equivalence $\varphi_1\equiv\varphi_2$ iff $\mathit{Words}(\varphi_1)=\mathit{Words}(\varphi_2)$, with duality, expansion, and distributive laws; weak until $\varphi\,W\,\psi \stackrel{\text{def}}{=} (\varphi\,U\,\psi)\lor\Box\varphi$ (until is the *least* solution, weak-until the *greatest* solution, of the expansion equivalence $\kappa \equiv \psi \lor (\varphi \land \bigcirc\kappa)$); positive normal form (PNF) using $W$ or the release operator $\varphi\,R\,\psi \stackrel{\text{def}}{=} \neg(\neg\varphi\,U\,\neg\psi)$ (release-PNF avoids the exponential blowup of weak-until PNF); LTL fairness constraints (unconditional $\Box\Diamond\Psi$, strong $\Box\Diamond\Phi\to\Box\Diamond\Psi$, weak $\Diamond\Box\Phi\to\Box\Diamond\Psi$) and the fair satisfaction relation $\models_{\mathit{fair}}$, reducible to plain LTL via $\mathrm{TS}\models_{\mathit{fair}}\varphi$ iff $\mathrm{TS}\models(\mathit{fair}\to\varphi)$. : [[Linear-Temporal-Logic|Link]]
- **5.2 Automata-Based LTL Model Checking** — model checking via $\mathrm{TS}\models\varphi$ iff $\mathit{Traces}(\mathrm{TS})\cap\mathcal{L}_\omega(A_{\neg\varphi})=\emptyset$, checked by building the product $\mathrm{TS}\otimes A_{\neg\varphi}$ and searching for a reachable accepting cycle; generalized NBA (GNBA), a Büchi automaton with a set $\mathcal{F}$ of acceptance sets (each must be visited infinitely often); closure of a formula (all subformulae and their negations) and elementary sets of formulae (propositionally consistent, maximal, locally consistent w.r.t. until) used as GNBA states; construction of $G_\varphi$ with $\mathcal{L}_\omega(G_\varphi)=\mathit{Words}(\varphi)$ in $2^{O(|\varphi|)}$ time/space; lower bound showing every NBA for some formula family needs $2^n$ states, hence NBA are strictly more expressive than LTL. : [[Automata-Based-LTL-Model-Checking|Link]]
  - **5.2.1 Complexity of the LTL Model-Checking Problem** — overall time/space complexity $O(|\mathrm{TS}|\cdot 2^{|\varphi|})$ (linear in system size, exponential in formula size); on-the-fly model checking avoiding full automaton construction; PSPACE-hardness proven by reduction from the Hamiltonian path problem (coNP-hardness) and from arbitrary PSPACE Turing machines (full PSPACE-hardness); membership in PSPACE via a nondeterministic polynomial-space algorithm (Savitch's theorem) — overall LTL model checking is **PSPACE-complete**. : [[Automata-Based-LTL-Model-Checking|Link]]
  - **5.2.2 LTL Satisfiability and Validity Checking** — satisfiability/validity reduced to NBA emptiness checking; both problems are PSPACE-complete. : [[Automata-Based-LTL-Model-Checking|Link]]

**Key Questions:**
1. Why is until $\varphi\,U\,\psi$ characterized as the *least* solution of the expansion law $\kappa \equiv \psi \lor (\varphi \land \bigcirc\kappa)$ while weak until is the *greatest* solution — and what LTL formula (e.g. $\Box\varphi$) exploits this distinction?
2. In the automata-based LTL model-checking algorithm, why is the automaton built for the *negation* $\neg\varphi$ rather than $\varphi$ itself, and what does an accepting run of the product $\mathrm{TS}\otimes A_{\neg\varphi}$ represent?
3. The LTL model-checking problem is linear in $|\mathrm{TS}|$ but exponential in $|\varphi|$ — why does the book argue this is not a practical obstacle, and which factor (formula size or system size) is actually the bottleneck in real verification?

---

### Chapter 6: Computation Tree Logic (pp. 313–447)

**Summary:** Introduces CTL, a branching-time temporal logic with explicit existential/universal path quantifiers over the computation tree of a transition system, shows CTL and LTL have incomparable expressiveness, develops an explicit polynomial-time CTL model-checking algorithm (extended to handle fairness and counterexample generation), presents a symbolic (OBDD-based) reformulation for combating state-space explosion, and introduces CTL* as a unifying superlogic. : [[Computation-Tree-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Introduction** — branching vs. linear time: a computation tree is the unfolding of a transition system at a state; path quantifiers $\exists$ ("for some path") and $\forall$ ("for all paths"); summary table contrasting LTL (PSPACE-complete, trace-based equivalence, fairness needs no extra machinery) against CTL (PTIME model checking, (bi)simulation-based equivalence, fairness requires special treatment). : [[Bisimulation-Equivalence|Link1]], [[Timed-CTL-and-TCTL-Model-Checking|Link2]]
- **6.2 Computation Tree Logic** — : [[Computation-Tree-Logic|Link]]
  - **6.2.1 Syntax** — two-stage grammar: state formulae $\Phi ::= \text{true}\mid a\mid \Phi_1\land\Phi_2\mid\neg\Phi\mid\exists\varphi\mid\forall\varphi$, path formulae $\varphi ::= \bigcirc\Phi \mid \Phi_1 U \Phi_2$ (temporal operators must be immediately preceded by a path quantifier); derived $\exists\Diamond\Phi$ ("potentially"), $\forall\Diamond\Phi$ ("inevitable"), $\exists\Box\Phi$, $\forall\Box\Phi$ ("invariantly"). : [[Timed-CTL-and-TCTL-Model-Checking|Link]]
  - **6.2.2 Semantics** — satisfaction relation $s\models\Phi$ over states and $\pi\models\varphi$ over paths; satisfaction set $\mathit{Sat}(\Phi)=\{s\in S\mid s\models\Phi\}$; $\forall\Box\forall\Diamond a$ characterizes "$a$ infinitely often on every path."
  - **6.2.3 Equivalence of CTL Formulae** — duality, expansion, and distributive laws, e.g. $\exists(\Phi U \Psi)\equiv\Psi\lor(\Phi\land\exists\bigcirc\exists(\Phi U\Psi))$; note $\forall\Diamond(\Phi\lor\Psi)\not\equiv\forall\Diamond\Phi\lor\forall\Diamond\Psi$ (unlike the LTL/CTL* existential case). : [[Bisimulation-Equivalence|Link1]], [[CTL-Star|Link2]], [[Computation-Tree-Logic|Link3]]
  - **6.2.4 Normal Forms for CTL** — existential normal form (ENF, using only $\exists\bigcirc,\exists U,\exists\Box$), used as the basis of the model-checking algorithm; positive normal form (PNF) using the weak-until (or release) dual operator. : [[Computation-Tree-Logic|Link1]], [[Linear-Temporal-Logic|Link2]], [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link3]]
- **6.3 Expressiveness of CTL vs. LTL** — equivalence between a CTL and an LTL formula defined via identical $\mathrm{TS}\models$ behavior; Theorem 6.18: dropping all path quantifiers from a CTL formula yields an equivalent LTL formula *if one exists at all*; concrete non-equivalences ($\forall\Box\forall\Diamond a \not\equiv \Diamond\Box a$; $\forall\Diamond(a\land\forall\bigcirc a)\not\equiv\Diamond(a\land\bigcirc a)$) establish that CTL and LTL have strictly **incomparable** expressive power (Theorem 6.21). : [[LTL-versus-CTL-Expressiveness|Link]]
- **6.4 CTL Model Checking** — : [[CTL-Model-Checking|Link]]
  - **6.4.1 Basic Algorithm** — recursive bottom-up computation of $\mathit{Sat}(\Psi)$ over the parse tree of $\Phi$; $\mathrm{TS}\models\Phi$ iff $I\subseteq\mathit{Sat}(\Phi)$; $\mathit{Sat}(\exists\bigcirc\Phi)$ characterized directly, $\mathit{Sat}(\exists(\Phi U\Psi))$ as a *least* fixed point (backward reachability), and $\mathit{Sat}(\exists\Box\Phi)$ as a *greatest* fixed point. : [[CTL-Model-Checking|Link]]
  - **6.4.2 The Until and Existential Always Operator** — enumerative backward-search algorithms for until and always. : [[Computation-Tree-Logic|Link]]
  - **6.4.3 Time and Space Complexity** — overall time complexity linear in $|\mathrm{TS}|\cdot|\Phi|$ — a PTIME algorithm, contrasting with LTL's PSPACE-completeness (illustrated via a CTL encoding of the NP-complete Hamiltonian path problem that stays polynomial-time checkable only because the *formula*, not the problem instance, grows exponentially). : [[CTL-Model-Checking|Link]]
- **6.5 Fairness in CTL** — unlike LTL, fairness constraints cannot be expressed as CTL formulae (Boolean connectives $\to,\land$ are disallowed at the path-formula level); instead the semantics of $\exists,\forall$ is redefined to quantify over *fair paths* only; CTL fairness assumption as an LTL-style formula over CTL state formulae; model checking with fairness adds a multiplicative factor proportional to the number of fairness constraints. : [[Fairness|Link]]
- **6.6 Counterexamples and Witnesses** — for $\forall\varphi$, a violating path prefix is a counterexample (as in LTL); for $\exists\varphi$ (and its fair variant), witness/counterexample generation is more involved due to existential path quantification. : [[CTL-Model-Checking|Link1]], [[Probabilistic-Computation-Tree-Logic|Link2]]
- **6.7 Symbolic CTL Model Checking** — motivated by state-space explosion; states/transitions encoded as bit vectors, subsets and the transition relation represented as *switching functions* (Boolean functions) rather than explicit sets. : [[CTL-Model-Checking|Link1]], [[CTL-Star|Link2]], [[Probabilistic-Computation-Tree-Logic|Link3]], [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link4]]
  - **6.7.1 Switching Functions** — cofactor $f|_{z=1}$, essential variable, Shannon expansion $f = (\neg z\land f|_{z=0})\lor(z\land f|_{z=1})$. : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
  - **6.7.2 Encoding Transition Systems by Switching Functions** — symbolic reformulation of $\mathit{Sat}(\exists(C\,U\,B))$/$\mathit{Sat}(\exists\Box B)$ as fixed-point iterations over switching functions. : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
  - **6.7.3 Ordered Binary Decision Diagrams** — a $\wp$-OBDD is a DAG of nodes labeled by variables respecting an ordering $\wp$, with 0/1-successors and terminal drains, representing a switching function $f_B$; reduced OBDD (ROBDD) — no two nodes represent the same $\wp$-consistent cofactor; Universality and Canonicity of ROBDDs — every switching function has an essentially unique ROBDD representation for a fixed variable ordering, making ROBDDs a canonical data structure. : [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link]]
  - **6.7.4 Implementation of ROBDD-Based Algorithms** — shared OBDDs, the ITE (if-then-else) operator for Boolean composition, and the relational-product operation for symbolic image computation. : [[Safety-Properties-and-Invariants|Link1]], [[Concurrency-and-Communication-Modeling|Link2]]
- **6.8 CTL\*** —
  - **6.8.1 Logic, Expressiveness, and Equivalence** — CTL* unifies LTL and CTL by allowing arbitrary nesting of path quantifiers with linear temporal operators (state formulae $\Phi::=\text{true}\mid a\mid\Phi_1\land\Phi_2\mid\neg\Phi\mid\exists\varphi$; path formulae $\varphi::=\Phi\mid\varphi_1\land\varphi_2\mid\neg\varphi\mid\bigcirc\varphi\mid\varphi_1 U\varphi_2$); LTL embeds into CTL* via $\varphi \mapsto \forall\varphi$; CTL* is strictly more expressive than LTL and CTL combined (e.g. $(\forall\Diamond\Box a)\lor(\forall\Box\exists\Diamond b)$ has no LTL or CTL equivalent). : [[Simulation-Preorders-and-Equivalence|Link1]], [[Bisimulation-Equivalence|Link2]], [[Stutter-Equivalences|Link3]], [[LTL-versus-CTL-Expressiveness|Link4]]
  - **6.8.2 CTL\* Model Checking** — combines the CTL recursive-descent procedure with the LTL automata-based procedure at maximal state subformulae; the problem is PSPACE-complete. : [[CTL-Model-Checking|Link1]], [[CTL-Star|Link2]], [[Probabilistic-Computation-Tree-Logic|Link3]], [[Symbolic-Model-Checking-with-Binary-Decision-Diagrams|Link4]]

**Key Questions:**
1. Why does the CTL model-checking algorithm run in time linear in $|\mathrm{TS}|\cdot|\Phi|$ (PTIME) while LTL model checking is PSPACE-complete, given that CTL* — which subsumes both — is itself PSPACE-complete? What does this say about the source of LTL's complexity (formula structure vs. path quantification)?
2. Give a property expressible in CTL but not LTL, and one expressible in LTL but not CTL, and explain in each case *why* the other logic cannot capture it (hint: existential vs. universal path quantification nesting, and the "reset" nature of $\forall\Diamond\forall\Box a$).
3. Why must fairness in CTL be built into the *semantics* (quantifying over fair paths) rather than added as a formula premise the way it is in LTL, and what specifically about CTL's syntax rules this out?
4. What do "universality" and "canonicity" mean for reduced OBDDs, and why is canonicity (for a fixed variable ordering) essential for using OBDDs as the data structure underneath symbolic CTL model checking?

---

### Chapter 7: Equivalences and Abstraction (pp. 449–593)

**Summary:** This chapter develops equivalence and preorder relations between transition systems — bisimulation, simulation, and their stutter-insensitive variants — that let model checking be performed on smaller, abstracted models while preserving the truth of temporal-logic formulae, and gives partition-refinement algorithms for computing the corresponding quotient systems. : [[Mathematical-Preliminaries|Link1]], [[Stutter-Equivalences|Link2]], [[CTL-Star|Link3]], [[Linear-Temporal-Logic|Link4]]

**Key Definitions & Concepts by Section:**
- **7.1 Bisimulation** — bisimulation equivalence ($TS_1 \sim TS_2$, a relation requiring matched initial states, equal labeling, and mutual stepwise simulation of successors); bisimulation as a relation on states of a single $TS$ ($s_1 \sim_{TS} s_2$); coarsest bisimulation; bisimulation quotient $TS/\!\sim$; action-based bisimulation ($\sim^{Act}$, matching transition labels instead of state labels), shown to be a congruence for parallel composition with handshaking. : [[Simulation-Preorders-and-Equivalence|Link1]], [[Bisimulation-Equivalence|Link2]]
- **7.2 Bisimulation and CTL\* Equivalence** — CTL\*-equivalence ($\equiv_{CTL^*}$) and CTL-equivalence of states/systems; the central theorem that for finite transition systems without terminal states, $\sim_{TS} = \equiv_{CTL} = \equiv_{CTL^*}$ (bisimulation is the coarsest equivalence preserving all of CTL\*); master formulae used to characterize equivalence classes logically. : [[Bisimulation-Equivalence|Link]]
- **7.3 Bisimulation-Quotienting Algorithms** — partition, block, superblock; the $AP$-partition $\Pi_{AP}$; refinement operator $\text{Refine}(\Pi,C)$; splitter and stability; a first partition-refinement algorithm ($O(|S|\cdot(|AP|+M))$); an efficiency improvement using a ternary refinement operator that always splits on the smaller half, achieving $O(|S|\cdot|AP| + M\log|S|)$ (Hopcroft-style minimization); checking bisimilarity of two systems via the quotient of their disjoint union; PSPACE-completeness of checking trace equivalence. : [[Simulation-Preorders-and-Equivalence|Link1]], [[Bisimulation-Equivalence|Link2]], [[Partition-Refinement-Algorithms|Link3]]
- **7.4 Simulation Relations** — simulation order ($TS_1 \preceq TS_2$: every step of $TS_1$ can be matched by $TS_2$, but not conversely); abstraction function and induced abstract transition system ($TS \preceq TS_f$); simulation equivalence ($\simeq$); simulation preserves finite trace inclusion and (for systems without terminal states) full trace inclusion; $AP$-deterministic transition systems, for which $\sim$ and $\simeq$ coincide. : [[Bisimulation-Equivalence|Link1]], [[Simulation-Preorders-and-Equivalence|Link2]], [[Computation-Tree-Logic|Link3]], [[Model-Checking-Fundamentals|Link4]]
- **7.5 Simulation and ∀CTL\* Equivalence** — the universal fragment $\forall CTL^*$ (state formulae in positive normal form with only universal path quantification) and its dual $\exists CTL^*$; the theorem that the simulation order coincides with formula implication over $\forall CTL^*$ (equivalently, over $\exists CTL^*$ in the reverse direction). : [[Bisimulation-Equivalence|Link1]], [[Simulation-Preorders-and-Equivalence|Link2]]
- **7.6 Simulation-Quotienting Algorithms** — partition-refinement algorithms for computing the simulation preorder/quotient, analogous to but more involved than the bisimulation case. : [[Simulation-Preorders-and-Equivalence|Link1]], [[Partition-Refinement-Algorithms|Link2]]
- **7.7 Stutter Linear-Time Relations** — stutter step (a self-labeled transition); stutter-equivalence of paths/traces ($\pi_1 \asymp \pi_2$, traces agreeing up to finite repetition blocks); stutter trace equivalence of transition systems ($TS_1 \asymp TS_2$); $LTL_{\setminus\bigcirc}$ (LTL without the next operator); the result that stutter-equivalent traces satisfy the same $LTL_{\setminus\bigcirc}$ formulae; stutter-insensitive LT properties. : [[Stutter-Equivalences|Link]]
- **7.8 Stutter Bisimulation** — stutter bisimulation ($s_1 \approx_{TS} s_2$: a transition of one side may be matched by a whole path fragment of internally-equivalent states on the other); divergence-sensitive stutter bisimulation ($\approx^{div}$, additionally ruling out infinite internal looping); normed (bi)simulation; the theorem that $\approx^{div}$ coincides with $CTL^*_{\setminus\bigcirc}$-equivalence; stutter bisimulation quotienting via $\Pi$-splitters and stutter cycles/exit states. : [[Stutter-Equivalences|Link]]

**Key Questions:**
1. Why does bisimulation equivalence coincide exactly with CTL\* (and even plain CTL) equivalence, and what does this buy you when you only have access to the (much smaller) quotient system $TS/\!\sim$?
2. Simulation is not symmetric, so it cannot be characterized by a logic closed under negation — why does restricting to the universal fragment $\forall CTL^*$ resolve this, and what kind of properties (safety vs. liveness) does the simulation order therefore preserve?
3. Why is the next-operator excluded from $LTL_{\setminus\bigcirc}$ for stutter trace/bisimulation results, and why does stutter bisimulation need to match a single transition against an entire path fragment rather than a single transition?

---

### Chapter 8: Partial Order Reduction (pp. 595–671)

**Summary:** This chapter addresses the state-space explosion caused by interleaving independent concurrent actions by presenting the ample-set method, which explores only a representative subset of enabled actions per state while provably preserving stutter-trace equivalence (for LTL) or divergence-sensitive stutter bisimulation (for CTL/CTL\*). : [[Partial-Order-Reduction|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Independence of Actions** — independence of two actions $\alpha,\beta$ (commuting and non-disabling whenever both are enabled); dependence; independence of an action from a set of actions; stutter action (an action whose execution never changes the state labeling); key lemmas on permuting independent actions within an execution fragment (finite and infinite), and on permuting/adding independent stutter actions while preserving stutter equivalence of the resulting executions. : [[Partial-Order-Reduction|Link]]
- **8.2 The Linear-Time Ample Set Approach** — ample set $ample(s) \subseteq Act(s)$, the reduced set of actions explored at $s$, yielding the reduced transition system $\widehat{TS}$; goal: $TS \asymp \widehat{TS}$ (stutter trace equivalence), sound for $LTL_{\setminus\bigcirc}$. : [[Partial-Order-Reduction|Link]]
  - **8.2.1 Ample Set Constraints** — the four conditions (A1)–(A4): (A1) nonemptiness ($\emptyset \ne ample(s) \subseteq Act(s)$); (A2) dependency condition (any action depending on $ample(s)$ must be preceded by some action of $ample(s)$ along every execution); (A3) stutter condition (if $ample(s) \ne Act(s)$, every action in $ample(s)$ must be a stutter action); (A4) cycle condition (every action enabled somewhere on a cycle of $\widehat{TS}$ must eventually be included in some $ample(s_j)$ along that cycle, precluding action starvation by the reduction). : [[Partial-Order-Reduction|Link1]], [[Real-Time-Systems-and-Timed-Automata|Link2]], [[Automata-over-Finite-and-Infinite-Words|Link3]], [[Automata-Based-Verification-of-Properties|Link4]]
  - **8.2.2 Dynamic Partial Order Reduction** — on-the-fly computation of $\widehat{TS}$ interleaved with LTL model checking of $\widehat{TS}\otimes A_{\neg\varphi}$, avoiding full generation of $TS$. : [[Partial-Order-Reduction|Link]]
  - **8.2.3 Computing Ample Sets** — practical, syntax-directed (program-graph-based) heuristics approximating conditions (A1)–(A4), typically using process-local "safe" or invisible transitions as ample-set candidates. : [[Partial-Order-Reduction|Link1]], [[Mathematical-Preliminaries|Link2]]
  - **8.2.4 Static Partial Order Reduction** — computing a symbolic reduced program (an $\widehat{TS}$ representation) as a preprocessing phase prior to verification, rather than during state-space exploration. : [[Partial-Order-Reduction|Link]]
- **8.3 The Branching-Time Ample Set Approach** — shows by counterexample that conditions (A1)–(A4) alone (sufficient for LTL) do not preserve $CTL_{\setminus\bigcirc}$; strengthens the approach so that $TS \approx^{div} \widehat{TS}$ (divergence-sensitive stutter bisimulation), which is sound for $CTL_{\setminus\bigcirc}$ and $CTL^*_{\setminus\bigcirc}$; introduces the additional conditions needed (beyond A1–A4) to guarantee branching-time-preserving reductions. : [[Partial-Order-Reduction|Link]]

**Key Questions:**
1. Why is the dependency condition (A2) — not merely picking *some* nonempty subset of enabled actions — the crux of soundness for partial order reduction, and what goes wrong if it is dropped?
2. Why does the cycle condition (A4) exist, and what pathological behavior (e.g., a process being perpetually ignored by the reduction) would arise without it?
3. Why do the linear-time ample-set conditions (A1)–(A4), sufficient for $LTL_{\setminus\bigcirc}$, fail to preserve $CTL_{\setminus\bigcirc}$ formulae in general, and what does moving from stutter trace equivalence to divergence-sensitive stutter bisimulation buy you to fix this?

---

### Chapter 9: Timed Automata (pp. 673–743)

**Summary:** This chapter extends the model-checking framework to real-time systems by adding real-valued clocks to program graphs, yielding timed automata whose infinite-state transition-system semantics must be handled via the finite "region" abstraction; it then introduces Timed CTL (TCTL) and shows TCTL model checking is decidable, in fact PSPACE-complete, by reducing it to CTL model checking on a finite region transition system. : [[Real-Time-Systems-and-Timed-Automata|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Timed Automata** — clock (a real-valued variable that only resets or advances at rate 1), clock constraint $g$ (conjunction of atomic comparisons $x < c$, $x \le c$, etc.), timed automaton $TA = (Loc, Act, C, \rightarrow, Loc_0, Inv, AP, L)$ (a program graph over clocks with edge guards/resets and per-location invariants), location invariant (bounds residence time in a location; the only means to force a transition), handshaking/parallel composition of timed automata ($TA_1 \|_H TA_2$), clock valuation $\eta$, transition system semantics $TS(TA)$ combining discrete transitions (guarded, resetting) and delay transitions ($\ell,\eta \xrightarrow{d} \ell,\eta{+}d$). : [[Real-Time-Systems-and-Timed-Automata|Link]]
  - **9.1.1 Semantics** — discrete vs. delay transitions, uncountably infinite/branching state space, multiple actions taking place in zero time.
  - **9.1.2 Time Divergence, Timelock, and Zenoness** — elapsed time of a path (ExecTime), time-divergent vs. time-convergent path, timelock (a state from which no time-divergent path emanates; timed automata should be timelock-free), zeno path (time-convergent with infinitely many actions; represents an unrealizable infinitely-fast execution), non-zenoness. : [[Real-Time-Systems-and-Timed-Automata|Link]]
- **9.2 Timed Computation Tree Logic** — TCTL syntax ($\Phi ::= true \mid a \mid g \mid \Phi\land\Phi \mid \neg\Phi \mid \exists\varphi \mid \forall\varphi$, with $\varphi ::= \Phi\, U^J\, \Phi$ for interval $J$), timed modalities $\Diamond^J$, $\Box^J$, path quantification restricted to time-divergent paths only (analogous to fair-path quantification in fair CTL), the subtlety that $\Phi\,U^J\,\Psi$ requires $\Phi\lor\Psi$ (not just $\Phi$) along the prefix, timelock-freedom characterized by $\exists\, true$. : [[Computation-Tree-Logic|Link]]
- **9.3 TCTL Model Checking** — reduction scheme $TA \models_{TCTL} \Phi$ iff $RTS(TA,\Phi) \models_{CTL} \bar\Phi$. : [[Timed-CTL-and-TCTL-Model-Checking|Link1]], [[CTL-Model-Checking|Link2]]
  - **9.3.1 Eliminating Timing Parameters** — using a fresh clock $z$ to reduce a timed until bound $U^J$ to an atomic clock constraint on $z$, reducing TCTL to $\text{TCTL}_\Diamond \subseteq$ CTL. : [[Timed-CTL-and-TCTL-Model-Checking|Link]]
  - **9.3.2 Region Transition Systems** — clock equivalence $\sim_c$ (identifies clock valuations that agree on integer parts up to the maximal constants and on the ordering of fractional parts), clock region (an equivalence class of $\sim_c$), state region $[\ell,\eta]$, region transition system $RTS(TA,\Phi)$ (finite quotient of $TS(TA)$ that is a bisimulation w.r.t. clock constraints and time-divergent successors); number of clock regions is exponential in the number of clocks and the maximal constants. : [[Timed-CTL-and-TCTL-Model-Checking|Link]]
  - **9.3.3 The TCTL Model-Checking Algorithm** — bottom-up labeling of the region transition system by subformula (as in CTL model checking); TCTL model checking is $O((N+K)\cdot|\Phi|)$ in the size of the region transition system, and PSPACE-complete overall. : [[CTL-Model-Checking|Link1]], [[Timed-CTL-and-TCTL-Model-Checking|Link2]]

**Key Questions:**
1. Why must an invariant (rather than just a stronger guard) be used to force a timed automaton to take a transition within a bounded time, and what would go wrong if only guards were used?
2. Why does the semantics of $\Phi\,U^J\,\Psi$ require $\Phi\lor\Psi$ (rather than just $\Phi$) to hold before the witnessing $\Psi$-state, unlike the untimed until of LTL/CTL?
3. Why is TCTL model checking reduced to CTL model checking on a *finite* region transition system rather than performed directly on $TS(TA)$, and why is the region equivalence a bisimulation with respect to both atomic clock constraints and time-divergent path behavior?

---

### Chapter 10: Probabilistic Systems (pp. 745–908)

**Summary:** This long chapter replaces nondeterministic transitions with probabilistic ones, first for (discrete-time) Markov chains — covering reachability, qualitative/quantitative properties, the logic PCTL and its qualitative fragment, LTL model checking via product with deterministic Rabin automata, PCTL$^*$, probabilistic bisimulation, and Markov reward models — and then for Markov decision processes (MDPs), which reintroduce nondeterminism resolved by schedulers, covering extremal reachability probabilities, PCTL model checking, end components for long-run behavior, and fairness. : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link1]], [[Probabilistic-Computation-Tree-Logic|Link2]], [[Markov-Chains-and-Probabilistic-Verification|Link3]], [[Simulation-Preorders-and-Equivalence|Link4]]

**Key Definitions & Concepts by Section:**
- **10.1 Markov Chains** — (discrete-time) Markov chain $M=(S,P,\iota_{init},AP,L)$ (memoryless: successor distribution depends only on the current state), transition probability function $P$, absorbing state, $TS(M)$ (the transition system abstracting away probabilities, used for qualitative LTL/CTL reasoning), probability space $(Outc,E,Pr)$/σ-algebra, cylinder set, σ-algebra of a Markov chain. : [[Markov-Chains-and-Probabilistic-Verification|Link1]], [[Markov-Decision-Processes|Link2]], [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link3]], [[Probabilistic-Computation-Tree-Logic|Link4]]
  - **10.1.1 Reachability Probabilities** — bottom strongly connected component (BSCC), $Pr(s \models \Diamond B)$ obtained via a linear equation system over the "unknown" states, unconstrained vs. constrained reachability. : [[Markov-Chains-and-Probabilistic-Verification|Link1]], [[Markov-Decision-Processes|Link2]]
  - **10.1.2 Qualitative Properties** — almost-sure reachability of a BSCC, repeated reachability and persistence expressed via accepting BSCCs, checkable purely by graph algorithms for finite MCs. : [[Markov-Chains-and-Probabilistic-Verification|Link]]
- **10.2 Probabilistic Computation Tree Logic** — PCTL syntax ($\Phi ::= true \mid a \mid \Phi_1\land\Phi_2 \mid \neg\Phi \mid P_J(\varphi)$ with $\varphi ::= \bigcirc\Phi \mid \Phi_1 U \Phi_2 \mid \Phi_1 U^{\le n}\Phi_2$), the probabilistic operator $P_J(\varphi)$ as the quantitative counterpart to $\exists/\forall$, measurability of PCTL path events, PCTL equivalences (e.g. $P_{<p}(\varphi)\equiv\neg P_{\ge p}(\varphi)$), counterexamples/witnesses as finite sets of paths whose probability mass exceeds a bound. : [[Probabilistic-Computation-Tree-Logic|Link]]
  - **10.2.1 PCTL Model Checking** — bottom-up parse-tree evaluation of $Sat(\Phi)$; next-step via matrix-vector multiplication; bounded/unbounded until via vector-matrix iteration / linear equation systems; time complexity $O(poly(size(M))\cdot n_{max}\cdot|\Phi|)$. : [[Markov-Decision-Processes|Link1]], [[Probabilistic-Computation-Tree-Logic|Link2]], [[CTL-Model-Checking|Link3]]
  - **10.2.2 The Qualitative Fragment of PCTL** — fragment restricted to bounds $>0$ and $=1$; incomparable in expressiveness with CTL in general (though PCTL can express persistence, which CTL cannot). : [[Probabilistic-Computation-Tree-Logic|Link]]
- **10.3 Linear-Time Properties** — computing the probability of an LT property via the product of $M$ with a deterministic Rabin automaton (DRA) for the (complement of the) property. : [[Linear-Time-Properties|Link]]
- **10.4 PCTL$^*$ and Probabilistic Bisimulation** — : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
  - **10.4.1 PCTL$^*$** — PCTL$^*$ syntax (LTL-style path formulae combined with the probability operator $P_J$), double-exponential (or single-exponential via alternative techniques) model-checking complexity in $|\varphi|$ due to the DRA translation.
  - **10.4.2 Probabilistic Bisimulation** — probabilistic bisimulation on Markov chains (equal labels, equal cumulative transition probability $P(s,T)$ to every equivalence class $T$), bisimulation quotient, coincidence of probabilistic bisimulation with PCTL/PCTL$^*$ equivalence (the quantitative analogue of the CTL/CTL$^*$–bisimulation correspondence of Chapter 7). : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
- **10.5 Markov Chains with Costs** — Markov reward model (MRM) $(M, rew)$, cumulative reward along a finite path. : [[Markov-Chains-and-Probabilistic-Verification|Link1]], [[Markov-Decision-Processes|Link2]], [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link3]], [[Probabilistic-Computation-Tree-Logic|Link4]]
  - **10.5.1 Cost-Bounded Reachability** — expected reward until reaching a target set $B$, $ExpRew(s \models \Diamond B)$. : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
  - **10.5.2 Long-Run Properties** — long-run (steady-state) distributions, expected long-run reward between $B$-states. : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link]]
- **10.6 Markov Decision Processes** — Markov decision process (MDP) $M=(S,Act,P,\iota_{init},AP,L)$ (nondeterministic choice of enabled action, then probabilistic choice of successor), Markov chains as MDPs with singleton action sets, Probmela (a probabilistic guarded-command modeling language with random assignment, probabilistic choice, and lossy channels). : [[Markov-Decision-Processes|Link]]
  - **10.6.1 Reachability Probabilities** — path in an MDP, scheduler (a.k.a. adversary/policy/strategy) resolving nondeterminism, induced Markov chain $M^{\mathcal S}$, maximal/minimal reachability probability $Pr_{max}/Pr_{min}(s\models\Diamond B)$, computed via a linear equation system (with memoryless schedulers sufficing) or equivalently a linear program. : [[Markov-Chains-and-Probabilistic-Verification|Link1]], [[Markov-Decision-Processes|Link2]]
  - **10.6.2 PCTL Model Checking** — PCTL over MDPs interprets $P_J(\varphi)$ as ranging over all schedulers; reduces to computing extremal reachability probabilities. : [[Markov-Decision-Processes|Link1]], [[Probabilistic-Computation-Tree-Logic|Link2]], [[CTL-Model-Checking|Link3]]
  - **10.6.3 Limiting Properties** — sub-MDP, end component (a sub-MDP whose induced digraph is strongly connected), recurrence property of end components, the limit of almost every path under any scheduler is an end component; long-run behavior analyzed via extremal probability of reaching an accepting end component. : [[Linear-Time-Properties|Link]]
  - **10.6.4 Linear-Time Properties and PCTL$^*$** — automata-based (Rabin-automaton product) approach to ω-regular / PCTL$^*$ model checking on MDPs, analogous to the MC case but under extremal schedulers. : [[Markov-Decision-Processes|Link]]
  - **10.6.5 Fairness** — fair scheduler (almost surely generates only fair paths); fairness is irrelevant for maximal reachability but affects minimal reachability probabilities. : [[Fairness|Link]]

**Key Questions:**
1. Why does an MDP not come with a unique probability measure over its paths the way a Markov chain does, and what role does a scheduler play in fixing one?
2. In what precise sense are probabilistic bisimulation, PCTL equivalence, and PCTL$^*$ equivalence on Markov chains the same relation, and how does this mirror the bisimulation/CTL$^*$ correspondence for ordinary transition systems (Chapter 7)?
3. Why does the qualitative fragment of PCTL fail to coincide with CTL even though both only distinguish "always/never" versus "sometimes," and what property (expressible in PCTL but not CTL) exposes the gap?

---

### Appendix A: Preliminaries (pp. 909–929)

**Summary:** A self-contained reference chapter collecting the mathematical background assumed by the rest of the book: notation, relations/equivalences/partitions, formal language theory (words, regular expressions), propositional logic syntax/semantics, elementary graph theory and graph algorithms (DFS/BFS, SCCs), and the basic concepts of computational complexity (deterministic/nondeterministic algorithms, PTIME, NP, PSPACE) used to state the complexity results throughout the book. : [[Probabilistic-Bisimulation-and-Markov-Reward-Models|Link1]], [[Probabilistic-Computation-Tree-Logic|Link2]], [[Markov-Chains-and-Probabilistic-Verification|Link3]], [[Simulation-Preorders-and-Equivalence|Link4]]

**Key Definitions & Concepts by Section:**
- **A.1 Frequently Used Symbols and Notations** — Landau symbols $O,\Omega,\Theta$ (asymptotic upper/lower/tight bounds), relation properties (transitive, reflexive, symmetric, antisymmetric), equivalence relation and equivalence class $[x]_R$, quotient space $X/R$, index of an equivalence relation, refinement (finer/coarser) of equivalence relations, transitive-reflexive closure $R^*$, partition of a set, preorder and its kernel.
- **A.2 Formal Languages** — alphabet, word, prefix/suffix/subword, concatenation and Kleene star ($L^*$, $L^+$), regular expression and its language $L(E)$, regular language.
- **A.3 Propositional Logic** — propositional formula (inductively defined from $true$, atomic propositions, $\neg$, $\land$), derived operators ($\lor,\to,\leftrightarrow,\oplus$), abstract syntax via BNF grammar, length of a formula.
- **A.4 Graphs** — digraph, successors/predecessors $Post(v)/Pre(v)$, terminal vertex, path/simple path/cycle, reachability $Post^*(v)$, depth-first search (DFS) and breadth-first search (BFS) as instances of a generic reachability-analysis skeleton, backward edge (used for cycle detection), strongly connected component (SCC) and terminal SCC, (directed) tree/root/leaf, Hamiltonian path, undirected graph.
- **A.5 Computational Complexity** — decision problem, deterministic vs. nondeterministic algorithm ("guess and check"), time/space complexity functions $T_A, S_A$, polytime/polyspace algorithm, complexity classes PTIME, NP, PSPACE, NPSPACE (with PSPACE = NPSPACE), coNP, the open PTIME-vs-NP and NP-vs-PSPACE questions.

**Key Questions:**
1. Why is a nondeterministic algorithm's correctness criterion asymmetric between the "yes" and "no" cases (as in the definitions given for SAT), and how does this asymmetry underlie the definition of NP?
2. How does the notion of bisimulation-style equivalence refinement (finer/coarser partitions, index of a relation) recur across the book's later partition-refinement algorithms for transition systems and Markov chains?
