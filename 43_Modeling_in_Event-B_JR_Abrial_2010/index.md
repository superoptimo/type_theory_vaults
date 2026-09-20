# Modeling in Event-B: System and Software Engineering — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Formal Methods and the Modeling Philosophy** : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Formal methods versus testing : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Modeling as blueprint construction : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Requirements document structure and traceability labels : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Explanatory text versus reference text : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Solution validation versus problem validation : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
   - Discovering requirements through failed proofs : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]

2. **Discrete Transition Systems** : [[Discrete-Transition-Systems|Link]]
   - State as a set of variables : [[Discrete-Transition-Systems|Link]]
   - Events as guards and actions : [[Discrete-Transition-Systems|Link]]
   - Deterministic and non-deterministic actions : [[Discrete-Transition-Systems|Link]]
   - Before-after predicates : [[Discrete-Transition-Systems|Link]]
   - Invariants and gluing invariants : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Discrete-Transition-Systems|Link2]], [[Refinement-Theory|Link3]]
   - Conditional invariants : [[Discrete-Transition-Systems|Link]]
   - Deadlock and deadlock freedom : [[Case-Study-Access-Control-and-Train-Systems|Link1]], [[Discrete-Transition-Systems|Link2]]
   - Closed models of a controller and its environment : [[Discrete-Transition-Systems|Link]]

3. **The Event-B Notation** : [[The-Event-B-Notation|Link]]
   - Machines and contexts : [[The-Event-B-Notation|Link]]
   - Sees extends and refines relationships : [[The-Event-B-Notation|Link]]
   - Carrier sets constants and axioms : [[The-Event-B-Notation|Link]]
   - Event parameters and witnesses : [[The-Event-B-Notation|Link]]
   - Convergent anticipated and ordinary events : [[The-Event-B-Notation|Link]]
   - Numeric and finite-set variants : [[The-Event-B-Notation|Link]]
   - Functional override and non-deterministic assignment : [[The-Event-B-Notation|Link]]

4. **Proof Obligation Rules** : [[Proof-Obligation-Rules|Link]]
   - Invariant preservation : [[Proof-Obligation-Rules|Link]]
   - Feasibility : [[Proof-Obligation-Rules|Link]]
   - Guard strengthening : [[Proof-Obligation-Rules|Link]]
   - Guard merging : [[Proof-Obligation-Rules|Link]]
   - Simulation : [[Proof-Obligation-Rules|Link]]
   - Convergence via natural-number or finite-set variants : [[The-Event-B-Notation|Link1]], [[Proof-Obligation-Rules|Link2]]
   - Witness feasibility : [[Proof-Obligation-Rules|Link]]
   - Theorem and well-definedness obligations : [[Proof-Obligation-Rules|Link]]
   - Relative deadlock freedom : [[Discrete-Transition-Systems|Link]]

5. **The Sequent Calculus and Logical Inference** : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Sequents rules of inference and proof trees : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Theories as sets of inference rules
   - Propositional inference rules : [[The-Sequent-Calculus-and-Logical-Inference|Link1]], [[Sequential-Program-Derivation|Link2]]
   - Predicate language and quantifier rules : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Equality and one point rules : [[The-Sequent-Calculus-and-Logical-Inference|Link]]
   - Proof by cases

6. **The Set-Theoretic Mathematical Language** : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Set comprehension and the extensionality axiom
   - Binary relation operators : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Domain and range restriction and subtraction
   - Partial and total functions
   - Lambda abstraction and function application
   - Boolean and arithmetic language : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Well-definedness conditions : [[The-Set-Theoretic-Mathematical-Language|Link]]
   - Peano axioms for natural numbers

7. **Advanced Data Structures** : [[Advanced-Data-Structures|Link]]
   - Irreflexive transitive closure : [[Advanced-Data-Structures|Link]]
   - Strongly connected graphs : [[Advanced-Data-Structures|Link]]
   - Infinite and finite lists : [[Advanced-Data-Structures|Link]]
   - Rings
   - Infinite finite-depth and free trees : [[Advanced-Data-Structures|Link]]
   - Tree induction and list induction : [[Advanced-Data-Structures|Link1]], [[Case-Study-Distributed-Network-Algorithms|Link2]]
   - Well-founded relations : [[Exercises-Projects-and-Mathematical-Developments|Link]]

8. **Refinement Theory** : [[Refinement-Theory|Link]]
   - Horizontal refinement
   - Vertical or data refinement : [[Case-Study-Communication-Protocols|Link1]], [[Case-Study-Distributed-Network-Algorithms|Link2]], [[Refinement-Theory|Link3]]
   - Superposition refinement
   - Splitting and merging events : [[Refinement-Theory|Link]]
   - New events and convergence : [[Refinement-Theory|Link]]
   - Forward and backward simulation : [[Refinement-Theory|Link]]
   - Trace semantics of refinement : [[Refinement-Theory|Link]]
   - Gluing invariants linking abstract and concrete state
   - External and internal variables : [[Refinement-Theory|Link]]

9. **Design Patterns for Reactive Controllers** : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - The action-reaction pattern : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - Weak synchronization of an action and a reaction : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - Strong synchronization of an action and a reaction : [[Design-Patterns-for-Reactive-Controllers|Link]]
   - Composing synchronization patterns across two action-reaction pairs : [[Design-Patterns-for-Reactive-Controllers|Link]]

10. **Case Study: Bridge and Press Controllers** : [[Case-Study-Bridge-and-Press-Controllers|Link]]
    - Controlling cars on a one-way bridge : [[Case-Study-Bridge-and-Press-Controllers|Link]]
    - Traffic lights and car sensors
    - The mechanical press controller : [[Case-Study-Bridge-and-Press-Controllers|Link]]
    - Motor clutch and door safety constraints

11. **Case Study: Communication Protocols** : [[Case-Study-Communication-Protocols|Link]]
    - The two-phase handshake file transfer protocol : [[Case-Study-Communication-Protocols|Link]]
    - The bounded retransmission protocol : [[Case-Study-Communication-Protocols|Link]]
    - Fault tolerance and timer-based abortion
    - The alternating bit and parity optimizations
    - Anticipated events in protocol development : [[Case-Study-Communication-Protocols|Link1]], [[Exercises-Projects-and-Mathematical-Developments|Link2]], [[Sequential-Program-Derivation|Link3]]

12. **Case Study: Concurrent Programs and Electronic Circuits** : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Simpson's four-slot fully asynchronous mechanism : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Interleaving of concurrent instructions : [[Formal-Methods-and-the-Modeling-Philosophy|Link]]
    - Writing and reading traces : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Synchronous electronic circuit modeling : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]
    - Circuit-environment coupling and the bool operator : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link1]], [[Case-Study-Distributed-Network-Algorithms|Link2]]
    - The single pulser and the arbiter circuits
    - The road traffic light circuit : [[Case-Study-Concurrent-Programs-and-Electronic-Circuits|Link]]

13. **Case Study: Distributed Network Algorithms** : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Leader election on a ring-shaped network : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Phase synchronization on a tree-shaped network : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Mobile agent routing with logical clocks : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Leader election on a connected graph network : [[Case-Study-Distributed-Network-Algorithms|Link]]
    - Contention resolution and symmetry breaking

14. **Sequential Program Derivation** : [[Sequential-Program-Derivation|Link]]
    - Naked events and implicit scheduling : [[Sequential-Program-Derivation|Link]]
    - Anticipated and convergent event status : [[Sequential-Program-Derivation|Link]]
    - Merging rules for if-statements and while-loops : [[Sequential-Program-Derivation|Link1]], [[Formal-Methods-and-the-Modeling-Philosophy|Link2]]
    - Binary search and sorting derivations : [[Sequential-Program-Derivation|Link]]
    - Pointer-based linked-list derivation : [[Sequential-Program-Derivation|Link]]
    - Generic function inversion and instantiation : [[Sequential-Program-Derivation|Link]]

15. **Case Study: Access Control and Train Systems** : [[Case-Study-Access-Control-and-Train-Systems|Link]]
    - The location access controller : [[Case-Study-Bridge-and-Press-Controllers|Link1]], [[Design-Patterns-for-Reactive-Controllers|Link2]], [[Case-Study-Access-Control-and-Train-Systems|Link3]]
    - Card readers turnstiles and doors
    - Physical versus logical variables
    - The train network safety system
    - Routes blocks signals and points

16. **Exercises Projects and Mathematical Developments** : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - End-of-book exercises and larger projects : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - Well-founded induction and fixpoint theory : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - The Cantor-Bernstein theorem : [[Exercises-Projects-and-Mathematical-Developments|Link]]
    - Zermelo's well-ordering theorem : [[Exercises-Projects-and-Mathematical-Developments|Link]]

---
