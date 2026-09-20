# Practical Foundations for Programming Languages — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Syntactic Objects and Binding** : [[Syntactic-Objects-and-Binding|Link]]
   - Abstract syntax trees classified by sorts and operators with arities : [[Syntactic-Objects-and-Binding|Link]]
   - Variables as unknowns given meaning by substitution : [[Syntactic-Objects-and-Binding|Link]]
   - Parameters as symbolic identifiers admitting disequality : [[Syntactic-Objects-and-Binding|Link]]
   - Abstract binding trees with abstractors and valences : [[Syntactic-Objects-and-Binding|Link]]
   - $\alpha$-equivalence and identification up to renaming : [[Syntactic-Objects-and-Binding|Link]]
   - Capture-avoiding substitution and the freshness condition : [[Syntactic-Objects-and-Binding|Link]]

2. **Inductive Definitions and Rule Induction** : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Judgments and judgment forms over syntactic objects : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Inference rules as sufficient conditions for judgments : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Derivations as finite compositions of rules : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Forward and backward chaining search strategies : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Rule induction as reasoning over the strongest closed judgment : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Iterated and simultaneous inductive definitions : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Defining functions by their graph with existence and uniqueness : [[Inductive-Definitions-and-Rule-Induction|Link]]
   - Mode specifications of inputs and outputs : [[Inductive-Definitions-and-Rule-Induction|Link]]

3. **Hypothetical and General Judgments** : [[Hypothetical-and-General-Judgments|Link]]
   - Derivability as entailment stable under rule extension : [[Hypothetical-and-General-Judgments|Link]]
   - Admissibility as closure under already-derivable judgments : [[Hypothetical-and-General-Judgments|Link]]
   - Hypothetical rules with global and local hypotheses : [[Hypothetical-and-General-Judgments|Link]]
   - Generic judgments ranging over fresh variable renamings : [[Hypothetical-and-General-Judgments|Link]]
   - Parametric judgments ranging over fresh symbol renamings : [[Hypothetical-and-General-Judgments|Link]]
   - Structural properties of proliferation renaming and substitution : [[Hypothetical-and-General-Judgments|Link]]

4. **Statics and Dynamics** : [[Function-Types-and-the-Lambda-Calculus|Link1]], [[Statics-And-Dynamics|Link2]]
   - Phase distinction between static checking and dynamic execution
   - Type systems as inductive definitions of typing judgments : [[Statics-And-Dynamics|Link]]
   - Transition systems with states initial and final : [[Statics-And-Dynamics|Link]]
   - Structural dynamics with instruction and search rules : [[Statics-And-Dynamics|Link]]
   - Contextual dynamics with evaluation contexts and holes : [[Statics-And-Dynamics|Link]]
   - Equational dynamics as definitional equality : [[Statics-And-Dynamics|Link]]
   - Evaluation dynamics relating expressions directly to values : [[Statics-And-Dynamics|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]]
   - Cost dynamics augmenting evaluation with step counts : [[Statics-And-Dynamics|Link]]

5. **Type Safety** : [[Type-Safety|Link]]
   - Preservation of typing under transition
   - Progress of well-typed closed expressions : [[Type-Safety|Link]]
   - Canonical forms characterizing values by type : [[Type-Safety|Link]]
   - Stuck states as ill-defined programs
   - Checked versus unchecked run-time errors : [[Type-Safety|Link]]

6. **Function Types and the Lambda Calculus** : [[Function-Types-and-the-Lambda-Calculus|Link]]
   - First-order function definitions by substitution : [[Function-Types-and-the-Lambda-Calculus|Link]]
   - Higher-order functions as first-class values : [[Function-Types-and-the-Lambda-Calculus|Link]]
   - $\lambda$-abstraction as introduction and application as elimination : [[Function-Types-and-the-Lambda-Calculus|Link]]
   - Call-by-value versus call-by-name dynamics : [[Function-Types-and-the-Lambda-Calculus|Link]]
   - Static binding versus dynamic binding : [[Function-Types-and-the-Lambda-Calculus|Link]]
   - Evaluation dynamics and definitional equality for functions : [[Function-Types-and-the-Lambda-Calculus|Link]]

7. **Gödel's System T and Total Computation** : [[Godels-System-T-and-Total-Computation|Link]]
   - Primitive recursion with predecessor and recursive call : [[Product-Types|Link]]
   - Iteration as a restricted form of recursion : [[Polymorphism-and-System-F|Link]]
   - Definability of total functions including Ackermann's function : [[Plotkins-PCF-and-Partial-Computation|Link]]
   - Intrinsic termination from the structure of recursion : [[Statics-And-Dynamics|Link1]], [[Godels-System-T-and-Total-Computation|Link2]], [[Generic-Programming|Link3]]
   - Undefinability of the universal function by diagonalization : [[Godels-System-T-and-Total-Computation|Link]]
   - Gödel-numbering of expressions as data : [[Generic-Programming|Link]]

8. **Plotkin's PCF and Partial Computation** : [[Plotkins-PCF-and-Partial-Computation|Link]]
   - General recursion as the least fixed point operator : [[Plotkins-PCF-and-Partial-Computation|Link]]
   - Unwinding the recursion by self-substitution : [[Plotkins-PCF-and-Partial-Computation|Link]]
   - Partial functions and definability via minimization : [[Plotkins-PCF-and-Partial-Computation|Link]]
   - Church's Law identifying effective computability : [[Plotkins-PCF-and-Partial-Computation|Link]]
   - Definability of the universal function as an interpreter : [[Plotkins-PCF-and-Partial-Computation|Link]]

9. **Product Types** : [[Product-Types|Link]]
   - Binary and finite products as ordered tuples : [[Product-Types|Link]]
   - Nullary product as the unit type : [[Product-Types|Link]]
   - Projections as elimination forms : [[Product-Types|Link1]], [[Propositions-as-Types|Link2]], [[Sum-Types|Link3]], [[Statics-And-Dynamics|Link4]]
   - Eager versus lazy dynamics for pairing : [[Product-Types|Link]]
   - Encoding primitive recursion from iteration via pairs : [[Product-Types|Link]]
   - Mutual recursion as recursion over a product : [[Product-Types|Link]]

10. **Sum Types** : [[Sum-Types|Link]]
    - Binary and finite sums as tagged alternatives : [[Sum-Types|Link]]
    - Nullary sum as the void type with abort elimination : [[Product-Types|Link]]
    - Case analysis as the elimination form : [[Sum-Types|Link]]
    - Booleans and enumerations encoded as sums : [[Sum-Types|Link]]
    - Option types and the null pointer fallacy : [[Sum-Types|Link]]

11. **Pattern Matching** : [[Pattern-Matching|Link]]
    - Pattern language with wildcards variables pairs and injections
    - Match and mismatch judgments with substitutions
    - Typing of rules and rule sequences : [[Pattern-Matching|Link]]
    - Exhaustiveness enforced by match constraints
    - Redundancy elimination relative to preceding rules
    - De Morgan dual for negating constraints : [[Pattern-Matching|Link]]

12. **Generic Programming** : [[Generic-Programming|Link]]
    - Type operators marking spots for transformation : [[Generic-Programming|Link]]
    - Polynomial type operators from sums and products : [[Generic-Programming|Link]]
    - Positive type operators allowing restricted function types : [[Generic-Programming|Link]]
    - Generic extension by mapping a function through a structure : [[Generic-Programming|Link]]
    - Functorial action of type constructors : [[Generic-Programming|Link]]

13. **Inductive and Coinductive Types** : [[Inductive-and-Coinductive-Types|Link]]
    - Inductive types as least solutions of type equations : [[Polymorphism-and-System-F|Link1]], [[Inductive-Definitions-and-Rule-Induction|Link2]]
    - Recursors or catamorphisms for inductive types : [[Inductive-and-Coinductive-Types|Link1]], [[Recursive-Types|Link2]]
    - Coinductive types as greatest solutions of type equations : [[Polymorphism-and-System-F|Link1]], [[Inductive-Definitions-and-Rule-Induction|Link2]]
    - Generators or anamorphisms for coinductive types : [[Inductive-and-Coinductive-Types|Link]]
    - Streams characterized by head and tail observations
    - Positivity requirement on recursive type operators : [[Dynamic-Typing-and-Hybrid-Typing|Link]]

14. **Recursive Types** : [[Recursive-Types|Link]]
    - Solutions to type isomorphism equations $\mu t.\tau \cong [\mu t.\tau/t]\tau$
    - Fold and unfold as introduction and elimination : [[Inductive-and-Coinductive-Types|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]], [[Recursive-Types|Link3]]
    - Recursive representations of lists and trees : [[Recursive-Types|Link]]
    - Streams via lazy recursive types : [[Recursive-Types|Link]]
    - Self-reference and general recursion derived from recursive types
    - Origin of state from feedback and self-reference : [[Recursive-Types|Link]]

15. **Dynamic Types and the Untyped Lambda Calculus** : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link]]
    - Untyped $\lambda$-calculus as the uni-typed language : [[Function-Types-and-the-Lambda-Calculus|Link1]], [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link2]]
    - Church numerals and encodings of arithmetic
    - Y combinator and fixed points
    - Scott's theorem on undecidability of definitional equality : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link]]
    - Embedding the untyped calculus into recursive type $D \cong D \to D$

16. **Dynamic Typing and Hybrid Typing** : [[Dynamic-Typing-and-Hybrid-Typing|Link]]
    - Dynamically classified values with run-time class tags : [[Data-Abstraction-and-Existential-Types|Link1]], [[Dynamic-Classification|Link2]]
    - Class checking judgments and run-time errors
    - Dynamic typing as a restricted static language : [[Dynamic-Typing-and-Hybrid-Typing|Link]]
    - Hybrid language with type dyn and cast operations : [[State-and-Assignables|Link]]
    - Optimization of dynamic code by hoisting checks : [[Dynamic-Typing-and-Hybrid-Typing|Link]]

17. **Polymorphism and System F** : [[Polymorphism-and-System-F|Link]]
    - [[Polymorphism-and-System-F|Type abstraction $\Lambda(t.e)$ and type application $e[\tau]$]] : [[Polymorphism-and-System-F|Link]]
    - Universal type $\forall(t.\tau)$ : [[Polymorphism-and-System-F|Link]]
    - Impredicative instantiation by polymorphic types : [[Polymorphism-and-System-F|Link]]
    - Church encodings of products sums and natural numbers : [[Polymorphism-and-System-F|Link]]
    - Parametricity and free theorems : [[Polymorphism-and-System-F|Link]]
    - Predicative prenex and rank-restricted fragments : [[Polymorphism-and-System-F|Link]]

18. **Data Abstraction and Existential Types** : [[Data-Abstraction-and-Existential-Types|Link]]
    - Packages as implementations and clients as open expressions
    - Existential type $\exists(t.\tau)$ as an interface : [[Data-Abstraction-and-Existential-Types|Link]]
    - Representation independence of clients : [[Data-Abstraction-and-Existential-Types|Link1]], [[Equational-Reasoning|Link2]], [[Modularity-and-Linking|Link3]]
    - Bisimilarity of implementations via a relation
    - Definability of existentials from universals : [[Data-Abstraction-and-Existential-Types|Link]]

19. **Constructors and Kinds** : [[Constructors-and-Kinds|Link]]
    - Kinds as classifiers of static data : [[Constructors-and-Kinds|Link]]
    - Neutral and canonical constructor forms : [[Constructors-and-Kinds|Link]]
    - Kind T of types as classifiers of expressions : [[Constructors-and-Kinds|Link]]
    - Canonizing hereditary substitution : [[Constructors-and-Kinds|Link1]], [[Plotkins-PCF-and-Partial-Computation|Link2]]
    - Canonization of general-form constructors

20. **Singleton and Dependent Kinds** : [[Singleton-and-Dependent-Kinds|Link]]
    - Singleton kind $S(\tau)$ pinning a type up to definitional equality : [[Statics-And-Dynamics|Link]]
    - Subkinding with $S(\tau) <: \text{T}$
    - Dependent product kind $\Sigma u::\kappa_1.\kappa_2$
    - Dependent function kind $\Pi u::\kappa_1.\kappa_2$
    - Higher singletons $S(c::\kappa)$ for constructors of any kind : [[Singleton-and-Dependent-Kinds|Link]]

21. **Subtyping** : [[Subtyping|Link]]
    - Subsumption principle for substituting subtypes
    - Variance covariant contravariant and invariant positions : [[Subtyping|Link]]
    - Product and sum subtyping by width and depth : [[Subtyping|Link]]
    - Function subtyping contravariant in the domain : [[Subtyping|Link]]
    - Recursive type subtyping via bounded assumptions
    - Bounded quantification over subtypes

22. **Objects and Inheritance** : [[Objects-and-Inheritance|Link]]
    - Dynamic dispatch on the class of an object : [[Dynamic-Classification|Link]]
    - Dispatch matrix recording method behavior per class
    - Class-based organization as tuples of methods : [[Objects-and-Inheritance|Link]]
    - Method-based organization as dispatch on sums : [[Objects-and-Inheritance|Link]]
    - Self-reference via abstract object type : [[Recursive-Types|Link]]
    - Inheritance as extension and overriding of a dispatch matrix : [[Objects-and-Inheritance|Link]]

23. **Control Stacks and Abstract Machines** : [[Control-Stacks-and-Abstract-Machines|Link]]
    - Explicit control stacks recording pending computations
    - Frames corresponding to search rules
    - Evaluation and return states : [[Plotkins-PCF-and-Partial-Computation|Link]]
    - Correctness relating machine to structural dynamics : [[Control-Stacks-and-Abstract-Machines|Link]]

24. **Exceptions** : [[Exceptions|Link]]
    - Failures and catch handlers
    - Exceptions carrying values of an exception type
    - Stack unwinding to the nearest handler
    - Extensible exception classification : [[Dynamic-Classification|Link]]
    - Encapsulation distinguishing fallible from infallible expressions : [[Exceptions|Link]]

25. **Continuations** : [[Continuations|Link]]
    - Reified control stacks as first-class values : [[Control-Stacks-and-Abstract-Machines|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]]
    - letcc to seize and throw to restore a continuation : [[Continuations|Link1]], [[Propositions-as-Types|Link2]]
    - Unlimited extent of continuations : [[Continuations|Link]]
    - Coroutines as symmetric mutually resuming routines : [[Continuations|Link]]
    - Cooperative multi-threading via a scheduler : [[Continuations|Link]]

26. **Propositions as Types** : [[Propositions-as-Types|Link]]
    - Constructive truth as existence of a proof
    - Proof terms for conjunction disjunction implication and falsehood
    - Gentzen's principle that elimination inverts introduction : [[Propositions-as-Types|Link]]
    - Correspondence between connectives and type constructors
    - Classical logic with proofs and refutations : [[Propositions-as-Types|Link]]
    - Law of excluded middle as backtracking computation : [[Propositions-as-Types|Link]]
    - Double-negation translation of classical into constructive logic : [[Propositions-as-Types|Link]]

27. **Symbols and Dynamic Binding** : [[Symbols-and-Dynamic-Binding|Link]]
    - Symbols as atomic names given meaning by operations : [[Symbols-and-Dynamic-Binding|Link]]
    - Symbol declaration with scoped versus scope-free dynamics : [[Symbols-and-Dynamic-Binding|Link]]
    - Symbolic references and decidable comparison : [[Symbols-and-Dynamic-Binding|Link]]
    - Fluid binding as a type-safe dynamic binding : [[Symbols-and-Dynamic-Binding|Link]]
    - Mobility of types independent of local symbols

28. **Dynamic Classification** : [[Dynamic-Classification|Link]]
    - Dynamically generated classes as run-time secrets : [[Data-Abstraction-and-Existential-Types|Link1]], [[Dynamic-Classification|Link2]]
    - Classified values sealed and matched by class
    - Definability of dynamic classes from existentials and references : [[Dynamic-Classification|Link]]
    - Confidentiality and integrity by controlling class access : [[Dynamic-Classification|Link]]

29. **State and Assignables** : [[State-and-Assignables|Link]]
    - Modernized Algol separating expressions from commands
    - Assignables declared with block structure and stack discipline
    - Get and set operations on assignables : [[State-and-Assignables|Link]]
    - Mobility restriction preserving stack allocation : [[State-and-Assignables|Link1]], [[Polymorphism-and-System-F|Link2]]
    - References as values naming assignables : [[State-and-Assignables|Link]]
    - Aliasing and interference : [[State-and-Assignables|Link]]
    - Free assignables with scope-free dynamics : [[Dynamic-Classification|Link1]], [[Symbols-and-Dynamic-Binding|Link2]], [[State-and-Assignables|Link3]]
    - Benign effects combining expressions and commands : [[Modularity-and-Linking|Link]]

30. **Laziness and Polarization** : [[Laziness-and-Polarization|Link]]
    - By-need evaluation with memoization and sharing
    - Naming deferred computations with symbols : [[Laziness-and-Polarization|Link]]
    - Black holes detecting circular dependencies
    - Suspension types $\tau\ \text{susp}$ with force
    - Positive types defined by values and negative types by observations : [[Laziness-and-Polarization|Link]]
    - Focusing separating values continuations and computations : [[Laziness-and-Polarization|Link]]

31. **Parallelism** : [[Parallelism|Link]]
    - Fork-join nested parallelism via parallel binding
    - Implicit parallelism theorem equating sequential and parallel dynamics : [[Parallelism|Link]]
    - Cost graphs with work and depth
    - Series-parallel combination of costs : [[Sum-Types|Link]]
    - Brent's theorem bounding time on $p$ processors
    - Data-parallel sequence operations
    - Futures for pipelined evaluation
    - Speculations for work-inefficient parallelism : [[Parallelism|Link]]

32. **Concurrency and Process Calculus** : [[Concurrency-and-Process-Calculus|Link]]
    - Processes awaiting events and structural congruence
    - Actions signals queries and silent steps
    - Synchronization of complementary actions
    - Replication as unbounded copies of a process : [[Concurrency-and-Process-Calculus|Link]]
    - Channel allocation with name binding and scope extrusion : [[Concurrency-and-Process-Calculus|Link]]
    - Synchronous and asynchronous communication
    - Channel passing and the $\pi$-calculus : [[Concurrency-and-Process-Calculus|Link]]
    - Universality by encoding the untyped $\lambda$-calculus : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]]

33. **Concurrent and Distributed Algol** : [[Concurrent-and-Distributed-Algol|Link]]
    - Broadcast communication of dynamically classified messages : [[Concurrent-and-Distributed-Algol|Link]]
    - Selective communication over events : [[Concurrent-and-Distributed-Algol|Link]]
    - Free assignables implemented as server processes : [[Concurrent-and-Distributed-Algol|Link]]
    - Distributed Algol with located resources and sites : [[Concurrent-and-Distributed-Algol|Link]]
    - Spatial type system indexing commands channels and events by site
    - Situated types factoring skeleton from site : [[Concurrent-and-Distributed-Algol|Link]]

34. **Modularity and Linking** : [[Modularity-and-Linking|Link]]
    - Linking as substitution discharging interface hypotheses
    - Interfaces as types mediating client and implementor : [[Modularity-and-Linking|Link]]
    - Initialization sequencing effects of components
    - Modules with static and dynamic parts : [[Modularity-and-Linking|Link1]], [[Statics-And-Dynamics|Link2]]
    - Signatures with kind and type components
    - Sealing to enforce abstraction : [[Modularity-and-Linking|Link]]
    - Type abstractions as opaque modules : [[Modularity-and-Linking|Link]]
    - Type classes as transparent constraints via singleton kinds
    - Module hierarchies as dependent pairs
    - Functors as parameterized modules : [[Modularity-and-Linking|Link]]
    - Generative versus applicative functor semantics : [[Modularity-and-Linking|Link]]

35. **Equational Reasoning** : [[Equational-Reasoning|Link]]
    - Kleene equality of complete programs
    - Observational equivalence via program contexts : [[Equational-Reasoning|Link]]
    - Logical equivalence defined by induction on types : [[Syntactic-Objects-and-Binding|Link1]], [[Equational-Reasoning|Link2]], [[Inductive-Definitions-and-Rule-Induction|Link3]]
    - Coincidence of logical and observational equivalence
    - Admissible relations closed under converse evaluation
    - Fixed point induction and compactness for PCF : [[Equational-Reasoning|Link]]
    - Co-natural numbers with coinductive equivalence : [[Equational-Reasoning|Link]]
    - Parametricity theorem for polymorphic types : [[Polymorphism-and-System-F|Link]]
    - Strong and weak bisimilarity of processes

---
