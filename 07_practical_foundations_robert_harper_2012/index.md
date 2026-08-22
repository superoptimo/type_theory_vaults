# Practical Foundations for Programming Languages — Index

[[book-guidelines|↩ Back to guidelines]]

1. **[[Syntactic-Objects-and-Binding|Syntactic Objects and Binding]]**
   - [[Syntactic-Objects-and-Binding|Abstract syntax trees classified by sorts and operators with arities]]
   - [[Syntactic-Objects-and-Binding|Variables as unknowns given meaning by substitution]]
   - [[Syntactic-Objects-and-Binding|Parameters as symbolic identifiers admitting disequality]]
   - [[Syntactic-Objects-and-Binding|Abstract binding trees with abstractors and valences]]
   - [[Syntactic-Objects-and-Binding|$\alpha$-equivalence and identification up to renaming]]
   - [[Syntactic-Objects-and-Binding|Capture-avoiding substitution and the freshness condition]]

2. **[[Inductive-Definitions-and-Rule-Induction|Inductive Definitions and Rule Induction]]**
   - [[Inductive-Definitions-and-Rule-Induction|Judgments and judgment forms over syntactic objects]]
   - [[Inductive-Definitions-and-Rule-Induction|Inference rules as sufficient conditions for judgments]]
   - [[Inductive-Definitions-and-Rule-Induction|Derivations as finite compositions of rules]]
   - [[Inductive-Definitions-and-Rule-Induction|Forward and backward chaining search strategies]]
   - [[Inductive-Definitions-and-Rule-Induction|Rule induction as reasoning over the strongest closed judgment]]
   - [[Inductive-Definitions-and-Rule-Induction|Iterated and simultaneous inductive definitions]]
   - [[Inductive-Definitions-and-Rule-Induction|Defining functions by their graph with existence and uniqueness]]
   - [[Inductive-Definitions-and-Rule-Induction|Mode specifications of inputs and outputs]]

3. **[[Hypothetical-and-General-Judgments|Hypothetical and General Judgments]]**
   - [[Hypothetical-and-General-Judgments|Derivability as entailment stable under rule extension]]
   - [[Hypothetical-and-General-Judgments|Admissibility as closure under already-derivable judgments]]
   - [[Hypothetical-and-General-Judgments|Hypothetical rules with global and local hypotheses]]
   - [[Hypothetical-and-General-Judgments|Generic judgments ranging over fresh variable renamings]]
   - [[Hypothetical-and-General-Judgments|Parametric judgments ranging over fresh symbol renamings]]
   - [[Hypothetical-and-General-Judgments|Structural properties of proliferation renaming and substitution]]

4. **[[Function-Types-and-the-Lambda-Calculus|Statics and Dynamics]]**
   - Phase distinction between static checking and dynamic execution
   - [[Statics-And-Dynamics|Type systems as inductive definitions of typing judgments]]
   - [[Statics-And-Dynamics|Transition systems with states initial and final]]
   - [[Statics-And-Dynamics|Structural dynamics with instruction and search rules]]
   - [[Statics-And-Dynamics|Contextual dynamics with evaluation contexts and holes]]
   - [[Statics-And-Dynamics|Equational dynamics as definitional equality]]
   - [[Statics-And-Dynamics|Evaluation dynamics relating expressions directly to values]]
   - [[Statics-And-Dynamics|Cost dynamics augmenting evaluation with step counts]]

5. **[[Type-Safety|Type Safety]]**
   - Preservation of typing under transition
   - [[Type-Safety|Progress of well-typed closed expressions]]
   - [[Type-Safety|Canonical forms characterizing values by type]]
   - Stuck states as ill-defined programs
   - [[Type-Safety|Checked versus unchecked run-time errors]]

6. **[[Function-Types-and-the-Lambda-Calculus|Function Types and the Lambda Calculus]]**
   - [[Function-Types-and-the-Lambda-Calculus|First-order function definitions by substitution]]
   - [[Function-Types-and-the-Lambda-Calculus|Higher-order functions as first-class values]]
   - [[Function-Types-and-the-Lambda-Calculus|$\lambda$-abstraction as introduction and application as elimination]]
   - [[Function-Types-and-the-Lambda-Calculus|Call-by-value versus call-by-name dynamics]]
   - [[Function-Types-and-the-Lambda-Calculus|Static binding versus dynamic binding]]
   - [[Function-Types-and-the-Lambda-Calculus|Evaluation dynamics and definitional equality for functions]]

7. **[[Godels-System-T-and-Total-Computation|Gödel's System T and Total Computation]]**
   - [[Product-Types|Primitive recursion with predecessor and recursive call]]
   - [[Polymorphism-and-System-F|Iteration as a restricted form of recursion]]
   - [[Plotkins-PCF-and-Partial-Computation|Definability of total functions including Ackermann's function]]
   - [[Statics-And-Dynamics|Intrinsic termination from the structure of recursion]]
   - [[Godels-System-T-and-Total-Computation|Undefinability of the universal function by diagonalization]]
   - [[Generic-Programming|Gödel-numbering of expressions as data]]

8. **[[Plotkins-PCF-and-Partial-Computation|Plotkin's PCF and Partial Computation]]**
   - [[Plotkins-PCF-and-Partial-Computation|General recursion as the least fixed point operator]]
   - [[Plotkins-PCF-and-Partial-Computation|Unwinding the recursion by self-substitution]]
   - [[Plotkins-PCF-and-Partial-Computation|Partial functions and definability via minimization]]
   - [[Plotkins-PCF-and-Partial-Computation|Church's Law identifying effective computability]]
   - [[Plotkins-PCF-and-Partial-Computation|Definability of the universal function as an interpreter]]

9. **[[Product-Types|Product Types]]**
   - [[Product-Types|Binary and finite products as ordered tuples]]
   - [[Product-Types|Nullary product as the unit type]]
   - [[Product-Types|Projections as elimination forms]]
   - [[Product-Types|Eager versus lazy dynamics for pairing]]
   - [[Product-Types|Encoding primitive recursion from iteration via pairs]]
   - [[Product-Types|Mutual recursion as recursion over a product]]

10. **[[Sum-Types|Sum Types]]**
    - [[Sum-Types|Binary and finite sums as tagged alternatives]]
    - [[Product-Types|Nullary sum as the void type with abort elimination]]
    - [[Sum-Types|Case analysis as the elimination form]]
    - [[Sum-Types|Booleans and enumerations encoded as sums]]
    - [[Sum-Types|Option types and the null pointer fallacy]]

11. **[[Pattern-Matching|Pattern Matching]]**
    - Pattern language with wildcards variables pairs and injections
    - Match and mismatch judgments with substitutions
    - [[Pattern-Matching|Typing of rules and rule sequences]]
    - Exhaustiveness enforced by match constraints
    - Redundancy elimination relative to preceding rules
    - [[Pattern-Matching|De Morgan dual for negating constraints]]

12. **[[Generic-Programming|Generic Programming]]**
    - [[Generic-Programming|Type operators marking spots for transformation]]
    - [[Generic-Programming|Polynomial type operators from sums and products]]
    - [[Generic-Programming|Positive type operators allowing restricted function types]]
    - [[Generic-Programming|Generic extension by mapping a function through a structure]]
    - [[Generic-Programming|Functorial action of type constructors]]

13. **[[Inductive-and-Coinductive-Types|Inductive and Coinductive Types]]**
    - [[Polymorphism-and-System-F|Inductive types as least solutions of type equations]]
    - [[Inductive-and-Coinductive-Types|Recursors or catamorphisms for inductive types]]
    - [[Polymorphism-and-System-F|Coinductive types as greatest solutions of type equations]]
    - [[Inductive-and-Coinductive-Types|Generators or anamorphisms for coinductive types]]
    - Streams characterized by head and tail observations
    - [[Dynamic-Typing-and-Hybrid-Typing|Positivity requirement on recursive type operators]]

14. **[[Recursive-Types|Recursive Types]]**
    - Solutions to type isomorphism equations $\mu t.\tau \cong [\mu t.\tau/t]\tau$
    - [[Inductive-and-Coinductive-Types|Fold and unfold as introduction and elimination]]
    - [[Recursive-Types|Recursive representations of lists and trees]]
    - [[Recursive-Types|Streams via lazy recursive types]]
    - Self-reference and general recursion derived from recursive types
    - [[Recursive-Types|Origin of state from feedback and self-reference]]

15. **[[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Dynamic Types and the Untyped Lambda Calculus]]**
    - [[Function-Types-and-the-Lambda-Calculus|Untyped $\lambda$-calculus as the uni-typed language]]
    - Church numerals and encodings of arithmetic
    - Y combinator and fixed points
    - [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Scott's theorem on undecidability of definitional equality]]
    - Embedding the untyped calculus into recursive type $D \cong D \to D$

16. **[[Dynamic-Typing-and-Hybrid-Typing|Dynamic Typing and Hybrid Typing]]**
    - [[Data-Abstraction-and-Existential-Types|Dynamically classified values with run-time class tags]]
    - Class checking judgments and run-time errors
    - [[Dynamic-Typing-and-Hybrid-Typing|Dynamic typing as a restricted static language]]
    - [[State-and-Assignables|Hybrid language with type dyn and cast operations]]
    - [[Dynamic-Typing-and-Hybrid-Typing|Optimization of dynamic code by hoisting checks]]

17. **[[Polymorphism-and-System-F|Polymorphism and System F]]**
    - [[Polymorphism-and-System-F|Type abstraction $\Lambda(t.e)$ and type application $e[\tau]$]]
    - [[Polymorphism-and-System-F|Universal type $\forall(t.\tau)$]]
    - [[Polymorphism-and-System-F|Impredicative instantiation by polymorphic types]]
    - [[Polymorphism-and-System-F|Church encodings of products sums and natural numbers]]
    - [[Polymorphism-and-System-F|Parametricity and free theorems]]
    - [[Polymorphism-and-System-F|Predicative prenex and rank-restricted fragments]]

18. **[[Data-Abstraction-and-Existential-Types|Data Abstraction and Existential Types]]**
    - Packages as implementations and clients as open expressions
    - [[Data-Abstraction-and-Existential-Types|Existential type $\exists(t.\tau)$ as an interface]]
    - [[Data-Abstraction-and-Existential-Types|Representation independence of clients]]
    - Bisimilarity of implementations via a relation
    - [[Data-Abstraction-and-Existential-Types|Definability of existentials from universals]]

19. **[[Constructors-and-Kinds|Constructors and Kinds]]**
    - [[Constructors-and-Kinds|Kinds as classifiers of static data]]
    - [[Constructors-and-Kinds|Neutral and canonical constructor forms]]
    - [[Constructors-and-Kinds|Kind T of types as classifiers of expressions]]
    - [[Constructors-and-Kinds|Canonizing hereditary substitution]]
    - Canonization of general-form constructors

20. **[[Singleton-and-Dependent-Kinds|Singleton and Dependent Kinds]]**
    - [[Statics-And-Dynamics|Singleton kind $S(\tau)$ pinning a type up to definitional equality]]
    - Subkinding with $S(\tau) <: \text{T}$
    - Dependent product kind $\Sigma u::\kappa_1.\kappa_2$
    - Dependent function kind $\Pi u::\kappa_1.\kappa_2$
    - [[Singleton-and-Dependent-Kinds|Higher singletons $S(c::\kappa)$ for constructors of any kind]]

21. **[[Subtyping|Subtyping]]**
    - Subsumption principle for substituting subtypes
    - [[Subtyping|Variance covariant contravariant and invariant positions]]
    - [[Subtyping|Product and sum subtyping by width and depth]]
    - [[Subtyping|Function subtyping contravariant in the domain]]
    - Recursive type subtyping via bounded assumptions
    - Bounded quantification over subtypes

22. **[[Objects-and-Inheritance|Objects and Inheritance]]**
    - [[Dynamic-Classification|Dynamic dispatch on the class of an object]]
    - Dispatch matrix recording method behavior per class
    - [[Objects-and-Inheritance|Class-based organization as tuples of methods]]
    - [[Objects-and-Inheritance|Method-based organization as dispatch on sums]]
    - [[Recursive-Types|Self-reference via abstract object type]]
    - [[Objects-and-Inheritance|Inheritance as extension and overriding of a dispatch matrix]]

23. **[[Control-Stacks-and-Abstract-Machines|Control Stacks and Abstract Machines]]**
    - Explicit control stacks recording pending computations
    - Frames corresponding to search rules
    - [[Plotkins-PCF-and-Partial-Computation|Evaluation and return states]]
    - [[Control-Stacks-and-Abstract-Machines|Correctness relating machine to structural dynamics]]

24. **[[Exceptions|Exceptions]]**
    - Failures and catch handlers
    - Exceptions carrying values of an exception type
    - Stack unwinding to the nearest handler
    - [[Dynamic-Classification|Extensible exception classification]]
    - [[Exceptions|Encapsulation distinguishing fallible from infallible expressions]]

25. **[[Continuations|Continuations]]**
    - [[Control-Stacks-and-Abstract-Machines|Reified control stacks as first-class values]]
    - [[Continuations|letcc to seize and throw to restore a continuation]]
    - [[Continuations|Unlimited extent of continuations]]
    - [[Continuations|Coroutines as symmetric mutually resuming routines]]
    - [[Continuations|Cooperative multi-threading via a scheduler]]

26. **[[Propositions-as-Types|Propositions as Types]]**
    - Constructive truth as existence of a proof
    - Proof terms for conjunction disjunction implication and falsehood
    - [[Propositions-as-Types|Gentzen's principle that elimination inverts introduction]]
    - Correspondence between connectives and type constructors
    - [[Propositions-as-Types|Classical logic with proofs and refutations]]
    - [[Propositions-as-Types|Law of excluded middle as backtracking computation]]
    - [[Propositions-as-Types|Double-negation translation of classical into constructive logic]]

27. **[[Symbols-and-Dynamic-Binding|Symbols and Dynamic Binding]]**
    - [[Symbols-and-Dynamic-Binding|Symbols as atomic names given meaning by operations]]
    - [[Symbols-and-Dynamic-Binding|Symbol declaration with scoped versus scope-free dynamics]]
    - [[Symbols-and-Dynamic-Binding|Symbolic references and decidable comparison]]
    - [[Symbols-and-Dynamic-Binding|Fluid binding as a type-safe dynamic binding]]
    - Mobility of types independent of local symbols

28. **[[Dynamic-Classification|Dynamic Classification]]**
    - [[Data-Abstraction-and-Existential-Types|Dynamically generated classes as run-time secrets]]
    - Classified values sealed and matched by class
    - [[Dynamic-Classification|Definability of dynamic classes from existentials and references]]
    - [[Dynamic-Classification|Confidentiality and integrity by controlling class access]]

29. **[[State-and-Assignables|State and Assignables]]**
    - Modernized Algol separating expressions from commands
    - Assignables declared with block structure and stack discipline
    - [[State-and-Assignables|Get and set operations on assignables]]
    - [[State-and-Assignables|Mobility restriction preserving stack allocation]]
    - [[State-and-Assignables|References as values naming assignables]]
    - [[State-and-Assignables|Aliasing and interference]]
    - [[Dynamic-Classification|Free assignables with scope-free dynamics]]
    - [[Modularity-and-Linking|Benign effects combining expressions and commands]]

30. **[[Laziness-and-Polarization|Laziness and Polarization]]**
    - By-need evaluation with memoization and sharing
    - [[Laziness-and-Polarization|Naming deferred computations with symbols]]
    - Black holes detecting circular dependencies
    - Suspension types $\tau\ \text{susp}$ with force
    - [[Laziness-and-Polarization|Positive types defined by values and negative types by observations]]
    - [[Laziness-and-Polarization|Focusing separating values continuations and computations]]

31. **[[Parallelism|Parallelism]]**
    - Fork-join nested parallelism via parallel binding
    - [[Parallelism|Implicit parallelism theorem equating sequential and parallel dynamics]]
    - Cost graphs with work and depth
    - [[Sum-Types|Series-parallel combination of costs]]
    - Brent's theorem bounding time on $p$ processors
    - Data-parallel sequence operations
    - Futures for pipelined evaluation
    - [[Parallelism|Speculations for work-inefficient parallelism]]

32. **[[Concurrency-and-Process-Calculus|Concurrency and Process Calculus]]**
    - Processes awaiting events and structural congruence
    - Actions signals queries and silent steps
    - Synchronization of complementary actions
    - [[Concurrency-and-Process-Calculus|Replication as unbounded copies of a process]]
    - [[Concurrency-and-Process-Calculus|Channel allocation with name binding and scope extrusion]]
    - Synchronous and asynchronous communication
    - [[Concurrency-and-Process-Calculus|Channel passing and the $\pi$-calculus]]
    - [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Universality by encoding the untyped $\lambda$-calculus]]

33. **[[Concurrent-and-Distributed-Algol|Concurrent and Distributed Algol]]**
    - [[Concurrent-and-Distributed-Algol|Broadcast communication of dynamically classified messages]]
    - [[Concurrent-and-Distributed-Algol|Selective communication over events]]
    - [[Concurrent-and-Distributed-Algol|Free assignables implemented as server processes]]
    - [[Concurrent-and-Distributed-Algol|Distributed Algol with located resources and sites]]
    - Spatial type system indexing commands channels and events by site
    - [[Concurrent-and-Distributed-Algol|Situated types factoring skeleton from site]]

34. **[[Modularity-and-Linking|Modularity and Linking]]**
    - Linking as substitution discharging interface hypotheses
    - [[Modularity-and-Linking|Interfaces as types mediating client and implementor]]
    - Initialization sequencing effects of components
    - [[Modularity-and-Linking|Modules with static and dynamic parts]]
    - Signatures with kind and type components
    - [[Modularity-and-Linking|Sealing to enforce abstraction]]
    - [[Modularity-and-Linking|Type abstractions as opaque modules]]
    - Type classes as transparent constraints via singleton kinds
    - Module hierarchies as dependent pairs
    - [[Modularity-and-Linking|Functors as parameterized modules]]
    - [[Modularity-and-Linking|Generative versus applicative functor semantics]]

35. **[[Equational-Reasoning|Equational Reasoning]]**
    - Kleene equality of complete programs
    - [[Equational-Reasoning|Observational equivalence via program contexts]]
    - [[Syntactic-Objects-and-Binding|Logical equivalence defined by induction on types]]
    - Coincidence of logical and observational equivalence
    - Admissible relations closed under converse evaluation
    - [[Equational-Reasoning|Fixed point induction and compactness for PCF]]
    - [[Equational-Reasoning|Co-natural numbers with coinductive equivalence]]
    - [[Polymorphism-and-System-F|Parametricity theorem for polymorphic types]]
    - Strong and weak bisimilarity of processes

---
