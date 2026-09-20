# Practical Foundations for Programming Languages — Guidelines

## Header

**Title:** Practical Foundations for Programming Languages
**Author(s):** Robert Harper (Carnegie Mellon University)
**Publication:** Version 1.32, revised 05.15.2012 (electronic edition, Creative Commons Attribution-Noncommercial-No Derivative Works 3.0 US)

**Brief Summary:**
The book develops the theory of programming languages in the unifying framework of type theory. Every language feature is defined by its *statics* (typing rules governing well-formed use) and its *dynamics* (execution rules), and the coherence of the two is expressed by *type safety*. Topics range from the syntactic foundations (abstract syntax and binding, inductive definitions) through functions, data types, polymorphism, subtyping, objects, control, state, laziness, parallelism, concurrency, modularity, and equational reasoning. The central thesis is that types are the central organizing principle of language design: language features are manifestations of type structure.

**Intent of the Author:**
Harper wants to give a precise yet intuitive, uniform methodology for specifying, analyzing, and implementing programming language features. The reader should come away able to define a language by its statics and dynamics, prove its safety, and reason equationally about its programs — with methods that scale across the full spectrum of language concepts and support mechanized reasoning.

---

## Topic List

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

## Chapter Summaries

### Chapter 1: Syntactic Objects (pp. 3–13)

**Summary:** Introduces the formal objects that programs are built from: abstract syntax trees (ASTs) and abstract binding trees (ABTs). ASTs capture hierarchical structure via operators and sorts; ABTs enrich them with binding and scope. : [[Syntactic-Objects-and-Binding|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Abstract Syntax Trees** — *abstract syntax tree* (ordered tree whose leaves are variables and interior nodes are operators), *sort* (syntactic category), *operator arity* (finite sequence of argument sorts), *variable* (unknown object given meaning by substitution), *structural induction* (proof principle over tree formation), *parameter* (symbolic name indexing a family of operators, admitting disequality, not substitutable). : [[Syntactic-Objects-and-Binding|Link]]
- **1.2 Abstract Binding Trees** — *abstractor* ($x_1,\ldots,x_k.a$, binds variables in body), *valence* ($(\vec{s}_1)s$, specifies bound variable sorts and argument sort), *scope* (range of significance of a binding), *freshness condition* (bound variables chosen fresh to avoid collision), *$\alpha$-equivalence* ($a =_\alpha b$, identity up to bound-variable renaming), *capture avoidance* (substitution must not bind free variables of the substituting term), *identification convention* (ABTs always taken up to $\alpha$-equivalence). : [[Syntactic-Objects-and-Binding|Link]]

**Key Questions:**
1. Why are variables given meaning by substitution whereas parameters are not?
2. Why must substitution be defined on $\alpha$-equivalence classes rather than raw ABTs to be total?
3. What is the difference between a variable and a parameter, and why does disequality behave differently for them?

---

### Chapter 2: Inductive Definitions (pp. 15–25)

**Summary:** Develops the framework of inductive definitions: rules deriving judgments, derivations as evidence, and rule induction as the proof principle. This is the foundational tool used throughout for defining statics and dynamics. : [[Hypothetical-and-General-Judgments|Link1]], [[Inductive-Definitions-and-Rule-Induction|Link2]], [[Statics-And-Dynamics|Link3]]

**Key Definitions & Concepts by Section:**
- **2.1 Judgments** — *judgment* (assertion about syntactic objects), *judgment form* or *predicate* (the property or relation asserted), *subject* (object the judgment is about). : [[Statics-And-Dynamics|Link]]
- **2.2 Inference Rules** — *rule* (premises above a line, conclusion below), *axiom* (rule with no premises), *rule scheme* (finite pattern for an infinite family of rules), *strongest judgment closed under the rules* (rules are both sufficient and necessary). : [[Inductive-Definitions-and-Rule-Induction|Link]]
- **2.3 Derivations** — *derivation* (finite composition of rules ending in a judgment; evidence for it), *forward chaining* (bottom-up search from axioms), *backward chaining* (top-down goal-directed search). : [[Dynamic-Typing-and-Hybrid-Typing|Link]]
- **2.4 Rule Induction** — *rule induction* (to prove a property of all derivable judgments, show it is closed under each rule), *inductive hypotheses* (property assumed for premises), *mathematical induction* and *tree induction* as special cases. : [[Inductive-Definitions-and-Rule-Induction|Link]]
- **2.5 Iterated and Simultaneous Inductive Definitions** — *iterated definition* (builds on a previously defined judgment), *simultaneous definition* (several judgments defined at once by one rule set). : [[Inductive-Definitions-and-Rule-Induction|Link]]
- **2.6 Defining Functions by Rules** — *graph of a function* (relation between inputs and outputs), proof obligation of *existence* and *uniqueness* of outputs. : [[Inductive-Definitions-and-Rule-Induction|Link]]
- **2.7 Modes** — *mode specification* (which arguments are inputs $\forall$ and which outputs $\exists$ or $\exists!$ or $\exists_{\le 1}$), *principal mode*.

**Key Questions:**
1. Why is an inductively defined judgment the *strongest* judgment closed under its rules, and what does that justify?
2. How does rule induction differ from structural induction?
3. What must be proved to legitimately treat a relation defined by rules as a function?

---

### Chapter 3: Hypothetical and General Judgments (pp. 27–36)

**Summary:** Extends inductive definitions to hypothetical judgments (entailment from assumptions) and general judgments (generality over variables and parameters). Distinguishes derivability from admissibility, a distinction central to metatheory. : [[Hypothetical-and-General-Judgments|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Hypothetical Judgments** — *derivability* ($\Gamma \vdash_R J$, conclusion derivable treating hypotheses as temporary axioms; stable under rule extension), *admissibility* ($\Gamma \models_R J$, whenever hypotheses are derivable so is the conclusion; not stable under extension), *structural properties* (reflexivity, weakening, transitivity). : [[Hypothetical-and-General-Judgments|Link1]], [[Propositions-as-Types|Link2]]
- **3.2 Hypothetical Inductive Definitions** — *hypothetical rule* (rule with global hypotheses $\Gamma$ and local hypotheses $\Gamma_i$ per premise), *uniform rule* (stated for all contexts), *formal derivability judgment* ($\Gamma \vdash J$ as an inductively defined judgment). : [[Hypothetical-and-General-Judgments|Link1]], [[Inductive-Definitions-and-Rule-Induction|Link2]], [[Statics-And-Dynamics|Link3]]
- **3.3 General Judgments** — *generic judgment* (holds for all fresh substitution instances of variables), *parametric judgment* (holds for all fresh renamings of symbols), *proliferation*, *renaming*, and *substitution* structural principles. : [[Hypothetical-and-General-Judgments|Link]]
- **3.4 Generic Inductive Definitions** — *generic rule* (with global and local type variables), *formal generic judgment* ($\vec{x} \mid \Gamma \vdash J$, identified up to renaming). : [[Inductive-Definitions-and-Rule-Induction|Link1]], [[Hypothetical-and-General-Judgments|Link2]], [[Statics-And-Dynamics|Link3]]

**Key Questions:**
1. What is the essential difference between derivability and admissibility, and which is stable under adding rules?
2. Why can one not substitute for a parameter the way one substitutes for a variable?
3. What are local hypotheses in a hypothetical rule, and how do they differ from global ones?

---

### Chapter 4: Statics (pp. 39–44)

**Summary:** Introduces the static phase of a language through the example language $\mathcal{L}\{\text{nat str}\}$, defining its syntax and type system, and establishing the structural properties (weakening, substitution, decomposition) that support modularity. : [[Symbols-and-Dynamic-Binding|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Syntax** — *syntax chart* (notation defining sorts, operators, and arities together with concrete syntax), *abstract syntax* as the official presentation. : [[Exceptions|Link1]], [[Plotkins-PCF-and-Partial-Computation|Link2]]
- **4.2 Type System** — *typing context* $\Gamma$ (finite map from variables to types), *typing judgment* ($\Gamma \vdash e : \tau$), *unicity of typing* (each expression has at most one type), *inversion for typing* (necessary conditions reversing each typing rule), *syntax-directed rules* (one rule per expression form). : [[Statics-And-Dynamics|Link1]], [[Type-Safety|Link2]]
- **4.3 Structural Properties** — *weakening* (adding unused assumptions preserves typing), *substitution lemma* ($\Gamma, x:\tau \vdash e':\tau'$ and $\Gamma \vdash e:\tau$ imply $\Gamma \vdash [e/x]e' : \tau'$), *decomposition* (converse of substitution, isolating a subexpression as a module), *introductory forms* (construct values/canonical forms), *eliminatory forms* (manipulate values). : [[Hypothetical-and-General-Judgments|Link1]], [[Statics-And-Dynamics|Link2]]

**Key Questions:**
1. What does the substitution lemma express about linking a client with an implementation?
2. Why is the classification into introduction and elimination forms important for language design?
3. What can go wrong in a type system that lacks weakening?

---

### Chapter 5: Dynamics (pp. 45–54)

**Summary:** Defines the dynamic phase — how programs execute — in three equivalent styles: structural dynamics (step-by-step transitions), contextual dynamics (evaluation contexts), and equational dynamics (definitional equality). : [[Exceptions|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Transition Systems** — *state*, *initial* and *final state*, *transition* ($s \mapsto s'$), *stuck state* (not final, no transition), *transition sequence*, *complete sequence* (maximal and final), $s \Downarrow$ (existence of a complete sequence), *iterated transition* ($s \mapsto^\ast s'$), *determinacy*. : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link1]], [[Statics-And-Dynamics|Link2]]
- **5.2 Structural Dynamics** — *value judgment* ($e\ \text{val}$), *instruction transition* (primitive computation step), *search transition* (determines evaluation order), *by-value* vs *by-name* interpretation of definitions. : [[Control-Stacks-and-Abstract-Machines|Link1]], [[Generic-Programming|Link2]], [[Statics-And-Dynamics|Link3]]
- **5.3 Contextual Dynamics** — *instruction transition* ($e_1 \to e_2$), *evaluation context* ($E\ \text{ectxt}$, template with a hole $\circ$ locating the next instruction), *filling the hole* ($e' = E\{e\}$), equivalence theorem between structural and contextual dynamics. : [[Statics-And-Dynamics|Link]]
- **5.4 Equational Dynamics** — *definitional equality* ($\Gamma \vdash e \equiv e' : \tau$), *congruence relation*, *symbolic evaluation*, *semantic equivalence* (fills the gap for laws like commutativity via induction). : [[Statics-And-Dynamics|Link]]

**Key Questions:**
1. What is the difference between an instruction transition and a search transition?
2. How does an evaluation context encode the order of evaluation?
3. Why is definitional equality too weak to prove $x_1 + x_2 \equiv x_2 + x_1$ with free variables?

---

### Chapter 6: Type Safety (pp. 55–60)

**Summary:** States and proves the safety theorem for $\mathcal{L}\{\text{nat str}\}$: well-typed programs do not get stuck. Safety decomposes into preservation (steps preserve types) and progress (well-typed states are values or can step). : [[Type-Safety|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Preservation** — *preservation theorem* (if $e:\tau$ and $e \mapsto e'$ then $e':\tau$), proved by induction on the transition derivation. : [[Dynamic-Typing-and-Hybrid-Typing|Link]]
- **6.2 Progress** — *canonical forms lemma* (characterizes values of each type), *progress theorem* (if $e:\tau$ then $e\ \text{val}$ or $e \mapsto e'$ for some $e'$), *safety* = preservation + progress.
- **6.3 Run-Time Errors** — *unchecked error* (ruled out statically, no run-time check needed), *checked error* (detected at run time, e.g. division by zero), *error judgment* ($e\ \text{err}$), *progress with error* (a well-typed expression errs, is a value, or steps). : [[Data-Abstraction-and-Existential-Types|Link1]], [[Symbols-and-Dynamic-Binding|Link2]]

**Key Questions:**
1. Why is preservation proved by induction on the dynamics while progress is proved by induction on the statics?
2. What role does the canonical forms lemma play in the proof of progress?
3. Why is division by zero treated as a checked rather than unchecked error?

---

### Chapter 7: Evaluation Dynamics (pp. 61–66)

**Summary:** Presents evaluation dynamics, an inductive relation $e \Downarrow v$ directly linking expressions to values, suppressing intermediate steps. Relates it to structural dynamics, revisits safety in this setting, and introduces cost dynamics. : [[Control-Stacks-and-Abstract-Machines|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]], [[Statics-And-Dynamics|Link3]]

**Key Definitions & Concepts by Section:**
- **7.1 Evaluation Dynamics** — *evaluation judgment* ($e \Downarrow v$), *by-name* vs *by-value* rule for let, non-syntax-directed rules. : [[Control-Stacks-and-Abstract-Machines|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]], [[Statics-And-Dynamics|Link3]]
- **7.2 Relating Structural and Evaluation Dynamics** — equivalence theorem $e \mapsto^\ast v$ iff $e \Downarrow v$, *converse evaluation* or *head expansion* lemma. : [[Generic-Programming|Link1]], [[Statics-And-Dynamics|Link2]]
- **7.3 Type Safety, Revisited** — *going wrong judgment* ($e \uparrow$), the methodological weakness that one must define errors explicitly just to prove they cannot arise. : [[Symbols-and-Dynamic-Binding|Link]]
- **7.4 Cost Dynamics** — *cost judgment* ($e \Downarrow^k v$, evaluation in $k$ steps), correspondence $e \Downarrow^k v$ iff $e \mapsto^k v$. : [[Parallelism|Link1]], [[Statics-And-Dynamics|Link2]]

**Key Questions:**
1. Why is evaluation dynamics ill-suited to expressing progress?
2. What is the advantage and disadvantage of evaluation dynamics relative to structural dynamics?
3. How does cost dynamics recover a notion of time complexity absent from plain evaluation dynamics?

---

### Chapter 8: Function Definitions and Values (pp. 69–76)

**Summary:** Moves from computing with numbers to abstracting computation itself. Introduces first-order function definitions, then consolidates them into higher-order functions via $\lambda$-abstraction and function types, and critiques dynamic scope. : [[Function-Types-and-the-Lambda-Calculus|Link1]], [[Inductive-Definitions-and-Rule-Induction|Link2]]

**Key Definitions & Concepts by Section:**
- **8.1 First-Order Functions** — *function header* ($f(\tau_1):\tau_2$), *function substitution* ($x.e/fe'$), domain and range restricted to base types. : [[Function-Types-and-the-Lambda-Calculus|Link]]
- **8.2 Higher-Order Functions** — *$\lambda$-abstraction* ($\text{lam}[\tau](x.e)$), *application* ($\text{ap}(e_1;e_2)$), *function type* ($\text{arr}(\tau_1;\tau_2)$ or $\tau_1 \to \tau_2$), *first-class functions*, preservation and progress theorems. : [[Function-Types-and-the-Lambda-Calculus|Link]]
- **8.3 Evaluation Dynamics and Definitional Equality** — evaluation rule for application, *$\beta$-reduction* ($\text{ap}(\text{lam};e_1) \equiv [e_1/x]e_2$), call-by-value definitional equality with values including variables. : [[Function-Types-and-the-Lambda-Calculus|Link]]
- **8.4 Dynamic Scope** — *static binding* (substitution avoiding capture), *dynamic binding* (replacement incurring capture), failure of type safety and modularity under dynamic scope. : [[Dynamic-Classification|Link1]], [[Symbols-and-Dynamic-Binding|Link2]]

**Key Questions:**
1. How does a function type consolidate function definitions and expression definitions?
2. Why does dynamic binding make the names of bound variables significant?
3. What is the difference between call-by-value and call-by-name application dynamics?

---

### Chapter 9: Gödel's T (pp. 77–84)

**Summary:** Introduces $\mathcal{L}\{\text{nat}\to\}$ (Gödel's System T), combining natural numbers with higher-order functions and *primitive recursion*. Every program is intrinsically terminating, which yields definability results and an undefinability result by diagonalization. : [[Modularity-and-Linking|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Statics** — *numerals* ($\bar{n}$), *primitive recursion* ($\text{rec}(e;e_0;x.y.e_1)$), *iteration* as a special case, typing rules. : [[Symbols-and-Dynamic-Binding|Link]]
- **9.2 Dynamics** — value and transition rules, recursion on $\text{z}$ and $\text{s}(e)$, safety theorem. : [[Exceptions|Link]]
- **9.3 Definability** — *definable function* ($e_f(\bar{n}) \equiv \overline{f(n)}$), doubling example, *Ackermann's function* as higher-order primitive recursion using the iterator $\text{it}$. : [[Exceptions|Link]]
- **9.4 Undefinability** — *termination theorem* (every well-typed expression is definitionally equal to a value), *Gödel-numbering*, *universal function* $f_{\text{univ}}$, *diagonal function*, diagonalization proof that the universal function is not definable, tradeoff between termination and universality.

**Key Questions:**
1. Why is Ackermann's function definable in System T even though it is not first-order primitive recursive?
2. How does the diagonal argument show that System T cannot be universal?
3. What is the tradeoff between demanding termination and expressive power?

---

### Chapter 10: Plotkin's PCF (pp. 85–92)

**Summary:** Introduces $\mathcal{L}\{\text{nat}\rightharpoonup\}$ (Plotkin's PCF), which adds *general recursion* (fixed points) to functions and naturals. Programs may diverge; definable functions are partial, and the termination proof moves into the programmer's head. : [[Plotkins-PCF-and-Partial-Computation|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 Statics** — *partial function type* ($\text{parr}(\tau_1;\tau_2)$), *zero test* ($\text{ifz}$), *general recursion* ($\text{fix}[\tau](x.e)$), self-referential typing rule. : [[Symbols-and-Dynamic-Binding|Link]]
- **10.2 Dynamics** — *unwinding the recursion* ($\text{fix}[\tau](x.e) \mapsto [\text{fix}[\tau](x.e)/x]e$), safety theorem, definitional equality. : [[Exceptions|Link]]
- **10.3 Definability** — *recursive functions*, *partial recursive functions* (primitive recursive + minimization), *Church's Law* (partial recursive = effectively computable), *universal function* $\varphi_{\text{univ}}$ as an interpreter, why diagonalization yields divergence rather than contradiction here. : [[Exceptions|Link]]

**Key Questions:**
1. How does the fixed-point operator solve recursion equations, and why may the solution be partial?
2. What does Church's Law assert and why is it called a scientific law?
3. Why does the diagonal construction in PCF produce a non-terminating program instead of a contradiction?

---

### Chapter 11: Product Types (pp. 95–100)

**Summary:** Introduces product types: binary products (pairs), the nullary product (unit), and finite products (tuples/records). Products admit both eager and lazy dynamics and support primitive and mutual recursion. : [[Product-Types|Link]]

**Key Definitions & Concepts by Section:**
- **11.1 Nullary and Binary Products** — *unit type* (nullary product with single element $\langle\rangle$), *pair* ($\langle e_1, e_2\rangle$), *projections* ($e \cdot l$, $e \cdot r$), eager vs lazy value rules, safety theorem. : [[Sum-Types|Link]]
- **11.2 Finite Products** — *finite product* ($\prod_{i\in I}\tau_i$), *tuple* ($\langle e_i\rangle_{i\in I}$), *projection* ($e \cdot i$), labeled tuples or records. : [[Product-Types|Link]]
- **11.3 Primitive and Mutual Recursion** — defining primitive recursion from iteration via pairs, *mutual recursion* as recursion over a product of functions. : [[Concurrency-and-Process-Calculus|Link1]], [[Product-Types|Link2]]

**Key Questions:**
1. How does the eager versus lazy choice affect when the components of a pair are evaluated?
2. How can product types encode mutual recursion?
3. Why is there no elimination form for the unit type?

---

### Chapter 12: Sum Types (pp. 101–108)

**Summary:** Introduces sum types: binary sums (tagged alternatives), the nullary sum (void), and finite sums. Sums model heterogeneous data and underlie booleans, enumerations, and option types. : [[Sum-Types|Link]]

**Key Definitions & Concepts by Section:**
- **12.1 Nullary and Binary Sums** — *void type* (nullary sum, no introduction), *abort* (elimination from void), *injections* ($l \cdot e$, $r \cdot e$), *case analysis*, safety theorem. : [[Sum-Types|Link]]
- **12.2 Finite Sums** — *finite sum* ($\sum_{i\in I}\tau_i$), *injection* ($i \cdot e$), *I-way case analysis*. : [[Sum-Types|Link]]
- **12.3 Applications of Sum Types** — *void vs unit* (unit has one element, void has none), *booleans* as $\text{unit}+\text{unit}$, *enumerations* as sums of units, *option type* ($\tau\ \text{opt} = \text{unit} + \tau$), *null pointer fallacy* (confusing $\tau$ with $\tau\ \text{opt}$). : [[Polymorphism-and-System-F|Link1]], [[Propositions-as-Types|Link2]], [[Subtyping|Link3]], [[Sum-Types|Link4]]

**Key Questions:**
1. Why must both branches of a case analysis have the same type?
2. What is the difference between the void and unit types, and why is the "void" of many languages actually unit?
3. How do option types avoid the null pointer fallacy?

---

### Chapter 13: Pattern Matching (pp. 109–119)

**Summary:** Generalizes the elimination forms of products and sums into a pattern-matching language over eager data. Develops the statics of patterns, the dynamics of matching, and enforcement of exhaustiveness and irredundancy via match constraints. : [[Pattern-Matching|Link]]

**Key Definitions & Concepts by Section:**
- **13.1 A Pattern Language** — *match expression* ($\text{match}\ e\{rs\}$), *rules*, *patterns* (wildcard, variable, unit, pair, injections). : [[Pattern-Matching|Link]]
- **13.2 Statics** — *pattern typing* ($\Lambda \models p : \tau$, binding variables at most once), *rule typing*, *rule sequence typing*. : [[Symbols-and-Dynamic-Binding|Link]]
- **13.3 Dynamics** — *substitution* ($\theta$), *match judgment* ($\theta \models p / e$), *mismatch judgment* ($e \perp p$), safety theorem. : [[Exceptions|Link]]
- **13.4 Exhaustiveness and Redundancy** — *match constraints* ($\xi$), *De Morgan dual* ($\bar{\xi}$), *satisfaction* ($e \models \xi$), *entailment* ($\xi_1 \models \xi_2$), *exhaustiveness* (every value satisfies some rule's constraint), *redundancy* (a rule subsumed by preceding rules), *inconsistency* ($\Xi\ \text{incon}$) deciding validity.

**Key Questions:**
1. How do match constraints express the set of values matched by a pattern?
2. Why must pattern variables occur at most once in a pattern?
3. How is exhaustiveness checking reduced to deciding inconsistency of a constraint set?

---

### Chapter 14: Generic Programming (pp. 121–125)

**Summary:** Introduces generic programming: extending a function $f : \rho \to \rho'$ to act on data of type $[\rho/t]\tau$ guided by a type operator $t.\tau$ that marks where the transformation applies. : [[Generic-Programming|Link]]

**Key Definitions & Concepts by Section:**
- **14.1 Introduction** — motivation for type-generic extension, ambiguity of where to apply a transformation. : [[Dynamic-Typing-and-Hybrid-Typing|Link1]], [[Continuations|Link2]], [[Constructors-and-Kinds|Link3]]
- **14.2 Type Operators** — *type operator* ($t.\tau$, a type with a designated variable marking transformation spots), *instance* ($[\rho/t]\tau$), *polynomial type operators* (built from $t$, void, unit, product, sum). : [[Generic-Programming|Link]]
- **14.3 Generic Extension** — *generic extension* ($\text{map}[t.\tau](x.e'; e)$), dynamics by structural recursion on the operator, *positive type operators* (admitting function types with $t$ only in positive positions), *negative occurrences*, *type isomorphism* for full functoriality. : [[Generic-Programming|Link]]

**Key Questions:**
1. Why is a type operator needed to make generic extension unambiguous?
2. Why must $t$ occur only positively in a positive type operator?
3. How does generic extension relate to the categorical notion of a functor?

---

### Chapter 15: Inductive and Co-Inductive Types (pp. 129–135)

**Summary:** Presents inductive types (least/initial solutions, defined by values, eliminated by recursion) and coinductive types (greatest/final solutions, defined by observations, introduced by generation), both built from positive type operators. : [[Inductive-and-Coinductive-Types|Link]]

**Key Definitions & Concepts by Section:**
- **15.1 Motivating Examples** — natural numbers consolidated into one introduction ($\text{fold}_{\text{nat}}$) and one elimination (recursor), streams with $\text{hd}$ and $\text{tl}$ observations and a generator. : [[Data-Abstraction-and-Existential-Types|Link]]
- **15.2 Statics** — *self-reference type variable* ($t$), *inductive type* ($\text{ind}(t.\tau)$ or $\mu_i(t.\tau)$), *coinductive type* ($\text{coi}(t.\tau)$ or $\mu_f(t.\tau)$), positivity requirement, expressions: $\text{fold}$, $\text{rec}$, $\text{unfold}$, $\text{gen}$. : [[Symbols-and-Dynamic-Binding|Link]]
- **15.3 Dynamics** — recursor dynamics via generic extension, generator dynamics as the dual, preservation and progress lemmas. : [[Exceptions|Link]]

**Key Questions:**
1. How do inductive and coinductive types differ in what defines their elements?
2. What role does the generic extension (map) play in the dynamics of recursion and generation?
3. Why is positivity required of the type operator in a recursive type?

---

### Chapter 16: Recursive Types (pp. 137–145)

**Summary:** Introduces general recursive types $\mu t.\tau$ solving type isomorphism equations $\mu t.\tau \cong [\mu t.\tau/t]\tau$ via fold/unfold. Uses them to represent data structures, derive general recursion, and explain the origin of state. : [[Recursive-Types|Link]]

**Key Definitions & Concepts by Section:**
- **16.1 Solving Type Isomorphisms** — *recursive type* ($\text{rec}(t.\tau)$), *fold* (introduction) and *unfold* (elimination) as mutually inverse operations, type formation rules, safety theorem.
- **16.2 Recursive Data Structures** — naturals as $\mu t.[z \hookrightarrow \text{unit}, s \hookrightarrow t]$, lists, streams via $\mu t.\text{nat} \times t$ (lazy) or $\mu t.\text{unit} \to (\text{nat} \times t)$ (eager). : [[Laziness-and-Polarization|Link1]], [[Recursive-Types|Link2]]
- **16.3 Self-Reference** — *self-referential type* ($\text{self}(\tau) \cong \text{self}(\tau) \to \tau$), derivation of $\text{fix}$ from recursive types, non-conservativity of recursive types. : [[Laziness-and-Polarization|Link1]], [[Objects-and-Inheritance|Link2]], [[Recursive-Types|Link3]]
- **16.4 The Origin of State** — state from feedback/self-reference, RS latch modeled as $\mu t.\langle X \hookrightarrow \text{bool}, Q \hookrightarrow \text{bool}, N \hookrightarrow t\rangle$. : [[Recursive-Types|Link]]

**Key Questions:**
1. Why are types not sets, given that $\mu t.t \to t$ is impossible set-theoretically?
2. How does one derive general recursion from recursive types?
3. How does self-reference give rise to state, as in a latch?

---

### Chapter 17: The Untyped $\lambda$-Calculus (pp. 149–157)

**Summary:** Shows the untyped $\lambda$-calculus is not untyped but *uni-typed*: a single recursive type $D \cong D \to D$. Develops its definitional equality, its surprising expressiveness (Church numerals, Y combinator), and Scott's undecidability theorem. : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link]]

**Key Definitions & Concepts by Section:**
- **17.1 The $\lambda$-Calculus** — syntax (variable, $\lambda(x.u)$, application), well-formedness judgment ($u\ \text{ok}$), definitional equality. : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]]
- **17.2 Definability** — *Church numerals*, encodings of successor, addition, multiplication, predecessor via pairs ("shift registers"), *Y combinator* and its derivation via self-application. : [[Exceptions|Link]]
- **17.3 Scott's Theorem** — *inseparability* of non-trivial behavioral properties, undecidability of definitional equality. : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link]]
- **17.4 Untyped Means Uni-Typed** — recursive type $D \cong D \to D$, faithful embedding of the untyped calculus into a typed language with recursive types, rolling and unrolling. : [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link]]

**Key Questions:**
1. Why is "untyped" more accurately described as "uni-typed"?
2. How does the Y combinator work, and how can it be derived from the self-application convention?
3. What does Scott's theorem imply about deciding equality of untyped terms?

---

### Chapter 18: Dynamic Typing (pp. 159–167)

**Summary:** Formulates a dynamically typed language $\mathcal{L}\{\text{dyn}\}$ (dynamic PCF) with run-time class tags and class checks. Argues that dynamic languages are restricted static languages confined to a single recursive type. : [[Dynamic-Typing-and-Hybrid-Typing|Link1]], [[Godels-System-T-and-Total-Computation|Link2]]

**Key Definitions & Concepts by Section:**
- **18.1 Dynamically Typed PCF** — *class* (num, fun), *tagging of values*, *class-checking judgments* ($d\ \text{is num}\ n$, $d\ \text{isnt fun}$), *error judgment* ($d\ \text{err}$), progress and exclusivity lemmas. : [[Generic-Programming|Link1]], [[Dynamic-Types-and-the-Untyped-Lambda-Calculus|Link2]], [[Dynamic-Typing-and-Hybrid-Typing|Link3]]
- **18.2 Variations and Extensions** — treating zero/succ as separate classes, null and cons for lists, predicates and destructors ($\text{car}$, $\text{cdr}$, $\text{nil?}$), conditional dispatch. : [[Generic-Programming|Link]]
- **18.3 Critique of Dynamic Typing** — redundancy of run-time checks, inability to express loop invariants, overhead of classification, need for static types to optimize. : [[Dynamic-Typing-and-Hybrid-Typing|Link1]], [[Godels-System-T-and-Total-Computation|Link2]]

**Key Questions:**
1. Why must every value in a dynamic language carry a class tag?
2. What invariants can a static type system express that a dynamic language cannot?
3. Why is dynamic PCF not properly seen as PCF minus its type system?

---

### Chapter 19: Hybrid Typing (pp. 169–176)

**Summary:** Combines static and dynamic typing by adding a type dyn of classified values to a static language. Shows dyn is definable as a recursive type, and that dynamic typing is a mode of use of static typing. : [[Dynamic-Typing-and-Hybrid-Typing|Link]]

**Key Definitions & Concepts by Section:**
- **19.1 A Hybrid Language** — type $\text{dyn}$, *new* (attach classifier) and *cast* (check classifier) operations, canonical forms and safety theorems, definability of dyn as $\mu t.[\text{num} \hookrightarrow \text{nat}, \text{fun} \hookrightarrow t \rightharpoonup t]$. : [[Dynamic-Typing-and-Hybrid-Typing|Link]]
- **19.2 Dynamic as Static Typing** — embedding translation $d^\dagger$ of $\mathcal{L}\{\text{dyn}\}$ into the hybrid language. : [[Dynamic-Typing-and-Hybrid-Typing|Link1]], [[Function-Types-and-the-Lambda-Calculus|Link2]], [[Godels-System-T-and-Total-Computation|Link3]], [[Pattern-Matching|Link4]]
- **19.3 Optimization of Dynamic Typing** — hoisting class checks out of loops, changing types from dyn to $\text{dyn} \rightharpoonup \text{dyn}$ and $\text{nat} \rightharpoonup \text{nat}$ to eliminate redundant tags. : [[Dynamic-Typing-and-Hybrid-Typing|Link1]], [[Godels-System-T-and-Total-Computation|Link2]]
- **19.4 Static Versus Dynamic Typing** — refutation of common distinctions (types-with-values vs types-with-variables, run-time vs compile-time checks, heterogeneous vs homogeneous collections). : [[Function-Types-and-the-Lambda-Calculus|Link1]], [[Statics-And-Dynamics|Link2]]

**Key Questions:**
1. How is the type dyn definable from sums and recursive types?
2. Why can optimizations of dynamic code only be expressed in a static type system?
3. What is wrong with the claim that dynamic languages associate types with values while static ones associate them with variables?

---

### Chapter 20: Girard's System F (pp. 179–190)

**Summary:** Introduces polymorphism via System F ($\mathcal{L}\{\to\forall\}$), with type abstraction and type application. Demonstrates its remarkable definability (products, sums, naturals), gives an overview of parametricity, and examines restricted fragments. : [[Polymorphism-and-System-F|Link]]

**Key Definitions & Concepts by Section:**
- **20.1 System F** — *type abstraction* ($\Lambda(t.e)$), *type application* ($e[\tau]$), *universal type* ($\forall(t.\tau)$), type formation and typing rules, regularity, substitution, safety. : [[Polymorphism-and-System-F|Link]]
- **20.2 Polymorphic Definability** — Church encodings: unit as $\forall(r.r \to r)$, products, void as $\forall(r.r)$, sums, naturals as $\forall(t.t \to (t \to t) \to t)$, definitional equality, evaluator for System T definable in System F. : [[Polymorphism-and-System-F|Link]]
- **20.3 Parametricity Overview** — *free theorems*, polymorphic types constraining behavior (identity from $\forall(t.t \to t)$). : [[Polymorphism-and-System-F|Link]]
- **20.4 Restricted Forms of Polymorphism** — *impredicativity* (instantiating with polymorphic types), *predicative fragment* (quantification only over unquantified types), *prenex fragment* $\mathcal{L}_1\{\to\forall\}$ (monotypes and polytypes), *rank-restricted fragments* $\mathcal{L}_k\{\to\forall\}$.

**Key Questions:**
1. What is impredicative quantification and why is it responsible for System F's expressive power?
2. How are natural numbers encoded and why does the encoding force the iterator?
3. Why does the prenex fragment require a primitive let construct?

---

### Chapter 21: Abstract Types (pp. 191–200)

**Summary:** Models data abstraction using existential types. Interfaces are existential types, implementations are packages, clients are open expressions. Establishes representation independence via parametricity. : [[Product-Types|Link1]], [[Dynamic-Classification|Link2]], [[Sum-Types|Link3]], [[Data-Abstraction-and-Existential-Types|Link4]]

**Key Definitions & Concepts by Section:**
- **21.1 Existential Types** — *interface* ($\exists(t.\tau)$), *package* ($\text{pack}\ \rho\ \text{with}\ e\ \text{as}\ \exists(t.\tau)$), *client* ($\text{open}\ e_1\ \text{as}\ t,x.\ e_2$), *representation type*, *generativity*, statics, dynamics, safety. : [[Data-Abstraction-and-Existential-Types|Link]]
- **21.2 Data Abstraction Via Existentials** — queue example with list and pair-of-lists implementations, client independence from representation. : [[Data-Abstraction-and-Existential-Types|Link]]
- **21.3 Definability of Existentials** — encoding $\exists(t.\tau) \cong \forall(u.\forall(t.\tau \to u) \to u)$. : [[Data-Abstraction-and-Existential-Types|Link1]], [[Dynamic-Classification|Link2]]
- **21.4 Representation Independence** — *bisimilarity*, clients polymorphic in the representation type, proving a candidate implementation correct relative to a reference. : [[Data-Abstraction-and-Existential-Types|Link1]], [[Equational-Reasoning|Link2]], [[Modularity-and-Linking|Link3]]

**Key Questions:**
1. Why must the result type of an open expression not mention the abstract type?
2. How are existential types definable from universal types?
3. What is a bisimulation and how does it establish representation independence?

---

### Chapter 22: Constructors and Kinds (pp. 201–211)

**Summary:** Adds a layer of constructors classified by kinds, separating static data (constructors) from dynamic data (expressions). Distinguishes neutral from canonical constructors and develops canonizing substitution to preserve this distinction. : [[Constructors-and-Kinds|Link]]

**Key Definitions & Concepts by Section:**
- **22.1 Statics** — *kinds* (T, Unit, product, function kinds), *neutral constructors* ($u$, projections, application), *canonical constructors* ($\hat{a}$, $\langle\rangle$, pairs, $\lambda$), *constructor formation judgments* ($\Delta \vdash a \Rightarrow \kappa$ neutral, $\Delta \vdash c \Leftarrow \kappa$ canonical), canonical forms lemma. : [[Symbols-and-Dynamic-Binding|Link]]
- **22.2 Higher Kinds** — integrating constructors with a language, *type formation* ($\Delta \vdash \tau\ \text{type}$), impredicative vs predicative treatment of quantifiers, phase distinction. : [[Singleton-and-Dependent-Kinds|Link]]
- **22.3 Canonizing Substitution** — *canonizing substitution* ($[c/u:\kappa]a = a'$, etc.), simplifying illegal neutral-canonical combinations, well-definedness by lexicographic induction on kind. : [[Constructors-and-Kinds|Link]]
- **22.4 Canonization** — *general-form constructors*, *canonization judgment* ($\Delta \vdash c :: \kappa \Downarrow c$), *atomization judgment* ($\Delta \vdash c \Rightarrow c :: \kappa$), constructor equivalence via identical canonical forms. : [[Continuations|Link]]

**Key Questions:**
1. Why distinguish neutral from canonical constructors?
2. What problem does canonizing substitution solve that ordinary substitution cannot?
3. What is the phase distinction between constructors and expressions?

---

### Chapter 23: Subtyping (pp. 215–225)

**Summary:** Introduces subtyping as a preorder validating the subsumption principle. Analyzes subtyping for numeric, product, sum, function, quantified, and recursive types, with careful attention to variance and safety. : [[Subtyping|Link]]

**Key Definitions & Concepts by Section:**
- **23.1 Subsumption** — *subtyping judgment* ($\tau' <: \tau$), *subsumption rule* (reflexivity and transitivity structural rules). : [[Subtyping|Link]]
- **23.2 Varieties of Subtyping** — numeric subtyping and representation issues, product subtyping by width ($J \subseteq I$), sum subtyping with reversed containment. : [[Subtyping|Link]]
- **23.3 Variance** — *covariant*, *contravariant*, *invariant* positions, function types covariant in range and contravariant in domain, quantifier variance, bounded quantification ($t <: \rho$), recursive type subtyping and the unsoundness of naive rule $t\ \text{type} \vdash \tau' <: \tau \Rightarrow \mu t.\tau' <: \mu t.\tau$. : [[Subtyping|Link]]
- **23.4 Safety** — preservation and progress with subsumption, canonical forms with subtyping, inversion lemmas. : [[Dynamic-Classification|Link1]], [[State-and-Assignables|Link2]]

**Key Questions:**
1. Why is the function type contravariant in its domain?
2. Why does the naive subtyping rule for recursive types lead to unsoundness?
3. How does subsumption weaken the meaning of a type assertion?

---

### Chapter 24: Singleton Kinds (pp. 227–237)

**Summary:** Introduces singleton kinds $S(\tau)$ to express type definitions and sharing: the kind of constructors definitionally equal to $\tau$. Develops subkinding, dependent product and function kinds, and higher singletons. : [[Singleton-and-Dependent-Kinds|Link]]

**Key Definitions & Concepts by Section:**
- **24.1 Overview** — type abbreviation as the motivating problem, compositionality, singleton kinds capturing type identity.
- **24.2 Singletons** — *singleton kind* ($S(c)$), *self-recognition* ($c :: S(c)$), *subkinding* ($\kappa_1 <: \kappa_2$), $S(c) <: \text{T}$, kind equivalence.
- **24.3 Dependent Kinds** — *dependent product kind* ($\Sigma u::\kappa_1.\kappa_2$), *dependent function kind* ($\Pi u::\kappa_1.\kappa_2$), formation/introduction/elimination rules, subkinding variance, extensionality. : [[Singleton-and-Dependent-Kinds|Link]]
- **24.4 Higher Singletons** — $S(c::\kappa)$ defined by induction on $\kappa$, self-recognition rules, theorem that every constructor has a singleton kind determining it up to definitional equality. : [[Singleton-and-Dependent-Kinds|Link]]

**Key Questions:**
1. How does a singleton kind express a type definition?
2. Why are dependent kinds needed once singletons are introduced?
3. What do the extensionality principles state for $\Sigma$ and $\Pi$ kinds?

---

### Chapter 25: Dynamic Dispatch (pp. 241–249)

**Summary:** Analyzes object-oriented dynamic dispatch as an abstraction over a dispatch matrix. Develops two dual organizations — class-based (objects as tuples of methods) and method-based (methods as case analysis on sums) — and adds self-reference. : [[Exceptions|Link1]], [[Plotkins-PCF-and-Partial-Computation|Link2]], [[Dynamic-Classification|Link3]]

**Key Definitions & Concepts by Section:**
- **25.1 The Dispatch Matrix** — *dispatch matrix* ($e_{\text{dm}}$), *class*, *method*, *instance type*, *instance data*, *object*, *new* and message send ($e \Leftarrow d$). : [[Objects-and-Inheritance|Link]]
- **25.2 Class-Based Organization** — *class vector* ($e_{\text{cv}}$), object type $\rho = \prod_{d\in D}\rho_d$, message send as projection. : [[Objects-and-Inheritance|Link]]
- **25.3 Method-Based Organization** — transpose of the dispatch matrix, *method vector* ($e_{\text{mv}}$), object type $\tau = \sum_{c\in C}\tau_c$, dispatch functions. : [[Objects-and-Inheritance|Link]]
- **25.4 Self-Reference** — abstract object type $t$, methods parameterized by class and method vectors, $\text{self}(\tau)$ type for self-referential vectors. : [[Laziness-and-Polarization|Link1]], [[Objects-and-Inheritance|Link2]], [[Recursive-Types|Link3]]

**Key Questions:**
1. What is the defining equation of dynamic dispatch relating new and message send?
2. How are the class-based and method-based organizations related by a duality?
3. How does self-reference enable methods to create objects and send messages?

---

### Chapter 26: Inheritance (pp. 251–255)

**Summary:** Builds on the dispatch matrix to define inheritance: extending a dispatch matrix with new classes or methods, inheriting some behaviors and overriding others, in both class-based and method-based organizations. : [[Objects-and-Inheritance|Link]]

**Key Definitions & Concepts by Section:**
- **26.1 Class and Method Extension** — adding a new class (specifying instance type and each method's behavior), adding a new method, *subclass* and *submethod*, subtype conditions for sensible inheritance. : [[Objects-and-Inheritance|Link]]
- **26.2 Class-Based Inheritance** — extending the class vector, inheritance as a record of definition history with no semantic content, object subtyping when methods are added. : [[Objects-and-Inheritance|Link]]
- **26.3 Method-Based Inheritance** — dual treatment extending the method vector, object type widening when a class is added. : [[Objects-and-Inheritance|Link]]

**Key Questions:**
1. Why does inheritance carry no semantic significance in the class-based organization?
2. What subtype condition must hold for inheriting a method to be sensible?
3. How does adding a new method differ in effect between class-based and method-based organizations?

---

### Chapter 27: Control Stacks (pp. 259–266)

**Summary:** Introduces the abstract machine $\mathcal{K}\{\text{nat}\rightharpoonup\}$ with an explicit control stack recording pending computations, making control flow explicit and eliminating search-rule premises. Proves the machine equivalent to the structural dynamics. : [[Control-Stacks-and-Abstract-Machines|Link]]

**Key Definitions & Concepts by Section:**
- **27.1 Machine Definition** — *state* ($k \triangleright e$ evaluation, $k \triangleleft e$ return), *control stack* (list of frames), *frame* (records a pending context), *initial* and *final states*. : [[Continuations|Link]]
- **27.2 Safety** — *stack typing* ($k : \tau$), *frame typing* ($f : \tau \Rightarrow \tau'$), *well-formed states*, preservation and progress for the machine. : [[Dynamic-Classification|Link1]], [[State-and-Assignables|Link2]]
- **27.3 Correctness of the Control Machine** — *completeness* (structural evaluation implies machine evaluation), *soundness* (machine evaluation implies structural evaluation), *unravelling* ($s \# e$), wrapping a stack around an expression. : [[Control-Stacks-and-Abstract-Machines|Link]]

**Key Questions:**
1. What advantage does an explicit control stack provide over search rules?
2. How does the machine's two-state form (evaluation vs return) mirror the dynamics?
3. How is soundness of the machine proved via unravelling states to expressions?

---

### Chapter 28: Exceptions (pp. 267–275)

**Summary:** Introduces exceptions as a non-local transfer of control. Starts with simple failures, generalizes to exceptions carrying values, discusses the choice of exception type, and adds a modality encapsulating fallible computations. : [[Exceptions|Link]]

**Key Definitions & Concepts by Section:**
- **28.1 Failures** — *fail* and *catch*, *stack unwinding*, failure state ($k \blacktriangleright$), handler frame, safety with failure.
- **28.2 Exceptions** — *raise* and *handle*, exception value of type $\tau_{\text{exn}}$, exception state ($k \blacktriangleright e$). : [[Exceptions|Link]]
- **28.3 Exception Type** — choosing $\tau_{\text{exn}}$ as strings, naturals, sums, or extensible sums (dynamic classification). : [[Exceptions|Link]]
- **28.4 Encapsulation of Exceptions** — *fallible* vs *infallible* expressions, modality $\text{fallible}(\tau)$, *ok* and *try* forms, ensuring uncaught failures cannot arise. : [[Exceptions|Link]]

**Key Questions:**
1. How does stack unwinding locate the nearest enclosing handler?
2. Why is a sum type or extensible sum preferable for the exception type?
3. What does the encapsulation modality achieve by distinguishing fallible from infallible expressions?

---

### Chapter 29: Continuations (pp. 277–285)

**Summary:** Introduces continuations as reified control stacks — first-class values representing the rest of the computation. Presents letcc/throw, proves safety, and implements coroutines. : [[Continuations|Link]]

**Key Definitions & Concepts by Section:**
- **29.1 Informal Overview** — short-circuiting evaluation with continuations, composition of a function with a continuation.
- **29.2 Semantics of Continuations** — *continuation type* ($\text{cont}(\tau)$), *letcc* (seize current continuation), *throw* (restore a continuation), reified stack value ($\text{cont}(k)$), safety theorem. : [[Continuations|Link]]
- **29.3 Coroutines** — *coroutines* as symmetric cooperating routines, type isomorphism $\tau_{\text{coro}} \cong (\tau \times \tau_{\text{coro}})\ \text{cont}$, *resume*, producer/consumer example, cooperative multi-threading. : [[Continuations|Link]]

**Key Questions:**
1. How does letcc duplicate the control stack and how does throw destroy it?
2. Why do continuations never expire?
3. How is a system of two coroutines bootstrapped?

---

### Chapter 30: Constructive Logic (pp. 289–297)

**Summary:** Presents constructive logic where truth means having a proof. Introduces proof terms and their dynamics, culminating in the propositions-as-types correspondence identifying proofs with programs. : [[Constructors-and-Kinds|Link]]

**Key Definitions & Concepts by Section:**
- **30.1 Constructive Semantics** — *proof* vs *refutation*, undecided/open problems, constructive logic as a logic of positive information. : [[Continuations|Link1]], [[Constructors-and-Kinds|Link2]]
- **30.2 Constructive Logic** — *provability* ($\varphi\ \text{true}$), *introduction* and *elimination rules* for truth, conjunction, implication, falsehood, disjunction, *negation* ($\neg\varphi \equiv \varphi \supset \perp$), *proof terms* ($p : \varphi$). : [[Constructors-and-Kinds|Link]]
- **30.3 Proof Dynamics** — *Gentzen's Principle* (elimination inverts introduction), *conservation of proof*, *reversibility of proof*, definitional equivalences. : [[Control-Stacks-and-Abstract-Machines|Link]]
- **30.4 Propositions as Types** — correspondence chart: $\top \leftrightarrow \text{unit}$, $\perp \leftrightarrow \text{void}$, $\wedge \leftrightarrow \times$, $\supset \leftrightarrow \to$, $\vee \leftrightarrow +$. : [[Propositions-as-Types|Link]]

**Key Questions:**
1. Why can constructive logic not assert that every proposition is either true or false?
2. What is the computational content of a proof of an implication?
3. How do the introduction and elimination rules for conjunction mirror products?

---

### Chapter 31: Classical Logic (pp. 299–311)

**Summary:** Presents classical logic as a logic of perfect information with symmetric truth and falsity conditions, mediated by contradiction. Explains the computational content via proofs and refutations (continuations) and the double-negation translation. : [[Propositions-as-Types|Link]]

**Key Definitions & Concepts by Section:**
- **31.1 Classical Logic** — *provability* and *refutability* judgments, *contradiction* ($\#$), *proofs* ($p$) and *refutations* ($k$), $\text{ccp}$ (call with current proof) and $\text{ccr}$ (call with current refutation), truth and falsity rules for each connective. : [[Propositions-as-Types|Link]]
- **31.2 Deriving Elimination Forms** — packaging indirect proof to recover constructive elimination rules. : [[Propositions-as-Types|Link]]
- **31.3 Proof Dynamics** — transition system on contradictions $k \# p$, lazy vs eager priority, preservation and progress. : [[Control-Stacks-and-Abstract-Machines|Link]]
- **31.4 Law of the Excluded Middle** — derivation of $\varphi \vee \neg\varphi$, computational behavior as backtracking. : [[Propositions-as-Types|Link]]
- **31.5 The Double-Negation Translation** — translation $\varphi^\ast$ of classical into constructive logic, classical truth weakened to constructive irrefutability ($\neg\neg\varphi^\ast$), showing constructive logic is more expressive. : [[Propositions-as-Types|Link]]

**Key Questions:**
1. Why is classical logic weaker (less expressive) than constructive logic despite having more principles?
2. What is the computational meaning of a refutation?
3. How does the proof of excluded middle "change its mind" under inspection?

---

### Chapter 32: Symbols (pp. 315–321)

**Summary:** Introduces symbols as atomic names given meaning by families of operations. Covers symbol declaration with scoped and scope-free dynamics, and symbolic references with decidable comparison.

**Key Definitions & Concepts by Section:**
- **32.1 Symbol Declaration** — *symbol*, *signature* $\Sigma$ (mapping symbols to types), *generation* ($\nu a:\tau\ \text{in}\ e$), *mobility* ($\tau\ \text{mobile}$), *scoped dynamics* (extent limited to scope), *scope-free dynamics* (symbol persists). : [[Symbols-and-Dynamic-Binding|Link]]
- **32.2 Symbolic References** — *symbolic reference type* ($\text{sym}(\tau)$), *reference value* ($\&a$), *comparison* ($\text{is}[a][t.\tau](e;e_1;e_2)$), statics mediating type discrepancy, safety. : [[Symbols-and-Dynamic-Binding|Link]]

**Key Questions:**
1. How does a symbol differ from a variable?
2. Why must the result type of a symbol declaration be mobile under scoped dynamics?
3. How does the comparison form reveal the type of a symbol in the positive branch?

---

### Chapter 33: Fluid Binding (pp. 323–330)

**Summary:** Recovers a type-safe analogue of dynamic binding by divorcing it from variables and applying it to symbols. Fluid binding associates a value with a symbol within a dynamic scope. : [[Symbols-and-Dynamic-Binding|Link]]

**Key Definitions & Concepts by Section:**
- **33.1 Statics** — *put* ($\text{put}[a](e_1;e_2)$) and *get* ($\text{get}[a]$), symbol as parameter not binder. : [[Symbols-and-Dynamic-Binding|Link]]
- **33.2 Dynamics** — stack-like environment $\mu$ mapping symbols to values, *unbound judgment* ($e\ \text{unbound}_\mu$). : [[Exceptions|Link]]
- **33.3 Type Safety** — preservation and progress with unbound symbols. : [[Type-Safety|Link]]
- **33.4 Some Subtleties** — interaction with function types, closures capturing unbound symbols, comparison with static binding, fluid binding as implicit argument passing. : [[Symbols-and-Dynamic-Binding|Link]]
- **33.5 Fluid References** — *fluid reference type* ($\text{fluid}(\tau)$), $\text{getfl}$ and $\text{putfl}$ deferring to symbol-indexed primitives. : [[Symbols-and-Dynamic-Binding|Link]]

**Key Questions:**
1. How does fluid binding differ from the dynamic scope criticized in Chapter 8?
2. What can go wrong when a fluid-bound symbol is captured in a returned function?
3. Why do references to fluids fail to be mobile?

---

### Chapter 34: Dynamic Classification (pp. 331–337)

**Summary:** Introduces dynamic classification: generating new classes at run time to classify values. New classes are unguessable secrets, enabling extensibility, encryption-like confidentiality, and exception handling. : [[Dynamic-Classification|Link]]

**Key Definitions & Concepts by Section:**
- **34.1 Dynamic Classes** — *classified type* ($\text{clsfd}$), *instance* ($\text{in}[a](e)$), *comparison/match* ($\text{isin}[a](e;x.e_1;e_2)$), free dynamics for class generation, reliance on disequality of names. : [[Concurrent-and-Distributed-Algol|Link1]], [[Dynamic-Classification|Link2]]
- **34.2 Class References** — *class reference type* ($\text{class}(\tau)$), *mk* and *isofcls* (two-stage pattern matching). : [[Dynamic-Classification|Link1]], [[State-and-Assignables|Link2]]
- **34.3 Definability of Dynamic Classes** — $\text{clsfd} \cong \exists(t.t\ \text{sym} \times t)$. : [[Concurrent-and-Distributed-Algol|Link1]], [[Dynamic-Classification|Link2]]
- **34.4 Classifying Secrets** — confidentiality and integrity via controlling access to constructors and destructors. : [[Dynamic-Classification|Link]]

**Key Questions:**
1. Why must the dynamics of dynamic classification use a scope-free (free) symbol dynamics?
2. How does dynamic classification provide "perfect encryption"?
3. Why is it not sensible for the dynamics to rely on disequality of variables?

---

### Chapter 35: Modernized Algol (pp. 341–351)

**Summary:** Introduces an imperative block-structured language $\mathcal{L}\{\text{nat cmd}\rightharpoonup\}$ separating pure expressions from impure commands acting on assignables. Enforces a stack discipline for allocation and a mobility restriction for safety.

**Key Definitions & Concepts by Section:**
- **35.1 Basic Commands** — *commands* (ret, bnd, dcl, get, set), *assignables*, *encapsulated command* ($\text{cmd}(m)$), *block structure*, *stack discipline*, memory $\mu$, statics and dynamics, preservation and progress.
- **35.2 Some Programming Idioms** — sequential composition, conditionals, while loops, procedures, factorial example with loop invariant. : [[State-and-Assignables|Link1]], [[Generic-Programming|Link2]]
- **35.3 Typed Commands and Typed Assignables** — typed command ($m \sim \tau$), typed assignable ($a \sim \tau$), *command type* ($\text{cmd}(\tau)$), *mobility* ($\tau\ \text{mobile}$) and the mobility condition, why unrestricted types break preservation. : [[State-and-Assignables|Link]]

**Key Questions:**
1. Why must assignables and returned values have mobile types to preserve the stack discipline?
2. What is the difference between a variable and an assignable?
3. How does the modal separation of expressions and commands keep expression evaluation unconstrained?

---

### Chapter 36: Assignable References (pp. 353–364)

**Summary:** Adds references to assignables, providing capabilities to get/set and equality testing. Covers scoped references (immobile) and free assignables (enabling mutable and cyclic structures), and benign effects. : [[State-and-Assignables|Link]]

**Key Definitions & Concepts by Section:**
- **36.1 Capabilities** — getter/setter pair as a capability, generic doubling procedure.
- **36.2 Scoped Assignables** — *reference type* ($\text{ref}(\tau)$), *reference value* ($\&a$), $\text{getref}$ and $\text{setref}$, immobility of references, *aliasing* and interference. : [[State-and-Assignables|Link]]
- **36.3 Free Assignables** — scope-free dynamics ($\nu\Sigma\{m \parallel \mu\}$), $\text{newref}$ allocating and returning a reference, mutable data structures. : [[Concurrent-and-Distributed-Algol|Link1]], [[State-and-Assignables|Link2]]
- **36.4 Safety for Free Assignables** — well-formed memories accounting for cyclic dependencies, preservation and progress. : [[State-and-Assignables|Link]]
- **36.5 Benign Effects** — consolidating expressions and commands, backpatching for recursion, memoization, splay trees. : [[State-and-Assignables|Link]]

**Key Questions:**
1. Why are references immobile when assignables are stack-allocated?
2. What is aliasing and why does it complicate reasoning about reference-based code?
3. How does backpatching implement recursion using state?

---

### Chapter 37: Lazy Evaluation (pp. 367–377)

**Summary:** Develops by-need (lazy) evaluation using memoization and sharing via named computations. Covers by-need dynamics with black holes, lazy data structures, and a suspension type consolidating laziness. : [[Laziness-and-Polarization|Link]]

**Key Definitions & Concepts by Section:**
- **37.1 By-Need Dynamics** — *memo table* $\mu$, naming deferred computations with symbols, *black hole* ($\bullet$) detecting circular dependencies, lazy successor, by-need application, shared recursion. : [[Laziness-and-Polarization|Link]]
- **37.2 Safety** — well-formed states permitting self-reference through the memo table, *loops judgment* ($\nu\Sigma\{e\parallel\mu\}\ \text{loops}$), preservation and progress. : [[Dynamic-Classification|Link1]], [[State-and-Assignables|Link2]]
- **37.3 Lazy Data Structures** — by-need products with symbols for components. : [[Laziness-and-Polarization|Link]]
- **37.4 Suspensions** — *suspension type* ($\tau\ \text{susp}$), *delay* ($\text{susp}\ x:\tau\ \text{is}\ e$), *force*, lazy lists $\mu t.(\text{unit}+(\text{nat}\times t))\ \text{susp}$.

**Key Questions:**
1. How does naming a deferred computation achieve sharing?
2. What does the black hole detect and why is it needed?
3. How does the suspension type let the programmer choose laziness per type?

---

### Chapter 38: Polarization (pp. 379–386)

**Summary:** Resolves the arbitrary choice between eager and lazy dynamics by distinguishing types by polarity: positive (defined by values, eager/inductive) and negative (defined by observations, lazy/coinductive), using focusing. : [[Laziness-and-Polarization|Link]]

**Key Definitions & Concepts by Section:**
- **38.1 Positive and Negative Types** — *positive types* ($\tau^+$: suspension $\downarrow\tau^-$, nat), *negative types* ($\tau^-$: inclusion $\uparrow\tau^+$, partial function), *polarity shift*. : [[Laziness-and-Polarization|Link]]
- **38.2 Focusing** — three forms: values, continuations, computations; positive/negative values and continuations, cuts. : [[Plotkins-PCF-and-Partial-Computation|Link1]], [[Recursive-Types|Link2]]
- **38.3 Statics** — typing rules for positive values, positive/negative continuations, negative values, computations. : [[Symbols-and-Dynamic-Binding|Link]]
- **38.4 Dynamics** — interaction rules between values and continuations, composition of computations and continuations. : [[Exceptions|Link]]
- **38.5 Safety** — preservation via substitution and composition lemmas, progress from canonical forms. : [[Dynamic-Classification|Link1]], [[State-and-Assignables|Link2]]

**Key Questions:**
1. How does polarity distinguish eager from lazy types within one language?
2. What is a positive type defined by and what is a negative type defined by?
3. How does focusing make the value status of each type evident?

---

### Chapter 39: Nested Parallelism (pp. 389–402)

**Summary:** Introduces deterministic fork-join parallelism via a parallel binding construct. Proves the implicit parallelism theorem (sequential and parallel dynamics coincide) and develops a cost dynamics with work and depth, culminating in Brent's theorem. : [[Parallelism|Link]]

**Key Definitions & Concepts by Section:**
- **39.1 Binary Fork-Join** — *parallel binding* ($\text{par}\ x_1=e_1\ \text{and}\ x_2=e_2\ \text{in}\ e$), sequential and parallel dynamics, *implicit parallelism theorem* (deterministic parallelism theorem). : [[Parallelism|Link]]
- **39.2 Cost Dynamics** — *cost graphs* ($0$, $1$, $\otimes$, $\oplus$), *work* $\text{wk}(c)$, *depth* $\text{dp}(c)$, *critical path*, correspondence of work/depth to sequential/parallel complexity. : [[Parallelism|Link1]], [[Statics-And-Dynamics|Link2]]
- **39.3 Multiple Fork-Join** — *data parallelism*, sequence operations (tabulate, map, concatenate) with cost dynamics. : [[Parallelism|Link]]
- **39.4 Provably Efficient Implementations** — *SMP model*, *Brent's theorem* (time $O(\max(w/p, d))$), *parallelizability ratio* ($w/d$), greedy scheduling. : [[Parallelism|Link]]

**Key Questions:**
1. Why does parallelism affect only efficiency and not semantics?
2. What do work and depth measure, and how do they bound execution on $p$ processors?
3. When is a program considered parallelizable?

---

### Chapter 40: Futures and Speculations (pp. 403–411)

**Summary:** Introduces futures (evaluated eagerly in parallel, work-efficient) and speculations (evaluated eagerly but possibly wasted, work-inefficient). Gives sequential and parallel dynamics and applications like pipelining and sparks. : [[Parallelism|Link]]

**Key Definitions & Concepts by Section:**
- **40.1 Futures** — *future type* ($\text{fut}(\tau)$), *fut* and *fsyn*, sequential dynamics.
- **40.2 Speculations** — *speculation type* ($\text{spec}(\tau)$), *spec* and *ssyn*, speculations as values. : [[Dynamic-Typing-and-Hybrid-Typing|Link1]], [[Continuations|Link2]]
- **40.3 Parallel Dynamics** — task names, local and global transitions, final states differ (futures require all tasks complete, speculations may be abandoned). : [[Parallelism|Link1]], [[Exceptions|Link2]], [[Statics-And-Dynamics|Link3]]
- **40.4 Applications of Futures** — *pipelining*, work lists with future tails, *sparks* for forcing suspensions in parallel, encoding binary nested parallelism. : [[Parallelism|Link]]

**Key Questions:**
1. What is the key difference between a future and a suspension?
2. Why are futures work-efficient while speculations are work-inefficient?
3. How do futures implement pipelining to overlap producer and consumer?

---

### Chapter 41: Process Calculus (pp. 415–432)

**Summary:** Develops a process calculus modeling concurrent interaction: processes awaiting events, synchronization, replication, channel allocation, communication, channel passing, and universality via encoding the untyped $\lambda$-calculus. : [[Concurrency-and-Process-Calculus|Link1]], [[Concurrent-and-Distributed-Algol|Link2]]

**Key Definitions & Concepts by Section:**
- **41.1 Actions and Events** — *sequential process* ($\$E$), *event* (sum of signal/query), *structural congruence*, vending machine example. : [[Concurrency-and-Process-Calculus|Link]]
- **41.2 Interaction** — *inert process* ($1$), *parallel composition* ($P_1 \parallel P_2$), labeled transitions ($P \xrightarrow{\alpha} P'$), *actions* (query $a?$, signal $a!$, silent $\varepsilon$), complementarity. : [[Continuations|Link1]], [[Exceptions|Link2]], [[Laziness-and-Polarization|Link3]]
- **41.3 Replication** — $*P$, *replicated synchronization* to avoid indeterminacy. : [[Dynamic-Typing-and-Hybrid-Typing|Link1]], [[Exceptions|Link2]]
- **41.4 Allocating Channels** — *channel declaration* ($\nu a.P$), *scope extrusion*, statics ensuring proper scoping. : [[Concurrency-and-Process-Calculus|Link]]
- **41.5 Communication** — *send* ($!a(e;P)$) and *receive* ($?a(x.P)$), typed channels, synchronous and asynchronous communication. : [[Continuations|Link1]], [[Dynamic-Typing-and-Hybrid-Typing|Link2]]
- **41.6 Channel Passing** — *channel type* ($\tau\ \text{chan}$), dynamic send/receive on references. : [[Concurrency-and-Process-Calculus|Link]]
- **41.7 Universality** — encoding the untyped $\lambda$-calculus, continuation as $\pi \cong (\pi\ \text{chan} \times \pi)\ \text{chan}$. : [[Polymorphism-and-System-F|Link]]

**Key Questions:**
1. How do two processes synchronize on complementary actions?
2. What is scope extrusion and why is it important for channel passing?
3. How does the process calculus achieve universality?

---

### Chapter 42: Concurrent Algol (pp. 435–446)

**Summary:** Integrates concurrency into Modernized Algol, using broadcast communication of dynamically classified values as the synchronization mechanism. Adds selective communication and shows free assignables are definable as server processes. : [[Concurrent-and-Distributed-Algol|Link]]

**Key Definitions & Concepts by Section:**
- **42.1 Concurrent Algol** — processes ($1$, $\text{proc}(m)$, $\parallel$, $\nu a\sim\tau.p$), statics and dynamics, command execution judgment. : [[Concurrent-and-Distributed-Algol|Link]]
- **42.2 Broadcast Communication** — *spawn*, *emit*, *acc*, *newch*, channels as dynamic classes, confidentiality via classification. : [[Concurrent-and-Distributed-Algol|Link]]
- **42.3 Selective Communication** — *event type* ($\text{event}(\tau)$), *select* ($?a$), *never*, *or*, *sync*, pattern-driven events. : [[Concurrent-and-Distributed-Algol|Link]]
- **42.4 Free Assignables as Processes** — server process per assignable handling get/set messages. : [[Concurrent-and-Distributed-Algol|Link]]

**Key Questions:**
1. How are channels identified with dynamic classes in Concurrent Algol?
2. Why does broadcast communication require polling and how does selective communication fix it?
3. How is a free assignable implemented as a server process?

---

### Chapter 43: Distributed Algol (pp. 447–456)

**Summary:** Extends Concurrent Algol with a spatial type system mediating access to located resources across network sites. Commands, channels, and events are indexed by site, and the safety theorem ensures resources are accessed only at their site. : [[Concurrent-and-Distributed-Algol|Link]]

**Key Definitions & Concepts by Section:**
- **43.1 Statics** — *site-indexed types* ($\text{cmd}[w](\tau)$, $\text{chan}[w](\tau)$, $\text{event}[w](\tau)$), *at* command to change locus of execution, possible-worlds interpretation (S5). : [[Symbols-and-Dynamic-Binding|Link]]
- **43.2 Dynamics** — atomic process $\text{proc}[w](m)$, command execution at a site, no cross-site synchronization. : [[Exceptions|Link]]
- **43.3 Safety** — preservation and progress ensuring channel synchronization only at the channel's site. : [[Dynamic-Classification|Link1]], [[State-and-Assignables|Link2]]
- **43.4 Situated Types** — *skeleton* ($\varphi$) factored from site, *situated type* ($\varphi\ \text{at}\ w$), *instantiation* ($\varphi\langle w\rangle$), *constant family* ($\text{exactly}(\tau)$), *mobile families*. : [[Concurrent-and-Distributed-Algol|Link]]

**Key Questions:**
1. How does the spatial type system ensure a resource is accessed only at its site?
2. What does it mean to interpret location as a principal in a security setting?
3. Why must the result of an at command have a mobile (constant) family?

---

### Chapter 44: Components and Linking (pp. 459–463)

**Summary:** Connects modularity to the structural properties of hypothetical judgments: dependencies are free variables, interfaces are types, and linking is substitution. Discusses initialization and effects. : [[Modularity-and-Linking|Link]]

**Key Definitions & Concepts by Section:**
- **44.1 Simple Units and Linking** — *client* and *implementor*, *interface* ($\tau_{\text{intf}}$), *linking as substitution* ($[e_{\text{impl}}/x]e_{\text{client}}$), *API*, *separate compilation*, *separate checking*, *dynamic linking*. : [[Modularity-and-Linking|Link]]
- **44.2 Initialization and Effects** — encapsulated commands ($\tau_{\text{intf}}\ \text{cmd}$) for effectful components, *sequentialization*, *initialization procedure* staging effects. : [[Modularity-and-Linking|Link]]

**Key Questions:**
1. How does linking correspond to the structural rule of transitivity/substitution?
2. Why must effectful components be typed as encapsulated commands rather than plain implementations?
3. What is the role of an initialization procedure?

---

### Chapter 45: Type Abstractions and Type Classes (pp. 465–478)

**Summary:** Develops module types (signatures) as the controlled revelation of type information. Type abstractions are opaque (existential), type classes are transparent (singleton kinds), unified by translucency via subtyping and subkinding. : [[Modularity-and-Linking|Link]]

**Key Definitions & Concepts by Section:**
- **45.1 Type Abstraction** — *signature* ($[t::\kappa;\tau]$), *structure*, *sealing* ($M \upharpoonright \sigma$), static and dynamic parts ($M\cdot s$, $M\cdot d$), representation independence forbidding the static part of a sealed module. : [[Data-Abstraction-and-Existential-Types|Link1]], [[Modularity-and-Linking|Link2]], [[Polymorphism-and-System-F|Link3]]
- **45.2 Type Classes** — *type class* or *view*, *instance*, principal signature via singleton kinds, subsumption linking, ordered types example. : [[Modularity-and-Linking|Link]]
- **45.3 A Module Language** — $\mathcal{L}\{\text{mod}\}$ syntax (signatures, modules, constructors, expressions), signature formation/equivalence/subsignature, module values, *self-recognition*, *avoidance problem* requiring explicit signature annotations. : [[Modularity-and-Linking|Link]]
- **45.4 First- and Second-Class** — first-class (signatures as types) vs second-class modules, why second-class is more expressive, packages as first-class modules, open. : [[Modularity-and-Linking|Link]]

**Key Questions:**
1. How do type abstractions and type classes represent the two extremes of translucency?
2. Why is the static part of a sealed module not accessible?
3. What is the avoidance problem and why does it require explicit signature annotations?

---

### Chapter 46: Hierarchy and Parameterization (pp. 481–493)

**Summary:** Extends modules with hierarchies (dependent pairs of modules with sharing constraints) and parameterization (functors). Develops sharing propagation and contrasts generative with applicative functors. : [[Modularity-and-Linking|Link]]

**Key Definitions & Concepts by Section:**
- **46.1 Hierarchy** — *hierarchical signature* ($\sum X:\sigma_1.\sigma_2^X$), *sharing specification* and *sharing propagation*, *submodule*, *projectibility*, fibration reading.
- **46.2 Parameterization** — *functor* ($\lambda Z:\sigma_{\text{eqord}}.M_{\text{keydict}}$), *functor signature* ($\prod Z:\sigma_1.\sigma_2^Z$), *signature modification* for sharing constraints, deducing instance signatures. : [[Pattern-Matching|Link1]], [[Laziness-and-Polarization|Link2]]
- **46.3 Extending Modules** — syntax for hierarchies and functors, *projectible judgment*, formation/equivalence/subsignature rules, generative functors.
- **46.4 Applicative Functors** — *applicative functor* (instances projectible), incompatibility with conditional modules, compromise of representation independence. : [[Modularity-and-Linking|Link]]

**Key Questions:**
1. How does a hierarchical signature express that two components share a type?
2. Why are functors treated as generative by default?
3. What does one give up by making functors applicative?

---

### Chapter 47: Equational Reasoning for T (pp. 497–508)

**Summary:** Develops the theory of observational equivalence for System T, introduces logical equivalence via logical relations, and proves the two coincide. Establishes laws of equality including induction. : [[Equational-Reasoning|Link]]

**Key Definitions & Concepts by Section:**
- **47.1 Observational Equivalence** — *complete program* (closed expression of type nat), *Kleene equality* ($e \cong e'$), *expression context* and *program context*, *replacement* ($C\{e\}$), *observational equivalence* ($\Gamma \vdash e \cong_\sim e' : \tau$), *consistent congruence*, coarsest consistent congruence theorem. : [[Equational-Reasoning|Link]]
- **47.2 Logical Equivalence** — *logical equivalence* ($e \sim_\tau e'$) by induction on types, passive vs active uses, open logical equivalence. : [[Equational-Reasoning|Link]]
- **47.3 Logical and Observational Equivalence Coincide** — *converse evaluation*, *consistency*, *reflexivity* (fundamental theorem), *congruence*, *termination*, *symbolic evaluation* principle.
- **47.4 Some Laws of Equality** — general laws, function extensionality, induction law for nat. : [[Equational-Reasoning|Link]]

**Key Questions:**
1. Why is observational equivalence the coarsest consistent congruence?
2. How is logical equivalence defined at function type and why?
3. What does the coincidence of logical and observational equivalence buy us for reasoning?

---

### Chapter 48: Equational Reasoning for PCF (pp. 509–519)

**Summary:** Extends equational reasoning to PCF with general recursion. The proof relies on admissible relations, fixed point induction, and compactness, and the chapter concludes with co-natural numbers. : [[Equational-Reasoning|Link]]

**Key Definitions & Concepts by Section:**
- **48.1 Observational Equivalence** — Kleene equality accounting for divergence, observational equivalence, coarsest consistent congruence. : [[Equational-Reasoning|Link]]
- **48.2 Logical Equivalence** — logical equivalence for partial functions, *strictness* (divergent terms are equivalent). : [[Equational-Reasoning|Link]]
- **48.3 Logical and Observational Equivalence Coincide** — *bounded recursion* ($\text{fix}^m$), *fixed point induction*.
- **48.4 Compactness** — *compactness theorem* (only finitely many unwindings needed in a complete evaluation), proved via the stack machine.
- **48.5 Co-Natural Numbers** — lazy successor admitting $\omega$, *co-natural numbers* ($\text{conat}$), coinductive definition of logical equivalence, proof by coinduction. : [[Equational-Reasoning|Link]]

**Key Questions:**
1. What does compactness state and why is it essential for fixed point induction?
2. How does logical equivalence handle divergent expressions?
3. Why is induction invalid for co-natural numbers?

---

### Chapter 49: Parametricity (pp. 521–535)

**Summary:** Develops parametricity for System F: polymorphic types constrain programs so strongly that correctness follows from typing. Defines parametric logical equivalence, proves the parametricity theorem, and derives free theorems and representation independence. : [[Polymorphism-and-System-F|Link]]

**Key Definitions & Concepts by Section:**
- **49.1 Overview** — informal parametricity (identity from $\forall(t.t\to t)$, emptiness of $\forall(t.t)$, Church numerals).
- **49.2 Observational Equivalence** — answer type $2$ with $\text{tt}$ and $\text{ff}$, Kleene equality, observational equivalence for System F. : [[Equational-Reasoning|Link]]
- **49.3 Logical Equivalence** — *admissible relation*, *type substitution* ($\delta$), *admissible relation assignment* ($\eta$), *parametric logical equivalence* ($e \sim_\tau e'[\eta:\delta\leftrightarrow\delta']$), *parametricity theorem* (every expression is logically equivalent to itself), *identity extension*. : [[Equational-Reasoning|Link]]
- **49.4 Parametricity Properties** — identity function theorem, strong definability of unit/products/naturals, unicity of iterators. : [[Polymorphism-and-System-F|Link]]
- **49.5 Representation Independence, Revisited** — clients as polymorphic functions, bisimilarity via parametricity. : [[Data-Abstraction-and-Existential-Types|Link1]], [[Equational-Reasoning|Link2]], [[Modularity-and-Linking|Link3]]

**Key Questions:**
1. Why does the definition of logical equivalence for $\forall$ quantify over all relations between possibly different types?
2. What is an admissible relation and why is admissibility required?
3. How does parametricity imply representation independence for abstract types?

---

### Chapter 50: Process Equivalence (pp. 537–545)

**Summary:** Defines equivalence of concurrent processes by their potential for interaction rather than final outcomes, using strong and weak bisimilarity, and proves congruence. : [[Equational-Reasoning|Link]]

**Key Definitions & Concepts by Section:**
- **50.1 Process Calculus** — consolidates processes and events with broadcast communication, statics and dynamics, structural congruence. : [[Concurrency-and-Process-Calculus|Link1]], [[Concurrent-and-Distributed-Algol|Link2]]
- **50.2 Strong Equivalence** — *process relation* and *event relation*, *strong bisimulation*, *strong equivalence* ($\approx$), *proof by coinduction*, congruence lemmas (variables vs classes), strong equivalence is a congruence.
- **50.3 Weak Equivalence** — *weak bisimulation* abstracting silent actions ($\varepsilon$), *weak equivalence* ($\sim$), matching transitions up to silent steps, congruence. : [[Equational-Reasoning|Link]]

**Key Questions:**
1. Why is process equivalence based on interaction potential rather than outcomes?
2. How does weak equivalence differ from strong equivalence in treating silent actions?
3. Why must classes be related schematically rather than by substitution, unlike variables?

---

### Appendix A: Finite Sets and Finite Functions (pp. 549–550)

**Summary:** Collects the background notions of discrete, countable, and finite sets and of finite (computable partial) functions used throughout the book. : [[Equational-Reasoning|Link]]

**Key Definitions & Concepts:**
- **Finite Sets and Finite Functions** — *discrete set* (decidable equality), *countable set* (bijection with $\omega$), *finite set* (bijection with an initial segment), *finite function* (computable partial function), *domain* ($\text{dom}(\varphi)$), *disjoint* finite functions, *empty finite function* ($\emptyset$), *singleton function* ($u \hookrightarrow v$), *combination* ($\varphi \otimes \psi$).

**Key Questions:**
1. Why are sets required to be discrete with decidable equality?
2. How is a finite function represented and combined?
