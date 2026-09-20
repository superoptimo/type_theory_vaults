# Programming with Higher-Order Logic — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Logic Programming as Proof Search** : [[Logic-Programming-as-Proof-Search|Link]]
   - Computation-as-model versus computation-as-deduction
   - Proof normalization versus proof search as computational paradigms : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Sequents as the unit of computational state : [[Logic-Programming-as-Proof-Search|Link]]
   - Goal-directed search and the fixed search semantics of logical connectives : [[Logic-Programming-as-Proof-Search|Link]]
   - Backchaining against program clauses : [[Logic-Programming-as-Proof-Search|Link]]
   - The cut rule and Gentzen's cut-elimination theorem
   - Uniform proofs and abstract logic programming languages : [[Logic-Programming-as-Proof-Search|Link]]
   - Focused proof systems : [[Implementing-Proof-Systems|Link]]

2. **Typed First-Order Terms and Type Structure** : [[Typed-First-Order-Terms-and-Type-Structure|Link]]
   - Sorts, type constructors, and kinds : [[Typed-First-Order-Terms-and-Type-Structure|Link]]
   - Type expressions, target and argument types : [[Typed-First-Order-Terms-and-Type-Structure|Link]]
   - The order of a type : [[Typed-First-Order-Terms-and-Type-Structure|Link]]
   - Typed first-order terms and the type assignment calculus : [[Typed-First-Order-Terms-and-Type-Structure|Link]]
   - Polymorphic and pervasive constants : [[Polymorphic-and-Pervasive-Constants|Link]]
   - Parametric versus nonparametric polymorphism : [[Typed-First-Order-Terms-and-Type-Structure|Link]]
   - Representing structured data with value constructors : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
   - Representing linguistic objects such as formulas and imperative programs
   - Type declarations and operator declarations in $\lambda$Prolog : [[Polymorphic-and-Pervasive-Constants|Link]]

3. **First-Order Unification** : [[First-Order-Unification|Link]]
   - Unification problems as multisets of equations : [[First-Order-Unification|Link]]
   - Most general unifiers and solved form : [[First-Order-Unification|Link]]
   - Rigid terms and the term-reduction, reorientation, and variable-elimination transformations : [[First-Order-Unification|Link]]
   - The occurs-check and constant clashes
   - Unification problems read as quantified formulas : [[First-Order-Unification|Link1]], [[Higher-Order-Unification|Link2]]

4. **First-Order Horn Clause Logic Programming** : [[First-Order-Horn-Clause-Logic-Programming|Link]]
   - The fohc language of definite goals and clauses
   - Signatures, programs, and goals as sequent components
   - Right-introduction and left-introduction proof rules : [[First-Order-Horn-Clause-Logic-Programming|Link]]
   - Answer substitutions : [[First-Order-Horn-Clause-Logic-Programming|Link]]
   - Completeness of fohc for classical and intuitionistic logic : [[First-Order-Horn-Clause-Logic-Programming|Link]]
   - Predicate-indexed clauses and the Warren Abstract Machine
   - The operational role of types beyond static well-formedness : [[First-Order-Horn-Clause-Logic-Programming|Link]]
   - Determinate and transparent types : [[First-Order-Unification|Link]]

5. **Hereditary Harrop Formulas and Modular Search** : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]
   - The fohh language admitting implications and universal quantifiers in goals
   - The disjunction and existential property of hereditary Harrop formulas : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]
   - Program and signature augmentation during proof search : [[Logic-Programming-as-Proof-Search|Link]]
   - Hypothetical reasoning via implicational goals : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]
   - Eigenvariables and the generic reading of universal goals : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]
   - Minimal logic, intuitionistic logic, and ex falso quodlibet : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]
   - Open-world versus closed-world assumption : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]
   - Scope extrusion and the failure of fohh under classical logic : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]

6. **The Simply Typed $\lambda$-Calculus** : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Abstraction, application, and the type assignment calculus for $\lambda$-terms : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - $\alpha$-, $\beta$-, and $\eta$-conversion : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - $\beta$-normal form and $\lambda$-normal form : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Church numerals and the complexity of $\beta$-normalization
   - Quantifiers as abstractions over formulas of type $o$ : [[The-Simply-Typed-Lambda-Calculus|Link]]

7. **Higher-Order Unification** : [[Higher-Order-Unification|Link]]
   - Unification problems as quantified equalities with mixed quantifier prefixes : [[First-Order-Unification|Link1]], [[Higher-Order-Unification|Link2]]
   - Raising as the dual of Skolemization
   - Unifiers versus solutions under nonempty-domain assumptions
   - Rigid and flexible terms, and the classification of equations : [[Higher-Order-Unification|Link]]
   - Undecidability via Post correspondence and Hilbert's Tenth Problem
   - Huet's pre-unification procedure and matching trees : [[Higher-Order-Unification|Link]]
   - Imitation and projection substitutions
   - Absence of most general unifiers and of finite complete sets of unifiers
   - The $L_\lambda$ pattern subset and its decidable, unitary unification

8. **Higher-Order Logic Programming Languages** : [[Higher-Order-Logic-Programming-Languages|Link]]
   - hohc, hohh, and hohh$^+$ as higher-order extensions of fohc and fohh
   - Rigid versus flexible atoms and the restriction on clause heads : [[Higher-Order-Logic-Programming-Languages|Link1]], [[Higher-Order-Unification|Link2]]
   - The Herbrand universe for higher-order programs
   - Predicate-name hiding via essentially universal clause heads
   - Flexible goals and strategies for handling them
   - Defining logical constants and negation-as-failure within the language : [[Higher-Order-Logic-Programming-Languages|Link]]
   - Functions represented as $\lambda$-terms and functional difference lists : [[Higher-Order-Logic-Programming-Languages|Link]]
   - Limits of higher-order unification as a general-purpose programming tool : [[Higher-Order-Logic-Programming-Languages|Link1]], [[Higher-Order-Unification|Link2]]
   - Comparison with higher-order functional programming : [[Higher-Order-Logic-Programming-Languages|Link1]], [[Computing-over-Functional-Programs|Link2]]

9. **Modular Program Structuring** : [[Modular-Program-Structuring|Link]]
   - Modules and signatures as $\lambda$Prolog's units of structuring : [[Modular-Program-Structuring|Link]]
   - Accumulation of modules and of signatures : [[Modular-Program-Structuring|Link]]
   - Signature elaboration and module well-formedness : [[Modular-Program-Structuring|Link]]
   - E-formulas and existential quantification over program clauses : [[Modular-Program-Structuring|Link]]
   - Static scoping of hidden constants and the module query interpretation
   - Abstract datatypes and code extensibility through modules
   - Module parametrization by accumulated signatures
   - Resolution of the call/1 ambiguity through logical module semantics

10. **$\lambda$-Tree Syntax and Computation over Binders** : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
    - Representing binding structure via second-order constants paired with abstraction : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
    - Object-level substitution realized as meta-level $\beta$-conversion : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
    - Mobility of binders across term, formula, and proof level : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
    - Eigenvariable-based recursion under a binder
    - Higher-order abstract syntax versus $\lambda$-tree syntax : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
    - De Bruijn representations and their translation
    - Signature-dependent copy clauses for substitution : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
    - The $L_\lambda$ subset as the computational core of $\lambda$-tree syntax programs

11. **Implementing Proof Systems** : [[Implementing-Proof-Systems|Link]]
    - Loop-free reformulation of sequent calculus rules as decision procedures : [[Implementing-Proof-Systems|Link]]
    - Natural deduction proof objects and the # typing-style relation : [[Implementing-Proof-Systems|Link]]
    - Hypothetical judgments and eigenvariable freshness in encoded rules
    - A sequent calculus for classical logic and its zoned sequent structure : [[Implementing-Proof-Systems|Link]]
    - Iterative deepening for completeness under existential instantiation
    - Goals, tactics, and tacticals as a theorem-proving architecture : [[Implementing-Proof-Systems|Link]]
    - Invertible rules in proof search : [[Logic-Programming-as-Proof-Search|Link]]

12. **Computing over Functional Programs** : [[Computing-over-Functional-Programs|Link]]
    - The miniFP language and its type-neutral, then type-restricted, representation : [[Typed-First-Order-Terms-and-Type-Structure|Link]]
    - Big-step versus evaluation-context (small-step) specifications of evaluation : [[Computing-over-Functional-Programs|Link]]
    - Fixpoint evaluation by unfolding
    - Intensional term equality versus structural program equality : [[Computing-over-Functional-Programs|Link]]
    - Partial evaluation and mixed evaluation under a binder : [[Computing-over-Functional-Programs|Link]]
    - Continuation-passing style transformation and administrative redexes : [[Computing-over-Functional-Programs|Link]]

13. **Encoding the $\pi$-Calculus** : [[Encoding-the-Pi-Calculus|Link]]
    - $\lambda$-tree syntax representation of process syntax and name binding : [[Lambda-Tree-Syntax-and-Computation-over-Binders|Link]]
    - Free-action and bound-action one-step transition relations
    - Declarative encoding of freshness and scope-extrusion side conditions : [[Hereditary-Harrop-Formulas-and-Modular-Search|Link]]
    - Traces and the animation of process behavior : [[Higher-Order-Unification|Link]]
    - May-judgments versus must-judgments : [[Encoding-the-Pi-Calculus|Link]]
    - The unsoundness of a naive simulation encoding
    - Encoding the call-by-name $\lambda$-calculus translation into the $\pi$-calculus

14. **The Teyjus Implementation** : [[The-Teyjus-Implementation|Link]]
    - Compiler, emulator, linker, and disassembler toolchain
    - The read-prove-print loop and type inference at the top level : [[The-Teyjus-Implementation|Link]]
    - Realizing the modules language through separate compilation
    - exportdef and useonly module-interface disciplines : [[The-Teyjus-Implementation|Link]]
    - Built-in arithmetic, stream I/O, cut, and negation predicates
    - Deviations from the idealized language, including partial higher-order unification

---
