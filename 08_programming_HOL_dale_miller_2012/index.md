# Programming with Higher-Order Logic — Index

[[book-guidelines|↩ Back to guidelines]]

1. **[[Logic-Programming-as-Proof-Search|Logic Programming as Proof Search]]**
   - Computation-as-model versus computation-as-deduction
   - [[The-Simply-Typed-Lambda-Calculus|Proof normalization versus proof search as computational paradigms]]
   - [[Logic-Programming-as-Proof-Search|Sequents as the unit of computational state]]
   - [[Logic-Programming-as-Proof-Search|Goal-directed search and the fixed search semantics of logical connectives]]
   - [[Logic-Programming-as-Proof-Search|Backchaining against program clauses]]
   - The cut rule and Gentzen's cut-elimination theorem
   - [[Logic-Programming-as-Proof-Search|Uniform proofs and abstract logic programming languages]]
   - [[Implementing-Proof-Systems|Focused proof systems]]

2. **[[Typed-First-Order-Terms-and-Type-Structure|Typed First-Order Terms and Type Structure]]**
   - [[Typed-First-Order-Terms-and-Type-Structure|Sorts, type constructors, and kinds]]
   - [[Typed-First-Order-Terms-and-Type-Structure|Type expressions, target and argument types]]
   - [[Typed-First-Order-Terms-and-Type-Structure|The order of a type]]
   - [[Typed-First-Order-Terms-and-Type-Structure|Typed first-order terms and the type assignment calculus]]
   - Polymorphic and pervasive constants
   - [[Typed-First-Order-Terms-and-Type-Structure|Parametric versus nonparametric polymorphism]]
   - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Representing structured data with value constructors]]
   - Representing linguistic objects such as formulas and imperative programs
   - Type declarations and operator declarations in $\lambda$Prolog

3. **[[First-Order-Unification|First-Order Unification]]**
   - [[First-Order-Unification|Unification problems as multisets of equations]]
   - [[First-Order-Unification|Most general unifiers and solved form]]
   - [[First-Order-Unification|Rigid terms and the term-reduction, reorientation, and variable-elimination transformations]]
   - The occurs-check and constant clashes
   - [[First-Order-Unification|Unification problems read as quantified formulas]]

4. **[[First-Order-Horn-Clause-Logic-Programming|First-Order Horn Clause Logic Programming]]**
   - The fohc language of definite goals and clauses
   - Signatures, programs, and goals as sequent components
   - [[First-Order-Horn-Clause-Logic-Programming|Right-introduction and left-introduction proof rules]]
   - [[First-Order-Horn-Clause-Logic-Programming|Answer substitutions]]
   - [[First-Order-Horn-Clause-Logic-Programming|Completeness of fohc for classical and intuitionistic logic]]
   - Predicate-indexed clauses and the Warren Abstract Machine
   - [[First-Order-Horn-Clause-Logic-Programming|The operational role of types beyond static well-formedness]]
   - [[First-Order-Unification|Determinate and transparent types]]

5. **[[Hereditary-Harrop-Formulas-and-Modular-Search|Hereditary Harrop Formulas and Modular Search]]**
   - The fohh language admitting implications and universal quantifiers in goals
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|The disjunction and existential property of hereditary Harrop formulas]]
   - [[Logic-Programming-as-Proof-Search|Program and signature augmentation during proof search]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Hypothetical reasoning via implicational goals]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Eigenvariables and the generic reading of universal goals]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Minimal logic, intuitionistic logic, and ex falso quodlibet]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Open-world versus closed-world assumption]]
   - [[Hereditary-Harrop-Formulas-and-Modular-Search|Scope extrusion and the failure of fohh under classical logic]]

6. **[[The-Simply-Typed-Lambda-Calculus|The Simply Typed $\lambda$-Calculus]]**
   - [[The-Simply-Typed-Lambda-Calculus|Abstraction, application, and the type assignment calculus for $\lambda$-terms]]
   - [[The-Simply-Typed-Lambda-Calculus|$\alpha$-, $\beta$-, and $\eta$-conversion]]
   - [[The-Simply-Typed-Lambda-Calculus|$\beta$-normal form and $\lambda$-normal form]]
   - Church numerals and the complexity of $\beta$-normalization
   - [[The-Simply-Typed-Lambda-Calculus|Quantifiers as abstractions over formulas of type $o$]]

7. **[[Higher-Order-Unification|Higher-Order Unification]]**
   - [[First-Order-Unification|Unification problems as quantified equalities with mixed quantifier prefixes]]
   - Raising as the dual of Skolemization
   - Unifiers versus solutions under nonempty-domain assumptions
   - [[Higher-Order-Unification|Rigid and flexible terms, and the classification of equations]]
   - Undecidability via Post correspondence and Hilbert's Tenth Problem
   - [[Higher-Order-Unification|Huet's pre-unification procedure and matching trees]]
   - Imitation and projection substitutions
   - Absence of most general unifiers and of finite complete sets of unifiers
   - The $L_\lambda$ pattern subset and its decidable, unitary unification

8. **[[Higher-Order-Logic-Programming-Languages|Higher-Order Logic Programming Languages]]**
   - hohc, hohh, and hohh$^+$ as higher-order extensions of fohc and fohh
   - [[Higher-Order-Logic-Programming-Languages|Rigid versus flexible atoms and the restriction on clause heads]]
   - The Herbrand universe for higher-order programs
   - Predicate-name hiding via essentially universal clause heads
   - Flexible goals and strategies for handling them
   - [[Higher-Order-Logic-Programming-Languages|Defining logical constants and negation-as-failure within the language]]
   - [[Higher-Order-Logic-Programming-Languages|Functions represented as $\lambda$-terms and functional difference lists]]
   - [[Higher-Order-Logic-Programming-Languages|Limits of higher-order unification as a general-purpose programming tool]]
   - [[Higher-Order-Logic-Programming-Languages|Comparison with higher-order functional programming]]

9. **[[Modular-Program-Structuring|Modular Program Structuring]]**
   - [[Modular-Program-Structuring|Modules and signatures as $\lambda$Prolog's units of structuring]]
   - [[Modular-Program-Structuring|Accumulation of modules and of signatures]]
   - [[Modular-Program-Structuring|Signature elaboration and module well-formedness]]
   - [[Modular-Program-Structuring|E-formulas and existential quantification over program clauses]]
   - Static scoping of hidden constants and the module query interpretation
   - Abstract datatypes and code extensibility through modules
   - Module parametrization by accumulated signatures
   - Resolution of the call/1 ambiguity through logical module semantics

10. **[[Lambda-Tree-Syntax-and-Computation-over-Binders|$\lambda$-Tree Syntax and Computation over Binders]]**
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Representing binding structure via second-order constants paired with abstraction]]
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Object-level substitution realized as meta-level $\beta$-conversion]]
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Mobility of binders across term, formula, and proof level]]
    - Eigenvariable-based recursion under a binder
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Higher-order abstract syntax versus $\lambda$-tree syntax]]
    - De Bruijn representations and their translation
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|Signature-dependent copy clauses for substitution]]
    - The $L_\lambda$ subset as the computational core of $\lambda$-tree syntax programs

11. **[[Implementing-Proof-Systems|Implementing Proof Systems]]**
    - [[Implementing-Proof-Systems|Loop-free reformulation of sequent calculus rules as decision procedures]]
    - [[Implementing-Proof-Systems|Natural deduction proof objects and the # typing-style relation]]
    - Hypothetical judgments and eigenvariable freshness in encoded rules
    - [[Implementing-Proof-Systems|A sequent calculus for classical logic and its zoned sequent structure]]
    - Iterative deepening for completeness under existential instantiation
    - [[Implementing-Proof-Systems|Goals, tactics, and tacticals as a theorem-proving architecture]]
    - [[Logic-Programming-as-Proof-Search|Invertible rules in proof search]]

12. **[[Computing-over-Functional-Programs|Computing over Functional Programs]]**
    - [[Typed-First-Order-Terms-and-Type-Structure|The miniFP language and its type-neutral, then type-restricted, representation]]
    - [[Computing-over-Functional-Programs|Big-step versus evaluation-context (small-step) specifications of evaluation]]
    - Fixpoint evaluation by unfolding
    - [[Computing-over-Functional-Programs|Intensional term equality versus structural program equality]]
    - [[Computing-over-Functional-Programs|Partial evaluation and mixed evaluation under a binder]]
    - [[Computing-over-Functional-Programs|Continuation-passing style transformation and administrative redexes]]

13. **[[Encoding-the-Pi-Calculus|Encoding the $\pi$-Calculus]]**
    - [[Lambda-Tree-Syntax-and-Computation-over-Binders|$\lambda$-tree syntax representation of process syntax and name binding]]
    - Free-action and bound-action one-step transition relations
    - [[Hereditary-Harrop-Formulas-and-Modular-Search|Declarative encoding of freshness and scope-extrusion side conditions]]
    - [[Higher-Order-Unification|Traces and the animation of process behavior]]
    - [[Encoding-the-Pi-Calculus|May-judgments versus must-judgments]]
    - The unsoundness of a naive simulation encoding
    - Encoding the call-by-name $\lambda$-calculus translation into the $\pi$-calculus

14. **[[The-Teyjus-Implementation|The Teyjus Implementation]]**
    - Compiler, emulator, linker, and disassembler toolchain
    - [[The-Teyjus-Implementation|The read-prove-print loop and type inference at the top level]]
    - Realizing the modules language through separate compilation
    - [[The-Teyjus-Implementation|exportdef and useonly module-interface disciplines]]
    - Built-in arithmetic, stream I/O, cut, and negation predicates
    - Deviations from the idealized language, including partial higher-order unification

---
