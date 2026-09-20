# A HoTT Approach to Computational Effects — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Computational Effects and Existing Models** : [[Computational-Effects-and-Existing-Models|Link]]
   - Computational effects as mutations of real-world state : [[Computational-Effects-and-Existing-Models|Link]]
   - Pure versus impure functional programming
   - Monads as programmable semicolons
   - Limitations of monads from a type-theoretic perspective
   - Algebraic effects and the separation of declaration from handling : [[Computational-Effects-and-Existing-Models|Link]]
   - Motivation for unifying a theory of effects with a theory of types
2. **Foundations of Homotopy Type Theory** : [[Foundations-of-Homotopy-Type-Theory|Link]]
   - Types as topological spaces : [[Type-Formers|Link]]
   - Judgments of typing and judgmental equality : [[Propositions-as-Types|Link]]
   - Universes and the cumulative hierarchy
   - Typical ambiguity
   - Function types and currying : [[Equivalence-and-Univalence|Link1]], [[Type-Formers|Link2]]
   - Constant functions and fibers
   - Totality and continuity of type-theoretic functions
3. **Type Formers** : [[Type-Formers|Link]]
   - Sum types as disjoint unions : [[Type-Formers|Link]]
   - Product types as ordered pairs : [[Type-Formers|Link]]
   - The empty type : [[Type-Formers|Link]]
   - The unit type : [[Type-Formers|Link]]
   - Constructing finite types from empty and unit types : [[Type-Formers|Link]]
   - Dependent types as type families : [[Type-Formers|Link]]
   - Dependent product types : [[Type-Formers|Link]]
   - Dependent sum types : [[Type-Formers|Link]]
4. **Propositions as Types** : [[Propositions-as-Types|Link]]
   - The Curry-Howard correspondence
   - Identity types and propositional equality : [[Propositions-as-Types|Link]]
   - Reflexivity and path induction
   - Propositions as contractible types : [[Propositions-as-Types|Link]]
   - Truncation of non-propositional types : [[Propositions-as-Types|Link]]
   - Encoding predicate logic (implication, negation, conjunction, disjunction, quantifiers) as types
5. **Equivalence and Univalence** : [[Equivalence-and-Univalence|Link]]
   - Homotopy between functions : [[Equivalence-and-Univalence|Link1]], [[Foundations-of-Homotopy-Type-Theory|Link2]]
   - Quasi-inverse and homotopy equivalence : [[Equivalence-and-Univalence|Link]]
   - Singleton types : [[Propositions-as-Types|Link]]
   - Fibers and the definition of equivalence : [[Equivalence-and-Univalence|Link]]
   - The Univalence Axiom
   - Sets as types identified only by reflexivity : [[Equivalence-and-Univalence|Link]]
6. **Models of Computation** : [[Models-of-Computation|Link]]
   - Formal languages and alphabets : [[Cardinality-and-Uncountability|Link1]], [[Models-of-Computation|Link2]]
   - Finite automata and regular languages
   - Pushdown automata and context-free languages
   - Non-determinism and computational power : [[Models-of-Computation|Link]]
   - Turing machines and decidable languages : [[Models-of-Computation|Link]]
   - Recursively enumerable languages
   - The halting problem
7. **Cardinality and Uncountability** : [[Cardinality-and-Uncountability|Link]]
   - Countable infinity
   - Bijections between infinite sets : [[Cardinality-and-Uncountability|Link]]
   - Cantor's diagonalization argument : [[Cardinality-and-Uncountability|Link]]
   - Uncountability of the power set of a countably infinite set
   - Existence of non-Turing-recognizable languages : [[Cardinality-and-Uncountability|Link]]
8. **Computation Within HoTT** : [[Computation-Within-HoTT|Link]]
   - Open problem of a computational interpretation of univalence
   - Reasoning about computation models internally to HoTT
   - Turing machines encoded as functions : [[Computation-Within-HoTT|Link]]
   - Encoding partiality with a sum type
   - Turing categories as an alternative categorical model
9. **The Coq Proof Assistant** : [[The-Coq-Proof-Assistant|Link]]
   - Inductive type definitions : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link1]], [[The-Coq-Proof-Assistant|Link2]]
   - The Set universe
   - Constructors and automatically generated induction principles
   - Basic proof commands (Theorem, Proof, reflexivity, intros, exact, Qed)
   - Record types for dependent sums : [[The-Coq-Proof-Assistant|Link]]
   - Function definitions via pattern matching : [[The-Coq-Proof-Assistant|Link]]
   - The HoTT library for Coq : [[The-Coq-Proof-Assistant|Link]]
10. **A Type-Theoretic Model of Actions and Effects** : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Referential transparency for effectful programs : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Definition of an action as bind, eval, and transform functions
    - The eval-bind identity law
    - Lifting ordinary functions to functions on effects : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - The Identity Action : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Interactive Input as an action : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Exception Handling as an action : [[A-Type-Theoretic-Model-of-Actions-and-Effects|Link]]
    - Safe-division example with exception transform

---
