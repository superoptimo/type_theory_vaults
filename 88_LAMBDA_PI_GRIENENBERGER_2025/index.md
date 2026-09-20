# Combining Computational Theories — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Interoperability of Proof Assistants** : [[Interoperability-of-Proof-Assistants|Link]]
   - Cross checking and comparing formal proofs across systems
   - Trust in proof assistant formalizations : [[Interoperability-of-Proof-Assistants|Link]]
   - Direct translations between proof assistants : [[Interoperability-of-Proof-Assistants|Link]]
   - Theory U as a common ground for embedding proof systems : [[Interoperability-of-Proof-Assistants|Link]]
   - Dedukti as a tool for interoperability

2. **Ecumenical Logics** : [[Ecumenical-Logics|Link]]
   - Intuitionistic versus classical natural deduction
   - Witness and disjunction properties : [[Ecumenical-Logics|Link1]], [[Proof-Normalization-in-Ecumenical-Logic|Link2]]
   - Design of the ecumenical system NE with indexed connectives
   - Statements and the embedding of formulas via double negation
   - Ecumenical entailment and externally classical judgments : [[Ecumenical-Logics|Link]]
   - Soundness and conservativity of NE with respect to NJ and NK : [[Ecumenical-Logics|Link]]
   - Consistency and non collapse of ecumenical fragments : [[Theory-U-and-Ecumenical-Fragments|Link1]], [[Ecumenical-Logics|Link2]]

3. **Deduction Modulo Theory** : [[Deduction-Modulo-Theory|Link]]
   - Congruences over terms and formulas : [[Deduction-Modulo-Theory|Link]]
   - Non confusing and decidable congruences : [[Deduction-Modulo-Theory|Link]]
   - Convergent rewrite systems as congruences : [[Deduction-Modulo-Theory|Link]]
   - Definition by equality versus definition by reduction : [[Deduction-Modulo-Theory|Link]]
   - Delta reduction for unfolding definitions : [[Deduction-Modulo-Theory|Link]]
   - Iota reduction for inductive recursors : [[Deduction-Modulo-Theory|Link]]
   - Higher order rewrite rules : [[Deduction-Modulo-Theory|Link]]
   - Well typedness of a computational theory : [[Deduction-Modulo-Theory|Link]]

4. **Proof Normalization in Ecumenical Logic** : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
   - Cut elimination for ecumenical natural deduction : [[Higher-Order-Ecumenical-Type-Theory|Link1]], [[Theory-U-and-Ecumenical-Fragments|Link2]], [[Proof-Normalization-in-Ecumenical-Logic|Link3]]
   - Reducibility candidates and strong normalization : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
   - Simple cuts versus n cuts and commuting eliminations
   - Subject reduction under index constraints
   - The exchange construction for fake cuts : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
   - Pre models of a congruence as a normalization hypothesis
   - Ecumenical witness and disjunction properties for normal proofs : [[Proof-Normalization-in-Ecumenical-Logic|Link]]

5. **Higher-Order Ecumenical Type Theory** : [[Higher-Order-Ecumenical-Type-Theory|Link]]
   - Ecumenical simple type theory as a first order computational theory : [[Deduction-Modulo-Theory|Link1]], [[Higher-Order-Ecumenical-Type-Theory|Link2]]
   - Encoding lambda terms with combinators and an application symbol
   - Separating propositional contents from propositions via a truth predicate
   - Soundness and conservativity of ecumenical simple type theory : [[Ecumenical-Logics|Link1]], [[Higher-Order-Ecumenical-Type-Theory|Link2]], [[Theory-U-and-Ecumenical-Fragments|Link3]]
   - Confluence and termination of the ecumenical rewrite system : [[Higher-Order-Ecumenical-Type-Theory|Link]]

6. **Pure Type Systems** : [[Pure-Type-Systems|Link]]
   - Definition of a pure type system as sorts axioms and rules : [[Pure-Type-Systems|Link]]
   - Barendregt's lambda cube : [[Pure-Type-Systems|Link]]
   - Syntax of terms free and bound variables and substitution : [[Pure-Type-Systems|Link]]
   - Alpha equivalence : [[Pure-Type-Systems|Link]]
   - Beta reduction as computation in pure type systems : [[Proof-Normalization-in-Ecumenical-Logic|Link1]], [[Pure-Type-Systems|Link2]]
   - Confluence normalization and strong normalization of rewrite relations : [[Higher-Order-Ecumenical-Type-Theory|Link]]
   - Nontermination of untyped beta reduction and Girard's paradox : [[Pure-Type-Systems|Link]]
   - Typing rules and the conversion rule : [[Pure-Type-Systems|Link]]
   - Product injectivity subject reduction and uniqueness of types : [[Pure-Type-Systems|Link]]
   - Undecidability of type checking and type reconstruction : [[Theory-U-and-Ecumenical-Fragments|Link]]
   - Universe hierarchies for normalizing type systems : [[Proof-Normalization-in-Ecumenical-Logic|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]

7. **The Lambda-Pi-Calculus Modulo Theory** : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - The Edinburgh Logical Framework as an ancestor of $\lambda\Pi$ : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Dedukti as a $\lambda\Pi$ type checker : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Dedukti concrete syntax for declarations definitions and rewrite rules
   - Shallow versus deep encodings of formal systems : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Encoding minimal predicate logic by formulae as types : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Encoding propositions as objects via a proof embedding
   - Encoding arbitrary pure type systems via universes and decoding functions : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]

8. **Modularity of Type Theories** : [[Modularity-of-Type-Theories|Link]]
   - Theory contexts as incremental definitions : [[Modularity-of-Type-Theories|Link]]
   - Strongly well formed theory contexts : [[Modularity-of-Type-Theories|Link]]
   - Weakly well formed theory contexts : [[Modularity-of-Type-Theories|Link]]
   - Non modularity of theory unions and extensions : [[Modularity-of-Type-Theories|Link]]
   - Constraint generation and presolutions for rewrite rules : [[Modularity-of-Type-Theories|Link1]], [[Deduction-Modulo-Theory|Link2]]
   - Safe theory extensions : [[Modularity-of-Type-Theories|Link]]

9. **Theory Fragmentation** : [[Theory-Fragmentation|Link]]
   - Dependency and fragments of a theory : [[Theory-Fragmentation|Link]]
   - The fragment theorem : [[Theory-Fragmentation|Link]]
   - Weakening the hypotheses of the fragment theorem : [[Theory-Fragmentation|Link]]
   - Fragments of strongly and weakly well formed theories : [[Theory-Fragmentation|Link]]
   - Type inference under fragmentation : [[Theory-Fragmentation|Link]]
   - Finding a presolution in a fragment : [[Theory-Fragmentation|Link]]

10. **Theory U and Ecumenical Fragments** : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Shallow encoding of ecumenical simple type theory in Dedukti : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Super consistency and $\Pi$-algebra models : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Normalization and decidability of type checking for ecumenical STT : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Soundness and conservativity with respect to first order logic : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Soundness and conservativity with respect to higher order logic : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Consistency of ecumenical simple type theory : [[Theory-U-and-Ecumenical-Fragments|Link]]

---
