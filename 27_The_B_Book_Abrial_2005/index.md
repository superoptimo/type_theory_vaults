# The B-Book: Assigning Programs to Meanings — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Formal Proof and Predicate Logic** : [[Formal-Proof-and-Predicate-Logic|Link]]
   - Sequents and rules of inference : [[Formal-Proof-and-Predicate-Logic|Link]]
   - Propositional calculus proof procedure : [[Formal-Proof-and-Predicate-Logic|Link]]
   - Predicate calculus and quantification : [[Formal-Proof-and-Predicate-Logic|Link]]
   - Non-freeness and variable capture : [[Formal-Proof-and-Predicate-Logic|Link]]
   - Substitution and the one point rule : [[Formal-Proof-and-Predicate-Logic|Link]]
   - Equality and the Leibnitz law : [[Formal-Proof-and-Predicate-Logic|Link]]
   - Ordered pairs and multiple quantification : [[Formal-Proof-and-Predicate-Logic|Link]]

2. **Set Theory and the Relational Calculus** : [[Set-Theory-and-the-Relational-Calculus|Link]]
   - Cartesian product power set and comprehension as primitives
   - A simplified non-ZF axiomatization of sets
   - Type-checking as a decision procedure
   - The empty set relative to a super-set : [[Set-Theory-and-the-Relational-Calculus|Link]]
   - Binary relations and the relational calculus : [[Set-Theory-and-the-Relational-Calculus|Link]]
   - Domain and range restriction and subtraction : [[Fixpoint-Construction-and-Induction|Link]]
   - Function types and functional abstraction : [[Implementation-and-Modular-Architecture|Link1]], [[Set-Theory-and-the-Relational-Calculus|Link2]]

3. **Fixpoint Construction and Induction** : [[Fixpoint-Construction-and-Induction|Link]]
   - The Knaster-Tarski fixpoint theorem : [[Fixpoint-Construction-and-Induction|Link]]
   - Induction principle derived from least fixpoints : [[Sequencing-Loops-and-Termination-Proofs|Link1]], [[Fixpoint-Construction-and-Induction|Link2]]
   - Finite subsets and finite versus infinite sets : [[Fixpoint-Construction-and-Induction|Link]]
   - Construction of natural numbers and the Peano axioms : [[Fixpoint-Construction-and-Induction|Link]]
   - Strong induction and well-ordering : [[Fixpoint-Construction-and-Induction|Link]]
   - Recursive function definition on natural numbers : [[Fixpoint-Construction-and-Induction|Link1]], [[Algorithm-Construction-Methodology|Link2]]
   - Finite sequences and trees and their induction principles : [[Fixpoint-Construction-and-Induction|Link]]
   - Well-founded relations as a unifying framework : [[Fixpoint-Construction-and-Induction|Link]]

4. **Abstract Machines and the Generalized Substitution Language** : [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link]]
   - Abstract machines as state plus operations : [[Refinement-Theory|Link]]
   - The hiding principle : [[Algorithm-Construction-Methodology|Link]]
   - Before-after predicates as operation specifications : [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link1]], [[Semantics-of-Generalized-Substitutions|Link2]], [[Case-Studies-in-Specification|Link3]]
   - Generalized substitutions and weakest precondition style : [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link]]
   - Pre-conditioned and guarded substitution : [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link]]
   - Bounded and unbounded choice substitution : [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link]]
   - Generous versus defensive specification style : [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link]]
   - Machine parameterization constraints and initialization : [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link1]], [[Set-Theory-and-the-Relational-Calculus|Link2]]
   - Deferred and enumerated sets
   - Proof obligations for abstract machines : [[Case-Studies-in-Refinement|Link1]], [[Refinement-Theory|Link2]]

5. **Semantics of Generalized Substitutions** : [[Semantics-of-Generalized-Substitutions|Link]]
   - Dijkstra's healthiness conditions
   - The normalized form theorem : [[Semantics-of-Generalized-Substitutions|Link]]
   - Termination feasibility and before-after characterization : [[Semantics-of-Generalized-Substitutions|Link1]], [[Sequencing-Loops-and-Termination-Proofs|Link2]]
   - Set-theoretic models of a substitution : [[Semantics-of-Generalized-Substitutions|Link]]
   - The set transformer model : [[Semantics-of-Generalized-Substitutions|Link]]

6. **Composing Large Specifications** : [[Composing-Large-Specifications|Link]]
   - Multiple generalized substitution and its algebra : [[Semantics-of-Generalized-Substitutions|Link1]], [[Composing-Large-Specifications|Link2]], [[Abstract-Machines-and-the-Generalized-Substitution-Language|Link3]], [[Sequencing-Loops-and-Termination-Proofs|Link4]]
   - The INCLUDES clause and incremental specification : [[Composing-Large-Specifications|Link]]
   - The USES clause and read-only sharing : [[Composing-Large-Specifications|Link]]
   - The PROMOTES and EXTENDS clauses : [[Composing-Large-Specifications|Link]]
   - Machine signatures and visibility rules
   - Operation calls as substitution on substitutions : [[Composing-Large-Specifications|Link]]

7. **Case Studies in Specification** : [[Case-Studies-in-Specification|Link]]
   - Layered machine construction in the invoice system : [[Case-Studies-in-Specification|Link]]
   - Modeling concurrent systems as event machines : [[Case-Studies-in-Specification|Link]]
   - The lift control liveness problem : [[Case-Studies-in-Specification|Link]]
   - Liveness properties as refinement obligations : [[Case-Studies-in-Specification|Link]]

8. **Sequencing Loops and Termination Proofs** : [[Sequencing-Loops-and-Termination-Proofs|Link]]
   - Sequencing of generalized substitutions : [[Sequencing-Loops-and-Termination-Proofs|Link]]
   - The loop operator as a substitution fixpoint : [[Sequencing-Loops-and-Termination-Proofs|Link]]
   - Termination as a well-founded stability condition : [[Sequencing-Loops-and-Termination-Proofs|Link]]
   - The invariant theorem : [[Sequencing-Loops-and-Termination-Proofs|Link]]
   - The variant theorem and abstraction relations : [[Sequencing-Loops-and-Termination-Proofs|Link]]
   - Traditional while loop proof rules : [[Sequencing-Loops-and-Termination-Proofs|Link]]

9. **Algorithm Construction Methodology** : [[Algorithm-Construction-Methodology|Link]]
   - Re-use of proved algorithms via pre-condition checked calls : [[Algorithm-Construction-Methodology|Link]]
   - Unbounded and bounded search for a minimum : [[Algorithm-Construction-Methodology|Link]]
   - Binary search and the role of monotonicity : [[Algorithm-Construction-Methodology|Link]]
   - Recursive schemes on natural numbers sequences and trees : [[Algorithm-Construction-Methodology|Link]]
   - Fast exponentiation by repeated squaring : [[Algorithm-Construction-Methodology|Link]]
   - Filters and filter-pipes : [[Algorithm-Construction-Methodology|Link]]
   - Parsing as rewriting over a well-founded relation : [[Algorithm-Construction-Methodology|Link]]

10. **Refinement Theory** : [[Refinement-Theory|Link]]
    - The refinement relation and its partial order : [[Refinement-Theory|Link]]
    - Refining a generalized assignment : [[Refinement-Theory|Link]]
    - Abstract machine refinement via a gluing relation : [[Refinement-Theory|Link]]
    - Sufficient refinement conditions via pre and rel : [[Refinement-Theory|Link]]
    - Refinement proof obligations : [[Refinement-Theory|Link]]

11. **Implementation and Modular Architecture** : [[Implementation-and-Modular-Architecture|Link]]
    - The IMPLEMENTATION construct : [[Implementation-and-Modular-Architecture|Link]]
    - The IMPORTS clause and importation
    - The VALUES clause and acyclic constant valuation : [[Implementation-and-Modular-Architecture|Link]]
    - Comparing IMPORTS INCLUDES and SEES : [[Implementation-and-Modular-Architecture|Link]]
    - Recursively defined operations : [[Implementation-and-Modular-Architecture|Link]]
    - Multiple refinement of several abstractions : [[Implementation-and-Modular-Architecture|Link]]

12. **Case Studies in Refinement** : [[Case-Studies-in-Refinement|Link]]
    - A library of basic hardware abstraction machines : [[Case-Studies-in-Refinement|Link]]
    - The layered data-base system development : [[Case-Studies-in-Refinement|Link]]
    - Backward refinement in the boiler control system : [[Case-Studies-in-Refinement|Link]]
    - System analysis and synthesis for reactive systems
    - Architectural resilience to specification changes : [[Case-Studies-in-Refinement|Link]]

---
