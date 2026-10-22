# A Focused Sequent Calculus Framework for Proof-Search in Pure Type Systems — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Pure Type Systems and the Lambda Cube** : [[Pure-Type-Systems-and-the-Lambda-Cube|Link]]
   - Sorts, axioms and rules
   - Systems F, F$\omega$, $\lambda\Pi$ and the Calculus of Constructions
   - Natural deduction presentation : [[Pure-Type-Systems-and-the-Lambda-Cube|Link]]
   - Strong normalisation of a PTS : [[Pure-Type-Systems-and-the-Lambda-Cube|Link]]
2. **Focused Sequent Calculus and Permutation-Free Proof-Search** : [[Focused-Sequent-Calculus-and-Permutation-Free-Proof-Search|Link]]
   - Herbelin's calculus LJT : [[Focused-Sequent-Calculus-and-Permutation-Free-Proof-Search|Link]]
   - Gentzen-style calculi such as G3
   - Focusing and the stoup
   - Uniform proofs and goal-directed search
   - Don't-care versus don't-know non-determinism : [[Proof-Search-System-PS|Link1]], [[Focused-Sequent-Calculus-and-Permutation-Free-Proof-Search|Link2]]
3. **Pure Type Sequent Calculi** : [[Pure-Type-Sequent-Calculi|Link]]
   - Terms and lists
   - Explicit substitutions
   - Sequent typing rules including left and right introduction of $\Pi$
   - Cut rules and environment manipulation
   - Conversion rules for term and list typing
4. **Operational Semantics and Confluence** : [[Operational-Semantics-and-Confluence|Link]]
   - Rewrite systems B and x$'$ : [[Operational-Semantics-and-Confluence|Link1]], [[Pure-Type-Systems-and-the-Lambda-Cube|Link2]], [[Proof-Search-System-PS|Link3]]
   - Termination of x$'$ by lexicographic path ordering
   - Translations between sequent calculus and $\lambda$-terms
   - Confluence by simulation : [[Operational-Semantics-and-Confluence|Link]]
5. **Meta-Theory of PTSC** : [[Meta-Theory-of-PTSC|Link]]
   - Weakening and thinning
   - Subject reduction
   - Preservation of typing in both directions
   - Equivalence of strong normalisation with the PTS : [[Meta-Theory-of-PTSC|Link1]], [[Pure-Type-Systems-and-the-Lambda-Cube|Link2]]
6. **Proof-Search System PS** : [[Proof-Search-System-PS|Link]]
   - Syntax-directed rules with built-in conversion : [[Proof-Search-System-PS|Link]]
   - Quasi-normal forms
   - Soundness and completeness : [[Proof-Enumeration-System-PE|Link]]
   - Sources of non-determinism in search : [[Proof-Search-System-PS|Link]]
   - Relation to the constructive engine
7. **Meta-Variables and Partial Proof-Terms** : [[Meta-Variables-and-Partial-Proof-Terms|Link]]
   - Scoped meta-variables for terms and lists : [[Meta-Variables-and-Partial-Proof-Terms|Link1]], [[Operational-Semantics-and-Confluence|Link2]]
   - Meta-variables in the style of CRS versus ERS : [[Operational-Semantics-and-Confluence|Link1]], [[Meta-Variables-and-Partial-Proof-Terms|Link2]]
   - Goal environments with goals and constraints : [[Meta-Variables-and-Partial-Proof-Terms|Link]]
   - Substitutions and solutions
   - Meta-variables as higher-order variables
8. **Proof Enumeration System PE** : [[Proof-Enumeration-System-PE|Link]]
   - Claim rules and delayed sub-goals
   - Unification constraints from the axiom rule
   - Solving goals in any order
   - Soundness and completeness of PE : [[Proof-Enumeration-System-PE|Link]]
   - Avoiding $r$-splitting : [[Proof-Enumeration-System-PE|Link]]
9. **Unification and Type Inhabitation** : [[Unification-and-Type-Inhabitation|Link]]
   - Proof-search and unification as a single process : [[Proof-Search-System-PS|Link1]], [[Proof-Enumeration-System-PE|Link2]]
   - Higher-order unification
   - Type inhabitant enumeration : [[Meta-Theory-of-PTSC|Link1]], [[Unification-and-Type-Inhabitation|Link2]]
   - Comparison with Dowek and Muñoz : [[Meta-Variables-and-Partial-Proof-Terms|Link]]
10. **Proof-Search Strategies and Tactics** : [[Proof-Search-Strategies-and-Tactics|Link]]
    - Eager and lazy treatment of sub-goals
    - Coq tactics intro and apply
    - Interactive proof construction
    - Incomplete proofs in the work of McBride, Jojgov and Delahaye
11. **Worked Example in System F** : [[Worked-Example-in-System-F|Link]]
    - Commutativity of conjunction
    - Head-variable choice from constraints : [[Unification-and-Type-Inhabitation|Link]]

---
