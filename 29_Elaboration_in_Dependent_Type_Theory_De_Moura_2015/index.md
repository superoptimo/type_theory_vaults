# Elaboration in Dependent Type Theory — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The Elaboration Task** : [[The-Elaboration-Task|Link]]
   - Elaboration as passing from a partial expression to a fully specified term
   - Type inference and implicit arguments
   - Placeholders and underscore-inferred arguments
   - Generalizing Hindley–Milner type inference to dependent types
2. **Higher-Order Unification** : [[Higher-Order-Unification|Link]]
   - First-order vs. higher-order unification problems in implicit argument synthesis
   - Undecidability of second-order unification : [[Higher-Order-Unification|Link]]
   - Inferring substitution contexts and induction predicates
   - Miller patterns : [[Higher-Order-Unification|Link]]
   - Huet's unification algorithm : [[Higher-Order-Unification|Link]]
   - Imitation and projection case splits
   - Quasi-patterns and reduced case-split search
3. **Computational Behavior and Reduction** : [[Computational-Behavior-and-Reduction|Link]]
   - Definitional equality and $\beta$/$\iota$-reduction : [[Computational-Behavior-and-Reduction|Link]]
   - Weak head normal form and stuck terms : [[Computational-Behavior-and-Reduction|Link]]
   - Unfolding of defined constants during elaboration
   - Reducibility annotations: irreducible, reducible, semireducible
   - Definition depth and delta-constraint unfolding heuristics
4. **Type Classes and Class Inference** : [[Type-Classes-and-Class-Inference|Link]]
   - Haskell-style type classes in a dependently typed setting
   - Instance declarations and backward-chaining Prolog-like search
   - The algebraic hierarchy via structure extension
   - Fully bundled structures and coercion-based projection : [[Type-Classes-and-Class-Inference|Link]]
   - The decidable class and constructive/classical interplay
   - Ondemand choice constraints for class resolution : [[Constraints-and-Justifications|Link1]], [[Tactics-and-Proof-Structuring|Link2]]
5. **Overloading and Coercions** : [[Overloading-and-Coercions|Link]]
   - Ad hoc polymorphism versus parametric polymorphism
   - Notation and identifier overloading across namespaces
   - Namespace disambiguation
   - Coercion between families of types : [[Overloading-and-Coercions|Link]]
   - Coercion to the class of sorts
   - Coercion to the class of function types : [[Overloading-and-Coercions|Link]]
6. **Tactics and Proof Structuring** : [[Tactics-and-Proof-Structuring|Link]]
   - Tactic blocks interleaved with term-mode expressions
   - The have and show structuring keywords : [[Tactics-and-Proof-Structuring|Link]]
   - Local surgical tactics versus global constraint-based elaboration
   - Sectioning long proof terms into independent elaboration problems
7. **Term Representation and Core Data Structures** : [[Term-Representation-and-Core-Data-Structures|Link]]
   - Locally nameless variable representation : [[Term-Representation-and-Core-Data-Structures|Link]]
   - De Bruijn indices for bound variables
   - Metavariables as holes with unique identifiers and types
   - Closed-term-only metavariable assignment : [[Term-Representation-and-Core-Data-Structures|Link]]
   - Environments, declarations, and constants : [[Term-Representation-and-Core-Data-Structures|Link]]
8. **Constraints and Justifications** : [[Constraints-and-Justifications|Link]]
   - Unification constraints versus choice constraints
   - Asserted, assumption, and join justifications : [[Constraints-and-Justifications|Link]]
   - Substitutions as metavariable assignments with justification tracking : [[Constraints-and-Justifications|Link]]
   - Regular versus ondemand choice constraints : [[Constraints-and-Justifications|Link]]
9. **The Constraint Simplification Procedure** : [[The-Constraint-Simplification-Procedure|Link]]
   - The simp procedure for decomposing unification constraints
   - Constraint categories: delta, pattern, quasi-pattern, flex-rigid, flex-flex, recursor : [[Higher-Order-Unification|Link]]
   - Symmetric case elision in the simp pseudocode
10. **The Preprocessing Phase** : [[The-Preprocessing-Phase|Link]]
    - Converting preterms to terms with metavariables and constraints
    - ensurefun and function-type inference
    - Coercion insertion during application elaboration
    - Implicit-argument metavariable creation
11. **The Constraint Solving Procedure** : [[The-Constraint-Solving-Procedure|Link]]
    - Priority queue ordering over constraint categories : [[The-Constraint-Solving-Procedure|Link]]
    - The metavariable-to-constraint mapping U
    - Nonchronological backtracking and case-split stacks : [[The-Constraint-Solving-Procedure|Link]]
    - Pure data structures for constant-time state copies
    - The visit, resolve, and process procedures : [[The-Constraint-Solving-Procedure|Link]]
12. **Performance and Implementation Optimizations** : [[Performance-and-Implementation-Optimizations|Link]]
    - Cost of the locally nameless approach
    - Bound tracking to optimize instantiate
    - Free-variable bits to optimize abstract
    - Compilation time comparison with and without optimizations
13. **Related Work and Positioning** : [[Related-Work-and-Positioning|Link]]
    - Miller-style pattern unification and pruning : [[Higher-Order-Unification|Link]]
    - Dependency erasure and first-order approximation in Coq's unifier
    - Type classes and canonical structures in Coq and Matita : [[Related-Work-and-Positioning|Link]]
    - Axiomatic type classes and locales in Isabelle : [[Related-Work-and-Positioning|Link1]], [[Type-Classes-and-Class-Inference|Link2]]
    - Elaboration via theorem-proving analogy in Idris : [[Related-Work-and-Positioning|Link]]

---
