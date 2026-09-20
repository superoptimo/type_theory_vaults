# Foundations of Logic Programming (2nd Edition) — Index

[[book-guidelines|↩ Back to guidelines]]

1. **First-Order Logic as a Foundation for Logic Programming** : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Alphabets, terms, and well-formed formulas : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Clausal form and clausal notation : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Interpretations, models, and logical consequence : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
   - Herbrand universes, Herbrand bases, and Herbrand interpretations
   - Prenex conjunctive normal form
   - Typed (many-sorted) first-order theories : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
2. **Unification** : [[Unification|Link]]
   - Substitutions and instances : [[Unification|Link]]
   - Composition of substitutions
   - Variants and renaming substitutions
   - Most general unifiers : [[Unification|Link]]
   - The unification algorithm and the occur check : [[Unification|Link]]
   - Worst-case exponential behaviour of unification
3. **Fixpoint Theory** : [[Fixpoint-Theory|Link]]
   - Partial orders and complete lattices
   - Monotonic and continuous mappings : [[Fixpoint-Theory|Link]]
   - Least and greatest fixpoints (Knaster–Tarski theorem)
   - Ordinal powers of a mapping
   - Kleene's characterisation of least fixpoints for continuous mappings
4. **Declarative Semantics of Definite Programs** : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Definite program clauses, definite programs, and definite goals
   - The least Herbrand model and the model intersection property : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - The immediate consequence operator $T_P$ : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Fixpoint characterisation of the least Herbrand model : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Correct answers : [[Declarative-Semantics-of-Definite-Programs|Link]]
5. **SLD-Resolution** : [[SLD-Resolution|Link]]
   - Resolvents, SLD-derivations, and SLD-refutations : [[SLD-Resolution|Link]]
   - Computed answers : [[SLD-Resolution|Link]]
   - Soundness of SLD-resolution : [[SLD-Resolution|Link]]
   - The mgu lemma and the lifting lemma
   - Completeness of SLD-resolution : [[SLD-Resolution|Link1]], [[Negation-in-Logic-Programs|Link2]]
   - Independence of the computation rule and the switching lemma : [[SLD-Resolution|Link]]
   - SLD-trees, search rules, and fairness
   - Depth-first search and incompleteness in practical PROLOG systems
   - Coroutining and automatic control generation
   - The cut control facility and safe versus unsafe cuts
6. **Computational Adequacy of Logic Programs** : [[Computational-Adequacy-of-Logic-Programs|Link]]
   - Encoding partial recursive functions as definite programs : [[Declarative-Semantics-of-Definite-Programs|Link]]
   - Composition, primitive recursion, and minimalisation as program schemas
7. **The Occur Check Problem** : [[The-Occur-Check-Problem|Link]]
   - Unsoundness of unification without the occur check : [[Integrity-Constraint-Checking|Link]]
   - Difference lists and circular bindings : [[The-Occur-Check-Problem|Link]]
   - Programming methodologies to contain occur-check errors
8. **Negation in Logic Programs** : [[Negation-in-Logic-Programs|Link]]
   - The closed world assumption
   - Non-monotonic inference rules : [[Negation-in-Logic-Programs|Link]]
   - The SLD finite failure set and its characterisations
   - Fair derivations and fair SLD-trees
   - The negation as failure rule : [[Negation-in-Logic-Programs|Link]]
   - Program completion and the equality theory : [[Negation-in-Logic-Programs|Link]]
   - Normal programs, normal goals, and program clauses with negative literals
   - Hierarchical and stratified programs
   - SLDNF-resolution and the safeness condition on literal selection
   - Floundering and the allowedness condition
   - Soundness and completeness of the negation as failure rule : [[Semantics-of-Perpetual-Processes|Link]]
   - Soundness and completeness of SLDNF-resolution for hierarchical programs : [[Negation-in-Logic-Programs|Link]]
   - Effect of cut on soundness in normal programs
9. **Programs and Goals with Arbitrary First-Order Bodies** : [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link]]
   - Program statements with arbitrary formula bodies : [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link]]
   - Completion of a program : [[Negation-in-Logic-Programs|Link1]], [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link2]]
   - Transformation of a program into normal form : [[Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Link]]
   - Soundness and completeness of the negation as failure rule and SLDNF-resolution for programs
10. **Declarative Error Diagnosis** : [[Declarative-Error-Diagnosis|Link]]
    - Intended interpretations and program correctness : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
    - Uncovered atoms and incorrect statement instances
    - The declarative error diagnoser (wrong and missing predicates) : [[Declarative-Error-Diagnosis|Link]]
    - The top-down version of the diagnoser and its use of an oracle
    - Comparison with single-stepping and divide-and-query algorithms
    - Soundness and completeness of the error diagnoser : [[Declarative-Error-Diagnosis|Link1]], [[Semantics-of-Perpetual-Processes|Link2]]
11. **Deductive Database Theory** : [[Deductive-Database-Theory|Link]]
    - Database statements, databases, and queries
    - Typed first-order theories for database semantics
    - Integrity constraints and the model-theoretic versus proof-theoretic view : [[Deductive-Database-Theory|Link]]
    - Hierarchical and stratified databases : [[Negation-in-Logic-Programs|Link]]
    - Transformation of typed formulas into type-free form
    - Soundness and completeness of query evaluation : [[Deductive-Database-Theory|Link]]
    - Domain closure axioms : [[Deductive-Database-Theory|Link]]
12. **Integrity Constraint Checking** : [[Integrity-Constraint-Checking|Link]]
    - Transactions as sequences of additions and deletions
    - The simplification theorem for integrity constraint checking : [[Integrity-Constraint-Checking|Link]]
    - Computing the atom sets that capture model differences
    - Stopping rules for practical implementation
13. **Semantics of Perpetual Processes** : [[Semantics-of-Perpetual-Processes|Link]]
    - Possibly-infinite terms and atoms as labelled trees : [[Semantics-of-Perpetual-Processes|Link]]
    - The complete Herbrand universe and complete Herbrand base : [[First-Order-Logic-as-a-Foundation-for-Logic-Programming|Link]]
    - Compactness under the ultrametric on terms
    - The mapping $T'_P$ on complete Herbrand interpretations
    - Closedness and weak continuity of $T'_P$
    - Atoms computable at infinity : [[Semantics-of-Perpetual-Processes|Link]]
    - Soundness of SLD-resolution for perpetual processes : [[Semantics-of-Perpetual-Processes|Link1]], [[SLD-Resolution|Link2]]

---
