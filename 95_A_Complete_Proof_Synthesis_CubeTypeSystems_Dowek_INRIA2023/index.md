# A Complete Proof Synthesis Method for the Cube of Type Systems — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Proofs-as-Objects and Proof Synthesis** : [[Proofs-as-Objects-and-Proof-Synthesis|Link]]
   - Proofs as terms through Heyting semantics and the Curry–Howard isomorphism
   - Proof synthesis as finding an inhabitant of a type
   - Heterogeneous proof trees versus a single syntactic category
   - Proof synthesis as a semi-decision procedure : [[Proofs-as-Objects-and-Proof-Synthesis|Link]]
2. **Pure Type Systems and Barendregt's Cube** : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - Sorts, axioms and rules
   - Functional type systems : [[Unification-in-Type-Systems|Link]]
   - The eight systems of the cube : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - Typing judgments and the conversion rule : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - $\beta\eta$-conversion and normalization
   - Normal $\eta$-long forms : [[Pure-Type-Systems-and-Barendregts-Cube|Link]]
   - Atomic terms and head variables
   - Calculus of Constructions with universes and without cumulativity
3. **Contexts, Quantifiers and Constraints** : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Constrained quantified contexts : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Miller's mixed prefixes
   - Equivalence modulo constraints : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Well-typedness without using the constraints : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Rigid and flexible terms : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Success and failure contexts : [[Contexts-Quantifiers-and-Constraints|Link]]
4. **Meta Type System and Existential Variables** : [[Meta-Type-System-and-Existential-Variables|Link]]
   - Embedding a cube system in the Meta type system : [[Meta-Type-System-and-Existential-Variables|Link1]], [[Pure-Type-Systems-and-Barendregts-Cube|Link2]]
   - Variables standing for arbitrary well-typed terms
   - Existential variables as metavariables with dependency on the local context : [[Meta-Type-System-and-Existential-Variables|Link]]
5. **Substitutions Under Quantified Contexts** : [[Substitutions-Under-Quantified-Contexts|Link]]
   - Substitutions carrying an existential context : [[Substitutions-Under-Quantified-Contexts|Link]]
   - Applying and composing substitutions
   - Well-typed substitutions : [[Soundness-and-Completeness|Link]]
   - Preservation of typing under substitution : [[Substitutions-Under-Quantified-Contexts|Link]]
6. **Higher-Order Unification and Resolution** : [[Higher-Order-Unification-and-Resolution|Link]]
   - Huet's enumeration of normal $\eta$-long terms
   - Flexible-rigid and flexible-flexible equations : [[Contexts-Quantifiers-and-Constraints|Link1]], [[Unification-in-Type-Systems|Link2]]
   - Introduction-resolution on hereditary Horn clauses : [[Higher-Order-Unification-and-Resolution|Link1]], [[Weak-Splitting-and-Incomplete-Variants|Link2]]
   - The splitting rule
   - Resolution and unification merged into one process
7. **Elementary Substitutions and the Search Tree** : [[Elementary-Substitutions-and-the-Search-Tree|Link]]
   - Head variable choice and fresh argument variables
   - Typing constraints for well-typedness : [[Contexts-Quantifiers-and-Constraints|Link]]
   - Splitting degree
   - Product and sort substitutions : [[Elementary-Substitutions-and-the-Search-Tree|Link1]], [[Substitutions-Under-Quantified-Contexts|Link2]]
   - Derivations and search trees : [[Elementary-Substitutions-and-the-Search-Tree|Link]]
   - Interleaving an infinitely branching tree
8. **Soundness and Completeness** : [[Soundness-and-Completeness|Link]]
   - Solutions and normal solutions of a context : [[Meta-Type-System-and-Existential-Variables|Link1]], [[Substitutions-Under-Quantified-Contexts|Link2]], [[Higher-Order-Unification-and-Resolution|Link3]]
   - Soundness of derivations : [[Soundness-and-Completeness|Link]]
   - Completeness by induction on the size of a substitution
   - A well-founded order on terms and types
9. **Search Efficiency and Pruning** : [[Search-Efficiency-and-Pruning|Link]]
   - Incremental simplification of rigid-rigid constraints
   - Priority for flexible-rigid constraints : [[Search-Efficiency-and-Pruning|Link1]], [[Contexts-Quantifiers-and-Constraints|Link2]]
   - Delaying instantiation until the type has a rigid head
   - Priority to the rightmost variable : [[Search-Efficiency-and-Pruning|Link]]
   - Decidable unification fragments as heuristics
   - Avoiding splitting in the $\lambda\Pi$-calculus
   - Sort variables and floating universes : [[Meta-Type-System-and-Existential-Variables|Link]]
10. **Weak Splitting and Incomplete Variants** : [[Weak-Splitting-and-Incomplete-Variants|Link]]
    - Algorithm with weak splitting : [[Weak-Splitting-and-Incomplete-Variants|Link1]], [[Search-Efficiency-and-Pruning|Link2]]
    - Relation to introduction-resolution : [[Weak-Splitting-and-Incomplete-Variants|Link]]
    - Completeness of the transitive closure : [[Weak-Splitting-and-Incomplete-Variants|Link]]
11. **Unification in Type Systems** : [[Unification-in-Type-Systems|Link]]
    - Ground unifiability versus open unifiability
    - Empty types and inhabitation : [[Unification-in-Type-Systems|Link]]
    - Undecidability of flexible-flexible unification under a quantified prefix : [[Substitutions-Under-Quantified-Contexts|Link]]

---
