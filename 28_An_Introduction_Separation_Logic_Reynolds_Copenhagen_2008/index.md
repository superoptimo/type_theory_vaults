# An Introduction to Separation Logic (Preliminary Draft) — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The Separation Logic Assertion Language** : [[The-Separation-Logic-Assertion-Language|Link]]
   - The separating conjunction as asserting disjoint sub-heaps : [[The-Separation-Logic-Assertion-Language|Link1]], [[The-Frame-Rule-and-Local-Reasoning|Link2]]
   - The separating implication as extending the heap with a disjoint part : [[The-Separation-Logic-Assertion-Language|Link]]
   - The points-to assertion for a single heap cell
   - Abbreviations for active cells and multi-field records
   - Axiom schemata for separating conjunction and implication : [[The-Iterated-Separating-Conjunction|Link1]], [[The-Frame-Rule-and-Local-Reasoning|Link2]]
   - Unsoundness of contraction and weakening for separating conjunction : [[The-Separation-Logic-Assertion-Language|Link]]
   - Substructural character of separation logic : [[The-Separation-Logic-Assertion-Language|Link]]

2. **Semantics of Assertions** : [[Semantics-Of-Assertions|Link]]
   - Stores and heaps as the two components of a state
   - The satisfaction relation defined by structural induction : [[Semantics-Of-Assertions|Link]]
   - Substitution laws for expressions and assertions : [[Assertion-Variables|Link]]
   - Validity and satisfiability of assertions : [[Semantics-Of-Assertions|Link]]
   - Formal proofs versus meta-proofs : [[Semantics-Of-Assertions|Link]]

3. **Special Classes of Assertions** : [[Special-Classes-Of-Assertions|Link]]
   - Pure assertions independent of the heap : [[Special-Classes-Of-Assertions|Link]]
   - Strictly exact assertions that uniquely determine the heap : [[Special-Classes-Of-Assertions|Link]]
   - Precise assertions that determine a unique subheap : [[Special-Classes-Of-Assertions|Link]]
   - Intuitionistic assertions monotone under heap extension : [[Special-Classes-Of-Assertions|Link]]
   - Supported assertions and their least-subheap property : [[Special-Classes-Of-Assertions|Link]]
   - The precising operation converting supported assertions into precise ones : [[Special-Classes-Of-Assertions|Link]]
   - Isomorphism between precise and supported intuitionistic assertions : [[Special-Classes-Of-Assertions|Link]]

4. **Hoare Triples and Specifications** : [[Hoare-Triples-And-Specifications|Link]]
   - Partial versus total correctness specifications : [[Hoare-Triples-And-Specifications|Link1]], [[Annotated-Specifications|Link2]], [[Case-Studies-in-Program-Verification|Link3]]
   - Preconditions and postconditions : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link]]
   - Memory faults falsifying a specification
   - Well-specified programs don't go wrong : [[Hoare-Triples-And-Specifications|Link]]
   - The heap-manipulating commands: allocation, lookup, mutation, deallocation : [[Hoare-Triples-And-Specifications|Link]]
   - Indeterminacy of allocation addresses

5. **Hoare Logic Foundations** : [[Hoare-Logic-Foundations|Link]]
   - Command-specific versus structural inference rules : [[Hoare-Logic-Foundations|Link]]
   - Assignment, sequential composition, and consequence rules : [[Annotated-Specifications|Link]]
   - Verification conditions as the bridge to domain mathematics
   - The while-command rule and its invariant : [[Hoare-Logic-Foundations|Link]]
   - Vacuity, disjunction, conjunction, and quantification rules : [[Hoare-Logic-Foundations|Link]]
   - Ghost variables : [[Assertion-Variables|Link]]
   - The substitution rule and aliasing restrictions : [[Hoare-Logic-Foundations|Link]]
   - The unsound rule of constancy : [[Hoare-Logic-Foundations|Link1]], [[Procedures-And-Hypothetical-Specifications|Link2]]

6. **The Frame Rule and Local Reasoning** : [[The-Frame-Rule-and-Local-Reasoning|Link]]
   - The frame rule as O'Hearn's replacement for the rule of constancy
   - Footprint of a command
   - Safety monotonicity and the frame property : [[The-Frame-Rule-and-Local-Reasoning|Link]]
   - Soundness of the frame rule from programming-language properties
   - Locality as a two-way correspondence between footprint and heap assertion

7. **Inference Rules for Heap-Manipulating Commands** : [[Inference-Rules-for-Heap-Manipulating-Commands|Link]]
   - Local, global, and backward-reasoning forms of a rule : [[Inference-Rules-for-Heap-Manipulating-Commands|Link]]
   - Mutation rules and their interderivability via the frame rule
   - Deallocation rules
   - Nonoverwriting versus overwriting allocation rules : [[Inference-Rules-for-Heap-Manipulating-Commands|Link]]
   - Generalized assignment commands
   - The rich family of lookup rules : [[Inference-Rules-for-Heap-Manipulating-Commands|Link]]
   - Fractional permissions for shared read-only access

8. **Annotated Specifications** : [[Annotated-Specifications|Link]]
   - Proof outlines as a practical presentation of formal proofs
   - Left-complete, right-complete, and complete annotations : [[Annotated-Specifications|Link]]
   - Weakest (liberal) precondition
   - Annotation rules mirroring each structural and command-specific rule : [[Hoare-Logic-Foundations|Link1]], [[Semantics-Of-Assertions|Link2]]
   - Erasure functions connecting annotated specifications to formal proofs : [[Hoare-Triples-And-Specifications|Link1]], [[Hoare-Logic-Foundations|Link2]]
   - The function mapping formal proofs into annotation descriptions : [[Annotated-Specifications|Link]]

9. **Procedures and Hypothetical Specifications** : [[Procedures-And-Hypothetical-Specifications|Link]]
   - Simple procedures with modifiable and unmodifiable parameters
   - Hypothetical specifications and contexts : [[Procedures-And-Hypothetical-Specifications|Link]]
   - Nonrecursive and recursive procedure rules
   - Procedure call rules and substitution into hypotheses
   - Ghost parameters
   - Annotated contexts and annotated procedure definitions

10. **Abstract Data Types via Inductive Predicates** : [[Abstract-Data-Types-Via-Inductive-Predicates|Link]]
    - Representing abstract values (sequences, S-expressions) versus their heap representations
    - Singly-linked lists and the list predicate
    - List segments and the composition law
    - Touching versus nontouching list segments : [[Abstract-Data-Types-Via-Inductive-Predicates|Link1]], [[Doubly-Linked-and-Xor-Linked-List-Segments|Link2]]
    - Preciseness of list and list-segment predicates : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link]]
    - Bornat lists representing sequences of addresses rather than values : [[Abstract-Data-Types-Via-Inductive-Predicates|Link]]

11. **Trees, Dags, and Sharing** : [[Trees-Dags-And-Sharing|Link]]
    - S-expressions as the abstract data type : [[Abstract-Data-Types-Via-Inductive-Predicates|Link]]
    - Trees as sharing-free representations
    - Dags as representations permitting acyclic sharing
    - Preciseness of tree predicates versus intuitionistic character of dag predicates
    - Skewed sharing and its prevention via field counts : [[Trees-Dags-And-Sharing|Link]]
    - Heap auxiliaries as attributes independent of command execution

12. **Assertion Variables** : [[Assertion-Variables|Link]]
    - Assertion variables as ghost variables ranging over heap properties
    - The assertion store extending the concept of state : [[Assertion-Variables|Link]]
    - Generalized substitution law for assertion variables : [[Assertion-Variables|Link]]
    - Strengthening recursive specifications to rule out heap-dependent copying errors

13. **Doubly-Linked and Xor-Linked List Segments** : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link]]
    - The dlseg predicate with forward and backward linkage
    - Emptiness conditions from either direction of linkage : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link]]
    - Small procedures distinguished by which parameter they modify
    - Xor-linked list segments encoding both neighbors in one field

14. **Shared-Variable Concurrency** : [[Shared-Variable-Concurrency|Link]]
    - Failure of the naive parallel composition rule under heap interference
    - Separating conjunction replacing ordinary conjunction in the parallel rule
    - Conditional critical regions and resource invariants : [[Shared-Variable-Concurrency|Link]]
    - Ownership transfer of heap portions between processes and resources

15. **The Iterated Separating Conjunction** : [[The-Iterated-Separating-Conjunction|Link]]
    - Binding operator generalizing separating conjunction over an index range : [[The-Iterated-Separating-Conjunction|Link1]], [[The-Separation-Logic-Assertion-Language|Link2]]
    - Axiom schemata for splitting, shifting, and distributing the iterated conjunction : [[The-Iterated-Separating-Conjunction|Link]]
    - Arrays as heap-allocated blocks described by the iterated conjunction
    - The array predicate relating a heap range to a sequence
    - Cyclic buffers described via modular indexing

16. **Case Studies in Program Verification** : [[Case-Studies-in-Program-Verification|Link]]
    - The Schorr-Waite marking algorithm and reversed-spine invariants : [[Case-Studies-in-Program-Verification|Link]]
    - Sorting a list by merging with an n log n in-place algorithm
    - Partition and quicksort on arrays : [[Case-Studies-in-Program-Verification|Link]]
    - Copying and substitution procedures on trees and dags : [[Assertion-Variables|Link1]], [[Semantics-Of-Assertions|Link2]]
    - A LISP program computing all subsets of a list via shared sublist storage

---
