# An Introduction to Separation Logic — Guidelines

## Header

**Title:** An Introduction to Separation Logic (Preliminary Draft)
**Author(s):** John C. Reynolds
**Publication:** Lecture notes, ITU University Copenhagen, October 20–22, 2008 (corrected October 23, 2008)

**Brief Summary:**
This is a preliminary draft of lecture notes introducing separation logic, a system for reasoning about imperative programs that manipulate shared mutable data structures. Separation logic extends Hoare logic with the separating conjunction $P * Q$ and separating implication $P \mathbin{-\!*} Q$, operators that let assertions describe how the heap splits into disjoint parts. The notes build from the basic assertion language and its semantics, through a full proof theory for Hoare triples and "annotated specifications" (proof outlines), to worked verifications of increasingly elaborate heap-manipulating programs — lists, trees, dags, doubly- and xor-linked structures, arrays, and classic algorithms like mergesort, quicksort, and LISP's subset-list construction. The organizing idea throughout is O'Hearn's frame rule, which licenses *local reasoning*: a specification of a command need only describe the "footprint" of heap cells it actually touches.

**Intent of the Author:**
Reynolds wrote these notes to give a self-contained, rigorous introduction to separation logic — its assertion language, its semantics, its full apparatus of inference rules (local, global, and backward-reasoning forms), and the discipline of annotated specifications — so that a reader could both understand the theory and see it applied to nontrivial programs. He wants readers to appreciate the frame rule as the key mechanism that gives the logic its scalability advantage over classical Hoare logic when reasoning about sharing and mutation.

---

## Topic List

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

## Chapter Summaries

### Chapter 1: An Overview (pp. 3–32)

**Summary:** Introduces the motivating problem — reasoning about shared mutable data structures forces conventional logics into unwieldy explicit non-aliasing conditions — and shows how the separating conjunction $*$ collapses this complexity. It surveys the whole logic in miniature: the programming language extensions, the assertion language, Hoare-triple specifications, list and tree predicates, arrays via iterated separating conjunction, the Schorr-Waite proof, shared-variable concurrency, and fractional permissions.

**Key Definitions & Concepts by Section:**
- **1.1 An Example of the Problem** — in-place list reversal (`LREV`), reachability predicate, the explosion of non-sharing conditions in classical Hoare-logic invariants. : [[Case-Studies-in-Program-Verification|Link]]
- **1.2 Background** — history of separation logic's development by Reynolds, Ishtiaq, and O'Hearn; the "bunched implications" connection; survey of subsequent extensions (concurrency, higher-order procedures, decision procedures, fractional permissions). : [[Abstract-Data-Types-Via-Inductive-Predicates|Link1]], [[Assertion-Variables|Link2]], [[Procedures-And-Hypothetical-Specifications|Link3]], [[Trees-Dags-And-Sharing|Link4]]
- **1.3 The Programming Language** — the store/heap state model, allocation (`cons`), lookup (`[e]`), mutation, deallocation, and the memory-fault semantics (`abort`). : [[The-Separation-Logic-Assertion-Language|Link]]
- **1.4 Assertions** — $\mathrm{emp}$, $e \mapsto e'$, $p_1 * p_2$ (separating conjunction), $p_1 \mathbin{-\!*} p_2$ (separating implication); abbreviations $e \mapsto -$ and $e \hookrightarrow e'$; axiom schemata including currying/decurrying and the unsoundness of contraction and weakening. : [[Assertion-Variables|Link1]], [[Case-Studies-in-Program-Verification|Link2]], [[Semantics-Of-Assertions|Link3]]
- **1.5 Specifications and their Inference Rules** — partial and total correctness Hoare triples, "well-specified programs don't go wrong," the frame rule versus the unsound rule of constancy, local/global/backward-reasoning rule forms for mutation, deallocation, and allocation. : [[Case-Studies-in-Program-Verification|Link]]
- **1.6 Lists** — the `list α i` predicate defined by induction on the sequence $\alpha$, and its use in the list-reversal proof.
- **1.7 Trees and Dags** — S-expressions, `tree τ(i)` and `dag τ(i)` predicates. : [[Assertion-Variables|Link1]], [[Trees-Dags-And-Sharing|Link2]]
- **1.8 Arrays and the Iterated Separating Conjunction** — the `allocate` command and the $\bigstar$-style iterated conjunction for describing arrays and cyclic buffers. : [[The-Iterated-Separating-Conjunction|Link]]
- **1.9 Proving the Schorr-Waite Algorithm** — Yang's proof using separating implication to assert that a reversed spine, once restored, preserves the original spanning tree. : [[Case-Studies-in-Program-Verification|Link]]
- **1.10 Shared-Variable Concurrency** — O'Hearn's parallel-composition rule with separating conjunction, conditional critical regions, resource invariants. : [[Shared-Variable-Concurrency|Link]]
- **1.11 Fractional Permissions** — Bornat/Boyland permissions attached to $\mapsto$ for read-only sharing, with a conservation law for permission fractions.

**Key Questions:**
1. Why does the separating conjunction succeed in expressing non-sharing invariants so much more concisely than explicit reachability conditions in classical Hoare logic?
2. What programming-language properties does the frame rule depend on, and why does the rule of constancy fail in separation logic but the frame rule does not?
3. Why must a valid specification's precondition preclude memory faults, and what practical consequence does this have for the implementor of the heap?

---

### Chapter 2: Assertions (pp. 33–56)

**Summary:** Gives the formal semantics of assertions via the satisfaction relation $s, h \models p$, develops the machinery of inference and formal proof, and classifies assertions into special classes (pure, strictly exact, precise, intuitionistic, supported) whose properties license extra axiom schemata used throughout the rest of the notes. : [[Assertion-Variables|Link1]], [[Case-Studies-in-Program-Verification|Link2]], [[Semantics-Of-Assertions|Link3]]

**Key Definitions & Concepts by Section:**
- **2.1 The Meaning of Assertions** — the satisfaction relation $s,h \models p$ defined by structural induction; validity and satisfiability; the Partial Substitution Law for Assertions. : [[Semantics-Of-Assertions|Link]]
- **2.2 Inference** — inference rules, instances, soundness, axiom schemas, formal proofs versus meta-proofs; the crucial distinction between a sound rule $p / q$ and a sound implication $p \Rightarrow q$.
- **2.3 Special Classes of Assertions** — pure assertions (heap-independent); strictly exact assertions (unique heap); precise assertions (unique subheap, Section 2.3.3); intuitionistic assertions (monotone under heap extension, Section 2.3.4) and their modal translation from intuitionistic to classical logic; supported assertions (least common subheap property, Section 2.3.5); the precising operation $\mathrm{Pr}\,p = p \wedge \neg(p * \neg\,\mathrm{emp})$ (Section 2.3.6) and its isomorphism between precise and supported-intuitionistic assertions. : [[Special-Classes-Of-Assertions|Link]]
- **2.4 Some Derived Inference Rules** — derivations of $q * (q \mathbin{-\!*} p) \Rightarrow p$ and related currying/decurrying lemmas used repeatedly in later soundness proofs.

**Key Questions:**
1. What is the difference between a precise assertion and a strictly exact assertion, and why can no assertion be both precise and intuitionistic (except when unsatisfiable)?
2. How does the precising operation $\mathrm{Pr}$ act as an inverse to $- * \mathrm{true}$, and in what sense are precise and supported-intuitionistic assertions isomorphic?
3. Why do the semidistributive laws for $*$ over $\wedge$ and $\forall$ become full distributive laws exactly when one operand is precise (or supported and the others intuitionistic)?

---

### Chapter 3: Specifications (pp. 57–110)

**Summary:** Develops the full proof theory of Hoare triples for separation logic: the classical Hoare-logic rules (reviewed and shown still sound), the formal machinery of annotated specifications that make proofs practical to read, the frame rule's precise soundness conditions, and the complete family of local/global/backward-reasoning rules for mutation, deallocation, allocation, and lookup, together with proofs that these forms are interderivable. : [[Annotated-Specifications|Link1]], [[Hoare-Triples-And-Specifications|Link2]]

**Key Definitions & Concepts by Section:**
- **3.1 Hoare Triples** — partial ($\{p\}\,c\,\{q\}$) and total ($[p]\,c\,[q]$) correctness specifications. : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link1]], [[Hoare-Triples-And-Specifications|Link2]]
- **3.2 Hoare's Inference Rules for Specifications** — assignment, sequential composition, strengthening precedent, partial correctness of while, weakening consequent, skip, conditional, variable declaration; verification conditions; alternative (Floyd-style) forward assignment and conditional rules; the combined consequence rule. : [[Hoare-Triples-And-Specifications|Link]]
- **3.3 Annotated Specifications** — annotation descriptions $A \vdash \{p\}\,c\,\{q\}$; left-complete, right-complete, and complete annotations; the weakest (liberal) precondition; annotated forms of assignment, sequential composition, strengthening precedent, while, skip, conditional, and variable declaration. : [[Annotated-Specifications|Link]]
- **3.4 More Structural Inference Rules** — vacuity, disjunction, conjunction, existential/universal quantification, ghost variables, substitution (with aliasing restrictions), renaming.
- **3.5 The Frame Rule** — safety monotonicity and the frame property as the two programming-language properties underlying its soundness; a soundness proof. : [[Case-Studies-in-Program-Verification|Link1]], [[Doubly-Linked-and-Xor-Linked-List-Segments|Link2]], [[Hoare-Triples-And-Specifications|Link3]], [[Procedures-And-Hypothetical-Specifications|Link4]]
- **3.6 More Rules for Annotated Specifications** — annotated versions of vacuity, disjunction, conjunction, existential/universal quantification, frame, and substitution. : [[Annotated-Specifications|Link]]
- **3.7 Inference Rules for Mutation and Disposal** — local (MUL), global (MUG), backward-reasoning (MUBR) mutation rules and local (DISL), global/backward (DISBR) disposal rules, each derived from the others via the frame rule. : [[Inference-Rules-for-Heap-Manipulating-Commands|Link]]
- **3.8 Rules for Allocation** — nonoverwriting local/global forms, and the fuller local (CONSL), global (CONSG), and backward-reasoning (CONSBR) forms handling overwriting, related by the equivalence $v := \mathrm{cons}(e) \cong \mathrm{newvar}\ \hat v\ \mathrm{in}\ (\hat v := \mathrm{cons}(e); v := \hat v)$. : [[Inference-Rules-for-Heap-Manipulating-Commands|Link]]
- **3.9 Rules for Lookup** — nonoverwriting and general local (LKL), global (LKG), and two backward-reasoning (LKBR1, LKBR2) forms; the observation that a lookup command can "erase" an existential quantifier.
- **3.10 Annotated Specifications for the New Rules** — annotation descriptions for the backward-reasoning forms as the natural weakest-precondition rules. : [[Annotated-Specifications|Link]]
- **3.11 A Final Example** — the two-cell cyclic-structure construction annotated in full detail.
- **3.12 More about Annotated Specifications** — the erasure functions `erase-annspec`/`erase-spec`, the completeness-forcing functions `left-compl`/`right-compl`/`compl`, and the function $\Phi$ mapping formal proofs to annotation descriptions (and its converse direction via $\Psi$), establishing that annotated specifications faithfully correspond to formal proofs. : [[Annotated-Specifications|Link]]

**Key Questions:**
1. Why are three different forms (local, global, backward-reasoning) given for each heap-manipulating command, and in what sense are they interderivable rather than independently primitive?
2. What is the technical trick that lets annotated specifications determine their own premisses when applying the sequential-composition rule, and why does this fail without annotation?
3. Why does the substitution rule need a side condition preventing an actual parameter from occurring free in other substituted expressions, and what invalid conclusion would result without it?

---

### Chapter 4: Lists and List Segments (pp. 111–160)

**Summary:** Moves from bare lists to list segments and the reasoning needed for programs that manipulate parts of lists, introduces simple (nonrecursive and recursive) procedures with hypothetical specifications to enable modular verification, and works through progressively richer list representations (Bornat lists, doubly-linked segments, xor-linked segments) culminating in an efficient in-place mergesort. : [[Case-Studies-in-Program-Verification|Link1]], [[Doubly-Linked-and-Xor-Linked-List-Segments|Link2]]

**Key Definitions & Concepts by Section:**
- **4.1 Singly-Linked List Segments** — `lseg α (i, j)` defined by structural induction; the composition law $\mathrm{lseg}_{\alpha\cdot\beta}(i,k) \Leftrightarrow \exists j.\ \mathrm{lseg}_\alpha(i,j) * \mathrm{lseg}_\beta(j,k)$; touching versus nontouching segments (`ntlseg`); annotated insertion and deletion programs. : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link]]
- **4.2 A Cyclic Buffer** — a list-based (rather than array-based) cyclic buffer invariant combining two list segments with length bookkeeping. : [[Abstract-Data-Types-Via-Inductive-Predicates|Link1]], [[The-Iterated-Separating-Conjunction|Link2]]
- **4.3 Preciseness Revisited** — formal proof that `list α i` and $\exists\alpha.\ \mathrm{list}_\alpha\ i$ are precise, using a careful language/metalanguage distinction for sequence variables.
- **4.4 Bornat Lists** — `listN σ i`, representing a list as a sequence of addresses rather than values, describing only the link fields. : [[Abstract-Data-Types-Via-Inductive-Predicates|Link]]
- **4.5 Simple Procedures** — syntactic restrictions defining "simple" procedures; hypothetical specifications $\Gamma \vdash \{p\}\,c\,\{q\}$; nonrecursive (SPROC) and recursive (SRPROC) procedure rules; call (CALL) and general call (GCALL) rules; ghost parameters; the `multfact` worked example. : [[Procedures-And-Hypothetical-Specifications|Link]]
- **4.6 Still More about Annotated Specifications** — extension of the erasure/completion apparatus and $\Phi$/$\Psi$ functions to hypothetical (procedure-aware) annotation descriptions. : [[Annotated-Specifications|Link1]], [[Hoare-Triples-And-Specifications|Link2]]
- **4.7 An Extended Example: Sorting by Merging** — sequence concepts (image, pointwise-extended relations, `ord`, rearrangement `∼`); the `mergesort` and `merge` procedure specifications and their recursive proof structure.
- **4.8 Doubly-Linked List Segments** — `dlseg α (i, i0, j, j0)`; forward/backward emptiness conditions; procedures `lookuprpt`/`setrpt`/`lookuplpt`/`setlpt` distinguished by which parameter they modify, and their use in an insertion program via the frame rule. : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link]]
- **4.9 Xor-Linked List Segments** — `xlseg α (i, i0, j, j0)` storing $j \oplus i_0$ in a single field via exclusive-or. : [[Doubly-Linked-and-Xor-Linked-List-Segments|Link]]

**Key Questions:**
1. Why is $\exists\alpha.\ \mathrm{lseg}_\alpha(i,j)$ not precise even though $\mathrm{lseg}_\alpha(i,j)$ itself is, and what does "touching" have to do with this?
2. What restriction on a recursive procedure's specification lets one use the hypothesis about the procedure to prove its own body, and why must this restriction be limited to partial (not total) correctness?
3. In the doubly-linked list example, why does swapping `setrpt` for `lookuprpt` (despite both satisfying the same Hoare triple) break the proof of the surrounding insertion program?

---

### Chapter 5: Trees and Dags (pp. 161–180)

**Summary:** Extends the representational framework from sequences to S-expressions, contrasting sharing-free trees with sharing-permitting dags, and shows that verifying a dag-copying procedure correctly requires strengthening the recursion hypothesis with an assertion variable so that the proof does not (falsely) allow the procedure to disturb shared substructure. Closes with the problem of skewed sharing and its prevention via field counts. : [[Assertion-Variables|Link1]], [[Trees-Dags-And-Sharing|Link2]]

**Key Definitions & Concepts by Section:**
- **5.1 Trees** — `tree τ(i)` defined by structural induction using separating conjunction between subtrees; the `copytree` procedure and its recursive proof.
- **5.2 Dags** — `dag τ(i)` defined using ordinary conjunction between shared subdags; proofs that `dag τ(i)` and $\exists\tau.\ \mathrm{dag}_\tau(i)$ are intuitionistic and supported; the precising operation applied to obtain precise dag assertions; the failure of a naive recursive proof that `copytree` preserves a dag's sharing.
- **5.3 Assertion Variables** — extending the state with an assertion store mapping assertion variables to heap properties; the generalized substitution law; extended substitution rules (SUB, SUBan). : [[Assertion-Variables|Link]]
- **5.4 Copying Dags to Trees** — the strengthened specification $\{p \wedge \mathrm{dag}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau,p\}\ \{p * \mathrm{tree}_\tau(j)\}$ and its successful recursive proof. : [[Assertion-Variables|Link]]
- **5.5 Substitution in S-expressions** — the `subst1` procedure substituting a dag for an atom occurring in a tree, using `copytree` internally. : [[Assertion-Variables|Link]]
- **5.6 Skewed Sharing** — the phenomenon of overlapping-but-nonidentical records permitted by the bare dag definition; field counts as a heap auxiliary; the annotated points-to $e \xrightarrow{[\hat e]} e'$; revised allocation/mutation/lookup/deallocation rules incorporating field counts. : [[Trees-Dags-And-Sharing|Link]]

**Key Questions:**
1. Why does the naive recursive hypothesis $\{\mathrm{dag}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau\}\ \{\mathrm{dag}_\tau(i) * \mathrm{tree}_\tau(j)\}$ fail to support the proof of `copytree`'s own recursive call, and how does introducing an assertion-variable parameter $p$ fix this?
2. What is skewed sharing, and why does the bare `dag` definition (without field counts) permit it even though it seems to only allow "legitimate" acyclic sharing?
3. Why must deallocation of a multi-field record be atomic (`dispose(e,n)`) once field counts are introduced, rather than allowing single-field disposal?

---

### Chapter 6: Iterated Separating Conjunction (pp. 181–204)

**Summary:** Introduces a binding form of separating conjunction, $\bigast_{v=e}^{e'} p$, that iterates $*$ over a contiguous range of indices, and uses it to give a clean account of heap-allocated arrays, culminating in verified Partition and Quicksort procedures and a sophisticated case study — a LISP subset-list program whose extensive internal sharing is precisely characterized using the iterated conjunction. : [[The-Iterated-Separating-Conjunction|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 A New Form of Assertion** — the iterated separating conjunction $\bigast_{v=e}^{e'} p$ defined via a partition of the heap indexed by a contiguous integer range; axiom schemata for empty range, singleton range, splitting, shifting the index, and distributing over pure conjuncts. : [[The-Separation-Logic-Assertion-Language|Link]]
- **6.2 Arrays** — the `allocate` command and its local/global/backward-reasoning rules using the iterated conjunction; the `array α (a,b)` predicate relating a heap range to a sequence, with splitting and single-cell axioms.
- **6.3 Partition** — an annotated specification of Hoare's Partition algorithm rearranging an array around a pivot. : [[Case-Studies-in-Program-Verification|Link]]
- **6.4 From Partition to Quicksort** — the recursive `quicksort` specification and proof, including the trick of pre-sorting the two end elements to guarantee nonempty partitions and termination. : [[Case-Studies-in-Program-Verification|Link]]
- **6.5 Another Cyclic Buffer** — an array-based cyclic buffer using modular index arithmetic ($x \oplus y$) and the iterated conjunction, with an annotated insertion program. : [[Abstract-Data-Types-Via-Inductive-Predicates|Link1]], [[The-Iterated-Separating-Conjunction|Link2]]
- **6.6 Connecting Two Views of Simple Lists** — the identity relating `list` to `listN` via an iterated conjunction over data fields.
- **6.7 Specifying a Program for Subset Lists** — a historically important LISP algorithm computing all sub-multisets of a list with maximal sharing; predicates `ss`, `Q`, `R`, `W` built with the iterated conjunction to characterize the resulting sharing structure and its size precisely. : [[Case-Studies-in-Program-Verification|Link]]

**Key Questions:**
1. How does the iterated separating conjunction's index-shifting axiom (6.4) support reasoning about a cyclic buffer's modular addressing scheme?
2. In the Quicksort proof, why is it necessary to sort the two end elements of the array separately and use their mean as the pivot, rather than choosing an arbitrary pivot?
3. What role does the predicate $W(\beta,\gamma,a)$ play in proving that the subset-list program's output has exactly the expected size, despite the extensive sharing between sublists?
