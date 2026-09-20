# Proof Theory and Logic Programming: Computation as Proof Search — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Terms, Types, and Formulas in the Simple Theory of Types** : [[Terms-Types-and-Formulas-in-the-Simple-Theory-of-Types|Link]]
   - The untyped and simply typed $\lambda$-calculus
   - $\alpha$, $\beta$, and $\eta$ conversion and normal forms
   - Simple types and the order of a type : [[Terms-Types-and-Formulas-in-the-Simple-Theory-of-Types|Link]]
   - Signatures and typed terms : [[Terms-Types-and-Formulas-in-the-Simple-Theory-of-Types|Link]]
   - Formulas as terms of type $o$ : [[Terms-Types-and-Formulas-in-the-Simple-Theory-of-Types|Link]]
   - Clausal order and polarity of subformula occurrences
   - Sequents as pairs of formula collections : [[Terms-Types-and-Formulas-in-the-Simple-Theory-of-Types|Link]]

2. **The Sequent Calculus** : [[The-Sequent-Calculus|Link]]
   - Frege proofs versus sequent calculus proofs : [[Linear-Logic-Programming|Link1]], [[The-Sequent-Calculus|Link2]]
   - Structural rules: exchange, contraction, weakening : [[The-Sequent-Calculus|Link1]], [[Linear-Logic|Link2]]
   - Identity rules: initial and cut : [[Classical-and-Intuitionistic-Logic|Link]]
   - Introduction rules and eigenvariables : [[Classical-and-Intuitionistic-Logic|Link1]], [[The-Sequent-Calculus|Link2]]
   - Additive versus multiplicative inference rules : [[The-Sequent-Calculus|Link1]], [[Linear-Logic|Link2]]
   - Permutation of inference rules and invertibility : [[The-Sequent-Calculus|Link]]
   - Focused versus unfocused proof systems : [[The-Sequent-Calculus|Link]]
   - Cut-elimination and its consequences : [[Classical-and-Intuitionistic-Logic|Link1]], [[Focused-Proofs-and-Cut-Elimination-for-Linear-Logic|Link2]], [[Higher-Order-Quantification|Link3]], [[The-Sequent-Calculus|Link4]]
   - The subformula property : [[Higher-Order-Quantification|Link]]
   - Derivable versus admissible rules : [[Classical-and-Intuitionistic-Logic|Link]]

3. **Classical and Intuitionistic Logic** : [[Classical-and-Intuitionistic-Logic|Link]]
   - C-proofs and I-proofs as single- versus multiple-conclusion sequent systems : [[Classical-and-Intuitionistic-Logic|Link]]
   - Duality of the initial and cut rules : [[Classical-and-Intuitionistic-Logic|Link]]
   - Logical equivalence and formula replacement : [[Classical-and-Intuitionistic-Logic|Link]]
   - Invertible introduction rules : [[Classical-and-Intuitionistic-Logic|Link]]
   - Negation, false, and minimal logic : [[Classical-and-Intuitionistic-Logic|Link]]
   - Excluded middle and its proof
   - Nondeterminism in proof search and don't-care versus don't-know choices : [[Classical-and-Intuitionistic-Logic|Link]]

4. **Goal-Directed Proof Search and Uniform Proofs** : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link]]
   - Uniform proofs and abstract logic programming languages
   - The disjunction and existence properties
   - First-order Horn clauses (fohc) : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link]]
   - First-order hereditary Harrop formulas (fohh) : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link]]
   - Backchaining as focused rule application : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link]]
   - The $\Downarrow$fohh focused proof system : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link]]
   - Completeness of focused proofs for intuitionistic logic : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link1]], [[Classical-and-Intuitionistic-Logic|Link2]]
   - Paths in a formula and their associated sequents
   - A canonical Kripke model for intuitionistic provability : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link1]], [[Classical-and-Intuitionistic-Logic|Link2]]
   - Synthetic inference rules : [[Goal-Directed-Proof-Search-and-Uniform-Proofs|Link1]], [[Linear-Logic|Link2]]
   - Modular and hierarchical logic programming : [[Linear-Logic-Programming|Link]]
   - Limitations of fohc and fohh (non-reachability, inequality, scoping)

5. **Linear Logic** : [[Linear-Logic|Link]]
   - Linear logic as a logic of resources : [[Collection-Analysis-for-Horn-Clauses|Link]]
   - The exponentials $!$ and $?$ : [[Linear-Logic|Link]]
   - Multiplicative additive linear logic (MALL)
   - The eight MALL connectives and their units : [[Linear-Logic|Link1]], [[Higher-Order-Quantification|Link2]]
   - Duality and polarity of connectives : [[Linear-Logic|Link]]
   - Linear implication $\multimap$ and intuitionistic implication $\Rightarrow$ : [[Linear-Logic|Link]]
   - Two-zone (bounded/unbounded) sequents : [[Linear-Logic|Link]]
   - Lolli and the $L_1$ fragment
   - Forum and the $L_2$ fragment
   - Multiple-conclusion uniform proofs : [[Linear-Logic|Link]]
   - Lazy splitting of contexts (the IO proof system)
   - Conservativity of $L_2$ over $L_1$ and $L_0$
   - Generalized synthetic inference rules : [[Linear-Logic|Link]]

6. **Focused Proofs and Cut-Elimination for Linear Logic** : [[Focused-Proofs-and-Cut-Elimination-for-Linear-Logic|Link]]
   - Generalized paths and their normal form
   - Admissibility of the general initial rule : [[Focused-Proofs-and-Cut-Elimination-for-Linear-Logic|Link]]
   - The four cut rules (cutl, cut!, cut?, key cut) and their elimination
   - Rank, degree, and measure of a cut occurrence
   - Soundness and completeness of $\Downarrow L_2$ with respect to $L$ : [[Classical-and-Intuitionistic-Logic|Link]]
   - Andreoli's asynchronous and synchronous phases

7. **Linear Logic Programming** : [[Linear-Logic-Programming|Link]]
   - Encoding multisets as formulas (conjunctive and disjunctive encodings) : [[Linear-Logic-Programming|Link]]
   - Multiset rewriting on the left and on the right of sequents : [[Linear-Logic-Programming|Link]]
   - Context management for implementing theorem provers : [[Linear-Logic-Programming|Link]]
   - Using linear logic as a metalogic to specify sequent calculus proof systems
   - Object logic versus metalogic : [[Linear-Logic-Programming|Link]]

8. **Higher-Order Quantification** : [[Higher-Order-Quantification|Link]]
   - Quantification at all types, including predicate and propositional types
   - The near-focused proof system $\Downarrow N$ : [[Linear-Logic|Link]]
   - Instantiation of higher-order quantifiers and loss of the subformula property
   - Leibniz equality : [[Higher-Order-Quantification|Link]]
   - Cut-elimination via candidats de r\'eductibilit\'e
   - Higher-order programming, tactics, and tacticals : [[Higher-Order-Quantification|Link]]
   - Hiding predicates and specification details via existential quantification
   - Proving the symmetry of reverse using higher-order substitution
   - Higher-order Horn clauses and higher-order hereditary Harrop formulas
   - Rigid versus flexible atomic formulas : [[Higher-Order-Quantification|Link]]

9. **Specifying Computations with Multisets and Automata** : [[Specifying-Computations-with-Multisets-and-Automata|Link]]
   - Numerals and arithmetic encoded as multisets
   - Words and letters encoded as $\lambda$-terms
   - Encoding finite automata as linear logic theories : [[Specifying-Computations-with-Multisets-and-Automata|Link]]
   - Encoding pushdown automata : [[Specifying-Computations-with-Multisets-and-Automata|Link]]
   - Alternating finite automata via additive conjunction : [[Specifying-Computations-with-Multisets-and-Automata|Link]]

10. **Collection Analysis for Horn Clauses** : [[Collection-Analysis-for-Horn-Clauses|Link]]
    - Static analysis via approximating data structures by multisets, sets, or lists
    - Substituting for types, non-logical constants, and assumptions in proof theory : [[Collection-Analysis-for-Horn-Clauses|Link]]
    - Multiset and set statements and their linear logic translations
    - Automating collection analysis with specialized proof systems

11. **Encoding Security Protocols and Process Calculi** : [[Encoding-Security-Protocols-and-Process-Calculi|Link]]
    - The $\pi$-calculus and its encoding into linear logic formulas : [[Encoding-Security-Protocols-and-Process-Calculi|Link]]
    - Scope extrusion and restriction
    - Communicating on a public network via multiset rewriting : [[Encoding-Security-Protocols-and-Process-Calculi|Link]]
    - Static distribution of keys and dynamic creation of new symbols : [[Encoding-Security-Protocols-and-Process-Calculi|Link]]
    - Agent clauses, agent theories, and agent state predicates
    - The Needham–Schroeder Shared Key Protocol
    - Agents as nested linear implications : [[Encoding-Security-Protocols-and-Process-Calculi|Link]]

12. **Formalizing Operational Semantics** : [[Formalizing-Operational-Semantics|Link]]
    - Multiset rewriting, structural operational semantics, and abstract machines as three frameworks
    - Encoding programs as terms with binding via $\lambda$-abstraction
    - Big-step versus small-step semantics : [[Formalizing-Operational-Semantics|Link]]
    - Binary clauses and continuation-passing style : [[Formalizing-Operational-Semantics|Link]]
    - The Krivine machine and the SECD machine as abstract evaluation systems
    - Specifying global state and concurrency primitives in linear logic : [[Formalizing-Operational-Semantics|Link]]

---
