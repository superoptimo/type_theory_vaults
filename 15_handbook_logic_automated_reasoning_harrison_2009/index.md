# Handbook of Practical Logic and Automated Reasoning — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Foundations of Symbolic Logic in OCaml** : [[Foundations-of-Symbolic-Logic-in-OCaml|Link]]
   - Syntax versus semantics distinction
   - Abstract syntax trees : [[Foundations-of-Symbolic-Logic-in-OCaml|Link1]], [[Propositional-Logic|Link2]]
   - Object language and metalanguage : [[Foundations-of-Symbolic-Logic-in-OCaml|Link]]
   - Parsing and prettyprinting of formulas
   - Term rewriting and simplification via pattern matching
   - Boole's algebra of logic : [[Foundations-of-Symbolic-Logic-in-OCaml|Link]]
   - Leibniz's characteristica universalis and calculus ratiocinator
2. **Propositional Logic** : [[Propositional-Logic|Link]]
   - Propositional syntax and semantics : [[First-Order-Logic-Syntax-and-Semantics|Link1]], [[Foundations-of-Symbolic-Logic-in-OCaml|Link2]], [[Propositional-Logic|Link3]]
   - Tautology, satisfiability, and logical consequence
   - Negation normal form : [[Propositional-Logic|Link]]
   - Disjunctive and conjunctive normal form : [[Propositional-Logic|Link]]
   - Definitional CNF and the Tseitin transformation : [[Propositional-Logic|Link]]
   - Equisatisfiability versus logical equivalence : [[Propositional-Logic|Link]]
   - De Morgan laws and duality : [[Propositional-Logic|Link]]
   - Compactness theorem for propositional logic : [[Propositional-Logic|Link1]], [[Automated-First-Order-Theorem-Proving|Link2]]
3. **Propositional Satisfiability Algorithms** : [[Propositional-Satisfiability-Algorithms|Link]]
   - The Davis–Putnam procedure : [[Propositional-Satisfiability-Algorithms|Link]]
   - Unit propagation and the pure literal rule
   - The DPLL procedure
   - Backjumping and clause learning : [[Propositional-Satisfiability-Algorithms|Link]]
   - Stålmarck's method and the dilemma rule : [[Propositional-Satisfiability-Algorithms|Link]]
   - Binary decision diagrams : [[Propositional-Satisfiability-Algorithms|Link]]
   - Digital circuit and arithmetic encodings
   - NP-completeness and the P versus NP problem
4. **First-Order Logic: Syntax and Semantics** : [[First-Order-Logic-Syntax-and-Semantics|Link]]
   - Terms, quantifiers, and variable binding : [[First-Order-Logic-Syntax-and-Semantics|Link]]
   - Free and bound variables and substitution : [[Automated-First-Order-Theorem-Proving|Link]]
   - Prenex normal form : [[First-Order-Logic-Syntax-and-Semantics|Link]]
   - Skolemization : [[Equality-Reasoning|Link]]
   - Herbrand's theorem and Herbrand models : [[First-Order-Logic-Syntax-and-Semantics|Link]]
   - Canonical models : [[First-Order-Logic-Syntax-and-Semantics|Link]]
5. **Automated First-Order Theorem Proving** : [[Automated-First-Order-Theorem-Proving|Link]]
   - Unification and most general unifiers
   - Analytic tableaux and the Prawitz procedure : [[Automated-First-Order-Theorem-Proving|Link]]
   - The resolution principle and the lifting lemma : [[Automated-First-Order-Theorem-Proving|Link]]
   - Subsumption and replacement : [[Automated-First-Order-Theorem-Proving|Link]]
   - Refinements of resolution : [[Automated-First-Order-Theorem-Proving|Link]]
   - Horn clauses and logic programming : [[Automated-First-Order-Theorem-Proving|Link]]
   - SLD resolution and Prolog : [[Automated-First-Order-Theorem-Proving|Link]]
   - Model elimination and the MESON calculus : [[Automated-First-Order-Theorem-Proving|Link]]
   - Compactness and Löwenheim–Skolem theorems for first-order logic : [[Automated-First-Order-Theorem-Proving|Link]]
6. **Equality Reasoning** : [[Equality-Reasoning|Link]]
   - Equality axioms : [[Equality-Reasoning|Link]]
   - Congruence closure : [[Equality-Reasoning|Link]]
   - Term rewriting systems and confluence
   - Termination orderings and the lexicographic path order : [[Equality-Reasoning|Link]]
   - Knuth–Bendix completion : [[Equality-Reasoning|Link]]
   - Critical pairs : [[Equality-Reasoning|Link]]
   - Equality elimination via the Brand transformation : [[Equality-Reasoning|Link]]
   - Demodulation and paramodulation : [[Combining-Decision-Procedures|Link]]
   - Categoricity and elementary equivalence : [[Equality-Reasoning|Link]]
7. **Decidable Theories and Quantifier Elimination** : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - The decision problem and decidable fragments : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - The AE fragment and miniscoping : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - The finite model property and the small model property : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - Aristotelian syllogisms
   - Quantifier elimination as a method : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - Dense linear orders : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - Presburger arithmetic and Cooper's algorithm : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - Quantifier elimination over the complex numbers : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
   - Quantifier elimination over the real numbers : [[Decidable-Theories-and-Quantifier-Elimination|Link]]
8. **Algebraic Decision Procedures** : [[Algebraic-Decision-Procedures|Link]]
   - Word problems for rings and the Nullstellensatz : [[Algebraic-Decision-Procedures|Link]]
   - Gröbner bases and Buchberger's algorithm : [[Algebraic-Decision-Procedures|Link]]
   - Geometric theorem proving and Wu's method : [[Algebraic-Decision-Procedures|Link]]
9. **Combining Decision Procedures** : [[Combining-Decision-Procedures|Link]]
   - Craig's interpolation theorem : [[Combining-Decision-Procedures|Link]]
   - The Nelson–Oppen combination method : [[Combining-Decision-Procedures|Link]]
   - Stably infinite and convex theories
   - Shostak's method : [[Combining-Decision-Procedures|Link]]
   - Satisfiability modulo theories : [[Propositional-Satisfiability-Algorithms|Link1]], [[Propositional-Logic|Link2]]
10. **Interactive Theorem Proving and the LCF Approach** : [[Interactive-Theorem-Proving-and-the-LCF-Approach|Link]]
    - Hilbert systems, natural deduction, and sequent calculus : [[Interactive-Theorem-Proving-and-the-LCF-Approach|Link]]
    - The cut rule and cut elimination : [[Interactive-Theorem-Proving-and-the-LCF-Approach|Link]]
    - The LCF abstract type of theorems
    - Deriving inference rules from a small primitive core
    - First-order proof reconstructed by inference : [[Interactive-Theorem-Proving-and-the-LCF-Approach|Link]]
    - Skolemization and the drinker's principle in proof reconstruction
    - Tactics and tacticals : [[Interactive-Theorem-Proving-and-the-LCF-Approach|Link]]
    - Declarative versus procedural proof styles
11. **Limits of Automated Reasoning** : [[Limits-of-Automated-Reasoning|Link]]
    - Hilbert's programme : [[Limits-of-Automated-Reasoning|Link]]
    - Tarski's undefinability of truth : [[Limits-of-Automated-Reasoning|Link]]
    - Gödel numbering and self-reference : [[Limits-of-Automated-Reasoning|Link]]
    - Gödel's first incompleteness theorem : [[Limits-of-Automated-Reasoning|Link]]
    - Gödel's second incompleteness theorem : [[Limits-of-Automated-Reasoning|Link]]
    - Turing machines and computability : [[Limits-of-Automated-Reasoning|Link]]
    - Recursively enumerable sets : [[Limits-of-Automated-Reasoning|Link]]
    - Church's theorem on undecidability of first-order logic : [[Limits-of-Automated-Reasoning|Link]]
    - Hilbert's tenth problem and Diophantine sets : [[Limits-of-Automated-Reasoning|Link]]
    - The nature of logic : [[Limits-of-Automated-Reasoning|Link]]

---
