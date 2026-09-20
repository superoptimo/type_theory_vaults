# Tree Automata Techniques and Applications (TATA) — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Terms, Trees, and Contexts** : [[Terms-Trees-and-Contexts|Link]]
   - Ranked alphabets and arity : [[Terms-Trees-and-Contexts|Link]]
   - Terms as ground or variable-containing expressions
   - Ordered ranked trees as partial functions on positions : [[Terms-Trees-and-Contexts|Link]]
   - Subterms, substitutions, and contexts : [[Terms-Trees-and-Contexts|Link]]
   - Term size and height

2. **Recognizable Tree Languages and Finite Tree Automata** : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
   - Bottom-up nondeterministic finite tree automata
   - Runs, moves, and acceptance
   - Determinization by subset construction : [[Automata-for-Unranked-Trees|Link]]
   - Reduced and complete automata
   - Closure under union, intersection, and complementation : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link1]], [[Automata-with-Constraints|Link2]]
   - Tree homomorphisms and linearity : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
   - The pumping lemma for tree languages : [[Context-Free-Tree-Languages|Link]]
   - Myhill-Nerode theorem and minimal tree automata : [[Alternating-Tree-Automata|Link1]], [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link2]]
   - Top-down tree automata and the determinism gap : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link1]], [[Applications-of-Tree-Automata-to-Term-Rewriting|Link2]]
   - Complexity of membership, emptiness, and inclusion

3. **Regular Tree Grammars and Expressions** : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Regular tree grammars and derivations : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Equivalence of regularity and recognizability : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Regular tree expressions and Kleene's theorem for trees : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Substitution and iteration through placeholder symbols
   - Regular equation systems and least fixed points : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Derivation trees of context-free word grammars : [[Context-Free-Tree-Languages|Link1]], [[Regular-Tree-Grammars-and-Expressions|Link2]]
   - The Yield operator and context-free word languages : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - Local tree languages versus regular tree languages : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]

4. **Context-Free Tree Languages** : [[Context-Free-Tree-Languages|Link]]
   - Context-free tree grammars with argument-taking nonterminals : [[Context-Free-Tree-Languages|Link]]
   - The IO and OI derivation strategies
   - Non-linearity as the source of IO/OI divergence
   - Closure properties of IO tree languages : [[Context-Free-Tree-Languages|Link1]], [[Alternating-Tree-Automata|Link2]]

5. **Automata on Tuples of Trees** : [[Automata-on-Tuples-of-Trees|Link]]
   - Three notions of recognizability for relations : [[Regular-Tree-Grammars-and-Expressions|Link]]
   - The overlap coding of tuples into a single term
   - Ground Tree Transducers and shared-context relations : [[Automata-on-Tuples-of-Trees|Link]]
   - Closure under composition and transitive closure : [[Automata-on-Tuples-of-Trees|Link]]
   - Projection and cylindrification : [[Automata-on-Tuples-of-Trees|Link]]

6. **Weak Monadic Second-Order Logic and Tree Automata** : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
   - Syntax and semantics of WSkS : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
   - Coding finite sets of positions as trees : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
   - Definable sets equal recognizable sets
   - Decidability of WSkS
   - Non-elementary complexity of the decision procedure : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]

7. **Applications of Tree Automata to Term Rewriting** : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Order-sorted signatures as automata with subsort transitions : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Encompassment and the reducibility theory : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Ground reducibility : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Decidability of the first-order theory of a reduction relation : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Sequentiality and optimal reduction strategies : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Rigid E-unification : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Higher-order matching and 2-automata : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]

8. **Automata with Constraints** : [[Automata-with-Constraints|Link]]
   - Equality and disequality constraints between subtrees
   - Non-linear pattern recognition
   - Undecidability of emptiness for the general constrained class : [[Applications-of-Tree-Automata-to-Term-Rewriting|Link]]
   - Automata with constraints between brothers : [[Automata-with-Constraints|Link1]], [[Tree-Set-Automata-and-Set-Constraints|Link2]]
   - Reduction automata and bounded equality depth : [[Automata-with-Constraints|Link1]], [[Applications-of-Tree-Automata-to-Term-Rewriting|Link2]]
   - Ground normal forms of term rewriting systems : [[Automata-with-Constraints|Link]]

9. **Tree Set Automata and Set Constraints** : [[Tree-Set-Automata-and-Set-Constraints|Link]]
   - Generalized tree sets as valuations into a finite set
   - Tree set automata and their acceptance via range conditions : [[Tree-Set-Automata-and-Set-Constraints|Link]]
   - Deterministic, strongly deterministic, and simple automata
   - Regular generalized tree sets
   - Emptiness and satisfiability of set constraint systems : [[Tree-Set-Automata-and-Set-Constraints|Link]]
   - Least solutions of positive set constraints : [[Tree-Set-Automata-and-Set-Constraints|Link]]

10. **Tree Transducers** : [[Tree-Transducers|Link]]
    - Rational word transducers and the bimorphism theorem
    - Bottom-up versus top-down tree transducers : [[Automata-on-Tuples-of-Trees|Link]]
    - Copy-then-process versus process-then-copy behavior
    - Linearity and determinism as sources of good closure properties : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
    - The infinite hierarchy under transducer composition : [[Tree-Transducers|Link]]
    - Recognizability of transducer domains and images : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
    - Tree bimorphisms and delabelings : [[Tree-Transducers|Link]]

11. **Alternating Tree Automata** : [[Alternating-Tree-Automata|Link]]
    - Positive Boolean transition formulas : [[Alternating-Tree-Automata|Link]]
    - Complementation without determinization
    - Equivalence to deterministic bottom-up automata : [[Recognizable-Tree-Languages-and-Finite-Tree-Automata|Link]]
    - Complexity of emptiness and membership
    - Correspondence with Horn clauses and definite set constraints : [[Tree-Set-Automata-and-Set-Constraints|Link]]
    - Two-way alternating tree automata : [[Alternating-Tree-Automata|Link]]
    - Two-way automata versus pushdown automata : [[Alternating-Tree-Automata|Link1]], [[XML-Schema-Formalisms|Link2]]

12. **Automata for Unranked Trees** : [[Automata-for-Unranked-Trees|Link]]
    - Unranked trees and hedges : [[Automata-for-Unranked-Trees|Link]]
    - Hedge automata with regular horizontal languages : [[Automata-for-Unranked-Trees|Link]]
    - Determinism and the subset construction for hedges : [[Automata-for-Unranked-Trees|Link]]
    - First-child-next-sibling and extension encodings into ranked trees : [[Automata-for-Unranked-Trees|Link]]
    - Weak monadic second-order logic over child and sibling relations : [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata|Link]]
    - Representations of horizontal languages and their complexity
    - Minimization and the failure of the naive Myhill-Nerode congruence
    - Stepwise hedge automata and the @-congruence : [[Automata-for-Unranked-Trees|Link]]

13. **XML Schema Formalisms** : [[XML-Schema-Formalisms|Link]]
    - Document Type Definitions as local languages : [[XML-Schema-Formalisms|Link]]
    - Deterministic content models : [[XML-Schema-Formalisms|Link]]
    - Extended DTDs and typed alphabets
    - XML Schema and single-type extended DTDs : [[XML-Schema-Formalisms|Link]]
    - Relax NG as an unranked regular tree grammar : [[Regular-Tree-Grammars-and-Expressions|Link1]], [[Automata-for-Unranked-Trees|Link2]]
    - The interleave operator and its complexity cost

---
