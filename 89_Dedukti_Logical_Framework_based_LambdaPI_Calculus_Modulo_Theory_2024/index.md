# Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The λΠ-Calculus and Its Typing Judgments** : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]
   - Dependent types and the sorts Type and Kind : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]
   - Contexts, well-formedness, and local versus global contexts : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]
   - Typing rules for variables, products, abstraction, and application
   - The conversion rule and definitional equality up to β-reduction : [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link]]

2. **The λΠ-Calculus Modulo Theory** : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Rewrite rules as part of the global context : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link1]], [[Lambda-Pi-Calculus-and-Its-Typing-Judgments|Link2]]
   - Conversion extended by a user-declared congruence : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Subject reduction and its dependence on well-typed rules and product compatibility
   - Uniqueness of types modulo conversion
   - Rule schemes and finite contexts for infinite theories : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]

3. **Decidability via Effective Subsystems** : [[Decidability-via-Effective-Subsystems|Link]]
   - Confluence as a prerequisite proved before termination or typing
   - Higher-order rewriting and rewriting modulo β-equivalence : [[Decidability-via-Effective-Subsystems|Link]]
   - Miller's pattern unification as the tractable fragment for left-hand sides
   - Static versus definable symbols and injectivity : [[Decidability-via-Effective-Subsystems|Link]]
   - Most general typing substitutions for non-well-typed left-hand sides : [[Decidability-via-Effective-Subsystems|Link]]
   - The effectiveness theorem linking confluence and termination to decidable type-checking

4. **The Dedukti System and Concrete Syntax** : [[The-Dedukti-System-and-Concrete-Syntax|Link]]
   - Dedukti as a proof-checker rather than a proof-development environment
   - Variable and rewrite-rule declaration syntax
   - Definable symbols, static symbols, wildcards, and guards : [[Decidability-via-Effective-Subsystems|Link]]
   - Confluence checking deferred to external tools via TPDB export : [[The-Dedukti-System-and-Concrete-Syntax|Link]]

5. **Embedding Predicate Logic in a Logical Framework** : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
   - Language, term, and proposition embeddings : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
   - Propositions as types versus propositions as a subtype of types (the epsilon embedding)
   - Deep encoding via a universe of propositions versus shallow Type-level encoding
   - Deduction modulo theory as rewrite-rule-defined connectives and quantifiers : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]
   - Comprehension schemes and skolemization : [[Embedding-Predicate-Logic-in-a-Logical-Framework|Link]]

6. **Classical Logic via Double-Negation Connectives** : [[Classical-Logic-via-Double-Negation-Connectives|Link]]
   - The distinction between classical proofs and classical connectives
   - Negative translation and the introduction of an explicit atom-embedding connective
   - Defining classical connectives and quantifiers from constructive ones : [[Classical-Logic-via-Double-Negation-Connectives|Link]]
   - Avoiding critical pairs when translating classical rewrite rules : [[Classical-Logic-via-Double-Negation-Connectives|Link]]
   - Zenon and Zenon Modulo as tableaux-based classical proof producers : [[Classical-Logic-via-Double-Negation-Connectives|Link]]

7. **Simple Type Theory and Pure Type Systems** : [[Simple-Type-Theory-and-Pure-Type-Systems|Link]]
   - Simple type theory as an independent system versus as an instance of a Pure type system : [[Simple-Type-Theory-and-Pure-Type-Systems|Link]]
   - Indexing quantifiers and connectives by a term-level representation of types
   - Pure type system specifications via sorts, axioms, and rules
   - Tarski-style universes and the embedding of terms, types, and contexts : [[Simple-Type-Theory-and-Pure-Type-Systems|Link]]
   - Preservation of computation, preservation of typing, and conservativity results

8. **Embedding Programming Languages** : [[Embedding-Programming-Languages|Link]]
   - Shallow embeddings preserving binding, typing, and operational semantics
   - The untyped and simply-typed λ-calculus with an explicit fixpoint operator
   - The ς-calculus, object records, and the preobject technique for partial construction : [[Embedding-Programming-Languages|Link]]
   - ML pattern matching via destructors and recursion via a call-freezing operator : [[Embedding-Programming-Languages|Link]]
   - FoCaLiZe as a certified-program environment delegating proofs to Zenon Modulo

9. **Inductive Types and Universe Hierarchies** : [[Inductive-Types-and-Universe-Hierarchies|Link]]
   - Constructors and primitive recursion/elimination operators (Gödel's system T style)
   - The Calculus of Inductive Constructions as an extension with inductive types
   - Cumulative universe hierarchies and explicit lifting operators : [[Inductive-Types-and-Universe-Hierarchies|Link]]
   - Ensuring unique term representations under cumulativity
   - Matita's Calculus of Constructions with universes and proof irrelevance

10. **Interoperability and Reverse Engineering of Proofs** : [[Interoperability-and-Reverse-Engineering-of-Proofs|Link]]
    - Translating and checking large external proof libraries as validation of expressivity
    - The role of a small trusted kernel in auditing proofs from independent systems
    - Combining lemmas developed in different theories and systems : [[Interoperability-and-Reverse-Engineering-of-Proofs|Link]]
    - Reverse engineering as identifying the minimal theory a proof actually needs

---
