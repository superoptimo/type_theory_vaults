# Certified Programming with Dependent Types — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The Coq Proof Assistant and Certified Programming** : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - Certified versus certifying programs
   - Comparison of proof assistants : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - The de Bruijn criterion : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - Coq versus Agda and Epigram : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - Design patterns for readable and maintainable proofs : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link]]
   - The Calculus of Inductive Constructions and Gallina : [[Techniques-for-General-Recursion|Link]]
   - Strong normalization and relative consistency

2. **The Curry–Howard Correspondence** : [[The-Curry-Howard-Correspondence|Link]]
   - Proofs as programs and propositions as types
   - Propositional and first-order logic encoded as inductive types
   - Constructive versus classical logic
   - Program extraction from constructive proofs : [[The-Curry-Howard-Correspondence|Link]]

3. **Inductive Types** : [[Inductive-Types|Link]]
   - Enumerations and simple recursive types : [[Inductive-Types|Link]]
   - Parameterized and polymorphic types : [[Inductive-Types|Link]]
   - Mutually inductive types and their induction principles : [[Inductive-Types|Link]]
   - Reflexive types and higher-order abstract syntax : [[Reasoning-About-Programming-Language-Syntax|Link1]], [[Inductive-Types|Link2]]
   - The strict positivity requirement : [[Inductive-Types|Link]]
   - Nested inductive types : [[Inductive-Types|Link]]
   - Manual construction of induction principles : [[Coinductive-Types-and-Infinite-Data|Link1]], [[Datatype-Generic-Programming|Link2]]

4. **Inductive Predicates and Judgments** : [[Inductive-Predicates-and-Judgments|Link]]
   - Judgments as inductively defined predicates : [[Inductive-Predicates-and-Judgments|Link]]
   - Equality as an inductive type : [[Inductive-Types|Link]]
   - Rule induction : [[Inductive-Predicates-and-Judgments|Link]]
   - Quantifier ordering and its effect on induction hypotheses : [[The-Curry-Howard-Correspondence|Link1]], [[Inductive-Predicates-and-Judgments|Link2]]
   - Case analysis pitfalls of destruct versus inversion : [[Inductive-Predicates-and-Judgments|Link]]

5. **Coinductive Types and Infinite Data** : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Streams and co-fixpoints : [[Coinductive-Types-and-Infinite-Data|Link]]
   - The guardedness condition and productivity : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Bisimulation and co-inductive equality : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Co-induction principles : [[Coinductive-Types-and-Infinite-Data|Link]]
   - Co-inductive operational semantics for non-termination : [[Techniques-for-General-Recursion|Link]]

6. **Dependent Types for Program Correctness** : [[Dependent-Types-for-Program-Correctness|Link]]
   - Subset types and proof erasure : [[Dependent-Types-for-Program-Correctness|Link]]
   - Decidable propositions and sumbool : [[Dependent-Types-for-Program-Correctness|Link1]], [[Proof-by-Reflection|Link2]]
   - Partial subset types and sumor
   - Monadic notations for dependently typed computation
   - Certified type checkers
   - Length-indexed lists and the fin index type
   - Heterogeneous lists and the member type family : [[Dependent-Types-for-Program-Correctness|Link]]
   - The convoy pattern : [[Dependent-Types-for-Program-Correctness|Link]]
   - Dependently typed red-black trees : [[Dependent-Types-for-Program-Correctness|Link]]
   - Certified regular expression matching : [[Dependent-Types-for-Program-Correctness|Link]]
   - The one rule of dependent pattern matching : [[Dependent-Types-for-Program-Correctness|Link]]
   - Tagless interpreters via type-indexed syntax
   - Recursive versus reflexive encodings of dependent data structures : [[Dependent-Types-for-Program-Correctness|Link]]

7. **Techniques for General Recursion** : [[Techniques-for-General-Recursion|Link]]
   - Well-founded recursion and the accessibility predicate : [[Techniques-for-General-Recursion|Link]]
   - Domain-theoretic non-termination monads : [[Techniques-for-General-Recursion|Link]]
   - Co-inductive non-termination monads : [[Techniques-for-General-Recursion|Link]]
   - Comparing general recursion encodings : [[Techniques-for-General-Recursion|Link]]

8. **Reasoning About Equality Proofs** : [[Reasoning-About-Equality-Proofs|Link]]
   - Definitional versus propositional equality
   - Unicity of identity proofs and Streicher's axiom K
   - Heterogeneous equality : [[Reasoning-About-Equality-Proofs|Link]]
   - Equivalence of Coq's equality axioms
   - Function extensionality : [[Reasoning-About-Equality-Proofs|Link]]

9. **Datatype-Generic Programming** : [[Datatype-Generic-Programming|Link]]
   - Reifying datatype definitions as universe types : [[Datatype-Generic-Programming|Link]]
   - Recursion schemes as reified induction principles : [[Datatype-Generic-Programming|Link]]
   - Generic proofs about generic programs : [[Datatype-Generic-Programming|Link]]

10. **Universes and Axioms** : [[Universes-and-Axioms|Link]]
    - The Type hierarchy and predicativity
    - Girard's paradox
    - Parameters versus indices in inductive definitions
    - The Prop universe and the elimination restriction
    - Impredicativity of Prop
    - Axioms of classical logic and choice
    - Axioms and stuck computation : [[Universes-and-Axioms|Link]]
    - Techniques for avoiding axioms : [[Universes-and-Axioms|Link]]

11. **Proof Automation by Logic Programming** : [[Proof-Automation-by-Logic-Programming|Link]]
    - The auto and eauto tactics
    - Backtracking and unification in proof search : [[Proof-Automation-by-Logic-Programming|Link]]
    - Hint databases and hint kinds : [[Proof-Automation-by-Logic-Programming|Link]]
    - Program synthesis via inductive relations : [[Proof-Automation-by-Logic-Programming|Link]]
    - Rewrite hints and autorewrite : [[Proof-Automation-by-Logic-Programming|Link]]

12. **The Ltac Tactic Language** : [[The-Ltac-Tactic-Language|Link]]
    - The match goal construct and its backtracking semantics
    - Ltac as a functional and imperative hybrid language : [[The-Ltac-Tactic-Language|Link]]
    - Continuation-passing style in Ltac
    - Custom recursive proof search tactics : [[The-Ltac-Tactic-Language|Link]]
    - Explicit unification variable allocation and forward reasoning : [[The-Ltac-Tactic-Language|Link]]

13. **Proof by Reflection** : [[Proof-by-Reflection|Link]]
    - Verified decision procedures : [[Proof-by-Reflection|Link]]
    - Syntax reification of Gallina propositions
    - Injecting uninterpreted atoms into reified syntax
    - Reification under variable binders : [[Proof-by-Reflection|Link]]
    - Proof term size as a design metric

14. **Engineering Large Proof Developments** : [[Engineering-Large-Proof-Developments|Link]]
    - Ltac anti-patterns and maintainable proof style : [[The-Coq-Proof-Assistant-and-Certified-Programming|Link1]], [[Engineering-Large-Proof-Developments|Link2]]
    - Debugging and profiling proof automation
    - The Coq module system and functors
    - Build processes for multi-file projects

15. **Reasoning About Programming Language Syntax** : [[Reasoning-About-Programming-Language-Syntax|Link]]
    - Dependent de Bruijn indices : [[Reasoning-About-Programming-Language-Syntax|Link]]
    - Lifting and weakening operations
    - Higher-order abstract syntax and parametric HOAS : [[Reasoning-About-Programming-Language-Syntax|Link]]
    - Term well-formedness and parametricity
    - Verifying program transformations

---
