# Towards a Practical Programming Language Based on Dependent Type Theory — Index

[[book-guidelines|↩ Back to guidelines]]

1. **Dependent Type Theory Foundations** : [[Dependent-Type-Theory-Foundations|Link]]
   - The theory $UTT_\Sigma$: dependent function and pair types : [[Dependent-Type-Theory-Foundations|Link]]
   - Telescopes as dependency-ordered sequences of types
   - Universe hierarchy and cumulativity : [[Dependent-Type-Theory-Foundations|Link]]
   - Subtyping between universes : [[Dependent-Type-Theory-Foundations|Link]]
   - Bidirectional type checking and type inference : [[Dependent-Type-Theory-Foundations|Link]]
   - Weak head normal form and conversion checking : [[Dependent-Type-Theory-Foundations|Link]]
   - Inductive families of datatypes : [[Dependent-Type-Theory-Foundations|Link]]
   - The identity type and uniqueness of identity proofs : [[Dependent-Type-Theory-Foundations|Link]]
   - The K axiom : [[Dependent-Type-Theory-Foundations|Link1]], [[Pattern-Matching-over-Inductive-Families|Link2]]
   - Record types encoded via Sigma types : [[Dependent-Type-Theory-Foundations|Link]]
   - Implicit function spaces : [[Dependent-Type-Theory-Foundations|Link1]], [[The-Agda-Language|Link2]]

2. **Pattern Matching over Inductive Families** : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Pattern matching instantiating both goal type and context
   - Accessible versus inaccessible patterns : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Context mappings as substitutions given by patterns
   - Matching, unification, and context splitting : [[Pattern-Matching-over-Inductive-Families|Link]]
   - The external versus internal approach to checking pattern matching : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Overlapping and prioritized clauses compiled to case trees
   - Coverage checking and the covering algorithm : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Caseless versus empty datatypes and refutation of impossible cases
   - Reduction of pattern matching to elimination rules via the K axiom : [[Pattern-Matching-over-Inductive-Families|Link]]
   - The `with` construct for matching on intermediate results : [[Pattern-Matching-over-Inductive-Families|Link]]
   - Views as a pattern for emulating non-standard case analysis : [[Pattern-Matching-over-Inductive-Families|Link]]

3. **Metavariables and Implicit Arguments** : [[Metavariables-and-Implicit-Arguments|Link]]
   - Metavariables standing for undetermined terms
   - Well-typed approximation of ill-typed intermediate terms
   - Guarded constants carrying a candidate value and a constraint : [[Metavariables-and-Implicit-Arguments|Link]]
   - Constraint generation and postponement during conversion checking
   - Restricted pattern unification for instantiating metavariables : [[Metavariables-and-Implicit-Arguments|Link]]
   - Soundness and termination of type checking with metavariables : [[Metavariables-and-Implicit-Arguments|Link1]], [[The-Agda-Language|Link2]]
   - Consistent signatures and constraint solving as signature extension
   - Implicit function spaces versus intersection types : [[The-Agda-Language|Link1]], [[Dependent-Type-Theory-Foundations|Link2]]
   - Automatic insertion of metavariables for omitted implicit arguments : [[Metavariables-and-Implicit-Arguments|Link]]

4. **Module Systems for Dependently Typed Languages** : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Separation of scope checking from type checking
   - Hierarchical modules, qualified names, and opening modules : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Private definitions and their effect on displayed normal forms : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Name modifiers: using, hiding, and renaming : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Re-exporting names with public opens : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Parameterised modules as sections with abstracted telescopes : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Module application and the open-module shorthand : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Splitting programs across files via import : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Records as parameterised projection modules : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Record subtyping and its interaction with metavariables : [[Module-Systems-for-Dependently-Typed-Languages|Link]]
   - Scope-checking algorithm: scope stacks and name spaces : [[Dependent-Type-Theory-Foundations|Link]]
   - Type-checking translation of sections and module applications : [[Module-Systems-for-Dependently-Typed-Languages|Link]]

5. **The Agda Language** : [[The-Agda-Language|Link]]
   - Names, operators, and mixfix syntax : [[The-Agda-Language|Link]]
   - Interaction points as unsolved metavariables : [[The-Agda-Language|Link]]
   - Implicit syntax and underscore placeholders : [[The-Agda-Language|Link]]
   - Datatype and function declarations with strict positivity : [[The-Agda-Language|Link]]
   - Inductive families and dotted (inaccessible) patterns : [[The-Agda-Language|Link]]
   - Record declarations and generated projection modules : [[The-Agda-Language|Link]]
   - Local and private helper definitions : [[The-Agda-Language|Link]]
   - Mutual inductive-recursive definitions : [[The-Agda-Language|Link]]
   - An internal certified solver for commutative monoid equations : [[The-Agda-Language|Link]]
   - Normalisation of monoid expressions and soundness of normalisation
   - Chain reasoning combinators for equational proofs

6. **Connecting Type Theory to First-Order Automation** : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - The logical framework $MLF_{Prop}$ with propositions and proof types : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - Translation of open formulas to first-order logic : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - Geometrical formulas and their intuitionistic clausification : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - The resolution and restricted paramodulation calculus : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - Well-typedness preservation under unification and resolution
   - The conservativity theorem connecting FOL proofs to framework derivations
   - The plug-in mechanism for external tool integration : [[Connecting-Type-Theory-to-First-Order-Automation|Link]]
   - The FOL plug-in and the Gandalf theorem prover
   - Human-readable proof traces as a design goal

7. **Related and Prior Work in Type Theory Implementations** : [[Related-and-Prior-Work-in-Type-Theory-Implementations|Link]]
   - Cayenne and undecidable type checking under general recursion
   - McBride's thesis and the Epigram programming model : [[Related-and-Prior-Work-in-Type-Theory-Implementations|Link]]
   - The Delphin language and higher-order pattern matching
   - Coq as a programming language and the Russell layer : [[Related-and-Prior-Work-in-Type-Theory-Implementations|Link]]
   - Module systems of Haskell, Cayenne, and Coq compared
   - Dependent ML, GADTs, and other limited dependent extensions

---
