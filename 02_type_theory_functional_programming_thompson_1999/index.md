# Type Theory and Functional Programming — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The Curry–Howard Isomorphism (Propositions as Types)** : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Judgements of the form p : P : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link1]], [[The-Lambda-Calculus|Link2]]
   - Proof objects for the logical connectives
   - Propositions as tasks versus a truth-functional semantics : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Formation, introduction, elimination and computation rules : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Extracting programs from constructive proofs

2. **Natural Deduction and Predicate Logic** : [[Natural-Deduction-and-Predicate-Logic|Link]]
   - Introduction and elimination rules for the connectives : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Discharge of assumptions : [[Natural-Deduction-and-Predicate-Logic|Link]]
   - Rules for the quantifiers and variable capture : [[Natural-Deduction-and-Predicate-Logic|Link]]
   - Classical extensions: excluded middle, double negation, proof by contradiction

3. **The Lambda Calculus** : [[The-Lambda-Calculus|Link]]
   - The untyped $\lambda$-calculus, reduction and normal forms
   - The Church–Rosser property : [[The-Lambda-Calculus|Link]]
   - Convertibility and $\beta$/$\eta$-conversion : [[The-Lambda-Calculus|Link1]], [[The-Formal-System-of-Type-Theory-(TT0)|Link2]], [[Contexts,-Derivability-and-Type-Uniqueness|Link3]]
   - The simply typed $\lambda$-calculus and strong normalisation : [[The-Lambda-Calculus|Link]]
   - The reducibility (Tait) method : [[The-Lambda-Calculus|Link]]

4. **Constructive Mathematics** : [[Constructive-Mathematics|Link]]
   - Existence proofs and the rejection of proof by contradiction
   - The principle of complete presentation : [[Constructive-Mathematics|Link]]
   - Constructive typing of mathematical objects : [[Constructive-Mathematics|Link]]
   - Apartness in place of inequality : [[Constructive-Mathematics|Link]]

5. **The Formal System of Type Theory ($TT_0$)** : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
   - Judgements, proofs and derivations : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
   - The four kinds of rule for each type former : [[Equality-in-Type-Theory|Link]]
   - The identity (equality) type : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
   - Convertibility and the rules of substitution : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]

6. **Base Types and Data Types** : [[Base-Types-and-Data-Types|Link]]
   - Booleans and finite types : [[Base-Types-and-Data-Types|Link]]
   - The unit and empty types : [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Link]]
   - Natural numbers and primitive recursion : [[The-Lambda-Calculus|Link]]
   - Well-founded algebraic types such as trees : [[Base-Types-and-Data-Types|Link]]

7. **Quantifiers and Dependent Types** : [[Quantifiers-and-Dependent-Types|Link]]
   - The dependent function type as universal quantifier : [[Quantifiers-and-Dependent-Types|Link]]
   - The dependent sum type as existential quantifier : [[Quantifiers-and-Dependent-Types|Link]]
   - Curried versus uncurried representations : [[Quantifiers-and-Dependent-Types|Link]]
   - Weak versus strong elimination rules for disjunction and existence : [[Programming-in-Type-Theory|Link1]], [[Quantifiers-and-Dependent-Types|Link2]]

8. **Contexts, Derivability and Type Uniqueness** : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Assumptions, discharge and consistency of contexts : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Naming and abbreviation conventions : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Derivability of "A is a type" from "a : A" : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]
   - Uniqueness of types : [[Contexts,-Derivability-and-Type-Uniqueness|Link]]

9. **Normalisation and Computational Properties** : [[Normalisation-and-Computational-Properties|Link]]
   - Restricted reduction and the system $TT_0^*$ : [[Normalisation-and-Computational-Properties|Link]]
   - Combinator and supercombinator abstraction; the system $TT_0^c$ : [[Normalisation-and-Computational-Properties|Link]]
   - The normalisation theorem and its corollaries : [[Normalisation-and-Computational-Properties|Link]]
   - Decidability of convertibility and of derivability

10. **Equality in Type Theory** : [[Equality-in-Type-Theory|Link]]
    - Definitional equality, convertibility, and the identity type : [[Equality-in-Type-Theory|Link1]], [[The-Formal-System-of-Type-Theory-(TT0)|Link2]]
    - Equality functions and formal decidability : [[Programming-in-Type-Theory|Link]]
    - Extensional equality defined inside an intensional theory : [[Equality-in-Type-Theory|Link]]
    - Martin-Löf's extensional identity rule and its cost : [[Equality-in-Type-Theory|Link]]

11. **Universes and Well-Founded Types** : [[Universes-and-Well-Founded-Types|Link]]
    - The hierarchy of universes and Girard's paradox
    - Type families and quantification over a universe : [[Universes-and-Well-Founded-Types|Link]]
    - Closure axioms and parametricity : [[Universes-and-Well-Founded-Types|Link]]
    - The W type and its relation to algebraic types : [[Universes-and-Well-Founded-Types|Link]]

12. **Programming in Type Theory** : [[Programming-in-Type-Theory|Link]]
    - Course-of-values recursion : [[Programming-in-Type-Theory|Link]]
    - Verified program development
    - Dependent types for vectors, modules and type classes
    - Program transformation and tail-recursive (imperative) form : [[Programming-in-Type-Theory|Link]]

13. **Specification in Type Theory** : [[Specification-in-Type-Theory|Link]]
    - What a specification is : [[Specification-in-Type-Theory|Link]]
    - Skolemising the quantifiers of a specification : [[Specification-in-Type-Theory|Link]]
    - Computational irrelevance and lazy evaluation : [[Specification-in-Type-Theory|Link]]
    - Proof extraction and top-down derivation : [[Specification-in-Type-Theory|Link]]

14. **The Subset Type and Its Difficulties** : [[The-Subset-Type-and-Its-Difficulties|Link]]
    - The naive subset type and its weak elimination rule : [[The-Subset-Type-and-Its-Difficulties|Link]]
    - Non-derivability results for subset comprehension : [[The-Formal-System-of-Type-Theory-(TT0)|Link]]
    - Propositions as distinct from types : [[The-Subset-Type-and-Its-Difficulties|Link]]
    - Whether subsets are necessary at all : [[The-Subset-Type-and-Its-Difficulties|Link]]

15. **Quotient and Congruence Types** : [[Quotient-and-Congruence-Types|Link]]
    - The quotient type formed from a base type and an equivalence relation
    - Congruence types : [[Quotient-and-Congruence-Types|Link]]
    - Case study: the rationals and the constructive real numbers : [[Quotient-and-Congruence-Types|Link]]

16. **Strengthened and Polymorphic Rules** : [[Strengthened-and-Polymorphic-Rules|Link]]
    - Strong elimination rules and hypothetical hypotheses : [[The-Inversion-Principle|Link1]], [[Programming-in-Type-Theory|Link2]], [[Quantifiers-and-Dependent-Types|Link3]], [[Strengthened-and-Polymorphic-Rules|Link4]]
    - The polymorphic type constructor : [[Strengthened-and-Polymorphic-Rules|Link]]
    - Non-termination introduced by extensional polymorphism : [[Strengthened-and-Polymorphic-Rules|Link1]], [[The-Subset-Type-and-Its-Difficulties|Link2]], [[Quantifiers-and-Dependent-Types|Link3]]

17. **Well-Founded and General Recursion** : [[Well-Founded-and-General-Recursion|Link]]
    - Well-founded orderings and the accessible part of a relation : [[Well-Founded-and-General-Recursion|Link]]
    - Adding well-founded recursion to type theory : [[Well-Founded-and-General-Recursion|Link]]
    - Inductively defined types as least fixed points : [[Well-Founded-and-General-Recursion|Link]]
    - Co-inductive types, streams and partial objects : [[Well-Founded-and-General-Recursion|Link1]], [[The-Lambda-Calculus|Link2]]

18. **Foundations and Related Systems** : [[Foundations-and-Related-Systems|Link]]
    - Realizability and conservativity over Heyting Arithmetic
    - Model theory: term models, type-free interpretations, inductive definitions
    - The inversion principle relating introduction and elimination rules
    - Related systems: Nuprl, TK, PX, AUTOMATH, System F, the Calculus of Constructions

---

---

## Extra Topics

Generated articles not (yet) matched to a Topic List entry in book-guidelines.md:

- [[Model-Theory|Model Theory]]
