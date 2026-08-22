# Type Theory and Functional Programming — Index

[[book-guidelines|↩ Back to guidelines]]

1. **[[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|The Curry–Howard Isomorphism (Propositions as Types)]]**
   - [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Judgements of the form p : P]]
   - Proof objects for the logical connectives
   - [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Propositions as tasks versus a truth-functional semantics]]
   - [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Formation, introduction, elimination and computation rules]]
   - Extracting programs from constructive proofs

2. **[[Natural-Deduction-and-Predicate-Logic|Natural Deduction and Predicate Logic]]**
   - [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|Introduction and elimination rules for the connectives]]
   - [[Natural-Deduction-and-Predicate-Logic|Discharge of assumptions]]
   - [[Natural-Deduction-and-Predicate-Logic|Rules for the quantifiers and variable capture]]
   - Classical extensions: excluded middle, double negation, proof by contradiction

3. **[[The-Lambda-Calculus|The Lambda Calculus]]**
   - The untyped $\lambda$-calculus, reduction and normal forms
   - [[The-Lambda-Calculus|The Church–Rosser property]]
   - [[The-Lambda-Calculus|Convertibility and $\beta$/$\eta$-conversion]]
   - [[The-Lambda-Calculus|The simply typed $\lambda$-calculus and strong normalisation]]
   - [[The-Lambda-Calculus|The reducibility (Tait) method]]

4. **[[Constructive-Mathematics|Constructive Mathematics]]**
   - Existence proofs and the rejection of proof by contradiction
   - [[Constructive-Mathematics|The principle of complete presentation]]
   - [[Constructive-Mathematics|Constructive typing of mathematical objects]]
   - [[Constructive-Mathematics|Apartness in place of inequality]]

5. **[[The-Formal-System-of-Type-Theory-(TT0)|The Formal System of Type Theory ($TT_0$)]]**
   - [[The-Formal-System-of-Type-Theory-(TT0)|Judgements, proofs and derivations]]
   - [[Equality-in-Type-Theory|The four kinds of rule for each type former]]
   - [[The-Formal-System-of-Type-Theory-(TT0)|The identity (equality) type]]
   - [[The-Formal-System-of-Type-Theory-(TT0)|Convertibility and the rules of substitution]]

6. **[[Base-Types-and-Data-Types|Base Types and Data Types]]**
   - [[Base-Types-and-Data-Types|Booleans and finite types]]
   - [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)|The unit and empty types]]
   - [[The-Lambda-Calculus|Natural numbers and primitive recursion]]
   - [[Base-Types-and-Data-Types|Well-founded algebraic types such as trees]]

7. **[[Quantifiers-and-Dependent-Types|Quantifiers and Dependent Types]]**
   - [[Quantifiers-and-Dependent-Types|The dependent function type as universal quantifier]]
   - [[Quantifiers-and-Dependent-Types|The dependent sum type as existential quantifier]]
   - [[Quantifiers-and-Dependent-Types|Curried versus uncurried representations]]
   - [[Programming-in-Type-Theory|Weak versus strong elimination rules for disjunction and existence]]

8. **[[Contexts,-Derivability-and-Type-Uniqueness|Contexts, Derivability and Type Uniqueness]]**
   - [[Contexts,-Derivability-and-Type-Uniqueness|Assumptions, discharge and consistency of contexts]]
   - [[Contexts,-Derivability-and-Type-Uniqueness|Naming and abbreviation conventions]]
   - [[Contexts,-Derivability-and-Type-Uniqueness|Derivability of "A is a type" from "a : A"]]
   - [[Contexts,-Derivability-and-Type-Uniqueness|Uniqueness of types]]

9. **[[Normalisation-and-Computational-Properties|Normalisation and Computational Properties]]**
   - [[Normalisation-and-Computational-Properties|Restricted reduction and the system $TT_0^*$]]
   - [[Normalisation-and-Computational-Properties|Combinator and supercombinator abstraction; the system $TT_0^c$]]
   - [[Normalisation-and-Computational-Properties|The normalisation theorem and its corollaries]]
   - Decidability of convertibility and of derivability

10. **[[Equality-in-Type-Theory|Equality in Type Theory]]**
    - [[Equality-in-Type-Theory|Definitional equality, convertibility, and the identity type]]
    - [[Programming-in-Type-Theory|Equality functions and formal decidability]]
    - [[Equality-in-Type-Theory|Extensional equality defined inside an intensional theory]]
    - [[Equality-in-Type-Theory|Martin-Löf's extensional identity rule and its cost]]

11. **[[Universes-and-Well-Founded-Types|Universes and Well-Founded Types]]**
    - The hierarchy of universes and Girard's paradox
    - [[Universes-and-Well-Founded-Types|Type families and quantification over a universe]]
    - [[Universes-and-Well-Founded-Types|Closure axioms and parametricity]]
    - [[Universes-and-Well-Founded-Types|The W type and its relation to algebraic types]]

12. **[[Programming-in-Type-Theory|Programming in Type Theory]]**
    - [[Programming-in-Type-Theory|Course-of-values recursion]]
    - Verified program development
    - Dependent types for vectors, modules and type classes
    - [[Programming-in-Type-Theory|Program transformation and tail-recursive (imperative) form]]

13. **[[Specification-in-Type-Theory|Specification in Type Theory]]**
    - [[Specification-in-Type-Theory|What a specification is]]
    - [[Specification-in-Type-Theory|Skolemising the quantifiers of a specification]]
    - [[Specification-in-Type-Theory|Computational irrelevance and lazy evaluation]]
    - [[Specification-in-Type-Theory|Proof extraction and top-down derivation]]

14. **[[The-Subset-Type-and-Its-Difficulties|The Subset Type and Its Difficulties]]**
    - [[The-Subset-Type-and-Its-Difficulties|The naive subset type and its weak elimination rule]]
    - [[The-Formal-System-of-Type-Theory-(TT0)|Non-derivability results for subset comprehension]]
    - [[The-Subset-Type-and-Its-Difficulties|Propositions as distinct from types]]
    - [[The-Subset-Type-and-Its-Difficulties|Whether subsets are necessary at all]]

15. **[[Quotient-and-Congruence-Types|Quotient and Congruence Types]]**
    - The quotient type formed from a base type and an equivalence relation
    - [[Quotient-and-Congruence-Types|Congruence types]]
    - [[Quotient-and-Congruence-Types|Case study: the rationals and the constructive real numbers]]

16. **[[Strengthened-and-Polymorphic-Rules|Strengthened and Polymorphic Rules]]**
    - [[Programming-in-Type-Theory|Strong elimination rules and hypothetical hypotheses]]
    - [[Strengthened-and-Polymorphic-Rules|The polymorphic type constructor]]
    - [[Strengthened-and-Polymorphic-Rules|Non-termination introduced by extensional polymorphism]]

17. **[[Well-Founded-and-General-Recursion|Well-Founded and General Recursion]]**
    - [[Well-Founded-and-General-Recursion|Well-founded orderings and the accessible part of a relation]]
    - [[Well-Founded-and-General-Recursion|Adding well-founded recursion to type theory]]
    - [[Well-Founded-and-General-Recursion|Inductively defined types as least fixed points]]
    - [[Well-Founded-and-General-Recursion|Co-inductive types, streams and partial objects]]

18. **[[Foundations-and-Related-Systems|Foundations and Related Systems]]**
    - Realizability and conservativity over Heyting Arithmetic
    - Model theory: term models, type-free interpretations, inductive definitions
    - The inversion principle relating introduction and elimination rules
    - Related systems: Nuprl, TK, PX, AUTOMATH, System F, the Calculus of Constructions

---
