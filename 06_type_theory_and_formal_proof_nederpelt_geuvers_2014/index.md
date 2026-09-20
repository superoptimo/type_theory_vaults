# Type Theory and Formal Proof: An Introduction — Index

[[book-guidelines|↩ Back to guidelines]]

1. **The Untyped Lambda Calculus** : [[The-Untyped-Lambda-Calculus|Link]]
   - Functions as abstraction and application : [[The-Untyped-Lambda-Calculus|Link]]
   - Syntax of lambda terms and subterm structure : [[The-Untyped-Lambda-Calculus|Link]]
   - Free and bound variables and variable binding : [[The-Untyped-Lambda-Calculus|Link]]
   - Alpha conversion and renaming of bound variables : [[The-Untyped-Lambda-Calculus|Link]]
   - Capture avoiding substitution
   - Beta reduction and redex contraction : [[The-Untyped-Lambda-Calculus|Link1]], [[Metatheory-of-Typed-Lambda-Calculi|Link2]], [[Formal-Definitions-in-Type-Theory|Link3]]
   - Normal forms and normalisation : [[Metatheory-of-Typed-Lambda-Calculi|Link1]], [[The-Untyped-Lambda-Calculus|Link2]], [[Formalising-Elementary-Mathematics|Link3]]
   - Church–Rosser theorem and confluence
   - Fixed points and fixed point combinators : [[The-Untyped-Lambda-Calculus|Link]]
   - Church numerals and data encodings
   - Turing completeness and Church's thesis

2. **The Simply Typed Lambda Calculus** : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Simple types and arrow types : [[The-Simply-Typed-Lambda-Calculus|Link1]], [[The-Lambda-Cube-of-Type-Systems|Link2]]
   - Explicit typing à la Church and implicit typing à la Curry
   - Derivation rules for variables application and abstraction
   - Tree style and flag style derivations : [[The-Simply-Typed-Lambda-Calculus|Link]]
   - Well typedness type checking and term finding problems
   - Uniqueness of types and subject reduction : [[Metatheory-of-Typed-Lambda-Calculi|Link]]
   - Strong normalisation of typed terms : [[Metatheory-of-Typed-Lambda-Calculi|Link]]

3. **The Lambda Cube of Type Systems** : [[The-Lambda-Cube-of-Type-Systems|Link]]
   - Second order abstraction and application in $\lambda 2$ : [[The-Untyped-Lambda-Calculus|Link]]
   - Pi types as binders for types : [[The-Lambda-Cube-of-Type-Systems|Link]]
   - Type constructors and kinds in $\lambda\omega$ : [[The-Lambda-Cube-of-Type-Systems|Link]]
   - Types depending on terms in $\lambda P$ : [[The-Lambda-Cube-of-Type-Systems|Link]]
   - Calculus of Constructions as the union of all extensions : [[The-Lambda-Cube-of-Type-Systems|Link]]
   - Barendregt cube and pure type systems : [[The-Lambda-Cube-of-Type-Systems|Link]]
   - Sorts and admissible formation rule combinations

4. **Metatheory of Typed Lambda Calculi** : [[Metatheory-of-Typed-Lambda-Calculi|Link]]
   - Free variables thinning condensing and permutation lemmas : [[Metatheory-of-Typed-Lambda-Calculi|Link]]
   - Generation lemma and syntax directedness : [[Metatheory-of-Typed-Lambda-Calculi|Link]]
   - Substitution lemma : [[Metatheory-of-Typed-Lambda-Calculi|Link1]], [[The-Simply-Typed-Lambda-Calculus|Link2]]
   - Subject reduction and type reduction : [[Metatheory-of-Typed-Lambda-Calculi|Link]]
   - Conversion rule and uniqueness of types up to conversion : [[Metatheory-of-Typed-Lambda-Calculi|Link]]
   - Weak and strong normalisation : [[Metatheory-of-Typed-Lambda-Calculi|Link]]
   - Confluence and uniqueness of normal forms : [[Metatheory-of-Typed-Lambda-Calculi|Link1]], [[The-Untyped-Lambda-Calculus|Link2]]
   - Decidability of type checking and undecidability of inhabitation : [[Metatheory-of-Typed-Lambda-Calculi|Link]]

5. **The Curry–Howard Isomorphism** : [[The-Curry-Howard-Isomorphism|Link]]
   - Propositions as types interpretation : [[The-Curry-Howard-Isomorphism|Link1]], [[Formal-Proof-Development-in-Practice|Link2]]
   - Proofs as terms and proof objects : [[The-Curry-Howard-Isomorphism|Link]]
   - Implication as function type : [[The-Curry-Howard-Isomorphism|Link]]
   - Universal quantification as Pi type : [[The-Curry-Howard-Isomorphism|Link]]
   - Second order encodings of conjunction disjunction and existence
   - Absurdity and negation : [[The-Curry-Howard-Isomorphism|Link]]
   - Classical logic via excluded middle or double negation : [[The-Curry-Howard-Isomorphism|Link]]

6. **Natural Deduction in Flag Style** : [[Natural-Deduction-in-Flag-Style|Link]]
   - Introduction and elimination rules for the connectives : [[Natural-Deduction-in-Flag-Style|Link]]
   - Flag style proofs with contexts and scope
   - Constructive propositional and predicate logic : [[Natural-Deduction-in-Flag-Style|Link]]
   - Classical propositional and predicate logic : [[Natural-Deduction-in-Flag-Style|Link]]
   - Alternative rules for disjunction and existence : [[Natural-Deduction-in-Flag-Style|Link]]
   - Proof by contradiction : [[Natural-Deduction-in-Flag-Style|Link]]

7. **Formal Definitions in Type Theory** : [[Formal-Definitions-in-Type-Theory|Link]]
   - Nature and purpose of mathematical definitions
   - Descriptive definitions with definiendum and definiens : [[Formal-Definitions-in-Type-Theory|Link]]
   - Primitive definitions for axioms and axiomatic notions : [[Formal-Definitions-in-Type-Theory|Link]]
   - Parameter lists and instantiation : [[Formal-Definitions-in-Type-Theory|Link]]
   - Definition unfolding and delta reduction : [[Formal-Definitions-in-Type-Theory|Link]]
   - Delta conversion and beta delta conversion : [[Formal-Definitions-in-Type-Theory|Link]]
   - Extended judgements with environments : [[Formal-Definitions-in-Type-Theory|Link]]
   - Derivation rules for adding and instantiating definitions : [[Formal-Definitions-in-Type-Theory|Link]]
   - Naming proofs and applying theorems : [[Sets-Relations-and-Maps|Link1]], [[Formal-Definitions-in-Type-Theory|Link2]]
   - Normalisation and confluence in $\lambda D$ : [[Formal-Definitions-in-Type-Theory|Link]]

8. **Formalising Elementary Mathematics** : [[Formalising-Elementary-Mathematics|Link]]
   - Leibniz equality and its properties : [[Formalising-Elementary-Mathematics|Link1]], [[Arithmetic-in-Type-Theory|Link2]]
   - Substitutivity and congruence : [[Formalising-Elementary-Mathematics|Link]]
   - Partial orders and order relations : [[Formalising-Elementary-Mathematics|Link]]
   - Unique existence quantifiers : [[Formalising-Elementary-Mathematics|Link]]
   - The iota descriptor operator : [[Formalising-Elementary-Mathematics|Link]]
   - Irrelevance of proof : [[Arithmetic-in-Type-Theory|Link1]], [[Formalising-Elementary-Mathematics|Link2]]
   - Mathematical statements in definition format : [[Natural-Deduction-in-Flag-Style|Link]]

9. **Sets Relations and Maps** : [[Sets-Relations-and-Maps|Link]]
   - Sets as types and subsets as predicates : [[Sets-Relations-and-Maps|Link]]
   - Powerset and elementhood
   - Set operations and special subsets : [[Sets-Relations-and-Maps|Link]]
   - Equivalence relations and equivalence classes : [[Sets-Relations-and-Maps|Link]]
   - Maps as functional relations : [[Sets-Relations-and-Maps|Link]]
   - Injectivity surjectivity and bijectivity
   - Image and origin of a subset : [[Sets-Relations-and-Maps|Link]]

10. **Arithmetic in Type Theory** : [[Arithmetic-in-Type-Theory|Link]]
    - Peano axioms for the natural numbers : [[Arithmetic-in-Type-Theory|Link]]
    - Axiomatic introduction of the integers : [[Arithmetic-in-Type-Theory|Link]]
    - Symmetric induction over the integers : [[Arithmetic-in-Type-Theory|Link]]
    - Recursion theorem for $\mathbb{Z}$ : [[Arithmetic-in-Type-Theory|Link]]
    - Addition subtraction and opposites : [[Arithmetic-in-Type-Theory|Link]]
    - Multiplication and distributivity : [[Arithmetic-in-Type-Theory|Link]]
    - Inequality relations on the integers : [[Arithmetic-in-Type-Theory|Link]]
    - Divisibility and greatest common divisor : [[Arithmetic-in-Type-Theory|Link]]
    - Minimum and maximum theorems : [[Arithmetic-in-Type-Theory|Link]]
    - Division theorem with quotient and remainder

11. **Formal Proof Development in Practice** : [[Formal-Proof-Development-in-Practice|Link]]
    - Bézout's Lemma as a worked example : [[Formal-Proof-Development-in-Practice|Link]]
    - Proof specialisation by parameter instantiation : [[Formal-Proof-Development-in-Practice|Link]]
    - Holes and deferred proof obligations : [[Formal-Proof-Development-in-Practice|Link]]
    - Skeleton proofs and proof hints : [[Formal-Proof-Development-in-Practice|Link]]
    - Fully detailed formal proofs : [[Formal-Proof-Development-in-Practice|Link]]

12. **Proof Assistants and the Future of Formalisation** : [[Proof-Assistants-and-the-Future-of-Formalisation|Link]]
    - Automath and the de Bruijn criterion : [[Proof-Assistants-and-the-Future-of-Formalisation|Link]]
    - Proof checking as type checking : [[Metatheory-of-Typed-Lambda-Calculi|Link1]], [[The-Curry-Howard-Isomorphism|Link2]]
    - Interactive proving with tactics : [[Proof-Assistants-and-the-Future-of-Formalisation|Link]]
    - Libraries of formalised mathematics : [[Proof-Assistants-and-the-Future-of-Formalisation|Link]]
    - Automation and machine learning for proving
    - High level explanation of formal proofs

---
