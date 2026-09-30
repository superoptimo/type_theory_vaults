# Learning Roadmap — Type Theory

The `type-theory` Focus Area is the spine of the compiler project: it supplies the term/type representation, the kernel's `isDefEq`, the bidirectional elaborator with Miller-style metavariable unification, and the refinement-type surface language. The sequence below starts from computation and judgment forms, climbs through simple and polymorphic types into Martin-Löf dependent type theory (Π, Σ, identity, inductive families), then specializes into the mechanisms the compiler actually needs — definitional equality, bidirectional checking, pattern unification, Lean-style elaboration, refinement/subset types — and ends with semantic and foundational material (automata-based domains, categorical models, HoTT) that clarifies *why* the machinery is sound but is not on the critical path. Cross-area prerequisites (unification procedures, proof search, SAT/SMT) are referenced by name to the `automated-reasoning` and `sat-smt-csp` roadmaps rather than restated.

---

## 1. Computation, Lambda Calculus, and the Limits of Decidability (Core Topic)

#### Pre-requisites
None — entry point. Programming and compiler background is assumed.

#### Why this topic is important
Every later component (kernel, elaborator, abstract interpreter, CSP kernel) sits on a computation model whose termination, confluence and undecidability properties bound what it can promise. Church–Rosser is what `isDefEq` silently relies on when it normalizes and compares; Rice/halting are why your analyses must be sound-but-incomplete and why the CSP counterexample search is only semi-decidable. Later topics: 2, 3, 7, 15.

#### Sources to Study
1. [[04_TAPL_Pierce_2002/book-guidelines|Types and Programming Languages]]
   - [[04_TAPL_Pierce_2002/The-Untyped-Lambda-Calculus|The Untyped Lambda-Calculus]]
   - [[04_TAPL_Pierce_2002/Nameless-Representation-of-Terms|Nameless Representation of Terms]]
2. [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/book-guidelines|Type Theory and Formal Proof]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/The-Untyped-Lambda-Calculus|The Untyped Lambda Calculus]]
3. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming]]
   - [[02_type_theory_functional_programming_thompson_1999/The-Lambda-Calculus|The Lambda Calculus]]
4. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic]]
   - [[10_boolos_burgess_computability_logic_2007/Turing-and-Abacus-Computability|Turing and Abacus Computability]]
   - [[10_boolos_burgess_computability_logic_2007/Recursive-Function-Theory|Recursive Function Theory]]
   - [[10_boolos_burgess_computability_logic_2007/Uncomputability|Uncomputability]]
5. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages]]
   - [[07_practical_foundations_robert_harper_2012/Dynamic-Types-and-the-Untyped-Lambda-Calculus|Dynamic Types and the Untyped Lambda Calculus]]
6. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic]] (background)
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Representability-and-Recursive-Functions|Representability and Recursive Functions]]

#### Key Concepts and Definitions
1. $\beta$-reduction, redexes, normal forms; Church–Rosser (confluence) ⇒ at most one normal form.
2. $\alpha$-conversion and capture-avoiding substitution; de Bruijn (nameless) representation as the implementation strategy for binders.
3. Fixed-point combinators; Turing-completeness of the untyped calculus.
4. Turing/abacus machines, general recursive functions; Church–Turing thesis.
5. Halting problem, Rice's theorem, r.e. vs. recursive sets.

#### Relevant Questions
1. Why does every untyped $\lambda$-term have a fixed point, and why is that both expressive power and a source of undecidability?
2. What does Church–Rosser guarantee about outcomes regardless of reduction order, and why does a normalizing equality checker depend on it?
3. In what precise sense does Rice's theorem rule out a sound *and* complete static analyzer for a Turing-complete language?
4. What are the trade-offs between named, locally-nameless and de Bruijn representations for a Rust term type?

---

## 2. Judgments, Inductive Definitions, Binding, and Substitution (Core Topic)

#### Pre-requisites
1. Computation, Lambda Calculus, and the Limits of Decidability.

#### Why this topic is important
Judgment forms and rules are the shared ancestor of "a type checker" and "a proof checker": they are what your kernel implements and what rule induction proves things about. Hypothetical/general judgments give you contexts and weakening/substitution lemmas — the plumbing under both elaboration and Hoare-logic soundness. Type safety (progress + preservation) is the template for every soundness argument in the project. Later topics: 3–12.

#### Sources to Study
1. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages]]
   - [[07_practical_foundations_robert_harper_2012/Syntactic-Objects-and-Binding|Syntactic Objects and Binding]]
   - [[07_practical_foundations_robert_harper_2012/Inductive-Definitions-and-Rule-Induction|Inductive Definitions and Rule Induction]]
   - [[07_practical_foundations_robert_harper_2012/Hypothetical-and-General-Judgments|Hypothetical and General Judgments]]
   - [[07_practical_foundations_robert_harper_2012/Statics-And-Dynamics|Statics and Dynamics]]
   - [[07_practical_foundations_robert_harper_2012/Type-Safety|Type Safety]]
2. [[04_TAPL_Pierce_2002/book-guidelines|Types and Programming Languages]]
   - [[04_TAPL_Pierce_2002/Inductive-Definitions-and-Proof-Techniques|Inductive Definitions and Proof Techniques]]
   - [[04_TAPL_Pierce_2002/Operational-Semantics|Operational Semantics]]
   - [[04_TAPL_Pierce_2002/Type-Safety|Type Safety]]
   - [[04_TAPL_Pierce_2002/Canonical-Forms-Lemmas|Canonical Forms Lemmas]]
3. [[01_programming_in_MLTT/book-guidelines|Programming in Martin-Löf's Type Theory]]
   - [[01_programming_in_MLTT/The-Theory-of-Expressions|The Theory of Expressions]]
   - [[01_programming_in_MLTT/The-Semantics-of-Judgement-Forms|The Semantics of Judgement Forms]]
4. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory]]
   - [[84_type-theory-book_Daniel_Gratzer_2026/Judgments-and-the-Substitution-Calculus|Judgments and the Substitution Calculus]]
5. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Induction-and-Recursion-on-Freely-Generated-Sets|Induction and Recursion on Freely Generated Sets]]
6. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis]] — WHILE/FUN semantics (bridge to `static-analysis`)

#### Key Concepts and Definitions
1. Judgment, rule, derivation; inductive definition and rule induction.
2. Hypothetical vs. general judgments; contexts, weakening, exchange, contraction, substitution lemma.
3. Abstract binding trees; structural vs. transition (small-step) semantics; statics vs. dynamics.
4. Progress and preservation ⇒ type safety; canonical forms.
5. Explicit substitutions / the substitution calculus as the basis of dependent-type presentations.

#### Relevant Questions
1. Why is the substitution lemma the load-bearing lemma of preservation, and where does variable capture bite when you implement it?
2. How do a typing judgment $\Gamma \vdash e : \tau$ and a provability judgment $\Gamma \vdash A$ differ only in what is being tracked?
3. What is the difference between proving safety via progress/preservation and via a logical-relations argument?

---

## 3. Simply Typed $\lambda$-Calculus, Curry–Howard, and Normalization (Core Topic)

#### Pre-requisites
1. Judgments, Inductive Definitions, Binding, and Substitution.

#### Why this topic is important
STLC is the smallest language where the type checker and proof checker coincide, and strong normalization is what makes definitional equality decidable — your kernel's termination guarantee. Natural deduction ↔ typed terms is the proof-term reconstruction story used by the theorem prover (see `automated-reasoning` roadmap). Later topics: 4, 5, 7.

#### Sources to Study
1. [[04_TAPL_Pierce_2002/book-guidelines|Types and Programming Languages]]
   - [[04_TAPL_Pierce_2002/The-Simply-Typed-Lambda-Calculus|The Simply Typed Lambda-Calculus]]
   - [[04_TAPL_Pierce_2002/The-Curry-Howard-Correspondence|The Curry-Howard Correspondence]]
   - [[04_TAPL_Pierce_2002/Normalization|Normalization]]
   - [[04_TAPL_Pierce_2002/Core-Language-Extensions|Core Language Extensions]]
2. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types]]
   - [[03_proofs_and_types_girard_1989/Natural-Deduction|Natural Deduction]]
   - [[03_proofs_and_types_girard_1989/The-Curry-Howard-Isomorphism|The Curry-Howard Isomorphism]]
   - [[03_proofs_and_types_girard_1989/Normalisation-Theorems|Normalisation Theorems]]
   - [[03_proofs_and_types_girard_1989/Gödel's-System-T|Gödel's System T]]
3. [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/book-guidelines|Type Theory and Formal Proof]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/The-Simply-Typed-Lambda-Calculus|The Simply Typed Lambda Calculus]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/The-Curry-Howard-Isomorphism|The Curry–Howard Isomorphism]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Metatheory-of-Typed-Lambda-Calculi|Metatheory of Typed Lambda Calculi]]
4. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages]]
   - [[07_practical_foundations_robert_harper_2012/Function-Types-and-the-Lambda-Calculus|Function Types and the Lambda Calculus]]
   - [[07_practical_foundations_robert_harper_2012/Godels-System-T-and-Total-Computation|Gödel's System T and Total Computation]]
   - [[07_practical_foundations_robert_harper_2012/Plotkins-PCF-and-Partial-Computation|Plotkin's PCF and Partial Computation]]
   - [[07_practical_foundations_robert_harper_2012/Product-Types|Product Types]]
   - [[07_practical_foundations_robert_harper_2012/Sum-Types|Sum Types]]
   - [[07_practical_foundations_robert_harper_2012/Propositions-as-Types|Propositions as Types]]
5. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming]]
   - [[02_type_theory_functional_programming_thompson_1999/Natural-Deduction-and-Predicate-Logic|Natural Deduction and Predicate Logic]]
   - [[02_type_theory_functional_programming_thompson_1999/The-Curry-Howard-Isomorphism-(Propositions-as-Types)|The Curry-Howard Isomorphism]]
   - [[02_type_theory_functional_programming_thompson_1999/Normalisation-and-Computational-Properties|Normalisation and Computational Properties]]
6. [[60_Structural_Proof_Theory_Negri_Plato_2008/book-guidelines|Structural Proof Theory]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/The-Sequent-Calculus-Natural-Deduction-Isomorphism|The Sequent Calculus–Natural Deduction Isomorphism]]

#### Key Concepts and Definitions
1. STLC typing rules; $\beta\eta$-equality; type erasure.
2. Curry–Howard: implication ↔ function type, conjunction ↔ product, disjunction ↔ sum, $\bot$ ↔ empty type.
3. Weak vs. strong normalization; reducibility candidates / logical predicates.
4. System T: primitive recursion at higher type; totality vs. PCF's partiality.
5. Inversion principle and harmony of introduction/elimination rules.

#### Relevant Questions
1. Why can't a normalizing calculus be Turing-complete, and what does the compiler pay for the guarantee?
2. How does the reducibility-candidate proof of strong normalization get around the circularity of induction on types?
3. Why does the inversion principle say elimination rules are "justified" by introduction rules, and how does it shape rule design?

---

## 4. Polymorphism, System F, and the $\lambda$-Cube (Core Topic)

#### Pre-requisites
1. Simply Typed $\lambda$-Calculus, Curry–Howard, and Normalization.

#### Why this topic is important
The $\lambda$-cube organizes the ways types and terms can depend on each other; $\lambda\Pi$ (types depending on terms) is the corner your language lives in, and the Calculus of Constructions is the top. System F also underlies higher-rank inference (topic 8) and the parametricity reasoning used for abstraction.

#### Sources to Study
1. [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/book-guidelines|Type Theory and Formal Proof]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/The-Lambda-Cube-of-Type-Systems|The Lambda Cube of Type Systems]]
2. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types]]
   - [[03_proofs_and_types_girard_1989/System-F-and-Polymorphism|System F and Polymorphism]]
   - [[03_proofs_and_types_girard_1989/Semantics-of-System-F|Semantics of System F]]
3. [[04_TAPL_Pierce_2002/book-guidelines|Types and Programming Languages]]
   - [[04_TAPL_Pierce_2002/Universal-Types-(System-F)|Universal Types (System F)]]
   - [[04_TAPL_Pierce_2002/Existential-Types|Existential Types]]
   - [[04_TAPL_Pierce_2002/Type-Operators-and-Kinding|Type Operators and Kinding]]
   - [[04_TAPL_Pierce_2002/Higher-Order-Polymorphism-(System-F-omega)|Higher-Order Polymorphism (System $F^\omega$)]]
4. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages]]
   - [[07_practical_foundations_robert_harper_2012/Polymorphism-and-System-F|Polymorphism and System F]]
   - [[07_practical_foundations_robert_harper_2012/Data-Abstraction-and-Existential-Types|Data Abstraction and Existential Types]]
   - [[07_practical_foundations_robert_harper_2012/Constructors-and-Kinds|Constructors and Kinds]]
5. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/book-guidelines|Categorical Logic and Type Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Polymorphic-Type-Theory|Polymorphic Type Theory]]
6. [[05_ATAPL_Pierce_2004/book-guidelines|Advanced Topics in Types and Programming Languages]]
   - [[05_ATAPL_Pierce_2004/Logical-Relations-and-Equivalence-Checking|Logical Relations and Equivalence Checking]]

#### Additional external sources
- Barendregt, *Lambda Calculi with Types* (1992) — the canonical PTS/λ-cube reference; Wadler, *Theorems for Free!* (1989) for parametricity.

#### Key Concepts and Definitions
1. Impredicative universal quantification $\forall\alpha.\,T$; System $F\omega$ and kinds.
2. The eight systems of the $\lambda$-cube; Pure Type Systems (sorts, axioms, rules).
3. Existential types as abstract data types.
4. Parametricity / relational interpretation of types.

#### Relevant Questions
1. Which cube edge does each of: polymorphism, type constructors, dependent types, add — and which combination does Lean's kernel land on?
2. Why is type inference for System F undecidable, and what restriction recovers it?
3. Why does impredicativity break naive set-theoretic models?

---

## 5. Martin-Löf Type Theory: Π, Σ, Identity, Universes (Core Topic)

#### Pre-requisites
2. Judgments, Inductive Definitions, Binding, and Substitution; 3. STLC/Curry–Howard; 4. λ-cube.

#### Why this topic is important
This is the calculus your kernel implements: the four judgment forms, contexts, $\Pi$/$\Sigma$/identity/inductive type formers, and universe hierarchy. Refinement types are a restriction of $\Sigma$/subset types over this base; dependent contracts (`requires`/`ensures`) are $\Pi$-types over propositions. Everything from topics 6–12 assumes fluency here.

#### Sources to Study
1. [[01_programming_in_MLTT/book-guidelines|Programming in Martin-Löf's Type Theory]]
   - [[01_programming_in_MLTT/Propositions-as-Sets-(The-Curry-Howard-Correspondence)|Propositions as Sets]]
   - [[01_programming_in_MLTT/General-Proof-Rules|General Proof Rules]]
   - [[01_programming_in_MLTT/The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier|Cartesian Product of a Family & Universal Quantifier]]
   - [[01_programming_in_MLTT/Disjoint-Unions-and-the-Existential-Quantifier|Disjoint Unions & Existential Quantifier]]
   - [[01_programming_in_MLTT/Equality-Sets|Equality Sets]]
   - [[01_programming_in_MLTT/The-Universe-of-Small-Sets|The Universe of Small Sets]]
2. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming]]
   - [[02_type_theory_functional_programming_thompson_1999/The-Formal-System-of-Type-Theory-(TT0)|The Formal System of Type Theory ($TT_0$)]]
   - [[02_type_theory_functional_programming_thompson_1999/Quantifiers-and-Dependent-Types|Quantifiers and Dependent Types]]
   - [[02_type_theory_functional_programming_thompson_1999/Contexts,-Derivability-and-Type-Uniqueness|Contexts, Derivability and Type Uniqueness]]
   - [[02_type_theory_functional_programming_thompson_1999/Universes-and-Well-Founded-Types|Universes and Well-Founded Types]]
3. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory]]
   - [[84_type-theory-book_Daniel_Gratzer_2026/Full-Spectrum-Dependent-Types|Full-Spectrum Dependent Types]]
   - [[84_type-theory-book_Daniel_Gratzer_2026/Type-Connectives-via-Universal-Properties|Type Connectives via Universal Properties]]
   - [[84_type-theory-book_Daniel_Gratzer_2026/Metatheory-and-Implementation-of-Type-Theory|Metatheory and Implementation of Type Theory]]
4. [[11_ulf_norell_thesis_2007/book-guidelines|Towards a Practical Programming Language Based on Dependent Type Theory]]
   - [[11_ulf_norell_thesis_2007/Dependent-Type-Theory-Foundations|Dependent Type Theory Foundations]]
5. [[05_ATAPL_Pierce_2004/book-guidelines|Advanced Topics in Types and Programming Languages]]
   - [[05_ATAPL_Pierce_2004/Dependent-Types|Dependent Types]]
6. [[04_TAPL_Pierce_2002/Dependent-Types|TAPL — Dependent Types]]
7. [[07_practical_foundations_robert_harper_2012/Singleton-and-Dependent-Kinds|PFPL — Singleton and Dependent Kinds]]
8. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/book-guidelines|Categorical Logic and Type Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/First-Order-Dependent-Type-Theory|First Order Dependent Type Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Strength-of-Sum-and-Equality-Types|Strength of Sum and Equality Types]]
9. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Universes-and-Axioms|Universes and Axioms]]

#### Additional external sources
- Martin-Löf, *Intuitionistic Type Theory* (Bibliopolis, 1984); Lean 4 kernel documentation (*Type Checking in Lean 4*, Carneiro) for the concrete kernel rule set and universe-level checks.

#### Key Concepts and Definitions
1. Four judgment forms: $\Gamma \vdash A\ \mathsf{type}$, $\Gamma \vdash a : A$, and the two equalities; well-formed contexts.
2. $\Pi$-formation/intro/elim/$\beta$/$\eta$; $\Sigma$-types and projections; identity type with $J$.
3. Universe hierarchies, cumulativity, Girard's paradox ($U:U$).
4. Full-spectrum (non-uniform) dependency vs. refinement-style uniform dependency.
5. Type uniqueness / subject reduction.

#### Relevant Questions
1. Why do $\Sigma$-types fail to be existential quantifiers under "propositions as some types," and what does truncation/`Prop` add?
2. What distinguishes uniform from full-spectrum dependency, and why does the refinement-type approach handle only the former?
3. Which context-validity and substitution invariants must a Rust kernel enforce to keep the judgment forms well-scoped?
4. Why does removing $U:U$ avoid Girard's paradox?

---

## 6. Inductive Types, Inductive Families, and Dependent Pattern Matching (Core Topic)

#### Pre-requisites
5. Martin-Löf Type Theory.

#### Why this topic is important
Inductive families (e.g. length-indexed vectors, well-scoped syntax) are the data-structure language of your compiler and the way refinement invariants ("sorted", "in-bounds") are carried by types. Recursors are the kernel's computation rules; dependent pattern matching is what the elaborator must compile into them. Later: 7, 11, 12, 15.

#### Sources to Study
1. [[01_programming_in_MLTT/book-guidelines|Programming in Martin-Löf's Type Theory]]
   - [[01_programming_in_MLTT/Natural-Numbers-and-Lists|Natural Numbers and Lists]]
   - [[01_programming_in_MLTT/Well-Orderings-and-General-Trees|Well-Orderings and General Trees]]
2. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming]]
   - [[02_type_theory_functional_programming_thompson_1999/Base-Types-and-Data-Types|Base Types and Data Types]]
   - [[02_type_theory_functional_programming_thompson_1999/Well-Founded-and-General-Recursion|Well-Founded and General Recursion]]
3. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Inductive-Types|Inductive Types]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Inductive-Predicates-and-Judgments|Inductive Predicates and Judgments]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Dependent-Types-for-Program-Correctness|Dependent Types for Program Correctness]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Techniques-for-General-Recursion|Techniques for General Recursion]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Reasoning-About-Equality-Proofs|Reasoning About Equality Proofs]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Reasoning-About-Programming-Language-Syntax|Reasoning About Programming Language Syntax]]
4. [[11_ulf_norell_thesis_2007/book-guidelines|Towards a Practical Programming Language Based on Dependent Type Theory]]
   - [[11_ulf_norell_thesis_2007/Pattern-Matching-over-Inductive-Families|Pattern Matching over Inductive Families]]
   - [[11_ulf_norell_thesis_2007/The-Agda-Language|The Agda Language]]
5. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/book-guidelines|Dependently Typed Functional Programs and their Proofs]]
   - [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Inductive-Datatypes-and-Their-Elimination|Inductive Datatypes and Their Elimination]]
   - [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Pattern-Matching-for-Dependent-Types|Pattern Matching for Dependent Types]]
   - [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Equality-and-Object-Level-Unification|Equality and Object-Level Unification]]
6. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages]]
   - [[07_practical_foundations_robert_harper_2012/Pattern-Matching|Pattern Matching]]
   - [[07_practical_foundations_robert_harper_2012/Inductive-and-Coinductive-Types|Inductive and Coinductive Types]]
   - [[07_practical_foundations_robert_harper_2012/Generic-Programming|Generic Programming]]
7. [[14_homotopy_type_theory/book-guidelines|Homotopy Type Theory]]
   - [[14_homotopy_type_theory/Inductive-Definitions-and-Initial-Algebras|Inductive Definitions and Initial Algebras]]
   - [[14_homotopy_type_theory/W-Types-as-Well-Founded-Trees|W-Types as Well-Founded Trees]]

#### Additional external sources
- Dybjer, "Inductive Families" (1994); Cockx, Devriese & Piessens, "Unifiers as Equivalences" / "Pattern matching without K" (ICFP 2014); Lean 4 *Inductive Types* reference (nested/mutual, recursor generation).

#### Key Concepts and Definitions
1. Strict positivity; recursor/eliminator and its computation rules; motive.
2. Inductive families: parameters vs. indices.
3. Dependent pattern matching as unification of indices (with-abstraction, "green slime"); elaboration into eliminators.
4. Structural vs. well-founded recursion; accessibility predicates.
5. W-types as the general well-founded tree former.

#### Relevant Questions
1. Why is strict positivity required, and what inconsistency arises without it?
2. How does dependent pattern matching reduce to index unification, and where does UIP/axiom K sneak in?
3. How do you compile a case-tree with indexed families to recursor applications?
4. When do you prefer well-founded recursion over structural recursion in a language with refinement contracts?

---

## 7. Definitional Equality, Conversion, and the Intensional/Extensional Divide (Core Topic)

#### Pre-requisites
3. Normalization; 5. Martin-Löf Type Theory; 6. Inductive types.

#### Why this topic is important
`isDefEq` *is* your kernel's core algorithm: normalization-by-evaluation or weak-head reduction plus $\eta$, proof irrelevance and unit-type rules. Deciding conversion is what makes type checking decidable; going extensional (equality reflection) trades that away — the design decision behind refinement-type "SMT-discharged equalities". Later: 8, 9, 10, 11.

#### Sources to Study
1. [[17_HofmannExtensionalIntensionalTypeTheory1995/book-guidelines|Extensional Concepts in Intensional Type Theory]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/Definitional-Versus-Propositional-Equality|Definitional Versus Propositional Equality]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/Intensional-And-Extensional-Type-Theory|Intensional and Extensional Type Theory]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/The-Six-Extensional-Concepts|The Six Extensional Concepts]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/Independence-Of-Uniqueness-Of-Identity-Proofs|Independence of UIP]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/Intensional-Quotient-Types|Intensional Quotient Types]]
2. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory]]
   - [[84_type-theory-book_Daniel_Gratzer_2026/Extensionality-versus-Intensionality|Extensionality versus Intensionality]]
   - [[84_type-theory-book_Daniel_Gratzer_2026/Metatheory-and-Implementation-of-Type-Theory|Metatheory and Implementation of Type Theory]]
3. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming]]
   - [[02_type_theory_functional_programming_thompson_1999/Equality-in-Type-Theory|Equality in Type Theory]]
   - [[02_type_theory_functional_programming_thompson_1999/Quotient-and-Congruence-Types|Quotient and Congruence Types]]
4. [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/book-guidelines|Elaboration in Dependent Type Theory]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Computational-Behavior-and-Reduction|Computational Behavior and Reduction]]
5. [[01_programming_in_MLTT/Equality-Sets|Equality Sets]] (MLTT)
6. [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/The-lambda-Pi-Calculus-Modulo|The λΠ-Calculus Modulo]] (conversion modulo rewriting; see topic 9)
7. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Reasoning-About-Equality-Proofs|CPDT — Reasoning About Equality Proofs]]
8. [[07_practical_foundations_robert_harper_2012/Equational-Reasoning|PFPL — Equational Reasoning]]
9. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]] — Type Systems as Abstract Interpretation (bridge to `static-analysis`)

#### Additional external sources
- Abel, Öhman & Vezzosi, "Decidability of Conversion for Type Theory in Type Theory" (POPL 2018); Coquand, "An algorithm for type-checking dependent types" (1996); Barras' thesis / Lean 4 kernel notes for defeq with $\eta$, proof irrelevance, lazy delta unfolding.

#### Key Concepts and Definitions
1. Definitional (judgmental) vs. propositional equality; conversion rule.
2. $\beta$, $\eta$ (functions, pairs, unit), $\delta$ (unfolding), $\iota$ (recursor) and $\zeta$ reductions.
3. Equality reflection ⇒ undecidable type checking; conservativity of extensional concepts (funext, UIP) over ITT.
4. Normalization structure ⇒ decidability of judgmental equality; N-canonicity.
5. Setoid, groupoid, syntactic models as consistency/independence arguments.

#### Relevant Questions
1. Why does equality reflection make type-checking itself undecidable?
2. What is preserved and lost when funext and UIP are postulated as axioms rather than derived?
3. What is the concrete algorithmic difference between WHNF-based conversion and normalization-by-evaluation?
4. How does a reducibility hint (lazy delta) system change `isDefEq` performance without changing its meaning?

---

## 8. Bidirectional Typing (Core Topic)

#### Pre-requisites
2. Judgments and rules; 4. Polymorphism; 5. MLTT.

#### Why this topic is important
Bidirectional typing (inference $\Rightarrow$ / checking $\Leftarrow$) is how a dependent-type checker avoids full inference: it tells the elaborator where annotations are needed and how implicit arguments can be pushed inward. It is the skeleton of the elaborator and of refinement-type checking with intersection/property types. Later: 10, 11, 12.

#### Sources to Study
1. [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/book-guidelines|Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism]]
   - [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/Bidirectional-Typechecking-Foundations|Bidirectional Typechecking Foundations]]
   - [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/The-Problem-of-Polymorphism-in-Bidirectional-Systems|The Problem of Polymorphism]]
   - [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/Declarative-Type-System|Declarative Type System]]
   - [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/Algorithmic-Contexts|Algorithmic Contexts]]
   - [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/Algorithmic-Subtyping-and-Instantiation|Algorithmic Subtyping and Instantiation]]
   - [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/Algorithmic-Typing|Algorithmic Typing]]
   - [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/Metatheory-of-the-Algorithm|Metatheory of the Algorithm]]
2. [[32_Tridirectional_Typechecking_Dunfield_Pfenning/book-guidelines|Tridirectional Typechecking]]
   - [[32_Tridirectional_Typechecking_Dunfield_Pfenning/Bidirectional-Typechecking-Design-Principles|Bidirectional Typechecking Design Principles]]
   - [[32_Tridirectional_Typechecking_Dunfield_Pfenning/The-Core-Language-and-Its-Bidirectional-Typing|The Core Language and Its Bidirectional Typing]]
   - [[32_Tridirectional_Typechecking_Dunfield_Pfenning/Contextual-Typing-Annotations|Contextual Typing Annotations]]
3. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/Bi-Directional-Type-Systems|Thiré — Bi-Directional Type Systems]]
4. [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Type-Inference-and-Type-Checking-Algorithms|Saillard — Type Inference and Type-Checking Algorithms]]
5. [[04_TAPL_Pierce_2002/Type-Reconstruction|TAPL — Type Reconstruction]] (contrast: constraint-based inference; see topic 13)

#### Additional external sources
- Pierce & Turner, "Local Type Inference" (TOPLAS 2000); Dunfield & Krishnaswami, "Bidirectional Typing" survey (ACM CSUR 2021); Abel/Coquand-style NbE checkers for dependent bidirectional rules.

#### Key Concepts and Definitions
1. Synthesis ($\Rightarrow$) vs. checking ($\Leftarrow$); mode discipline; annotation rules.
2. Application judgment $\Psi \vdash A \bullet e \Rightarrow\!\Rightarrow C$ for polymorphism.
3. Ordered algorithmic contexts with existential variables; context extension as information increase.
4. Subsumption; annotation-removal theorem; completeness w.r.t. a declarative system.
5. Third direction for indefinite property types (tridirectional).

#### Relevant Questions
1. Why does two-judgment bidirectional typing break under polymorphism, motivating the application judgment?
2. Why must existential variable declarations keep strict order in the context?
3. How is a mode table for $\Pi$/$\Sigma$ introduction and elimination chosen, and what happens to `isDefEq` calls at mode switches?
4. What does "annotation removal" tell the language designer about where to require type ascriptions?

---

## 9. Logical Frameworks and $\lambda\Pi$-Calculus Modulo Rewriting (Core Topic)

#### Pre-requisites
5. MLTT; 7. Definitional equality; 3. Normalization.

#### Why this topic is important
$\lambda\Pi$-modulo turns "definitional equality = $\beta$ plus a user-supplied rewrite system," which is a minimal, trusted-kernel architecture: a small checker whose theories are data. It is the cleanest model of a proof-producing kernel with an extensible conversion relation (relevant to plugging arithmetic/decision-procedure results into `isDefEq`). Cross-reference: rewriting and proof certificates in `automated-reasoning`.

#### Sources to Study
1. [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/book-guidelines|Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory]]
   - [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/Lambda-Pi-Calculus-and-Its-Typing-Judgments|The λΠ-Calculus and Its Typing Judgments]]
   - [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/The-Lambda-Pi-Calculus-Modulo-Theory|The λΠ-Calculus Modulo Theory]]
   - [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/Decidability-via-Effective-Subsystems|Decidability via Effective Subsystems]]
   - [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/Simple-Type-Theory-and-Pure-Type-Systems|Simple Type Theory and Pure Type Systems]]
   - [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/Inductive-Types-and-Universe-Hierarchies|Inductive Types and Universe Hierarchies]]
2. [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/book-guidelines|Typechecking in the λΠ-Calculus Modulo]]
   - [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Abstract-Rewriting-and-Confluence-Theory|Abstract Rewriting and Confluence Theory]]
   - [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types|Subject Reduction, Product Compatibility, Uniqueness of Types]]
   - [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Well-Typedness-of-Rewrite-Rules|Well-Typedness of Rewrite Rules]]
   - [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Rewriting Modulo β and HORS]]
   - [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Non-Left-Linear-Rewriting-and-Weak-Typing|Non-Left-Linear Rewriting and Weak Typing]]
3. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/book-guidelines|Interoperability between proof systems using Dedukti]]
   - [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/Cumulative-Type-Systems-(CTS)|Cumulative Type Systems]]
   - [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/Encoding-CTS-Into-LambdaPi-Calculus-Modulo-Theory|Encoding CTS into λΠ-modulo]]
   - [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/Dedukti-An-Implementation-of-Lambda-Pi-calculus-Modulo-Theory|Dedukti Implementation]]
   - [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/STT-A-Constructive-Higher-Order-Logic|STT∀]]
4. [[88_LAMBDA_PI_GRIENENBERGER_2025/book-guidelines|Combining Computational Theories]]
   - [[88_LAMBDA_PI_GRIENENBERGER_2025/Deduction-Modulo-Theory|Deduction Modulo Theory]]
   - [[88_LAMBDA_PI_GRIENENBERGER_2025/Pure-Type-Systems|Pure Type Systems]]
   - [[88_LAMBDA_PI_GRIENENBERGER_2025/Modularity-of-Type-Theories|Modularity of Type Theories]]

#### Key Concepts and Definitions
1. $\lambda\Pi$-calculus: dependent products only; judgments as a logical-framework encoding of object theories.
2. Rewrite rules $\ell \hookrightarrow r$ integrated into conversion: $\equiv_{\beta\mathcal R}$.
3. Confluence + subject reduction ⇒ decidable type checking (with termination of $\mathcal R$ as an extra assumption for decidability).
4. Higher-order rewriting/pattern-LHS restriction; non-left-linear rules and weak typing.
5. Deduction modulo: computation vs. deduction split.

#### Relevant Questions
1. Which conditions on $\mathcal R$ are needed for subject reduction, and which additionally for decidability of conversion?
2. Why are higher-order pattern LHSs the tractable class for rewriting modulo $\beta$ (compare topic 10)?
3. What does the trusted base of a Dedukti-style checker consist of, compared with a monolithic kernel like Lean's?

---

## 10. Metavariables and Higher-Order Pattern Unification (Core Topic)

#### Pre-requisites
5. MLTT; 7. Definitional equality; 8. Bidirectional typing. Also the `automated-reasoning` topic on first-order and higher-order unification.

#### Why this topic is important
This is the mechanism behind implicit-argument resolution: `?m x y = t` problems whose decidable, most-general fragment is Miller's pattern fragment. Getting metavariable contexts, pruning, occurs check and $\eta$ right for $\Pi$/$\Sigma$/unit is the elaborator's unifier, verbatim. Later: 11.

#### Sources to Study
1. [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/book-guidelines|Extensions to Miller's Pattern Unification for Dependent Types and Records]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/The-lambda-Pi-Sigma-Calculus-with-Meta-Variables|The λΠΣ-Calculus with Meta-Variables]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Higher-Order-Pattern-Unification|Higher-Order Pattern Unification]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Constraint-Based-Unification-as-an-Inference-System|Constraint-Based Unification as an Inference System]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Pruning-and-the-Occurs-Check|Pruning and the Occurs Check]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Inverting-Substitutions|Inverting Substitutions]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Type-Isomorphisms-for-Dependent-Records|Type Isomorphisms for Dependent Records]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Extension-to-the-Unit-and-Singleton-Types|Extension to the Unit and Singleton Types]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Correctness-of-the-Unification-Algorithm|Correctness of the Unification Algorithm]]
2. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference, Haskell and Dependent Types]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Contextual-Problem-Solving|Contextual Problem-Solving]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Miller-Pattern-Unification|Miller Pattern Unification]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/The-Evidence-Language|The Evidence Language]]
3. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/book-guidelines|Dependently Typed Functional Programs and their Proofs]]
   - [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/The-OLEG-Type-Theory-of-Holes|The OLEG Type Theory of Holes]]
   - [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/A-Structurally-Recursive-Unification-Algorithm|A Structurally Recursive Unification Algorithm]]
4. [[11_ulf_norell_thesis_2007/book-guidelines|Norell thesis]]
   - [[11_ulf_norell_thesis_2007/Metavariables-and-Implicit-Arguments|Metavariables and Implicit Arguments]]
5. [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/book-guidelines|Elaboration in Dependent Type Theory]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Higher-Order-Unification|Higher-Order Unification]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/The-Constraint-Solving-Procedure|The Constraint Solving Procedure]]
6. [[08_programming_HOL_dale_miller_2012/book-guidelines|Programming with Higher-Order Logic]]
   - [[08_programming_HOL_dale_miller_2012/First-Order-Unification|First-Order Unification]]
   - [[08_programming_HOL_dale_miller_2012/Higher-Order-Unification|Higher-Order Unification]]
   - [[08_programming_HOL_dale_miller_2012/Lambda-Tree-Syntax-and-Computation-over-Binders|λ-Tree Syntax]]
7. [[04_TAPL_Pierce_2002/Type-Reconstruction|TAPL — Type Reconstruction]] (first-order unification in HM)

#### Additional external sources
- Miller, "A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification" (1991); Abel & Pientka, "Higher-Order Dynamic Pattern Unification for Dependent Types and Records" (TLCA 2011) is the direct predecessor of source 1.

#### Key Concepts and Definitions
1. Metavariable as closure / contextual object $u[\sigma]$; meta-context vs. object context.
2. Miller pattern: $?m\ x_1 \ldots x_n$ with distinct bound variables; most-general unifier is unique.
3. Pruning, occurs check; rigid vs. strongly rigid occurrences.
4. Hereditary substitution vs. substitute-then-normalize.
5. $\eta$ for $\Sigma$/unit and its effect on free-variable invariants; constraint postponement ("dynamic" patterns).

#### Relevant Questions
1. Why is the pattern fragment decidable while full higher-order unification is not?
2. Why do practical systems need a *dynamic* pattern fragment rather than rejecting non-pattern constraints?
3. How does a Σ-type unification problem reduce to Π-only problems?
4. Why can metavariables of singleton type always be solved "on the spot"?

---

## 11. Elaboration: Implicit Arguments, Coercions, and Type Classes (Core Topic)

#### Pre-requisites
8. Bidirectional typing; 10. Pattern unification; 7. Definitional equality; 6. Inductive families.

#### Why this topic is important
The elaborator is the compiler's front half: it turns surface syntax with holes and implicit arguments into kernel terms, using bidirectional traversal plus a constraint solver. This roadmap topic maps directly onto Lean's elaborator architecture (preprocessing, constraint generation, postponement, backtracking). It is also where refinement-inference constraints get generated. See `automated-reasoning` (proof reconstruction) and `sat-smt-csp` (constraint solving).

#### Sources to Study
1. [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/book-guidelines|Elaboration in Dependent Type Theory]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/The-Elaboration-Task|The Elaboration Task]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/The-Preprocessing-Phase|The Preprocessing Phase]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Term-Representation-and-Core-Data-Structures|Term Representation and Core Data Structures]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Constraints-and-Justifications|Constraints and Justifications]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/The-Constraint-Simplification-Procedure|The Constraint Simplification Procedure]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Type-Classes-and-Class-Inference|Type Classes and Class Inference]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Overloading-and-Coercions|Overloading and Coercions]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Performance-and-Implementation-Optimizations|Performance and Implementation Optimizations]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Tactics-and-Proof-Structuring|Tactics and Proof Structuring]]
2. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference, Haskell and Dependent Types]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Elaboration-into-Explicit-Calculi|Elaboration into Explicit Calculi]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Hindley-Milner-Type-Inference-Reconstructed|Hindley-Milner Type Inference Reconstructed]]
3. [[11_ulf_norell_thesis_2007/book-guidelines|Norell thesis]]
   - [[11_ulf_norell_thesis_2007/Module-Systems-for-Dependently-Typed-Languages|Module Systems for Dependently Typed Languages]]
   - [[11_ulf_norell_thesis_2007/Connecting-Type-Theory-to-First-Order-Automation|Connecting Type Theory to First-Order Automation]]
4. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/The-Ltac-Tactic-Language|The Ltac Tactic Language]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Proof-by-Reflection|Proof by Reflection]]
5. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Implementation-and-Reflection|McBride — Implementation and Reflection]]
6. [[40_A_Framework_for_Modular_Extensible_Equivalence-Preserving_Compilation_Dustin_Jammer_2020/book-guidelines|Pyrosome]] — Proof Automation and Elaboration (compiler-correctness angle)

#### Additional external sources
- Ullrich & de Moura, "The Lean 4 Theorem Prover and Programming Language" (CADE 2021); Ziliani & Sozeau, "A Unification Algorithm for Coq Featuring Universe Polymorphism and Overloading" (ICFP 2015); Asperti et al., "A Bi-Directional Refinement Algorithm for the Calculus of (Co)Inductive Constructions" (LMCS 2012).

#### Key Concepts and Definitions
1. Elaboration as partial-term ⇒ kernel-term with metavariables; postponed vs. eager constraints.
2. Constraints with justifications; non-chronological backtracking.
3. Huet-style imitation/projection case splits for non-pattern problems.
4. Reducibility annotations (irreducible/semireducible/reducible) — elaborator-only.
5. Type classes as backward-chaining logic programming; coercion insertion.

#### Relevant Questions
1. What is the division of labor between preprocessing and constraint solving, and why is it "slightly too simplistic"?
2. Why is inferring the motive in `subst e H` genuinely higher-order, and what makes its solution ambiguous?
3. How does non-chronological backtracking with justifications save work after a failure?
4. Where should refinement-predicate constraints be emitted: during elaboration or in a separate pass after kernel checking?

---

## 12. Refinement, Subset, and Property Types (Core Topic)

#### Pre-requisites
5. MLTT; 7. Definitional equality (extensional concepts); 8. Bidirectional typing; 11. Elaboration. Depends on `sat-smt-csp` (SMT discharge) for automation.

#### Why this topic is important
This *is* the surface language: $\{x : A \mid \varphi(x)\}$ with dependent-subtyping contracts. The theory tells you what the subset type costs (loss of proof irrelevance / canonicity problems, quotient difficulties), how to keep the extensional flavor decidable (deliverables/setoid models), and how bidirectional refinement checking with intersection and union types works.

#### Sources to Study
1. [[01_programming_in_MLTT/book-guidelines|Programming in Martin-Löf's Type Theory]]
   - [[01_programming_in_MLTT/Subsets-and-the-Subset-Theory|Subsets and the Subset Theory]]
   - [[01_programming_in_MLTT/Programming-as-Program-Derivation|Programming as Program Derivation]]
   - [[01_programming_in_MLTT/Specification-of-Abstract-Data-Types|Specification of Abstract Data Types]]
2. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming]]
   - [[02_type_theory_functional_programming_thompson_1999/The-Subset-Type-and-Its-Difficulties|The Subset Type and Its Difficulties]]
   - [[02_type_theory_functional_programming_thompson_1999/Specification-in-Type-Theory|Specification in Type Theory]]
   - [[02_type_theory_functional_programming_thompson_1999/Strengthened-and-Polymorphic-Rules|Strengthened and Polymorphic Rules]]
3. [[17_HofmannExtensionalIntensionalTypeTheory1995/book-guidelines|Extensional Concepts in Intensional Type Theory]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/The-Deliverables-Model|The Deliverables Model]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/Applications-Of-Extensional-Concepts|Applications of Extensional Concepts]]
4. [[32_Tridirectional_Typechecking_Dunfield_Pfenning/book-guidelines|Tridirectional Typechecking]]
   - [[32_Tridirectional_Typechecking_Dunfield_Pfenning/Definite-Property-Types|Definite Property Types]]
   - [[32_Tridirectional_Typechecking_Dunfield_Pfenning/Indefinite-Property-Types-and-the-Third-Direction|Indefinite Property Types and the Third Direction]]
   - [[32_Tridirectional_Typechecking_Dunfield_Pfenning/Related-Work-on-Refinement-Intersection-and-Union-Types|Related Work on Refinement, Intersection and Union Types]]
5. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Subset-Types-and-Quotient-Types|Jacobs — Subset Types and Quotient Types]]
6. [[04_TAPL_Pierce_2002/Subtyping|TAPL — Subtyping]] and Metatheory and Algorithms for Subtyping (TAPL, no article yet)
7. [[84_type-theory-book_Daniel_Gratzer_2026/Full-Spectrum-Dependent-Types|Gratzer — Full-Spectrum Dependent Types]] (refinement vs. full dependency)
8. [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/book-guidelines|Introduction to Separation Logic]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Abstract-Data-Types-Via-Inductive-Predicates|Abstract Data Types via Inductive Predicates]] (bridge to `static-analysis`)

#### Additional external sources
Not covered by an on-hand book — **gap**: Rondon, Kawaguchi & Jhala, "Liquid Types" (PLDI 2008); Freeman & Pfenning, "Refinement Types for ML" (PLDI 1991); Vazou et al., "Refinement Types for Haskell" (ICFP 2014) and the Liquid Haskell tutorial; Xi & Pfenning, "Dependent Types in Practical Programming" (POPL 1999); Ou et al., "Dynamic Typing with Dependent Types". Also F*/Dijkstra monads (Swamy et al. 2016) for Hoare-style dependent contracts.

#### Key Concepts and Definitions
1. Subset type $\{x:A \mid P\}$; propositional vs. computational content (proof irrelevance).
2. Dependent subtyping $\{x:A\mid P\} <: \{x:A\mid Q\}$ generating verification conditions $P \Rightarrow Q$.
3. Deliverables / Σ-with-proof separation vs. subset types; quotient/setoid types.
4. Intersection, union, and property (refinement) types; contextual annotations.
5. Hoare triples as dependent function types over pre/postconditions.

#### Relevant Questions
1. What breaks (canonicity, decidable equality of terms) when proofs are hidden inside subset types?
2. How does a subtyping check between refinements become an SMT/CSP query, and what must the type-theory side ensure about the query's context?
3. Why do union/indefinite property types require a third bidirectional direction?
4. What is the precise relation between $\{x{:}A\mid P\}$, $\Sigma x{:}A.\,P$ and a Hoare-style contract?

---

## 13. Type Inference and Constraint Generation (Core Topic)

#### Pre-requisites
2. Judgments; 3. STLC; 4. Polymorphism; 8. Bidirectional typing; 10. Unification.

#### Why this topic is important
Constraint-based inference for refinement types starts from Hindley–Milner: generate equality constraints, solve by unification, generalize. The same generate-then-solve architecture is what emits refinement constraints (Horn clauses) for the SAT/SMT/CHC backend.

#### Sources to Study
1. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference, Haskell and Dependent Types]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Hindley-Milner-Type-Inference-Reconstructed|Hindley-Milner Type Inference Reconstructed]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Unification-for-Units-of-Measure|Unification for Units of Measure]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Dependent-Types-in-Haskell|Dependent Types in Haskell]]
2. [[04_TAPL_Pierce_2002/Type-Reconstruction|TAPL — Type Reconstruction]]; [[04_TAPL_Pierce_2002/ML-Implementation-Techniques|ML Implementation Techniques]]
3. [[05_ATAPL_Pierce_2004/ML-Type-Inference|ATAPL — ML Type Inference]]
4. [[46_Principles_of_Program_Analysis-Springer_2005/Type-and-Effect-Systems|Principles of Program Analysis — Type and Effect Systems]] (bridge to `static-analysis`)
5. [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/Related-Approaches-to-Higher-Rank-Type-Inference|Related Approaches to Higher-Rank Type Inference]]
6. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]] — Type Systems as Abstract Interpretation

#### Additional external sources
- Pottier & Rémy, "The Essence of ML Type Inference" (ATTAPL ch. 10, in [[05_ATAPL_Pierce_2004/book-guidelines|ATAPL]] scope for HM(X)); Vytiniotis et al., "OutsideIn(X)" (JFP 2011).

#### Key Concepts and Definitions
1. Principal types; let-generalization; constraint generation vs. on-the-fly unification.
2. HM(X): constraints over a constraint domain $X$.
3. Type-and-effect systems as annotated types with constraint solving.
4. Levels/ranks for efficient generalization.

#### Relevant Questions
1. Why does let-polymorphism need generalization side conditions, and how does this interact with metavariable scopes?
2. How does HM(X) let refinement predicates become the constraint domain?
3. When is inference undecidable (System F, dependent types), and how does bidirectionality restore decidability?

---

## 14. Recursion, Fixed Points, and Recursive/Coinductive Types (Core Topic)

#### Pre-requisites
1. Computation; 3. Normalization; 6. Inductive types.

#### Why this topic is important
Fixed points appear three ways in this project: recursive/coinductive types in the language, termination checking for recursive definitions in the kernel, and least/greatest fixpoints as the semantics of loop invariants in `static-analysis` and Horn-clause solving. This topic is the shared vocabulary.

#### Sources to Study
1. [[04_TAPL_Pierce_2002/book-guidelines|Types and Programming Languages]]
   - [[04_TAPL_Pierce_2002/Recursive-Types|Recursive Types]]
   - [[04_TAPL_Pierce_2002/Coinduction-and-Infinite-Types|Coinduction and Infinite Types]]
2. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages]]
   - [[07_practical_foundations_robert_harper_2012/Recursive-Types|Recursive Types]]
   - [[07_practical_foundations_robert_harper_2012/Inductive-and-Coinductive-Types|Inductive and Coinductive Types]]
3. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Coinductive-Types-and-Infinite-Data|CPDT — Coinductive Types and Infinite Data]]
4. [[18_JW_Lloyd_Foundations_logic_programming_1987/book-guidelines|Foundations of Logic Programming]]
   - Fixpoint Theory (no article yet — see book-guidelines)
5. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - Fixpoint Theory; Deductive, Inductive and Coinductive Definitions (no article yet — see book-guidelines)
6. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book]] — Fixpoint Construction and Induction
7. [[13_introduction_bisimulation_coinduction_sangiorgi/book-guidelines|Introduction to Bisimulation and Coinduction]] (untagged for this area; relevant only for the coinduction theory)
8. [[46_Principles_of_Program_Analysis-Springer_2005/book-guidelines|Principles of Program Analysis]] — Induction and Coinduction

#### Key Concepts and Definitions
1. Knaster–Tarski: least and greatest fixed points of monotone operators.
2. Iso- vs. equi-recursive types; unfolding.
3. Guardedness (productivity) vs. structural decrease.
4. Coinduction principle / bisimulation as proof technique.

#### Relevant Questions
1. Why is a recursive type $\mu X.\,T$ unsound as a proposition unless $X$ occurs positively?
2. How does guardedness relate to termination checking in the kernel?
3. How do Kleene iteration and Tarski's theorem connect type-level fixpoints to invariant computation?

---

## 15. Symbolic and Tree Automata as Type/Domain Machinery (Core Topic)

#### Pre-requisites
1. Computation; 14. Fixed points/recursive types; 6. Inductive types (terms as trees).

#### Why this topic is important
Your CSP kernel represents abstract data structures as automata/grammar-shaped domains; symbolic automata (automata over an effective Boolean algebra of predicates) are the bridge between refinement predicates and regular-language domains, and tree automata treat inductive data as regular tree languages. Cross-reference: `sat-smt-csp` (automata domains), `static-analysis`.

#### Sources to Study
1. [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/book-guidelines|The Power of Symbolic Automata and Transducers]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Effective-Boolean-Algebras|Effective Boolean Algebras]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Finite-Automata|Symbolic Finite Automata]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Minterms-and-Alphabet-Equivalence-Classes|Minterms and Alphabet Equivalence Classes]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Symbolic-Finite-Transducers|Symbolic Finite Transducers]]
   - [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/Variants-of-Symbolic-Automata|Variants of Symbolic Automata]]
2. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Terms-Trees-and-Contexts|Terms, Trees, and Contexts]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Recognizable-Tree-Languages-and-Finite-Tree-Automata|Recognizable Tree Languages and Finite Tree Automata]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Regular-Tree-Grammars-and-Expressions|Regular Tree Grammars and Expressions]]
   - [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Tree-Transducers|Tree Transducers]]
3. [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/book-guidelines|Pushdown Automata Inclusion Problems]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Pushdown-Automata-Foundations|Pushdown Automata Foundations]]
   - [[92_Pushdown_Automata_Inclusion_Problems_NguyenVanTang/Visibly-Pushdown-Automata|Visibly Pushdown Automata]]
4. [[20_AUTOMATA_TRANSDUCERS_Loris_DAntoni_thesis/book-guidelines|D'Antoni thesis — Automata and Transducers]] (untagged for this area; related background)

#### Key Concepts and Definitions
1. Effective Boolean algebra $\mathcal A=(\mathcal D,\Psi,[\![\cdot]\!],\bot,\top,\vee,\wedge,\neg)$ and symbolic finite automata.
2. Minterm construction; determinization/minimization over predicates.
3. Regular tree languages, tree automata, closure and decidability properties.
4. Visibly pushdown languages as a determinizable context-free class.

#### Relevant Questions
1. What does the underlying theory need to provide (decidable satisfiability, model generation) for symbolic automata algorithms to work?
2. How do minterms trade alphabet size for exponential blowup?
3. Which inductive data invariants are regular tree languages, and which need pushdown/visibly-pushdown models?

---

## 16. Categorical Semantics and Models of Type Theory (Optional Core)

#### Pre-requisites
5. MLTT; 7. Definitional equality; 4. Polymorphism. Basic category theory is developed inline below.

#### Why this topic is important
Categorical models (categories with families, fibrations, toposes) justify the kernel's rules — soundness/consistency — and explain why substitution must be stable in every rule. Not on the implementation critical path; read after the kernel is working when you need to justify new type formers (e.g. refinement or linear features).

#### Sources to Study
1. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/book-guidelines|Categorical Logic and Type Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Simple-Type-Theory|Simple Type Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Fibred-Category-Theory|Fibred Category Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Indexed-Categories-and-the-Grothendieck-Construction|Indexed Categories and the Grothendieck Construction]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Full-Higher-Order-Dependent-Type-Theory|Full Higher Order Dependent Type Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Realizability-Models-Omega-Sets-and-PERs|Realizability Models]]
2. [[17_HofmannExtensionalIntensionalTypeTheory1995/book-guidelines|Extensional Concepts in Intensional Type Theory]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/Categorical-Semantics-Of-Dependent-Type-Theory|Categorical Semantics of Dependent Type Theory]]
   - [[17_HofmannExtensionalIntensionalTypeTheory1995/The-Method-Of-Syntactic-Models|The Method of Syntactic Models]]
3. [[84_type-theory-book_Daniel_Gratzer_2026/Categorical-Semantics-of-Type-Theory|Gratzer — Categorical Semantics of Type Theory]]
4. [[61_notes_on_category_theory_2024/book-guidelines|Notes on Category Theory]] and [[48_From_Categories_Homotopy_Theory_Cambridge_Birgit_Richter_2020/book-guidelines|From Categories to Homotopy Theory]] — prerequisites/background (no articles on this area's topics yet where marked in guidelines)
5. [[80_topoi-the-categorical-analysis-of-logic-Goldblatt/book-guidelines|Topoi: The Categorical Analysis of Logic]]
6. [[03_proofs_and_types_girard_1989/Coherence-Space-Semantics|Girard — Coherence Space Semantics]]
7. [[93_Impredicativity_in_Linear_Dependent_Type_Theory_Speight_Weide_2026/book-guidelines|Impredicativity in Linear Dependent Type Theory]]
   - [[93_Impredicativity_in_Linear_Dependent_Type_Theory_Speight_Weide_2026/Comprehension-Categories-and-Fibrations|Comprehension Categories and Fibrations]]
   - [[93_Impredicativity_in_Linear_Dependent_Type_Theory_Speight_Weide_2026/Realizability-Models-via-Assemblies|Realizability Models via Assemblies]]

#### Additional external sources
- Dybjer, "Internal Type Theory" (categories with families); Hofmann, "Syntax and Semantics of Dependent Types" (1997); Awodey, *Category Theory*.

#### Key Concepts and Definitions
1. Categories with families / comprehension categories: types as fibres over contexts, substitution as reindexing.
2. Fibrations and indexed categories; Grothendieck construction.
3. Realizability (ω-sets, PERs, assemblies) as models of impredicative theories.
4. Stability under substitution as a semantic requirement.

#### Relevant Questions
1. Why must every semantic type former be stable under substitution, and how does this constrain kernel rules?
2. What does the groupoid model show about UIP that a purely syntactic argument cannot?
3. Why are realizability models the standard route to consistency of impredicative theories?

---

## 17. Substructural, Linear, and Session Types (Optional / Extension)

#### Pre-requisites
3. Curry–Howard/Normalization; 5. MLTT (for the dependent-linear material). Cross-reference: linear logic and focused sequent calculus in `automated-reasoning`.

#### Why this topic is important
Linear resources model ownership/heaps in a Rust-shaped language and connect to separation logic for `static-analysis`. Session types give Curry–Howard for concurrency; linear dependent type theory is the frontier for combining these with dependent contracts. This topic is optional for the first compiler iteration.

#### Sources to Study
1. [[22_wadler_2012_propositions_as_sessions/book-guidelines|Propositions as Sessions]]
   - [[22_wadler_2012_propositions_as_sessions/The-Curry-Howard-Correspondence-for-Concurrency|The Curry-Howard Correspondence for Concurrency]]
   - [[22_wadler_2012_propositions_as_sessions/GV-a-Session-Typed-Functional-Language|GV: a Session-Typed Functional Language]]
   - [[22_wadler_2012_propositions_as_sessions/Polymorphism-in-CP|Polymorphism in CP]]
2. [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/book-guidelines|Domain-Aware Session Types]]
   - [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/Session-Types-via-the-Curry-Howard-Correspondence|Session Types via Curry–Howard]]
   - [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/Hybrid-Linear-Logic-and-Domain-Aware-Types|Hybrid Linear Logic and Domain-Aware Types]]
3. [[93_Impredicativity_in_Linear_Dependent_Type_Theory_Speight_Weide_2026/Linear-Dependent-Type-Theory|Linear Dependent Type Theory]]
4. [[05_ATAPL_Pierce_2004/Substructural-Type-Systems|ATAPL — Substructural Type Systems]]
5. [[03_proofs_and_types_girard_1989/Linear-Logic|Girard — Linear Logic]]
6. [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/book-guidelines|Introduction to Separation Logic]] (bridge to `static-analysis`)

#### Key Concepts and Definitions
1. Structural rules (weakening, contraction, exchange) and their removal; linear/affine/relevant types.
2. Session types as linear propositions; cut ↔ communication.
3. Linear dependent types: how dependency interacts with resource usage.

#### Relevant Questions
1. Where do linearity restrictions enter the substitution lemma?
2. How does the "propositions as sessions" reading treat cut elimination as communication?
3. What obstacles arise when combining linearity with dependency (usage in types vs. terms)?

---

## 18. Univalence, HoTT, Cubical and Two-Level Type Theory (Optional / Foundations)

#### Pre-requisites
5. MLTT; 7. Intensional/extensional equality; 16. Categorical semantics helpful.

#### Why this topic is important
Not required for the compiler as scoped, but HoTT explains what identity types *are* (paths), why UIP is independent, how quotients and higher inductive types can be added computationally (cubical), and what two-level type theory buys for metatheory and semi-simplicial constructions. Read it to understand design choices such as `Prop` vs. `Type`, not to implement them.

#### Sources to Study
1. [[14_homotopy_type_theory/book-guidelines|Homotopy Type Theory]]
   - [[14_homotopy_type_theory/Type-Theory-as-a-Foundational-System|Type Theory as a Foundational System]]
   - [[14_homotopy_type_theory/Identity-Types-and-Path-Structure|Identity Types and Path Structure]]
   - [[14_homotopy_type_theory/Type-Families-as-Fibrations-with-Transport|Type Families as Fibrations with Transport]]
   - [[14_homotopy_type_theory/The-Univalence-Axiom-and-Its-Consequences|The Univalence Axiom]]
   - [[14_homotopy_type_theory/Higher-Inductive-Types|Higher Inductive Types]]
   - [[14_homotopy_type_theory/Homotopy-n-Types-and-Truncation-Levels|Homotopy n-Types and Truncation Levels]]
   - [[14_homotopy_type_theory/Formal-Metatheory|Formal Metatheory]]
2. [[84_type-theory-book_Daniel_Gratzer_2026/Cubical-Type-Theory|Gratzer — Cubical Type Theory]] and [[84_type-theory-book_Daniel_Gratzer_2026/Univalent-Foundations-and-Homotopy-Type-Theory|Univalent Foundations and HoTT]]
3. [[91_Two-Level_Type_Theory_Annekov_Capriotti_Kraus_2026/book-guidelines|Two-Level Type Theory and Applications]]
   - [[91_Two-Level_Type_Theory_Annekov_Capriotti_Kraus_2026/Two-Level-Type-Theory-(2LTT)-Foundations|2LTT Foundations]]
   - [[91_Two-Level_Type_Theory_Annekov_Capriotti_Kraus_2026/Fibrancy-and-Cofibrancy|Fibrancy and Cofibrancy]]
4. [[30_A_HoTT_Approach_to_Computational_Effects_Wells_2019/book-guidelines|A HoTT Approach to Computational Effects]]
   - [[30_A_HoTT_Approach_to_Computational_Effects_Wells_2019/Foundations-of-Homotopy-Type-Theory|Foundations of HoTT]]
   - [[30_A_HoTT_Approach_to_Computational_Effects_Wells_2019/A-Type-Theoretic-Model-of-Actions-and-Effects|A Type-Theoretic Model of Actions and Effects]]
5. [[48_From_Categories_Homotopy_Theory_Cambridge_Birgit_Richter_2020/book-guidelines|From Categories to Homotopy Theory]] (background)

#### Key Concepts and Definitions
1. Identity types as paths; transport; equivalences.
2. Univalence: $(A = B) \simeq (A \simeq B)$; consequences (funext).
3. Homotopy levels, propositional truncation, higher inductive types.
4. Cubical type theory: interval, Kan operations; canonicity with univalence.
5. 2LTT: outer (strict) and inner (fibrant) levels.

#### Relevant Questions
1. Why must $\mathsf{idtoequiv}$ be an equivalence, and what fails with mere inverse-existence?
2. How does cubical type theory reconcile univalence with canonicity?
3. What role does the strict outer level of 2LTT play in metatheory that is impossible in plain HoTT?

---

## Summary of gaps

Topics with thin or no on-hand coverage where external sources are recommended (see each topic's "Additional external sources"): **12. Refinement types proper** (Liquid Types, Freeman–Pfenning, Xi–Pfenning; F\*), **7. Conversion algorithms** (NbE / Abel et al., Coquand), **13. Constraint-based HM(X) inference** (Pottier–Rémy), **4. System F/λ-cube canonical references** (Barendregt), and **5.** a kernel-level Lean 4 reference (Carneiro). Pruned as out-of-area despite a stray tag: [[63_Rings_Fields_Vector_Spaces_Sethuraman/book-guidelines|Rings, Fields, and Vector Spaces]] (abstract algebra, not on the type-theory critical path).
