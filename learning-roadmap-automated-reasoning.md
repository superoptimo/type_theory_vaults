# Learning Roadmap — Automated Reasoning

The `automated-reasoning` Focus Area supplies the proof-theoretic and algorithmic machinery behind the compiler's embedded theorem prover: derivations and cut elimination as the meaning of "a proof," unification (first-order, then Miller patterns) as the engine of the elaborator and of resolution, clause generation and Craig interpolation for refining verification conditions, Hoare logic/weakest preconditions as the source of proof obligations, and proof certificates as the interface to a small trusted kernel. The sequence goes from classical logic and its metatheory, through proof systems (natural deduction, sequent calculus, focusing, linear logic), into the search-and-unification core (resolution, logic programming, equality reasoning, higher-order unification), then into program logics, decision procedures/SAT-proof machinery, clause generation, and finally certificates and proof assistants. Type-theoretic prerequisites are cross-referenced to [[learning-roadmap-type-theory|the type-theory roadmap]] rather than restated.

---

## 1. Classical Propositional and First-Order Logic: Syntax, Semantics, Soundness and Completeness (Core Topic)

#### Pre-requisites
General discrete mathematics and induction on inductively defined sets.

#### Why this topic is important
Every proof procedure in the toolchain is judged against this semantics: soundness is what the trusted kernel must guarantee, completeness what the prover can hope for. Compactness and Löwenheim–Skolem explain why the prover works with Herbrand-style syntactic search. Later topics: 2–8.

#### Sources to Study
1. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Sentential-Propositional-Logic|Sentential (Propositional) Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Sentential-Connectives-and-Their-Completeness|Sentential Connectives and Their Completeness]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Compactness-for-Sentential-Logic|Compactness for Sentential Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/First-Order-Languages|First-Order Languages]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Structures-Truth-and-Satisfaction|Structures, Truth and Satisfaction]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/The-Deductive-Calculus-for-First-Order-Logic|The Deductive Calculus for First-Order Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Soundness-and-Completeness|Soundness and Completeness]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Models-of-Theories|Models of Theories]]
2. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic]]
   - [[10_boolos_burgess_computability_logic_2007/First-Order-Syntax-and-Semantics|First-Order Syntax and Semantics]]
   - [[10_boolos_burgess_computability_logic_2007/Metalogical-Notions|Metalogical Notions]]
3. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Foundations-of-Symbolic-Logic-in-OCaml|Foundations of Symbolic Logic in OCaml]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Propositional-Logic|Propositional Logic]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/First-Order-Logic-Syntax-and-Semantics|First-Order Logic: Syntax and Semantics]]
4. [[18_JW_Lloyd_Foundations_logic_programming_1987/First-Order-Logic-as-a-Foundation-for-Logic-Programming|Lloyd — First-Order Logic as a Foundation for Logic Programming]]
5. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/book-guidelines|Categorical Logic and Type Theory]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Equational-Logic|Equational Logic]]
   - [[57_Categorical_Logic_Type_Theory_BART_JACOBS/First-Order-Predicate-Logic|First Order Predicate Logic]] (optional semantic view)

#### Key Concepts and Definitions
1. Structures, assignments, satisfaction, validity, logical consequence.
2. Soundness and completeness of a deductive calculus (Gödel completeness); compactness.
3. Functional completeness of connectives; the propositional/first-order divide (decidable vs. semi-decidable).
4. Substitution, free/bound variables and capture-avoiding substitution at the formula level.

#### Relevant Questions
1. Why is soundness the property a trusted kernel must keep minimal, while completeness is only a property of the search layer around it?
2. How does compactness turn first-order unsatisfiability into a finite, syntactically checkable fact?
3. Where does capture-avoiding substitution appear in the quantifier rules, and what goes wrong in an implementation that ignores it?

---

## 2. Natural Deduction and Normalization (Core Topic)

#### Pre-requisites
1. Classical Propositional and First-Order Logic. Type-theory roadmap topic 3 (Curry–Howard) is the companion.

#### Why this topic is important
Natural deduction is the shape of the terms your kernel checks: a derivation is a proof term, and normalization is what makes definitional equality/`isDefEq` and consistency arguments go through. The introduction/elimination discipline (inversion, harmony) is the design rule for any new logical connective or refinement rule. Later: 3, 4, 10, 17.

#### Sources to Study
1. [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/book-guidelines|An Introduction to Proof Theory]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Axiomatic-Hilbert-Style-Proof-Systems|Axiomatic (Hilbert-Style) Proof Systems]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Induction-as-a-Proof-Method|Induction as a Proof Method]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Natural-Deduction|Natural Deduction]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Normalization-of-Natural-Deduction|Normalization of Natural Deduction]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Equivalence-of-the-Proof-Systems|Equivalence of the Proof Systems]]
2. [[60_Structural_Proof_Theory_Negri_Plato_2008/book-guidelines|Structural Proof Theory]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Natural-Deduction-and-the-Inversion-Principle|Natural Deduction and the Inversion Principle]]
3. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types]]
   - [[03_proofs_and_types_girard_1989/Natural-Deduction|Natural Deduction]]
   - [[03_proofs_and_types_girard_1989/The-Curry-Howard-Isomorphism|The Curry-Howard Isomorphism]]
   - [[03_proofs_and_types_girard_1989/Normalisation-Theorems|Normalisation Theorems]]
4. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming]]
   - [[02_type_theory_functional_programming_thompson_1999/Natural-Deduction-and-Predicate-Logic|Natural Deduction and Predicate Logic]]
   - [[02_type_theory_functional_programming_thompson_1999/Constructive-Mathematics|Constructive Mathematics]]
5. [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Natural-Deduction-in-Flag-Style|Nederpelt–Geuvers — Natural Deduction in Flag Style]]
6. [[01_programming_in_MLTT/General-Proof-Rules|Nordström et al. — General Proof Rules]]
7. [[07_practical_foundations_robert_harper_2012/Propositions-as-Types|PFPL — Propositions as Types]] and [[07_practical_foundations_robert_harper_2012/Inductive-Definitions-and-Rule-Induction|Inductive Definitions and Rule Induction]]
8. [[04_TAPL_Pierce_2002/The-Curry-Howard-Correspondence|TAPL — The Curry-Howard Correspondence]]

#### Key Concepts and Definitions
1. Introduction/elimination rules; detours and $\beta$-reduction on derivations; normal derivations and the subformula property.
2. Inversion principle / harmony.
3. Hilbert-style vs. natural deduction vs. sequent presentations and their equivalence.
4. Rule induction as the basic proof technique on derivations.

#### Relevant Questions
1. Why does a normal natural-deduction proof only use subformulas of its conclusion and hypotheses, and why does that matter for proof search?
2. How does the inversion principle constrain the design of a new connective?
3. What is the exact correspondence between proof normalization and term reduction?

---

## 3. Sequent Calculus, Cut Elimination, and the Subformula Property (Core Topic)

#### Pre-requisites
2. Natural Deduction and Normalization.

#### Why this topic is important
Sequent calculi are the form in which proof *search* is organized: cut-free = analytic = a terminating-ish, goal-directed search space. Cut elimination justifies the prover's refusal to guess lemmas and underlies interpolation (topic 13) and focused proofs (topic 4/15). This is where the theorem prover's clause/resolution engine originates.

#### Sources to Study
1. [[60_Structural_Proof_Theory_Negri_Plato_2008/book-guidelines|Structural Proof Theory]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Sequent-Calculus-Foundations|Sequent Calculus Foundations]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Structural-Rules-and-Cut-Elimination|Structural Rules and Cut Elimination]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Consequences-of-Cut-Elimination|Consequences of Cut Elimination]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Classical-Propositional-and-Predicate-Logic|Classical Propositional and Predicate Logic]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Quantifiers-and-First-Order-Proof-Theory|Quantifiers and First-Order Proof Theory]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Variant-Sequent-Calculi|Variant Sequent Calculi]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/Structural-Proof-Analysis-of-Axiomatic-Theories|Structural Proof Analysis of Axiomatic Theories]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/The-Sequent-Calculus-Natural-Deduction-Isomorphism|The Sequent Calculus–Natural Deduction Isomorphism]]
   - [[60_Structural_Proof_Theory_Negri_Plato_2008/PESCA-the-Sequent-Calculus-Proof-Editor|PESCA, the Sequent Calculus Proof Editor]]
2. [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/book-guidelines|An Introduction to Proof Theory]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/The-Sequent-Calculus|The Sequent Calculus]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/The-Cut-Elimination-Theorem-Hauptsatz|The Cut-Elimination Theorem (Hauptsatz)]]
   - [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Consequences-of-Cut-Elimination|Consequences of Cut-Elimination]]
3. [[12_proof_theory_algebra_logic_hiroakira_ono/book-guidelines|Proof Theory and Algebra in Logic]]
   - [[12_proof_theory_algebra_logic_hiroakira_ono/Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Sequent Calculi for Classical and Intuitionistic Logic]]
   - [[12_proof_theory_algebra_logic_hiroakira_ono/Cut-Elimination|Cut Elimination]]
   - [[12_proof_theory_algebra_logic_hiroakira_ono/Subformula-Property|Subformula Property]]
   - [[12_proof_theory_algebra_logic_hiroakira_ono/Proof-Theoretic-Consequences-of-Cut-Elimination|Proof-Theoretic Consequences of Cut Elimination]]
4. [[03_proofs_and_types_girard_1989/Sequent-Calculus-and-Cut-Elimination|Girard — Sequent Calculus and Cut Elimination]]
5. [[10_boolos_burgess_computability_logic_2007/Sequent-Calculus-and-Formal-Deduction|Boolos–Burgess — Sequent Calculus and Formal Deduction]]
6. [[09_proof_theory_logic_programming_dale_miller_2025/The-Sequent-Calculus|Miller — The Sequent Calculus]]
7. [[43_Modeling_in_Event-B_JR_Abrial_2010/The-Sequent-Calculus-and-Logical-Inference|Abrial — Event-B: The Sequent Calculus and Logical Inference]] (practical proof-obligation calculus)

#### Key Concepts and Definitions
1. Sequents $\Gamma \Rightarrow \Delta$, left/right rules, structural rules (weakening, contraction, exchange).
2. Cut, cut elimination (Gentzen's Hauptsatz), subformula property.
3. Invertible vs. non-invertible rules (for proof-search determinism).
4. Sequent-calculus/natural-deduction correspondence (cut ↔ redex).

#### Relevant Questions
1. Why does cut elimination make proof search analytic, and what does it cost (non-elementary blow-up)?
2. Which rules are invertible and how does that prune backtracking?
3. How do structural rules interact with contexts in an implementation, and what changes if contraction is dropped?

---

## 4. Classical, Intuitionistic, and Intermediate Logics; Translations and Semantics (Core Topic)

#### Pre-requisites
2. Natural Deduction; 3. Sequent Calculus.

#### Why this topic is important
The kernel is constructive; users and SMT backends are classical. Negative translations (Gödel–Gentzen, double negation) and Kripke/Heyting semantics tell you exactly which classical reasoning may be imported and how proof terms are preserved. Ecumenical/dual-embedding ideas matter for combining an SMT-classical fragment with a constructive core. Later: 13, 17.

#### Sources to Study
1. [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/The-Godel-Gentzen-Translation|Mancosu et al. — The Gödel–Gentzen Translation]]
2. [[12_proof_theory_algebra_logic_hiroakira_ono/Gödel-Translation|Ono — Gödel Translation]], [[12_proof_theory_algebra_logic_hiroakira_ono/Heyting-Algebras-and-Algebraic-Logic|Heyting Algebras and Algebraic Logic]], [[12_proof_theory_algebra_logic_hiroakira_ono/Modal-Algebras-and-Kripke-Semantics|Modal Algebras and Kripke Semantics]]
3. [[60_Structural_Proof_Theory_Negri_Plato_2008/Intermediate-Logical-Systems|Negri–von Plato — Intermediate Logical Systems]]
4. [[09_proof_theory_logic_programming_dale_miller_2025/Classical-and-Intuitionistic-Logic|Miller — Classical and Intuitionistic Logic]]
5. [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/Classical-Logic-via-Double-Negation-Connectives|Dedukti — Classical Logic via Double-Negation Connectives]]
6. [[88_LAMBDA_PI_GRIENENBERGER_2025/Ecumenical-Logics|Grienenberger — Ecumenical Logics]] and [[88_LAMBDA_PI_GRIENENBERGER_2025/Proof-Normalization-in-Ecumenical-Logic|Proof Normalization in Ecumenical Logic]]
7. [[80_topoi-the-categorical-analysis-of-logic-Goldblatt/book-guidelines|Topoi: The Categorical Analysis of Logic]] — Intuitionism and Heyting Semantics (optional semantic view)
8. [[02_type_theory_functional_programming_thompson_1999/Constructive-Mathematics|Thompson — Constructive Mathematics]]

#### Key Concepts and Definitions
1. Excluded middle, double-negation elimination, Peirce's law; intuitionistic vs. classical sequent calculi (one-sided succedent restriction).
2. Negative translations; Glivenko-type results.
3. Kripke and Heyting-algebra semantics.
4. Ecumenical systems: shared connectives, separate classical/intuitionistic ones.

#### Relevant Questions
1. When can a classical solver's verdict be lifted to a constructive proof term, and at what cost?
2. What does the Gödel–Gentzen translation preserve, and why is it insufficient for extracting programs from classical proofs?
3. How does the restriction of the succedent to one formula correspond to constructive validity?

---

## 5. Limits, Undecidability, and Decidable Fragments (Core Topic)

#### Pre-requisites
1. Classical Logic; type-theory roadmap topic 1 (computation and decidability).

#### Why this topic is important
It tells you what the prover *cannot* promise (Church/Turing undecidability, Gödel incompleteness, Tarski undefinability) and where to carve decidable islands (monadic, Bernays–Schönfinkel, Presburger, real closed fields) — exactly the fragments an SMT/CSP backend can discharge automatically. Later: 6, 9, 14.

#### Sources to Study
1. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic]]
   - [[10_boolos_burgess_computability_logic_2007/The-Undecidability-of-First-Order-Logic|The Undecidability of First-Order Logic]]
   - [[10_boolos_burgess_computability_logic_2007/Decidable-and-Undecidable-Fragments-of-Logic|Decidable and Undecidable Fragments of Logic]]
   - [[10_boolos_burgess_computability_logic_2007/Arithmetization-of-Syntax-and-Representability|Arithmetization of Syntax and Representability]]
   - [[10_boolos_burgess_computability_logic_2007/The-Diagonal-Lemma-and-the-Limitative-Theorems|The Diagonal Lemma and the Limitative Theorems]]
   - [[10_boolos_burgess_computability_logic_2007/Gödel's-Second-Incompleteness-Theorem-and-the-Logic-of-Provability|Gödel's Second Incompleteness Theorem]]
   - [[10_boolos_burgess_computability_logic_2007/Decidable-Fragments-of-Arithmetic|Decidable Fragments of Arithmetic]]
   - [[10_boolos_burgess_computability_logic_2007/Second-Order-Logic|Second-Order Logic]]
2. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Godels-Incompleteness-Theorems|Gödel's Incompleteness Theorems]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Representability-and-Recursive-Functions|Representability and Recursive Functions]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Second-Order-Logic|Second-Order Logic]]
   - [[16_ENDERTON_Mathematical_Introduction_Logic/Weak-Fragments-of-Number-Theory|Weak Fragments of Number Theory]]
3. [[15_handbook_logic_automated_reasoning_harrison_2009/Limits-of-Automated-Reasoning|Harrison — Limits of Automated Reasoning]]
4. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Undecidability-and-the-Limits-of-Static-Analysis|Cousot — Undecidability and the Limits of Static Analysis]]
5. [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Gentzens-Consistency-Proof-of-Arithmetic|Gentzen's Consistency Proof of Arithmetic]] and [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/Ordinal-Notations-up-to-Epsilon-0|Ordinal Notations up to ε₀]] (optional)

#### Key Concepts and Definitions
1. Church's theorem; semi-decidability of validity (Herbrand/Gödel completeness).
2. Gödel's incompleteness theorems; Tarski undefinability; diagonal lemma.
3. Decidable fragments and their complexity.
4. Consistency strength and ordinal analysis (optional).

#### Relevant Questions
1. Why does first-order validity being only semi-decidable dictate a *search* architecture with time-outs and lemma hints?
2. What does the second incompleteness theorem imply about a system proving its own kernel sound?
3. Which arithmetic fragments are decidable, and which of them will refinement predicates typically fall into?

---

## 6. Normal Forms, Skolemization, and Herbrand's Theorem (Core Topic)

#### Pre-requisites
1. Classical Logic; 5. Limits.

#### Why this topic is important
Prenex/Skolem/clausal normal forms convert arbitrary first-order goals into the clause sets resolution and unification work on — the front door of the clause/resolution engine. Herbrand's theorem reduces first-order unsatisfiability to propositional unsatisfiability of ground instances, the basis of instantiation-based reasoning and quantifier handling in SMT.

#### Sources to Study
1. [[10_boolos_burgess_computability_logic_2007/Normal-Forms-and-Elimination-Techniques|Boolos–Burgess — Normal Forms and Elimination Techniques]]
2. [[16_ENDERTON_Mathematical_Introduction_Logic/Skolem-Functions-and-Normal-Forms|Enderton — Skolem Functions and Normal Forms]]
3. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Automated-First-Order-Theorem-Proving|Automated First-Order Theorem Proving]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Propositional-Logic|Propositional Logic]]
4. [[18_JW_Lloyd_Foundations_logic_programming_1987/Declarative-Semantics-of-Definite-Programs|Lloyd — Declarative Semantics of Definite Programs]] (Herbrand models)
5. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/The-Herbrand-Domain-and-Unification|Cousot — The Herbrand Domain and Unification]] (bridge to `static-analysis`)
6. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Propositional-Logic-Foundations|Wallon — Propositional Logic Foundations]]; [[25_Handbook_Satisfiability_Armin_Biere_2021/CNF-Encodings|Handbook of Satisfiability — CNF Encodings]]

#### Key Concepts and Definitions
1. Negation/prenex normal forms; Skolemization (equisatisfiability, not equivalence); clausal form; Tseitin encodings.
2. Herbrand universe/base, Herbrand interpretation; Herbrand's theorem.
3. Clause, literal, ground instance, Horn clause.

#### Relevant Questions
1. Why is Skolemization equisatisfiable rather than equivalent, and how does this affect proof reconstruction into a kernel?
2. How does Herbrand's theorem justify enumerating ground instances, and what replaces enumeration in practice (unification)?
3. What does a Tseitin transformation buy over naive CNF conversion?

---

## 7. First-Order Unification and Resolution (Core Topic)

#### Pre-requisites
6. Normal Forms and Herbrand.

#### Why this topic is important
First-order unification is the base case of the elaborator's unifier and the core operation of resolution: mgu computation, occurs check, and idempotent substitution composition are what you write in Rust first. Everything in topics 8–10 generalizes or interacts with it. Type-theory roadmap topic 10 (metavariables, Miller patterns) builds on this.

#### Sources to Study
1. [[18_JW_Lloyd_Foundations_logic_programming_1987/book-guidelines|Foundations of Logic Programming]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/Unification|Unification]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/SLD-Resolution|SLD-Resolution]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/The-Occur-Check-Problem|The Occur Check Problem]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/Negation-in-Logic-Programs|Negation in Logic Programs]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/Programs-and-Goals-with-Arbitrary-First-Order-Bodies|Programs and Goals with Arbitrary First-Order Bodies]]
2. [[08_programming_HOL_dale_miller_2012/book-guidelines|Programming with Higher-Order Logic]]
   - [[08_programming_HOL_dale_miller_2012/First-Order-Unification|First-Order Unification]]
   - [[08_programming_HOL_dale_miller_2012/First-Order-Horn-Clause-Logic-Programming|First-Order Horn Clause Logic Programming]]
3. [[15_handbook_logic_automated_reasoning_harrison_2009/Automated-First-Order-Theorem-Proving|Harrison — Automated First-Order Theorem Proving]]
4. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/A-Structurally-Recursive-Unification-Algorithm|McBride — A Structurally Recursive Unification Algorithm]]
5. [[76_ThetaSubsumption_article/Generality-and-Theta-Subsumption|Theta-Subsumption — Generality and θ-Subsumption]] (subsumption as one-way matching)
6. [[04_TAPL_Pierce_2002/Type-Reconstruction|TAPL — Type Reconstruction]] (unification in HM)

#### Additional external sources
- Baader & Snyder, "Unification Theory" (Handbook of Automated Reasoning, 2001); Martelli & Montanari (1982) on almost-linear unification; Robinson (1965) for the resolution principle; Bachmair & Ganzinger on ordered resolution.

#### Key Concepts and Definitions
1. Substitution, most general unifier, unification algorithm (Robinson; Martelli–Montanari), occurs check.
2. Resolution rule; refutation completeness; SLD-resolution with selection rules and unification.
3. Subsumption ($\theta$-subsumption) and factoring.

#### Relevant Questions
1. What does omitting the occurs check buy (speed) and cost (unsoundness) in a Prolog-style engine?
2. Why is SLD resolution complete for definite programs but needs negation-as-failure extensions for general programs?
3. How do you make unification linear/near-linear with union-find, and where do terms need sharing?

---

## 8. Logic Programming as Proof Search, Uniform Proofs, and Hereditary Harrop (Core Topic)

#### Pre-requisites
3. Sequent Calculus; 7. Unification and Resolution.

#### Why this topic is important
Goal-directed (uniform) proof search is a principled architecture for the prover: computation = search for cut-free proofs. It explains how Prolog-like engines relate to sequent calculi and gives the template for a proof-search core with modular scoping (hereditary Harrop), also what type-class resolution in the elaborator does (type-theory roadmap topic 11).

#### Sources to Study
1. [[09_proof_theory_logic_programming_dale_miller_2025/book-guidelines|Proof Theory and Logic Programming: Computation as Proof Search]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Goal-Directed-Proof-Search-and-Uniform-Proofs|Goal-Directed Proof Search and Uniform Proofs]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Higher-Order-Quantification|Higher-Order Quantification]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Collection-Analysis-for-Horn-Clauses|Collection Analysis for Horn Clauses]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Formalizing-Operational-Semantics|Formalizing Operational Semantics]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Specifying-Computations-with-Multisets-and-Automata|Specifying Computations with Multisets and Automata]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Encoding-Security-Protocols-and-Process-Calculi|Encoding Security Protocols and Process Calculi]]
2. [[08_programming_HOL_dale_miller_2012/book-guidelines|Programming with Higher-Order Logic]]
   - [[08_programming_HOL_dale_miller_2012/Logic-Programming-as-Proof-Search|Logic Programming as Proof Search]]
   - [[08_programming_HOL_dale_miller_2012/Hereditary-Harrop-Formulas-and-Modular-Search|Hereditary Harrop Formulas and Modular Search]]
   - [[08_programming_HOL_dale_miller_2012/Modular-Program-Structuring|Modular Program Structuring]]
   - [[08_programming_HOL_dale_miller_2012/Implementing-Proof-Systems|Implementing Proof Systems]]
   - [[08_programming_HOL_dale_miller_2012/The-Teyjus-Implementation|The Teyjus Implementation]]
3. [[18_JW_Lloyd_Foundations_logic_programming_1987/book-guidelines|Foundations of Logic Programming]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/Fixpoint-Theory|Fixpoint Theory]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/Computational-Adequacy-of-Logic-Programs|Computational Adequacy of Logic Programs]]
   - [[18_JW_Lloyd_Foundations_logic_programming_1987/Deductive-Database-Theory|Deductive Database Theory]]
4. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Proof-Automation-by-Logic-Programming|Chlipala — Proof Automation by Logic Programming]]
5. [[24_Handbook_Constraint_Programming_Elsevier_2006/Constraint-Logic-Programming|Handbook of CP — Constraint Logic Programming]] (bridge to `sat-smt-csp`)

#### Key Concepts and Definitions
1. Uniform proof: goal-directed decomposition then backchaining on atoms.
2. Hereditary Harrop formulas: implications and universals in goals give modules and scoped constants.
3. Least fixpoint (immediate consequence operator) semantics vs. proof-theoretic semantics.
4. Constraint logic programming: unification generalized to constraint solving.

#### Relevant Questions
1. Why do uniform proofs suffice for Horn clauses and hereditary Harrop formulas but not for full intuitionistic logic?
2. How does the fixpoint semantics relate to the proof-search semantics of a logic program?
3. How does type-class resolution in Lean instantiate this architecture?

---

## 9. Equality Reasoning, Rewriting, and E-Graphs (Core Topic)

#### Pre-requisites
7. Unification and Resolution; 5. Decidable fragments (helpful).

#### Why this topic is important
Definitional equality, congruence closure, and rewriting-modulo are the workhorses of the kernel-adjacent automation (`simp`-style normalization, refinement equalities). E-graphs/equality saturation give a modern data structure for equivalence classes under rewrite rules — directly usable for verification-condition simplification and translation validation. Cross-reference: type-theory roadmap topics 7 and 9.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/Equality-Reasoning|Harrison — Equality Reasoning]]
2. [[71_Unifying_Datalog_and_Equality_Saturation/book-guidelines|Better Together: Unifying Datalog and Equality Saturation]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/The-E-Graph-Data-Structure|The E-Graph Data Structure]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Equivalence-and-Canonicalization|Equivalence and Canonicalization]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Query-Evaluation-and-E-Matching|Query Evaluation and E-Matching]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/The-egglog-Language-Model|The egglog Language Model]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Formal-Semantics-of-egglog|Formal Semantics of egglog]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Unification-and-Logic-Programming-in-egglog|Unification and Logic Programming in egglog]]
   - [[71_Unifying_Datalog_and_Equality_Saturation/Fixpoint-Reasoning-Frameworks|Fixpoint Reasoning Frameworks]]
3. [[39_Equality-Saturation-RossThesis2012/book-guidelines|Equality Saturation (Tate's/Ross' thesis)]]
   - [[39_Equality-Saturation-RossThesis2012/Equality-Saturation|Equality Saturation]]
   - [[39_Equality-Saturation-RossThesis2012/Translation-Validation|Translation Validation]]
   - [[39_Equality-Saturation-RossThesis2012/Learning-Optimizations-from-Proofs|Learning Optimizations from Proofs]]
   - [[39_Equality-Saturation-RossThesis2012/Category-Theoretic-Foundations-of-Proof-Generalization|Category-Theoretic Foundations of Proof Generalization]]
4. [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/book-guidelines|Typechecking in the λΠ-Calculus Modulo]]
   - [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Abstract-Rewriting-and-Confluence-Theory|Abstract Rewriting and Confluence Theory]]
   - [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/Rewriting-Modulo-beta-and-Higher-Order-Rewrite-Systems|Rewriting Modulo β and HORS]]
5. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Applications-of-Tree-Automata-to-Term-Rewriting|TATA — Applications of Tree Automata to Term Rewriting]]
6. [[40_A_Framework_for_Modular_Extensible_Equivalence-Preserving_Compilation_Dustin_Jammer_2020/book-guidelines|Pyrosome]]
   - [[40_A_Framework_for_Modular_Extensible_Equivalence-Preserving_Compilation_Dustin_Jammer_2020/Language-Specifications-as-Equational-Theories|Language Specifications as Equational Theories]]
   - [[40_A_Framework_for_Modular_Extensible_Equivalence-Preserving_Compilation_Dustin_Jammer_2020/Proof-Automation-and-Elaboration|Proof Automation and Elaboration]]
7. [[07_practical_foundations_robert_harper_2012/Equational-Reasoning|PFPL — Equational Reasoning]]

#### Additional external sources
- Nelson & Oppen, "Fast Decision Procedures Based on Congruence Closure" (1980); Baader & Nipkow, *Term Rewriting and All That* (KB completion, confluence, termination); Willsey et al., "egg: Fast and Extensible Equality Saturation" (POPL 2021); de Moura & Bjørner, "Efficient E-matching for SMT solvers".

#### Key Concepts and Definitions
1. Equational theory, rewriting, confluence, termination, critical pairs; Knuth–Bendix completion.
2. Congruence closure and union-find; E-graph; e-matching.
3. Equality saturation vs. greedy rewriting (phase-ordering).
4. Datalog + e-graphs: relational e-matching with merge functions.
5. Translation validation by equality reasoning.

#### Relevant Questions
1. What does congruence closure decide and how do e-graphs make it incremental?
2. Why can equality saturation avoid the phase-ordering problem, and when does it blow up?
3. What is the relationship between confluence/termination of a rewrite system and decidability of its equational theory?

---

## 10. Higher-Order Unification and Pattern Unification (Core Topic)

#### Pre-requisites
7. First-Order Unification; type-theory roadmap topics 3 (STLC) and 5 (dependent types); 9. Rewriting (helpful).

#### Why this topic is important
This is the direct source of the metavariable unifier: full HOU is undecidable (Huet), while Miller's pattern fragment restores decidability and unique mgus. The automated-reasoning view emphasizes search strategy (imitation/projection), postponement and constraint simplification; the type-theory view (roadmap topic 10 there) emphasizes contextual metavariables and $\eta$ for $\Sigma$/unit.

#### Sources to Study
1. [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/book-guidelines|Extensions to Miller's Pattern Unification for Dependent Types and Records]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Higher-Order-Pattern-Unification|Higher-Order Pattern Unification]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Constraint-Based-Unification-as-an-Inference-System|Constraint-Based Unification as an Inference System]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Pruning-and-the-Occurs-Check|Pruning and the Occurs Check]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Inverting-Substitutions|Inverting Substitutions]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Correctness-of-the-Unification-Algorithm|Correctness of the Unification Algorithm]]
   - [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/Related-Unification-Algorithms-and-Applications|Related Unification Algorithms and Applications]]
2. [[08_programming_HOL_dale_miller_2012/Higher-Order-Unification|Miller & Nadathur — Higher-Order Unification]]
3. [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/book-guidelines|Elaboration in Dependent Type Theory]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Higher-Order-Unification|Higher-Order Unification]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Constraints-and-Justifications|Constraints and Justifications]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/The-Constraint-Simplification-Procedure|The Constraint Simplification Procedure]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/The-Constraint-Solving-Procedure|The Constraint Solving Procedure]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Performance-and-Implementation-Optimizations|Performance and Implementation Optimizations]]
   - [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Tactics-and-Proof-Structuring|Tactics and Proof Structuring]]
4. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference, Haskell and Dependent Types]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Contextual-Problem-Solving|Contextual Problem-Solving]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Miller-Pattern-Unification|Miller Pattern Unification]]
   - [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/Unification-for-Units-of-Measure|Unification for Units of Measure]]
5. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/book-guidelines|Dependently Typed Functional Programs and their Proofs]]
   - [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/The-OLEG-Type-Theory-of-Holes|The OLEG Type Theory of Holes]]
   - [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Equality-and-Object-Level-Unification|Equality and Object-Level Unification]]
6. [[11_ulf_norell_thesis_2007/Metavariables-and-Implicit-Arguments|Norell — Metavariables and Implicit Arguments]]
7. [[11_ulf_norell_thesis_2007/Pattern-Matching-over-Inductive-Families|Norell — Pattern Matching over Inductive Families]]

#### Additional external sources
- Huet, "A Unification Algorithm for Typed λ-Calculus" (1975); Miller (1991) on $L_\lambda$ patterns; Nipkow, "Functional Unification of Higher-Order Patterns" (LICS 1993); Abel & Pientka (2011, 2013) as the source lineage of book 70.

#### Key Concepts and Definitions
1. Huet's semi-decision procedure: imitation, projection, flex–flex pairs.
2. Miller pattern: flex term applied to distinct bound variables; unique mgu.
3. Pruning, occurs check, and metavariable scope (contextual metavariables).
4. Constraint postponement, justifications and non-chronological backtracking.
5. Reducibility hints and delta-unfolding in unification modulo definitions.

#### Relevant Questions
1. Why is the pattern fragment decidable with unique mgu while general HOU is not?
2. What must a *dynamic* pattern implementation do with a non-pattern constraint (postpone, then retry after other metas are solved)?
3. How do justifications let a solver backjump to the responsible case split?
4. Where in Lean's elaborator does the approximation to Miller patterns (first-order approximation, pruning) enter?

---

## 11. Higher-Order Logic, $\lambda$-Tree Syntax, and Encoding Proof Systems (Core Topic)

#### Pre-requisites
2. Natural Deduction; 10. Higher-Order Unification; type-theory roadmap topic 3 (STLC).

#### Why this topic is important
Simple type theory / higher-order logic (Church) is the classical logic your automation targets; $\lambda$-tree syntax (HOAS) shows how to represent binders, quantifiers, and substitution *inside* the logic, which is the plumbing of Hoare-logic proof obligations and of embedding object logics into a logical framework.

#### Sources to Study
1. [[09_proof_theory_logic_programming_dale_miller_2025/Terms-Types-and-Formulas-in-the-Simple-Theory-of-Types|Miller — Terms, Types, and Formulas in the Simple Theory of Types]]
2. [[08_programming_HOL_dale_miller_2012/Lambda-Tree-Syntax-and-Computation-over-Binders|Miller & Nadathur — λ-Tree Syntax and Computation over Binders]]
3. [[08_programming_HOL_dale_miller_2012/Typed-First-Order-Terms-and-Type-Structure|Typed First-Order Terms and Type Structure]], [[08_programming_HOL_dale_miller_2012/Polymorphic-and-Pervasive-Constants|Polymorphic and Pervasive Constants]], [[08_programming_HOL_dale_miller_2012/Computing-over-Functional-Programs|Computing over Functional Programs]]
4. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/STT-A-Constructive-Higher-Order-Logic|Thiré — STT∀: A Constructive Higher-Order Logic]]
5. [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/Embedding-Predicate-Logic-in-a-Logical-Framework|Dedukti — Embedding Predicate Logic in a Logical Framework]]
6. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Higher-Order-Predicate-Logic|Jacobs — Higher Order Predicate Logic]] and [[57_Categorical_Logic_Type_Theory_BART_JACOBS/Dependent-Predicate-Logic|Dependent Predicate Logic]]
7. [[10_boolos_burgess_computability_logic_2007/Second-Order-Logic|Boolos–Burgess — Second-Order Logic]]; [[16_ENDERTON_Mathematical_Introduction_Logic/Many-Sorted-and-General-Second-Order-Logic|Enderton — Many-Sorted and General Second-Order Logic]]
8. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Concrete-Categories-Functors-and-Monads-for-Syntax|McBride — Concrete Categories, Functors and Monads for Syntax]]

#### Key Concepts and Definitions
1. Simple theory of types: terms, types, formulas; Henkin vs. full semantics.
2. HOAS/$\lambda$-tree syntax: object-level binders as meta-level $\lambda$; $\nabla$ and generic judgments.
3. Logical framework encoding: judgments-as-types.

#### Relevant Questions
1. Why is HOAS convenient for substitution but awkward for structural recursion on syntax?
2. What is lost between standard and Henkin semantics for second-order quantification, and what does the prover actually implement?
3. How does a logical framework separate *deduction* from *computation*?

---

## 12. Hoare Logic, Weakest Preconditions, and Generalized Substitutions (Core Topic)

#### Pre-requisites
1. Classical Logic; 3. Sequent Calculus; 11. Higher-Order Logic (binders). Bridge to `static-analysis` (invariants).

#### Why this topic is important
Hoare triples are the compiler's specification language: `requires`/`ensures` become triples, and weakest-precondition/predicate-transformer semantics generate the verification conditions handed to SMT/CSP. Substitution and context soundness proofs here are the same plumbing as in elaboration. Later: 13, 14, 15.

#### Sources to Study
1. [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/book-guidelines|An Introduction to Separation Logic]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Hoare-Logic-Foundations|Hoare Logic Foundations]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Hoare-Triples-And-Specifications|Hoare Triples and Specifications]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Annotated-Specifications|Annotated Specifications]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Assertion-Variables|Assertion Variables]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Procedures-And-Hypothetical-Specifications|Procedures and Hypothetical Specifications]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Case-Studies-in-Program-Verification|Case Studies in Program Verification]]
2. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book]]
   - [[27_The_B_Book_Abrial_2005/Formal-Proof-and-Predicate-Logic|Formal Proof and Predicate Logic]]
   - [[27_The_B_Book_Abrial_2005/Abstract-Machines-and-the-Generalized-Substitution-Language|Abstract Machines and the Generalized Substitution Language]]
   - [[27_The_B_Book_Abrial_2005/Semantics-of-Generalized-Substitutions|Semantics of Generalized Substitutions]]
   - [[27_The_B_Book_Abrial_2005/Sequencing-Loops-and-Termination-Proofs|Sequencing, Loops and Termination Proofs]]
   - [[27_The_B_Book_Abrial_2005/Algorithm-Construction-Methodology|Algorithm Construction Methodology]]
   - [[27_The_B_Book_Abrial_2005/Refinement-Theory|Refinement Theory]]
   - [[27_The_B_Book_Abrial_2005/Fixpoint-Construction-and-Induction|Fixpoint Construction and Induction]]
3. [[26_Principles_of_Abstract_Interpretation_Cousot_2021/book-guidelines|Principles of Abstract Interpretation]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Relational-and-Predicate-Transformer-Semantics|Relational and Predicate Transformer Semantics]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Fixpoint-Based-Verification-Proof-Methods|Fixpoint-Based Verification Proof Methods]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Invariance-Verification-and-Hoare-Logic|Invariance Verification and Hoare Logic]]
   - [[26_Principles_of_Abstract_Interpretation_Cousot_2021/Set-Theory-and-Proof-Techniques-Prerequisites|Set Theory and Proof Techniques Prerequisites]]
4. [[43_Modeling_in_Event-B_JR_Abrial_2010/book-guidelines|Modeling in Event-B]]
   - [[43_Modeling_in_Event-B_JR_Abrial_2010/Proof-Obligation-Rules|Proof Obligation Rules]]
   - [[43_Modeling_in_Event-B_JR_Abrial_2010/Refinement-Theory|Refinement Theory]]
   - [[43_Modeling_in_Event-B_JR_Abrial_2010/Sequential-Program-Derivation|Sequential Program Derivation]]
5. [[23_Refinement_Semantics_Derrick_Boiten_2018/book-guidelines|Refinement: Semantics, Languages and Applications]] (Z/B/Event-B refinement theory)
6. [[19_TLAplus_Lesle_Lamport/book-guidelines|Specifying Systems (TLA+)]]
   - [[19_TLAplus_Lesle_Lamport/Elementary-Mathematical-Foundations-for-Specification|Elementary Mathematical Foundations for Specification]]
   - [[19_TLAplus_Lesle_Lamport/Refinement-and-Implementation|Refinement and Implementation]]
7. [[01_programming_in_MLTT/Programming-as-Program-Derivation|Nordström et al. — Programming as Program Derivation]]
8. [[02_type_theory_functional_programming_thompson_1999/Specification-in-Type-Theory|Thompson — Specification in Type Theory]]
9. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis]] — Foundational Soundness Proofs

#### Additional external sources
- Hoare (1969), Dijkstra, *A Discipline of Programming* (wp), Apt & Olderog, *Verification of Sequential and Concurrent Programs*; Leino, "Efficient weakest preconditions" (2005) for VC generation with sharing; Why3/Boogie documentation.

#### Key Concepts and Definitions
1. Hoare triple $\{P\}\,C\,\{Q\}$; partial vs. total correctness; consequence rule; loop invariants and variants.
2. Weakest (liberal) precondition $\mathrm{wp}(C,Q)$ and predicate transformer semantics; strongest postcondition.
3. Substitution as assignment semantics: $\mathrm{wp}(x:=e,Q)=Q[e/x]$.
4. Proof obligations: invariant establishment/preservation, variant decrease, refinement simulation.
5. Generalized substitutions (B method) and refinement as monotone predicate-transformer ordering.

#### Relevant Questions
1. Why does weakest-precondition VC generation need capture-avoiding substitution and fresh-variable discipline to be sound?
2. Where do loop invariants come from, and how does that motivate abstract interpretation (`static-analysis`) plus interpolation (topic 14)?
3. How do proof obligations from Event-B/B compare to VCs from a refinement-type checker?

---

## 13. Separation Logic, Frame Reasoning, and Abduction (Core Topic)

#### Pre-requisites
12. Hoare Logic; 8. Logic programming/proof search helps for entailment.

#### Why this topic is important
Frame inference via *abduction* (bi-abduction) is the concrete case of abductive reasoning in the project: inferring missing preconditions compositionally. Heap-manipulating verification is optional for the first compiler but abductive inference generalizes to inferring refinement preconditions.

#### Sources to Study
1. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/book-guidelines|Compositional Shape Analysis by means of Bi-Abduction]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Abductive-Inference|Abductive Inference]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Bi-Abduction|Bi-Abduction]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Proof-Systems-and-Algorithms-for-Abduction|Proof Systems and Algorithms for Abduction]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Quality-and-Ordering-of-Abduction-Solutions|Quality and Ordering of Abduction Solutions]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Soundness-and-Semantic-Models|Soundness and Semantic Models]]
   - [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Separation-Logic-Foundations|Separation Logic Foundations]]
2. [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/book-guidelines|An Introduction to Separation Logic]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/The-Separation-Logic-Assertion-Language|The Separation Logic Assertion Language]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Semantics-Of-Assertions|Semantics of Assertions]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/The-Frame-Rule-and-Local-Reasoning|The Frame Rule and Local Reasoning]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Inference-Rules-for-Heap-Manipulating-Commands|Inference Rules for Heap-Manipulating Commands]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Special-Classes-Of-Assertions|Special Classes of Assertions]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/Shared-Variable-Concurrency|Shared-Variable Concurrency]]
   - [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/The-Iterated-Separating-Conjunction|The Iterated Separating Conjunction]]
3. [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/book-guidelines|Interprocedural Shape Analysis Using Separation Logic]] (abstract intersection and composition algorithms)
4. [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/book-guidelines|Domain-Aware Session Types]] — see topic 17 for the linear-logic reading

#### Key Concepts and Definitions
1. Separating conjunction $*$, magic wand $-\!*$, points-to; frame rule.
2. Abduction: given $A * ?M \vdash G$ find $?M$; bi-abduction adds a frame $?F$.
3. Quality criteria for abductive solutions (weakest/most general, non-redundant).
4. Compositional (bottom-up) analysis with summaries.

#### Relevant Questions
1. What distinguishes abduction from deduction, and what makes one solution "better" than another?
2. Why does the frame rule enable compositional reasoning, and what side condition keeps it sound?
3. Can the same abductive loop propose *refinement* preconditions for a function whose contract is missing?

---

## 14. Decision Procedures, Theory Combination, and Craig Interpolation (Core Topic)

#### Pre-requisites
5. Decidable fragments; 6. Normal forms; 9. Equality reasoning. Cross-reference `sat-smt-csp` roadmap (SMT architecture).

#### Why this topic is important
Verification conditions land in theories (linear arithmetic, arrays, uninterpreted functions, bit-vectors). Decision procedures and Nelson–Oppen-style combination are what the prover calls; Craig interpolation extracts explanations that refine abstractions/invariants (CEGAR, invariant synthesis) and clause generation for refined types.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Decidable-Theories-and-Quantifier-Elimination|Decidable Theories and Quantifier Elimination]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Combining-Decision-Procedures|Combining Decision Procedures]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Algebraic-Decision-Procedures|Algebraic Decision Procedures]]
   - [[15_handbook_logic_automated_reasoning_harrison_2009/Propositional-Satisfiability-Algorithms|Propositional Satisfiability Algorithms]]
2. [[10_boolos_burgess_computability_logic_2007/Interpolation-and-Definability|Boolos–Burgess — Interpolation and Definability]] (Craig interpolation, Beth definability)
3. [[25_Handbook_Satisfiability_Armin_Biere_2021/SAT-Techniques-for-Richer-Logics|Handbook of Satisfiability — SAT Techniques for Richer Logics]]
4. [[11_ulf_norell_thesis_2007/Connecting-Type-Theory-to-First-Order-Automation|Norell — Connecting Type Theory to First-Order Automation]]
5. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Proof-by-Reflection|Chlipala — Proof by Reflection]]
6. [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/Quantified-CSP|CSP Complexity — Quantified CSP]] (bridge to `sat-smt-csp`)
7. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Weak-Monadic-Second-Order-Logic-and-Tree-Automata|TATA — Weak Monadic Second-Order Logic and Tree Automata]] (MSO decision via automata)
8. [[13_introduction_bisimulation_coinduction_sangiorgi/book-guidelines|Introduction to Bisimulation and Coinduction]] (optional; equivalence of behaviours)
9. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/Relation-to-Other-Cooperation-Frameworks|Talbot — Relation to Other Cooperation Frameworks]] (solver cooperation; bridge to `sat-smt-csp`)

#### Additional external sources
Not covered by an on-hand book — **gap**: Nelson & Oppen (1979); Kroening & Strichman, *Decision Procedures* (Springer); Bradley & Manna, *The Calculus of Computation*; McMillan, "Interpolation and SAT-based Model Checking" (CAV 2003) and "Lazy Abstraction with Interpolants" (CAV 2006); Craig (1957); Henzinger et al., "Abstractions from Proofs" (POPL 2004).

#### Key Concepts and Definitions
1. Quantifier elimination and decision procedures (Presburger, real closed fields, linear arithmetic); Nelson–Oppen combination and its convexity/stable-infiniteness requirements.
2. Craig interpolant $I$ for $A \wedge B$ unsat: $A\Rightarrow I$, $I \wedge B$ unsat, vocabulary(I) ⊆ common.
3. Interpolation from resolution proofs; use in invariant/predicate refinement.
4. MSO/WMSO decidability via automata.

#### Relevant Questions
1. What must two theories satisfy for Nelson–Oppen combination to be complete?
2. How is an interpolant extracted from a resolution refutation and used to refine a predicate abstraction?
3. Why is quantifier elimination a non-starter beyond a few theories, and what replaces it (E-matching, MBQI)?

---

## 15. Proof Systems for SAT: Resolution, CDCL, Cutting Planes, and Proofs of Unsatisfiability (Core Topic)

#### Pre-requisites
6. Normal forms; 14. Decision procedures (helpful). Cross-reference `sat-smt-csp`.

#### Why this topic is important
The clause-learning engine in your solver *is* a resolution proof generator; proof-logging formats (RUP/DRAT, cutting-planes certificates) are how a solver hands untrusted results to the small trusted checker. Proof complexity tells you which encodings are hopeless (pigeonhole) and when stronger proof systems (cutting planes for pseudo-Boolean constraints) pay off.

#### Sources to Study
1. [[25_Handbook_Satisfiability_Armin_Biere_2021/book-guidelines|Handbook of Satisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Complete-Search-Algorithms-for-SAT|Complete Search Algorithms for SAT]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Conflict-Driven-Clause-Learning|Conflict-Driven Clause Learning]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Proof-Complexity|Proof Complexity]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Proofs-of-Unsatisfiability|Proofs of Unsatisfiability]]
   - [[25_Handbook_Satisfiability_Armin_Biere_2021/Quantified-Boolean-Formulas|Quantified Boolean Formulas]]
2. [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/book-guidelines|Pseudo-Boolean Reasoning and Compilation]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/The-Cutting-Planes-Proof-System|The Cutting Planes Proof System]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Resolution-Based-Pseudo-Boolean-Solving|Resolution-Based Pseudo-Boolean Solving]]
   - [[50_Pseudo-Boolean_Reasoning_Compilation_Romain_Wallon_2020/Guiding-the-Search-in-CDCL-SAT-Solvers|Guiding the Search in CDCL SAT Solvers]]
3. [[15_handbook_logic_automated_reasoning_harrison_2009/Propositional-Satisfiability-Algorithms|Harrison — Propositional Satisfiability Algorithms]]
4. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/book-guidelines|Acceleration Driven Clause Learning for CHC]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Constrained-Horn-Clauses-(CHCs)|Constrained Horn Clauses]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Resolution-for-CHCs|Resolution for CHCs]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Syntactic-Implicants-and-Redundancy|Syntactic Implicants and Redundancy]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/The-ADCL-Calculus|The ADCL Calculus]]
   - [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Metatheoretic-Properties-of-ADCL|Metatheoretic Properties of ADCL]]

#### Key Concepts and Definitions
1. Resolution refutations; CDCL as conflict analysis + clause learning (1-UIP) + non-chronological backjumping.
2. Proof complexity: resolution lower bounds; cutting planes and stronger systems.
3. Clausal proof formats (RUP/DRUP/DRAT) and proof checking.
4. Constrained Horn clauses; resolution for CHCs; learning clauses from loop acceleration.

#### Relevant Questions
1. Why does CDCL's learned-clause derivation amount to a resolution proof, and how is it certified?
2. When does cutting planes give exponentially shorter proofs than resolution?
3. How does ADCL's clause learning generalize CDCL to CHCs with arithmetic constraints?

---

## 16. Clause Generation and Inductive/Abductive Learning (Core Topic)

#### Pre-requisites
7. Unification and Resolution; 13. Abduction; 14. Interpolation.

#### Why this topic is important
The project asks for abductive reasoning, interpolation and *clause generation* to refine types and verification conditions. Inductive logic programming (ILP) with $\theta$-subsumption as the generality order is the systematic framework for searching a hypothesis space of clauses given examples/counterexamples, directly relevant to synthesizing refinement predicates.

#### Sources to Study
1. [[76_ThetaSubsumption_article/book-guidelines|Theta-Subsumption / ILP article]]
   - [[76_ThetaSubsumption_article/Logic-Programming-Foundations|Logic Programming Foundations]]
   - [[76_ThetaSubsumption_article/Generality-and-Theta-Subsumption|Generality and θ-Subsumption]]
   - [[76_ThetaSubsumption_article/ILP-Problem-Formulations|ILP Problem Formulations]]
   - [[76_ThetaSubsumption_article/Language-Bias|Language Bias]]
   - [[76_ThetaSubsumption_article/Search-Methods-Over-the-Hypothesis-Space|Search Methods Over the Hypothesis Space]]
   - [[76_ThetaSubsumption_article/Predicate-Invention|Predicate Invention]]
   - [[76_ThetaSubsumption_article/Representative-ILP-Systems|Representative ILP Systems]]
2. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/Abductive-Inference|Calcagno et al. — Abductive Inference]]
3. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/Syntactic-Implicants-and-Redundancy|Frohn — Syntactic Implicants and Redundancy]]
4. [[39_Equality-Saturation-RossThesis2012/Learning-Optimizations-from-Proofs|Ross — Learning Optimizations from Proofs]]
5. [[55_MinkowskiSum_Domain_Dissertation_Marius-Greitschus_2018/book-guidelines|Minkowski-Sum Domain Dissertation]] — Path Programs and Loop Invariants (bridge to `static-analysis`)
6. [[18_JW_Lloyd_Foundations_logic_programming_1987/Declarative-Error-Diagnosis|Lloyd — Declarative Error Diagnosis]] (counterexample-driven diagnosis)

#### Additional external sources
- Muggleton & De Raedt, "Inductive Logic Programming: Theory and Methods" (1994); Plotkin (1970) on least general generalization; Cropper & Dumančić, "Inductive logic programming at 30" (JAIR 2022); Solar-Lezama, *Program Synthesis by Sketching*; Alur et al., *Syntax-Guided Synthesis* (FMCAD 2013) for the counterexample-guided loop.

#### Key Concepts and Definitions
1. Generality order: $C \preceq D$ iff $C\theta \subseteq D$; least general generalization.
2. Hypothesis-space search (top-down refinement, bottom-up); language bias.
3. Predicate invention.
4. Counterexample-guided inductive synthesis.

#### Relevant Questions
1. Why is $\theta$-subsumption a good but incomplete approximation of logical implication between clauses?
2. How can counterexamples produced by the CSP kernel drive clause/refinement generation?
3. What language bias keeps predicate search tractable for refinement predicates?

---

## 17. Proof Certificates, Trusted Kernels, and Proof Reconstruction (Core Topic)

#### Pre-requisites
2–3. Natural deduction and sequent calculus; 15. Proofs of unsatisfiability; type-theory roadmap topics 5 and 7 (kernel, definitional equality).

#### Why this topic is important
This is the architectural payoff: untrusted automation (SAT/SMT/CSP, unifier, tactics) emits *evidence*; a small trusted kernel checks it. Foundational Proof Certificates give a semantic framework for certificates across proof systems, and Dedukti-style frameworks show how to keep the kernel tiny while theories are data. Proof reconstruction from solver output is what closes the loop between the theorem prover and the type checker.

#### Sources to Study
1. [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/book-guidelines|A Semantic Framework for Proof Evidence (FPC)]]
   - [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/Foundational-Proof-Certificates-(FPC)-Framework|Foundational Proof Certificates (FPC) Framework]]
   - [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/Focused-Sequent-Calculus|Focused Sequent Calculus]]
   - [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/Clerks-and-Experts-as-an-Augmented-Kernel|Clerks and Experts as an Augmented Kernel]]
   - [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/Trusted-Kernels-and-Proof-Sharing|Trusted Kernels and Proof Sharing]]
   - [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/Case-Studies-in-Proof-Certificate-Design|Case Studies in Proof Certificate Design]]
   - [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/Relating-Classical-and-Intuitionistic-Proof-Checking|Relating Classical and Intuitionistic Proof Checking]]
   - [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/Logic-Programming-as-an-Implementation-Substrate|Logic Programming as an Implementation Substrate]]
2. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/book-guidelines|Interoperability between proof systems using Dedukti]]
   - [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/Exporting-Proofs-Across-Proof-Systems|Exporting Proofs Across Proof Systems]]
   - [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/Rewriting-as-a-Meta-Programming-Language-(Dkmeta)|Rewriting as a Meta-Programming Language (Dkmeta)]]
   - [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/Philosophy-and-Future-of-Interoperability|Philosophy and Future of Interoperability]]
3. [[88_LAMBDA_PI_GRIENENBERGER_2025/book-guidelines|Combining Computational Theories]]
   - [[88_LAMBDA_PI_GRIENENBERGER_2025/Deduction-Modulo-Theory|Deduction Modulo Theory]]
   - [[88_LAMBDA_PI_GRIENENBERGER_2025/Interoperability-of-Proof-Assistants|Interoperability of Proof Assistants]]
   - [[88_LAMBDA_PI_GRIENENBERGER_2025/Theory-Fragmentation|Theory Fragmentation]]
4. [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/book-guidelines|Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory]]
   - [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/The-Lambda-Pi-Calculus-Modulo-Theory|The λΠ-Calculus Modulo Theory]]
   - [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/Interoperability-and-Reverse-Engineering-of-Proofs|Interoperability and Reverse Engineering of Proofs]]
5. [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework|Saillard — The λΠ-Calculus Modulo as a Logical Framework]]
6. [[25_Handbook_Satisfiability_Armin_Biere_2021/Proofs-of-Unsatisfiability|Handbook of Satisfiability — Proofs of Unsatisfiability]]
7. [[15_handbook_logic_automated_reasoning_harrison_2009/Interactive-Theorem-Proving-and-the-LCF-Approach|Harrison — Interactive Theorem Proving and the LCF Approach]]
8. [[39_Equality-Saturation-RossThesis2012/Translation-Validation|Ross — Translation Validation]]

#### Additional external sources
- Milner (1978)/Gordon et al. on LCF; Böhme & Weber, "Fast LCF-style proof reconstruction for Z3" (ITP 2010); Barrett et al. (Alethe/LFSC) proof formats; Cruz-Filipe et al., "Formally Verified Software in the Real World" / verified DRAT checkers (cake_lpr).

#### Key Concepts and Definitions
1. LCF architecture: abstract `thm` type with a small set of primitive inference functions.
2. Foundational proof certificate: certificate + clerks/experts driving a focused-sequent kernel.
3. Proof reconstruction (checking untrusted proofs by replay) vs. certified decision procedures (proof by reflection).
4. Trusted computing base; proof sharing across systems.
5. Deduction modulo: putting computation into conversion.

#### Relevant Questions
1. What must a proof-certificate format contain so the kernel can check it without searching?
2. Reconstruction versus reflection: what does each cost in kernel size and performance?
3. How does a logical framework reduce the trusted code to a type checker plus rewrite rules?
4. Which SAT/SMT proof formats would you accept as inputs to your kernel, and what reconstruction step is needed for each?

---

## 18. Proof Assistants, Tactics, and Proof Automation (Core Topic)

#### Pre-requisites
2. Natural deduction; 10. Unification; 17. Certificates; type-theory roadmap topics 5–6, 11.

#### Why this topic is important
The embedded prover is essentially a tactic/automation layer over the kernel. Existing systems (Coq, Lean, Isabelle/LCF) are the design references: tactic languages, proof search by logic programming, reflection, and how to engineer large developments.

#### Sources to Study
1. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/The-Coq-Proof-Assistant-and-Certified-Programming|The Coq Proof Assistant and Certified Programming]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/The-Ltac-Tactic-Language|The Ltac Tactic Language]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Proof-Automation-by-Logic-Programming|Proof Automation by Logic Programming]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Proof-by-Reflection|Proof by Reflection]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/Engineering-Large-Proof-Developments|Engineering Large Proof Developments]]
   - [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/The-Curry-Howard-Correspondence|The Curry–Howard Correspondence]]
2. [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/book-guidelines|Type Theory and Formal Proof]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Formal-Proof-Development-in-Practice|Formal Proof Development in Practice]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Proof-Assistants-and-the-Future-of-Formalisation|Proof Assistants and the Future of Formalisation]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Formalising-Elementary-Mathematics|Formalising Elementary Mathematics]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Sets-Relations-and-Maps|Sets, Relations and Maps]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Arithmetic-in-Type-Theory|Arithmetic in Type Theory]]
   - [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/Metatheory-of-Typed-Lambda-Calculi|Metatheory of Typed Lambda Calculi]]
3. [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Tactics-and-Proof-Structuring|De Moura et al. — Tactics and Proof Structuring]] and [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/Type-Classes-and-Class-Inference|Type Classes and Class Inference]]
4. [[15_handbook_logic_automated_reasoning_harrison_2009/Interactive-Theorem-Proving-and-the-LCF-Approach|Harrison — Interactive Theorem Proving and the LCF Approach]]
5. [[30_A_HoTT_Approach_to_Computational_Effects_Wells_2019/The-Coq-Proof-Assistant|Wells — The Coq Proof Assistant]]
6. [[91_Two-Level_Type_Theory_Annekov_Capriotti_Kraus_2026/Formalisation-of-2LTT-in-Proof-Assistants|Formalisation of 2LTT in Proof Assistants]] (optional)
7. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Elimination-Rules-for-Refinement-Proof|McBride — Elimination Rules for Refinement Proof]] and [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/Implementation-and-Reflection|Implementation and Reflection]]

#### Additional external sources
- Lean 4 metaprogramming book (tactic framework, `Meta`/`Elab` monads); Nipkow, Paulson, Wenzel, *Isabelle/HOL*; Nawrocki et al., "Metaprogramming in Lean 4".

#### Key Concepts and Definitions
1. Tactic as proof-state transformer; goals and metavariable contexts.
2. Proof by reflection: verified decision procedure + computation.
3. Proof automation via backward chaining (`auto`, type-class resolution).
4. Engineering practices: proof stability, lemma hygiene.

#### Relevant Questions
1. How is a tactic prover related to logic-programming-style proof search over metavariables?
2. When is reflection preferable to certificate replay?
3. What does the Lean tactic framework expose that a Rust-embedded prover must also provide (goals, metavariable contexts, backtracking)?

---

## 19. Linear Logic, Focusing, and Substructural Proof Theory (Optional / Extension)

#### Pre-requisites
3. Sequent calculus; 8. Proof search. Type-theory roadmap topic 17 covers the typing side.

#### Why this topic is important
Focused proofs organize proof search into deterministic phases, giving the systematic basis for FPC (topic 17) and efficient search; linear logic models resources/state, connecting to separation logic (topic 13) and session types. Optional for a first prover but the main source of principled search-space pruning.

#### Sources to Study
1. [[09_proof_theory_logic_programming_dale_miller_2025/book-guidelines|Proof Theory and Logic Programming]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Linear-Logic|Linear Logic]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Focused-Proofs-and-Cut-Elimination-for-Linear-Logic|Focused Proofs and Cut-Elimination for Linear Logic]]
   - [[09_proof_theory_logic_programming_dale_miller_2025/Linear-Logic-Programming|Linear Logic Programming]]
2. [[03_proofs_and_types_girard_1989/Linear-Logic|Girard — Linear Logic]]
3. [[12_proof_theory_algebra_logic_hiroakira_ono/Substructural-Logics-Proof-Theoretic-View|Ono — Substructural Logics: Proof-Theoretic View]], [[12_proof_theory_algebra_logic_hiroakira_ono/Residuated-Lattices-and-FL-Algebras|Residuated Lattices and FL-Algebras]]
4. [[22_wadler_2012_propositions_as_sessions/book-guidelines|Propositions as Sessions]]
   - [[22_wadler_2012_propositions_as_sessions/CP-a-Classical-Linear-Logic-Process-Calculus|CP: a Classical Linear Logic Process Calculus]]
   - [[22_wadler_2012_propositions_as_sessions/Commuting-Conversions-and-Cut-Elimination|Commuting Conversions and Cut Elimination]]
   - [[22_wadler_2012_propositions_as_sessions/The-Curry-Howard-Correspondence-for-Concurrency|The Curry-Howard Correspondence for Concurrency]]
5. [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/book-guidelines|Domain-Aware Session Types]]
   - [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/Session-Types-via-the-Curry-Howard-Correspondence|Session Types via the Curry–Howard Correspondence]]
   - [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/Hybrid-Linear-Logic-and-Domain-Aware-Types|Hybrid Linear Logic and Domain-Aware Types]]
6. [[93_Impredicativity_in_Linear_Dependent_Type_Theory_Speight_Weide_2026/Linear-Dependent-Type-Theory|Linear Dependent Type Theory]]

#### Additional external sources
- Andreoli, "Logic Programming with Focusing Proofs in Linear Logic" (1992); Liang & Miller, "Focusing and Polarization in Linear, Intuitionistic, and Classical Logics" (TCS 2009).

#### Key Concepts and Definitions
1. Multiplicative/additive/exponential connectives; resource-sensitive sequents.
2. Focusing: invertible (asynchronous) vs. non-invertible (synchronous) phases; polarity.
3. Linear logic as a logic-programming language (Lolli, Forum).
4. Proof nets/cut elimination as computation.

#### Relevant Questions
1. How does focusing remove spurious non-determinism from proof search?
2. What does polarity assignment change about a proof system's certificates?
3. How does linearity change the structural rules and the meaning of "context" in a Rust-shaped ownership setting?

---

## 20. Temporal Logic, Model Checking, and Bisimulation as Proof Techniques (Optional / Extension)

#### Pre-requisites
1. Classical logic; 12. Hoare logic; 9 (fixpoints) helpful. Bridge to `static-analysis` (model checking modulo theories, reachability).

#### Why this topic is important
Safety/invariant properties and reachability connect proof-based reasoning with state-space exploration; coinduction and bisimulation supply the equivalence proofs used in refinement and compiler-correctness reasoning. Optional at first; needed when extending beyond sequential functional/imperative contracts.

#### Sources to Study
1. [[67_Principles_of_Model_Checking_2008/book-guidelines|Principles of Model Checking]]
   - [[67_Principles_of_Model_Checking_2008/Safety-Properties-and-Invariants|Safety Properties and Invariants]]
   - [[67_Principles_of_Model_Checking_2008/Linear-Temporal-Logic|Linear Temporal Logic]]
   - [[67_Principles_of_Model_Checking_2008/Linear-Time-Properties|Linear-Time Properties]]
   - [[67_Principles_of_Model_Checking_2008/Probabilistic-Computation-Tree-Logic|Probabilistic Computation Tree Logic]]
   - [[67_Principles_of_Model_Checking_2008/Markov-Decision-Processes|Markov Decision Processes]]
2. [[19_TLAplus_Lesle_Lamport/book-guidelines|Specifying Systems (TLA+)]]
   - [[19_TLAplus_Lesle_Lamport/The-Syntax-of-TLA+|The Syntax of TLA+]]
   - [[19_TLAplus_Lesle_Lamport/Formal-Semantics-of-the-TLA+-Language|Formal Semantics of the TLA+ Language]]
   - [[19_TLAplus_Lesle_Lamport/Temporal-Logic-and-Liveness|Temporal Logic and Liveness]]
   - [[19_TLAplus_Lesle_Lamport/Specifying-Safety-Properties|Specifying Safety Properties]]
3. [[13_introduction_bisimulation_coinduction_sangiorgi/book-guidelines|Introduction to Bisimulation and Coinduction]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/Coinduction-and-the-Duality-with-Induction|Coinduction and the Duality with Induction]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/Bisimulation-and-Bisimilarity|Bisimulation and Bisimilarity]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/CCS-and-Algebraic-Properties-of-Bisimilarity|CCS and Algebraic Properties of Bisimilarity]]
   - [[13_introduction_bisimulation_coinduction_sangiorgi/Barbed-Bisimilarity-and-Congruence|Barbed Bisimilarity and Congruence]]
4. [[46_Principles_of_Program_Analysis-Springer_2005/Induction-and-Coinduction|Nielson et al. — Induction and Coinduction]]; [[46_Principles_of_Program_Analysis-Springer_2005/Control-Flow-Analysis-(0-CFA-and-Constraint-Based-Analysis)|Control Flow Analysis (0-CFA and Constraint-Based Analysis)]]; [[46_Principles_of_Program_Analysis-Springer_2005/Context-Sensitivity-in-Control-Flow-Analysis|Context Sensitivity in Control Flow Analysis]]
5. [[10_boolos_burgess_computability_logic_2007/Modal-Logic-and-the-Logic-of-Provability|Boolos–Burgess — Modal Logic and the Logic of Provability]]; [[12_proof_theory_algebra_logic_hiroakira_ono/Modal-Logic-Proof-Theory|Ono — Modal Logic Proof Theory]]
6. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Alternating-Tree-Automata|TATA — Alternating Tree Automata]] and [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/Context-Free-Tree-Languages|Context-Free Tree Languages]]
7. [[44_Introduction_to_Static_Analysis_Xavier_Rival/book-guidelines|Introduction to Static Analysis]] — Specialized Static Analysis Frameworks

#### Key Concepts and Definitions
1. Kripke structures, LTL/CTL semantics; safety vs. liveness; invariants.
2. Automata-theoretic verification.
3. Bisimulation as the greatest fixed point; coinductive proof principle.
4. Refinement mappings in TLA+.

#### Relevant Questions
1. How does an inductive invariant relate to a safety property, and how do proof-based and model-checking-based verification differ?
2. What is the coinduction proof principle, and how does it justify bisimulation-based equivalence arguments?
3. How does a TLA+ refinement mapping compare with B/Event-B refinement proof obligations?

---

## Summary of gaps

Where on-hand books are thin or absent, the topics above carry "Additional external sources": **14. Decision procedures and Craig interpolation** (Kroening–Strichman, Bradley–Manna, McMillan, Henzinger et al.), **7. Unification theory and resolution refinements** (Baader–Snyder, Robinson, Bachmair–Ganzinger), **9. Term rewriting** (Baader–Nipkow) and congruence closure (Nelson–Oppen), **16. Program synthesis / CEGIS** (Solar-Lezama, SyGuS), **12. VC generation and weakest preconditions** (Dijkstra, Leino), and **17/18. proof reconstruction and Lean tactic metaprogramming**. Superdeterministic/pushdown automata (92), symbolic automata (75), the Handbook of Constraint Programming and hybrid-systems/optimization books were not drawn from here.
