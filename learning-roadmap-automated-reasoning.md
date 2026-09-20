# Learning Roadmap — Automated Reasoning

Automated Reasoning is the area that turns judgments into *search*: unification
that resolves metavariables, resolution/tableaux that discharge proof
obligations, sequent calculi whose cut-elimination doubles as a decidability
argument, and the certificate formats that let a small trusted kernel accept
a large amount of external search without expanding the trusted computing
base. This sequence starts from first-order syntax/semantics and classical
proof theory, builds through unification (first-order, then higher-order,
then Miller's pattern fragment — the direct ancestor of the elaborator's
metavariable solver), turns to logic programming and resolution-based
theorem proving, and then assembles the three things the compiler's toolchain
actually needs: a bidirectional elaborator with a pattern unifier, a trusted
proof-checking kernel (LCF/de Bruijn-style, generalized to the λΠ-calculus
modulo theory), and a clause/constraint engine (CHC solving, abduction,
equality saturation) that can discharge or refute Hoare-style verification
conditions. It closes with the adjacent formal-methods and program-logic
material (Hoare/separation logic, refinement) and two more specialized
threads (linear logic/session types, categorical/topos semantics) that
connect this area back to `type-theory`, `sat-smt-csp`, and `static-analysis`.

---

## 1. First-Order Syntax, Semantics, and Classical Metalogic (Core Topic)

#### Pre-requisites
None — this is the entry point of the whole Focus Area.

#### Why this topic is important
Every later topic — unification, resolution, sequent calculi, proof
certificates — is stated over first-order terms/formulas and relies on the
soundness/completeness vocabulary set up here (satisfaction, validity,
Herbrand models, compactness). This is also where the project's "judgment
forms as shared ancestor of type checker and proof checker" thread first
appears, before Topic 2 develops it structurally.

#### Sources to Study
1. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic (Enderton)]]
   - [[First-Order-Languages]]
   - [[Structures-Truth-and-Satisfaction]]
   - [[The-Deductive-Calculus-for-First-Order-Logic]]
   - [[Soundness-and-Completeness]]
2. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic (Boolos, Burgess, Jeffrey)]]
   - First-order syntax/semantics and metalogical-notions articles
3. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Foundations-of-Symbolic-Logic-in-OCaml]]
   - [[First-Order-Logic-Syntax-and-Semantics]]
   - [[Propositional-Logic]]
4. [[19_TLAplus_Lesle_Lamport/book-guidelines|Specifying Systems: The TLA+ Language and Tools (Lamport)]]
   - Elementary mathematical foundations for specification (untyped logic, `choose`)

#### Key Concepts and Definitions
1. Satisfaction relation $s,h\models p$/Tarskian truth definition, logical implication, validity, and satisfiability.
2. Herbrand universe/base/model, and the syntax/semantics/metalanguage separation Harrison builds his OCaml implementation on.
3. Soundness Theorem (axiom validity + MP-preservation) and the Substitution Lemma.
4. `choose` (Hilbert's epsilon) as a deterministic choice operator, and why TLA+ deliberately has no type system.

#### Relevant Questions
1. What does "logical form" mean for validity, and why does keeping syntax and semantics sharply separated matter for building a symbolic-computation system?
2. How does the Soundness Theorem reduce to two local facts (axioms are valid, MP preserves validity)?
3. Why is `choose` deterministic rather than nondeterministic, and what does that buy a specification language?

---

## 2. Natural Deduction and the Curry–Howard Correspondence (Core Topic)

#### Pre-requisites
[[#1. First-Order Syntax, Semantics, and Classical Metalogic (Core Topic)|Topic 1]].

#### Why this topic is important
This is the load-bearing bridge the project's "judgment forms as the shared
ancestor of a type checker and a proof checker" thread depends on: every
later trusted-kernel and elaborator topic (9, 10, 11) is a judgment built
from exactly this apparatus, read once as formula/proof and once as
type/program.

#### Sources to Study
1. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types (Girard)]]
   - [[Natural-Deduction]]
   - [[The-Curry-Howard-Isomorphism]]
   - [[Sense-and-Denotation]]
2. [[01_programming_in_MLTT/book-guidelines|Programming in Martin-Löf's Type Theory (Nordström/Petersson/Smith)]]
   - [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)]]
   - [[The-Semantics-of-Judgement-Forms]]
   - [[General-Proof-Rules]]
3. [[06_type_theory_and_formal_proof_nederpelt_geuvers_2014/book-guidelines|Type Theory and Formal Proof (Nederpelt & Geuvers)]]
   - [[Natural-Deduction-in-Flag-Style]]
4. [[60_Structural_Proof_Theory_Negri_Plato_2008/book-guidelines|Structural Proof Theory (Negri & von Plato)]]
   - [[Natural-Deduction-and-the-Inversion-Principle]]
5. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types (Chlipala)]]
   - [[The-Curry-Howard-Correspondence]]

#### Key Concepts and Definitions
1. Deduction trees, alive vs. discharged hypotheses, and the deduction-as-λ-term reading (Girard).
2. BHK proof semantics vs. Tarski's truth-table semantics — grounds "proofs as constructive content."
3. The inversion principle: general elimination rules unify the special-case E-rules across connectives (Negri–Plato), including the awkward disjunction case.
4. Flag-style natural deduction as an explicit scope stack, with ∃-elimination read as proof search.

#### Relevant Questions
1. Why does Girard insist Curry–Howard is a genuine isomorphism (normal proof ↔ normal term structurally), not just a bijection?
2. How does Heyting's BHK reading of $A\Rightarrow B$ differ from Tarski's truth-table reading, and why does that matter for constructivity?
3. Why doesn't disjunction's ordinary elimination rule fit the normal-form pattern, and how does the generalized inversion principle fix this?

---

## 3. Sequent Calculus and Cut Elimination (Core Topic)

#### Pre-requisites
[[#2. Natural Deduction and the Curry–Howard Correspondence (Core Topic)|Topic 2]].

#### Why this topic is important
Cut elimination is the proof-theoretic engine behind decidability, the
subformula property, and consistency proofs throughout this roadmap — and
it is the structural ancestor of focused proof search (Topic 8) and the
proof-certificate framework (Topic 10). The B-Book's mechanized Proof
Procedure is a concrete, implementable instance worth studying alongside the
classical Gentzen development.

#### Sources to Study
1. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types (Girard)]]
   - [[Sequent-Calculus-and-Cut-Elimination]]
2. [[60_Structural_Proof_Theory_Negri_Plato_2008/book-guidelines|Structural Proof Theory (Negri & von Plato)]]
   - [[Sequent-Calculus-Foundations]]
   - [[Structural-Rules-and-Cut-Elimination]]
   - [[Consequences-of-Cut-Elimination]]
3. [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/book-guidelines|An Introduction to Proof Theory (Mancosu, Galvan & Zach)]]
   - [[The-Sequent-Calculus]]
   - [[The-Cut-Elimination-Theorem-Hauptsatz]]
4. [[12_proof_theory_algebra_logic_hiroakira_ono/book-guidelines|Proof Theory and Algebra in Logic (Ono)]]
   - [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic]]
   - [[Cut-Elimination]]
5. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book (Abrial)]]
   - [[Formal-Proof-and-Predicate-Logic]]
6. [[09_proof_theory_logic_programming_dale_miller_2025/book-guidelines|Proof Theory and Logic Programming (Miller, 2025)]]
   - Sequent calculus and cut-elimination chapters (no article yet)

#### Key Concepts and Definitions
1. Sequent $\Gamma\Rightarrow\Delta$/$HYP\vdash P$; structural rules (exchange, weakening, contraction) as *the* important rules distinguishing calculi.
2. Gentzen's mix rule, the extended cut (e-cut) needed once contraction is present, and double induction on grade/height.
3. Subformula property as the direct consequence of cut-freeness, and its role in consistency/decidability arguments.
4. Contraction-free (G3-style) calculi with height-preserving admissibility as a cleaner route to the same theorems.

#### Relevant Questions
1. Why is ordinary cut elimination insufficient once contraction is in the system, and what does Gentzen's e-cut/mix fix?
2. How does the subformula property give a purely syntactic route to consistency, decidability, and the disjunction/existence properties?
3. Why must G3ip's axiom be restricted to atoms, and why does cut-admissibility there need induction on formula weight *with* a subinduction on cut-height?

---

## 4. Gödel's Theorems and the Limits of Automated Reasoning (Core Topic)

#### Pre-requisites
[[#1. First-Order Syntax, Semantics, and Classical Metalogic (Core Topic)|Topic 1]], [[#3. Sequent Calculus and Cut Elimination (Core Topic)|Topic 3]].

#### Why this topic is important
Before building a trusted kernel (Topic 10) it matters to know exactly what
a proof-checking system can and cannot certify: undecidability of validity,
the impossibility of a complete decision procedure, and the precise
derivability conditions behind Gödel II bound what "soundness" can mean for
any prover this project builds.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Limits-of-Automated-Reasoning]]
2. [[16_ENDERTON_Mathematical_Introduction_Logic/book-guidelines|A Mathematical Introduction to Logic (Enderton)]]
   - [[Godels-Incompleteness-Theorems]]
3. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic (Boolos, Burgess, Jeffrey)]]
   - Diagonal Lemma, Gödel's Second Incompleteness/Logic of Provability, and undecidability-of-first-order-logic articles
4. [[54_An_Introduction_ProofTheory_Normalization_Mancosu_Galvan_Zach_2021/book-guidelines|An Introduction to Proof Theory (Mancosu, Galvan & Zach)]]
   - [[Gentzens-Consistency-Proof-of-Arithmetic]]
   - [[Ordinal-Notations-up-to-Epsilon-0]]
   - [[Applications-of-Induction-up-to-Epsilon-0]]

#### Key Concepts and Definitions
1. Tarski's undefinability theorem, proved before and used to sharpen Gödel's incompleteness results.
2. Gödel numbering, the Fixed-Point/Diagonal Lemma, and the three derivability conditions behind Gödel II.
3. Church's theorem: undecidability of first-order validity via reduction from the halting problem.
4. Gentzen's ordinal-analysis consistency proof of PA using induction up to $\varepsilon_0$ — illustrated by the Hydra game and Goodstein's theorem.

#### Relevant Questions
1. How does Tarski's undefinability theorem force the semantic incompleteness-vs-unsoundness choice before Gödel's sharper syntactic result?
2. What do the three derivability conditions buy Gödel's Second Incompleteness Theorem, and in what precise sense does it refute Hilbert's programme?
3. Why must Gentzen's ordinal notations stay strictly below $\varepsilon_0$, and how is that bound itself a consequence of Gödel II?

---

## 5. First-Order Unification and Equality Reasoning (Core Topic)

#### Pre-requisites
[[#1. First-Order Syntax, Semantics, and Classical Metalogic (Core Topic)|Topic 1]].

#### Why this topic is important
This is the tractable base case the project's higher-order/pattern unifier
(Topic 7) generalizes. Congruence closure and term-rewriting/completion here
are also the direct machinery behind egglog/equality saturation (Topic 16)
and the Dedukti-family kernels' convertibility checking (Topic 11).

#### Sources to Study
1. [[18_JW_Lloyd_Foundations_logic_programming_1987/book-guidelines|Foundations of Logic Programming (Lloyd)]]
   - [[Unification]]
   - [[The-Occur-Check-Problem]]
2. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Equality-Reasoning]]
   - [[Algebraic-Decision-Procedures]]
3. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications (Comon et al.)]]
   - [[Applications-of-Tree-Automata-to-Term-Rewriting]]

#### Key Concepts and Definitions
1. Substitutions, instances, composition, and the most general unifier (MGU); Robinson-style unification via term-reduction/reorientation/variable-elimination transforms.
2. The occur check, its worst-case-exponential cost when the MGU must be printed explicitly, and Martelli–Montanari-style fixes.
3. Congruence closure, confluence (Newman's lemma, Church–Rosser), and Knuth–Bendix completion via critical pairs.
4. Superposition/paramodulation as equality reasoning integrated into resolution.

#### Relevant Questions
1. Why is unification worst-case exponential once the MGU must be materialized as an explicit substitution, and how does a DAG-based representation avoid this?
2. How does Newman's lemma let Knuth–Bendix completion get away with checking only finitely many critical pairs?
3. What is the scope difference between plain congruence closure and paramodulation over a full equational theory?

---

## 6. Resolution, Tableaux, and Automated First-Order Theorem Proving (Core Topic)

#### Pre-requisites
[[#5. First-Order Unification and Equality Reasoning (Core Topic)|Topic 5]].

#### Why this topic is important
This is the classical decision-procedure lineage (Gilmore → DP → tableaux →
resolution → model elimination) the project's embedded first-order prover
sits in, and it is where Horn clauses first appear as the fragment that
becomes logic programming (Topic 7) and, later, Constrained Horn Clauses
(Topic 15).

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Automated-First-Order-Theorem-Proving]]
   - [[Interactive-Theorem-Proving-and-the-LCF-Approach]]
2. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic (Boolos, Burgess, Jeffrey)]]
   - Normal forms/elimination-techniques and interpolation/definability articles
3. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types (Girard)]]
   - Resolution/Horn-clause discussion within [[Sequent-Calculus-and-Cut-Elimination]]
4. [[11_ulf_norell_thesis_2007/book-guidelines|Towards a Practical Programming Language Based on Dependent Type Theory (Norell)]]
   - Connecting Type Theory to First-Order Automation

#### Key Concepts and Definitions
1. Skolemization (equisatisfiability, not equivalence) and Herbrand's theorem as the bridge from validity to finite propositional search.
2. Resolution + the lifting lemma; subsumption/replacement and resolution refinements; Horn clauses as the SLD-resolvable fragment.
3. Model elimination/MESON as top-down (goal-directed) search versus resolution's bottom-up architecture.
4. The Craig interpolation thread introduced here (formally developed in Topic 12).

#### Relevant Questions
1. Why does Skolemization only preserve equisatisfiability, never logical equivalence?
2. How do successive provers in this lineage each attack the same Herbrand-instance explosion differently?
3. What is the architectural tradeoff between resolution's bottom-up search and model elimination's top-down search?

---

## 7. Logic Programming: Proof Search as Computation (Core Topic)

#### Pre-requisites
[[#6. Resolution, Tableaux, and Automated First-Order Theorem Proving (Core Topic)|Topic 6]].

#### Why this topic is important
This is the "computation-as-deduction" reading that later underlies the
project's proof-search-based theorem-prover kernel: uniform proofs and
focused sequent systems here (Topic 8) are exactly the abstract
characterization of what makes a logic a *programming* language, not just a
specification language.

#### Sources to Study
1. [[18_JW_Lloyd_Foundations_logic_programming_1987/book-guidelines|Foundations of Logic Programming (Lloyd)]]
   - [[Declarative-Semantics-of-Definite-Programs]]
   - [[SLD-Resolution]]
   - [[Negation-in-Logic-Programs]]
   - [[Deductive-Database-Theory]]
2. [[08_programming_HOL_dale_miller_2012/book-guidelines|Programming with Higher-Order Logic (Miller & Nadathur)]]
   - Logic Programming as Proof Search, First-Order Horn Clause LP, Hereditary Harrop Formulas & Modular Search
3. [[76_ThetaSubsumption_article/book-guidelines|Inductive Logic Programming At 30 (Cropper & Dumančić)]]
   - [[Logic-Programming-Foundations]]
   - [[Generality-and-Theta-Subsumption]]

#### Key Concepts and Definitions
1. Least Herbrand model $M_P$ and the van Emden–Kowalski fixpoint characterization ($T_P$ operator) — computation as fixpoint approximation, resurfacing in Topic 16's egglog treatment.
2. SLD-resolution, computed vs. correct answers, and the Independence-of-Computation-Rule result.
3. Closed World Assumption vs. negation-as-failure vs. program completion, and why completeness needs *hierarchical*, not merely stratified, programs.
4. Uniform proofs and hereditary Harrop formulas as the abstract characterization of "logic programming language."
5. $\theta$-subsumption as a decidable syntactic proxy for the undecidable semantic entailment relation.

#### Relevant Questions
1. Why is "correct answer is an instance of the computed answer" the right correctness statement, rather than equality?
2. Why is negation-as-failure strictly weaker than the Closed World Assumption, with the Herbrand rule sitting between them?
3. In what sense is $\theta$-subsumption's generality order syntactic rather than semantic, and why does that make it tractable where entailment is not?

---

## 8. Focused Sequent Calculi and Proof Certificates (Core Topic)

#### Pre-requisites
[[#3. Sequent Calculus and Cut Elimination (Core Topic)|Topic 3]], [[#7. Logic Programming: Proof Search as Computation (Core Topic)|Topic 7]].

#### Why this topic is important
Focusing is what makes proof search tractable by collapsing don't-care
nondeterminism into synthetic inference rules ("molecules from atoms"), and
Foundational Proof Certificates give a checkable, technology-independent
format for the output of that search — directly informing how the project's
embedded prover should hand proof objects to a trusted kernel (Topic 10).

#### Sources to Study
1. [[09_proof_theory_logic_programming_dale_miller_2025/book-guidelines|Proof Theory and Logic Programming (Miller, 2025)]]
   - Sequent Calculus, Goal-Directed Proof Search & Uniform Proofs, Focused Proofs & Cut-Elimination for Linear Logic (no articles yet)
2. [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/book-guidelines|A Semantic Framework for Proof Evidence (Chihani, Miller & Renaud)]]
   - Foundational Proof Certificates Framework, Focused Sequent Calculus, Clerks and Experts as an Augmented Kernel, Case Studies in Proof Certificate Design (no articles yet)

#### Key Concepts and Definitions
1. Polarized formulas, asynchronous/synchronous phases, and synthetic inference rules — the "chemistry of inference" view (molecules built from atomic rules).
2. The four FPC desiderata (D1–D4): simple checkability, broad coverage, denoting a genuine structural-proof-theory proof, and allowing reconstruction from partial detail (Poincaré's Principle).
3. Clerks (asynchronous) and experts (synchronous) as the augmented kernel that turns a certificate term into a guided proof search, with soundness following "for free" via erasure back to the unaugmented system.
4. Resolvent-triple certificates for binary resolution, and why quantifier instantiation can be safely omitted given the right unification property.

#### Relevant Questions
1. What makes a connective positive vs. negative, and how does polarity determine invertibility and where contraction (`decide`) must live?
2. Why does soundness of the augmented (clerk/expert) kernel follow automatically from the erasure map back to the unaugmented focused system?
3. Why does checking a justified Horn-clause proof need *specific* premise indexes rather than an unordered set of hypotheses?

---

## 9. Higher-Order Unification and Miller's Pattern Fragment (Core Topic)

#### Pre-requisites
[[#5. First-Order Unification and Equality Reasoning (Core Topic)|Topic 5]].

#### Why this topic is important
This is the single most directly load-bearing topic in the whole Focus Area
for the project's metavariable unifier: full higher-order unification is
undecidable (Post correspondence, Hilbert's 10th), but Miller's pattern
fragment ($L_\lambda$) is decidable and unitary — exactly the fragment the
elaborator (Topic 10) is built on.

#### Sources to Study
1. [[08_programming_HOL_dale_miller_2012/book-guidelines|Programming with Higher-Order Logic (Miller & Nadathur)]]
   - Higher-Order Unification, λ-Tree Syntax articles
2. [[11_ulf_norell_thesis_2007/book-guidelines|Towards a Practical Programming Language Based on Dependent Type Theory (Norell)]]
   - Metavariables and Implicit Arguments
3. [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/book-guidelines|Extensions to Miller's Pattern Unification for Dependent Types and Records (Abel & Pientka)]]
   - Higher-Order Pattern Unification, Constraint-Based Unification as an Inference System, Pruning and the Occurs Check, Correctness of the Unification Algorithm (no articles yet)
4. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference, Haskell and Dependent Types (Gundry)]]
   - [[Miller-Pattern-Unification]]
   - [[Contextual-Problem-Solving]]
5. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/book-guidelines|Dependently Typed Functional Programs and their Proofs (McBride)]]
   - [[A-Structurally-Recursive-Unification-Algorithm]]
   - [[Equality-and-Object-Level-Unification]]

#### Key Concepts and Definitions
1. Pattern (Miller pattern): a metavariable applied only to a sequence of pairwise-distinct bound variables — the condition that guarantees a unique MGU.
2. Rigid/flexible/strongly-rigid occurrences; pruning as recovery from a "bad" (blocking, non-eliminable) rigid occurrence, distinguished from outright unification failure.
3. Twin variables (Gundry) for heterogeneous equality, and lowering through $\Sigma$-types to reduce record/Σ-unification to Π-unification (Abel–Pientka).
4. Termination via an ordinal-valued measure (not merely a natural number), because Σ-flattening needs extra "weight" to pay for.
5. `thin`/`thick` and the `Knockout` witness (McBride) as a structurally-recursive reformulation of the occurs check that also proves maximality.

#### Relevant Questions
1. Why is the pattern fragment decidable and unitary while full higher-order unification is not?
2. Walk through why $u[x]=\mathrm{suc}(v[x,y])$ can be pruned but $u[x]=\mathrm{suc}(v[x,w[y]])$ cannot — what makes the nested-metavariable case different?
3. Why does McBride's approach need an *ordinal*-valued termination measure rather than a natural-number one?
4. Why is termination of the full dynamic/heterogeneous pattern-unification algorithm still an open problem, per Gundry's thesis?

---

## 10. Elaboration, Bidirectional Type Checking, and Metavariable Resolution (Core Topic)

#### Pre-requisites
[[#9. Higher-Order Unification and Miller's Pattern Fragment (Core Topic)|Topic 9]].

#### Why this topic is important
This is where the project's elaborator gets assembled: metavariables plus
constraint postponement plus bidirectional (check/synth) typing modes is
precisely the architecture Lean's own elaborator and kernel unifier use, and
several sources here are direct algorithmic blueprints rather than only
theory.

#### Sources to Study
1. [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/book-guidelines|Elaboration in Dependent Type Theory (De Moura, Kong, Avigad, van Doorn & von Raumer)]]
   - Higher-Order Unification, Constraints and Justifications, The Constraint Simplification Procedure, The Constraint Solving Procedure
2. [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/book-guidelines|Complete and Easy Bidirectional Typechecking (Dunfield & Krishnaswami)]]
   - [[Bidirectional-Typechecking-Foundations]]
   - [[Metatheory-of-the-Algorithm]]
3. [[32_Tridirectional_Typechecking_Dunfield_Pfenning/book-guidelines|Tridirectional Typechecking (Dunfield & Pfenning)]]
   - [[Soundness-and-Completeness-of-the-Simple-Tridirectional-System]]
4. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference, Haskell and Dependent Types (Gundry)]]
   - [[Elaborating-inch-into-the-Evidence-Language]]
   - [[The-Evidence-Language]]
5. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory (Angiuli & Gratzer)]]
   - [[Metatheory-and-Implementation-of-Type-Theory]]

#### Key Concepts and Definitions
1. Checking vs. synthesis judgments grounded in focalization (Andreoli), and the application judgment for spine-form applications under polymorphism.
2. Ordered algorithmic contexts with unsolved/solved existential variables, and context extension as the central metatheoretic device for soundness/completeness/decidability.
3. Justifications (asserted/assumption/join) enabling nonchronological backtracking over a priority-queue constraint solver, instead of re-exploring failed search space.
4. Elaboration as an algorithmic judgment $\Gamma\vdash\tau\ \mathrm{type}\rightsquigarrow A$, with normalization sufficing for (and equivalent to) decidable definitional equality.

#### Relevant Questions
1. Why is `subst`-predicate-style inference genuinely higher-order and inherently ambiguous, and what does De Moura et al.'s justification-tracking buy against that?
2. Why must context-extension ordering be rigid for ordinary declarations but flexible for existential-variable solutions?
3. Why does a normalization structure suffice for, and turn out equivalent to, decidable definitional equality?

---

## 11. Trusted Kernels, the de Bruijn Criterion, and Proof Automation (Core Topic)

#### Pre-requisites
[[#8. Focused Sequent Calculi and Proof Certificates (Core Topic)|Topic 8]], [[#10. Elaboration, Bidirectional Type Checking, and Metavariable Resolution (Core Topic)|Topic 10]].

#### Why this topic is important
This directly addresses the trusted-computing-base requirement in the
project's depth requirements: a small, independently-checkable kernel that
accepts arbitrarily clever external search (tactics, automation, an embedded
ATP) without inheriting its complexity or risk of unsoundness.

#### Sources to Study
1. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Interactive-Theorem-Proving-and-the-LCF-Approach]]
2. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types (Chlipala)]]
   - [[The-Coq-Proof-Assistant-and-Certified-Programming]]
   - [[Proof-Automation-by-Logic-Programming]]
   - [[The-Ltac-Tactic-Language]]
   - [[Proof-by-Reflection]]
3. [[68_A_semantic_framework_for_proof_evidence_Dale_Miller_2016/book-guidelines|A Semantic Framework for Proof Evidence (Chihani, Miller & Renaud)]]
   - Trusted Kernels and Proof Sharing (no article yet)

#### Key Concepts and Definitions
1. The de Bruijn criterion: a small trusted kernel re-checks every generated proof term regardless of how the term was found, decoupling trust from search complexity.
2. LCF's abstract `thm` type: soundness enforced by the type discipline itself, not by trusted search code — tactics/tacticals are derived, never privileged.
3. Proof by reflection: reifying a proposition into inductive syntax plus a denotation function, yielding constant/linear-size proof terms instead of superlinear ones.
4. `auto`/`eauto` bounded-depth backtracking search over hint databases, and `match goal`'s backtracking semantics (retries on tactic-body failure, unlike ordinary pattern matching).

#### Relevant Questions
1. What does the de Bruijn criterion mean precisely, and why does it separate Coq/HOL-style systems from ACL2/PVS-style ones?
2. Why does soundness burden sit on the type discipline of the abstract `thm` type rather than on the correctness of the search/tactic code?
3. Why does proof by reflection avoid superlinear proof-term blowup, and why does naive reification fail on terms under a binder (fixed via `@?X` patterns)?

---

## 12. The λΠ-Calculus Modulo Theory and Logical Framework Interoperability (Core Topic)

#### Pre-requisites
[[#9. Higher-Order Unification and Miller's Pattern Fragment (Core Topic)|Topic 9]], [[#11. Trusted Kernels, the de Bruijn Criterion, and Proof Automation (Core Topic)|Topic 11]].

#### Why this topic is important
Dedukti and its ecosystem are a concrete, implemented instance of exactly
the trusted-kernel-plus-rewriting architecture this project needs: a
minimal type theory (λΠ) extended by user-defined rewrite rules, where
Miller patterns govern which rewrite rules preserve subject reduction and
decidable type-checking.

#### Sources to Study
1. [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/book-guidelines|Typechecking in the λΠ-Calculus Modulo (Saillard)]]
   - [[The-lambda-Pi-Calculus-Modulo-as-a-Logical-Framework]]
   - [[Well-Typedness-of-Rewrite-Rules]]
   - [[Type-Inference-and-Type-Checking-Algorithms]]
2. [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/book-guidelines|Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory (Assaf et al.)]]
   - [[The-Lambda-Pi-Calculus-Modulo-Theory]]
   - [[Decidability-via-Effective-Subsystems]]
3. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/book-guidelines|Interoperability between proof systems using Dedukti (Thiré)]]
   - [[Interoperability-Between-Type-Systems]]
   - [[Dedukti-An-Implementation-of-Lambda-Pi-calculus-Modulo-Theory]]
   - [[Universo-Deciding-Universe-Level-Embeddings]]
4. [[88_LAMBDA_PI_GRIENENBERGER_2025/book-guidelines|Combining Computational Theories (Grienenberger)]]
   - [[Interoperability-of-Proof-Assistants]]
   - [[Deduction-Modulo-Theory]]

#### Key Concepts and Definitions
1. Static vs. definable symbols, and Miller patterns governing well-typed rewrite-rule left-hand sides.
2. Well-formed vs. weakly-well-formed rewrite systems, and the exact characterization of type-safety as an inclusion between unification-constraint solution sets.
3. The Effectiveness Theorem: confluence plus well-typed rules gives subject reduction; adding termination gives decidable type-checking (confluence must be established *first*).
4. Universo's pipeline (elaboration → free-CTS generation → SMT solving → reconstruction) as a direct precedent for embedding an SMT solver in a dependently-typed toolchain.

#### Relevant Questions
1. When is it type-safe to linearize a non-left-linear rewrite rule, and what's the difference between a most-general solution and a weaker pre-solution?
2. Why must confluence be established before termination in the Effectiveness Theorem's proof order?
3. Why can't Universo simply reuse the stock type checker for universe-level constraints, and why does it need SMT?

---

## 13. Hoare Logic, Separation Logic, and Local Reasoning (Core Topic)

#### Pre-requisites
[[#1. First-Order Syntax, Semantics, and Classical Metalogic (Core Topic)|Topic 1]], [[#3. Sequent Calculus and Cut Elimination (Core Topic)|Topic 3]].

#### Why this topic is important
This is the direct source for the compiler's Hoare-triple/requires-ensures
contract layer: separation logic's frame rule is the concrete mechanism
behind compositional (per-procedure) verification-condition generation, and
the B-Book's generalized-substitution semantics is a fully worked
alternative WP-based foundation for the same proof obligations.

#### Sources to Study
1. [[28_An_Introduction_Separation_Logic_Reynolds_Copenhagen_2008/book-guidelines|An Introduction to Separation Logic (Reynolds)]]
   - [[Hoare-Logic-Foundations]]
   - [[The-Frame-Rule-and-Local-Reasoning]]
   - [[Inference-Rules-for-Heap-Manipulating-Commands]]
   - [[Procedures-And-Hypothetical-Specifications]]
2. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book (Abrial)]]
   - [[Semantics-of-Generalized-Substitutions]]
   - [[Sequencing-Loops-and-Termination-Proofs]]
   - [[Refinement-Theory]]
3. [[43_Modeling_in_Event-B_JR_Abrial_2010/book-guidelines|Modeling in Event-B (Abrial)]]
   - [[Proof-Obligation-Rules]]
   - [[The-Sequent-Calculus-and-Logical-Inference]]

#### Key Concepts and Definitions
1. Separating conjunction $*$/separating implication $-\!*$, points-to $e\mapsto e'$, and the unsoundness of unrestricted contraction/weakening over these assertions.
2. The frame rule as the mechanism succeeding where the classical rule of constancy fails, enabling compositional/local reasoning.
3. Dijkstra's healthiness conditions for generalized substitutions, and the normalized-form theorem $P\mid @x'\cdot(Q\Rightarrow x{:=}x')$ unifying WP semantics with a relational model.
4. Event-B's proof obligation schema (INV, FIS, GRD, SIM, VAR, ...) as a fully worked, mechanically checkable instance of Hoare-style contract discharge.

#### Relevant Questions
1. Why does the frame rule succeed at compositional reasoning where the rule of constancy fails?
2. Why must the INV proof obligation differ structurally between a single event and a refining event (witness predicates only in the refining case)?
3. How does the B-Book's normalized-form theorem let a single fixpoint-based semantics justify both the WP and the relational reading of a generalized substitution?

---

## 14. Refinement, Formal Specification, and Proof-Obligation Methodology (Core Topic)

#### Pre-requisites
[[#13. Hoare Logic, Separation Logic, and Local Reasoning (Core Topic)|Topic 13]].

#### Why this topic is important
Refinement is the formal-methods analogue of the compiler's own
elaboration-then-checking pipeline: a gluing/linking invariant proof
obligation is structurally the same kind of soundness argument the
elaborator's context-extension machinery (Topic 10) makes, just at the
specification level instead of the term level.

#### Sources to Study
1. [[27_The_B_Book_Abrial_2005/book-guidelines|The B-Book (Abrial)]]
   - [[Algorithm-Construction-Methodology]]
   - [[Refinement-Theory]]
2. [[23_Refinement_Semantics_Derrick_Boiten_2018/book-guidelines|Refinement: Semantics, Languages and Applications (Derrick & Boiten)]]
   - [[State-Based-Specification-Languages-Z-and-B]]
   - [[Event-B-and-Abstract-State-Machines-ASM]]
   - [[Beyond-This-Book-Related-Refinement-Theories]]
3. [[19_TLAplus_Lesle_Lamport/book-guidelines|Specifying Systems: The TLA+ Language and Tools (Lamport)]]
   - [[Composing-Specifications]]
   - [[Advanced-Specification-Examples]]
   - [[Writing-Specifications-Engineering-Practice]]

#### Key Concepts and Definitions
1. Refinement $S\sqsubseteq T$ as a partial order ($pre(S)\subseteq pre(T)\wedge rel(T)\subseteq rel(S)$), and abstract-machine refinement via a total gluing/linking invariant.
2. Forward vs. backward simulation, and why Event-B's generalized $m$:$n$ simulation is needed once event splitting/merging is allowed (dropping strict conformality).
3. Rely-guarantee composition ($E\overset{+}{\leadsto}M$) for open systems, versus interleaving composition for closed, machine-closed components.

#### Relevant Questions
1. Why must the gluing relation in abstract-machine refinement be total, and how does "doing less but also more" stay harmless under the Hiding Principle?
2. Why does Event-B's willingness to split/merge events force a generalized $m$:$n$ simulation instead of strict 1:1?
3. What problem does rely-guarantee composition ($E\overset{+}{\leadsto}M$) solve that a plain implication between specifications doesn't?

---

## 15. Abductive Reasoning, Interpolation, and Constraint/Analysis Combination (Core Topic)

#### Pre-requisites
[[#6. Resolution, Tableaux, and Automated First-Order Theorem Proving (Core Topic)|Topic 6]], [[#13. Hoare Logic, Separation Logic, and Local Reasoning (Core Topic)|Topic 13]].

#### Why this topic is important
This is the project's counterexample/precondition-inference thread: bi-
abduction is exactly the mechanism for inferring the missing preconditions
that make a Hoare triple valid without a global specification, and Craig
interpolation is the classical tool for refining an abstract-interpretation
domain or combining decision procedures across theory boundaries — both are
central to the planned CSP kernel's counterexample search.

#### Sources to Study
1. [[38_Compositional_Shape_Analysis_by_means_of_Bi-Abduction_Calcagno/book-guidelines|Compositional Shape Analysis by Means of Bi-Abduction (Calcagno, Distefano, O'Hearn & Yang)]]
   - [[Abductive-Inference]]
   - [[Bi-Abduction]]
   - [[Proof-Systems-and-Algorithms-for-Abduction]]
   - [[Quality-and-Ordering-of-Abduction-Solutions]]
2. [[12_proof_theory_algebra_logic_hiroakira_ono/book-guidelines|Proof Theory and Algebra in Logic (Ono)]]
   - [[Proof-Theoretic-Consequences-of-Cut-Elimination]] (Maehara's interpolation method)
3. [[10_boolos_burgess_computability_logic_2007/book-guidelines|Computability and Logic (Boolos, Burgess, Jeffrey)]]
   - Interpolation and definability article
4. [[15_handbook_logic_automated_reasoning_harrison_2009/book-guidelines|Handbook of Practical Logic and Automated Reasoning (Harrison)]]
   - [[Combining-Decision-Procedures]]
5. [[73_Interprocedural_Shape_Analysis_Using_Separation_Logic_Illous_Rival_2021/book-guidelines|Interprocedural Shape Analysis Using Separation Logic (Illous, Lemerre & Rival)]]
   - Abstract Intersection and Composition Algorithms (no article yet)
6. [[79_Modular_Constraint_Solver_Cooperation_via_Abstract_Interpretation_Pierre_Talbot_2020/book-guidelines|Modular Constraint Solver Cooperation via Abstract Interpretation (Talbot, Monfroy & Truchet)]]
   - [[Delayed-Product-DP]]
   - [[Relation-to-Other-Cooperation-Frameworks]]

#### Key Concepts and Definitions
1. Abduction as missing-hypothesis inference ($A\wedge M\vdash G$ classically, $A * M\vdash G$ in separation logic), constrained by consistency and minimality.
2. Bi-abduction: jointly inferring an anti-frame and a frame ($\Delta * ?\text{anti-frame}\vdash H * ?\text{frame}$) — the inverse of the ordinary frame-inference problem — enabling compositional analysis without a precomputed global spec.
3. Maehara's syntactic method for proving Craig interpolation directly from a cut-free sequent derivation, versus the model-theoretic proof.
4. Nelson–Oppen combination of decision procedures, and why stable-infiniteness/convexity failures (linear-integer, nonlinear-real arithmetic) force case-splitting.

#### Relevant Questions
1. In a worked bi-abduction example, why is the abduced anti-frame exactly `list(y)` — not weaker or stronger — and what does that reveal about the minimality criterion?
2. How does Maehara's syntactic interpolation method differ from, and improve on, the semantic model-theoretic proof of Craig interpolation?
3. Why does convexity failure in linear-integer and nonlinear-real arithmetic force Nelson–Oppen-style combination into case-splitting?

---

## 16. Constrained Horn Clauses and Clause Learning for Verification (Core Topic)

#### Pre-requisites
[[#7. Logic Programming: Proof Search as Computation (Core Topic)|Topic 7]], [[#15. Abductive Reasoning, Interpolation, and Constraint/Analysis Combination (Core Topic)|Topic 15]].

#### Why this topic is important
CHCs are the standard intermediate representation for invariant-generation
and requires/ensures verification conditions in modern verifiers — this is
the concrete target format the project's abstract-interpretation and CSP
kernel should be able to both produce and discharge.

#### Sources to Study
1. [[69_Acceleration_Driven_Clause_Learning_for_CHC_Frohn_2023/book-guidelines|Acceleration Driven Clause Learning for CHCs (Frohn & Giesl)]]
   - [[Constrained-Horn-Clauses-(CHCs)]]
   - [[Resolution-for-CHCs]]
   - [[Syntactic-Implicants-and-Redundancy]]
   - [[The-ADCL-Calculus]]
   - [[Metatheoretic-Properties-of-ADCL]]

#### Key Concepts and Definitions
1. CHC as fact/rule/query/conditional-empty-clause forms, with A-interpretation as the semantic target for satisfiability.
2. Resolution for CHCs via MGU-based resolvents, lifted to sequences, with soundness proved via a lifting lemma.
3. Syntactic implicants and the redundancy relation $\varphi\sqsubseteq\pi$, which lift loop acceleration from conjunctive-only CHCs to the general case.
4. The ADCL calculus's state (search trace + blocking-clause sequence) and its rules (Init/Step/Accelerate/Covered/Backtrack/Refute/Prove), with refutational completeness proved but termination shown false in general (via a Thue–Morse-sequence non-termination proof).

#### Relevant Questions
1. Why must acceleration originally be restricted to conjunctive CHCs, and how do syntactic implicants lift this restriction?
2. What justifies the Accelerate rule collapsing an entire recursive suffix's blocking history into a single formula via $\mathrm{res}(\varphi,\varphi)\sqsubseteq\varphi$?
3. How does the Thue–Morse-sequence non-termination proof avoid contradicting ADCL's refutational completeness on unsatisfiable instances?

---

## 17. Equality Saturation, E-Graphs, and Proof-Term Generalization (Core Topic)

#### Pre-requisites
[[#5. First-Order Unification and Equality Reasoning (Core Topic)|Topic 5]].

#### Why this topic is important
Equality saturation is a compiler-optimization and translation-validation
technique built directly on congruence closure (Topic 5) that eliminates
phase-ordering problems — directly relevant to a Rust compiler's own
optimization and proof-generation passes, and egglog shows how the same
e-graph machinery subsumes Datalog-style fixpoint reasoning (Topic 7).

#### Sources to Study
1. [[39_Equality-Saturation-RossThesis2012/book-guidelines|Program Expression Graphs and Equality Saturation (Tate)]]
   - [[Equality-Saturation]]
   - [[Translation-Validation]]
   - [[Learning-Optimizations-from-Proofs]]
   - [[Category-Theoretic-Foundations-of-Proof-Generalization]]
2. [[71_Unifying_Datalog_and_Equality_Saturation/book-guidelines|Better Together: Unifying Datalog and Equality Saturation (Zhang et al.)]]
   - [[Fixpoint-Reasoning-Frameworks]]
   - [[The-E-Graph-Data-Structure]]
   - [[The-egglog-Language-Model]]
   - [[Unification-and-Logic-Programming-in-egglog]]

#### Key Concepts and Definitions
1. Additive equality analyses vs. destructive rewrites: the additivity property ($ir_1\to ir_2\implies ir_1\sqsubseteq ir_2$) that eliminates phase-ordering by keeping all rewrites simultaneously present.
2. Monotonic analyses implying confluence (hence a unique saturated normal form), and non-termination bounded by an expression-count cap.
3. E-nodes/e-classes, congruence, e-matching, and `:merge` expressions resolving functional-dependency conflicts — the mechanism letting egglog subsume both Datalog's lattice semantics and equality saturation's congruence closure.
4. Backward-from-conclusion generalization of a proof (pushout/pullback/pushout-completion) as a category-theoretic account of "learning an optimization rule from one concrete proof instance," proven maximally general.

#### Relevant Questions
1. Why does monotonicity of an analysis guarantee confluence, not merely termination?
2. Why does naive metavariable substitution under-generalize when learning a rewrite rule from a concrete proof, and how does processing backward from the conclusion resolve it?
3. How does egglog's "function as map with `:merge`" mechanism let one uniform construct subsume both Datalog-style lattice joins and e-graph congruence closure?

---

## 18. Linear Logic and the Curry–Howard Correspondence for Concurrency (Core Topic)

#### Pre-requisites
[[#2. Natural Deduction and the Curry–Howard Correspondence (Core Topic)|Topic 2]], [[#3. Sequent Calculus and Cut Elimination (Core Topic)|Topic 3]].

#### Why this topic is important
Linear logic is the proof-theoretic origin of the resource-sensitive
reasoning behind separation logic's structural-rule restrictions (Topic 13)
and provides, via session types, a second worked example of Curry–Howard
where cut elimination has direct *operational* content (deadlock/race
freedom) — a useful model for what a proof certificate (Topic 8) should
guarantee about the process it certifies.

#### Sources to Study
1. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types (Girard)]]
   - [[Linear-Logic]]
2. [[09_proof_theory_logic_programming_dale_miller_2025/book-guidelines|Proof Theory and Logic Programming (Miller, 2025)]]
   - Linear Logic and Linear Logic Programming chapters (no articles yet)
3. [[22_wadler_2012_propositions_as_sessions/book-guidelines|Propositions as Sessions (Wadler)]]
   - [[The-Curry-Howard-Correspondence-for-Concurrency]]
   - [[CP-a-Classical-Linear-Logic-Process-Calculus]]
   - [[Commuting-Conversions-and-Cut-Elimination]]
4. [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/book-guidelines|Domain-Aware Session Types (Caires, Pérez, Pfenning & Toninho)]]
   - [[Session-Types-via-the-Curry-Howard-Correspondence]]
   - [[Type-Safety-and-Correctness-Results]]

#### Key Concepts and Definitions
1. Structural-rule restriction (dropping weakening/contraction) motivating linear logic's dual connectives (tensor/par, plus/with) and exponentials (!/?) for controlled reuse.
2. Proof nets as "natural deduction done right" for linear logic — graph-based, order-independent, with local and parallel cut elimination.
3. Propositions-as-session-types: cut elimination read as communication, with top-level cut elimination proved equivalent to deadlock freedom.
4. Linearity guaranteeing race-freedom directly from the sequent calculus's context-disjointness side condition on the Cut rule.

#### Relevant Questions
1. Why was linear logic born from fixing coherence-space semantics specifically for the sum type?
2. Why does Curry–Howard for session types guarantee race and deadlock freedom essentially "for free," rather than as a separately proved property?
3. Why does the two-sided sequent presentation of intuitionistic session types ($\pi$DILL) force two separate output rules where the classical (CP) presentation needs only one?

---

## 19. Tree Automata, Monadic Second-Order Logic, and Decidable Fragments (Core Topic)

#### Pre-requisites
[[#5. First-Order Unification and Equality Reasoning (Core Topic)|Topic 5]].

#### Why this topic is important
Tree automata give a decision-procedure engine for logical theories over
terms and are the concrete mechanism the standing project's goals name for
representing abstract data structures as automata/DFA-based domains — this
topic supplies the automated-reasoning half of that (decidability via
automata-theoretic reduction) that Topic-Theory's own treatment stops short of.

#### Sources to Study
1. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications (Comon et al.)]]
   - [[Weak-Monadic-Second-Order-Logic-and-Tree-Automata]]
   - [[Alternating-Tree-Automata]]
   - [[Context-Free-Tree-Languages]]
2. [[34_The_Constraint_Satisfaction_Problem_Complexity_and_Approximability/book-guidelines|The Constraint Satisfaction Problem: Complexity and Approximability (Krokhin & Živný, eds.)]]
   - [[Quantified-CSP]]

#### Key Concepts and Definitions
1. The Thatcher–Wright correspondence: WSkS-definable ≡ recognizable-by-tree-automaton, with non-elementary complexity in the quantifier-alternation depth.
2. Alternating tree automata equal in power to deterministic bottom-up automata (exponential conversion), with complementation "free" under conjunction unlike nondeterministic complementation.
3. IO vs. OI derivation strategies for context-free tree grammars, and their collapse under linearity.
4. QCSP's surjective-polymorphism Galois connection running parallel to, but structurally "unwieldier" than, plain CSP's clone-based Galois connection.

#### Relevant Questions
1. How does the completeness direction of the Thatcher–Wright correspondence encode an existential second-order quantifier as "guessing an accepting run"?
2. Why does conjunction make alternating-automata complementation free, while nondeterministic-automata complementation requires exponential determinization first?
3. Why do IO and OI tree-grammar derivation strategies coincide exactly under linearity?

---

## 20. Categorical and Topos-Theoretic Semantics of Logic (Core Topic)

#### Pre-requisites
[[#2. Natural Deduction and the Curry–Howard Correspondence (Core Topic)|Topic 2]].

#### Why this topic is important
This is background depth rather than a direct implementation dependency:
Goldblatt's topos semantics gives the model-theoretic counterpart to the
intuitionistic/constructive logic underlying definitional equality, and
Tate's pushout/pullback account of proof generalization (Topic 17) is a
concrete instance of exactly this categorical machinery being put to
algorithmic use.

#### Sources to Study
1. [[80_topoi-the-categorical-analysis-of-logic-Goldblatt/book-guidelines|Topoi: The Categorical Analysis of Logic (Goldblatt)]]
   - [[Intuitionism-and-Heyting-Semantics]]
   - [[Elementary-First-Order-Truth-in-a-Topos]]
   - [[Adjointness-and-Quantifiers]]
   - [[Logical-Geometry]]

#### Key Concepts and Definitions
1. Heyting algebras (relative pseudo-complement) and Kripke semantics with a monotone forcing relation, as the constructive alternative to Boolean semantics.
2. Quantifiers as adjoints: $\exists_f$ left adjoint / $\forall_f$ right adjoint to substitution $f^*$.
3. Geometric morphisms and the Mitchell–Bénabou internal language, culminating in the classifying topos of a theory treated as a site.

#### Relevant Questions
1. How does Boolean implication differ from Heyting implication, and which classical law fails constructively?
2. What is the categorical significance of reading quantifiers as adjoint functors rather than as primitive syntax?
3. Why must the inverse-image functor of a geometric morphism be left exact?

---

## Topics Without Dedicated Book Coverage

No gaps were found requiring purely-external sourcing: every fundamental
identified in the preliminary background sketch (Step 1) — first-order
logic, unification (first- and higher-order), resolution, sequent calculi
and cut elimination, logic programming, trusted kernels, Hoare/separation
logic, abduction, CHCs, equality saturation, linear logic — has at least one
strong source already processed in `vaults/`. The area is unusually
well-covered; the main gap is *depth of extraction* rather than *absence of
sources*: books 09 (Miller, *Proof Theory and Logic Programming*, 2025), 40
(Jamner, Pyrosome), 68 (Chihani/Miller/Renaud, FPC), 70 (Abel–Pientka), and
73 (Illous–Lemerre–Rival) have no generated topic articles yet — running
`book-topic-batch` on these five, all cited above as primary or
co-primary sources for Topics 3, 7, 8, 9, 12, and 15, would convert this
roadmap's guidelines-only citations into full deep-dive notes.
