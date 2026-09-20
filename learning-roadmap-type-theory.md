# Learning Roadmap — Type Theory

Type Theory is the ground floor of the whole project: it supplies the term/type
representation the elaborator manipulates, the kernel's `isDefEq` judgment that
decides when two terms are the same, and the surface language in which
refinement contracts get expressed. This sequence starts from judgments and
the Curry–Howard correspondence, builds up the dependent-type core
(Π/Σ-types, equality, inductive families, universes), then turns to the two
things the compiler actually needs built: an elaborator (bidirectional
typing, metavariables, Miller-pattern unification) and a rewriting-based
trusted kernel (λΠ-calculus modulo theory, in the Dedukti tradition). It
closes with the semantic/foundational depth (categorical semantics, HoTT)
and two adjacent threads (refinement types, automata-as-domains) that
connect this area back to `automated-reasoning`, `sat-smt-csp`, and
`static-analysis`.

---

## 1. Judgments, Contexts, and the Curry–Howard Correspondence (Core Topic)

#### Pre-requisites
None — this is the entry point of the whole Focus Area.

#### Why this topic is important
Every later topic in this roadmap — typing rules, the elaborator, the
trusted kernel — is a judgment form built out of the same primitive: a
derivation object standing for a proof/program pair. Getting comfortable
with "judgment as the shared ancestor of a type checker and a proof
checker" now is what makes Topics 9–13 (bidirectional typing, elaboration,
the λΠ-modulo kernel) legible later instead of feeling like unrelated
machinery.

#### Sources to Study
1. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming (Thompson)]]
   - [[The-Curry-Howard-Isomorphism-(Propositions-as-Types)]]
   - [[Natural-Deduction-and-Predicate-Logic]]
   - [[Contexts,-Derivability-and-Type-Uniqueness]]
2. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types (Girard)]]
   - [[Natural-Deduction]]
   - [[The-Curry-Howard-Isomorphism]]
3. [[01_programming_in_MLTT/book-guidelines|Programming in Martin-Löf's Type Theory (Nordström/Petersson/Smith)]]
   - [[Propositions-as-Sets-(The-Curry-Howard-Correspondence)]]
   - [[The-Semantics-of-Judgement-Forms]]
   - [[General-Proof-Rules]]
4. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types (Chlipala)]]
   - [[The-Curry-Howard-Correspondence]]

#### Key Concepts and Definitions
1. Judgment $p:P$ and derivations built by rule application; discharge of assumptions vs. "alive" hypotheses.
2. Natural deduction's introduction/elimination symmetry, and the deduction-to-λ-term interpretation (hypothesis→variable, ∧I→pair, ⇒I→abstraction).
3. Primary equations (β, projection) vs. secondary equations (η, surjective pairing).
4. A normal proof corresponds to a normal term independently — the basis for calling Curry–Howard a genuine isomorphism, not a mere bijection.
5. Curry–Howard's "strain points": named vs. anonymous discharge, and where the correspondence stops being perfectly tree-shaped.

#### Relevant Questions
1. Why does Girard insist Curry–Howard is a true isomorphism, not just a bijection?
2. What does it mean for a hypothesis to be "alive" vs. "discharged," and how does ⇒I show natural deduction is only "vaguely" tree-like?
3. Why do the same four rules, read once as formula/proof and once as type/program, constitute the correspondence — and where does that reading show strain?

---

## 2. The Lambda Calculus and Operational/Computational Semantics (Core Topic)

#### Pre-requisites
[[#1. Judgments, Contexts, and the Curry–Howard Correspondence (Core Topic)|Topic 1]] (judgments and typing-rule notation).

#### Why this topic is important
The elaborator's term representation and the kernel's reduction/defeq
machinery are both built directly on top of the λ-calculus's substitution
and β-reduction. Progress + preservation here is the same safety argument
you'll later re-run, in a much more elaborate form, for the dependently
typed kernel (Topics 5, 13).

#### Sources to Study
1. [[04_TAPL_Pierce_2002/book-guidelines|Types and Programming Languages (Pierce)]]
   - Untyped and simply-typed λ-calculus, operational semantics, and type-safety articles ([[Untyped-Lambda-Calculus]]-family; see the book's Topic List for the full 27-article set)
2. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages (Harper)]]
   - Function types and the λ-calculus, System T, PCF articles

#### Key Concepts and Definitions
1. Untyped λ-calculus: abstraction, application, capture-avoiding substitution, β-reduction.
2. De Bruijn nameless representation and the shifting operation it requires.
3. Church encodings and fixed-point (Y/Z) combinators for recursion without a primitive construct.
4. Simply typed λ-calculus with contexts $\Gamma \vdash t : T$; typing rules T-Var/T-Abs/T-App.
5. Inversion, uniqueness of types, weakening, permutation; canonical-forms lemma.
6. Type safety = progress + preservation.

#### Relevant Questions
1. Why must substitution avoid variable capture, and how do fixed-point combinators encode recursion without a primitive construct?
2. Why does de Bruijn substitution need shifting that named substitution doesn't?
3. How do progress and preservation together entail that a well-typed term never gets stuck?

---

## 3. Subtyping, Polymorphism, and System F (Core Topic)

#### Pre-requisites
[[#2. The Lambda Calculus and Operational/Computational Semantics (Core Topic)|Topic 2]].

#### Why this topic is important
System F's reducibility-candidates normalization proof and its
operational reading of $\forall$ as a "plugging instruction" are the
last simply-typed-world ideas before dependent types make everything
context-relative. Subtyping's safety metatheory (progress/preservation
under $<:$) is also the closest non-dependent analogue to the
subsumption reasoning refinement-type checking will need in Topic 17.

#### Sources to Study
1. [[03_proofs_and_types_girard_1989/book-guidelines|Proofs and Types (Girard)]]
   - [[System-F-and-Polymorphism]]
   - [[Semantics-of-System-F]]
2. [[04_TAPL_Pierce_2002/book-guidelines|Types and Programming Languages (Pierce)]]
   - Subtyping (+ metatheory/algorithms), [[Universal-Types-(System-F)]], bounded quantification articles
3. [[07_practical_foundations_robert_harper_2012/book-guidelines|Practical Foundations for Programming Languages (Harper)]]
   - System F/polymorphism, subtyping articles

#### Key Concepts and Definitions
1. System F types/terms: types as $(\wedge, \Rightarrow)$-formulas plus $\forall$; polymorphic quantification.
2. Strong normalization for System F via reducibility candidates (not plain structural induction).
3. Coherence-space denotational semantics.
4. Subtyping judgment $t : T$ with structural subsumption; safety metatheory under $<:$.
5. Bounded quantification, existential types for data abstraction.
6. Higher-order polymorphism: type operators, kinding, System F$\omega$.

#### Relevant Questions
1. Why does strong normalisation for F require a reducibility-candidate argument, not a simple structural induction?
2. In what sense is a type a "plugging instruction" under the operational reading of System F?
3. What does subtyping's progress+preservation proof need beyond simple typing's?

---

## 4. Dependent Types: Π-Types, Σ-Types, and Type Families (Core Topic)

#### Pre-requisites
[[#3. Subtyping, Polymorphism, and System F (Core Topic)|Topic 3]] (non-dependent quantification as a baseline to generalize from).

#### Why this topic is important
This is the surface language of the refinement-type compiler itself.
Π and Σ are the type formers everything else in this roadmap (universes,
elaboration, the λΠ-calculus-modulo kernel) is stated in terms of, and
the explicit substitution calculus introduced here is exactly the
plumbing the elaborator's context management will need.

#### Sources to Study
1. [[01_programming_in_MLTT/book-guidelines|Programming in Martin-Löf's Type Theory (Nordström/Petersson/Smith)]]
   - [[The-Cartesian-Product-of-a-Family-and-the-Universal-Quantifier]]
   - [[Equality-Sets]]
   - [[The-Cartesian-Product-of-Two-Sets-and-Conjunction]]
   - [[Disjoint-Unions-and-the-Existential-Quantifier]]
2. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory (Angiuli & Gratzer)]]
   - [[Full-Spectrum-Dependent-Types]]
   - [[Judgments-and-the-Substitution-Calculus]]
   - [[Type-Connectives-via-Universal-Properties]]
3. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming (Thompson)]]
   - [[Quantifiers-and-Dependent-Types]]
4. [[05_ATAPL_Pierce_2004/book-guidelines|Advanced Topics in Types and Programming Languages (ed. Pierce)]]
   - [[Dependent-Types]]

#### Key Concepts and Definitions
1. $\Pi(A,B)$ as the dependent function set, canonical element $\lambda(b)$, elimination via `apply`/`funsplit`.
2. Non-dependent product $A \times B$ as a special case of Σ; projections via `split`.
3. Hypothetical judgments and context-relative typing $\Gamma \vdash A\ \mathrm{type}$.
4. Explicit substitution calculus: weakening $\mathbf p$, variable $\mathbf q$, substitution extension $\gamma.a$.
5. Π's "mapping-in" universal property (internalizing hypothetical judgment) vs. Σ's (internalizing pairs).
6. Functional extensionality provable via $Eq$ but not via the intensional identity type $Id$.

#### Relevant Questions
1. Why is Π's generality essential for interpreting $\forall$ and dependent specifications?
2. Why can $\langle \mathrm{fst}(z), \mathrm{snd}(z)\rangle =_{A\times B} z$ be proved propositionally but not judgementally?
3. Why must Σ-types fail to behave as existential quantifiers under "propositions as some types"?

---

## 5. Definitional Equality, Reduction, and Normalization (Core Topic)

#### Pre-requisites
[[#4. Dependent Types: Π-Types, Σ-Types, and Type Families (Core Topic)|Topic 4]].

#### Why this topic is important
This is the mechanism your elaborator's `isDefEq` will need — the exact
question of when two terms in the trusted kernel count as "the same
type." The undecidability result for extensional equality reflection is
also the concrete reason the kernel design in Topic 13 has to commit to
intensional equality plus controlled rewrite rules instead.

#### Sources to Study
1. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming (Thompson)]]
   - [[Equality-in-Type-Theory]]
   - [[Normalisation-and-Computational-Properties]]
2. [[17_HofmannExtensionalIntensionalTypeTheory1995/book-guidelines|Extensional Concepts in Intensional Type Theory (Hofmann)]]
   - Definitional vs. propositional equality; independence-of-UIP articles

#### Key Concepts and Definitions
1. Computation rules vs. equivalence (extensionality) rules; convertibility $\leftrightarrow_{\beta\eta}$.
2. Identity type $I(A,a,b)$ and its elimination operator $J$.
3. Equality reflection rule (defines ETT) vs. intensional Id-types.
4. ETT's definitional equality/typechecking is undecidable — two independent proofs (SK-combinator encoding; Hofmann's Turing-machine interpreter).
5. Uniqueness of Identity Proofs (UIP) and Axiom K; the groupoid model refuting UIP.

#### Relevant Questions
1. Why does `succ(n)` hold propositionally but not judgementally equal to `addone(n)`?
2. Why is definitional equality in ETT undecidable, and what role does the equality-reflection rule play?
3. Why can identity types not get a mapping-in universal property the way Eq-types can?

---

## 6. Inductive Types, Pattern Matching, and Elimination Principles (Core Topic)

#### Pre-requisites
[[#5. Definitional Equality, Reduction, and Normalization (Core Topic)|Topic 5]].

#### Why this topic is important
Inductive families are how both program data and proof terms get
represented in the elaborator, and the strict-positivity and
guarded-recursion conditions here are exactly the admissibility checks a
Rust kernel implementation has to enforce to stay sound. This is also
where "pattern matching vs. eliminators" gets settled — directly
relevant to how the compiler's surface syntax gets elaborated down to
core terms.

#### Sources to Study
1. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types (Chlipala)]]
   - [[Inductive-Types]]
   - [[Inductive-Predicates-and-Judgments]]
   - [[Coinductive-Types-and-Infinite-Data]]
2. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/book-guidelines|Dependently Typed Functional Programs and their Proofs (McBride)]]
   - [[Inductive-Datatypes-and-Their-Elimination]]
   - [[Pattern-Matching-for-Dependent-Types]]
   - [[Elimination-Rules-for-Refinement-Proof]]
3. [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/book-guidelines|Dedukti: A Logical Framework based on the λΠ-Calculus Modulo Theory]]
   - [[Inductive-Types-and-Universe-Hierarchies]]

#### Key Concepts and Definitions
1. Curry–Howard for inductive datatypes (True/False as unit/empty); strict positivity, and why naive HOAS breaks it.
2. Auto-generated induction principle `T_ind`; why mutual/nested inductives need manual reconstruction.
3. The four-part datatype schema — former, constructors, eliminator, ι-reduction — covering simple, parameterised, higher-order-recursive, and dependent-indexed families uniformly.
4. Guarded fixpoint construction, and the Fibonacci counterexample it's needed to repair.
5. Coquand's ALF admissibility conditions (no nesting, guarded recursion, unification-driven covering), and the conservativity theorem relating pattern matching to eliminators.

#### Relevant Questions
1. Why must inductive definitions satisfy strict positivity?
2. Why does the one-step eliminator fail for Burstall–Darlington-style Fibonacci, and how does the guarded-fixpoint construction repair it?
3. What is Berry's majority-function counterexample, and why does it show that constructor-form exhaustive/disjoint patterns aren't sufficient for intensionally correct matching?

---

## 7. Universes and Type Hierarchies (Core Topic)

#### Pre-requisites
[[#6. Inductive Types, Pattern Matching, and Elimination Principles (Core Topic)|Topic 6]].

#### Why this topic is important
A refinement-type compiler with a metaprogramming elaborator needs a
principled universe hierarchy to stay consistent (Girard's paradox is
not a theoretical curiosity — it's exactly the bug a "Type : Type"
kernel shortcut reintroduces). The cumulativity/lifting design choices
here directly shape how the kernel represents universe-polymorphic
definitions.

#### Sources to Study
1. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types (Chlipala)]]
   - [[Universes-and-Axioms]]
2. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/book-guidelines|Interoperability of Proof Systems (Thiré)]]
   - [[Cumulative-Type-Systems-(CTS)]]
   - [[Universo-Deciding-Universe-Level-Embeddings]]
3. [[02_type_theory_functional_programming_thompson_1999/book-guidelines|Type Theory and Functional Programming (Thompson)]]
   - [[Universes-and-Well-Founded-Types]]

#### Key Concepts and Definitions
1. `Set`/`Type`/`Prop`/`Kind` sorts; Girard's paradox and why a type of all types is inconsistent.
2. Universe hierarchy $U_0, U_1, \dots$ and cumulativity; universes à la Tarski (`El`) vs. à la Russell.
3. Large elimination, and why it fails to be structurally recursive.
4. The "multiple representation" problem under cumulativity, and explicit `lift` operators.
5. Universe polymorphism/indexing (per-sort $U_s$, $e_s$) in a Pure Type System embedding.

#### Relevant Questions
1. Why must a hierarchy of universes replace a single type of all types?
2. Why can't cumulativity be implemented by simply identifying $U_i$ with $U_{i+1}$, and what failure does an explicit `lift` operator repair?
3. Why does Girard's paradox arise from a "$U:U$" round-trip, and how does removing it avoid the paradox?

---

## 8. Intensional vs. Extensional Type Theory (Core Topic)

#### Pre-requisites
[[#5. Definitional Equality, Reduction, and Normalization (Core Topic)|Topic 5]], [[#7. Universes and Type Hierarchies (Core Topic)|Topic 7]].

#### Why this topic is important
This is the concrete design decision behind the whole kernel: an
intensional theory (decidable typechecking) plus controlled extensions,
versus an extensional one (undecidable). Hofmann's conservativity
theorem is the theoretical justification for adding `Funext`/`UIP` as
axioms without secretly changing what's provable — directly relevant to
deciding what the Rust kernel's trusted core will and won't include.

#### Sources to Study
1. [[17_HofmannExtensionalIntensionalTypeTheory1995/book-guidelines|Extensional Concepts in Intensional Type Theory (Hofmann)]]
   - Intensional/extensional TT, six extensional concepts, deliverables model, setoid model articles
2. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory (Angiuli & Gratzer)]]
   - [[Extensionality-versus-Intensionality]]

#### Key Concepts and Definitions
1. TTE's equality-reflection rule vs. TTI's eliminator-based Id-type ($J$).
2. UIP: definable at Unit/Void/Id/ℕ/Σ but not at universes.
3. Functional extensionality's non-derivability in ITT (strong-normalization argument), and Turner's `Ext` axiom.
4. Hofmann's conservativity theorem: ITT + Funext + UIP ≡ ETT for inhabitation.
5. The "deliverables" categorical model separating algorithm from correctness proof, vs. the refinement-type style of mixing them in one Σ-type.
6. Proof irrelevance as derivable (not axiomatized) via the extensional unit-type trick.

#### Relevant Questions
1. What precisely does it mean for TTE to be "conservative" over TTI, and why does this justify treating extended-ITT as no less expressive?
2. Why is it surprising that intensional quotient types are *not* conservative over pure ITT?
3. What bookkeeping problem does the "deliverables" style solve compared with freely mixing specs and code inside Σ-types?

---

## 9. Bidirectional and Tridirectional Type Checking (Core Topic)

#### Pre-requisites
[[#3. Subtyping, Polymorphism, and System F (Core Topic)|Topic 3]], [[#4. Dependent Types: Π-Types, Σ-Types, and Type Families (Core Topic)|Topic 4]].

#### Why this topic is important
This is the algorithmic shape the elaborator's type checker will take —
check vs. synthesize as the two modes, with an application judgment
handling higher-rank polymorphism. The "context extension" metatheoretic
device (rigid vs. flexible information increase) is the direct model for
how the elaborator's metavariable context evolves during unification
(Topic 11).

#### Sources to Study
1. [[31_Bidirectional_Type_Checking_for_High_Rang_Polymorphism_Dunfield_Krishnaswami/book-guidelines|Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism (Dunfield & Krishnaswami)]]
   - [[Bidirectional-Typechecking-Foundations]]
   - [[Algorithmic-Contexts]]
   - [[Algorithmic-Subtyping-and-Instantiation]]
   - [[Metatheory-of-the-Algorithm]]
2. [[32_Tridirectional_Typechecking_Dunfield_Pfenning/book-guidelines|Tridirectional Typechecking (Dunfield & Pfenning)]]
   - [[Bidirectional-Typechecking-Design-Principles]]
   - [[Indefinite-Property-Types-and-the-Third-Direction]]

#### Key Concepts and Definitions
1. Checking judgment $\Psi \vdash e \Leftarrow A$ vs. synthesis $\Psi \vdash e \Rightarrow A$.
2. Application judgment $\Psi \vdash A \bullet e \Rightarrow\!\Rightarrow C$ for polymorphism.
3. Ordered algorithmic contexts with existential variables $\hat\alpha$ (unsolved/solved), and "articulation" instantiation.
4. Context extension $\Gamma \longrightarrow \Delta$ as the central metatheoretic device (rigid vs. flexible information increase).
5. Soundness/completeness/decidability via a lexicographic termination measure.
6. The tridirectional extension: a third "indefinite property" direction beyond check/synthesize.

#### Relevant Questions
1. Why does the standard two-judgment formulation break under higher-rank polymorphism, motivating the application judgment?
2. What problem does "articulation" solve, and why must new existentials be inserted immediately left of the solved one?
3. Why is $\hat\alpha\mathrm{App}$ the only algorithmic rule without a declarative analogue?

---

## 10. Metavariables, Elaboration, and Implicit Argument Resolution (Core Topic)

#### Pre-requisites
[[#9. Bidirectional and Tridirectional Type Checking (Core Topic)|Topic 9]].

#### Why this topic is important
This is the elaborator itself — the component the compiler's whole
meta-programming layer is built around. De Moura's constraint categories
(pattern, quasi-pattern, flex-rigid, flex-flex) and guarded constants are
close to a direct blueprint for the metavariable-unification engine the
project needs, and Norell's thesis is the concrete "how do you actually
implement this for a dependently typed language" companion.

#### Sources to Study
1. [[29_Elaboration_in_Dependent_Type_Theory_De_Moura_2015/book-guidelines|Elaboration in Dependent Type Theory (de Moura et al.)]]
   - [[The-Elaboration-Task]]
   - [[Higher-Order-Unification]]
   - [[Type-Classes-and-Class-Inference]]
   - [[Overloading-and-Coercions]]
2. [[11_ulf_norell_thesis_2007/book-guidelines|Towards a Practical Programming Language Based on Dependent Type Theory (Norell)]]
   - [[Metavariables-and-Implicit-Arguments]]
   - [[Pattern-Matching-over-Inductive-Families]]

#### Additional external sources
- de Moura, Kong, Avigad, van Doorn, von Raumer, *"The Lean 4 Theorem Prover and Programming Language"* (CADE 2021) — the elaborator/kernel architecture this roadmap's design language ("elaborator resolving implicit arguments via metavariable unification") is directly modeled on; not covered in `vaults/` since it postdates the 2015 elaboration paper above.

#### Key Concepts and Definitions
1. Elaboration as passing from quasi-formal to fully precise terms.
2. Higher-order unification and Miller patterns as the tractable fragment.
3. Six unification-constraint categories: delta, pattern, quasi-pattern, flex-rigid, flex-flex, recursor.
4. Priority-queue constraint solving with nonchronological backtracking; Huet-style imitation/projection for flex-rigid.
5. Guarded constants (Norell) — the mechanism preventing ill-typed intermediate terms during dependent elaboration.
6. Type class inference as backward-chaining, Prolog-like search.

#### Relevant Questions
1. Why is inferring the motive in `subst e H` genuinely higher-order (and inherently ambiguous)?
2. How does nonchronological backtracking avoid re-exploring the search space after failure?
3. Why is it unsafe in dependent types to allow ill-typed intermediate terms, and how does the `coerce`/Ω example show the danger concretely?

---

## 11. Unification: First-Order to Higher-Order and Miller Patterns (Core Topic)

#### Pre-requisites
[[#10. Metavariables, Elaboration, and Implicit Argument Resolution (Core Topic)|Topic 10]]. Intersects with `automated-reasoning`'s unification-algorithm topics — see [[learning-roadmap-automated-reasoning|↪ focused roadmap]] if generated.

#### Why this topic is important
This is the metavariable unifier by name — the exact algorithm the
project's elaborator needs, "in the spirit of Miller's pattern
unification." The pattern condition's uniqueness-of-mgu guarantee is
what makes the whole approach tractable instead of full (undecidable)
higher-order unification.

#### Sources to Study
1. [[83_Type_Inference_Haskell_Dependent_Types_Gundry_2013/book-guidelines|Type Inference in Context (Gundry)]]
   - [[Miller-Pattern-Unification]]
   - [[Contextual-Problem-Solving]]
2. [[85_Dependently_Typed_Functional_Programs_and_their_Proofs_McBride_2000/book-guidelines|Dependently Typed Functional Programs and their Proofs (McBride)]]
   - [[A-Structurally-Recursive-Unification-Algorithm]]
   - [[Equality-and-Object-Level-Unification]]
3. [[70_Extensions_to_Miller_Pattern_Unification_For_Dependent_Types/book-guidelines|Extensions to Miller's Pattern Unification for Dependent Types (Abel & Pientka)]] — no generated article yet
   - λΠΣ-calculus with meta-variables; type isomorphisms for dependent records

#### Additional external sources
- D. Miller, *"A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification"* (JLC 1991) — the original pattern-unification paper the whole thread is named after; worth reading directly rather than only through the two dependent-type-specific extensions above.

#### Key Concepts and Definitions
1. Constructor-form first-order unification transition rules (identity, coalescence, substitution, conflict, injectivity, cycle) with a lexicographic termination measure.
2. Auto-derived "no confusion"/"no cycle" theorems per datatype.
3. John Major equality $\simeq$ for telescopic equations.
4. Miller's pattern condition (a metavariable applied only to distinct bound variables) guaranteeing a unique most general unifier.
5. Twin variables $\hat x : S \ddagger T$ for provably-but-not-definitionally-equal types; pruning and metavariable simplification.
6. Open termination question for full-spectrum pattern unification.

#### Relevant Questions
1. Why does Miller's pattern condition guarantee a *unique* most general unifier?
2. What problem do twin variables solve that ordinary binding cannot?
3. Why does a naïve inductive "no-cycle" proof fail for asymmetric cycles, and what strengthening repairs it?

---

## 12. Equational Theories, Rewriting, and Compiler/Equality-Saturation Correctness (Core Topic)

#### Pre-requisites
[[#5. Definitional Equality, Reduction, and Normalization (Core Topic)|Topic 5]].

#### Why this topic is important
This is where "definitional equality" becomes an engineering problem:
how do you decide term equivalence efficiently and prove a compilation
pass preserves meaning? Pyrosome's `Preserving` predicate is a direct
template for structuring correctness proofs of the compiler's own
lowering passes, and egglog's unification of Datalog-style lattice
reasoning with e-graph congruence closure is relevant to how the kernel
might implement rewrite-rule-driven definitional equality (Topic 13).

#### Sources to Study
1. [[39_Equality-Saturation-RossThesis2012/book-guidelines|Equality Saturation (Ross Tate's thesis lineage)]]
   - [[Converting-Between-Imperative-Code-and-PEGs]]
   - [[Domain-Independent-Applications-of-Generalization]]
2. [[40_A_Framework_for_Modular_Extensible_Equivalence-Preserving_Compilation_Dustin_Jammer_2020/book-guidelines|A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Pyrosome)]] — no generated article yet
   - `Preserving` predicate; language specs as equational theories; compilers as finite maps; STLC→CPS→closures case study
3. [[71_Unifying_Datalog_and_Equality_Saturation/book-guidelines|Unifying Datalog and Equality Saturation (egglog)]] — no generated article yet
   - Fixpoint reasoning frameworks; the egglog language model; formal semantics

#### Key Concepts and Definitions
1. `Preserving(L_t, cmp, L_s)` reducing compiler verification to one obligation per syntactic form/equation.
2. Language specifications as generalized algebraic theories; equivalence preservation vs. contextual equivalence (and where the former's blind spots are).
3. Compiler-extension/codomain-embedding modularity theorems.
4. E-graphs/e-classes and congruence closure.
5. egglog: unifying Datalog's `:merge`-based lattice reasoning with equality saturation's `union`/congruence via one functional-database mechanism.
6. The rebuilding operator restoring functional-dependency validity after non-monotone union steps.

#### Relevant Questions
1. Why can `Preserving` obligations for disjoint language extensions be proved independently?
2. Why does equivalence preservation deliberately not imply contextual-equivalence preservation, and why is that a feature rather than a gap?
3. How does replacing "relation as set" with "function as map with `:merge`" let egglog subsume both Datalog and equality saturation with one mechanism?

---

## 13. The λΠ-Calculus Modulo Theory and Rewriting-Based Kernels (Core Topic)

#### Pre-requisites
[[#8. Intensional vs. Extensional Type Theory (Core Topic)|Topic 8]], [[#12. Equational Theories, Rewriting, and Compiler/Equality-Saturation Correctness (Core Topic)|Topic 12]].

#### Why this topic is important
This is the single closest match in the whole vault to a "trusted
kernel with a custom theorem prover" — Dedukti's λΠ-calculus modulo
theory is exactly a minimal dependent type checker whose definitional
equality is extended by user-supplied rewrite rules, with confluence and
subject reduction established as the soundness conditions. This is the
strongest candidate architecture for the project's own kernel.

#### Sources to Study
1. [[87_Typechecking_in_the_lambda-Pi-Calculus_Modulo_Theory_Saillard_2015/book-guidelines|Typechecking in the λΠ-Calculus Modulo Theory (Saillard)]]
   - [[Abstract-Rewriting-and-Confluence-Theory]]
   - [[The-lambda-Pi-Calculus-Modulo]]
   - [[Subject-Reduction-Product-Compatibility-and-Uniqueness-of-Types]]
   - [[Well-Typedness-of-Rewrite-Rules]]
   - [[Type-Inference-and-Type-Checking-Algorithms]]
2. [[89_Dedukti_Logical_Framework_based_LambdaPI_Calculus_Modulo_Theory_2024/book-guidelines|Dedukti: A Logical Framework based on the λΠ-Calculus Modulo Theory]]
   - [[Lambda-Pi-Calculus-and-Its-Typing-Judgments]]
   - [[The-Lambda-Pi-Calculus-Modulo-Theory]]
   - [[Decidability-via-Effective-Subsystems]]
   - [[The-Dedukti-System-and-Concrete-Syntax]]
3. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/book-guidelines|Interoperability of Proof Systems (Thiré)]]
   - [[The-λΠ-Calculus-Modulo-Theory]]
   - [[Dedukti-An-Implementation-of-Lambda-Pi-calculus-Modulo-Theory]]

#### Key Concepts and Definitions
1. Eight typing rules of plain λΠ-calculus ($Type$/$Kind$, dependent product).
2. Global rewrite rules $l \longrightarrow_\Delta r$ changing definitional equality; subject reduction from well-typed rewrite rules + product compatibility.
3. Confluence proved independent of (and before) termination — reversed from the usual textbook order.
4. Miller's pattern fragment used again here, for decidable higher-order rewriting/matching.
5. Static vs. definable symbols; guards for well-typedness Dedukti can't verify statically.
6. The "most general typing substitution" $\tau$ fixing naive-rule rejection problems.
7. Effectiveness Theorem: confluent + terminating ⇒ decidable typing.

#### Relevant Questions
1. Why must confluence be established before termination/well-typedness assumptions here, against the usual order?
2. Walk through the `Tail` example — why does the naive rule reject it, and what does $\tau$ buy?
3. Why does λ-abstraction in a rewrite LHS break ordinary first-order confluence, and how does Miller's pattern fragment restore decidability?

---

## 14. Pure Type Systems and Generalized Type-Theoretic Frameworks (Core Topic)

#### Pre-requisites
[[#13. The λΠ-Calculus Modulo Theory and Rewriting-Based Kernels (Core Topic)|Topic 13]].

#### Why this topic is important
This is the abstraction layer above a single fixed calculus — useful if
the compiler's type theory needs to be parameterized (e.g. different
universe/sort structures for different subsystems) rather than hardcoded.
The ecumenical-systems idea (mixing constructive/classical connectives at
the connective level) is also directly relevant to a theorem prover that
needs both a constructive core and classical reasoning for some
verification-condition discharge.

#### Sources to Study
1. [[88_LAMBDA_PI_GRIENENBERGER_2025/book-guidelines|Combining Computational Theories (Grienenberger)]]
   - [[Pure-Type-Systems]]
   - [[Theory-U-and-Ecumenical-Fragments]]
   - [[Modularity-of-Type-Theories]]
2. [[86_Interoperability_proof_systems_LambdaPI_calculus_modulo_theory_Thire_2021/book-guidelines|Interoperability of Proof Systems (Thiré)]]
   - [[Cumulative-Type-Systems-(CTS)]]
   - [[Interoperability-Between-Type-Systems]]
   - [[Well-Structured-Derivation-Trees]]

#### Key Concepts and Definitions
1. PTS specification $(S, A, R)$ embedded via per-sort universes $U_s/e_s$ and per-rule product formers $\pi_{s_1 s_2}$.
2. Cumulative Type Systems (CTS) generalizing PTS with subtyping; well-structured derivation trees; bi-directional CTS presentations.
3. Ecumenical systems mixing constructive/classical connectives at the connective (not proof) level.
4. Modularity of type theories via theory fragmentation.
5. Embedding theorems: preservation of computation/typing, conservativity/adequacy, equivalence of provability.

#### Relevant Questions
1. Why is a separate $U_s$/$e_s$ pair needed per sort in the PTS embedding?
2. Why does attaching classicality to connectives (not proofs) let constructive/classical reasoning coexist safely?
3. What does "modularity of type theories" via fragmentation buy over one monolithic specification?

---

## 15. Categorical and Denotational Semantics of Type Theory (Core Topic)

#### Pre-requisites
[[#4. Dependent Types: Π-Types, Σ-Types, and Type Families (Core Topic)|Topic 4]], [[#8. Intensional vs. Extensional Type Theory (Core Topic)|Topic 8]].

#### Why this topic is important
This is the soundness argument underneath everything else: exhibiting a
model is what justifies trusting the kernel's rules are consistent.
The fibred treatment of equality/quantifiers as adjoints is also the
cleanest way to see why Topic 17's refinement/subset types and Topic 4's
Σ-types are secretly the same construction wearing different logical
clothes.

#### Sources to Study
1. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/book-guidelines|Categorical Logic and Type Theory (Jacobs)]]
   - Fibred category theory, indexed categories, functorial (Lawvere) semantics articles
2. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory (Angiuli & Gratzer)]]
   - [[Categorical-Semantics-of-Type-Theory]]
3. [[48_From_Categories_Homotopy_Theory_Cambridge_Birgit_Richter_2020/book-guidelines|From Categories to Homotopy Theory (Richter)]] — general category-theory background (limits/colimits, Yoneda, adjunctions), cited here for prerequisite machinery rather than type-theoretic content directly.

#### Key Concepts and Definitions
1. Classifying category $\mathfrak C(\Sigma)$ (contexts as objects, term-tuples as morphisms) with finite products.
2. Lawvere functorial semantics: models as product-preserving functors; the generic model as the identity functor.
3. The fibred account of exponents as simple products in a simple fibration.
4. Equality as a left adjoint to a contraction functor, unifying reflexivity/symmetry/transitivity/replacement into one rule.
5. Regular/coherent/first-order fibrations classifying increasingly rich predicate logics.
6. Categories with families as the semantic backbone of the explicit substitution calculus (cross-reference Topic 4).
7. Grothendieck-universe set models establishing ETT's consistency.

#### Relevant Questions
1. Why is presenting exponents as *simple products in a fibration* categorically preferable to assuming product types outright?
2. Why does presenting equality as a left adjoint unify the four equality rules into one, and what role does Beck–Chevalley play?
3. Why does exhibiting any nontrivial model suffice for consistency, while canonicity needs a special gluing model?

---

## 16. Homotopy Type Theory and Univalent Foundations (Core Topic)

#### Pre-requisites
[[#8. Intensional vs. Extensional Type Theory (Core Topic)|Topic 8]], [[#15. Categorical and Denotational Semantics of Type Theory (Core Topic)|Topic 15]].

#### Why this topic is important
Lower priority for the compiler's near-term goals than Topics 9–13, but
directly relevant to how far the identity-type story from Topic 5 can be
pushed, and to understanding cubical type theory as the modern answer to
the canonicity/univalence tension that a Rust kernel implementation
would eventually have to make a design decision about if equality types
grow richer than plain intensional Id.

#### Sources to Study
1. [[14_homotopy_type_theory/book-guidelines|Homotopy Type Theory: Univalent Foundations of Mathematics]]
   - Type formers, identity types, univalence axiom, higher inductive types articles
2. [[84_type-theory-book_Daniel_Gratzer_2026/book-guidelines|Principles of Dependent Type Theory (Angiuli & Gratzer)]]
   - [[Cubical-Type-Theory]]
   - [[Univalent-Foundations-and-Homotopy-Type-Theory]]

#### Key Concepts and Definitions
1. Univalence axiom: `idtoequiv` is an equivalence.
2. Homotopy levels ($\mathrm{IsOfHLevel}$, n-types, h-sets).
3. Higher inductive types (circle $S^1$, suspensions, set truncation); propositional truncation recovering ∃/∨.
4. Tension between axiomatic univalence and canonicity, resolved by cubical type theory's Path type over a judgmental interval structure.
5. Homogeneous composition (`hcomp`) and the Glue/V-type mechanism computing univalence.

#### Relevant Questions
1. Why does univalence specifically require `idtoequiv` to be an *equivalence* rather than merely admitting an inverse map?
2. In what precise sense does cubical type theory's Path type resolve the canonicity/univalence tension that axiomatic HoTT cannot?
3. Why must higher inductive types like the circle exist to reach types of no finite homotopy level?

---

## 17. Refinement Types and Dependent Predicate Logic for Program Correctness (Core Topic)

#### Pre-requisites
[[#4. Dependent Types: Π-Types, Σ-Types, and Type Families (Core Topic)|Topic 4]], [[#15. Categorical and Denotational Semantics of Type Theory (Core Topic)|Topic 15]]. Intersects heavily with `automated-reasoning` (Hoare logic, weakest preconditions) — see [[learning-roadmap-automated-reasoning|↪ focused roadmap]] if generated.

#### Why this topic is important
This is the refinement-type surface language itself — the project's
stated goal is constraint-based inference for exactly this kind of type.
The subset/quotient-type duality (both adjoints to the same functor
`Eq`) gives a principled way to think about what a refinement predicate
"means" formally, rather than treating it as an informal annotation
bolted onto the type system.

#### Sources to Study
1. [[57_Categorical_Logic_Type_Theory_BART_JACOBS/book-guidelines|Categorical Logic and Type Theory (Jacobs)]]
   - Subset/quotient types, dependent predicate logic articles
2. [[37_Certified_Programming_with_Dependent_Types_Adam_Chlipala_2019/book-guidelines|Certified Programming with Dependent Types (Chlipala)]]
   - [[Dependent-Types-for-Program-Correctness]]

#### Additional external sources
- P. Rondon, M. Kawaguchi, R. Jhala, *"Liquid Types"* (PLDI 2008), and the LiquidHaskell line of work — the closest concrete precedent for "constraint-based inference for refinement types" as stated in the project goals; nothing in `vaults/` currently covers refinement-type *inference* specifically (as opposed to refinement-type *checking*), so this is a genuine gap worth adding to `sources/`.

#### Key Concepts and Definitions
1. Subset types $\{x{:}\sigma \mid \varphi\}$ as a right adjoint to the terminal-object functor ("has subsets").
2. Quotient types $\sigma/R$ as a left adjoint to equality ("has quotients") — the categorical duality with subset types.
3. ∃/∀ as left/right adjoints to weakening, requiring Beck–Chevalley for arbitrary reindexing.
4. Regular/coherent/first-order fibrations and logoses; unique choice and "very strong equality."
5. Coq's `sig`/`sumbool`/`sumor` families and proof erasure during extraction; the `hasType` determinism lemma feeding certified type-checkers.

#### Relevant Questions
1. Why must ∃/∀ be adjoints to *weakening* specifically, and what extra hypothesis extends this to arbitrary reindexing?
2. Why are subset types and quotient types "secretly dual" constructions on the same functor `Eq`?
3. Why does the same predecessor function extract to identical OCaml code across increasingly precise Coq types?

---

## 18. Tree and Symbolic Automata as Structural Foundations for Typed Data (Core Topic)

#### Pre-requisites
[[#6. Inductive Types, Pattern Matching, and Elimination Principles (Core Topic)|Topic 6]].

#### Why this topic is important
Lower priority, included because the project's CSP kernel is explicitly
meant to represent abstract data structures as automata/DFA-based
domains — this topic is where the type-theoretic side of that idea
(recognizable tree languages as a semantics for inductively defined
term structures) meets its `sat-smt-csp` payoff. See the
`sat-smt-csp` focused roadmap for the CSP-domain-propagation side of
this same material.

#### Sources to Study
1. [[33_TATA_Tree_Automata_TechniquesApplications_Comon_Dauchet_2008/book-guidelines|Tree Automata Techniques and Applications (Comon et al.)]]
   - [[Terms-Trees-and-Contexts]]
   - [[Recognizable-Tree-Languages-and-Finite-Tree-Automata]]
   - [[Regular-Tree-Grammars-and-Expressions]]
2. [[75_The_power_of_symbolic_automata_Transducers_LorisDAntoni_MSResearch/book-guidelines|The Power of Symbolic Automata and Transducers (D'Antoni)]] — no generated article yet
   - Symbolic finite automata (s-FA) and their variants; effective Boolean algebras

#### Key Concepts and Definitions
1. NFTA/DFTA over ranked alphabets; determinization via subset construction (bottom-up cost-free, top-down strictly weaker).
2. Myhill–Nerode theorem for trees (finite-index congruence ⟺ recognizable); pumping lemma for non-recognizability proofs.
3. Regular tree grammars ⟺ recognizability (Kleene's theorem for trees).
4. IO vs. OI derivation strategies for context-free tree languages.
5. Effective Boolean algebras and symbolic finite automata (s-FA) generalizing classic automata to infinite/structured alphabets.
6. Minterm-based reduction and the "predicate space explosion" as a second complexity axis beyond state-space blowup.

#### Relevant Questions
1. Why does nondeterminism cost nothing for bottom-up tree automata but strictly reduce top-down expressive power?
2. Why does determinizing a symbolic finite automaton introduce a predicate-space explosion beyond the classic state-space one?
3. Why does the IO/OI distinction vanish exactly when a grammar is linear?

---

## 19. Propositions-as-Types Beyond Sequential Programs: Session Types (Core Topic)

#### Pre-requisites
[[#1. Judgments, Contexts, and the Curry–Howard Correspondence (Core Topic)|Topic 1]].

#### Why this topic is important
Lowest priority in this Focus Area — the project's goals don't currently
call for a concurrency/session-typed component. Kept in the roadmap
because it's the most rigorous extension of Curry–Howard on hand (linear
logic ⟷ session fidelity) and worth knowing about if the compiler's
verification-condition language ever needs to reason about concurrent or
resource-sensitive protocols.

#### Sources to Study
1. [[22_wadler_2012_propositions_as_sessions/book-guidelines|Propositions as Sessions (Wadler)]]
   - [[The-Curry-Howard-Correspondence-for-Concurrency]]
   - [[GV-a-Session-Typed-Functional-Language]]
2. [[72_Domain-Aware_Session_Types_Caires_Perez_Pfenning_Toninho_2019/book-guidelines|Domain-Aware Session Types (Caires, Pérez, Pfenning, Toninho)]]
   - [[Session-Types-via-the-Curry-Howard-Correspondence]]
   - [[Hybrid-Linear-Logic-and-Domain-Aware-Types]]

#### Key Concepts and Definitions
1. πDILL (dual intuitionistic linear logic) and CP (classical linear-logic process calculus, one-sided sequents).
2. The session-typed "twist": reusing the same channel name across hypothesis/conclusion, vs. the pairing interpretation's fresh names.
3. Cut elimination as communication; commuting conversions as the aspect prior translations missed.
4. Deadlock freedom as the concurrent analogue of termination.
5. GV as a race/deadlock-free linear functional language with session types.
6. Domain-aware extension: hybrid linear logic, modal worlds as domains, adding session fidelity plus global progress under domain migration.

#### Relevant Questions
1. In what sense do prior process-calculus translations from linear logic fall short of full Curry–Howard, and what does Caires–Pfenning's twist fix?
2. Why does letting cut elimination directly specify CP's reduction rules matter?
3. Why is domain information (e.g. "resides in domain AmazonUS") inexpressible in prior session-type frameworks?
