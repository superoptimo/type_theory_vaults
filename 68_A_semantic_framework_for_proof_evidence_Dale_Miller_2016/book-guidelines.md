# A Semantic Framework for Proof Evidence — Guidelines

## Header

**Title:** A Semantic Framework for Proof Evidence
**Author(s):** Zakaria Chihani, Dale Miller, Fabien Renaud
**Publication:** Journal of Automated Reasoning (manuscript / draft, July 2, 2016) — extension of the CADE 2013 conference paper "Foundational Proof Certificates in First-Order Logic"

**Brief Summary:**
This paper proposes the Foundational Proof Certificates (FPC) framework: a proof-theoretic, technology-independent way of giving formal semantics to the many different formats in which theorem provers export "proof evidence" (resolution refutations, natural deductions, Frege proofs, equational rewritings, typed $\lambda$-terms, and more). The framework's foundation is the augmented focused sequent calculus — specifically the LKF (classical) and LJF (intuitionistic) systems of Liang and Miller — decorated with certificate terms and two families of predicates, clerks and experts, that mediate what a proof checker may deterministically compute versus what it must non-deterministically (or interactively) decide. A single small trusted kernel, implementing only the atoms of inference and the "chemistry" that assembles them into phases, can then check a very wide range of proof styles simply by being paired with a different FPC specification, in the same way one parser-generator can be retargeted by changing a grammar.

**Intent of the Author:**
The authors want to give computational logic systems (theorem provers, model checkers, type checkers, static analyzers) a common, formally defined "assembly language" for proofs — analogous to how grammars standardized programming-language syntax and denotational/operational semantics standardized programming-language meaning — so that proof evidence can be separated from its provenance, shared across systems, and checked by small, independently trustable checkers rather than by trusting the full complexity of whichever prover produced it.

---

## Topic List

1. **Foundational Proof Certificates (FPC) Framework** : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - Proof certificates as exported documents of proof evidence : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - The four desiderata for a general notion of proof certificate : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - The five FPC parameters: polarization, certificate terms, indexes, clerks, experts
   - Kernels as trusted implementations of an augmented focused proof system : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - Proof checking as computation and interaction : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
   - Proof reconstruction versus mere provability checking : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]

2. **Focused Sequent Calculus** : [[Focused-Sequent-Calculus|Link]]
   - Atoms of inference versus molecules (synthetic inference rules) : [[Focused-Sequent-Calculus|Link]]
   - Asynchronous and synchronous phases
   - Polarized formulas and connective polarity
   - The LKF focused proof system for first-order classical logic
   - The LJF focused proof system for first-order intuitionistic logic
   - Structural rules: store, release, decide, cut
   - Completeness and cut-elimination for focused systems : [[Focused-Sequent-Calculus|Link]]
   - LKneg and LKpos as invertible and non-invertible restrictions of LKF

3. **Clerks and Experts as an Augmented Kernel** : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]
   - Augmenting LKF and LJF into LKFa and LJFa
   - Clerk predicates governing the asynchronous phase
   - Expert predicates governing the synchronous phase
   - The tax-office clerks-and-experts analogy : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]
   - Deterministic versus non-deterministic certificate behavior : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]
   - Indexes as the addressing mechanism for stored formulas : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]

4. **Case Studies in Proof Certificate Design** : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - A CNF decision procedure as an FPC : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Oracle strings for LKpos proofs : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Binary resolution refutations as an FPC : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Simply typed $\lambda$-terms in $\eta$-long $\beta$-normal form as certificates : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Justified Horn clause proofs : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Frege proofs encoded via Horn clause entailment : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - The mimic FPC and completeness of atomic initial rules : [[Case-Studies-in-Proof-Certificate-Design|Link]]

5. **Relating Classical and Intuitionistic Proof Checking** : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]
   - Hosting an LKFa kernel on an LJFa kernel
   - Chaudhuri's translation between LKF and LJF formulas : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]
   - Phase correspondence between classical and intuitionistic focusing : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]
   - Double-negation translations of classical into intuitionistic logic : [[Relating-Classical-and-Intuitionistic-Proof-Checking|Link]]

6. **Logic Programming as an Implementation Substrate** : [[Logic-Programming-as-an-Implementation-Substrate|Link]]
   - $\lambda$Prolog as the specification language for FPCs
   - $\lambda$-tree syntax and higher-order abstract syntax for bindings
   - Hypothetical reasoning for managing storage contexts
   - Unification and backtracking search in proof reconstruction : [[Logic-Programming-as-an-Implementation-Substrate|Link]]
   - Teyjus and other $\lambda$Prolog implementations : [[Logic-Programming-as-an-Implementation-Substrate|Link]]

7. **Trusted Kernels and Proof Sharing** : [[Trusted-Kernels-and-Proof-Sharing|Link]]
   - LCF-style provers and the abstract datatype of theorems
   - The de Bruijn criterion for trustworthy theorem provers : [[Trusted-Kernels-and-Proof-Sharing|Link]]
   - Grammars as an analogy for standardizing proof structure
   - Existing proof-sharing standards: OpenTheory, LFSC, MMT, Dedukti : [[Trusted-Kernels-and-Proof-Sharing|Link]]

8. **Extensions and Open Problems** : [[Extensions-and-Open-Problems|Link]]
   - Equational rewriting and paramodulation certificates : [[Case-Studies-in-Proof-Certificate-Design|Link]]
   - Linear logic, the LKU system, and unifying multiple logics
   - Multifocusing, expansion trees, and proof nets
   - The multicut rule and independent lemma reuse
   - FPCs for modal logics and dependently typed calculi
   - Certificates for model checking and inductive theorem proving

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 2–6)

**Summary:** Motivates the need for a shared, formal semantics of proof evidence by analogy with how grammars standardized programming-language syntax and denotational/operational/natural semantics standardized meaning; surveys prior notions of proof (Frege-Hilbert, LCF, natural deduction, sequent calculus, focused proof systems) and introduces the "atoms, molecules, and chemistry" metaphor together with the four desiderata a proof certificate framework should satisfy. : [[Case-Studies-in-Proof-Certificate-Design|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Dealing with many proof languages** — proof certificate (an exported document containing discovered proof evidence), the grammar/parser analogy for standardizing proof structure.
- **1.2 What can be learned about proof structure from proof theory** — Frege-Hilbert proofs, LCF approach (theorems as an abstract datatype), natural deduction proofs, uniform proofs and logic programming as goal-directed search, focused proof system (Andreoli).
- **1.3 The atoms, molecules, and chemistry of inference** — atoms of inference (introduction, structural, identity rules), molecules of inference / synthetic rules (whole focusing phases), the four desiderata D1–D4 (simple checkability, broad proof-system coverage, denoting a structural-proof-theory proof, allowing proof reconstruction from partial detail). : [[Focused-Sequent-Calculus|Link1]], [[Foundational-Proof-Certificates-(FPC)-Framework|Link2]]
- **1.4 Machine-machine transmission and checking of formal proofs** — the paper's scope: formal, machine-checkable proofs rather than human-readable ones.

**Key Questions:**
1. Why is a "chemistry of inference" (molecules built from atoms) a better unit for defining proof semantics than individual sequent-calculus inference rules?
2. How do desiderata D1–D4 jointly rule out both "a checker that trusts everything" and "a checker that must fully reconstruct every proof step from nothing"?

---

### Chapter 2: Proof checking as computation and interaction (pp. 6–7)

**Summary:** Frames proof checking as an interactive process between a checker and a certificate, using Poincaré's Principle (proofs need not encode routine computation) and a robot-navigating-a-maze analogy to distinguish deterministic "corridor" computation from non-deterministic, communication-requiring "maze" search. : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Navigating a robot through corridors and mazes** — deterministic corridor traversal versus non-deterministic maze search as an analogy for asynchronous versus synchronous proof phases.
- **2.2 Sorting out this analogy** — asynchronous phase (determinate, no communication) mapped to corridors; synchronous phase (choice-laden, communication-heavy) mapped to mazes. : [[Clerks-and-Experts-as-an-Augmented-Kernel|Link]]

**Key Questions:**
1. In what sense does non-determinism in a proof checker's computation reduce certificate size rather than merely add complexity?
2. How does the corridor/maze analogy anticipate the later formal split between asynchronous (clerk-governed) and synchronous (expert-governed) phases?

---

### Chapter 3: Two proof systems for propositional classical logic (pp. 7–9)

**Summary:** Introduces LKneg and LKpos, two simple one-sided sequent calculi for propositional classical logic that isolate, respectively, fully invertible and fully non-invertible treatment of disjunction, to illustrate how a proof system can itself define an interactive checking protocol and how certificate size trades off against checking time.

**Key Definitions & Concepts by Section:**
- **3.1 LKneg and the invertible inference rules** — a decision procedure using only invertible rules; exponential-time, information-free checking (essentially CNF conversion). : [[Focused-Sequent-Calculus|Link]]
- **3.2 LKpos and non-invertible rules** — the restart rule and unbounded search; oracle trees and oracle strings as explicit certificates recording left/right disjunction choices.
- **3.3 A proof system can yield a protocol** — contrast between LKneg's silent, exponential-time checking and LKpos's certificate-guided, near-linear checking on the same formula.

**Key Questions:**
1. Why does LKneg's determinism (except at `init`) let it check proofs with zero external information but at exponential cost?
2. How does the oracle-string certificate for LKpos let checking time drop even though the underlying proof search space is non-deterministic?

---

### Chapter 4: LKF as a framework for classical focused proofs (pp. 9–12)

**Summary:** Presents LKF, the focused proof system for first-order classical logic (Liang and Miller) that generalizes and hybridizes LKneg and LKpos, introducing polarized formulas, up-arrow/down-arrow sequents, and the asynchronous/synchronous phase structure that underlies the entire FPC framework.

**Key Definitions & Concepts by Section:**
- Polarized formula (occurrences of connectives/constants marked $+$ or $-$); positive and negative formulas; de Morgan duals of polarized connectives.
- Up-arrow sequents $\vdash \Gamma \Uparrow \Theta$ and down-arrow sequents $\vdash \Gamma \Downarrow B$; storage zone.
- Asynchronous introduction rules (invertible) versus synchronous introduction rules (choice-laden).
- Structural rules: store, release, decide; identity rules: init, cut.
- Theorem 1 (soundness/completeness of LKF, and cut-elimination) [60].
- Synthetic inference rule (Example 1): a decide application unfolds into a whole derivation fragment.

**Key Questions:**
1. What makes a connective occurrence a candidate for positive versus negative polarization, and how does that choice determine whether it is treated invertibly?
2. Why must the `decide` rule be the sole locus of contraction in LKF, and what does that imply about which formulas must be positively polarized?
3. How does Example 1's synthetic inference rule illustrate the gap between "individually checkable inference rules" and "efficiently checkable synthetic/macro rules" (Cook's polynomial-checkability sense)?

---

### Chapter 5: Augmented LKF and checking certificates (pp. 12–13)

**Summary:** Introduces $LKF^a$, the augmentation of LKF with certificate terms $\Xi$, indexed storage, and an extra clerk/expert premise on every inference rule, and motivates the design with the accounting-office analogy: clerks handle asynchronous "bookkeeping," experts handle synchronous "investigative" decisions.

**Key Definitions & Concepts by Section:**
- $LKF^a$: three augmentations of LKF — a certificate-term decoration $\Xi$ on every sequent, indexed pairs $l:B$ in storage, and clerk/expert premises on every rule.
- Clerk predicate (subscript `c`, governs asynchronous-phase computation) and expert predicate (subscript `e`, governs synchronous-phase decisions).
- Kernel (an implementation of an augmented focused proof system).
- Soundness of $LKF^a$ by erasure back to LKF.

**Key Questions:**
1. Why does soundness of $LKF^a$ follow "for free" from the erasure map back to LKF, and what does that buy the framework in terms of trust?
2. How does the clerks/experts split mirror the asynchronous/synchronous phase split established in Chapter 4?

---

### Chapter 6: Foundational proof certificates (pp. 13–17)

**Summary:** Defines the five parameters that jointly constitute an FPC — polarization, certificate terms, indexes, clerks, experts — and introduces $\lambda$Prolog as the concrete specification language used throughout the paper, explaining kind/type declarations and $\lambda$-binder notation. : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]

**Key Definitions & Concepts by Section:**
- Polarization (choice of how to polarize connectives/atoms; contractibility tied to positive polarity).
- Certificate terms (inhabitants of type `cert`, threaded through $LKF^a$ rules via $\Xi$).
- Indexes (inhabitants of type `index`; label stored formulas; dereferencing may be non-deterministic).
- Experts (extract information / continuation certificates during synchronous rules; may be maximally non-deterministic).
- Clerks (perform deterministic computation during asynchronous rules, e.g. computing indexes).
- $\lambda$Prolog syntax: `kind`/`type` declarations, infix backslash for $\lambda$-abstraction, `sigma`/`pi` for object-level $\exists$/$\forall$.
- FPC (the collective name for the five-parameter specification).

**Key Questions:**
1. Why must polarity choices for atoms and connectives be made "in concert" with the definition of clerks and experts rather than independently?
2. What is gained by using $\lambda$Prolog's $\lambda$-tree syntax specifically for encoding formula-level and proof-level bindings (quantifiers, eigenvariables)?

---

### Chapter 7: Examples of FPCs in classical, first-order logic (pp. 17–24)

**Summary:** Works through concrete FPCs — a CNF decision procedure, an oracle-string encoding of LKpos, and a binary resolution refutation checker — showing the uniform recipe (polarize, declare `cert`/`index` constructors, define clerks/experts) and how certificate design trades explicitness for checking efficiency.

**Key Definitions & Concepts by Section:**
- **7.1 CNF decision procedure** — negative polarization of all connectives; single-constructor `cert`/`index` types; four clerk and three expert predicates recovering the LKneg decision procedure. : [[Case-Studies-in-Proof-Certificate-Design|Link]]
- **7.2 LKpos example** — positive polarization of $\land,\lor$; oracle certificates linking `start`/`restart`/`consume` constructors to LKpos's restart rule.
- **7.3 Resolution refutations** — resolution clause, binary resolution (with factoring); certificate structure encoding a resolvent triple list $\langle i,j,k\rangle$; regions of the certificate (store negated clauses, sequence of cuts, per-step resolution proof); soundness without a converse guarantee (the checker also accepts some non-most-general-unifier "near-resolvents"). : [[Case-Studies-in-Proof-Certificate-Design|Link]]

**Key Questions:**
1. Why does the CNF-decision-procedure FPC need only a single-inhabitant `cert` type, and what does that reveal about the relationship between "how much a certificate says" and "how much work the kernel does"?
2. In the resolution-refutation FPC, why is quantifier instantiation deliberately left out of the certificate, and what property of first-order unification makes that omission safe?
3. What does the "non-most-general-unifier" counterexample near the end of §7.3 show about the difference between soundness and completeness-as-uniqueness for a proof-checking FPC?

---

### Chapter 8: Intuitionistic first-order logic (pp. 22–30)

**Summary:** Develops LJF, the intuitionistic analogue of LKF (two-sided, four-zone sequents), its augmentation $LJF^a$, and a sequence of increasingly rich FPCs for intuitionistic proof evidence: simply typed $\lambda$-terms in $\eta$-long $\beta$-normal form via de Bruijn indexes, an extension covering non-normal terms, and the "mimic" FPC that recovers full (non-atomic) Gentzen-style initial sequents.

**Key Definitions & Concepts by Section:**
- **8.1 The LJF focused proof system** — two-sided four-zone sequents ($\Gamma \Uparrow \Theta \vdash R$ / $\Gamma \Downarrow B \vdash R$); polarity of $\supset$ (always negative) and of intuitionistic negation; single positive disjunction $\lor$ (no $\lor^-$); invariants on formula polarity across a derivation. : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
- **8.2 The $LJF^a$ focused proof system** — augmentation paralleling $LKF^a$; left-only indexing (storeL/storeR asymmetry since only one formula may sit on the right). : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
- **8.3 Simply typed $\lambda$-terms as proof certificates** — Curry-Howard correspondence between $\eta$-long $\beta$-normal simply typed $\lambda$-terms and natural deduction/minimal-logic proofs; de Bruijn index representation; the head-variable-offset encoding $[[\theta\mid t]]_d$; soundness without converse (checker doesn't verify full term structure). : [[Case-Studies-in-Proof-Certificate-Design|Link]]
- **8.4 Variation on certificates based on de Bruijn indexes** — encoding explicit $\lambda$-occurrences via a positive delay operator $\partial(\cdot)$. : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]
- **8.5 The mimic FPC** — completeness of atomic-only initial rules; mirroring the asynchronous phase's introduction steps during the synchronous phase to reconstruct a full (non-atomic) Gentzen-style `init`. : [[Case-Studies-in-Proof-Certificate-Design|Link]]

**Key Questions:**
1. What structural asymmetry between LKF and LJF forces the storeR rule (and not storeL) to be "linear," and how does that connect to intuitionistic logic's single-conclusion restriction?
2. How does the head-variable-offset encoding $[[\theta\mid t]]_d$ let a de Bruijn-indexed $\lambda$-term double as a proof certificate for LJF without explicit $\lambda$-binders?
3. What is the proof-theoretic content of the mimic FPC — i.e., why is proving completeness of atomic initial rules non-trivial in a *focused* system even though it is straightforward in unfocused Gentzen LJ?

---

### Chapter 9: Checking proofs instead of provability (pp. 30–35)

**Summary:** Shows that FPCs can enforce structural constraints stronger than mere theoremhood by developing "justified Horn clause proofs" (each derived atom carries an explicit justification referencing earlier atoms) and using that machinery to check Frege proofs by encoding propositional provability as a Horn clause entailment. : [[Foundational-Proof-Certificates-(FPC)-Framework|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Justified Horn clause proofs** — Horn clause, Horn clause entailment; justified Horn clause proof (sequence of indexed triples: label, atom, justification); `load`, `jlist`, `apply`/`args`/`finish` certificate constructors mediating successive cut rules. : [[Case-Studies-in-Proof-Certificate-Design|Link]]
- **9.2 Frege proofs** — Frege proof (list of formulas each an axiom instance or rule consequence); encoding an object-level provability predicate `pv` and axiom schemas as Horn clauses so that checking a Frege proof reduces to checking a justified Horn clause proof. : [[Case-Studies-in-Proof-Certificate-Design|Link]]

**Key Questions:**
1. Why does checking a justified Horn clause proof require the certificate to name *specific* premise indexes (via `finish`) rather than merely asserting that *some* earlier derivable atoms suffice?
2. How does reducing Frege-proof checking to justified-Horn-clause checking illustrate the FPC framework's claim to be "foundational" rather than proof-format-specific?

---

### Chapter 10: Hosting LKFa on an LJFa kernel (pp. 34–38)

**Summary:** Investigates whether a single trusted kernel (for the more expressive intuitionistic logic) can check both intuitionistic and classical proof evidence, using Chaudhuri's phase-preserving translation of LKF formulas/proofs into LJF to derive $LJF^a$ clerks and experts mechanically from $LKF^a$ ones.

**Key Definitions & Concepts by Section:**
- Double-negation translations (Gödel, Gentzen, Kolmogorov) as classical-into-intuitionistic encodings, contrasted with the additional machinery (modal logic, linear-logic `!`) needed for intuitionistic-into-classical translations.
- The single-conclusion restriction of LJ as a linear-logic-like exponential distinction between left (classical) and right (linear) contexts.
- Chaudhuri's $[\![\cdot]\!]^+$ / $[\![\cdot]\!]^-$ translation mapping LKF formulas to LJF formulas around a fixed negative atom $q$; one-to-one phase correspondence between LKF and translated LJF derivations.
- Mechanical derivation of $LJF^a$ clerk/expert clauses from $LKF^a$ ones (Figure 22); special handling of the cut rule and its polarity-dependent translation.

**Key Questions:**
1. Why does the paper avoid direct double-negation translations and instead adopt Chaudhuri's polarized translation for hosting classical on intuitionistic focusing?
2. What is the significance of proving a *phase-level* (not just theorem-level) correspondence between LKF and translated-LJF derivations for the goal of reusing one kernel for two logics?

---

### Chapter 11: A reference proof certificate checker (pp. 37–41)

**Summary:** Discusses implementing FPCs as logic programs, drawing an analogy between FPC-specification/checker-implementation and CFG-specification/parser-implementation, and details how $LKF^a$ sequents, storage, and inference rules translate directly into $\lambda$Prolog clauses, plus the specific benefits (and optionality) of $\lambda$Prolog's hypothetical reasoning, $\lambda$-tree syntax, and abstract-datatype modularity. : [[Case-Studies-in-Proof-Certificate-Design|Link1]], [[Foundational-Proof-Certificates-(FPC)-Framework|Link2]]

**Key Definitions & Concepts by Section:**
- **11.1 Kernels as logic programs** — encoding LKF's two sequent styles (`unf`, `foc`) and storage via hypothetical reasoning (`storage I C => ...`); the `check` predicate as the executable kernel. : [[Logic-Programming-as-an-Implementation-Substrate|Link]]
- **11.2 Implementations of checkers** — benefits of $\lambda$Prolog (unification/backtracking for reconstruction; $\lambda$-tree syntax avoiding prenex/Skolemization; modular abstract-datatype hiding); which features (typing, modularity, $\lambda$-tree syntax, hypothetical reasoning) are optional versus load-bearing; Teyjus, ELPI, Minlog, Isabelle/Pure as alternative implementations of the underlying logic.

**Key Questions:**
1. Why is unification-and-backtracking search identified as the one $\lambda$Prolog feature "most difficult to eliminate completely" from an FPC-checker implementation, and what would be lost (in certificate size) by removing it?
2. How does the CFG/parser analogy explain why "FPC specification" and "practical, efficient checker implementation" are described as distinct engineering problems?

---

### Chapter 12: Future work (pp. 40–42)

**Summary:** Sketches several directions beyond the paper's first-order classical/intuitionistic scope: more FPC case studies (equational rewriting, modal logics, dependently typed calculi), extending to linear logic and the LKU system, moving past first-order logic to model checking and inductive theorem proving, reasoning with background theories, and richer kernel extensions such as multifocusing, expansion trees, and the multicut rule.

**Key Definitions & Concepts by Section:**
- **12.1 Developing more examples of FPCs** — FPCs for equational rewriting/paramodulation; modal-logic labeled proofs; dependently typed $\lambda$-calculi (e.g. $\lambda\Pi$, LF) via encoding into intuitionistic logic and a "justified hereditary Harrop formula" certificate format.
- **12.2 Moving beyond first-order logic** — fixed-point operators in linear logic (Baelde); certifying model checking (reachability, bisimulation) and inductive theorem proving; open problem of flexible-polarity focusing for higher-order logic.
- **12.3 Theories** — proving theorems relative to a background theory by treating the theory as additional assumptions; open questions about relating conclusions across different theories.
- **12.4 Extensions to the kernel design** — multifocusing (focusing on several positive formulas at once); expansion trees and proof nets as minimal-commitment proof structures; the multicut rule for encoding independently-proved lemmas; extending kernels to relegate trust to external provers (e.g. SMT solvers). : [[Extensions-and-Open-Problems|Link]]

**Key Questions:**
1. Why does encoding a Horn clause justification format for dependently typed calculi require generalizing to "justified hereditary Harrop formulas" rather than reusing the justified Horn clause format of Chapter 9 unchanged?
2. What problem does the multicut rule solve that a sequence of ordinary (binary) cut rules does not, and why does that matter for certificate authors?

---

### Chapter 13: Related work (pp. 42–44)

**Summary:** Situates the FPC framework relative to the broader history of trusted-kernel theorem proving (LCF, Coq, Isabelle, HOL, the de Bruijn criterion) and existing proof-sharing efforts (OpenTheory, LFSC, MMT, Dedukti), arguing that most prior approaches remain technology-specific or ad hoc compared to FPC's proof-theoretic foundation.

**Key Definitions & Concepts by Section:**
- De Bruijn criterion (a prover with a small trusted checking subsystem for alleged proofs).
- OpenTheory (shared standard theory library across HOL provers).
- LFSC ("Logical Framework with Side Conditions", extension of LF, used to check SMT proof evidence).
- MMT (logic-independent framework for defining/analyzing/checking proof systems).
- Dedukti ($\lambda\Pi$-modulo based checker incorporating constructive, dependently typed, inductive reasoning).

**Key Questions:**
1. What distinguishes the FPC framework's "technology-independent" ambition from LFSC's and Dedukti's own broad-spectrum checking approaches?
2. Why does the paper characterize ad hoc, technology-based proof sharing (e.g. prover A directly consuming prover B's native proof scripts) as fragile across prover versions?

---

### Chapter 14: Conclusions (p. 44)

**Summary:** Summarizes the paper's central claim — that augmenting the focused proof systems LJF and LKF with clerk/expert relational specifications gives both a formal definition and an executable specification for a wide range of proof systems — and reiterates that the richer intuitionistic kernel can host classical-logic checking directly.

**Key Definitions & Concepts by Section:**
- Synthetic inference rule (revisited as the paper's unifying explanatory device).
- Augmented focused proof system as simultaneously a semantic definition and an executable checker specification.

**Key Questions:**
1. In what precise sense does the paper claim its augmented focused systems are "both a formal definition... as well as an executable specification" — and what would be required to show these two roles actually coincide (soundness *and* the specification's computational adequacy)?

---
