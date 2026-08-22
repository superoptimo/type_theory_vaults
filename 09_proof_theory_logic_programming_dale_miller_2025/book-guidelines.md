# Proof Theory and Logic Programming: Computation as Proof Search — Guidelines

## Header

**Title:** Proof Theory and Logic Programming: Computation as Proof Search
**Author(s):** Dale Miller
**Publication:** Cambridge University Press, December 2025 (free online draft dated 30-12-2025; DOI: 10.1017/9781009561280)

**Brief Summary:**
This book develops the proof theory of classical, intuitionistic, and linear logics using Gentzen's sequent calculus, and shows how that proof theory yields a proof-theoretic foundation for logic programming languages. It builds a chain of increasingly expressive abstract logic programming languages — first-order Horn clauses (Prolog), hereditary Harrop formulas ($\lambda$Prolog), and linear-logic-based languages (Lolli, Forum) — all understood through goal-directed proof search, backchaining, and focused proof systems, and proves cut-elimination and completeness theorems for each. The organizing idea is that computation can be modeled as the *search for a proof* of a sequent (rather than as normalization of a proof term), with logic programs read as the left-hand side of a sequent and goals as the right-hand side.

**Intent of the Author:**
Miller wants to establish, via a uniform sequent-calculus and focused-proof-theoretic framework, how successively richer logics (classical/intuitionistic/linear, first- and higher-order) can serve directly as programming languages, and to demonstrate this expressiveness through extended applications (automata, static analysis, security protocols, operational semantics). The book explicitly sets aside the Curry–Howard "proofs-as-programs" tradition (proof normalization as computation) in favor of proof search as computation, though it notes the two perspectives are complementary.

---

## Topic List

1. **Terms, Types, and Formulas in the Simple Theory of Types**
   - The untyped and simply typed $\lambda$-calculus
   - $\alpha$, $\beta$, and $\eta$ conversion and normal forms
   - Simple types and the order of a type
   - Signatures and typed terms
   - Formulas as terms of type $o$
   - Clausal order and polarity of subformula occurrences
   - Sequents as pairs of formula collections

2. **The Sequent Calculus**
   - Frege proofs versus sequent calculus proofs
   - Structural rules: exchange, contraction, weakening
   - Identity rules: initial and cut
   - Introduction rules and eigenvariables
   - Additive versus multiplicative inference rules
   - Permutation of inference rules and invertibility
   - Focused versus unfocused proof systems
   - Cut-elimination and its consequences
   - The subformula property
   - Derivable versus admissible rules

3. **Classical and Intuitionistic Logic**
   - C-proofs and I-proofs as single- versus multiple-conclusion sequent systems
   - Duality of the initial and cut rules
   - Logical equivalence and formula replacement
   - Invertible introduction rules
   - Negation, false, and minimal logic
   - Excluded middle and its proof
   - Nondeterminism in proof search and don't-care versus don't-know choices

4. **Goal-Directed Proof Search and Uniform Proofs**
   - Uniform proofs and abstract logic programming languages
   - The disjunction and existence properties
   - First-order Horn clauses (fohc)
   - First-order hereditary Harrop formulas (fohh)
   - Backchaining as focused rule application
   - The $\Downarrow$fohh focused proof system
   - Completeness of focused proofs for intuitionistic logic
   - Paths in a formula and their associated sequents
   - A canonical Kripke model for intuitionistic provability
   - Synthetic inference rules
   - Modular and hierarchical logic programming
   - Limitations of fohc and fohh (non-reachability, inequality, scoping)

5. **Linear Logic**
   - Linear logic as a logic of resources
   - The exponentials $!$ and $?$
   - Multiplicative additive linear logic (MALL)
   - The eight MALL connectives and their units
   - Duality and polarity of connectives
   - Linear implication $\multimap$ and intuitionistic implication $\Rightarrow$
   - Two-zone (bounded/unbounded) sequents
   - Lolli and the $L_1$ fragment
   - Forum and the $L_2$ fragment
   - Multiple-conclusion uniform proofs
   - Lazy splitting of contexts (the IO proof system)
   - Conservativity of $L_2$ over $L_1$ and $L_0$
   - Generalized synthetic inference rules

6. **Focused Proofs and Cut-Elimination for Linear Logic**
   - Generalized paths and their normal form
   - Admissibility of the general initial rule
   - The four cut rules (cutl, cut!, cut?, key cut) and their elimination
   - Rank, degree, and measure of a cut occurrence
   - Soundness and completeness of $\Downarrow L_2$ with respect to $L$
   - Andreoli's asynchronous and synchronous phases

7. **Linear Logic Programming**
   - Encoding multisets as formulas (conjunctive and disjunctive encodings)
   - Multiset rewriting on the left and on the right of sequents
   - Context management for implementing theorem provers
   - Using linear logic as a metalogic to specify sequent calculus proof systems
   - Object logic versus metalogic

8. **Higher-Order Quantification**
   - Quantification at all types, including predicate and propositional types
   - The near-focused proof system $\Downarrow N$
   - Instantiation of higher-order quantifiers and loss of the subformula property
   - Leibniz equality
   - Cut-elimination via candidats de r\'eductibilit\'e
   - Higher-order programming, tactics, and tacticals
   - Hiding predicates and specification details via existential quantification
   - Proving the symmetry of reverse using higher-order substitution
   - Higher-order Horn clauses and higher-order hereditary Harrop formulas
   - Rigid versus flexible atomic formulas

9. **Specifying Computations with Multisets and Automata**
   - Numerals and arithmetic encoded as multisets
   - Words and letters encoded as $\lambda$-terms
   - Encoding finite automata as linear logic theories
   - Encoding pushdown automata
   - Alternating finite automata via additive conjunction

10. **Collection Analysis for Horn Clauses**
    - Static analysis via approximating data structures by multisets, sets, or lists
    - Substituting for types, non-logical constants, and assumptions in proof theory
    - Multiset and set statements and their linear logic translations
    - Automating collection analysis with specialized proof systems

11. **Encoding Security Protocols and Process Calculi**
    - The $\pi$-calculus and its encoding into linear logic formulas
    - Scope extrusion and restriction
    - Communicating on a public network via multiset rewriting
    - Static distribution of keys and dynamic creation of new symbols
    - Agent clauses, agent theories, and agent state predicates
    - The Needham–Schroeder Shared Key Protocol
    - Agents as nested linear implications

12. **Formalizing Operational Semantics**
    - Multiset rewriting, structural operational semantics, and abstract machines as three frameworks
    - Encoding programs as terms with binding via $\lambda$-abstraction
    - Big-step versus small-step semantics
    - Binary clauses and continuation-passing style
    - The Krivine machine and the SECD machine as abstract evaluation systems
    - Specifying global state and concurrency primitives in linear logic

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 3–9)

**Summary:** Surveys ways to relate logic and computation — computation-as-model versus computation-as-deduction, and within the latter, proof-normalization versus proof-search — and situates the book's approach (proof search via sequent calculus) relative to resolution-based accounts of logic programming and to the Curry–Howard tradition, which the book deliberately sets aside.

**Key Definitions & Concepts:**
- Computation-as-model vs. computation-as-deduction — logic used externally to describe computational structures, versus logic's own syntax (formulas, terms, proofs) serving as the elements of computation.
- Proof-normalization approach — computation as $\beta$-reduction/cut-elimination on a proof term; basis for functional programming.
- Proof-search approach — computation as the process of searching for a proof of a sequent; the book's chosen paradigm.
- $\text{Algorithm} = \text{Logic} + \text{Control}$ (Kowalski) — the gap between a logic specification and an executable algorithm.

**Key Questions:**
1. What distinguishes the proof-search view of computation from the proof-normalization (Curry–Howard) view, and why does the book adopt the former?
2. Why does the author consider basing logic programming on resolution refutation "unfortunate," and what alternative foundation does the book propose instead?

---

### Chapter 2: Terms, formulas, and sequents (pp. 11–20)

**Summary:** Lays the syntactic groundwork — untyped and simply typed $\lambda$-terms following Church's Simple Theory of Types, formulas as terms of type $o$, and sequents as structured collections of formulas — that underlies every later logic in the book.

**Key Definitions & Concepts by Section:**
- **2.1 Untyped $\lambda$-terms** — tokens/variables, application, abstraction $(\lambda x.M)$; $\alpha$-, $\beta$-, $\eta$-conversion; $\beta$-redex, $\eta$-redex; $\beta$-normal form (binder, head, arguments); substitution $s\theta$.
- **2.2 Types** — primitive types (sorts), arrow types $\tau_1 \to \tau_2$; order of a type $\mathrm{ord}(\tau)$; syntactic types (not extensional function spaces).
- **2.3 Signatures and typed terms** — signature $\Sigma$ as typed token declarations; determinate signatures; typing judgment $\Sigma \Vdash t : \tau$; $\beta\eta$-long normal form.
- **2.4 Formulas** — formulas as terms of type $o$; logical constants signature $\Sigma_{-1}$; propositional constants and quantifiers $\forall^\tau, \exists^\tau$; predicate/function symbols; clausal order $\mathrm{order}(B)$; positive/negative subformula occurrence.
- **2.5 Sequents** — sequent $\Gamma \vdash \Delta$ (list/multiset/set-valued); one-sided vs. two-sided sequents; eigenvariables and signature-prefixed sequents $\Sigma :: \Gamma \vdash \Delta$.

**Key Questions:**
1. Why does the book define formulas as terms of type $o$ rather than as a separate syntactic category from terms?
2. What is the practical difference (for proof search) between treating sequent contexts as lists, multisets, or sets?

---

### Chapter 3: Sequent calculus proof rules (pp. 23–38)

**Summary:** Introduces Gentzen's sequent calculus as a more structured alternative to Frege-style proofs, classifies inference rules (structural, identity, introduction; additive vs. multiplicative), and develops the two central proof-theoretic tools of the book: permutability/invertibility of rules and the cut-elimination theorem, motivating focused proof systems.

**Key Definitions & Concepts by Section:**
- **3.1 Sequent calculus and proof search** — informal two-sided sequent reading; derivation trees; multiple-conclusion sequents.
- **3.2 Inference rules** — structural rules (exchange, contraction, weakening); identity rules (init, cut); introduction rules and the small-collection principle; eigenvariables and binder mobility.
- **3.3 Additive and multiplicative inference rules** — subject vs. context occurrence; additive rule (context occurs in every premise) vs. multiplicative rule (context occurs in exactly one premise); cost tradeoffs for proof search vs. proof building.
- **3.4 Sequent calculus proofs** — derivation, proof, endsequent; proof system notation $\vdash_\mathcal{X}$.
- **3.5 Permutations of inference rules** — permuting introduction rules; invertible inference rule.
- **3.6 Focused and unfocused proof systems** — goal-reduction phase vs. backchaining phase; the focus marker $\Downarrow$.
- **3.7 Cut-elimination and its consequences** — cut-elimination theorem; consistency as a corollary; the subformula property; size explosion of cut-free proofs (hyperexponential blowup).

**Key Questions:**
1. Why is an inference rule with two premises classified as additive or multiplicative, and what does this classification predict about the cost of proof search versus proof construction?
2. In what sense does cut-elimination show that the left- and right-introduction rules for a connective "belong to the same connective"?
3. Why can cut-free proofs be useful as computation traces even though they can be astronomically larger than proofs with cut?

---

### Chapter 4: Classical and intuitionistic logics (pp. 39–59)

**Summary:** Presents sequent calculus proof systems for classical logic (C-proofs, multiple-conclusion) and intuitionistic logic (I-proofs, single-conclusion, a restriction of C-proofs), proves cut-elimination and invertibility results, and analyzes negation, minimal logic, and the sources of nondeterminism that proof search must confront — setting up the motivation for linear logic in the next chapter.

**Key Definitions & Concepts by Section:**
- **4.1 Classical and intuitionistic inference rules** — C-proof vs. I-proof (single-conclusion restriction); soundness/completeness of a proof system relative to classical/intuitionistic provability; signature inhabiting a set of types.
- **4.2 The identity rules and their elimination** — atomic initial rule; atomically closed proof; restricting cut to atomic formulas; definitional rules (defL, defR) and local cut permutation without global elimination.
- **4.3 Cut elimination and its consequences** — Theorem 4.13 (cut-elimination for C-/I-proofs); duality of cut and initial; size explosion example; logical equivalence $B \equiv C$ and formula replacement $\Sigma :: C \bowtie D$; invertibility of tR, $\vee$L, $\wedge$R, fL, $\forall$R, $\exists$L, $\supset$R.
- **4.4 Derivable and admissible rules** — derivable rule vs. admissible rule; strengthening; the instan rule.
- **4.5 Negation, false, and minimal logic** — Gentzen's LK/LJ negation rules vs. treating $\neg B$ as $B \supset \mathsf{f}$; minimal logic (M-proofs, no fL); ex falso quodlibet as an admissible rule; G-proofs and their translation to I-proofs.
- **4.6 Choices to consider during the search for proofs** — sources of nondeterminism (cut formula choice, structural rules, connective choice, term instantiation); don't-care vs. don't-know nondeterminism.

**Key Questions:**
1. What precisely distinguishes an I-proof from a C-proof, and why does this distinction anticipate the treatment of the exponentials in linear logic (Chapter 6)?
2. Why is $p \vee (p \supset q)$ a formula with a C-proof but no I-proof, and what does this show about the relative strength of classical versus intuitionistic provability?
3. Which sources of nondeterminism in unrestricted sequent-calculus proof search can be eliminated without losing completeness, and which remain essential ("don't-know") choices?

---

### Chapter 5: Two abstract logic programming languages (pp. 61–102)

**Summary:** Develops the central proof-theoretic account of logic programming: uniform proofs formalize goal-directed search, backchaining and the focused $\Downarrow$fohh proof system formalize the use of program clauses, and these are proved sound and complete for two abstract logic programming languages — first-order Horn clauses (fohc, i.e. Prolog) and first-order hereditary Harrop formulas (fohh, i.e. $\lambda$Prolog) — via a canonical Kripke model and synthetic inference rules; the chapter closes with concrete example programs and a catalogue of expressiveness limitations.

**Key Definitions & Concepts by Section:**
- **5.1 Goal-directed proof search** — uniform proof; abstract logic programming language $\langle D, G, \vdash_\mathcal{X}\rangle$; disjunction and existence properties.
- **5.2 Horn clauses** — three equivalent presentations of fohc (goal $G$/definite clause $D$ grammars); positive/negative Horn clause; curry/uncurry equivalences.
- **5.3 Hereditary Harrop formulas** — fohh via mutually recursive $G$/$D$ grammars; $L_0 = \{\mathsf{t}, \wedge, \supset, \forall\}$; Harrop formulas.
- **5.4 Backchaining as focused rule application** — focused sequent $\Sigma :: P \Downarrow D \vdash A$; the $\Downarrow$fohh proof system; right-introduction (goal-reduction) phase and left-introduction (backchaining) phase; decide rule.
- **5.5 Completeness of focused proofs** — paths in an $L_0$-formula and their associated sequent; admissibility of the general initial rule; cut and key-cut rules; cut-elimination for $\Downarrow^+L_0$; completeness of $\Downarrow L_0$ for intuitionistic provability.
- **5.6 A canonical Kripke model** — worlds as pairs $\langle\Sigma,P\rangle$; canonical Kripke model built from cut-free provability; equivalence of cut/instan admissibility with truth-in-canonical-model coinciding with provability.
- **5.7 Synthetic inference rules** — border sequent; backchaining relation $|\Gamma|_\Sigma$; synthetic inference rule combining backchaining and goal reduction into one derived rule.
- **5.8 Disjunctive and existential goals** — encoding $\vee$ and $\exists$ on the right using non-logical constants $\hat\vee$, $\hat\exists$; completeness of $\Downarrow$fohh-proofs for fohh.
- **5.9–5.12 Examples and dynamics** — $\lambda$Prolog syntax (kind, type, :-, comma, &); example programs (arithmetic, lists, graphs, sorting); modular scoping via implicational goals; scope extrusion in classical logic contrasted with fohh's proper scoping; growth of signature and program during fohh proof search.
- **5.13 Limitations to fohc and fohh logic programs** — inability to express non-reachability, set maximum stored logically, or inequality without explicit constructors; monotonicity of intuitionistic provability.

**Key Questions:**
1. How does the notion of a "uniform proof" formalize the intuition of goal-directed search, and why is completeness of uniform proofs not automatic for an arbitrary logic/connective set?
2. What is a synthetic inference rule, and how does it let a logic program be "compiled away" into inference rules over atomic formulas?
3. Why can fohh logic programs not express properties like graph non-reachability, and what does this reveal about the expressiveness ceiling of intuitionistic Horn-clause-style logic programming?

---

### Chapter 6: Linear logic (pp. 105–136)

**Summary:** Motivates and presents full linear logic (MALL plus the exponentials $!$/$?$) as a resource-sensitive refinement of classical/intuitionistic logic that resolves three limitations of the fohh account of logic programming, introduces two-zone (bounded/unbounded) sequents and the Lolli ($L_1$) and Forum ($L_2$) logic programming languages, and generalizes uniform proofs to the multiple-conclusion setting.

**Key Definitions & Concepts by Section:**
- **6.1 Reflections on the structural inference rules** — interplay of contraction/invertibility; additive vs. multiplicative connective choice; nondeterministic collision of cut with structural rules in LK.
- **6.2 LK vs LJ: an origin story for linear logic** — the two restrictions defining I-proofs as a subset of C-proofs motivate encoding intuitionistic implication as $(!B) \multimap C$ and marking contractible occurrences with $!$/$?$.
- **6.3 Sequent calculus proof systems for linear logic** — the $L$ proof system; **6.3.1** restaurant-style informal semantics for $\otimes$/&; **6.3.2** MALL and its eight connectives (additive $\top,\&,0,\oplus$ / multiplicative $1,\otimes,\bot, `$); **6.3.3** exponentials $!$ (promotion/dereliction/weakening/contraction) and $?$; **6.3.4** De Morgan duality and polarity (positive: $1,0,\otimes,\oplus,\exists,{!}$; negative: $\bot,\top, `,\&,\forall,?$); **6.3.5** linear implication $\multimap$ and intuitionistic implication $\Rightarrow$.
- **6.4 Introducing zones into sequents** — left-unbounded zone $\Psi$ vs. left-bounded zone $\Gamma$; the two-zone proof system $P$ for $L_1 = \{\top,\&,\multimap,\Rightarrow,\forall\}$; the focused $\Downarrow L_1$ proof system; backchaining relation $\|B\|_\Sigma$.
- **6.5 Embedding fohh into linear logic** — Lolli $= \langle L_1, L_1, \vdash_L\rangle$; Girard's translation of intuitionistic logic into linear logic; polarized $(\cdot)^+/(\cdot)^-$ translations.
- **6.6 A model of resource consumption** — lazy splitting of bounded contexts; the IO proof system with input/output option lists; the pick and subcontext predicates.
- **6.7 Multiple-conclusion uniform proofs** — $L_2 = L_1 \cup \{\bot, `, ?\}$ (the Forum presentation); multiple-conclusion uniform proof; the focused $\Downarrow L_2$ proof system with left/right-unbounded and left/right-bounded zones.
- **6.8 Conservativity results** — $\Downarrow L_2$ conservative over $\Downarrow L_1$ and $\Downarrow L_0$.
- **6.9 Generalizing synthetic inference rules** — border sequent generalized to $L_2$; example of specifying a toggling switch via synthetic rules.

**Key Questions:**
1. How do the two restrictions that turn Gentzen's LK into LJ motivate the introduction of the exponentials $!$ and $?$ in linear logic?
2. What is the difference between the additive connectives (&, $\oplus$, $\top$, $0$) and the multiplicative connectives ($\otimes$, ` , $1$, $\bot$) in terms of their operational (proof-search) reading, and how does the "digital fonts" example illustrate this?
3. Why does moving to multiple-conclusion sequents (the $L_2$/Forum presentation) allow linear logic to overcome the three limitations of fohh identified at the start of the chapter?

---

### Chapter 7: Formal properties of linear logic focused proofs (pp. 139–163)

**Summary:** Carries out the technical metatheory of the $\Downarrow L_2$ focused proof system for first-order linear logic — generalized paths, admissibility of the general initial rule, elimination of four cut rules, and soundness/completeness relative to the unfocused proof system $L$ — establishing that focusing loses no provability while gaining a two-phase, deterministic proof-search discipline.

**Key Definitions & Concepts by Section:**
- **7.1 Generalized paths and introduction phases** — paths for $L_2$-formulas and their normal form $\forall\bar{x}[C_1 \Rightarrow \cdots \Rightarrow B_1 \multimap \cdots \multimap A_1 ` \cdots ` {?}E_1\cdots]$; intuitionistic/linear arguments, atomic/?-targets; confluence of the right-introduction rewriting system.
- **7.2 Admissibility of the general initial rule** — Theorem 7.4: the generalized initial rule is admissible for arbitrary $L_2$-formulas, not just atoms.
- **7.3 Cut rules and cut elimination** — four cut rules (cutl, cut!, cut?, key cut, Figure 7.1); border cut vs. non-border cut; thread, rank, degree, and the measure $\langle d,q,w\rangle$ of a cut occurrence; atomic key cut, Rep and absorb rules; Theorem 7.15 (elimination of cuts for $\Downarrow^+L_2$).
- **7.4 The focused proof system is sound and complete** — polarity-respecting translation $(\cdot)^\triangledown/(\cdot)^\blacktriangledown$ between $L$-formulas and $L_2$-formulas; Theorem 7.18 (completeness of $\Downarrow L_2$-proofs).
- **7.5 Cut-elimination for $L$** — Theorem 7.19: cut-elimination for the unfocused proof system $L$ follows from completeness plus cut-elimination for $\Downarrow L_2$.

**Key Questions:**
1. Why must four distinct cut rules (rather than one) be introduced to prove cut-elimination for a two-zone focused proof system, and what special role does the key cut play?
2. In what sense does proving cut-elimination for the *focused* system $\Downarrow L_2$ first, and deriving cut-elimination for the unfocused system $L$ as a corollary, invert the usual (Gentzen-style) order of these results?

---

### Chapter 8: Linear logic programming (pp. 167–180)

**Summary:** Presents a suite of small linear logic programs — multiset encodings, list permutation, multiset rewriting on left and right, and a Lolli-based theorem-prover specification — culminating in a use of $L_2$ as a metalogic to specify sequent calculus proof systems for object-level intuitionistic logic via multiset rewriting on the right.

**Key Definitions & Concepts by Section:**
- **8.1 Encoding multisets as formulas** — conjunctive encoding (unit $1$, combinator $\otimes$) vs. disjunctive encoding (unit $\bot$, combinator ` ); multiset inclusion via $S ` 0 \multimap T$ or $\exists q.(S ` q \multimap T)$.
- **8.2 A syntax for Lolli programs** — Prolog/$\lambda$Prolog-style syntax for the positive connectives (true, comma, semicolon, exists, bang) defined via their right-introduction rules.
- **8.3 Permuting a list** — load/unload predicates using the bounded zone; the role of $!$ in forcing an empty bounded zone.
- **8.4 Multiset rewriting on the left** — encoding an abstract rewriting system $H$ as clauses for a rew predicate.
- **8.5 Context management in a theorem prover** — metalogic vs. object logic; specifying natural-deduction and sequent-calculus provability for propositional intuitionistic logic via hyp/pv predicates; a contraction-free reformulation of $\supset$L (Dyckhoff/Hudelmaier-style) yielding a terminating decision procedure.
- **8.6 Multiset rewriting on the right** — rewriting via the right-bounded zone using ` and the converse connectives $\rhd$/$\Leftarrow$.
- **8.7 Specification of sequent calculus proof systems** — encoding object-level sequents via $\lfloor\cdot\rfloor$/$\lceil\cdot\rceil$ predicates and $?$-marking; specification $J$ of intuitionistic sequent calculus; the special role of $\Leftarrow$ in specifying cut and $\supset$L correctly.

**Key Questions:**
1. How does the $!$ exponential enforce that a subgoal must be proved with an empty bounded zone, and why is this the mechanism that makes the permute/load-unload program correct?
2. Why must the metalevel specification of the object-level cut rule use $\Leftarrow$ rather than the converse of $`$, and what would go wrong (semantically) if it did not?

---

### Chapter 9: Higher-order quantification (pp. 181–206)

**Summary:** Extends linear logic to full higher-order quantification (quantifying at all types, including predicate and propositional types), introduces the near-focused proof system $\Downarrow N$ to handle the loss of stable atomicity under higher-order substitution, proves cut-elimination and completeness for $\Downarrow L_2^\omega$, and demonstrates the distinctive power of higher-order logic programming (hiding predicates, tactics/tacticals, and a proof that list-reversal is symmetric obtained purely by higher-order instantiation).

**Key Definitions & Concepts by Section:**
- **9.1 Introduction** — $L_2^\omega$-formulas; loss of the subformula property under higher-order instantiation; logical connectives appearing inside non-logical contexts.
- **9.2 Higher-order quantification** — $\forall^\tau/\exists^\tau$ for arbitrary $\tau$; $C^\omega$/$I^\omega$ proof systems; Leibniz equality $\forall^{i\to o}P.(Pt \supset Ps)$.
- **9.3 Near-focused proofs** — the near-focused system $\Downarrow N$ (relaxes atomicity requirements on init and decide); reduction of $\Downarrow N$-proofs to $\Downarrow L_2^\omega$-proofs (off-focus measure argument).
- **9.4 The proof theory of higher-order quantification** — Theorem 9.13 (cut-elimination for $\Downarrow N^+$, via candidats de r\'eductibilit\'e, not proved in the text); Theorem 9.14 (cut-admissibility for $\Downarrow L_2^\omega$).
- **9.5 Examples using quantification of type $o$** — defining $0,\top,1,\bot,\&,\oplus$ via higher-order quantification and (multiplicative/exponential) connectives.
- **9.6 Higher-order programming** — forevery, forsome, mappred, sublist, reflexive/symmetric/transitive closure; tactics and tacticals (maptac, then, orelse, repeat).
- **9.7 Proving that reverse is symmetric** — hiding the auxiliary predicate rv via $\forall rv$; proving symmetry of reverse by instantiating $rv$ with $\lambda x\lambda y.(rv\ y\ x)^\perp$, without induction.
- **9.8 Exploiting the hiding of specification details** — using cut-elimination plus higher-order instantiation to derive one implementation of reverse from another.
- **9.9 Synthetic rules and higher-order logic** — instability of clausal order and of rigid/flexible atom status under substitution; higher-order Horn clauses and higher-order hereditary Harrop formulas (restricted to rigid atomic heads).

**Key Questions:**
1. Why does substitution for a higher-order variable break the atomicity invariants that the first-order focused proof systems relied on, and how does the near-focused system $\Downarrow N$ work around this?
2. How does the proof that "reverse is symmetric" use higher-order instantiation (rather than induction) to derive a new fact about a logic program directly from its specification?
3. Why are higher-order Horn clauses and hereditary Harrop formulas restricted to rigid atomic heads, and what problem (repetition-rule-like nondeterminism) does this restriction avoid?

---

### Chapter 10: Specifying computations using multisets (pp. 209–219)

**Summary:** Uses higher-order linear logic and multiset rewriting to give faithful proof-theoretic encodings of natural number arithmetic, finite automata, and pushdown automata, proving (via cut-elimination and higher-order substitution) exact correspondences between machine transitions/language acceptance and provability.

**Key Definitions & Concepts by Section:**
- **10.1 Numerals as multisets** — encoding naturals via $\mathsf{zero}/\mathsf{succ}$ atoms or via multiset multiplicity of a token $\star$; a Fibonacci-number specification via multiset rewriting.
- **10.2 Letters and words** — encoding an alphabet as constants of type $o \to o$ and words as their function-composition.
- **10.3 Encoding finite automata** — automaton $\langle Q,\Lambda,\delta,s,F\rangle$; transition theory $T(\delta)$; Proposition 10.4 (transitions and language acceptance correspond exactly to $\Downarrow L_2^\omega$-provability).
- **10.4 Properties about finite automata** — homomorphic extension and closure of regular languages under homomorphism proved via eigenvariable substitution; splitting transitions using $\exists$; alternating finite automata via additive conjunction.
- **10.5 Encoding pushdown automata** — stack symbols as $o \to o$ constants; transition theory with stack push/pop encoded via ` -extension on both sides of an implication.

**Key Questions:**
1. How does Proposition 10.4 use invertibility and induction on transition-sequence length to show that machine transitions correspond exactly to linear-logic provability?
2. In what precise sense is a finite automaton with an empty stack-symbol set "the same as" a pushdown automaton, and how does this fall out of the shared multiset-rewriting encoding?

---

### Chapter 11: Collection analysis for Horn clauses (pp. 221–235)

**Summary:** Develops a static-analysis technique — collection analysis — that establishes partial correctness properties (e.g. that a sort program produces a permutation) of ordinary Horn clause programs by substituting linear logic multiset, set, or list expressions for data-structure constructors and predicates, then checking the resulting formulas are linear logic theorems.

**Key Definitions & Concepts by Section:**
- **11.1–11.2 Introduction and undercurrents** — motivating example (sorting as a multiset-preserving relation); scoped view of constants/eigenvariables; linear logic as a substrate for "sub-atomic" resource reasoning.
- **11.3 Abstraction and substitution in proof theory** — three substitution mechanisms: for primitive types, for non-logical (predicate) constants via higher-order instantiation, and for assumptions via cut.
- **11.4 Multiset approximations** — multiset expression (item, ` , $\bot$); multiset inclusion $S \sqsubseteq T$ and equality $S \stackrel{m}{=} T$; multiset statement; Proposition 11.1 (linear-logic provability implies validity of the multiset statement); worked sort-program example.
- **11.5 Formalizing the method** — the three-stage method (approximate types/constructors, associate judgments to predicates, prove resulting formulas) justified via substitution-into-proofs.
- **11.6 Set approximations** — set expression (item, &, $\top$); set inclusion $S \subseteq T$ and equality $S \stackrel{s}{=} T$; Proposition 11.3.
- **11.7 Automation of analysis** — specialized decidable proof systems (Figures 11.6, 11.7) for set and multiset statements; TOWER-hardness of multiset statement provability via Petri net reachability.
- **11.8 List approximations** — encoding ordered lists via nested linear implications (a non-commutative device within linear logic); Proposition 11.6 (list-expression equivalence corresponds to list equality).

**Key Questions:**
1. Why does proving that a Horn clause program's linear-logic "multiset abstraction" is a theorem give a *statically* checkable partial-correctness guarantee, when the underlying property (e.g. permutation-preservation) may itself require induction to prove directly?
2. What is lost — and why is the converse of Proposition 11.1 false — when moving from validity of a multiset statement to provability of its linear logic translation?

---

### Chapter 12: Encoding security protocols (pp. 237–251)

**Summary:** Extends multiset-rewriting-in-linear-logic to model communicating processes and, in particular, cryptographic protocols, first sketching a (partial, admittedly flawed) encoding of the $\pi$-calculus and then developing a dedicated notation for network messages, keys, and agent states, applying it to encode and reason about the Needham–Schroeder Shared Key Protocol in two equivalent styles (agent clauses and nested-implication agent formulas).

**Key Definitions & Concepts by Section:**
- **12.1 Communicating processes** — duality of $\otimes$ (static resource access) and ` (process synchronization); the Forum name's origin; $\pi$-calculus prefixes and reduction encoded via send/get/match/or; two flaws of the direct $\pi$-calculus-into-linear-logic encoding ($+$ vs. $\oplus$; $\forall$-left issues).
- **12.2 Specifying communication protocols** — the Needham–Schroeder Shared Key Protocol; **12.2.1** asynchronous public-network messaging via multiset rewriting; **12.2.2** static key distribution via local quantifier-like scoping; **12.2.3** dynamic symbol creation via a new-style quantifier; **12.2.4** mapping the new notation to linear logic (disjunctive vs. conjunctive approach); **12.2.5** encrypted data as an abstract data type.
- **12.3 Protocols as theories in linear logic** — agent identifier, agent state predicate/atom, agent clause, agent theory; encoding of the NS protocol (Figure 12.3).
- **12.4 Abstracting internal states** — reducing $n$-way synchronization to 2-way via hidden intermediate predicates; existential quantification over agent-state predicates for locality.
- **12.5 Agents as nested implications** — $H$/$K$ formula grammars; agents as deeply nested $\rhd$-implications alternating input/output; the equivalent Figure 12.4 encoding of Alice/Bob/server.

**Key Questions:**
1. Why does the direct encoding of $\pi$-calculus $+$ as linear logic $\oplus$ fail to capture the intended reduction semantics, and what alternative (non-logical) encoding is used instead?
2. How does existential quantification over predicate symbols (agent-state predicates, encryption keys) formally capture the notion of "scope" and "locality" that security protocols require?

---

### Chapter 13: Formalizing operational semantics (pp. 253–270)

**Summary:** Surveys three logic-programming-based frameworks for specifying operational semantics — multiset rewriting, structural operational semantics (via Horn clauses/hereditary Harrop formulas), and abstract machines (via binary clauses) — encoding the untyped $\lambda$-calculus and finite $\pi$-calculus as terms with native binding, and shows how linear logic extends binary-clause/abstract-machine specifications to support global state and CML-style concurrency primitives.

**Key Definitions & Concepts by Section:**
- **13.1 Three frameworks for operational semantics** — multiset rewriting; structural operational semantics (big-step/small-step); abstract machines and binary clauses.
- **13.2 The abstract syntax of programs-as-terms** — encoding the untyped $\lambda$-calculus and finite $\pi$-calculus as simply typed terms with $\lambda$-abstraction for binders; $\alpha$-conversion corresponds to $\beta\eta$-convertibility of encodings.
- **13.3 Big-step semantics** — call-by-value evaluation of the $\lambda$-calculus via the eval predicate.
- **13.4 Small-step semantics** — late transition semantics for the finite $\pi$-calculus split into free-action and bound-action ("harpoon" $\rightharpoonup$) relations; Proposition 13.1 (adequacy of the $\lambda$Prolog encoding $D_\pi$).
- **13.5 Binary clauses** — **13.5.1** continuation-passing-style transformation of Horn clauses into binary clauses to force evaluation order; **13.5.2** abstract evaluation systems (AES); the Krivine machine and SECD machine as term-rewriting systems encoded as binary clauses.
- **13.6 Linear logic** — **13.6.1** adding a global counter to an evaluator via multiset rewriting; three logically equivalent specifications of a counter (Proposition 13.2); **13.6.2** specifying Concurrent-ML-style concurrency primitives (sync, spawn, newchan, choose, transmit, wrap, poll) in linear logic.

**Key Questions:**
1. Why must Horn clauses be cps-transformed into binary clauses in order to specify operational semantics with explicit evaluation order and side effects, and what exactly does this transformation add to a plain Horn clause specification?
2. How does linear logic's treatment of resources make it possible to specify a global mutable counter — and to prove several distinct-looking implementations of that counter logically equivalent?
