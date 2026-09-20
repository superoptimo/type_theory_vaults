# An Introduction to Proof Theory: Normalization, Cut-Elimination, and Consistency Proofs — Guidelines

## Header

**Title:** An Introduction to Proof Theory: Normalization, Cut-Elimination, and Consistency Proofs
**Author(s):** Paolo Mancosu, Sergio Galvan, Richard Zach
**Publication:** Oxford University Press, 2021

**Brief Summary:**
The book is an elementary, unusually detailed introduction to classical proof theory, aimed at readers with only a background in propositional and predicate logic. Its first half covers structural proof theory: axiomatic (Hilbert-style) derivations, Gentzen's natural deduction (NM, NJ, NK), the normalization theorem, the sequent calculus (LM, LJ, LK), and the cut-elimination theorem (Hauptsatz) with its consequences. Its second half covers ordinal proof theory: a from-scratch, purely combinatorial development of ordinal notations up to $\varepsilon_0$, culminating in Gentzen's consistency proof for first-order Peano arithmetic by induction along $\varepsilon_0$.

**Intent of the Author:**
The authors wrote the book to fill a gap: no accessible English-language introduction to proof theory covered both structural and ordinal proof theory in enough detail for readers (especially philosophy students) without a strong mathematical background. They intend it as a companion to reading Gentzen's original papers, working through proofs and examples in far more detail than is customary so that no steps are left to the reader's imagination.

---

## Topic List

1. **Hilbert's Program and the Foundations of Proof Theory** : [[Hilberts-Program-and-the-Foundations-of-Proof-Theory|Link]]
   - Hilbert's consistency program and finitism : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
   - Metamathematics versus proper mathematics
   - The foundational debate with Brouwer and Weyl : [[Hilberts-Program-and-the-Foundations-of-Proof-Theory|Link]]
   - Gödel's incompleteness theorems and their impact on Hilbert's program : [[Hilberts-Program-and-the-Foundations-of-Proof-Theory|Link]]
   - Reductive proof theory versus general proof theory : [[Hilberts-Program-and-the-Foundations-of-Proof-Theory|Link]]

2. **Axiomatic (Hilbert-Style) Proof Systems** : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
   - Formulas as inductively defined trees : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
   - Minimal intuitionistic and classical propositional calculi : [[The-Sequent-Calculus|Link]]
   - Modus ponens as the sole inference rule : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
   - Predicate logic with free and bound variables : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
   - Eigenvariables in quantifier rules : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
   - The deduction theorem : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]

3. **Induction as a Proof Method** : [[Induction-as-a-Proof-Method|Link]]
   - Successor induction and strong induction on the natural numbers : [[Induction-as-a-Proof-Method|Link]]
   - Induction on formula complexity and derivation length : [[Induction-as-a-Proof-Method|Link]]
   - Double induction and quadruple induction as proof techniques : [[Normalization-of-Natural-Deduction|Link]]
   - Induction along a well-ordering : [[Induction-as-a-Proof-Method|Link]]

4. **Natural Deduction** : [[Natural-Deduction|Link]]
   - Deductions as trees of formulas with discharged assumptions
   - Introduction and elimination rules for each connective : [[Equivalence-of-the-Proof-Systems|Link1]], [[Natural-Deduction|Link2]]
   - Eigenvariable conditions on quantifier rules : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
   - NM NJ and NK for minimal intuitionistic and classical logic
   - The absurdity rules bottom-J and bottom-K
   - Multiple-conclusion natural deduction : [[Normalization-of-Natural-Deduction|Link1]], [[Natural-Deduction|Link2]]

5. **Normalization of Natural Deduction** : [[Normalization-of-Natural-Deduction|Link]]
   - Detours as introduction rules immediately undone by elimination rules : [[Equivalence-of-the-Proof-Systems|Link]]
   - Normal deductions and the normalization theorem
   - Weak versus strong normalization : [[Normalization-of-Natural-Deduction|Link]]
   - Cut segments and permutation conversions in NJ : [[Normalization-of-Natural-Deduction|Link]]
   - Classical conversions for normalizing NK : [[Normalization-of-Natural-Deduction|Link]]
   - The sub-formula property via threads and paths : [[Normalization-of-Natural-Deduction|Link]]
   - Consistency and the disjunction property as corollaries : [[Normalization-of-Natural-Deduction|Link]]

6. **The Sequent Calculus** : [[The-Sequent-Calculus|Link]]
   - Sequents as antecedent succedent pairs
   - LK LJ and LM as classical intuitionistic and minimal systems : [[The-Sequent-Calculus|Link]]
   - Structural rules of weakening contraction and interchange : [[The-Sequent-Calculus|Link]]
   - Operational left and right rules for connectives and quantifiers : [[The-Sequent-Calculus|Link]]
   - The cut rule and its structural role
   - Regular proofs and the variable replacement lemma : [[The-Sequent-Calculus|Link]]
   - Systematic backward proof search

7. **The Cut-Elimination Theorem (Hauptsatz)** : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]
   - The mix rule as a technical substitute for cut : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]
   - Degree and rank of a mix : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]
   - Double induction on degree and rank : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]
   - Why cut cannot be eliminated directly : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]
   - Cut-elimination for LJ and LM : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]

8. **Consequences of Cut-Elimination** : [[Consequences-of-Cut-Elimination|Link]]
   - The sub-formula property for cut-free proofs : [[Normalization-of-Natural-Deduction|Link]]
   - Consistency of LK LJ and LM : [[Consequences-of-Cut-Elimination|Link]]
   - The disjunction and existence properties of intuitionistic logic : [[Consequences-of-Cut-Elimination|Link]]
   - The mid-sequent theorem and prenex normal form : [[Consequences-of-Cut-Elimination|Link]]
   - Herbrand's theorem : [[Consequences-of-Cut-Elimination|Link]]

9. **Equivalence of the Proof Systems** : [[Equivalence-of-the-Proof-Systems|Link]]
   - Translating axiomatic derivations into natural deduction proofs : [[Equivalence-of-the-Proof-Systems|Link]]
   - Translating natural deduction proofs into axiomatic derivations : [[Equivalence-of-the-Proof-Systems|Link]]
   - Translating NJ deductions into LJ proofs and back

10. **The Gödel–Gentzen Translation** : [[The-Godel-Gentzen-Translation|Link]]
    - Translating classical arithmetic into intuitionistic arithmetic
    - Relative consistency of classical and intuitionistic Peano arithmetic : [[Gentzens-Consistency-Proof-of-Arithmetic|Link1]], [[The-Sequent-Calculus|Link2]]

11. **Gentzen's Consistency Proof of Arithmetic** : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
    - Peano arithmetic as a sequent calculus with atomic mathematical initial sequents
    - The induction rule replacing the induction axiom scheme : [[Induction-as-a-Proof-Method|Link]]
    - Simple proofs and the finitary notion of a true atomic sequent
    - The end part of a proof and boundary inferences
    - Bundles ancestors and descendants of formula occurrences : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
    - Suitable inductions and suitable cuts : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
    - Elimination of weakenings from the end part : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
    - Termination of the reduction procedure via ordinal notations

12. **Ordinal Notations up to $\varepsilon_0$** : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
    - Well-orderings and induction along a well-order : [[Induction-as-a-Proof-Method|Link]]
    - Lexicographical and short-lex orderings of sequences : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
    - Combinatorial construction of ordinal notations by height : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
    - Natural sum of ordinal notations : [[Natural-Deduction|Link1]], [[Ordinal-Notations-up-to-Epsilon-0|Link2]]
    - Ordinal notations are well-ordered : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
    - The level of a sequent and level transitions : [[Ordinal-Notations-up-to-Epsilon-0|Link1]], [[The-Godel-Gentzen-Translation|Link2]]
    - Assignment of ordinal notations to proofs : [[Ordinal-Notations-up-to-Epsilon-0|Link]]

13. **Transfinite Ordinals** : [[Transfinite-Ordinals|Link]]
    - Von Neumann definition of an ordinal : [[Transfinite-Ordinals|Link]]
    - Successor and limit ordinals : [[Transfinite-Ordinals|Link]]
    - The Burali-Forti paradox : [[Transfinite-Ordinals|Link]]
    - Ordinal addition multiplication and exponentiation : [[Transfinite-Ordinals|Link]]
    - Cantor normal form : [[Transfinite-Ordinals|Link]]
    - Constructing $\varepsilon_0$ as a limit : [[Transfinite-Ordinals|Link]]

14. **Applications of Induction up to $\varepsilon_0$** : [[Applications-of-Induction-up-to-Epsilon-0|Link]]
    - The Hydra game and its termination : [[Applications-of-Induction-up-to-Epsilon-0|Link]]
    - Goodstein sequences and Goodstein's theorem : [[Applications-of-Induction-up-to-Epsilon-0|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–12)

**Summary:** Surveys the historical development of proof theory, from Hilbert's consistency program and the foundational crisis provoked by Brouwer and Weyl, through Gödel's incompleteness theorems, to Gentzen's introduction of natural deduction, the sequent calculus, cut-elimination, and his ordinal-based consistency proof for arithmetic, closing with a brief look at post-Gentzen developments (normalization, general proof theory, stronger consistency proofs). : [[Natural-Deduction|Link1]], [[Induction-as-a-Proof-Method|Link2]]

**Key Definitions & Concepts:**
- Hilbert's consistency program — the project of proving the consistency of formalized mathematics by finitary (contentual, epistemologically safe) means
- Finitary / finitism — Hilbert's restriction to inferential procedures acceptable even to intuitionist critics
- Ordinary mathematics, proper mathematics, metamathematics — Hilbert's three-level distinction, introduced to answer Poincaré's circularity objection
- Impredicative definition — a definition of a set that quantifies over a totality to which the set itself belongs
- Gödel's incompleteness theorems — no consistent, sufficiently strong, specifiable system can prove its own consistency by means expressible within it
- Natural deduction and the sequent calculus — Gentzen's two proof systems, introduced in his 1935 dissertation
- Cut rule and cut-elimination theorem (Hauptsatz) — the sequent-calculus rule that lets formulas disappear from a proof, and Gentzen's theorem that it can always be removed
- Ordinal notation and $\varepsilon_0$ — Gentzen's finitary measure of proof complexity, used to show his reduction procedure for arithmetic terminates
- Reductive proof theory versus general proof theory — proof theory in the service of Hilbert's epistemic reduction program versus the study of proofs and their transformations as objects of interest in themselves
- $\omega$-rule — an infinitary inference rule (from $A(0), A(1), A(2), \dots$ infer $\forall x\, A(x)$) used in later, non-finitary consistency proofs
- Gödel's system $T$ — a system of computable functionals of finite type used for an alternative consistency proof of arithmetic

**Key Questions:**
1. Why did Poincaré's circularity objection force Hilbert to distinguish ordinary mathematics, proper mathematics, and metamathematics, and how does that distinction still permit a non-circular consistency proof?
2. In what sense does Gentzen's 1933 translation of classical into intuitionistic arithmetic defend classical mathematics against Brouwer and Weyl, even though it is not itself a finitary consistency proof?
3. How did Gödel's incompleteness theorems reshape the goal of Hilbert's program, and what allowed Gentzen's 1936/1938 consistency proofs to succeed where a strictly finitary proof could not?

---

### Chapter 2: Axiomatic calculi (pp. 13–64)

**Summary:** Presents the propositional and predicate calculi in axiomatic (Hilbert-style) form for minimal, intuitionistic, and classical logic, develops proof by induction and the deduction theorem as core proof-theoretic tools, and closes with Gentzen and Gödel's 1933 result that classical arithmetic $\text{PA}_K$ can be translated into intuitionistic arithmetic $\text{PA}_I$, so that the consistency of $\text{PA}_I$ implies the consistency of $\text{PA}_K$.

**Key Definitions & Concepts by Section:**
- **2.1 Propositional logic** — inductive definition (basis/inductive/extremal clause), formula (atomic formula, built from $\neg, \vee, \wedge, \supset$), metavariable
- **2.2 Reading formulas as trees** — tree representation of a formula's construction, leaf/root : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.3 Sub-formulas and main connectives** — conditional/antecedent/consequent, conjunction/conjuncts, disjunction/disjuncts, main connective, immediate sub-formula, degree $d(A)$ of a formula : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.4 Logical calculi** — minimal logic $M_0$, intuitionistic logic $J_0$ (adds PL11: $\neg A \supset (A \supset B)$), classical logic $K_0$ (adds PL12: $\neg\neg A \supset A$), axiom scheme
- **2.5 Inference rules** — modus ponens (mp), derivation, end-formula, theorem/provable ($\vdash_{S_0} B$), derived rule : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.6 Derivations from assumptions and provability** — derivability from a set $\Gamma$ ($\Gamma \vdash C$), provability as derivability from $\emptyset$, monotonicity : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.7 Proofs by induction** — successor induction, induction basis, inductive step/hypothesis, strong induction : [[Axiomatic-Hilbert-Style-Proof-Systems|Link1]], [[Induction-as-a-Proof-Method|Link2]]
- **2.8 The deduction theorem** — if $\Gamma, A \vdash B$ then $\Gamma \vdash A \supset B$, proved by induction on derivation length : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.9 Derivations as trees** — tree-form derivations (vs. linear axiomatic derivations), repeated leaves for repeated premise uses : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.10 Negation** — informal/intuitionistic vs. classical interpretation of connectives, $\bot$ (arbitrary contradiction), $\neg A \equiv A \supset \bot$, reductio ad absurdum (fails intuitionistically), ex falso quodlibet, minimal negation
- **2.11 Independence** — model-theoretic independence proofs via many-valued truth-tables
- **2.12 An alternative axiomatization of J0** — Gentzen's $J_0^\star$ (Glivenko's axiomatization), shown equivalent to $J_0$
- **2.13 Predicate logic** — free vs. bound variables as distinct syntactic categories, term, formula, axioms QL1 ($\forall x\, A(x) \supset A(t)$), QL2 ($A(t) \supset \exists x\, A(x)$), rules $qr_1, qr_2$, eigenvariable : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.14 The deduction theorem for the predicate calculus** — dependence of a derivation step on an assumption, deduction theorem with eigenvariable condition : [[Axiomatic-Hilbert-Style-Proof-Systems|Link]]
- **2.15 Intuitionistic and classical arithmetic** — Peano arithmetic variants $\text{PA}_M, \text{PA}_I, \text{PA}_K$ (Heyting arithmetic $= \text{PA}_I$), Gödel–Gentzen negative translation $G^*$, translation theorem, consistency, corollary: consistency of $\text{PA}_I$ implies consistency of $\text{PA}_K$ : [[The-Sequent-Calculus|Link]]

**Key Questions:**
1. Why does the extremal clause matter in an inductive definition of formulas, and what would go wrong without it?
2. What role does the eigenvariable condition play in the soundness of $qr_1$/$qr_2$ and in the predicate-calculus deduction theorem, and what breaks if it is dropped?
3. How does the Gödel–Gentzen translation $G^*$ work, and why does it establish that the consistency of intuitionistic arithmetic implies the consistency of classical arithmetic rather than the other way around?

---

### Chapter 3: Natural deduction (pp. 65–100)

**Summary:** Introduces Gentzen's natural deduction systems NM, NJ, and NK for minimal, intuitionistic, and classical predicate logic, in which proofs are trees built from hypothetical assumptions rather than derivations from axioms, with paired introduction/elimination rules for each connective and quantifier, and proves that natural deduction and axiomatic derivation systems prove exactly the same theorems. : [[Equivalence-of-the-Proof-Systems|Link1]], [[Natural-Deduction|Link2]], [[Normalization-of-Natural-Deduction|Link3]]

**Key Definitions & Concepts by Section:**
- **3.1 Introduction** — natural deduction, discharging an assumption, NM, NJ, NK (natural deduction systems for minimal, intuitionistic, classical predicate logic) : [[Natural-Deduction|Link1]], [[Induction-as-a-Proof-Method|Link2]]
- **3.2 Rules and deductions** — deduction (a tree of formulas where every non-assumption formula is the conclusion of a correct rule application; open assumptions; proof; theorem), introduction rule / elimination rule, major premise / minor premise, $\supset$i, $\supset$e, $\wedge$i, $\wedge$e, $\vee$i, $\vee$e, $\bot_J$ (ex falso), $\neg$i, $\neg$e, eigenvariable, $\forall$i, $\forall$e, $\exists$i, $\exists$e and their eigenvariable restrictions : [[Natural-Deduction|Link1]], [[Induction-as-a-Proof-Method|Link2]]
- **3.3 Natural deduction for classical logic** — $\bot_K$ (Prawitz's generalized absurdity rule giving classical logic), alternative routes to NK (adding $A \vee \neg A$, or double-negation elimination) : [[Natural-Deduction|Link]]
- **3.4 Alternative systems for classical logic** — rules gem and nd (alternatives to $\bot_K$), multiple-conclusion natural deduction : [[Natural-Deduction|Link]]
- **3.5 Measuring deductions** — size of a deduction (number of inferences), height of a deduction (longest branch) : [[Natural-Deduction|Link]]
- **3.6 Manipulating deductions, proofs about deductions** — substitution lemma, eigenvariable normalization, substituting a term for a free variable throughout a deduction : [[Natural-Deduction|Link]]
- **3.7 Equivalence of natural and axiomatic deduction** — translating $K_1$-derivations into NK-proofs and vice versa, establishing equivalence of the systems : [[Equivalence-of-the-Proof-Systems|Link]]

**Key Questions:**
1. Why does natural deduction require deductions to be trees of formulas rather than sequences, and how does this structure make tracking dependence on assumptions and their discharge possible?
2. What is the eigenvariable condition on $\forall$i and $\exists$e, and why does violating it let one derive invalid formulas such as $\exists x\, A(x) \supset \forall x\, A(x)$?
3. How does adding $\bot_K$ (or equivalently $A \vee \neg A$, or double-negation elimination) to NJ yield NK, and why does this make some classical deductions harder to find than in NJ?
4. What is the overall strategy by which the equivalence of NK and the axiomatic system $K_1$ is established?

---

### Chapter 4: Normal deductions (pp. 101–167)

**Summary:** Defines the notion of a "detour" in a natural deduction and shows, via the normalization theorem, that every deduction can be transformed into a normal (detour-free) one; establishes the sub-formula property of normal deductions and derives consistency and independence results for NM, NJ, and NK. : [[Natural-Deduction|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Introduction** — detour (an introduction rule immediately followed by an elimination rule applied to its conclusion), grafting a deduction onto open assumptions, normalization, normal deduction, normal form theorem vs. normalization theorem, weak vs. strong normalization : [[Natural-Deduction|Link1]], [[Induction-as-a-Proof-Method|Link2]]
- **4.2 Double induction** — induction on a pair of measures $\langle n, m \rangle$, illustrated by restricting $\bot_J$ to atomic conclusions : [[Induction-as-a-Proof-Method|Link1]], [[Normalization-of-Natural-Deduction|Link2]], [[The-Cut-Elimination-Theorem-Hauptsatz|Link3]]
- **4.3 Normalization for ∧, ⊃, ¬, ∀** — branch, cut/maximal formula, sub-formula property, cut degree $d(\delta)$ and cut rank $r(\delta)$, normalization for the $\wedge, \supset, \neg, \forall$ fragment by double induction on $\langle d(\delta), r(\delta) \rangle$ : [[Normalization-of-Natural-Deduction|Link]]
- **4.4 The sub-formula property** — extended sub-formula definition, thread, analytic part / synthetic part / minimum formula of a thread, order of a thread, theorem that normal deductions have the sub-formula property, consistency corollaries : [[Consequences-of-Cut-Elimination|Link1]], [[Normalization-of-Natural-Deduction|Link2]]
- **4.5 The size of normal deductions** — normal deductions can be exponentially larger than non-normal deductions of the same result : [[Natural-Deduction|Link]]
- **4.6 Normalization for NJ** — cut segment (generalized cut spanning $\vee$e/$\exists$e minor-premise chains), length/degree of a cut segment, rank $r^*(\delta)$, simplification conversions, permutation conversions, normalization theorem for full NJ, strong normalization (Prawitz 1971, proof omitted) : [[Normalization-of-Natural-Deduction|Link]]
- **4.7 An example** — worked normalization example
- **4.8 The sub-formula property for NJ** — path, segment of a path, minimum segment/formula, order of a path, sub-formula property for normal NJ deductions, consistency of NJ, disjunction property, independence results (NJ does not prove $A \vee \neg A$; NM does not prove ex falso) : [[Normalization-of-Natural-Deduction|Link1]], [[Consequences-of-Cut-Elimination|Link2]]
- **4.9 Normalization for NK** — the classical absurdity rule $\bot_K$'s detours resist direct removal, classical conversions (Statman; Andou), additional measures $s(\delta)$, $h(\delta)$, quadruple induction on $\langle d, r, s, h \rangle$, normalization for NK, attenuated sub-formula property for NK : [[Normalization-of-Natural-Deduction|Link]]

**Key Questions:**
1. Why is "detour-freeness" a better proof-theoretic notion of proof simplicity than mere shortness, given that normal deductions can be larger than non-normal ones?
2. How does the sub-formula property follow from normalization, and why does it immediately yield a syntactic consistency proof for NM, NJ, and NK?
3. What specifically makes normalizing NK harder than normalizing NJ, and how do the classical conversions and the extra measures resolve the problem?

---

### Chapter 5: The sequent calculus (pp. 168–201)

**Summary:** Introduces Gentzen's second logical calculus, the sequent calculus (LK, with the intuitionistic restriction LJ and minimal restriction LM), covering its axioms, structural rules, operational rules, and the eigenvariable condition, then a systematic proof-search procedure for building cut-free proofs and an assessment of what the cut rule is good for; closes with a formal translation between NJ-deductions and LJ-proofs establishing their equivalence. : [[Equivalence-of-the-Proof-Systems|Link1]], [[The-Sequent-Calculus|Link2]]

**Key Definitions & Concepts by Section:**
- **5.1 The language of the sequent calculus** — sequent ($\Gamma \Rightarrow \Delta$, antecedent and succedent), empty sequent $\Rightarrow$, translation of a sequent into a single formula : [[The-Sequent-Calculus|Link]]
- **5.2 Rules of LK** — axioms ($A \Rightarrow A$), structural rules (weakening, contraction, interchange, left/right versions) and cut, operational (logical) rules for $\wedge, \vee, \supset, \neg, \forall, \exists$, principal formula, auxiliary formula, side formulas, context, eigenvariable and critical condition, proof in LK, LJ (succedent has at most one formula), LM (LJ without wr) : [[The-Sequent-Calculus|Link]]
- **5.3 Constructing proofs in LK** — systematic bottom-up proof search, using contraction before rules with two "versions," interchange, and reducing eigenvariable-condition rules first : [[The-Sequent-Calculus|Link1]], [[Transfinite-Ordinals|Link2]], [[Induction-as-a-Proof-Method|Link3]]
- **5.4 The significance of cut** — cut as a device for combining separately built proofs and simulating inference steps not directly available operationally; cut-proofs can be much shorter than cut-free proofs : [[The-Sequent-Calculus|Link]]
- **5.5 Examples of proofs** — general axiom, worked LK/LJ/LM proofs of standard laws (Pseudo-Scotus, Paradox of Implication, Double Negation, Tertium Non Datur, Non-Contradiction, Modus Ponens, transitivity of implication, quantifier-transformation laws) : [[The-Sequent-Calculus|Link]]
- **5.6 Atomic logical axioms** — every LK-proof can be transformed into one whose logical initial sequents are all atomic : [[The-Sequent-Calculus|Link]]
- **5.7 Lemma on variable replacement** — variable replacement lemma, regular proof (each eigenvariable tied to a single $\forall$r/$\exists$l inference) : [[The-Sequent-Calculus|Link]]
- **5.8 Translating NJ to LJ** — mapping $P$ from NJ-deductions to LJ-proofs, by induction on the last inference : [[Equivalence-of-the-Proof-Systems|Link1]], [[The-Sequent-Calculus|Link2]], [[The-Godel-Gentzen-Translation|Link3]]
- **5.9 Translating LJ to NJ** — converse mapping $D$ from regular LJ-proofs to NJ-deductions, establishing NJ/LJ equivalence : [[Equivalence-of-the-Proof-Systems|Link1]], [[The-Sequent-Calculus|Link2]], [[The-Godel-Gentzen-Translation|Link3]]

**Key Questions:**
1. Why is the eigenvariable condition on $\forall$r and $\exists$l essential, and what invalid sequents would become "provable" without it?
2. What exactly does the cut rule let LK-proofs do that no combination of other rules can, and how does this connect to the "detours" removed by normalization in natural deduction?
3. Why does bottom-up proof search need special handling via contraction for $\wedge$l and $\vee$r, and why do quantifier rules introduce genuine indeterminacy that other rules avoid?

---

### Chapter 6: The cut-elimination theorem (pp. 202–268)

**Summary:** Proves Gentzen's Hauptsatz — that any LK/LJ/LM proof using cut can be transformed into a cut-free proof of the same end-sequent — via the auxiliary mix rule, and develops the theorem's major consequences: the sub-formula property, consistency, the disjunction and existence properties of intuitionistic logic, and the mid-sequent and Herbrand theorems. : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Preliminary definitions** — mix rule (erasing all occurrences of a mix formula from both premises at once), degree of a mix, degree of a proof ending in mix, left/right branch, left rank $\mathrm{rk}_l(\pi)$ and right rank $\mathrm{rk}_r(\pi)$, rank $\mathrm{rk}(\pi) = \mathrm{rk}_l(\pi) + \mathrm{rk}_r(\pi)$
- **6.2 Outline of the lemma** — Main Lemma (any regular proof ending in a single mix reduces to a mix-free proof); double induction ordered by degree then rank
- **6.3 Removing mixes directly** — mixes eliminable when a premise is an axiom or a weakening; induction basis
- **6.4 Reducing the degree of mix** — mix as principal formula on both sides: mix pushed to an immediate sub-formula, strictly lowering degree : [[The-Cut-Elimination-Theorem-Hauptsatz|Link]]
- **6.5 Reducing the rank** — mix permuted upward past the rule introducing the mix formula, strictly lowering rank at equal degree
- **6.8 Intuitionistic sequent calculus LJ** — LJ presented explicitly, cut-elimination extended to LJ; LM introduced as exercise : [[Equivalence-of-the-Proof-Systems|Link]]
- **6.9 Why mix?** — mix used because permuting cut past a contraction on the cut formula does not straightforwardly lower rank
- **6.10 Consequences of the Hauptsatz** — sub-formula property, consistency theorem, disjunction property of LJ, non-derivability of $A \vee \neg A$ and $\neg\neg A \supset A$ in LJ, non-derivability of ex falso in LM : [[Consequences-of-Cut-Elimination|Link]]
- **6.11 The mid-sequent theorem** — prenex normal form, mid-sequent theorem, order of a quantificational inference/proof, Herbrand's theorem, existence property for LJ/LM : [[Consequences-of-Cut-Elimination|Link]]

**Key Questions:**
1. Why does Gentzen prove eliminability of the mix rule rather than eliminating cut directly, and where does the direct strategy break down?
2. How does the double induction on $\langle$degree, rank$\rangle$ guarantee termination, given that reducing rank can increase the companion degree measure and vice versa?
3. How does cut-freeness, via the sub-formula property, yield both the consistency of LK/LJ/LM and the disjunction/existence properties of intuitionistic logic as corollaries?

---

### Chapter 7: The consistency of arithmetic (pp. 269–311)

**Summary:** Formulates Peano arithmetic (PA) as a sequent-calculus system with atomic mathematical initial sequents and an induction rule cj, then lays out Gentzen's strategy for proving PA consistent: transform any proof of an atomic end-sequent into a "simple" proof by repeatedly removing induction inferences, weakenings, and suitable complex cuts from the proof's end-part, since simple proofs can never prove the empty sequent. : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Introduction** — language of arithmetic ($0, {}', +, \cdot, =$), numeral $\bar n$, mathematical initial sequents $\text{PA}_S1$–$\text{PA}_S10$, induction rule cj ($F(a), \Gamma \Rightarrow \Theta, F(a') \,/\, F(0), \Gamma \Rightarrow \Theta, F(t)$, eigenvariable $a$), abbreviated inference patterns sym and tr : [[Natural-Deduction|Link1]], [[Induction-as-a-Proof-Method|Link2]]
- **7.2 Consistency of simple proofs** — atomic vs. complex cut, simple proof (no free variables, only atomic formulas, only weakening/contraction/interchange/atomic cut), true/false atomic sentence, every sequent in a simple proof is true, $\mathrm{val}(t)$ : [[Gentzens-Consistency-Proof-of-Arithmetic|Link1]], [[Hilberts-Program-and-the-Foundations-of-Proof-Theory|Link2]], [[Normalization-of-Natural-Deduction|Link3]]
- **7.3 Preliminary details** — regular proof in PA, regularization, substitution for eigenvariables, successor/predecessor of a formula occurrence, bundle (maximal chain of successor formula occurrences), ancestor/descendant, implicit vs. explicit bundle and inference, end-part of a proof, boundary inference
- **7.4 Overview of the consistency proof** — three-step reduction strategy: replace suitable inductions by cuts, remove weakenings, reduce suitable complex cuts : [[Gentzens-Consistency-Proof-of-Arithmetic|Link1]], [[Hilberts-Program-and-the-Foundations-of-Proof-Theory|Link2]]
- **7.5 Replacing inductions** — suitable induction inference, cj inferences eliminable from the end-part by unfolding into cuts, induction chain, measures $m(\pi)$/$o(\pi)$ : [[Induction-as-a-Proof-Method|Link]]
- **7.6 Reducing suitable cuts** — reduction of a cut on a complex formula into cuts on sub-formulas, replacing boundary operational inferences by weakenings : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
- **7.7 A first example** — worked illustration of steps 1–3
- **7.8 Elimination of weakenings** — weakenings removable from the end-part : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
- **7.9 Existence of suitable cuts** — suitable cut (complex cut whose cut-formula occurrences descend from principal formulas of boundary inferences) : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
- **7.10 A simple example** — full worked reduction of a proof to a simple proof
- **7.11 Summary** — recap of the three-step procedure; termination requires ordinal notations (Chapters 8–9)

**Key Questions:**
1. Why must the induction axiom be formulated as the inference rule cj rather than as a mathematical initial sequent, and why does this block a direct application of cut-elimination to PA?
2. What is the "end-part" of a proof, and why do Gentzen's reduction steps need to operate on bundles across the whole end-part rather than on isolated sub-proofs?
3. Why does reducing a suitable complex cut initially make the proof larger and multiply cuts rather than shrinking it, and what quantity is actually decreasing on each application?

---

### Chapter 8: Ordinal notations and induction (pp. 312–345)

**Summary:** Develops the combinatorial theory of ordinal notations up to $\varepsilon_0$ from scratch, showing that induction along well-orderings other than the natural numbers is possible; builds the tools needed for the consistency proof of arithmetic in the following chapters, and closes with applications to the Hydra game and Goodstein's theorem. : [[Ordinal-Notations-up-to-Epsilon-0|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Orders, well-orders, and induction** — strict linear order, well-ordering, induction along well-orderings, order isomorphism/order type, successor in a well-order : [[Induction-as-a-Proof-Method|Link1]], [[Ordinal-Notations-up-to-Epsilon-0|Link2]]
- **8.2 Lexicographical orderings** — lexicographical ordering $\prec_{lex}$ on $\mathbb{N}^k$ and $\mathbb{N}^*$, short-lex ordering $\prec_{slex}$, decreasing/non-increasing sequences remaining well-ordered by $\prec_{lex}$ : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
- **8.3 Ordinal notations up to $\varepsilon_0$** — ordinal notations as finite strings built from $0$ and $\boldsymbol{\omega}$ via sums and exponents, defined by height, the ordering $\prec$ : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
- **8.4 Operations on ordinal notations** — natural sum $\alpha \# \beta$, abbreviated form $\boldsymbol{\omega}^{\gamma_1}\cdot c_1 + \cdots$, monotonicity of $\#$, tower function $\omega_n(\alpha)$ : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
- **8.5 Ordinal notations are well-ordered** — proof that $\langle O, \prec \rangle$ is a well-ordering, via the sequence results of §8.2 : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
- **8.6 Set-theoretic definitions of the ordinals** — von Neumann ordinal, successor ordinal $S(\alpha) = \alpha \cup \{\alpha\}$, limit ordinal, Burali-Forti paradox, $\varepsilon_0$ as the least ordinal not nameable by the notations of §8.3
- **8.7 Constructing $\varepsilon_0$ from below** — iterated successor/union construction up to $\varepsilon_0 = \sup\{\omega, \omega^\omega, \omega^{\omega^\omega}, \dots\}$ : [[Transfinite-Ordinals|Link]]
- **8.8 Ordinal arithmetic** — ordinal addition, multiplication, exponentiation via order-isomorphism, Cantor normal form theorem : [[Transfinite-Ordinals|Link]]
- **8.9 Trees and Goodstein sequences** — finite finitely-branching trees as a well-order of type $\varepsilon_0$, the Hydra game and its termination theorem (Kirby and Paris, 1982), hereditary base-$b$ notation, Goodstein sequences and Goodstein's theorem : [[Applications-of-Induction-up-to-Epsilon-0|Link]]

**Key Questions:**
1. Why must ordinal notations be defined purely combinatorially rather than by appeal to transfinite ordinals or set theory?
2. How does the well-ordering of ordinal notations below $\varepsilon_0$ reduce to the well-ordering of sequences over already-established well-orders, and why does this inductive-on-height strategy work?
3. What makes the Hydra game and Goodstein's theorem striking illustrations of induction up to $\varepsilon_0$, given that ordinary induction on $\mathbb{N}$ cannot prove their termination?

---

### Chapter 9: The consistency of arithmetic, continued (pp. 346–379)

**Summary:** Completes Gentzen's consistency proof for PA begun in Chapter 7 by defining an assignment of ordinal notations $< \varepsilon_0$ to proofs and showing that each of the three reduction steps strictly decreases this ordinal notation, so the reduction procedure must terminate in a simple proof — establishing PA's consistency. : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Assigning ordinal notations < ε0 to proofs** — level of a sequent, level transition, ordinal notation assignment $o(S;\pi)$ / $o(I;\pi)$, $o(\pi)$, ordinal notations never decrease going downward in a proof, a proof of an atomic end-sequent has $o(\pi) \prec \boldsymbol{\omega}_1$ iff it is simple : [[Ordinal-Notations-up-to-Epsilon-0|Link]]
- **9.2 Eliminating inductions from the end-part** — replacing a lowermost suitable cj inference by cuts strictly decreases $o(\pi)$ : [[Applications-of-Induction-up-to-Epsilon-0|Link]]
- **9.3 Removing weakenings** — weakening-elimination does not increase the assigned ordinal notation; sequent labelling by level and label correction : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
- **9.4 Reduction of suitable cuts** — extends the reduction of suitable cuts to the general case; reducing an uppermost suitable cut strictly decreases $o(\pi)$ : [[Gentzens-Consistency-Proof-of-Arithmetic|Link]]
- **9.5 A simple example, revisited** — reworks the running example from §7.10 with levels and ordinal notations displayed at every sequent

**Key Questions:**
1. Why must the ordinal notations used to measure proof complexity go all the way up to (but not including) $\varepsilon_0$, and how does Gödel's second incompleteness theorem constrain how much smaller a notation system could be?
2. Why does the ordinal notation assigned to a sequent depend on its level — on inferences occurring below it in the proof — and what problem does this create when inferences are removed during weakening-elimination?
3. How does the reduction of "the ordinal notation of the whole proof decreases" to "the ordinal notation of one replaced sub-proof decreases" work, and why is the absence of intervening cj inferences essential to it?
