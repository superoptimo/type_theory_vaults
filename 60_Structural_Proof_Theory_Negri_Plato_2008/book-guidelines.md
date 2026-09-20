# Structural Proof Theory — Guidelines

## Header

**Title:** Structural Proof Theory
**Author(s):** Sara Negri and Jan von Plato, with an Appendix by Aarne Ranta
**Publication:** Cambridge University Press; first published 2001, this digitally printed version 2008

**Brief Summary:**
This book is both a concise introduction to and a research-level treatment of structural proof theory, the branch of logic studying the structure and properties of formal proofs, in the tradition originating with Gerhard Gentzen's natural deduction and sequent calculus. It develops contraction-free sequent calculi for intuitionistic and classical logic in careful, elementary detail, proves the admissibility of the structural rules (weakening, contraction, cut) and derives cut elimination ("Gentzen's Hauptsatz") from first principles, then extends this machinery to variants of sequent calculi, axiomatic mathematical theories (order, lattice theory, affine geometry), intermediate logics, and back to natural deduction, culminating in an isomorphism between cut-free sequent calculus and normal natural deduction. Appendices cover simple type theory and categorial grammar, constructive type theory, and PESCA, an interactive proof editor for sequent calculus.

**Intent of the Author:**
The authors, writing out of their own research on contraction-free sequent calculi, intend to give students of philosophy, mathematics, and computer science a self-contained, computationally oriented introduction to structural proof theory while also presenting substantial new research results — especially on extending cut-free calculi beyond pure logic into mathematics — that will interest specialists.

---

## Topic List

1. **Natural Deduction and the Inversion Principle** : [[Natural-Deduction-and-the-Inversion-Principle|Link]]
   - BHK meaning explanations for the connectives
   - The inversion principle : [[Natural-Deduction-and-the-Inversion-Principle|Link]]
   - General elimination rules : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]]
   - Normal form and normalization : [[Natural-Deduction-and-the-Inversion-Principle|Link]]
   - Discharge of assumptions : [[Natural-Deduction-and-the-Inversion-Principle|Link]]
   - Detour and permutation conversions : [[Type-Theory-and-Categorial-Grammar|Link]]

2. **Sequent Calculus Foundations** : [[Sequent-Calculus-Foundations|Link]]
   - From natural deduction's derivability relation to sequents : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
   - Left and right rules : [[Sequent-Calculus-Foundations|Link]]
   - Principal, active, and context formulas
   - The subformula property : [[Consequences-of-Cut-Elimination|Link1]], [[Intermediate-Logical-Systems|Link2]], [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link3]], [[Variant-Sequent-Calculi|Link4]]
   - Logical axioms restricted to atoms : [[Intermediate-Logical-Systems|Link]]
   - Contraction-free calculi : [[Variant-Sequent-Calculi|Link]]

3. **Structural Rules and Cut Elimination** : [[Structural-Rules-and-Cut-Elimination|Link]]
   - Weakening, contraction, and cut : [[Sequent-Calculus-Foundations|Link1]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link2]], [[Structural-Rules-and-Cut-Elimination|Link3]]
   - Height-preserving admissibility proofs : [[Structural-Rules-and-Cut-Elimination|Link]]
   - Cut-height induction : [[Structural-Rules-and-Cut-Elimination|Link]]
   - Gentzen's Hauptsatz
   - Invertibility of sequent calculus rules : [[Variant-Sequent-Calculi|Link1]], [[PESCA-the-Sequent-Calculus-Proof-Editor|Link2]], [[Structural-Rules-and-Cut-Elimination|Link3]], [[Sequent-Calculus-Foundations|Link4]]
   - Multicut and Gentzen's mix rule

4. **Consequences of Cut Elimination** : [[Consequences-of-Cut-Elimination|Link]]
   - The disjunction property : [[Consequences-of-Cut-Elimination|Link]]
   - Harrop formulas : [[Consequences-of-Cut-Elimination|Link]]
   - Decidability via terminating proof search : [[Consequences-of-Cut-Elimination|Link]]
   - Underivability by loop-detecting proof search : [[Consequences-of-Cut-Elimination|Link]]
   - Consistency and independence results : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]

5. **Classical Propositional and Predicate Logic** : [[Classical-Propositional-and-Predicate-Logic|Link]]
   - Multisuccedent classical sequent calculus : [[Classical-Propositional-and-Predicate-Logic|Link1]], [[Variant-Sequent-Calculi|Link2]]
   - Regular sequents and trace formulas : [[Classical-Propositional-and-Predicate-Logic|Link1]], [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link2]]
   - Validity as a negative notion : [[Classical-Propositional-and-Predicate-Logic|Link]]
   - Completeness of classical propositional logic : [[Classical-Propositional-and-Predicate-Logic|Link]]
   - Completeness of classical predicate logic : [[Classical-Propositional-and-Predicate-Logic|Link]]
   - The reduction tree method and König's lemma : [[Classical-Propositional-and-Predicate-Logic|Link]]

6. **Quantifiers and First-Order Proof Theory** : [[Quantifiers-and-First-Order-Proof-Theory|Link]]
   - Quantifier rules via the inversion principle : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]]
   - Variable restrictions and eigenvariables
   - Height-preserving alpha-conversion and substitution : [[Quantifiers-and-First-Order-Proof-Theory|Link]]
   - The existence property : [[Quantifiers-and-First-Order-Proof-Theory|Link]]
   - The Herbrand disjunction : [[Variant-Sequent-Calculi|Link]]
   - Failure of prenex normal form intuitionistically
   - The midsequent theorem : [[Quantifiers-and-First-Order-Proof-Theory|Link]]

7. **Variant Sequent Calculi** : [[Variant-Sequent-Calculi|Link]]
   - Sequent calculi with independent contexts : [[Sequent-Calculus-Foundations|Link]]
   - Sequent calculi in natural deduction style : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
   - Multiplicity exponents for weakening and contraction : [[Structural-Rules-and-Cut-Elimination|Link]]
   - The intuitionistic multisuccedent calculus : [[Variant-Sequent-Calculi|Link]]
   - Glivenko's theorem : [[Variant-Sequent-Calculi|Link]]
   - Terminating intuitionistic calculi

8. **Structural Proof Analysis of Axiomatic Theories** : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
   - Axioms as nonlogical rules of inference
   - The closure condition for principal atoms : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
   - Four equivalent ways of adding axioms : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
   - Predicate logic with equality : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
   - Herbrand's theorem for universal theories : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
   - Cut-free theories of order, apartness, and lattices
   - Proof-theoretic independence of the parallel postulate : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]

9. **Intermediate Logical Systems** : [[Intermediate-Logical-Systems|Link]]
   - The weak law of excluded middle : [[Intermediate-Logical-Systems|Link]]
   - Stable logic and the double-negation law : [[Intermediate-Logical-Systems|Link]]
   - Double-negation translations : [[Intermediate-Logical-Systems|Link]]
   - Dummett logic and the linearity axiom
   - Sonobe's relaxed implication rule

10. **The Sequent Calculus–Natural Deduction Isomorphism** : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
    - Weakening and contraction as vacuous and multiple discharge : [[Sequent-Calculus-Foundations|Link1]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link2]]
    - Translation between sequent calculus and natural deduction : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
    - Threads and the subformula property : [[Intermediate-Logical-Systems|Link]]
    - Strong normalization
    - Classical natural deduction via excluded middle on atoms : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Sequent-Calculus-Foundations|Link2]], [[Quantifiers-and-First-Order-Proof-Theory|Link3]]
    - A uniform logical calculus unifying both systems

11. **Type Theory and Categorial Grammar** : [[Type-Theory-and-Categorial-Grammar|Link]]
    - Simple type theory : [[Type-Theory-and-Categorial-Grammar|Link]]
    - Categorial grammar for logical languages : [[Type-Theory-and-Categorial-Grammar|Link]]
    - Bounded and dependent quantifiers : [[Type-Theory-and-Categorial-Grammar|Link]]
    - Constructive type theory : [[Type-Theory-and-Categorial-Grammar|Link1]], [[Variant-Sequent-Calculi|Link2]]
    - Propositions as sets (Curry–Howard)
    - Canonical and noncanonical proof objects : [[Type-Theory-and-Categorial-Grammar|Link]]
    - Type systems as program specifications

12. **PESCA, the Sequent Calculus Proof Editor** : [[PESCA-the-Sequent-Calculus-Proof-Editor|Link]]
    - Top-down determinacy of proof search : [[PESCA-the-Sequent-Calculus-Proof-Editor|Link]]
    - Interactive refinement of proof goals
    - Axiom files for nonlogical rules
    - Translation to sequent calculus and natural deduction LaTeX output : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]

---

## Chapter Summaries

### Chapter 1: From Natural Deduction to Sequent Calculus (pp. 1–24)

**Summary:** The chapter builds natural deduction for propositional logic from meaning explanations (BHK-conditions) via a generalized inversion principle that yields general elimination rules, then shows how sequent calculus arises as an explicit formalization of natural deduction's derivability relation, introducing the structural rules and previewing the book's overall program. : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Logical Systems** — logical language (inductive definition of formulas vs. categorial-grammar/functional definition), proposition vs. formula, rules of inference, Hilbert-style/axiomatic systems, natural deduction systems, sequent calculus systems, derivability, formal proof-object. : [[Intermediate-Logical-Systems|Link]]
- **1.2 Natural Deduction** — BHK-conditions (Brouwer–Heyting–Kolmogorov) for $\&, \vee, \supset, \bot$; introduction rules; inversion principle ("whatever follows from the direct grounds for deriving a proposition must follow from that proposition"); general elimination rules (more general than standard "special" elimination rules); normal form, normalization, strong normalization, uniqueness of normal form; discharge of assumptions and discharge functions; "natural deduction in sequent calculus style" ($\Gamma \vdash A$); rule of excluded middle $Em$ and reductio ad absurdum $Raa$ for classical logic; propositions-as-sets / proof-objects (link to constructive type theory). : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]], [[Sequent-Calculus-Foundations|Link3]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link4]]
- **1.3 From Natural Deduction to Sequent Calculus** — sequent $\Gamma \Rightarrow C$ (antecedent/succedent), right rules (from introduction rules) and left rules (from elimination rules), principal formula vs. active formula vs. context, subformula property, independent vs. shared contexts, logical axiom $A \Rightarrow A$, rule of weakening, rule of contraction, rule of cut, "closure with respect to cut," cut elimination vs. admissibility. : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
- **1.4 The Structure of Proofs** — admissibility of a rule (defined generally), cut-height and formula-weight induction as proof methods, standard applications of cut elimination (consistency, disjunction property, decidability via terminating proof search), extension of sequent calculus to mathematical axioms via nonlogical rules (previewing Chapter 6), intermediate logical systems (previewing Chapter 7), sequent calculus/natural deduction isomorphism (previewing Chapter 8). : [[Sequent-Calculus-Foundations|Link]]

**Key Questions:**
1. Why does the ordinary ("special") elimination rule for disjunction not fit the same normal-form pattern as conjunction and implication, and how does the generalized inversion principle fix this uniformly across all connectives?
2. What is the precise correspondence between vacuous/multiple discharge of assumptions in natural deduction and the structural rules of weakening/contraction in sequent calculus?
3. Why does Girard's example ($\Rightarrow A \supset B$, $\Rightarrow A$ as axioms deriving $\Rightarrow B$) seem to show cut elimination fails once mathematical axioms are added, and what escape does the book propose?

---

### Chapter 2: Sequent Calculus for Intuitionistic Logic (pp. 25–46)

**Summary:** The chapter presents the contraction-free sequent calculus G3ip for intuitionistic propositional logic and proves, by elementary induction on formula weight/derivation height, that weakening, contraction, and cut are all admissible in it, then draws out the main consequences of cut elimination: the subformula property, disjunction property, decidability, and several underivability results. : [[Classical-Propositional-and-Predicate-Logic|Link1]], [[Variant-Sequent-Calculi|Link2]], [[Sequent-Calculus-Foundations|Link3]]

**Key Definitions & Concepts by Section:**
- **2.1 Constructive Reasoning** — computability content of intuitionistic vs. classical reasoning (illustrated by the "decimal expansion" example); apartness relation $a \# b$ vs. classical equality; negative/infinitistic notion of equality ($a = b := \sim a \# b$); law of excluded middle as decidability; genuine reductio ad absurdum vs. constructive proof of a negation; double-negation translation of classical into intuitionistic logic; predicativity (Poincaré, Russell) and impredicative definitions (Russell's paradox, second-order quantification, $\bot := (\forall X)X$). : [[Variant-Sequent-Calculi|Link]]
- **2.2 Intuitionistic Sequent Calculus** — the calculus **G3ip** (rules $L\&, R\&, L\vee, R\vee_1, R\vee_2, L\supset, R\supset, L\bot$), logical axiom restricted to atoms $P, \Gamma \Rightarrow P$, context, active formula, principal formula, shared vs. independent contexts, repetition of principal formula in $L\supset$ (Kleene's device) for a contraction-free calculus. : [[Variant-Sequent-Calculi|Link]]
- **2.3 Proof Methods for Admissibility** — formula weight $w(A)$, derivation height, height-preserving weakening, inversion lemma for $\&, \vee, \supset$, invertibility of rules, non-invertibility of $L\supset$'s first premiss (counterexample via $\bot \supset \bot$).
- **2.4 Admissibility of Contraction and Cut** — height-preserving contraction, cut-height (sum of premiss derivation heights), admissibility of cut for G3ip (the "Hauptsatz") proved by induction on cut-formula weight with subinduction on cut-height, permutation of cut upward through non-principal and principal cases, cut with a shared context as a derived admissible rule. : [[Structural-Rules-and-Cut-Elimination|Link]]
- **2.5 Some Consequences of Cut Elimination** — subformula property; disjunction property and its strengthening to Harrop formulas; equivalence with Hilbert-style axiomatic intuitionistic logic; underivability of excluded middle, weak excluded middle, double negation, Dummett's law, Peirce's law, and disjunction-property-under-hypothesis sequents via loop-detecting cut-free proof search; independence of intuitionistic connectives; decidability of G3ip via bounded proof search. : [[Consequences-of-Cut-Elimination|Link]]

**Key Questions:**
1. Why must the axiom of G3ip be restricted to atomic formulas (excluding $\bot$), and what would break if compound formulas were allowed as axioms?
2. Why does proving admissibility of the cut rule require induction on cut formula weight with a *subinduction* on cut-height, rather than simple induction on either measure alone — and why is cut-height not monotone going down a derivation?
3. How does loop detection in root-first proof search serve as a decision procedure and as the mechanism for proving underivability results like $\not\Rightarrow P \vee \sim P$?

---

### Chapter 3: Sequent Calculus for Classical Logic (pp. 47–60)

**Summary:** Introduces the multisuccedent classical sequent calculus G3cp, motivated by Gentzen's operational reading of sequents $\Gamma \Rightarrow \Delta$ as open assumptions and open cases, and proves its rules invertible, its structural rules admissible, and gives a completeness proof via a decision procedure based on decomposition into regular sequents. : [[Classical-Propositional-and-Predicate-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 An Invertible Classical Calculus** — the calculus G3cp (multisuccedent sequents $\Gamma \Rightarrow \Delta$, multisets, logical axiom $P, \Gamma \Rightarrow \Delta, P$); height-preserving inversion of all rules; uniqueness of decomposition into topsequents; regular sequent (a sequent $P_1,\ldots,P_m \Rightarrow Q_1,\ldots,Q_n,\bot,\ldots,\bot$ with $P_i \neq Q_j$); trace formula of a regular sequent; a formula is equivalent to the conjunction of the trace formulas of its decomposition; negation as a primitive connective (admissible in G3cp via $\sim A = A \supset \bot$). : [[Classical-Propositional-and-Predicate-Logic|Link]]
- **3.2 Admissibility of Structural Rules** — height-preserving weakening and contraction for G3cp; admissibility of cut, proved by induction on cut-height with cases on which premiss is principal; subformula property; discussion of why interdefinability of connectives can break cut elimination (Gentzen's remark on reduced-connective fragments). : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
- **3.3 Completeness** — valuation ($v: \text{Formulas} \to \{0,1\}$); refutable/valid sequent defined negatively (no refuting valuation exists); soundness; completeness via root-first proof search terminating in axioms or regular sequents; decomposition into regular sequents as a syntactic decision procedure for classical propositional validity.

**Key Questions:**
1. Why does restricting the succedent of G3cp's sequents to a single formula recover intuitionistic logic, and what specifically about the $R\supset$ rule is responsible for classicality rather than the multiset structure itself?
2. How does the notion of validity as a negative concept (absence of a refuting valuation) drive the completeness proof, and why is this framing preferred over a positive definition?
3. What is the trace formula of a regular sequent, and how does the decomposition theorem turn root-first decomposition into a syntactic decision procedure for classical propositional logic?

---

### Chapter 4: The Quantifiers (pp. 61–86)

**Summary:** Extends the language, natural deduction, and sequent calculus (G3i, G3c) with quantifiers, proves the structural properties (height-preserving $\alpha$-conversion, substitution, weakening, contraction, cut admissibility) needed to keep cut elimination in first-order logic, and derives consequences — the existence property, several underivability results distinguishing intuitionistic from classical logic, the midsequent theorem, and completeness of classical predicate logic via Schütte's reduction-tree method.

**Key Definitions & Concepts by Section:**
- **4.1 Quantifiers in Natural Deduction and in Sequent Calculus** — first-order language (terms, formulas, free/bound variables); substitution $A(t/x)$ and the "free for $x$" condition; quantifier introduction/elimination rules for natural deduction, including the general elimination rule for $\forall$ derived from the inversion principle; sequent calculus rules $L\forall$, $R\forall$, $L\exists$, $R\exists$ for G3i and G3c with variable restrictions; weight of quantified formulas $w(\forall xA) = w(A)+1$; height-preserving $\alpha$-conversion; the substitution lemma. : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
- **4.2 Admissibility of Structural Rules** — height-preserving weakening, inversion of $L\exists$/$R\forall$, contraction, and cut for both G3i and G3c, with the new technical device of substituting a fresh variable before permuting cut past a quantifier rule with a variable restriction. : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
- **4.3 Applications of Cut Elimination** — subformula property extended to quantifiers; consistency; existence property for G3i and its failure in G3c (Herbrand disjunction instead); underivability of $\sim\forall x\sim A \supset \exists xA$ and of the predicate-logic form of Glivenko's theorem in G3i, both via infinite root-first proof search; failure of prenex normal form intuitionistically; midsequent theorem for G3c. : [[Consequences-of-Cut-Elimination|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]], [[Structural-Rules-and-Cut-Elimination|Link3]]
- **4.4 Completeness of Classical Predicate Logic** — valuation extended to quantifiers via inf/sup; soundness; reduction tree construction (staged root-first rule application); König's lemma; completeness — a finite reduction tree gives a proof, an infinite one (by König's lemma) yields a refuting valuation. : [[Classical-Propositional-and-Predicate-Logic|Link]]

**Key Questions:**
1. Why must a fresh variable be substituted before permuting cut past a quantifier rule with a variable restriction, and what would go wrong in the cut-elimination proof without this step?
2. How does the failure of prenex normal form in intuitionistic logic reveal a structural difference from classical logic, and how is underivability shown via nonterminating root-first proof search?
3. In the completeness proof for G3c, how does König's lemma bridge the gap between a nonterminating reduction tree and the construction of an explicit refuting valuation?

---

### Chapter 5: Variants of Sequent Calculi (pp. 87–125)

**Summary:** This chapter presents alternative formulations of sequent calculus beyond the shared-context G3 calculi of Chapters 2–4: calculi with independent contexts and explicit structural rules (closer to Gentzen's original LJ/LK), calculi with structural rules built in implicitly (closer to natural deduction), a multisuccedent intuitionistic calculus, a single-succedent classical calculus obtained by adding excluded middle to intuitionistic logic, and a terminating calculus for intuitionistic propositional logic. : [[Variant-Sequent-Calculi|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Sequent Calculi with Independent Contexts** — GOi, GOc (calculi with independent contexts and explicit weakening/contraction, dual to Gentzen's LJ/LK); multicut (Gentzen's original device eliminating $m>1$ copies of a cut formula in one step, avoided here); cut elimination without multicut, handled via a global case analysis on the derivation of contraction's premiss. : [[Sequent-Calculus-Foundations|Link]]
- **5.2 Sequent Calculi in Natural Deduction Style** — GN, GM (calculi with no explicit structural rules; formulas carry multiplicity exponents $A^m$, so $m=0$ encodes weakening and $m>1$ contraction); multiset reduct (a context obtained from another by multiplying/deleting formulas); redundant cut, hereditarily principal / hereditarily nonprincipal / hereditarily vacuous / hereditarily multiple cut; subformula property proved via elimination of hereditarily principal cuts only. : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
- **5.3 An Intuitionistic Multisuccedent Calculus** — G3im (Dragalin's GHPC), with left/right implication and universal-quantifier rules restricted so exactly one formula appears in a premiss succedent; height-preserving weakening/contraction/inversion for G3im; equivalence theorem: $\Gamma \Rightarrow \Delta$ in G3im iff $\Gamma \Rightarrow \bigvee\Delta$ in G3i — the succedent comma behaves as intuitionistic disjunction. : [[Variant-Sequent-Calculi|Link]]
- **5.4 A Classical Single Succedent Calculus** — rule of excluded middle restricted to atoms, Gem-at; G3ip+Gem-at as a cut-free classical calculus retaining intuitionistic connective rules; proof that Gem for arbitrary formulas is admissible (by induction on formula length); Glivenko's theorem (a classical proof of a negated formula $\Gamma \Rightarrow {\sim}C$ converts to an intuitionistic one) proved by explicit transformation; strict subformula property (Gem-at restricted to atoms of the conclusion $C$); application to Peirce's law. : [[Variant-Sequent-Calculi|Link]]
- **5.5 A Terminating Intuitionistic Calculus** — G4ip (Hudelmaier/Dyckhoff), refining the left implication rule $L\supset$ into four rules keyed to the form of the antecedent ($P$, $C\&D$, $C\lor D$, $C\supset D$) to avoid the looping repetition of the principal formula; a weight function making active formulas strictly lighter than principal formulas; admissibility of contraction and cut for G4ip, and its equivalence with G3ip. : [[Variant-Sequent-Calculi|Link]]

**Key Questions:**
1. Why does eliminating multicut let Gentzen avoid the complication that arises when the right premiss of an ordinary cut is derived by contraction, and how do GOi/GOc's proofs sidestep multicut altogether?
2. In what precise sense does the calculus GN encode weakening and contraction "implicitly," and why does cut elimination there only need to target hereditarily principal cuts rather than all cuts?
3. What does the equivalence theorem for G3i and G3im reveal about the relationship between multisuccedent sequents and disjunction?
4. Why must the rule of excluded middle be restricted to atoms (Gem-at) to preserve a subformula property, and how does lifting this restriction back to arbitrary formulas avoid breaking cut-admissibility?
5. What is the structural reason (in terms of formula weight and antecedent shape) that G4ip guarantees termination of proof search where G3ip's plain $L\supset$ rule does not?

---

### Chapter 6: Structural Proof Analysis of Axiomatic Theories (pp. 126–155)

**Summary:** Develops a general method for adding mathematical axioms to sequent calculus as *nonlogical rules of inference* — formulated so that cut remains eliminable — then applies it to build cut-free systems for equality, apartness, order, lattice theory, and plane affine geometry. : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 From Axioms to Rules** — nonlogical rules have only atoms as active/principal formulas in the antecedent, arbitrary succedent context; rule-scheme $\frac{Q_1,\Gamma\Rightarrow\Delta \;\ldots\; Q_n,\Gamma\Rightarrow\Delta}{P_1,\ldots,P_m,\Gamma\Rightarrow\Delta}$; regular sequent, trace formula (four types); invertible/noninvertible leaf; regular formula and its regular decomposition / regular normal form; the closure condition (handles substitution instances collapsing two principal atoms). : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
- **6.2 Admissibility of Structural Rules** — height-preserving weakening, contraction, and cut proved admissible for $\text{G3im}^*$/$\text{G3c}^*$ (multisuccedent calculi extended with nonlogical rules satisfying the scheme and closure condition). : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
- **6.3 Four Approaches to Extension by Axioms** — A-system (axioms as initial sequents), B-system (basic sequents), C-system (axioms as context formulas), R-system (axioms as rules); proof of equivalence of all four.
- **6.4 Properties of Cut-free Derivations** — subformula property for nonlogical-rule systems (all formulas are subformulas of the endsequent or atomic); consistency/inconsistency criteria from derivation shape; syntactic independence proofs for axioms via underivability. : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
- **6.5 Predicate Logic with Equality** — reflexivity rule Ref ($a=a,\Gamma\Rightarrow\Delta$), replacement rule Repl for atomic predicates, admissibility of Repl for arbitrary predicates; Repl* (contracted replacement); conservativity of equality logic over pure predicate logic via elimination of Ref. : [[Structural-Proof-Analysis-of-Axiomatic-Theories|Link]]
- **6.6 Application to Axiomatic Systems** — Herbrand's theorem for universal theories and its corollary for classical predicate logic; cut-free rule systems for theories of equality (Ref, Trans), decidable equality (Gem-at/Deq), apartness (Irref, Split), decidable apartness (Dap); disjunction property for apartness; constructive linear order (Asym, Split) and partial order (Ref, Trans), nondegenerate partial order, conservativity results; lattice theory rules and conservativity over partial order; plane affine geometry — apartness-style primitives ($a\ne b$, $l\ne m$, $l\between m$ convergent, $A(a,l)$ outside), constructions ($ln(a,b)$, $pt(l,m)$, $par(l,a)$), independence of the parallel postulate proved proof-theoretically.

**Key Questions:**
1. Why must nonlogical rules restrict active/principal formulas to atoms in the antecedent, and how does the closure condition patch the one case (duplicated principal atoms) this restriction would otherwise break?
2. In what precise sense are the A-, B-, C-, and R-system formulations of "adding axioms" equivalent, and why do only C- and R-systems dispense with cut?
3. How does converting Euclid's fifth postulate into a nonlogical-rule derivation turn independence of the parallel postulate into a proof-search/underivability argument rather than a model-theoretic one?

---

### Chapter 7: Intermediate Logical Systems (pp. 156–164)

**Summary:** Studies logics strictly between intuitionistic and classical propositional logic — weak excluded middle, stable (double-negation) logic, and Dummett logic — via sequent-calculus rules added to $\text{G3ip}$/$\text{G3ipm}$, extending the nonlogical-rule and axiom-as-rule methodology of Chapters 5–6 to logical (not just mathematical) principles. : [[Intermediate-Logical-Systems|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 A Sequent Calculus for the Weak Law of Excluded Middle** — weak excluded middle $\neg A\vee\neg\neg A$; rule Wem-at for atoms, $\frac{\neg P,\Gamma\Rightarrow C \quad \neg\neg P,\Gamma\Rightarrow C}{\Gamma\Rightarrow C}$; admissibility of structural rules (no principal formula); extension Wem to arbitrary formulas by induction on weight; adjusted subformula property (formulas or negated-negated atoms). : [[Intermediate-Logical-Systems|Link1]], [[PESCA-the-Sequent-Calculus-Proof-Editor|Link2]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link3]]
- **7.2 A Sequent Calculus for Stable Logic** — stability $\neg\neg A\supset A$; rule of indirect proof for atoms, Raa-at; $\text{G3ip}+\text{Raa-at}$ is *not* complete for classical logic, unlike Wem-at with Gem-at; structural rules admissible; Raa restricted to disjunction-free fragment; double-negation translation (Kolmogorov/Gödel–Gentzen) connecting classical and intuitionistic derivability; unrestricted Raa gives a complete but non-cut-eliminable calculus. : [[Classical-Propositional-and-Predicate-Logic|Link]]
- **7.3 Sequent Calculi for Dummett Logic** — Dummett's law $(A\supset B)\vee(B\supset A)$; (a) left rule Dmt-at for atoms (admissible structurally, but *not* extendable to arbitrary formulas — implication case fails); (b) calculus $\text{G3LC}$ via Sonobe's relaxed right-implication rule $S{\supset}R$ (introduces several implications at once) and modified left-implication rule; admissibility of weakening, identity sequents, auxiliary permutation lemmas, contraction; cut admissible in $\text{G3LC}$. : [[Sequent-Calculus-Foundations|Link1]], [[Variant-Sequent-Calculi|Link2]]

**Key Questions:**
1. Why does the rule Raa-at (indirect proof restricted to atoms) fail to yield full classical completeness, while the analogous restriction Wem-at (weak excluded middle on atoms) succeeds — what does this reveal about the different logical strength of stability vs. weak excluded middle?
2. Why does the natural left rule for Dummett's law work for atoms but break down for compound (especially implicational) formulas, forcing a switch to a modified *right* implication rule instead?
3. What is the trade-off in $\text{G3LC}$ between gaining a genuine cut-elimination proof for Dummett logic and the loss of a clean single-formula subformula property, given the relaxed multi-formula right-implication rule?

---

### Chapter 8: Back to Natural Deduction (pp. 165–210)

**Summary:** This chapter establishes a precise, formal correspondence between natural deduction with general elimination rules and cut-free sequent calculus, showing that weakening and contraction correspond exactly to vacuous and multiple discharge of assumptions, and it uses this correspondence to give both a translation-based and a direct proof of strong normalization, culminating in a normal form for classical propositional natural deduction via a rule of excluded middle. : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]], [[Sequent-Calculus-Foundations|Link3]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link4]]

**Key Definitions & Concepts by Section:**
- **8.1 Natural Deduction with General Elimination Rules** — unique discharge of assumptions (no two rule instances share a discharge label); formal derivability relation for natural deduction (open assumptions form a multiset, not a metamathematical relation); discharge labels vs. assumption labels; vacuous discharge ($m=0$ or $n=0$) and multiple discharge ($m>1$ or $n>1$); composition of derivations / closure under substitution, formalized as the rule $\dfrac{\Gamma \vdash A \quad A,\Delta \vdash C}{\Gamma,\Delta \vdash C}\ \mathrm{Subst}$, distinct in character from cut. : [[Quantifiers-and-First-Order-Proof-Theory|Link]]
- **8.2 Translation from Sequent Calculus to Natural Deduction** — used formula (active in an antecedent of a logical rule); translation defined only for derivations in $\mathrm{G0i}$ with no inactive (unused) weakening/contraction formulas; full normal form (all major premisses of E-rules are assumptions); weakening formulas become vacuously discharged, contraction formulas multiply discharged; multiset reduct. : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
- **8.3 Translation from Natural Deduction to Sequent Calculus** — inductive translation of fully normal derivations to $\mathrm{G0i}$; converse translation; subformula property of normal natural deduction derivations, derived via the sequent-calculus translation; isomorphism between normal ND derivations and cut-free sequent-calculus derivations (exact via translation to $\mathrm{GN}$, which has no explicit structural rules); translation of the *special* elimination rules (ordinary $\&E$, modus ponens) shown to correspond to "hidden cuts" in sequent calculus, i.e. cut elimination fails for the zero-premiss special rules. : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
- **8.4 Derivations with Cuts and Non-normal Derivations** — detour cuts and permutation cuts (together, principal cuts) vs. nonprincipal cuts; conversion formula (a major premiss of an E-rule that is not an assumption); translation of derivations-with-cuts back to natural deduction; translation of the five kinds of non-normal instances into sequent calculus with cut; normalization theorem (translate to sequent calculus, eliminate cut, translate back — yields a normal derivation, non-unique since cut elimination is non-unique). : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link]]
- **8.5 The Structure of Normal Derivations** — detour conversions (generalized, with multiset substitution for vacuous/multiple discharge); permutation conversions for general elimination rules; simplification conversions (an E-rule instance with no discharged assumptions, corresponding to a hereditarily vacuous cut); thread (a chain of formulas through major/minor premisses replacing "branch" once disjunction/general elimination is present); direct proof of the subformula property via threads; Ekman's problem of normal form, solved using the general implication-elimination rule; translation of intuitionistic to minimal logic; proper assumption (an underivable major premiss) and eliminability of derivable principal formulas (Mints's result); direct proof of strong normalization via a lexicographic ordering of threads by height of major premisses and a multiset ordering of convertible-formula lengths. : [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link1]], [[Structural-Rules-and-Cut-Elimination|Link2]], [[Intermediate-Logical-Systems|Link3]]
- **8.6 Classical Natural Deduction for Propositional Logic** — rule of excluded middle for atoms $\mathrm{Gem0\text{-}at}$: $\dfrac{P,\Gamma\Rightarrow C \quad {\sim}P,\Delta\Rightarrow C}{\Gamma,\Delta\Rightarrow C}$ with independent contexts; cut admissible in $\mathrm{G0ip}+\mathrm{Gem0\text{-}at}$; excluded middle for arbitrary formulas, $\mathrm{Gem0}$, is admissible; natural-deduction rule $\mathrm{Nem\text{-}at}$ (discharging $P$ and $\sim P$) and its translation to/from $\mathrm{Gem0\text{-}at}$; the classical rule of indirect proof as a derivable special case of $\mathrm{Nem\text{-}at}$, and its failure of full normal form (repaired by the general-elimination-rule formulation); excluded middle on compound formulas converts to excluded middle on atoms; full normal form for intuitionistic ND + $\mathrm{Nem\text{-}at}$; restriction of $\mathrm{Nem\text{-}at}$ instances to atoms of the conclusion; classical derivability of $C$ iff $(P_1\lor{\sim}P_1)\&\ldots\&(P_n\lor{\sim}P_n)\supset C$ is intuitionistically derivable — giving a Curry–Howard-style reading of classical proofs as functions turning decisions on atoms into a proof of $C$. : [[Classical-Propositional-and-Predicate-Logic|Link]]

**Key Questions:**
1. Why does the *usual* natural-deduction elimination rule for conjunction (and modus ponens) fail to correspond isomorphically to cut-free sequent calculus, and how does replacing it with the *general* elimination rule restore the correspondence?
2. In what precise sense do weakening and contraction in sequent calculus "mean" vacuous and multiple discharge of assumptions in natural deduction, and why does this require the *formal* (multiset-based) derivability relation rather than the usual metamathematical one?
3. What is a "thread," why does it replace "branch" as the carrier of the subformula property once general elimination rules are used, and how does the height of major premisses along threads drive the direct proof of strong normalization?
4. How does the rule of excluded middle for atoms ($\mathrm{Gem0\text{-}at}$) yield both admissibility of cut and a full normal form for classical propositional natural deduction, and what does this reveal about the layered (minimal/intuitionistic/classical) structure of a classical proof?

---

### Conclusion: Diversity and Unity in Structural Proof Theory (pp. 211–218)

**Summary:** Compares natural deduction and sequent calculus as they were developed through the book, showing how the shift to general elimination rules and independent-context calculi narrows the gap between them, then presents a single uniform logical calculus MG (a multiple-conclusion natural deduction with general rules written sequent-calculus-style) from which sequent calculus, natural deduction, and their rule inverses can all be recovered as special cases. : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]], [[Sequent-Calculus-Foundations|Link3]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link4]]

**Key Definitions & Concepts by Section:**
- **Comparing Sequent Calculus and Natural Deduction** — sequent calculus supports root-first proof search better than natural deduction; structural modifications ("Strukturänderungen": weakening, contraction, exchange, change of bound variable) per Gentzen; Hertz's simultaneous cut / "syllogism" rule $\Gamma_1\Rightarrow A_1 \ \ldots\ \Gamma_n\Rightarrow A_n \ \ A_1,\ldots,A_n,\Delta\Rightarrow B \big/ \Gamma_1,\ldots,\Gamma_n,\Delta\Rightarrow B$; multicut vs. Gentzen's mix rule as generalizations of cut; the "chain rule" ("Kettenschluss").
- **A Uniform Logical Calculus** — the uniform calculus $MG$: contexts as multisets, single-arrow derivability notation, rule of assumption $A\to A$, general introduction rules formulated in symmetry with general elimination rules; normalization for $MG$ via translation to $GM{+}\mathrm{Cut}$, cut elimination, and translation back; $MG$ is not strongly normalizing; recovery of multisuccedent sequent calculus $GM$/$G\Omega c$, single succedent calculus $GN$/$G\Omega i$, inverses of sequent calculus rules, and natural deduction systems $NG$ as special cases/substitution instances of $MG$.

**Key Questions:**
1. In what precise sense does treating weakening and contraction implicitly (rather than as explicit structural rules) bring cut-free sequent-calculus proofs and normal natural-deduction proofs into exact correspondence, and what residual difference between cut and detour conversion remains even then?
2. How does the uniform calculus $MG$ recover ordinary sequent calculus rules, their inverses, and natural deduction rules as three different substitution/restriction instances of the same general logical rules?

---

### Appendix A: Simple Type Theory and Categorial Grammar (pp. 219–224)

**Summary:** Introduces simple type theory (functional abstraction, application, $\beta$-conversion) as a general framework for functions, then uses it as a categorial grammar to define the languages of propositional and predicate logic, including bounded quantifiers, as an alternative to the inductive-clause definition of Chapter 1. : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]], [[Sequent-Calculus-Foundations|Link3]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link4]]

**Key Definitions & Concepts by Section:**
- **A.1 Simple Type Theory** — type ($\alpha,\beta,\gamma,\ldots$) as domain/range of functions; function type $(\alpha)\beta$; declaration $a:\alpha$; functional application $f:(\alpha)\beta,\ a:\alpha \big/ f(a):\beta$; functional abstraction $[x:\alpha]\ b:\beta \big/ (x)b:(\alpha)\beta$; definitional equality $a=b:\alpha$; $\beta$-conversion $((x)b)(a)=b(a/x):\beta$; multi-argument functions as curried applications; category $\mathrm{Prop}$; propositional functions (e.g. $\mathrm{Even}:(N)\mathrm{Prop}$, $\mathrm{Incident}:(\mathrm{Point})(\mathrm{Line})\mathrm{Prop}$).
- **A.2 Categorial Grammar for Logical Languages** — atomic propositions as parameters $P,Q,R:\mathrm{Prop}$; connectives as functions ($\mathrm{Not}:(\mathrm{Prop})\mathrm{Prop}$, $\mathrm{And}, \mathrm{Or}, \mathrm{Implies}:(\mathrm{Prop})(\mathrm{Prop})\mathrm{Prop}$); infix notation as hidden functional structure with binding conventions; equivalence and negation as defined notions; grammar summary $A::=\bot \mid P \mid A\&B \mid A\vee B \mid A\supset B$; quantifiers as functions $\mathrm{Every}, \mathrm{Some}:((D)\mathrm{Prop})\mathrm{Prop}$ over a fixed domain $D$; bounded quantifiers $\forall(D,A)$, $\exists(D,A)$ with variable domain $D:\mathrm{Set}$, needing types beyond simple type theory; $\alpha$-conversion for renaming bound variables.

**Key Questions:**
1. How does representing connectives and quantifiers as typed functions (rather than as symbols governed by inductive formation clauses) make explicit the "functional structure" that ordinary infix/quantifier notation hides, and why does this require moving beyond simple type theory for bounded quantifiers?
2. What is the difference between the fixed-domain quantifiers $\mathrm{Every}/\mathrm{Some}:((D)\mathrm{Prop})\mathrm{Prop}$ and the bounded, dependently-typed quantifiers $\forall(D,A)/\exists(D,A)$ with $D:\mathrm{Set}$ as an argument?

---

### Appendix B: Proof Theory and Constructive Type Theory (pp. 225–234)

**Summary:** Develops constructive (Martin-Löf) type theory in two stages — a lower-level theory that attaches proof-objects to the rules of natural deduction via the propositions-as-sets principle, and a higher-level theory generalizing simple type theory with dependent types — then illustrates type systems with a formalization of elementary geometry. : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]], [[Sequent-Calculus-Foundations|Link3]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link4]]

**Key Definitions & Concepts by Section:**
- **B.1 Lower-level Type Theory** — four judgment forms: $A:\mathrm{Prop}$ ($A:\mathrm{Set}$), $a:A$, $a=b:A$, $A=B:\mathrm{Set}$; proof-object/proof term; reflexivity and transitivity rules for definitional equality (symmetry derived); dependent types / product type $(x:A)B$; hypothetical judgments in a context; constructors ($\mathrm{pair}$, injections, $\lambda$-abstraction) vs. selectors (projections, $\mathrm{ap}$, general selectors $\&E$, $\mathrm{gap}$, $\vee E$); computation (equality) rules relating selectors to constructors; canonical vs. noncanonical proof-objects (Dummett's constructive semantics); general elimination rules for conjunction/implication in type theory and their reduction to the special elimination rules.
- **B.2 Higher-level Type Theory** — dependent type $(x:\alpha)\beta$ as a family of types parametrized by $\alpha$; generalized functional abstraction/application/$\beta$-conversion for dependent types; bounded quantifier categorization $\forall:(A:\mathrm{Set})(B:(A)\mathrm{Prop})\mathrm{Prop}$; explicit typings of constructors and selectors carrying their type arguments.
- **B.3 Type Systems** — type theory read as constructive set theory (conjunction = intersection, disjunction = disjoint union, $\forall$ = Cartesian product, $\exists$ = direct sum) vs. as program specification (types as problems, objects as programs, $a:A$ as "$a$ meets specification $A$"); worked example: elementary geometry as a type system with dependently-typed constructions for connecting lines and intersection points; proof editors as interactive, type-checked proof/program development systems; formally verified proof as a terminating program converting given data to a solution.

**Key Questions:**
1. How does the lower-level type theory recover ordinary natural deduction "by hiding all the proof-objects," and in what sense are the computation rules the type-theoretic counterpart of detour conversion?
2. Why does formalizing elementary geometry (e.g. unique connecting lines and their incidence properties) require dependent typing rather than the simple type theory of Appendix A?

---

### Appendix C: PESCA — A Proof Editor for Sequent Calculus (pp. 235–243)

**Summary:** Written by Aarne Ranta, this appendix describes PESCA, a Haskell-implemented interactive proof editor and automatic theorem prover for sequent calculi that exploits top-down (root-first) determinacy of the rules to guide proof search, and documents its commands, axiom-file format, and internal architecture. : [[Natural-Deduction-and-the-Inversion-Principle|Link1]], [[Quantifiers-and-First-Order-Proof-Theory|Link2]], [[Sequent-Calculus-Foundations|Link3]], [[The-Sequent-Calculus-Natural-Deduction-Isomorphism|Link4]]

**Key Definitions & Concepts by Section:**
- **C.1 Introduction** — top-down determinacy ("given a conclusion and a rule, the premisses are determined") as the property enabling PESCA's proof search, adapted from the type-theoretic proof editor ALF; calculi supported: shared multiset contexts, no structural rules, single- or multi-formula succedents.
- **C.2 Two Example Sessions** — worked proof-editor sessions for disjunction commutativity ($A\vee B\Rightarrow B\vee A$) and the quantifier-switch law ($(\exists y)(\forall x)C(x,y)\Rightarrow(\forall x)(\exists y)C(x,y)$); subgoal numbering by digit sequences; rule refinement, instantiation of parameters, and translation of completed proofs to $\LaTeX$ sequent-calculus and natural-deduction form.
- **C.3 Some Commands** — core commands: refine, instantiate, try (automatic proof search, brute-force but terminating), new goal, undo, show subgoals, applicable rules, change calculus, read nonlogical-axiom file, print proof as $\LaTeX$ sequent calculus / natural deduction.
- **C.4 Axiom Files** — axiom formulas restricted to implications with conjunctions of atoms on the left and disjunctions of atoms on the right (either side possibly empty) so that cut elimination is preserved; worked example: lattice-theory axioms converted into sequent-calculus rules.
- **C.5 On the Implementation** — abstract syntax as Haskell data types (`Sequent`, `Formula`, `Term`, `Proof`, `AbsRule`); rule type expressing top-down determinacy; parsing/printing via the top-down combinator method (Wadler 1985); predefined calculi compiled in (not file-loadable, unlike nonlogical axioms); `replace` and `applicableRules` as the core proof-search primitives; translation to natural deduction (for $G3i$, $G3ip$ only).

**Key Questions:**
1. What is "top-down determinacy" and why is it essential both for PESCA's refinement-based proof search and for restricting which sequent calculi it can support?
2. Why must nonlogical axioms be restricted to Horn-like implications (conjunctions of atoms implying disjunctions of atoms) for PESCA's axiom-file mechanism to preserve cut elimination?
