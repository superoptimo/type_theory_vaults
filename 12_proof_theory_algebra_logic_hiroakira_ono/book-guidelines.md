# Proof Theory and Algebra in Logic — Guidelines

## Header

**Title:** Proof Theory and Algebra in Logic
**Author(s):** Hiroakira Ono
**Publication:** Springer, Short Textbooks in Logic series, 2019 (ISBN 978-981-13-7996-3)

**Brief Summary:**
An introductory textbook covering two complementary approaches to nonclassical logic: proof theory (Part I), built on Gentzen-style sequent systems, cut elimination, and the logical properties derivable from it (decidability, the disjunction property, Craig interpolation, Glivenko's theorem), and algebra (Part II), built on lattices, Boolean and Heyting algebras, residuated structures, and modal algebras. The book's organizing idea is that these two branches — syntactic/combinatorial versus semantic/structural — are independent but deeply interrelated ways of studying the same nonclassical logics (modal, superintuitionistic, substructural, many-valued), and that results in one often translate into results in the other.

**Intent of the Author:**
Ono designed the book so Part I and Part II can be read independently — a reader may start directly from Part II to learn algebraic logic and universal algebra with examples from nonclassical logic. He aims to keep mathematical prerequisites minimal while still reaching genuine research-level results (e.g. Maksimova's classification of the seven superintuitionistic logics with Craig interpolation), so the book doubles as an introduction to modal, many-valued, superintuitionistic, and substructural logics.

---

## Topic List

1. **Sequent Calculi for Classical and Intuitionistic Logic** : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
   - Sequents, antecedents and succedents, initial sequents and inference rules
   - The system LK for classical logic : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
   - The system LJ for intuitionistic logic as a single-succedent restriction of LK : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
   - Active, principal, and side formulas
   - Multiset presentation of sequents and redundancy of exchange rules
   - The invertible system LK* and proof search trees : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
   - Soundness and semantic completeness of LK via LK* : [[Lattices-and-Boolean-Algebras|Link]]
   - Corresponding formula of a sequent : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
   - Hilbert-style systems HK and HJ and their equivalence with LK and LJ

2. **Cut Elimination** : [[Cut-Elimination|Link]]
   - The cut rule as a formalization of transitive deductive reasoning
   - Grade and height of a cut application
   - The extended cut rule (e-cut) and why contraction defeats ordinary cut elimination : [[Cut-Elimination|Link]]
   - Gentzen's mix rule compared to extended cut
   - Double induction on grade and height : [[Cut-Elimination|Link]]
   - Cut elimination for LK, LJ, and normal modal sequent systems : [[Modal-Logic-Proof-Theory|Link]]
   - The subformula property as a consequence of cut elimination : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]
   - Conservative extension results via cut elimination : [[Subformula-Property|Link]]

3. **Proof-Theoretic Consequences of Cut Elimination** : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]
   - Decidability via backward proof search and loop-checking : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]
   - n-reduced sequents and reduced proofs
   - The disjunction property of intuitionistic logic : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link1]], [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link2]], [[Modal-Algebras-and-Kripke-Semantics|Link3]]
   - Halldén-completeness : [[Residuated-Lattices-and-FL-Algebras|Link]]
   - Craig's interpolation property and post- and pre-interpolants : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]
   - Maehara's method for proving interpolation from cut-free proofs
   - Uniform interpolation property : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link1]], [[Subformula-Property|Link2]]
   - Glivenko's theorem relating classical and intuitionistic provability : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]

4. **Modal Logic Proof Theory** : [[Modal-Logic-Proof-Theory|Link]]
   - Normal modal logics as extensions of K by axiom schemes D, T, 4, B, 5
   - Sequent rules for the modal operator and the systems GK, GKT, GK4, GS4, GS5
   - Cut elimination for standard modal sequent systems : [[Modal-Logic-Proof-Theory|Link]]
   - Failure of cut elimination for GS5 and the axiom B : [[Cut-Elimination|Link1]], [[Modal-Logic-Proof-Theory|Link2]]
   - Analytic cut property as a weaker substitute for cut elimination
   - Decidability and Craig interpolation for modal logics via cut elimination or analytic cut

5. **Substructural Logics: Proof-Theoretic View** : [[Substructural-Logics-Proof-Theoretic-View|Link]]
   - Structural rules (exchange, contraction, weakening) as governing reuse of assumptions
   - Fusion (multiplicative conjunction) versus additive conjunction : [[Substructural-Logics-Proof-Theoretic-View|Link]]
   - Left- and right-division (residuation) replacing implication when exchange is absent
   - The system FL (full Lambek calculus) and its extensions FLe, FLw, FLc, FLew, FLec
   - Cut elimination and decidability for basic substructural logics : [[Substructural-Logics-Proof-Theoretic-View|Link]]
   - Undecidability results for FLc and for the deducibility problem of FLe
   - Involutive substructural logics and the law of double negation : [[Substructural-Logics-Proof-Theoretic-View|Link]]
   - Substructural logics as generalizing Lambek calculus, linear logic, relevant logics, fuzzy logics, Łukasiewicz's many-valued logics, logics without contraction, and Johansson's minimal logic

6. **Deducibility, Deduction Theorems, and Axiomatic Extensions** : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link]]
   - Deducibility of a sequent or formula from a set of assumptions
   - Consequence relations: finitarity and substitution invariance : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link]]
   - The classical deduction theorem : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link1]], [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link2]]
   - Local deduction theorems for substructural and modal logics : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link]]
   - Axiomatic extensions and logics defined as substitution- and deducibility-closed sets of formulas
   - Superintuitionistic, substructural, and normal modal logics as logics over Int, FL, and K respectively

7. **Lattices and Boolean Algebras** : [[Lattices-and-Boolean-Algebras|Link]]
   - Partial orders, chains, and lattices defined by join and meet : [[Lattices-and-Boolean-Algebras|Link1]], [[Residuated-Lattices-and-FL-Algebras|Link2]]
   - Distributive lattices and the distributive law : [[Lattices-and-Boolean-Algebras|Link1]], [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link2]]
   - Complete lattices : [[Lattices-and-Boolean-Algebras|Link]]
   - Subalgebras, homomorphisms, and direct products : [[Lattices-and-Boolean-Algebras|Link]]
   - Boolean algebras via the law of residuation and the law of double negation
   - Stone's representation theorem for Boolean algebras : [[Lattices-and-Boolean-Algebras|Link]]
   - Algebraic completeness of classical logic : [[Lattices-and-Boolean-Algebras|Link]]

8. **Many-Valued Chains** : [[Many-Valued-Chains|Link]]
   - Extending two-valued semantics to chains with residuated implication
   - Gödel chains and Gödel logics
   - Łukasiewicz chains, Łukasiewicz implication, and fusion over the unit interval
   - Inclusion relations among finite-valued Gödel and Łukasiewicz logics
   - The Gödel-Dummett logic as the intersection of all finite Gödel logics
   - Maximality of prime-valued Łukasiewicz logics

9. **Heyting Algebras and Algebraic Logic** : [[Heyting-Algebras-and-Algebraic-Logic|Link]]
   - Heyting algebras as Boolean algebras without the law of double negation : [[Heyting-Algebras-and-Algebraic-Logic|Link1]], [[Modal-Algebras-and-Kripke-Semantics|Link2]]
   - Finite distributive lattices as Heyting algebras : [[Lattices-and-Boolean-Algebras|Link1]], [[Residuated-Lattices-and-FL-Algebras|Link2]]
   - The Lindenbaum-Tarski algebra and algebraic completeness of intuitionistic logic : [[Heyting-Algebras-and-Algebraic-Logic|Link1]], [[Lattices-and-Boolean-Algebras|Link2]]
   - Locally finite algebras and the Rieger-Nishimura lattice : [[Heyting-Algebras-and-Algebraic-Logic|Link]]
   - The finite embeddability property and the finite model property : [[Heyting-Algebras-and-Algebraic-Logic|Link1]], [[Modal-Algebras-and-Kripke-Semantics|Link2]]
   - Harrop's theorem linking finite axiomatizability and the finite model property to decidability
   - Filters, prime filters, ultrafilters, and the prime filter theorem
   - Canonical extensions and Stone's representation theorem for Heyting algebras : [[Heyting-Algebras-and-Algebraic-Logic|Link1]], [[Lattices-and-Boolean-Algebras|Link2]], [[Modal-Algebras-and-Kripke-Semantics|Link3]], [[Gödel-Translation|Link4]]

10. **Logics and Varieties** : [[Logics-and-Varieties|Link]]
    - The lattice of superintuitionistic logics under set inclusion : [[Modal-Algebras-and-Kripke-Semantics|Link1]], [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link2]]
    - Classical logic as the second-greatest consistent superintuitionistic logic
    - Varieties as classes of algebras closed under homomorphic images, subalgebras, and direct products : [[Lattices-and-Boolean-Algebras|Link]]
    - Duality between subvarieties of Heyting algebras and superintuitionistic logics
    - Equational classes and Birkhoff's theorem
    - Subdirect representation theorem and subdirectly irreducible algebras : [[Logics-and-Varieties|Link]]
    - Halldén-completeness characterized by well-connected and subdirectly irreducible algebras
    - Algebraic characterization of the disjunction property : [[Logics-and-Varieties|Link]]
    - Classification of superintuitionistic logics with Craig's interpolation property : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]

11. **Residuated Lattices and FL-Algebras** : [[Residuated-Lattices-and-FL-Algebras|Link]]
    - Semigroups, monoids, and partially ordered monoids : [[Residuated-Lattices-and-FL-Algebras|Link]]
    - The general law of residuation and left and right residuals
    - Residuated lattices and full Lambek (FL-) algebras : [[Residuated-Lattices-and-FL-Algebras|Link]]
    - Integral, commutative, and contractive residuated lattices : [[Residuated-Lattices-and-FL-Algebras|Link]]
    - Algebraic completeness of substructural logics : [[Lattices-and-Boolean-Algebras|Link]]
    - Triangular norms and left-continuity
    - Mathematical fuzzy logic: basic logic BL and monoidal t-norm logic MTL
    - Gödel-Dummett logic, infinite-valued Łukasiewicz logic, and product logic as t-norm logics

12. **Modal Algebras and Kripke Semantics** : [[Modal-Algebras-and-Kripke-Semantics|Link]]
    - Modal algebras as Boolean algebras with a normal unary operator : [[Modal-Algebras-and-Kripke-Semantics|Link]]
    - Algebraic inequalities corresponding to axiom schemes D, T, 4, B, 5
    - Finite embeddability property and finite model property of S4-algebras : [[Modal-Algebras-and-Kripke-Semantics|Link]]
    - Jónsson-Tarski theorem as the modal analogue of Stone's representation theorem : [[Lattices-and-Boolean-Algebras|Link]]
    - Dual frames, canonical extensions, and canonical embeddings : [[Modal-Algebras-and-Kripke-Semantics|Link]]
    - Kripke frames and valuations for modal and superintuitionistic logics : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
    - Kripke completeness and canonical modal logics : [[Lattices-and-Boolean-Algebras|Link]]
    - Existence of Kripke-incomplete modal logics : [[Lattices-and-Boolean-Algebras|Link]]

13. **Gödel Translation** : [[Gödel-Translation|Link]]
    - Translating intuitionistic formulas into modal formulas via necessitation
    - Open elements of an S4-algebra and the induced Heyting algebra
    - Equivalence of intuitionistic provability and S4-provability of the translation
    - Extension of the embedding to logics between S4 and Grz, and to classical logic and S5 : [[Many-Valued-Chains|Link]]

---

## Chapter Summaries

### Chapter 1: Sequent Systems (pp. 3–22)

**Summary:** Introduces basic notions of formulas, proofs, and provability, then presents the sequent systems LK (classical logic) and LJ (intuitionistic logic), proving soundness and semantic completeness of LK via the invertible auxiliary system LK*. : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Prologue** — subformula and proper subformula, formula occurrences, Hilbert-style system HK for classical logic (axiom schemes for weakening, contraction, exchange, and double negation), assignment, tautology, two-valued truth tables
- **1.2 Sequent Systems LK for Classical Logic** — sequent $\Gamma \Rightarrow \Delta$, antecedent/succedent, initial sequent, active/principal/side formula, left and right rules, cut rule, structural rules (exchange, contraction, weakening), proof and provability, multiset presentation, corresponding formula of a sequent, the invertible system $LK^*$, proof search tree, elementary sequent, soundness and completeness of $LK^*$ : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
- **1.3 Completeness and Cut Elimination** — completeness and cut elimination theorem for LK (Theorem 1.11), decidability corollary : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
- **1.4 Sequent System LJ for Intuitionistic Logic** — intuitionist's/constructive point of view, disjunction property (informal), single-succedent sequents, multi-succedent variant $LJ_m$ : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]

**Key Questions:**
1. Why does restricting LK's succedents to at most one formula (yielding LJ) correspond exactly to the loss of the law of excluded middle and double negation, rather than to some ad hoc axiom deletion?
2. How does the invertibility of every rule in $LK^*$ let Gentzen-style completeness be proved by pure proof search, without any semantic argument beyond soundness of initial sequents?
3. What is the difference between a sequent being "provable" and its "corresponding formula" being provable, and why does this distinction matter once succedents can hold more than one formula?

---

### Chapter 2: Cut Elimination for Sequent Systems (pp. 23–34)

**Summary:** Gives a general syntactic proof of cut elimination for LJ and LK, using the extended cut rule (e-cut) and a double induction on grade and height, and derives the subformula property. : [[Modal-Logic-Proof-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Basic Idea** — grade and height of a cut application, the deadlock case caused by contraction acting on the cut formula
- **2.2 Cut Elimination** — extended cut rule (e-cut), the well-ordering on (grade, height) pairs, the four-case analysis (initial sequent, structural rule, non-principal logical rule, principal logical rule on both sides), Gentzen's mix rule (compared in Remark 2.1) : [[Cut-Elimination|Link]]
- **2.3 Subformula Property** — subformula property of a proof/sequent system, conservative extension : [[Subformula-Property|Link]]

**Key Questions:**
1. Why is a single application of ordinary cut rule not always reducible by one step, forcing the introduction of the more general e-cut rule?
2. In the "trouble case" where the cut formula is the principal formula of a contraction, how does e-cut's ability to delete only *some* occurrences of the cut formula resolve the impasse that ordinary cut could not?
3. What logical fact about Hilbert-style proofs (where implication plays a "special and multiple role") does the subformula property make visible by contrast?

---

### Chapter 3: Proof-Theoretic Analysis of Logical Properties (pp. 35–46)

**Summary:** Shows how cut elimination and the subformula property yield decidability, the disjunction property, and Craig's interpolation property for classical and intuitionistic logic, and gives a syntactic proof of Glivenko's theorem via induction on proof length even in the presence of cut.

**Key Definitions & Concepts by Section:**
- **3.1 Decidability of Intuitionistic Logic** — decision problem, decidable/undecidable logic, n-reduced sequent, 1-reduced contraction, redundancy in a proof, reduced proof : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link1]], [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link2]]
- **3.2 Disjunction Property** — disjunction property, Halldén-completeness : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]
- **3.3 Craig's Interpolation Property** — interpolant, Craig's interpolation property (CIP), post-interpolant and pre-interpolant, uniform interpolation property, Maehara's method, partition of a sequent : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]
- **3.4 Glivenko's Theorem** — Glivenko's theorem relating classical and intuitionistic provability via double negation : [[Proof-Theoretic-Consequences-of-Cut-Elimination|Link]]

**Key Questions:**
1. Why does the presence of contraction rules (rather than the presence of cut) create the main obstacle to a naive decision procedure for LJ, and how does the notion of a "reduced" proof overcome it?
2. How does Maehara's syntactic proof of interpolation via cut-free proofs differ in generality from the semantic (two-valued) proof for classical logic, and why does this matter for extending CIP to other logics?
3. What does Glivenko's theorem say about the relative deductive strength of intuitionistic logic compared to classical logic, despite intuitionistic logic being strictly weaker?

---

### Chapter 4: Modal and Substructural Logics (pp. 47–60)

**Summary:** Introduces standard cut-free sequent systems for normal modal logics K, D, T, 4, B, S4, S5 (noting cut elimination fails for S5, replaced by the analytic cut property), then examines the role of each structural rule individually, leading to the sequent system FL and its extensions as the foundation of substructural logics. : [[Modal-Logic-Proof-Theory|Link1]], [[Substructural-Logics-Proof-Theoretic-View|Link2]]

**Key Definitions & Concepts by Section:**
- **4.1 Standard Sequent Systems for Normal Modal Logics** — axiom schemes D, T, 4, B, 5, normal extension of K, modal sequent rules (K), (D), (T), (4), (S4), (S5), systems GK–GS5, analytic cut, analytic cut property : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
- **4.2 Roles of Structural Rules** — exchange, contraction, and weakening rules restated for single-succedent sequents, fusion (multiplicative conjunction) vs. additive conjunction, associativity of fusion, resource-based reading of fusion : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link1]], [[Substructural-Logics-Proof-Theoretic-View|Link2]], [[Lattices-and-Boolean-Algebras|Link3]]
- **4.3 Sequent Systems for Basic Substructural Logics** — the system FL (full Lambek calculus), left- and right-division (residuation) \ and /, logical constants 0 and 1, systems FLe, FLw, FLc, FLew, FLec, involutive substructural logics (InFLe, InFLew, InFLec) : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]

**Key Questions:**
1. Why does the modal axiom B specifically break cut elimination for S5, and how does "analytic cut" recover enough of the subformula property to still derive decidability and interpolation?
2. In what precise sense does fusion differ from conjunction once contraction and weakening are absent, and how does the "$25 resource" example make this difference intuitive?
3. Why must a substructural logic lacking exchange introduce two distinct implication-like connectives (left- and right-division) instead of one?

---

### Chapter 5: Deducibility and Axiomatic Extensions (pp. 61–73)

**Summary:** Defines deducibility from a set of assumptions as an extension of provability, proves deduction theorems (full for classical/intuitionistic logic, local for substructural and modal logics), and uses deducibility to give a precise, uniform definition of "a logic over L" as an axiomatic extension, bridging proof theory (Part I) and algebra (Part II). : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Deducibility and Deduction Theorem** — deduction from a set S, deducibility relation, consequence relation, finitary/compact and substitution-invariant (structural) consequence relations, deduction theorem for classical and intuitionistic logic : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link]]
- **5.2 Local Deduction Theorems** — local deduction theorem for FLe, FLec, FLew, and normal extensions of K, deducibility problem, undecidability of the deducibility problem of FLe : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link]]
- **5.3 Axiomatic Extensions** — axiomatic extension of a logic, logic over Int (superintuitionistic logic), finitely axiomatizable logic, logic over a general logic L : [[Deducibility-Deduction-Theorems-and-Axiomatic-Extensions|Link]]
- **5.4 Framework for Substructural Logics and Modal Logics** — closure under modus ponens/adjunction/necessitation as explicit alternative characterizations of logics over Int, FLe, FL, and K : [[Substructural-Logics-Proof-Theoretic-View|Link]]
- **5.5 A View of Substructural Logics** — Lambek calculus, linear logic, relevant logics, logics without contraction, fuzzy logics, Łukasiewicz's many-valued logics, Johansson's minimal logic, superintuitionistic logics (historical survey) : [[Substructural-Logics-Proof-Theoretic-View|Link]]

**Key Questions:**
1. Why does the standard deduction theorem fail for FLe, and what does the "local" version — quantifying over some finite power $m$ — recover in its place?
2. How does defining "a logic over L" via closure under substitution and deducibility (rather than via a fixed proof system) allow later chapters to ask genuinely general questions like "how many logics are there over Int"?
3. What common structural feature — absence of a specific structural rule — unifies Łukasiewicz's many-valued logics, relevant logics, and linear logic as instances of substructural logics, despite their very different historical motivations?

---

### Chapter 6: From Algebra to Logic (pp. 77–95)

**Summary:** Develops the basic algebraic toolkit — lattices, Boolean algebras, subalgebras/homomorphisms/direct products — proves algebraic completeness of classical logic, and shows two distinct ways of generalizing two-valued semantics to many-valued chains depending on which form of residuation is preserved. : [[Heyting-Algebras-and-Algebraic-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Lattices and Boolean Algebras** — partial order, total order/chain, lattice (join and meet), distributive lattice, complete lattice, Boolean algebra (law of residuation plus law of double negation), two-valued Boolean algebra 2, degenerate Boolean algebra : [[Lattices-and-Boolean-Algebras|Link]]
- **6.2 Subalgebras, Homomorphisms and Direct Products** — language of algebras, subalgebra, homomorphism, embedding, homomorphic image, isomorphism, direct product : [[Lattices-and-Boolean-Algebras|Link]]
- **6.3 Representations of Boolean Algebras** — powerset Boolean algebra, finite vs. infinite Boolean algebras, Stone's representation theorem for Boolean algebras : [[Lattices-and-Boolean-Algebras|Link1]], [[Modal-Algebras-and-Kripke-Semantics|Link2]]
- **6.4 Algebraic Completeness of Classical Logic** — assignment/valuation on an algebra, validity of a formula in an algebra, algebraic completeness theorem : [[Lattices-and-Boolean-Algebras|Link]]
- **6.5 Many-Valued Chains and the Law of Residuation** — Gödel chains and Gödel logics, Gödel-Dummett logic GD, Łukasiewicz chains and Łukasiewicz implication, fusion on the standard Łukasiewicz chain, residuated algebraic structure : [[Many-Valued-Chains|Link]]

**Key Questions:**
1. Why must the residuation law force $a \to b = 1$ when $a \le b$ and $a \to b = b$ otherwise on any chain — and how does this single fact generate the entire definition of Gödel implication?
2. What is lost and what is gained by choosing Łukasiewicz implication (preserving double negation, sacrificing residuation with $\wedge$) over Gödel implication (the reverse trade-off)?
3. Why does $L(\mathrm{G}_{m+1}) \subsetneq L(\mathrm{G}_m)$ hold strictly, and what role does the formula sequence $\pi_n$ play in proving this?

---

### Chapter 7: Basics of Algebraic Logic (pp. 97–111)

**Summary:** Defines Heyting algebras, proves algebraic completeness of intuitionistic logic via the Lindenbaum-Tarski algebra, shows intuitionistic logic has the finite model property (though no single finite algebra suffices), and gives Stone's representation theorem for Heyting algebras via canonical extensions built from prime filters. : [[Heyting-Algebras-and-Algebraic-Logic|Link1]], [[Lattices-and-Boolean-Algebras|Link2]], [[Logics-and-Varieties|Link3]]

**Key Definitions & Concepts by Section:**
- **7.1 Heyting Algebras** — Heyting algebra (law of residuation without double negation), Gödel algebra (prelinearity), finite distributive lattices as Heyting algebras : [[Gödel-Translation|Link1]], [[Heyting-Algebras-and-Algebraic-Logic|Link2]]
- **7.2 Lindenbaum-Tarski Algebras** — logical equivalence $\equiv$, congruence and full invariance, equivalence classes, Lindenbaum-Tarski algebra $F_{\mathrm{Int}}$, canonical assignment : [[Heyting-Algebras-and-Algebraic-Logic|Link]]
- **7.3 Locally Finite Algebras** — characterization of a logic by a class of algebras, finite model property (FMP), subalgebra generated by a set, locally finite algebra, Rieger-Nishimura lattice : [[Heyting-Algebras-and-Algebraic-Logic|Link]]
- **7.4 Finite Embeddability Property and Finite Model Property** — partial algebra, finite embeddability property, Harrop's theorem (decidability from finite axiomatizability plus FMP) : [[Heyting-Algebras-and-Algebraic-Logic|Link1]], [[Modal-Algebras-and-Kripke-Semantics|Link2]]
- **7.5 Canonical Extensions of Heyting Algebras** — upward closed subset, dual Heyting algebra $U(S)$ of a poset, filter, prime/maximal/ultrafilter, prime filter theorem, dual intuitionistic frame $D(A)$, canonical extension $A^\delta$, canonical embedding : [[Heyting-Algebras-and-Algebraic-Logic|Link]]

**Key Questions:**
1. Why can no single finite Heyting algebra characterize intuitionistic logic, even though intuitionistic logic does have the finite model property?
2. How does the finite embeddability property of Heyting algebras let a *partial* algebra — built just from the subformulas of one non-provable formula — be completed into a genuine finite countermodel?
3. What is the structural analogy between Stone's representation theorem for Heyting algebras (via prime filters and upward-closed sets) and the earlier representation theorem for Boolean algebras (via powersets)?

---

### Chapter 8: Logics and Varieties (pp. 113–128)

**Summary:** Develops the universal-algebraic dictionary between superintuitionistic logics and subvarieties of Heyting algebras — via Birkhoff's equational-class theorem and the subdirect representation theorem — and uses it to give algebraic characterizations of Halldén-completeness and the disjunction property, culminating in Maksimova's classification of the logics with Craig interpolation. : [[Logics-and-Varieties|Link]]

**Key Definitions & Concepts by Section:**
- **8.1 Lattice Structure of Superintuitionistic Logics** — SUP (lattice of all superintuitionistic logics), consistent/inconsistent logic, join $\sqcup$ of logics, finitely axiomatizable logic : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link]]
- **8.2 The Variety HA of All Heyting Algebras** — logic characterized by an algebra/class of algebras, variety (closure under H, S, P), $L$-Heyting algebra, free algebra and universal mapping property : [[Gödel-Translation|Link1]], [[Heyting-Algebras-and-Algebraic-Logic|Link2]]
- **8.3 Subvarieties of HA and Superintuitionistic Logics** — variety generated by a class, subvariety, order-reversing (dual) lattice isomorphism between SUP and subvarieties of HA, equational class, term, equation, Birkhoff's theorem : [[Sequent-Calculi-for-Classical-and-Intuitionistic-Logic|Link1]], [[Modal-Algebras-and-Kripke-Semantics|Link2]]
- **8.4 Subdirect Representation Theorem** — subdirect product, subdirectly irreducible (s.i.) algebra, rooted poset, three-valued Gödel logic as the second-greatest consistent superintuitionistic logic : [[Lattices-and-Boolean-Algebras|Link]]
- **8.5 Algebraic Aspects of Logical Properties** — well-connected algebra, meet irreducible logic, algebraic characterization of Halldén-completeness, algebraic characterization of the disjunction property, Maksimova's classification of the seven logics with CIP : [[Logics-and-Varieties|Link]]

**Key Questions:**
1. Why does Birkhoff's theorem (variety = equational class) justify replacing the algebraic, order-theoretic condition "law of residuation" with two explicit inequations when proving HA is a variety?
2. How does the equivalence of "Halldén-complete," "characterized by a subdirectly irreducible algebra," and "meet irreducible in SUP" connect a syntactic property, a local algebraic property, and a global lattice-theoretic property of the same logic?
3. What makes the algebraic route to proving the disjunction property (via well-connected algebras and free algebras) more broadly applicable than the proof-theoretic route via cut elimination from Chapter 3?

---

### Chapter 9: Residuated Structures (pp. 129–138)

**Summary:** Generalizes residuation beyond Heyting algebras to residuated lattices and full Lambek (FL-) algebras — the exact algebraic counterparts of substructural logics — then specializes to residuated lattices over the unit interval, connecting them to triangular norms and Hájek's mathematical fuzzy logic.

**Key Definitions & Concepts by Section:**
- **9.1 Residuated Lattices and FL-Algebras** — semigroup, monoid, partially ordered semigroup/monoid, residuated p.o. semigroup/monoid, left and right residual, residuated lattice, integral and contractive residuated lattices : [[Residuated-Lattices-and-FL-Algebras|Link]]
- **9.2 FL-Algebras and Substructural Logics** — full Lambek algebra (FL-algebra), FLe-, FLw-, FLc-algebras, algebraic completeness of basic substructural logics, subvarieties of FL and substructural logics, fusion as an explicit presentation of the comma in a sequent : [[Heyting-Algebras-and-Algebraic-Logic|Link1]], [[Lattices-and-Boolean-Algebras|Link2]]
- **9.3 Residuations Over the Unit Interval** — triangular norm (t-norm), left-continuity and right-continuity, residuated complete lattice-ordered semigroup, product implication, basic logic BL, monoidal t-norm logic MTL, product logic $\Pi$ : [[Residuated-Lattices-and-FL-Algebras|Link]]

**Key Questions:**
1. Why is the notion of "residuated" defined relative to an arbitrary monoid operation rather than fixed to conjunction, and how does this let both Heyting algebras and Łukasiewicz chains count as residuated structures?
2. What does Lemma 9.4's equivalence between "residuated" and "left-continuous" reveal about which t-norms can serve as a basis for a genuine implication connective in fuzzy logic?
3. How does the algebraic notion of fusion as "an explicit presentation of comma" retroactively explain why substructural logics needed a new connective once structural rules were removed (Chapter 4)?

---

### Chapter 10: Modal Algebras (pp. 139–149)

**Summary:** Introduces modal algebras as Boolean algebras with a normal unary operator, proves the Jónsson-Tarski representation theorem (the modal analogue of Stone's theorem), shows how Kripke frames and algebraic semantics for modal and superintuitionistic logics correspond via dual frames and canonical extensions, and closes with an algebraic proof that the Gödel translation embeds intuitionistic logic into S4. : [[Modal-Algebras-and-Kripke-Semantics|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 Modal Algebras** — modal algebra, algebraic inequalities for D, T, 4, B, 5 (and their duals), L-modal algebra, finite embeddability property of S4-algebras : [[Modal-Algebras-and-Kripke-Semantics|Link]]
- **10.2 Canonical Extensions and Jónsson-Tarski Theorem** — modal frame, dual modal algebra of a frame, dual modal frame of an algebra, canonical extension $A^\delta$ of a modal algebra, Jónsson-Tarski theorem : [[Modal-Algebras-and-Kripke-Semantics|Link]]
- **10.3 Kripke Semantics from Algebraic Viewpoint** — Kripke frame, valuation, truth relation, Kripke model, validity in a Kripke frame, Kripke completeness, canonical modal logic, Kripke-incomplete modal logics : [[Modal-Algebras-and-Kripke-Semantics|Link]]
- **10.4 Gödel Translation** — Gödel (Gödel-McKinsey-Tarski) translation $T$, open element of an S4-algebra, the Heyting algebra $H_A$ of open elements, embedding of Int into S4 (and of Cl into S5) : [[Gödel-Translation|Link]]

**Key Questions:**
1. How does the Jónsson-Tarski theorem's construction (dual frame, then dual algebra of that frame) mirror the Stone representation construction for Heyting algebras, and what extra structure (the accessibility relation $R$) does modality require?
2. Why does having the finite model property guarantee Kripke completeness (Corollary 10.7), yet Kripke-incomplete modal logics still exist — what does this say about logics without FMP?
3. In the Gödel translation, why must "open elements" (where $a = \Box a$) be singled out as the image of Heyting algebra elements, and how does this correspond to the modal reading of intuitionistic truth as "provable/necessary truth"?
