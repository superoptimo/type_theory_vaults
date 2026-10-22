# A Focused Sequent Calculus Framework for Proof-Search in Pure Type Systems — Guidelines

## Header

**Title:** A Focused Sequent Calculus Framework for Proof-Search in Pure Type Systems
**Author(s):** Stéphane Lengrand (CNRS, École Polytechnique), Roy Dyckhoff (University of St Andrews), James McKinna (Radboud University Nijmegen)
**Publication:** Logical Methods in Computer Science, Vol. 7 (1:6) 2011, pp. 1–35. Submitted Oct. 3, 2009; published Mar. 22, 2011 (the source folder is labelled 2010).

**Brief Summary:**
The paper defines Pure Type Sequent Calculi (PTSC), a permutation-free, focused sequent-calculus presentation (after Herbelin's LJT) of every Pure Type System, with proof-terms in the explicit-substitution calculus $\overline{\lambda}$. It proves confluence, subject reduction, logical equivalence with the corresponding PTS and equivalence of strong normalisation. It then derives a syntax-directed proof-search system PS and extends the syntax with explicitly scoped meta-variables (PTSC$\alpha$) to form a proof-enumeration system PE, which represents partial proof-terms, delayed sub-goals and unification constraints. PE models tactics such as Coq's `apply`, inhabitant enumeration and higher-order unification in one framework, and removes the $r$-splitting of Dowek's method.

**Intent of the Author:**
The authors want a theoretical basis in which proof-search steps are simply root-first applications of the typing rules, so that the output of search is correct by construction and need not be re-type-checked. They also want the framework to be a neutral operational semantics for studying search strategies, from fully automated to interactive proof construction.

---

## Topic List

1. **Pure Type Systems and the Lambda Cube** : [[Pure-Type-Systems-and-the-Lambda-Cube|Link]]
   - Sorts, axioms and rules
   - Systems F, F$\omega$, $\lambda\Pi$ and the Calculus of Constructions
   - Natural deduction presentation : [[Pure-Type-Systems-and-the-Lambda-Cube|Link]]
   - Strong normalisation of a PTS : [[Pure-Type-Systems-and-the-Lambda-Cube|Link]]
2. **Focused Sequent Calculus and Permutation-Free Proof-Search** : [[Focused-Sequent-Calculus-and-Permutation-Free-Proof-Search|Link]]
   - Herbelin's calculus LJT : [[Focused-Sequent-Calculus-and-Permutation-Free-Proof-Search|Link]]
   - Gentzen-style calculi such as G3
   - Focusing and the stoup
   - Uniform proofs and goal-directed search
   - Don't-care versus don't-know non-determinism : [[Proof-Search-System-PS|Link1]], [[Focused-Sequent-Calculus-and-Permutation-Free-Proof-Search|Link2]]
3. **Pure Type Sequent Calculi** : [[Pure-Type-Sequent-Calculi|Link]]
   - Terms and lists
   - Explicit substitutions
   - Sequent typing rules including left and right introduction of $\Pi$
   - Cut rules and environment manipulation
   - Conversion rules for term and list typing
4. **Operational Semantics and Confluence** : [[Operational-Semantics-and-Confluence|Link]]
   - Rewrite systems B and x$'$ : [[Operational-Semantics-and-Confluence|Link1]], [[Pure-Type-Systems-and-the-Lambda-Cube|Link2]], [[Proof-Search-System-PS|Link3]]
   - Termination of x$'$ by lexicographic path ordering
   - Translations between sequent calculus and $\lambda$-terms
   - Confluence by simulation : [[Operational-Semantics-and-Confluence|Link]]
5. **Meta-Theory of PTSC** : [[Meta-Theory-of-PTSC|Link]]
   - Weakening and thinning
   - Subject reduction
   - Preservation of typing in both directions
   - Equivalence of strong normalisation with the PTS : [[Meta-Theory-of-PTSC|Link1]], [[Pure-Type-Systems-and-the-Lambda-Cube|Link2]]
6. **Proof-Search System PS** : [[Proof-Search-System-PS|Link]]
   - Syntax-directed rules with built-in conversion : [[Proof-Search-System-PS|Link]]
   - Quasi-normal forms
   - Soundness and completeness : [[Proof-Enumeration-System-PE|Link]]
   - Sources of non-determinism in search : [[Proof-Search-System-PS|Link]]
   - Relation to the constructive engine
7. **Meta-Variables and Partial Proof-Terms** : [[Meta-Variables-and-Partial-Proof-Terms|Link]]
   - Scoped meta-variables for terms and lists : [[Meta-Variables-and-Partial-Proof-Terms|Link1]], [[Operational-Semantics-and-Confluence|Link2]]
   - Meta-variables in the style of CRS versus ERS : [[Operational-Semantics-and-Confluence|Link1]], [[Meta-Variables-and-Partial-Proof-Terms|Link2]]
   - Goal environments with goals and constraints : [[Meta-Variables-and-Partial-Proof-Terms|Link]]
   - Substitutions and solutions
   - Meta-variables as higher-order variables
8. **Proof Enumeration System PE** : [[Proof-Enumeration-System-PE|Link]]
   - Claim rules and delayed sub-goals
   - Unification constraints from the axiom rule
   - Solving goals in any order
   - Soundness and completeness of PE : [[Proof-Enumeration-System-PE|Link]]
   - Avoiding $r$-splitting : [[Proof-Enumeration-System-PE|Link]]
9. **Unification and Type Inhabitation** : [[Unification-and-Type-Inhabitation|Link]]
   - Proof-search and unification as a single process : [[Proof-Search-System-PS|Link1]], [[Proof-Enumeration-System-PE|Link2]]
   - Higher-order unification
   - Type inhabitant enumeration : [[Meta-Theory-of-PTSC|Link1]], [[Unification-and-Type-Inhabitation|Link2]]
   - Comparison with Dowek and Muñoz : [[Meta-Variables-and-Partial-Proof-Terms|Link]]
10. **Proof-Search Strategies and Tactics** : [[Proof-Search-Strategies-and-Tactics|Link]]
    - Eager and lazy treatment of sub-goals
    - Coq tactics intro and apply
    - Interactive proof construction
    - Incomplete proofs in the work of McBride, Jojgov and Delahaye
11. **Worked Example in System F** : [[Worked-Example-in-System-F|Link]]
    - Commutativity of conjunction
    - Head-variable choice from constraints : [[Unification-and-Type-Inhabitation|Link]]

---

## Chapter Summaries

Chapter boundaries are the paper's own numbered sections (the paper has no book-style chapters); page numbers are the journal's printed page numbers.

### Chapter 0: Introduction (pp. 2–5)

**Summary:** Motivates sequent calculi for proof-search in PTS and situates PTSC$\alpha$ against Pym, Dowek, Pym–Dyckhoff, Geuvers–Jojgov and Gutiérrez–Ruiz.

**Key Definitions & Concepts:**
- **Pure Type System (PTS)** — Berardi/Terlouw generalisation of the $\lambda$-cube underlying Coq, Lego and the Edinburgh LF.
- **LJT and $\overline{\lambda}$** — Herbelin's permutation-free focused calculus for intuitionistic logic and its proof-term calculus with explicit substitutions, related to call-by-name $\beta$ and Krivine's machine.
- **$\Pi L$ rule** — $\dfrac{\Gamma\vdash M:A \quad \Gamma;\langle M/x\rangle B\vdash l:C}{\Gamma;\Pi x^A.B\vdash M\cdot l:C}$, closer in spirit to Coq's `apply` than natural-deduction $\Pi$-elimination.
- **Delayed premisses** — tactics may postpone the first premiss of $\Pi L$, yielding incomplete proof-terms and unification constraints, which the paper models with explicitly scoped meta-variables.
- **Correctness by construction** — search output needs no re-type-checking because search is root-first rule application.

**Key Questions:**
1. Why is a focused calculus (LJT) preferred over G3 here, and what does it cost?
2. In what sense is Coq's `apply` closer to $\Pi L$ than to $\Pi$-elimination?

---

### Chapter 1: Syntax and Operational Semantics of PTSC$\alpha$ (pp. 5–8)

**Summary:** Defines the term/list syntax with meta-variables and the rewrite systems, and proves termination of the substitution-propagation part. : [[Operational-Semantics-and-Confluence|Link]]

**Key Definitions & Concepts by Section:**
- **1.1 Syntax** — terms $M,N,P,A,B ::= \Pi x^A.B \mid \lambda x^A.M \mid s \mid x\,l \mid M\,l \mid \langle M/x\rangle N \mid \alpha(M_1,\dots,M_n)$ and lists $l ::= [] \mid M\cdot l \mid l@l' \mid \langle M/x\rangle l \mid \beta(M_1,\dots,M_n)$; ground terms contain no meta-variables; a variable is always applied to a list; meta-variables carry arity and behave like higher-order variables à la CRS, e.g. $\alpha(x,y)$ for an unknown term with free variables among $x,y$; instantiation never happens during computation. : [[Meta-Variables-and-Partial-Proof-Terms|Link]]
- **1.2 Operational semantics** — Fig. 1: rule B ($(\lambda x^A.M)(N\cdot l)\to(\langle N/x\rangle M)\,l$), B1–B3, append rules A1–A4, substitution-propagation rules C1–C6, $C\alpha$, D1–D3, $D\beta$; systems B, x$'$, xsubst$'$; first-order encoding $S(\_)$ with a lexicographic path ordering gives **Theorem 1.2/Corollary 1.3**: x$'$ is terminating on all terms. : [[Operational-Semantics-and-Confluence|Link]]

**Key Questions:**
1. Why must a meta-variable be applied to the variables that may occur free in the unknown term?
2. Why does x$'$ terminate on untyped terms while adding B does not?

---

### Chapter 2: $\lambda$-terms and Confluence (pp. 8–11)

**Summary:** Proves confluence of PTSC$\alpha$ by simulation through translations to and from a PTS fragment with reserved variables for meta-variables.

**Key Definitions & Concepts:**
- **Fragment PTS$\alpha$** — $\lambda$-terms in which reserved variables $\alpha^k$ (resp. $\beta^k$) are never bound and are applied to at least $k$ (resp. $k+1$) arguments; stable under $\beta$.
- **Translations $\mathcal B$ and $\mathcal A$** — from sequent calculus to $\lambda$-terms and back (Prawitz-style, with list-parameterised $\mathcal A_l$); list meta-variables get the future head variable as first argument.
- **List-needing terms** (Def. 2.3) to make $\mathcal A$ well-founded.
- **Theorems 2.2, 2.5, 2.7 and Corollary 2.9** — $\to_\beta$ simulates $\to_{Bx'}$ through $\mathcal B$; $\to_{Bx'}$ simulates $\to_\beta$ through $\mathcal A$; $\mathcal B(\mathcal A(t))=t$ and $M\to^*_{x'}\mathcal A(\mathcal B(M))$; confluence of $\to_{x'}$ and $\to_{Bx'}$.
- **CRS versus ERS meta-variables** — CRS style, with rules $C\alpha$ and $D\beta$, closes the $B$/C4 critical pair that breaks confluence in ERS style.

**Key Questions:**
1. How does simulation transfer confluence from $\beta$ to the sequent-calculus rewriting?
2. Why does the CRS-style choice of meta-variables restore confluence?

---

### Chapter 3: Typing System and Properties (pp. 12–14)

**Summary:** Gives the typing rules of PTSC (ground terms) with three judgments and proves the basic meta-theory up to subject reduction. : [[Pure-Type-Sequent-Calculi|Link]]

**Key Definitions & Concepts:**
- **PTSC parameters** — sorts $S$, axioms $\mathcal A\subseteq S^2$, rules $\mathcal R\subseteq S^3$.
- **Judgments** — $\Gamma\ wf$; $\Gamma\vdash M:A$; $\Gamma;B\vdash l:C$ where $B$ is the **stoup** (the type of what the list is applied to).
- **Rules (Fig. 6)** — empty, extend, sorted, $\Pi wf$, $\Pi R$, $Select_x$, axiom, $\Pi L$, three conversion rules ($conv_R$, $conv'_R$, $conv_L$), and cuts Cut1–Cut4, the substitution cuts shaped to manipulate the environment ($\Gamma,\langle P/x\rangle\Delta\sqsubseteq\Delta'\ wf$).
- **Environment inclusion $\Gamma\sqsubseteq\Delta$** — types may be replaced by convertible ones.
- **Lemmas 3.3–3.6** — typing invariants, weakening, thinning; **Theorem 3.7 (Subject Reduction)**, proved in the Appendix.

**Key Questions:**
1. What does the stoup contribute that natural-deduction typing lacks?
2. Why must the cut rules Cut2 and Cut4 reshape the environment?

---

### Chapter 4: Correspondence with PTS (pp. 14–16)

**Summary:** Shows typing is preserved by $\mathcal A$ and $\mathcal B$ and that a PTSC is strongly normalising iff its PTS is.

**Key Definitions & Concepts by Section:**
- **4.1 Type preservation** — PTS typing rules (Fig. 7); Theorem 4.1 (thinning, substitution, subject reduction in PTS); Corollary 4.2 (equational theories coincide); **Theorems 4.3, 4.4** (typing preserved in both directions, including environments). : [[Meta-Theory-of-PTSC|Link]]
- **4.2 Equivalence of strong normalisation** — **Theorem 4.5**; one direction by simulation (Theorem 2.5), the other by subject reduction plus an infinite-signature lpo encoding with terms of the PTS as labels (after Bloo and Geuvers); consequently every corner of the cube has a PTSC usable for proof-search. : [[Meta-Theory-of-PTSC|Link]]

**Key Questions:**
1. Which results make "PTSC is SN iff PTS is SN" work in each direction?
2. Why does the proof need a labelled, infinite signature?

---

### Chapter 5: Proof-Search (pp. 16–19)

**Summary:** Derives the syntax-directed system PS by folding conversion into the logical rules, proves it sound and complete, and classifies the non-determinism of search. : [[Focused-Sequent-Calculus-and-Permutation-Free-Proof-Search|Link1]], [[Proof-Search-Strategies-and-Tactics|Link2]], [[Proof-Search-System-PS|Link3]], [[Pure-Type-Systems-and-the-Lambda-Cube|Link4]]

**Key Definitions & Concepts:**
- **Goal** — a term type $A$ (or list type $C$ with stoup $B$) given as input; the output is a normal term.
- **PS rules (Fig. 9)** — axiom, $\Pi wf$, sorted, $Select_x$, $\Pi R$, $\Pi L$, each with conversion built into side-conditions (like the constructive engine, but for inhabitation, not synthesis).
- **Quasi-normal form** (Def. 5.1) — redexes only inside type annotations.
- **Theorem 5.2** — soundness (given $\Gamma\vdash A:s$) and completeness of PS, independent of expansion postponement since PS does not check types.
- **Three sources of non-determinism** — head-variable choice for $Select_x$; the $\Pi R$/$Select_x$ and $\Pi L$/axiom overlaps (removed by restricting to $\eta$-long forms/uniform proofs); three applicable rules when the goal reduces to a sort.
- **Don't-care versus don't-know non-determinism**, and the sequentialisation of the two premisses of $\Pi L$ causing endless backtracking.

**Key Questions:**
1. Why can PS skip type-checking of the premisses, and when does the proviso $\Gamma\vdash A:s$ come in?
2. How does the dependency in $\Pi L$ force an inefficient search order, and what is the remedy?

---

### Chapter 6: Using Meta-Variables for Proof-Search (pp. 19–23)

**Summary:** Introduces goal environments and the proof-enumeration system PE, whose delayed sub-goals and constraints formalise partial proofs and avoid $r$-splitting. : [[Meta-Variables-and-Partial-Proof-Terms|Link]]

**Key Definitions & Concepts:**
- **Goal environment $\Sigma$** (Def. 6.1) — list of term-goals $\Gamma\vdash\alpha:A$, list-goals $\Gamma;B\vdash\beta:A$ and constraints $A\overset{\Gamma}{=}B$; solved when only solved constraints $A\leftrightarrow^*B$ between ground terms remain.
- **Substitution** — maps $\alpha$ of arity $n$ to a closed higher-order term $x_1\dots x_n.M$; application yields the x$'$-normal form of $\langle\sigma(N_1)/x_1\rangle\dots\langle\sigma(N_n)/x_n\rangle M$.
- **PE (Fig. 10)** — statements $\Gamma\vdash M:A\mid\Sigma$, $\Gamma;B\vdash l:C\mid\Sigma$ and $\Sigma\Rightarrow\sigma$; rules $Claim_\alpha$, $Claim_\beta$ delay a goal, axiom emits a unification constraint $D\overset{\Gamma}{=}C$, $Solve_\alpha$, $Solve_\beta$, Solved.
- **Solution** (Def. 6.3), **Theorem 6.5 (Soundness)**, **Theorem 6.7 (Completeness)** — PS is the special case with $\Sigma$ always solved.
- **Two novelties vs. Dowek and Muñoz** — the search tree is a tree of sequent-calculus rules built root-first; list meta-variables of unknown length avoid $r$-splitting, so the head variable can be chosen without committing to its argument count (no infinitely branching tree and no interleaving).
- **Strategies** — PS is the eager strategy; Dowek's algorithm is the lazy one (always abandon the $\Pi L$ first premiss); mixed strategies suit interactive provers; comparison with Coq's `apply`.

**Key Questions:**
1. How do list meta-variables remove the need for $r$-splitting?
2. Where do unification constraints originate in PE, and how do they constrain delayed goals?
3. Why is PE's completeness unsurprising, and which question does it leave open?

---

### Chapter 7: Example: Commutativity of Conjunction (pp. 23–26)

**Summary:** Contrasts PS and PE on System F, where $S=\{\star,\square\}$, $\mathcal A=\{(\star,\square)\}$, $\mathcal R=\{(\star,\star),(\square,\star)\}$ and $A\wedge B=\Pi Q^\star.(A\to(B\to Q))\to Q$.

**Key Definitions & Concepts:**
- **PS derivation** — requires guessing the witnesses $N_A,N_B$ before the unification constraint is known.
- **PE derivation** — claims $\alpha_A,\alpha_B$ as delayed goals, commits only to the head variable $y$ because it yields the solved constraint $Q\overset{\Gamma}{=}Q$, then solves the goals in order, with $\alpha_1\mapsto A$ forced by $\alpha_1(\Gamma)\overset{\Gamma}{=}A$; final proof $\lambda xQy.\,y\,(x\,B\cdot(\lambda x'y'.y')\cdot[])\cdot(x\,A\cdot(\lambda x'y'.x')\cdot[])\cdot[]$.
- **Mechanical choices** — wrong head variables give unsolvable constraints detectable by a simple syntactic check.

**Key Questions:**
1. Why can $\alpha_1$ (inhabiting $\star$) not be solved before the delayed constraint is known, and what does PE do instead?
2. In which order must the delayed goals be solved, and why?

---

### Chapter 8: Conclusion and Further Work (pp. 26–27)

**Summary:** Recaps the framework and lists future directions. : [[Proof-Search-Strategies-and-Tactics|Link]]

**Key Definitions & Concepts:**
- **Contributions** — a sequent calculus per PTS with sequent-style types and proof-terms, direct confluence by simulation, strong correspondence with natural deduction (formalised in Coq), and meta-variables for incomplete proofs without $r$-splitting.
- **Further work** — redesign of the Coq proof engine, $\eta$-conversion and uniform proofs, direct strong-normalisation proofs, inductive types and their tactics, classical Pure Type Sequent Calculi.

**Key Questions:**
1. Which parts of the framework are already formalised and which remain future work?

---

### Appendix: Subject Reduction (pp. 30–35)

**Summary:** Proof of Theorem 3.7; treated as supporting material and not summarised further here beyond the statement in Chapter 3. : [[Proof-Search-Strategies-and-Tactics|Link]]
