# Combining Computational Theories — Guidelines

## Header

**Title:** Combining Computational Theories
**Author(s):** Émilie Grienenberger
**Publication:** PhD thesis (HAL, 2025). Written in French (Chapter 1) with a full English translation (Chapter 2 onward). Subjects: Logic in Computer Science (cs.LO), Formal Languages and Automata Theory (cs.FL). Keywords: ecumenicism, rewrite systems, type theories, proof assistants, formal proofs, interoperability.

**Brief Summary:**
This thesis studies how to combine and compare computational logical theories, motivated by the problem of interoperability between proof assistants (Coq, HOL Light, PVS, Lean, Isabelle, etc.). It develops two threads. The first (Part II) designs a new ecumenical natural-deduction system, NE, in which classical and intuitionistic connectives coexist as indexed primitives without collapsing into each other, extends it to a computational (rewriting-based) framework, proves a cut-elimination/normalization theorem for it, and lifts it to a higher-order ecumenical Simple Type Theory. The second (Parts III–IV) develops the metatheory of Pure Type Systems modulo rewriting theory and the λΠ-calculus modulo theory (implemented by Dedukti), studies when extending or fragmenting such a theory preserves well-typedness (culminating in the "fragment theorem"), and applies all of this to "theory U," a Dedukti theory expressive enough to encode minimal, constructive, classical, and ecumenical logics — proving normalization, decidability, soundness, conservativity, and consistency for its ecumenical fragments.

**Intent of the Author:**
The author wants to give proof assistants and their diverse logical foundations a common, rewriting-based logical framework (theory U / Dedukti) in which proofs from constructive and classical systems can coexist, be cross-checked, translated, and even partially "constructivized" — and to supply the general modularity/fragmentation machinery needed to trust that a proof imported into such a combined theory really only depends on the axioms of the subsystem it is claimed to belong to.

---

## Topic List

1. **Interoperability of Proof Assistants** : [[Interoperability-of-Proof-Assistants|Link]]
   - Cross checking and comparing formal proofs across systems
   - Trust in proof assistant formalizations : [[Interoperability-of-Proof-Assistants|Link]]
   - Direct translations between proof assistants : [[Interoperability-of-Proof-Assistants|Link]]
   - Theory U as a common ground for embedding proof systems : [[Interoperability-of-Proof-Assistants|Link]]
   - Dedukti as a tool for interoperability

2. **Ecumenical Logics** : [[Ecumenical-Logics|Link]]
   - Intuitionistic versus classical natural deduction
   - Witness and disjunction properties : [[Ecumenical-Logics|Link1]], [[Proof-Normalization-in-Ecumenical-Logic|Link2]]
   - Design of the ecumenical system NE with indexed connectives
   - Statements and the embedding of formulas via double negation
   - Ecumenical entailment and externally classical judgments : [[Ecumenical-Logics|Link]]
   - Soundness and conservativity of NE with respect to NJ and NK : [[Ecumenical-Logics|Link]]
   - Consistency and non collapse of ecumenical fragments : [[Theory-U-and-Ecumenical-Fragments|Link1]], [[Ecumenical-Logics|Link2]]

3. **Deduction Modulo Theory** : [[Deduction-Modulo-Theory|Link]]
   - Congruences over terms and formulas : [[Deduction-Modulo-Theory|Link]]
   - Non confusing and decidable congruences : [[Deduction-Modulo-Theory|Link]]
   - Convergent rewrite systems as congruences : [[Deduction-Modulo-Theory|Link]]
   - Definition by equality versus definition by reduction : [[Deduction-Modulo-Theory|Link]]
   - Delta reduction for unfolding definitions : [[Deduction-Modulo-Theory|Link]]
   - Iota reduction for inductive recursors : [[Deduction-Modulo-Theory|Link]]
   - Higher order rewrite rules : [[Deduction-Modulo-Theory|Link]]
   - Well typedness of a computational theory : [[Deduction-Modulo-Theory|Link]]

4. **Proof Normalization in Ecumenical Logic** : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
   - Cut elimination for ecumenical natural deduction : [[Higher-Order-Ecumenical-Type-Theory|Link1]], [[Theory-U-and-Ecumenical-Fragments|Link2]], [[Proof-Normalization-in-Ecumenical-Logic|Link3]]
   - Reducibility candidates and strong normalization : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
   - Simple cuts versus n cuts and commuting eliminations
   - Subject reduction under index constraints
   - The exchange construction for fake cuts : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
   - Pre models of a congruence as a normalization hypothesis
   - Ecumenical witness and disjunction properties for normal proofs : [[Proof-Normalization-in-Ecumenical-Logic|Link]]

5. **Higher-Order Ecumenical Type Theory** : [[Higher-Order-Ecumenical-Type-Theory|Link]]
   - Ecumenical simple type theory as a first order computational theory : [[Deduction-Modulo-Theory|Link1]], [[Higher-Order-Ecumenical-Type-Theory|Link2]]
   - Encoding lambda terms with combinators and an application symbol
   - Separating propositional contents from propositions via a truth predicate
   - Soundness and conservativity of ecumenical simple type theory : [[Ecumenical-Logics|Link1]], [[Higher-Order-Ecumenical-Type-Theory|Link2]], [[Theory-U-and-Ecumenical-Fragments|Link3]]
   - Confluence and termination of the ecumenical rewrite system : [[Higher-Order-Ecumenical-Type-Theory|Link]]

6. **Pure Type Systems** : [[Pure-Type-Systems|Link]]
   - Definition of a pure type system as sorts axioms and rules : [[Pure-Type-Systems|Link]]
   - Barendregt's lambda cube : [[Pure-Type-Systems|Link]]
   - Syntax of terms free and bound variables and substitution : [[Pure-Type-Systems|Link]]
   - Alpha equivalence : [[Pure-Type-Systems|Link]]
   - Beta reduction as computation in pure type systems : [[Proof-Normalization-in-Ecumenical-Logic|Link1]], [[Pure-Type-Systems|Link2]]
   - Confluence normalization and strong normalization of rewrite relations : [[Higher-Order-Ecumenical-Type-Theory|Link]]
   - Nontermination of untyped beta reduction and Girard's paradox : [[Pure-Type-Systems|Link]]
   - Typing rules and the conversion rule : [[Pure-Type-Systems|Link]]
   - Product injectivity subject reduction and uniqueness of types : [[Pure-Type-Systems|Link]]
   - Undecidability of type checking and type reconstruction : [[Theory-U-and-Ecumenical-Fragments|Link]]
   - Universe hierarchies for normalizing type systems : [[Proof-Normalization-in-Ecumenical-Logic|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]

7. **The Lambda-Pi-Calculus Modulo Theory** : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - The Edinburgh Logical Framework as an ancestor of $\lambda\Pi$ : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Dedukti as a $\lambda\Pi$ type checker : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Dedukti concrete syntax for declarations definitions and rewrite rules
   - Shallow versus deep encodings of formal systems : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Encoding minimal predicate logic by formulae as types : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
   - Encoding propositions as objects via a proof embedding
   - Encoding arbitrary pure type systems via universes and decoding functions : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]

8. **Modularity of Type Theories** : [[Modularity-of-Type-Theories|Link]]
   - Theory contexts as incremental definitions : [[Modularity-of-Type-Theories|Link]]
   - Strongly well formed theory contexts : [[Modularity-of-Type-Theories|Link]]
   - Weakly well formed theory contexts : [[Modularity-of-Type-Theories|Link]]
   - Non modularity of theory unions and extensions : [[Modularity-of-Type-Theories|Link]]
   - Constraint generation and presolutions for rewrite rules : [[Modularity-of-Type-Theories|Link1]], [[Deduction-Modulo-Theory|Link2]]
   - Safe theory extensions : [[Modularity-of-Type-Theories|Link]]

9. **Theory Fragmentation** : [[Theory-Fragmentation|Link]]
   - Dependency and fragments of a theory : [[Theory-Fragmentation|Link]]
   - The fragment theorem : [[Theory-Fragmentation|Link]]
   - Weakening the hypotheses of the fragment theorem : [[Theory-Fragmentation|Link]]
   - Fragments of strongly and weakly well formed theories : [[Theory-Fragmentation|Link]]
   - Type inference under fragmentation : [[Theory-Fragmentation|Link]]
   - Finding a presolution in a fragment : [[Theory-Fragmentation|Link]]

10. **Theory U and Ecumenical Fragments** : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Shallow encoding of ecumenical simple type theory in Dedukti : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Super consistency and $\Pi$-algebra models : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Normalization and decidability of type checking for ecumenical STT : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Soundness and conservativity with respect to first order logic : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Soundness and conservativity with respect to higher order logic : [[Theory-U-and-Ecumenical-Fragments|Link]]
    - Consistency of ecumenical simple type theory : [[Theory-U-and-Ecumenical-Fragments|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (français) (pp. 11–16)

**Summary:** The French-language introduction to the thesis. Its content is a direct counterpart of Chapter 2 — same motivating discussion of proof-assistant interoperability, the Wiedijk 100-theorems list, the PVS/HOL Light/Coq case study on the denumerability of $\mathbb{Q}$, Dedukti, and theory U. See Chapter 2 for the full breakdown of definitions, concepts, and questions. : [[Theory-Fragmentation|Link]]

---

### Chapter 2: Introduction (english) (pp. 17–22)

**Summary:** Motivates the thesis via the problem of trust and interoperability among proof assistants: many important theorems are formalized in only one system, raising questions of cross-checking, comparison of axiomatizations, and detection/factoring of redundant developments. Illustrates these differences concretely by comparing PVS, HOL Light, and Coq proofs of the denumerability of $\mathbb{Q}$, then introduces Dedukti (an implementation of the $\lambda\Pi$-calculus modulo theory) and "theory U" as a proposed common logical framework, and lays out the thesis's two-part structure (ecumenical logics; pure type systems modulo rewriting and their modularity).

**Key Definitions & Concepts:**
- **Logical framework** — a language allowing the formalization of mathematical theories, statements, and proofs, in which a theory's own definitions/axioms are clearly distinguished from the framework's logical axioms and deduction rules.
- **Edinburgh Logical Framework (LF)** — an early well-known logical framework, at the basis of de Bruijn's Automath, itself an ancestor of contemporary proof assistants.
- **Interoperability** — the question of whether mathematical theories and proofs can be shared and cross-checked across different proof assistants.
- **Denumerability of $\mathbb{Q}$ case study** — the same theorem formalized very differently in PVS (top-down subtyping refinement of a number hierarchy, proof scripts with unrecorded proof terms), HOL Light (natural numbers from the axiom of infinity and choice, non-constructive, minimal logical core), and Coq (natural numbers/integers built inductively as binary representations) — illustrating why direct pairwise translation between proof assistants is hard.
- **Dedukti** — an implementation of the $\lambda\Pi$-calculus modulo theory, an extension of LF supporting user-defined computational theories via rewriting; expressive enough to soundly and conservatively embed many proof assistants' logics.
- **Theory U** — a Dedukti theory in which proofs of minimal, constructive, classical, and ecumenical predicate logic and Simple Type Theory (with or without prenex polymorphism or predicate subtyping), plus the calculus of constructions, can all be expressed.
- **Combining computational theories** — the thesis's central object of study: theories (like theory U) that combine multiple logical subsystems, and the metatheoretical questions this raises (how subsystems interact, which properties transfer between a theory and its subtheories, how to identify which subsystem a given proof belongs to).

**Key Questions:**
1. What concrete technical obstacles (illustrated by the PVS/HOL Light/Coq case study) make direct translation and comparison of proofs across proof assistants difficult, even for as simple a theorem as the denumerability of $\mathbb{Q}$?
2. What is the relationship between Dedukti, the $\lambda\Pi$-calculus modulo theory, and theory U — which is the framework, which is the implementation, and which is a specific theory expressed within it?
3. What are the thesis's two main lines of study (ecumenical logics vs. pure type systems modulo rewriting), and how does the thesis argue they both bear on the same underlying question of combining computational theories?

---

### Chapter 3: A case for ecumenism (pp. 25–30)

**Summary:** Sets up the case for "ecumenical" logics that let intuitionistic and classical reasoning coexist in a single system. Reviews the reference systems NJ (constructive) and NK (classical) predicate logic, their divergence (excluded middle, double-negation elimination, Peirce's formula) and the extra information intuitionistic proofs carry (the witness and disjunction properties), surveys prior ecumenical systems, and previews NE, the thesis's own ecumenical system, together with its extension to computational theories (Chapters 4–7). : [[Theory-U-and-Ecumenical-Fragments|Link]]

**Key Definitions & Concepts:**
- **NJ / NK** — reference natural deduction systems for constructive and classical predicate logic, sharing the same term/formula syntax over a first-order language $(F,P)$; every NJ proof is an NK proof but not conversely (e.g. instances of excluded middle are not NJ-provable).
- **Witness and disjunction properties (Lemma 3.1.1)** — if $\vdash_{NJ} \exists x.A$ then $\vdash_{NJ} A[x:=t]$ for some term $t$; if $\vdash_{NJ} A \lor B$ then $\vdash_{NJ} A$ or $\vdash_{NJ} B$. These fail in NK, illustrating that intuitionistic proofs carry strictly more information.
- **Naive ecumenical construction and its collapse** — simply unioning NJ and NK rules with separate intuitionistic/classical connectives lets the "intuitionistic excluded middle" $A \lor_i \lnot_i A$ become provable for any $A$, collapsing the two fragments together (Figure 3.2) — motivating a more careful design.
- **Advantages of ecumenism** — programs can be extracted from proofs of intuitionistic statements even when the specification itself is classical; intuitionistic and classical proofs can be stored in one shared database rather than two disjoint ones.
- **NE's design principle** — rather than splitting contexts into "zones" or using double-negation translation to define classical connectives (as prior ecumenical systems do), NE introduces a single additional connective $\circ$ embedding formulas ("propositions") into statements, keeping both intuitionistic and classical connectives as syntactic primitives.

**Key Questions:**
1. Why does the naive approach of taking the union of NJ's and NK's rules with two separately-indexed copies of each connective fail to produce a genuine ecumenical system?
2. What concrete benefit does an ecumenical logic offer over keeping intuitionistic and classical logic as two entirely separate systems (e.g. for program extraction or for storing formal proof databases)?
3. How does NE's approach (a single embedding connective $\circ$, with indexed but shared deduction rules) differ structurally from prior ecumenical systems that split contexts into zones or that define classical connectives purely via double-negation translation?

---

### Chapter 4: The system NE (pp. 31–40)

**Summary:** Gives the formal definition of NE: its three-level syntax (terms, formulas, statements), its uniform deduction rules governed by an ordering on the indices $\{i,c\}$, and proves NE is ecumenical (its classical and intuitionistic fragments do not collapse), sound and conservative with respect to NJ and NK, and consistent.

**Key Definitions & Concepts:**
- **Indices and formulas (Def. 4.1.1)** — $I=\{i,c\}$; formulas built from atomic predicates, $\bot$, $\top$, $\lnot$, and *indexed* connectives $A \land_\sigma B$, $A \lor_\sigma B$, $A \Rightarrow_\sigma B$, $\forall^T_\sigma x.A$, $\exists^T_\sigma x.A$ for $\sigma \in I$; $\top,\bot,\lnot$ have a single (unindexed) copy since they are intuitionistically stable under double negation.
- **Statements (Def. 4.1.2)** — of the form $\circ_\sigma A$, where $\circ_i$/$\circ_c$ mark respectively the absence/presence of a prenex double negation, embedding a formula into a judged statement.
- **Ordering on indices (Def. 4.1.3)** — $c < i$, formalizing the principle "constructive proofs contain more information than classical proofs; constructive information can only be lost."
- **NE deduction rules (Def. 4.1.4, Fig. 4.2)** — a single introduction/elimination rule per connective (rather than one per index combination), each guarded by an index-ordering side condition (e.g. $\land$-i requires $\min(\sigma,\tau)\le\min(\sigma_A,\sigma_B)$) that collapses what would otherwise be a combinatorial explosion of rules (13 valid variants of conjunction-introduction alone, Figure 4.1) into one schematic rule.
- **Nonhybrid vs. hybrid objects (Def. 4.2.1)** — a formula/statement/judgment/proof is classical or intuitionistic if every connective in it carries that index uniformly; otherwise it is hybrid.
- **Externally classical/intuitionistic judgments (§4.2.3)** — a statement $\circ_\sigma A$ is externally classical if $\sigma=c$; such judgments inherit classical laws (double-negation elimination, de Morgan, Peirce's formula, excluded middle on instances $\circ_c(A\lor_\sigma\lnot A)$).
- **Soundness (Lemma 4.2.2)** and **conservativity (Lemma 4.2.3)** of NE with respect to NJ and NK, via mutually inverse embeddings $|\cdot|_\sigma$ / $|\cdot|^\sigma$ (Figs. 4.5–4.6) — $|\cdot|^i$ notably reconstructs the Kolmogorov double-negation translation.
- **Ecumenism and consistency (Corollaries 4.2.1–4.2.3)** — the classical and intuitionistic fragments of NE do not collapse into one another, and NE itself is consistent ($\vdash_{NE}\circ_\sigma\bot$ is unprovable), all following from conservativity.

**Key Questions:**
1. How does the single index-ordering side condition on each NE rule (e.g. $\min(\sigma,\tau)\le\min(\sigma_A,\sigma_B)$ for $\land$-introduction) manage to encode exactly the 13 "acceptable" combinations out of 16 possible index assignments for conjunction-introduction, and what principle rules out the other 3?
2. Why are $\top$, $\bot$, and $\lnot$ given only a single (unindexed) copy in NE while $\land,\lor,\Rightarrow,\forall,\exists$ each get two indexed copies?
3. What is the role of the mutually inverse embeddings $|\cdot|_\sigma$ and $|\cdot|^\sigma$ in establishing both soundness and conservativity, and how does $|\cdot|^i$ recover the classical Kolmogorov double-negation translation as a special case?

---

### Chapter 5: NE Modulo Theory (NE / ≡) (pp. 41–46)

**Summary:** Extends NE with a deduction-modulo-theory framework, letting terms and formulas be identified up to a fixed congruence so that computational theories (e.g. arithmetic operations and predicates defined by rewriting rather than by axiom) can be expressed directly inside NE's inference rules. : [[Deduction-Modulo-Theory|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]

**Key Definitions & Concepts:**
- **Congruence-modulo introduction/elimination (§5.1)** — e.g. defining $\mathsf{Positive}$ and $+$ by a congruence $\equiv$ such that $0+t\equiv t$, $S(u)+t\equiv S(t+u)$, $\mathsf{Positive}(0)\equiv\bot$, $\mathsf{Positive}(S(t))\equiv\top$, letting a single application of ($\top$-i) prove a fact like $\vdash\circ_i[\mathsf{Positive}(S(0)+S(S(x)))]$.
- **Contexts, binary relations, congruences (Def. 5.2.1–5.2.2)** — term/formula contexts $C[\cdot]$ with a hole; a relation is a *congruence* if it is an equivalence relation that is stable by context and by substitution; any relation has a smallest closure achieving reflexivity/transitivity/symmetry/congruence.
- **NE / $\equiv$ inference rules (Figs. 5.2–5.3)** — every NE introduction/elimination rule is relaxed to apply modulo $\equiv$ (conclusion/hypothesis need only be *congruent* to, not syntactically equal to, the rule's schematic form).
- **Well-behaved theory conditions (§5.3)** — a congruence defining a theory must be **non-confusing** (two formulas are congruent only if atomic, or share the same main connective/index with congruent subformulas — so the congruence never identifies an intuitionistic and a classical connective) and **decidable**; a sufficient condition for both is that the congruence come from a **convergent** (terminating and confluent) rewrite system mapping terms to terms and atomic propositions to propositions.

**Key Questions:**
1. Why must a congruence defining an NE theory be "non-confusing" — what would go wrong (e.g. for defining cut) if the congruence could equate an intuitionistic and a classical connective?
2. How does relaxing NE's introduction/elimination rules to apply "modulo $\equiv$" let a single rule application (as in the (⊤-i) example) stand in for what would otherwise require several unfolding steps?
3. Why is convergence (termination + confluence) of a rewrite system a natural sufficient condition for it to generate a decidable, non-confusing congruence?

---

### Chapter 6: Normalizing ecumenical proofs (pp. 47–68)

**Summary:** Defines proof terms for NE modulo a congruence ($\mathrm{NE}/\!\equiv$) and proves a cut-elimination/normalization theorem for them, extending known normalization results for NJ/NK modulo theory to the ecumenical setting without collapsing the intuitionistic/classical distinction. Establishes subject reduction and, as a payoff, recovers ecumenical (partial) versions of the witness and disjunction properties for externally intuitionistic judgments — showing NE's ecumenical structure survives proof normalization. : [[Proof-Normalization-in-Ecumenical-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Proof terms** — Proof terms $\pi,\rho,\dots$ built from $\lambda$-calculus-like constructors ($\lambda^\sigma\alpha.\pi$, $\mathrm{app}_\sigma(\pi,\pi')$, pairs, injections, etc.), plus new constructions $\mathrm{furl}(\cdot)$/$\mathrm{unfurl}(\cdot)$ for the embedding rules $\circ_i$-i/$\circ_i$-e, and $\theta$ for truth introduction. **Elimination vs. introduction proof terms** — a term is an elimination if headed by an elimination-rule constructor (e.g. $\mathrm{fst}$, $\mathrm{app}$, $\mathrm{unfurl}$), an introduction otherwise; **neutral** terms are non-introductions. Typing judgments $\Gamma\vdash\pi:\circ_\sigma A$ correspond one-to-one with $\mathrm{NE}/\!\equiv$ derivations (Lemma 6.1.1). : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
- **6.2 Normalizing proof terms** — **Cuts** (0-cuts and $n$-cuts) as paths from an elimination's major premise through intervening $\lor$-e/$\exists$-e applications to an introduction; a **0-cut** is an immediate redex, an **$n$-cut** requires first migrating intervening disjunction/existential eliminations outward via an auxiliary $\mathrm{exchange}^\alpha(\pi_1,\pi_2)$ term that reduces "fake cuts" (cuts visible in NE but absent after translation to NJ). Two reduction relations: simple reduction $\to$ and stronger **ultra-reduction** $\rhd$; strong normalization of $\rhd$ is proved via **reducibility candidates** using **pre-models** of a first-order signature/congruence to interpret formulas as reducibility-candidate sets $|A|_\varphi$, closed under the congruence. : [[Proof-Normalization-in-Ecumenical-Logic|Link]]
  - **6.2.1 Elimination of 0-cuts** — the reducibility-candidate interpretation $|A|_\varphi$ per connective (Def. 6.2.4); every typable proof term lies in the interpretation of its type (Lemma 6.2.8), yielding strong normalization (Lemma 6.2.9) *conditional on the congruence having a pre-model*.
  - **6.2.2 Elimination of n-cuts** — **commuting/elimination contexts** letting $\lor$-e/$\exists$-e commute outward past other eliminations; **simple proof terms** closed under $\to$-reduction; the main normalization theorem (6.2.13) gives every typable $\mathrm{NE}/\!\equiv$ proof term an $R$-normal form.
- **6.3 Subject Reduction** — reduction preserves typing (Theorem 6.3.1), via substitution lemmas and an **Exchange lemma** (6.3.4) handling the case where a cut's index constraints force routing through $\mathrm{exchange}$ rather than direct substitution, since reducing a cut can only raise (never lower) the embedding index. : [[Proof-Normalization-in-Ecumenical-Logic|Link1]], [[Pure-Type-Systems|Link2]]
- **6.4 Normal Proofs** — **Introduction property**: any $R$-normal proof of $\vdash\circ_i A$ must begin with an introduction rule; this yields ecumenical witness and disjunction properties (Theorem 6.4.2) for externally intuitionistic conclusions, generalizing Lemma 3.1.1 to the hybrid ecumenical setting, under the pre-model hypothesis. : [[Proof-Normalization-in-Ecumenical-Logic|Link]]

**Key Questions:**
1. Why is normalizing NE proofs "the long way" — via a direct $\mathrm{NE}/\!\equiv$ cut-elimination procedure — necessary, rather than relying on the sound/conservative translations into NJ/NK from Chapter 4?
2. What role does the "fake cut" notion and the $\mathrm{exchange}$ construction play, and why can't 0-cut elimination for implication/negation always be handled by ordinary substitution alone?
3. Why must the hypothesis "the congruence $\equiv$ has a pre-model" be assumed for normalization and the witness/disjunction properties, rather than these being unconditional consequences of $\mathrm{NE}/\!\equiv$'s definition?

---

### Chapter 7: Higher order ecumenism (pp. 69–73)

**Summary:** Uses the machinery of Chapters 5–6 to define an ecumenical Simple Type Theory (STT), expressed as a first-order computational theory rather than a primitive higher-order system, and shows it is sound, conservative with respect to constructive/classical STT, and normalizing — demonstrating that ecumenism extends beyond first-order predicate logic into the higher-order setting used by real proof assistants (the HOL family). : [[Higher-Order-Ecumenical-Type-Theory|Link1]], [[Deduction-Modulo-Theory|Link2]], [[Theory-U-and-Ecumenical-Fragments|Link3]]

**Key Definitions & Concepts by Section:**
- **7.1 Ecumenical STT** — higher-order terms encoded as first-order terms over sorts $T,U,V ::= o \mid \iota \mid s\to t$ ($\iota$ = individuals, $o$ = propositional contents); **combinators** $K_{T,U}$, $S_{T,U,V}$ and an application symbol $\alpha_{T,U}$ simulate $\lambda$-terms/$\beta$-reduction via rewrite rules. Higher-order connectives ($\dot\top,\dot\bot,\dot\land_\sigma,\dot\lor_\sigma,\dot\Rightarrow_\sigma,\dot\forall^T_\sigma,\dot\exists^T_\sigma,\dot\lnot$) are first-order constants; the predicate $\varepsilon$ maps propositional contents to actual propositions via rules like $\varepsilon(t\,\dot\land_\sigma\,u)\to\varepsilon(t)\land_\sigma\varepsilon(u)$. This rewrite system is shown non-confusing, decidable, terminating, and confluent — a valid NE theory per Chapter 5. : [[Higher-Order-Ecumenical-Type-Theory|Link1]], [[Theory-U-and-Ecumenical-Fragments|Link2]]
  - **7.1.1 Soundness** — the embedding $|\cdot|_\sigma$ over ecumenical-STT terms preserves congruence (7.1.1) and provability transfers from constructive/classical STT (7.1.2).
  - **7.1.2 Conservativity** — converse embeddings $|\cdot|^i$ (inserting double negations for classical connectives) and $|\cdot|^c$ (erasing indices) preserve congruence (7.1.3), yielding conservativity (7.1.4).
- **7.2 Normalization in Ecumenical STT** — re-verifies the Chapter 5–6 preconditions (non-confusing, decidable, has a pre-model) for ecumenical STT; constructs an explicit **pre-model** $\mathcal{M}$ interpreting sorts via reducibility candidates and connectives via the semantic clauses of Definition 6.2.4, concluding that cut-elimination and the ecumenical witness property transfer to ecumenical STT — "a truly ecumenical formalization of mathematics" combining classical expressivity with constructive proof-theoretic properties. : [[Theory-U-and-Ecumenical-Fragments|Link]]

**Key Questions:**
1. Why is higher-order ecumenical STT encoded via combinators and an explicit application symbol over a first-order signature, rather than given a native higher-order syntax with real binders?
2. What is the role of the predicate $\varepsilon$ in separating "propositional contents" (terms of sort $o$) from actual propositions, and why is this separation needed to combine higher-order quantification with the indexed ecumenical connectives?
3. What does it take to verify that ecumenical STT satisfies the abstract preconditions established generically in Chapters 5–6, and why must confluence/termination be re-proved rather than inherited automatically?

---

### Chapter 8: Pure type systems (pp. 77–88)

**Summary:** Introduces Pure Type Systems (PTSs), the general framework of typed $\lambda$-calculi (extending Barendregt's $\lambda$-cube and encompassing STT, System F, dependent types) underlying Dedukti and most contemporary proof assistants. Defines PTS syntax, $\beta$-reduction, the typing system, and key metatheoretic properties (subject reduction, uniqueness of types, decidability questions), setting up vocabulary used throughout the rest of the thesis. : [[Pure-Type-Systems|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **8.1 Introduction to PTSs** — a **pure type system** (Def. 8.1.1) is a triple $\langle S,A,R\rangle$: sorts $S$, axioms $A\subset S\times S$ (which sorts type which sorts), and rules $R\subset S\times S\times S$ (well-typedness of dependent products $\Pi x{:}A.B$). Barendregt's $\lambda$-cube arises from different rule combinations over sorts TYPE/KIND.
- **8.2 Syntax of PTS terms** — terms $t,u,M,N,A,B ::= x \mid s \mid MN \mid \lambda x{:}A.M \mid \Pi x{:}A.B$; free/bound variables, substitution, contexts with a hole; **stability by context/substitution** define a **congruence**; $\alpha$-equivalence as the context-stable closure of variable renaming, giving the quotient set $\Lambda(V,S)$. : [[Pure-Type-Systems|Link]]
- **8.3 Computation in PTSs: the $\beta$-reduction** — $(\lambda x{:}A.M)\,t\to_\beta M[x:=t]$ as the context-stable closure of the base step; general rewrite vocabulary (normalization, strong normalization, confluence, **convergence** = strongly normalizing + confluent). $\beta$-reduction is confluent (Thm. 8.3.4) but *not* normalizing in general, witnessed by $\Delta=\lambda x{:}y.\,xx$ and $\Omega=\Delta\Delta$ — a diagonal-argument construction analogous to Russell's paradox / the halting problem, motivating a typing discipline.
- **8.4 Typing system of PTSs** — contexts $\Gamma$, well-formedness $\vdash_P\Gamma\ \mathrm{wf}$, typing judgment $\Gamma\vdash_P t:T$; rules (empty), (decl), (sort) (using axioms $A$), (var), (app), (prod) (using rules $R$), (conv) (assimilating types up to $\equiv_\beta$), (abs). : [[Pure-Type-Systems|Link]]
- **8.5 Properties of PTSs** — properties (Def. 8.5.1): functionality, semi-fullness, fullness, injectivity. Key metatheorems (Thm. 8.5.2): **product injectivity** ("the Key Lemma": $\Pi x{:}A_1.B_1\equiv_\beta \Pi x{:}A_2.B_2 \Rightarrow A_1\equiv_\beta A_2 \wedge B_1\equiv_\beta B_2$), subject reduction, type correctness, inversion, uniqueness of types (for functional PTSs). STT is normalizing (Thm. 8.5.3, Tait's reducibility candidates), but this does **not** generalize: the minimal single-sort PTS $(*)$ is non-normalizing, related to **Girard's paradox** (an adaptation of Burali-Forti's paradox), exhibited in Girard's systems $\lambda U/\lambda U^-$; Agda avoids this via an infinite universe hierarchy $\mathrm{SET}_i$.
- **8.6 Decision problems over PTSs** — type-checking, typeability, and type reconstruction (Def. 8.6.1) are in general undecidable for PTSs. : [[Pure-Type-Systems|Link]]

**Key Questions:**
1. Why does typing terms with a PTS's sorts/axioms/rules block the diagonal-argument construction ($\Delta\Delta$) that makes untyped $\beta$-reduction non-normalizing, and why doesn't this argument generalize to guarantee normalization for every PTS?
2. What is product injectivity ("the Key Lemma"), and why is it indispensable to proving subject reduction for $\beta$-reduction?
3. How does Girard's paradox show that the single-sort PTS $(*)$ fails to be normalizing, and what design choice (à la Agda's universe hierarchy) restores normalization?

---

### Chapter 9: Pure type systems modulo rewriting (pp. 89–96)

**Summary:** Extends PTSs with user-defined computational content — a typed signature $\Sigma$ of constants plus a rewrite system $R$ — motivated by the need to *define* mathematical objects (e.g. addition on naturals) rather than only declare them axiomatically. Surveys the spectrum from definition-by-equality to $\delta$-reduction to $\iota$-reduction for inductive recursors, gives the general PTS-modulo-theory framework and its extended typing rules, and identifies the well-typedness conditions a theory $(\Sigma,R)$ must satisfy to preserve the good metatheoretic properties of Chapter 8 — the technical bridge to the $\lambda\Pi$-calculus modulo theory of Chapter 10. : [[Pure-Type-Systems|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **9.1 Motivation** — three ways to give computational content to a declared constant: (1) **definition by equality** — axioms $c=t$ plus equality rules, as in HOL Light (which lacks a formulae-as-types conversion rule and so needs an explicit $\beta$-equality axiom); (2) **definition by $\delta$-reduction** — $c\to_\delta t$ folded into the conversion relation $\equiv_{\beta\delta}$, letting definitional unfolding happen "for free" during typing; (3) **recursor by $\iota$-reduction** — recursion principles for inductive types (e.g. $(R\,e\,f)\,0\to_\iota e$, $(R\,e\,f)\,(S\,n)\to_\iota f\,[(R\,e\,f)\,n]\,n$) as rewrite rules, as in Coq's primitive inductive types; $\iota$ is genuinely **higher-order** (the metavariable $f$ is used as a function on the right-hand side), and higher-order rewriting metatheory (confluence, termination, modularity) is comparatively undeveloped.
- **9.2 PTSs modulo theory** — **signature** $\Sigma=c_1{:}T_1,\dots,c_n{:}T_n$ (Def. 9.2.1); **rewrite rule** $(\ell,r)$ with $FV(r)\subseteq FV(\ell)$ (Def. 9.2.2), generating a rewrite system and its associated conversion $\equiv_{\beta R}$; **PTS modulo theory** $P/\Sigma,R$ (Def. 9.2.3) extends $P$'s typing with a relaxed (conv) rule using $\equiv_{\beta R}$ and a (const) rule. **Well-typedness of a theory** (Def. 9.2.4) requires $\Sigma$ well-typed, $R$ type-preserving, and product injectivity modulo $\Sigma,R$; a pathological theory violating all three (collapsing TYPE and KIND) shows what fails without these constraints (Example 9.2.2). Theorem 9.2.5 (after Blanqui): for a well-typed theory, all the good PTS metatheoretic properties are recovered modulo $\equiv_{\beta R}$. : [[Deduction-Modulo-Theory|Link1]], [[The-Lambda-Pi-Calculus-Modulo-Theory|Link2]]

**Key Questions:**
1. What is the essential technical distinction between definition by equality, $\delta$-reduction, and $\iota$-reduction, and why do proof assistants generally prefer folding definitions into the conversion relation rather than treating them as ordinary equality axioms?
2. What can go wrong (subject reduction, type correctness, product injectivity) if an arbitrary rewrite system is added to a PTS's conversion rule without the well-typedness conditions of Definition 9.2.4?
3. Why is $\iota$-reduction for recursors over inductive types an inherently higher-order rewrite rule, and why does this matter for the theory's metatheoretic tractability?

---

### Chapter 10: The λΠ-calculus modulo theory (pp. 97–106)

**Summary:** Defines the $\lambda\Pi$-calculus modulo theory — the specific, well-behaved PTS (based on the Edinburgh Logical Framework) used as the thesis's central logical framework for interoperability — and its reference implementation Dedukti, with detailed concrete syntax. Demonstrates the framework's expressive power by encoding minimal predicate logic via formulae-as-types (§10.3.1) and arbitrary functional PTSs via a universe-and-decoding-function technique (§10.3.2), each with soundness/conservativity/decidability theorems — operationalizing the abstract machinery of Chapters 8–9 into the concrete tool used for the rest of the thesis. : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 An overview of $\lambda\Pi$-calculus modulo theory** — the specific PTS with sorts $\{\mathrm{TYPE},\mathrm{KIND}\}$, axiom $(\mathrm{TYPE},\mathrm{KIND})$, and rules $(\mathrm{TYPE},\mathrm{TYPE},\mathrm{TYPE})$, $(\mathrm{TYPE},\mathrm{KIND},\mathrm{KIND})$; $\lambda\Pi$ is injective, semi-full, functional, and normalizing, hence enjoys subject reduction, product compatibility, and decidable type-checking; by Theorem 9.2.5, any well-typed theory over $\lambda\Pi$ inherits these properties. : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
- **10.2 An implementation of $\lambda\Pi$-calculus modulo theory: Dedukti** — concrete syntax: `Type` for TYPE; constant declaration `new : T.`; arrow `A -> B`; dependent product `x : A -> B`; `def`/`thm` with `:=` (`def` adds a $\delta$-rewrite rule, unfoldable; `thm` keeps only the declaration, opaque and non-unfolding); rewrite rules `[x_1,...,x_n] l --> r.`; abstraction via `=>`. Dedukti's syntax is deliberately minimal — meant as a lightweight target for automatically generated/checked proofs, not manual development; LambdaPi is mentioned as a more user-friendly alternative implementation. : [[The-Lambda-Pi-Calculus-Modulo-Theory|Link]]
- **10.3.1 Formulae and proofs** — two ways to represent propositions: directly as types, or via a dedicated type `Prop : Type` with an embedding `Prf : Prop -> Type`; **Minimal Predicate Logic (MPL)** (Def. 10.3.1) restricted to $\top,\bot,\Rightarrow,\forall$; encoding via typed constructor functions per connective (Curry–Howard) versus via rewrite rules directly equating `Prf` of a connective with its expected functional type — the rewriting approach yields shorter proof terms at the cost of no longer recording which inference rule was used. Theorem 10.3.2: the resulting theory is well-typed, sound and conservative w.r.t. MPL derivability, with decidable type-checking.
- **10.3.2 Programs and types** — **shallow** encodings (source abstractions/applications map directly onto $\lambda\Pi$ ones, preserving $\beta$-redexes) versus **deep** encodings (source syntax reified as an inductive data type with its own separately-axiomatized reduction, enabling structural analysis but losing computational faithfulness); general encoding of any functional PTS $P=\langle S,A,R\rangle$ into $\lambda\Pi$ modulo theory (after Cousineau–Dowek) via per-sort universe types `Univ_s` and decoding functions `elts_s`, per-axiom elements, and per-rule product-constants `Prod_s1_s2_s3`. Theorem 10.3.3 (Cousineau–Dowek): the encoded theory is well-typed, sound and conservative w.r.t. $P$'s own typing relation, with decidable type-checking.

**Key Questions:**
1. What is the practical trade-off between axiom-based and rewrite-based encodings of a logic's inference rules in Dedukti — what is gained and lost by moving proof steps into the conversion relation?
2. Why does encoding an arbitrary functional PTS into $\lambda\Pi$-calculus modulo theory require separate `Univ_s`/`elts_s` pairs per sort rather than directly reusing $\lambda\Pi$'s own TYPE/KIND?
3. Why does the thesis favor shallow over deep encodings of source term syntax, given that deep encodings would seem to offer more powerful structural manipulation of terms?

---

### Chapter 11: Modularity of PTS theories (pp. 109–112)

**Summary:** Motivates the study of modularity for computational PTS theories: incremental (module-by-module) type-checking of user-defined theories and improved interoperability between proof-system embeddings both require understanding when extending or combining well-typed theories preserves well-typedness. Surveys Saillard's strongly/weakly well-formed theory framework, previews the chapter roadmap (extension in Ch. 12, fragmentation in Ch. 13, application to ecumenical logic in Ch. 14), and gives four counterexamples showing modularity can fail under union, extension, and fragmentation. : [[Modularity-of-Type-Theories|Link]]

**Key Definitions & Concepts:**
- **Strongly/weakly well-formed theories** — Saillard's notions, used in Dedukti's type-checker, the target framework for modular typing. **Theory extension** — adding declarations/rewrite rules to an existing theory.
- **Four non-modularity counterexamples (§11.2)** — non-modular theory union (product injectivity fails for the union of two individually well-typed theories); non-modular theory extension (a rewrite rule that stops being type-preserving once a new case is added, letting a variable instantiate to a term of a different type); two non-modular fragmentation examples showing a term typable in an extended theory need not be typable in the original fragment once a rewrite rule is added, whether via a retyped product target or via lost confluence.

**Key Questions:**
1. Why does naively type-checking "original theory + new declarations together" fail as a practical module system, and which property (injectivity, confluence, type-preservation) breaks in each counterexample?
2. What is the intended payoff of a theory like theory U for the interoperability pipeline described in Chapter 10?

---

### Chapter 12: Modular definition of computational theories (pp. 113–126)

**Summary:** Builds the formal machinery — theory contexts — for defining PTS theories incrementally, then reconstructs Saillard's strongly well-formed (swf) and weakly well-formed (wwf) frameworks (fixing a circularity in the original "permanently well-typed rewrite rule" notion and generalizing from Dedukti/$\lambda\Pi$ to general functional, injective, semi-full PTSs) to guarantee that declaration-by-declaration typing suffices for full well-typedness — enabling modular, incremental type-checking. : [[Modularity-of-Type-Theories|Link1]], [[Deduction-Modulo-Theory|Link2]], [[Pure-Type-Systems|Link3]]

**Key Definitions & Concepts by Section:**
- **12.1 Theory contexts** — a **theory context** $\Gamma$ is an inductively built list of constant declarations $(c{:}T)$ and rewrite-rule-set declarations $\Xi$; the **contextual theory** $T(\Gamma)=(\Sigma(\Gamma),R(\Gamma))$ extracted from it; $\Gamma$ is well-typed iff $T(\Gamma)$ is. : [[Modularity-of-Type-Theories|Link]]
- **12.2.1 Strongly well formed theory context (swf)** — **algebraic terms**: those built only from constants applied to constants/variables ($t,u ::= c \mid t\,u \mid t\,x$); a rewrite rule $u \hookrightarrow v$ is swf in $\Gamma$ if $u$ is algebraic and both sides are typable at the same type; swf contexts are built inductively requiring confluence of $\to_{\beta\Gamma,\Xi}$. The type of an algebraic term is stable under swf theory extension (Lemma 12.2.3), yielding **Theorem 12.2.6** (swf rules stay well-typed under swf extension) and **Theorem 12.2.7** (swf contexts are well-typed). : [[Modularity-of-Type-Theories|Link]]
- **12.2.2 Weakly well formed theory context (wwf)** — motivated because swf excludes common rules whose left-hand side isn't itself well-typed but whose *well-typed instances* preserve type; introduces **static vs. definable symbols** (only definable symbols may head a rule's LHS), a bidirectional constraint-generation type inference/checking system, **constraints and solutions** $\mathrm{Sol}_\Gamma(V,C)$, **safe extensions**, and **permanent presolutions** $\mathrm{PreSol}_\Gamma(V,C)$ — substitutions covering every solution in every safe extension up to convertibility. A rule is **weakly well-formed** if its LHS's inferred constraints admit a presolution making both sides typable at the same type. **Theorem 12.2.12**: wwf rules stay well-typed in safe extensions; **Theorem 12.2.14**: wwf theory contexts are well-typed. : [[Modularity-of-Type-Theories|Link]]

**Key Questions:**
1. What is the structural difference between a strongly and a weakly well-formed rewrite rule, and why does wwf need the machinery of constraints/presolutions while swf does not?
2. Why was the earlier "permanently well-typed rewrite rule" notion dropped, and what circularity did it introduce?
3. What must be true of a theory extension for it to preserve the well-typedness of a swf or wwf rule already in place (i.e. what makes an extension "safe")?

---

### Chapter 13: Fragmentation of theories (pp. 127–136)

**Summary:** Addresses the converse direction to Chapter 12: given a large combined theory (like theory U), can we tell which subtheory (fragment) a given well-typed proof belongs to, purely from which symbols it uses, without tracking rewriting inside the proof term? Defines dependency and fragments, states the **fragment theorem**, proves progressively stronger and less-hypothesis-laden versions of it, and shows that fragments of swf/wwf theories are themselves swf/wwf — so the fragment theorem applies "for free" to any theory type-checked via Dedukti's algorithm. : [[Theory-Fragmentation|Link]]

**Key Definitions & Concepts by Section:**
- **13.1.1 Fragments** — a set of symbols $\Sigma_1$ **depends on** symbol $s$ if $s$ occurs in the type of a symbol in $\Sigma_1$ or on the RHS of a rule whose LHS symbols are all in $\Sigma_1$; a **fragment** $(\Sigma_1,R_1)$ is a sub-theory closed under dependency. : [[Theory-Fragmentation|Link]]
- **13.1.2 The fragment theorem** — **Conjecture 13.1.1**: if $\Gamma;\Delta\vdash t:A$ is derivable and $t$, $A$, and $\Delta$'s types all lie in fragment $F$, then $F;\Delta\vdash t:A$ is already derivable — no hidden use of symbols outside $F$ is needed. Supporting lemmas on fragment closure under reduction and conversion; **Lemma 13.1.6 (Weak fragment theorem)** proves the conjecture under extra hypotheses (both $F,\Gamma$ well-typed and confluent). : [[Theory-Fragmentation|Link]]
- **13.1.3** — shows the extra "$\Delta$ well-formed in $F$" hypothesis is actually derivable from the others, leaving only well-typedness and confluence of $F$ to eliminate.
- **13.2 Fragments of strongly well formed theories** — fragments of swf theory contexts are themselves swf (Lemma 13.2.2); **Theorem 13.2.3**: the fragment theorem holds outright for swf $\Gamma$, with no side-conditions needed. : [[Theory-Fragmentation|Link]]
- **13.3 Fragments of weakly well formed theories** — **13.3.1 Type inference and fragmentation**: type inference commutes with fragmentation. **13.3.2 Finding a presolution in a fragment**: the `find_presolution` procedure is complete for normalizing theories and behaves identically on a fragment as on the whole theory, so establishing wwf-ness algorithmically for the whole theory automatically establishes it for any fragment. : [[Theory-Fragmentation|Link]]

**Key Questions:**
1. Why can't the fragment theorem be stated and proved unconditionally for an arbitrary theory context — what do the confluence and well-typedness side-conditions rule out?
2. What is the practical significance of the fragment theorem for interoperability: how does it let one determine "which axioms were used" in a proof imported into theory U, given that proof terms carry no syntactic trace of rewriting?
3. Why does swf give the fragment theorem "for free" while wwf requires the additional algorithmic argument about `find_presolution`?

---

### Chapter 14: Application to ecumenical logics (pp. 137–160)

**Summary:** Applies the modularity/fragmentation machinery of Chapters 12–13 to a concrete case: encoding ecumenical logic (echoing NE from Part II, but built via a *shallow* higher-order encoding exploiting that Dedukti/$\lambda\Pi$ is itself higher-order) inside theory U. Defines Constructive/Ecumenical Predicate Logic and STT as explicit Dedukti theories, proves they are well-typed fragments of theory U (hence subject to the fragment theorem and subject reduction "for free"), and does the harder metatheoretic work the general framework doesn't give: normalization (via a super-consistency argument), decidability of type-checking, and soundness/conservativity with respect to first- and higher-order reference systems (NJ/NK and HOL-$\lambda$/HOL-$\lambda$I), concluding with the consistency of Ecumenical STT. : [[Proof-Normalization-in-Ecumenical-Logic|Link1]], [[Ecumenical-Logics|Link2]]

**Key Definitions & Concepts by Section:**
- **14.1 Ecumenical STT and its subtheories** — base encoding via `SET`, `El`, `PROP`/`Prf`; connectives defined by rewriting (Curry–Howard style for $\Rightarrow$, Russell style otherwise), e.g. $\mathrm{Prf}(A\Rightarrow B)\hookrightarrow \mathrm{Prf}(A)\to\mathrm{Prf}(B)$. **Constructive Predicate Logic** $=(\Sigma^{FO}_c,R^{FO}_c)$; **Ecumenical Predicate Logic** extends it with classical connectives defined via double negation, e.g. $\mathrm{Prf}_c \hookrightarrow \lambda x{:}\mathrm{PROP}.\ \mathrm{Prf}(\lnot\lnot x)$. **Constructive STT** and **Ecumenical STT** extend predicate logic to a higher-order theory of propositions. : [[Higher-Order-Ecumenical-Type-Theory|Link1]], [[Theory-U-and-Ecumenical-Fragments|Link2]], [[Ecumenical-Logics|Link3]]
- **14.2 Properties of the logical fragments of theory U** — all four fragments (constructive/ecumenical, first-/higher-order) are well-typed (Lemma 14.2.1), giving subject reduction and the fragment theorem "for free" via Chapter 13. : [[Theory-Fragmentation|Link1]], [[Theory-U-and-Ecumenical-Fragments|Link2]], [[Interoperability-of-Proof-Assistants|Link3]]
  - **14.2.1 Normalization** — normalization is not modular for higher-order rewriting, so must be proved directly. **Full ordered complete $\Pi$-algebras** and **models valued in a $\Pi$-algebra**; a theory is **super-consistent** if it has a model in every such algebra. **Theorem 14.2.7**: $\beta$-reduction is strongly normalizing on well-typed terms of any super-consistent theory; **Theorem 14.2.8**: Minimal STT is super-consistent. Extends this model to **Constructive STT** (strong $\beta$-normalization), then derives **Corollary 14.2.3**: Ecumenical STT is *weakly* normalizing (via a 3-stage strategy: eliminate classical connectives, $\beta$-normalize, eliminate remaining constructive connectives), hence **Corollary 14.2.4**: type-checking in Ecumenical STT is decidable. Strong normalization of Ecumenical STT is left as **Conjecture 14.2.1**.
- **14.3 First order ecumenism** — soundness (14.3.1) and conservativity (14.3.2) of Constructive Predicate Logic w.r.t. NJ, correcting an error in prior proofs that mishandled free variables occurring only inside subproofs (fixed via a **witness constant**); soundness/conservativity of Ecumenical Predicate Logic w.r.t. NK, built by composing with the Kolmogorov double-negation translation. : [[Higher-Order-Ecumenical-Type-Theory|Link1]], [[Theory-U-and-Ecumenical-Fragments|Link2]]
- **14.4 Higher order ecumenism** — reference systems **HOL-$\lambda$** (intensional) and its constructive fragment **HOL-$\lambda$I** (no excluded middle); soundness and, after a chain of normal-form lemmas exploiting Constructive STT's normalization, conservativity of Constructive STT w.r.t. HOL-$\lambda$I via a **shallow embedding**; soundness and conservativity of Ecumenical STT w.r.t. full HOL-$\lambda$ via a higher-order double-negation translation, culminating in **Corollary 14.4.3: Ecumenical STT is consistent**. : [[Higher-Order-Ecumenical-Type-Theory|Link1]], [[Deduction-Modulo-Theory|Link2]], [[Theory-U-and-Ecumenical-Fragments|Link3]]

**Key Questions:**
1. Why does the fragment theorem/subject reduction follow "for free" from Chapter 13 for theory U's logical fragments, while normalization, soundness, and conservativity all require substantial fresh proof work in this chapter?
2. What is super-consistency, and why is proving it for Constructive STT the key stepping stone to normalization, decidability, and (eventually) consistency of Ecumenical STT?
3. What specific error in prior soundness proofs of Constructive Predicate Logic does this chapter identify and fix, and why does the "witness" trick work?
4. Why is the embedding of first-order logic into theory U "deep" while the embedding of HOL-$\lambda$ is "shallow," and why does the shallow embedding complicate the higher-order double-negation translation compared to the first-order case?

---

### Conclusion (pp. 161–163)

**Summary:** Frames the thesis's two threads as two approaches to combining computational theories. $\mathrm{NE}/\!\equiv$ (Part II) gives a framework for axiomatic and computational ecumenical theories with a normalization procedure and an ecumenical STT; the modularity/fragmentation results (Parts III–IV) generalize theory-extension and -fragmentation results, culminating in the fragment theorem, useful for classifying proofs in theory U by the axioms they actually depend on. Applying this machinery to theory U's ecumenical fragments (Ch. 14) yields normalization, consistency, decidable type-checking, soundness, and conservativity, supporting theory U's use for storing/rechecking/translating/hybridizing proofs across assistants. Extending these results to the entirety of theory U (not just its logical fragments) remains open, as does the behavior of hybrid ecumenical propositions/proofs. Future work: ecumenical versions of richer mathematical theories, constructivization procedures, semantics for NE, and ecumenical proof databases as a compact format preserving constructive information. : [[Proof-Normalization-in-Ecumenical-Logic|Link1]], [[Ecumenical-Logics|Link2]]

**Key Questions:**
1. What concrete open problems does the thesis leave for future work regarding theory U as a whole, as opposed to its individual logical fragments?
2. Why might "hybrid" ecumenical propositions/proofs (mixing classical and intuitionistic connectives) behave differently across different ecumenical systems, and what partial answer does normalization already give for Ecumenical STT?
