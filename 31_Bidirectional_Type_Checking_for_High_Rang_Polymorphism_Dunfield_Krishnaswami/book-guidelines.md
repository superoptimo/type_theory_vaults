# Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism — Guidelines

## Header

**Title:** Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism
**Author(s):** Jana Dunfield and Neelakantan R. Krishnaswami (Max Planck Institute for Software Systems)
**Publication:** ICFP '13, September 25–27, 2013, Boston, MA, USA (2021 revised version, correcting author information and reference URLs)

**Brief Summary:**
This paper extends the proof-theoretic account of bidirectional typechecking to full higher-rank (predicative) polymorphism, i.e., predicative System F. It gives a declarative, bidirectional type system that guesses quantifier instantiations and enjoys properties such as stability under $\eta$-reduction, and then presents a remarkably simple algorithm — built on ordered contexts containing existential type variables — that is proved sound, complete, and decidable with respect to that declarative specification.

**Intent of the Author:**
The authors want to close a gap in the theory of bidirectional typechecking: while the proof-theoretic account had been extended to refinements and intersection/union types, no satisfactory account existed for polymorphism. They aim to show that a simple algorithm — requiring no data structure more sophisticated than a list, and no search or backtracking — can be both sound and complete for higher-rank polymorphism, so that programmers can predict exactly where type annotations are needed.

**Intended readership:** researchers and language implementors already familiar with type theory, sequent calculus/proof theory, and System F; the paper is a dense, rule-heavy conference paper rather than an introductory text.

---

## Topic List

1. **Bidirectional Typechecking Foundations** : [[Bidirectional-Typechecking-Foundations|Link]]
   - Checking mode versus synthesis mode : [[Declarative-Type-System|Link]]
   - Proof-theoretic grounding via focalization : [[Bidirectional-Typechecking-Foundations|Link]]
   - Normal forms and neutral terms corresponding to checking and synthesis
   - Type annotations required only at redexes : [[Bidirectional-Typechecking-Foundations|Link]]
   - Application judgment for spine-form applications : [[Declarative-Type-System|Link1]], [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link2]]
2. **The Problem of Polymorphism in Bidirectional Systems** : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
   - Failure of type assignment System F to preserve typability under $\eta$-reduction : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
   - Undecidability of subtyping for impredicative polymorphism : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link1]], [[Declarative-Type-System|Link2]]
   - Restriction to predicative polymorphism : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
   - Modeling instantiation via subtyping : [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link]]
3. **Declarative Type System** : [[Declarative-Type-System|Link]]
   - Checking, synthesis, and application judgments : [[Declarative-Type-System|Link]]
   - Subtyping as a more-polymorphic-than relation : [[Declarative-Type-System|Link]]
   - The $\forall L$ and $\forall R$ subtyping rules
   - Let-generalization and the cut rule : [[Declarative-Type-System|Link]]
   - Relationship to type assignment System F : [[Declarative-Type-System|Link]]
   - Substitution and inverse substitution theorems : [[Declarative-Type-System|Link]]
   - Annotation removal theorem : [[Declarative-Type-System|Link]]
   - Soundness of the $\eta$ law
4. **Algorithmic Contexts** : [[Algorithmic-Contexts|Link]]
   - Ordered contexts with existential type variables
   - Unsolved versus solved existential variables
   - Complete contexts : [[Algorithmic-Contexts|Link]]
   - Context application as substitution : [[Algorithmic-Contexts|Link]]
   - Hole notation for contexts : [[Algorithmic-Contexts|Link]]
   - Input and output contexts : [[Algorithmic-Contexts|Link]]
5. **Algorithmic Subtyping and Instantiation** : [[Algorithmic-Subtyping-and-Instantiation|Link]]
   - Algorithmic subtyping rules : [[Algorithmic-Subtyping-and-Instantiation|Link1]], [[Algorithmic-Typing|Link2]]
   - Articulation of existential variables : [[Algorithmic-Subtyping-and-Instantiation|Link]]
   - The instantiation judgment : [[Metatheory-of-the-Algorithm|Link]]
   - Instantiate-to-subtype and instantiate-to-supertype : [[Algorithmic-Subtyping-and-Instantiation|Link]]
   - The reach rules for scope-constrained existentials : [[Algorithmic-Subtyping-and-Instantiation|Link]]
6. **Algorithmic Typing** : [[Algorithmic-Typing|Link]]
   - Typing rules mirroring the declarative system : [[Declarative-Type-System|Link1]], [[Algorithmic-Typing|Link2]]
   - The existential-application rule with no declarative analogue : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Typing|Link2]]
   - Context extension as a metatheoretic invariant : [[Algorithmic-Typing|Link]]
7. **Metatheory of the Algorithm** : [[Metatheory-of-the-Algorithm|Link]]
   - Context extension judgment : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Contexts|Link2]], [[Algorithmic-Typing|Link3]]
   - Decidability of instantiation : [[Algorithmic-Subtyping-and-Instantiation|Link1]], [[Metatheory-of-the-Algorithm|Link2]]
   - Decidability of subtyping : [[Algorithmic-Typing|Link]]
   - Decidability of algorithmic typing : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Typing|Link2]]
   - Soundness of instantiation subtyping and typing : [[Metatheory-of-the-Algorithm|Link]]
   - Completeness of instantiation subtyping and typing : [[Metatheory-of-the-Algorithm|Link]]
8. **Design Variations** : [[Design-Variations|Link]]
   - Eliminating type inference for a no-inference bidirectional system
   - Extending toward full Damas-Milner type inference : [[Design-Variations|Link]]
   - Tradeoffs among the $\eta$-law impredicativity and the System F type language : [[Design-Variations|Link]]
9. **Related Approaches to Higher-Rank Type Inference** : [[Related-Approaches-to-Higher-Rank-Type-Inference|Link]]
   - MLF and bounded quantification
   - HML and FPH as System-F-typed alternatives
   - Local type inference and colored local type inference
   - Greedy instantiation and its incompleteness : [[Metatheory-of-the-Algorithm|Link]]
   - Context-based type inference and mixed-prefix unification

---

## Chapter Summaries

### Section 1: Introduction (p. 1)

**Summary:** Motivates bidirectional typechecking's popularity and scalability, identifies the gap in extending its proof-theoretic foundations to higher-rank polymorphism, and previews the paper's two main contributions: a declarative bidirectional calculus and a sound-and-complete algorithm for it.

**Key Definitions & Concepts:**
- Bidirectional typechecking — terms either synthesize a type or are checked against a known type.
- Focalization — the proof-theoretic foundation (Andreoli) underlying bidirectional typechecking, used here to extend it to polymorphism.
- Spine form — representing applications as a sequence of applications to a head, enabling an application judgment $\Psi \vdash A \bullet e \Rightarrow\!\Rightarrow C$.
- Ordered context — the algorithm's central data structure, containing type variables, term variables, and existential variables, used to manage scope precisely.

**Key Questions:**
1. Why does the standard two-judgment (checking/synthesis) formulation of bidirectional typing break down in the presence of polymorphism, motivating the application judgment $\Psi \vdash A \bullet e \Rightarrow\!\Rightarrow C$?
2. What does it mean for the algorithm to be "complete," and what practical consequence does the paper draw from completeness regarding explicit type applications and annotations?

---

### Section 2: Declarative Type System (pp. 2–4)

**Summary:** Presents the declarative, bidirectional specification of higher-rank predicative polymorphism — grounded in subtyping-as-instantiation — and proves its relationship to type-assignment System F, its robustness under substitution, and its stability under $\eta$-reduction, none of which hold for the ordinary type-assignment presentation.

**Key Definitions & Concepts by Section:**
- **2.1 Typing in Detail** — the checking judgment $\Psi \vdash e \Leftarrow A$, synthesis judgment $\Psi \vdash e \Rightarrow A$, and application judgment $\Psi \vdash A \bullet e \Rightarrow\!\Rightarrow C$; rules $\mathrm{Decl1I}$, $\mathrm{Decl}{\to}I$, $\mathrm{Decl}{\forall}I$, $\mathrm{DeclSub}$, $\mathrm{Decl}{\forall}\mathrm{App}$, $\mathrm{Decl}{\to}\mathrm{App}$; the subtyping judgment $\Psi \vdash A \le B$ and its rules $\le\!\forall L$ (guesses an instantiation) and $\le\!\forall R$; let-generalization avoided in favor of preserving cut-admissibility. : [[Metatheory-of-the-Algorithm|Link]]
- **2.2 Bidirectional Typing and Type Assignment System F** — the type-assignment system for predicative System F (Figure 5); Theorem 1 (Completeness of Bidirectional Typing) and Theorem 2 (Soundness of Bidirectional Typing, up to $\beta\eta$). : [[Declarative-Type-System|Link]]
- **2.3 Robustness of Typing** — Theorem 3 (Substitution), Theorem 4 (Inverse Substitution), Theorem 5 (Annotation Removal), Theorem 6 (Soundness of Eta).

**Key Questions:**
1. Why do the authors reject the type-assignment version of System F as their declarative specification, and what specific example (involving $f : 1 \to \forall\alpha.\alpha$) illustrates the problem?
2. How does the application judgment let the calculus instantiate "exactly as many quantifiers as needed," and how does this connect to the $\eta$-law holding?
3. What is the practical import of the Annotation Removal theorem (Theorem 5) for programmers writing bidirectionally-typed code?

---

### Section 3: Algorithmic Type System (pp. 5–8)

**Summary:** Builds the syntax-directed algorithm corresponding to the declarative system, replacing the three "oracular" guessing rules with existential type variables organized in ordered algorithmic contexts, and presents the resulting subtyping, instantiation, and typing rules.

**Key Definitions & Concepts by Section:**
- **3.1 Algorithmic Contexts** — algorithmic contexts $\Gamma$ containing universal variables $\alpha$, term variables $x:A$, and existential variables $\hat\alpha$ (unsolved or solved to a monotype); complete contexts $\Omega$; well-formedness enforcing declaration order; context application $[\Gamma]A$ as substitution; hole notation $\Gamma_0[\Theta]$; input/output contexts written $\Gamma \vdash \cdots \dashv \Delta$. : [[Algorithmic-Contexts|Link]]
- **3.2 Algorithmic Subtyping** — rules $\mathord{<:}\mathrm{Var}$, $\mathord{<:}\mathrm{Unit}$, $\mathord{<:}\mathrm{Exvar}$, $\mathord{<:}{\to}$, $\mathord{<:}\forall L$ (replaces $\alpha$ with a fresh existential $\hat\alpha$, using a scope marker $I_{\hat\alpha}$), $\mathord{<:}\forall R$, $\mathord{<:}\mathrm{InstantiateL}/R$. : [[Algorithmic-Subtyping-and-Instantiation|Link1]], [[Algorithmic-Typing|Link2]]
- **3.3 Instantiation** — the two instantiation judgments $\Gamma \vdash \hat\alpha \mathbin{:=}\!\!< A \dashv \Delta$ and $\Gamma \vdash A \mathbin{=}\!\!\!<: \hat\alpha \dashv \Delta$; rules $\mathrm{InstLSolve}$, $\mathrm{InstLReach}$, $\mathrm{InstLArr}$ (articulation of $\hat\alpha$ into $\hat\alpha_1 \to \hat\alpha_2$), $\mathrm{InstLAllR}$, and their right-hand analogues; worked examples showing instantiation "changing its mind" about which existential to solve. : [[Metatheory-of-the-Algorithm|Link]]
- **3.4 Algorithmic Typing** — rules $\mathrm{Var}$, $\mathrm{Sub}$, $\mathrm{Anno}$, $1I$, $1I\Rightarrow$, $\forall I$, $\forall\mathrm{App}$, ${\to}I$, ${\to}I\Rightarrow$, ${\to}E$, $\hat\alpha\mathrm{App}$ (the one algorithmic rule with no declarative analogue), ${\to}\mathrm{App}$. : [[Algorithmic-Typing|Link]]

**Key Questions:**
1. Why must existential variable declarations preserve strict order in the context, and how does this ordering "aid in enforcing type variable scoping and dependencies"?
2. What problem does "articulation" (as in rule $\mathrm{InstLArr}$) solve, and why must the newly created existentials $\hat\alpha_1, \hat\alpha_2$ be inserted immediately to the left of $\hat\alpha$?
3. Why is $\hat\alpha\mathrm{App}$ the only algorithmic typing rule without a corresponding declarative rule?

---

### Section 4: Context Extension (p. 8)

**Summary:** Introduces the context extension judgment $\Gamma \longrightarrow \Delta$, the central metatheoretic device — capturing "information increase" from an algorithmic context to a more-solved one — used throughout the decidability, soundness, and completeness proofs.

**Key Definitions & Concepts:**
- Context extension $\Gamma \longrightarrow \Delta$ — read "$\Gamma$ is extended by $\Delta$"; all information derivable from $\Gamma$ remains derivable from $\Delta$.
- Extension rules — $\longrightarrow\!\mathrm{ID}$, $\longrightarrow\!\mathrm{Var}$, $\longrightarrow\!\mathrm{Uvar}$, $\longrightarrow\!\mathrm{Unsolved}$, $\longrightarrow\!\mathrm{Solved}$, $\longrightarrow\!\mathrm{Solve}$, $\longrightarrow\!\mathrm{Add}$, $\longrightarrow\!\mathrm{AddSolved}$, $\longrightarrow\!\mathrm{Marker}$.
- Rigidity versus flexibility of extension — declarations persist and preserve order (rigid), while existential solutions may become "more solved" (flexible), enabling scoping and dependency management simultaneously.

**Key Questions:**
1. In what precise sense does context extension formalize "information increase," and why is this the right notion for stating decidability, soundness, and completeness uniformly?
2. How can two different contexts $\Delta$ and $\Omega$ both extend $\Gamma$, with different-looking solutions for the same existential, yet still agree once a complete context is applied to them?

---

### Section 5: Decidability (pp. 8–10)

**Summary:** Proves that instantiation, subtyping, and (consequently) checking/synthesis/application typing judgments are all decidable, using a lexicographic measure combining quantifier count, unsolved-existential count, and a size notion that penalizes solved variables.

**Key Definitions & Concepts by Section:**
- **5.1 Decidability of Instantiation** — Lemma (Instantiation Size Preservation); Lemma (Monotypes Solve Variables), showing that instantiating to a monotype always reduces the number of unsolved existentials. : [[Algorithmic-Subtyping-and-Instantiation|Link1]], [[Metatheory-of-the-Algorithm|Link2]]
- **5.2 Decidability of Algorithmic Subtyping** — the lexicographic measure (S1) quantifier count, (S2) unsolved-existential count, (S3) contextual size $|\Gamma \vdash A|$ (which penalizes solved variables); Theorem 8 (Decidability of Subtyping). : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Typing|Link2]], [[Algorithmic-Subtyping-and-Instantiation|Link3]]
- **5.3 Decidability of Algorithmic Typing** — Theorem 9 (Decidability of Typing), covering synthesis, checking, and application; the induction measure ordering synthesis $\prec$ checking $\prec$ application. : [[Metatheory-of-the-Algorithm|Link1]], [[Algorithmic-Typing|Link2]]

**Key Questions:**
1. Why does contextual size $|\Gamma \vdash A|$ need to "penalize" solved existential variables rather than treating them as trivially small?
2. How does the lexicographic ordering across (S1)–(S3) ensure termination of the subtyping algorithm even though a single rule application does not always shrink every measure component?

---

### Section 6: Soundness (pp. 9–10)

**Summary:** Proves that the algorithmic system faithfully implements the declarative specification: any algorithmic derivation, when a complete context is applied, yields a valid declarative derivation.

**Key Definitions & Concepts:**
- Theorem 10 (Instantiation Soundness) — applying a complete extension $\Omega$ to an instantiation derivation yields a valid declarative subtyping.
- Theorem 11 (Soundness of Algorithmic Subtyping).
- Theorem 12 (Soundness of Algorithmic Typing) — covers checking, synthesis, and application.
- Lemma (Typing Extension) — every algorithmic typing derivation's output context extends its input context.

**Key Questions:**
1. Why is the Typing Extension lemma a necessary stepping stone to proving soundness of algorithmic typing, rather than soundness being provable directly by induction on typing derivations alone?

---

### Section 7: Completeness (p. 10)

**Summary:** Proves the converse of soundness — every declarative derivation is realized by some algorithmic derivation — which is subtler because the algorithm must additionally construct a completing context $\Omega'$ extending both the given completion and its own output.

**Key Definitions & Concepts:**
- Theorem 13 (Instantiation Completeness).
- Theorem 14 (Generalized Completeness of Subtyping).
- Theorem 15 (Completeness of Algorithmic Typing) — three parts, for checking, synthesis, and application.
- The completing context $\Omega'$ — extends both the originally given $\Omega$ and the algorithmic output context, needed because algorithmic derivations introduce fresh existentials absent from the declarative derivation.

**Key Questions:**
1. Why can't completeness simply mirror soundness by showing the algorithmic output context $\Delta$ extends to the given $\Omega$, and what role does the newly constructed $\Omega'$ play instead?

---

### Section 8: Design Variations (pp. 10–11)

**Summary:** Explores two alternative design points from the paper's baseline system: eliminating type inference entirely (a "no-inference" bidirectional variant) and extending toward full Damas-Milner-style type inference with let-generalization.

**Key Definitions & Concepts:**
- No-inference variant — replacing $1I\!\Rightarrow$ and ${\to}I\!\Rightarrow$ with checking-mode rules $1I^{\hat\alpha}$ and ${\to}I^{\hat\alpha}$ that check values against an unknown existential, restoring completeness without synthesis-mode introduction rules.
- Full Damas-Milner extension — a sketched ${\to}I\!\Rightarrow{}'$ rule using a scope marker $I_{\hat\alpha}$ to generalize over unsolved existentials, approximating ML-style let-generalization (not formally proved complete).

**Key Questions:**
1. Why does simply deleting the ${\to}I\!\Rightarrow$/$1I\!\Rightarrow$ synthesis rules break completeness, illustrated by the example of applying $f : \forall\alpha.\alpha\to\alpha$ to $()$?

---

### Section 9: Related Work and Discussion (pp. 11–12)

**Summary:** Situates the paper's algorithm relative to prior higher-rank type inference systems (MLF, HML, FPH, Peyton Jones et al.), other bidirectional/local type inference approaches, and the paper's own three key algorithmic ideas — ordered contexts, the instantiation judgment, and context extension — tracing their lineage and contrasting them with greedy and constraint-based alternatives.

**Key Definitions & Concepts by Section:**
- **9.1 Type Inference for System F** — the lineage from Dunfield (2009), whose decidability/completeness arguments the present paper found unsound, motivating a restart with a distinct instantiation judgment. : [[Related-Approaches-to-Higher-Rank-Type-Inference|Link]]
- **9.2 Other Type Systems** — Pierce and Turner's local type inference; colored local type inference (Odersky et al.). : [[Declarative-Type-System|Link1]], [[Design-Variations|Link2]], [[Related-Approaches-to-Higher-Rank-Type-Inference|Link3]], [[The-Problem-of-Polymorphism-in-Bidirectional-Systems|Link4]]
- **9.3 Our Algorithm** — ordered contexts (avoiding skolemization); the instantiation judgment (contrasted with Cardelli's incomplete greedy algorithm, illustrated by a $\forall\alpha.\alpha\to\alpha\to\alpha$ applied to Cat/Animal example); context extension (compared to Gundry et al.'s structured constraint solving and to Miller's mixed-prefix unification). : [[Metatheory-of-the-Algorithm|Link]]
- Figure 15 (Comparison table) — contrasts MLF, FPH, HML, Peyton Jones et al. (2007), and this paper along three axes: $\eta$-laws, impredicativity, and use of the System F type language.

**Key Questions:**
1. According to Figure 15's comparison, what unique combination of properties (regarding $\eta$-laws, impredicativity, and type language) does this paper's system achieve that no prior system achieved simultaneously?
2. Why was Cardelli's original greedy instantiation algorithm incomplete, and what two mechanisms (reaching, looking under quantifiers) does this paper's algorithm add to recover completeness?
