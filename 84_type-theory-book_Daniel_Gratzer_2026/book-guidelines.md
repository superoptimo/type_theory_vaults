# Principles of Dependent Type Theory — Guidelines

## Header

**Title:** Principles of Dependent Type Theory
**Author(s):** Carlo Angiuli and Daniel Gratzer
**Publication:** Pre-publication draft (2026-03-21), to be published by Cambridge University Press. Originated as shared graduate lecture notes taught simultaneously at Indiana University and Aarhus University in Spring 2024.

**Brief Summary:**
The book gives a modern research-level account of the *design* of full-spectrum dependent type theories — not how to use type theory as a programming language or proof assistant, but how different notions of equality (definitional, propositional, and univalent) shape a theory's mathematical properties. It follows a single throughline — extensional type theory (ETT), then intensional type theory (ITT), then univalent and cubical type theories — showing at each step what principle is gained, what is lost, and why researchers moved on to the next design. A parallel thread develops the categorical semantics (categories with families, orthogonality, local cartesian closure, Artin gluing) needed to state and prove the metatheorems — consistency, canonicity, normalization, decidability — that justify each theory's use in a proof assistant.

**Intent of the Author:**
The authors want readers to understand *why* there are so many dependent type theories rather than one, using notions of equality as a microcosm of that broader design question. After finishing, a reader should be equipped to engage with contemporary research on type theory and understand the motivations behind extensions such as homotopy and cubical type theory.

---

## Topic List

1. **Full-Spectrum Dependent Types** : [[Full-Spectrum-Dependent-Types|Link]]
   - Uniform versus non-uniform type dependency : [[Full-Spectrum-Dependent-Types|Link]]
   - Definitional equality in type-checking : [[Full-Spectrum-Dependent-Types|Link]]
   - The Curry–Howard correspondence : [[Full-Spectrum-Dependent-Types|Link]]
   - Propositional equality and proof by induction : [[Full-Spectrum-Dependent-Types|Link]]
   - Subst as a dependent casting operation

2. **Judgments and the Substitution Calculus** : [[Judgments-and-the-Substitution-Calculus|Link]]
   - Judgments contexts and presuppositions : [[Judgments-and-the-Substitution-Calculus|Link]]
   - Substitution as an explicit algebraic operation : [[Judgments-and-the-Substitution-Calculus|Link]]
   - Weakening and variable judgments
   - De Bruijn indexing : [[Judgments-and-the-Substitution-Calculus|Link]]
   - Categories with families as models of judgmental structure : [[Judgments-and-the-Substitution-Calculus|Link1]], [[Categorical-Semantics-of-Type-Theory|Link2]]

3. **Type Connectives via Universal Properties** : [[Type-Connectives-via-Universal-Properties|Link]]
   - Connectives as mapping-in or mapping-out constructions : [[Type-Connectives-via-Universal-Properties|Link]]
   - Pi and Sigma types internalizing hypothetical judgments and pairs : [[Type-Connectives-via-Universal-Properties|Link]]
   - Extensional equality types and equality reflection : [[Extensionality-versus-Intensionality|Link1]], [[Type-Connectives-via-Universal-Properties|Link2]]
   - The unit type : [[Type-Connectives-via-Universal-Properties|Link]]
   - Inductive types as initial algebras : [[Type-Connectives-via-Universal-Properties|Link]]
   - Large elimination : [[Type-Connectives-via-Universal-Properties|Link]]
   - Universes and universe hierarchies : [[Type-Connectives-via-Universal-Properties|Link]]
   - Cumulativity and universes à la Tarski versus à la Russell : [[Type-Connectives-via-Universal-Properties|Link]]
   - Girard's paradox : [[Type-Connectives-via-Universal-Properties|Link]]
   - Propositions as some types : [[Type-Connectives-via-Universal-Properties|Link]]
   - Propositional truncation and impredicative universes of propositions : [[Type-Connectives-via-Universal-Properties|Link]]
   - Constructivity and independence of the law of excluded middle

4. **Extensionality versus Intensionality** : [[Extensionality-versus-Intensionality|Link]]
   - Equality reflection and extensional type theory : [[Cubical-Type-Theory|Link1]], [[Extensionality-versus-Intensionality|Link2]], [[Univalent-Foundations-and-Homotopy-Type-Theory|Link3]], [[Metatheory-and-Implementation-of-Type-Theory|Link4]]
   - Intensional identity types and the J eliminator : [[Extensionality-versus-Intensionality|Link]]
   - Function extensionality : [[Extensionality-versus-Intensionality|Link]]
   - Uniqueness of identity proofs : [[Extensionality-versus-Intensionality|Link]]
   - The groupoid model : [[Extensionality-versus-Intensionality|Link]]
   - Hofmann's conservativity theorem : [[Extensionality-versus-Intensionality|Link]]
   - Observational type theory : [[Extensionality-versus-Intensionality|Link]]

5. **Metatheory and Implementation of Type Theory** : [[Metatheory-and-Implementation-of-Type-Theory|Link]]
   - Elaboration and bidirectional type-checking : [[Metatheory-and-Implementation-of-Type-Theory|Link]]
   - Normalization structures and decidable equality : [[Metatheory-and-Implementation-of-Type-Theory|Link]]
   - Invertible and injective type constructors
   - Singleton types for named definitions
   - Models of type theory and homomorphisms
   - The syntactic model as initial : [[Metatheory-and-Implementation-of-Type-Theory|Link]]
   - Consistency and canonicity : [[Metatheory-and-Implementation-of-Type-Theory|Link]]
   - Undecidability of extensional equality : [[Metatheory-and-Implementation-of-Type-Theory|Link]]
   - The set model and Grothendieck universes : [[Metatheory-and-Implementation-of-Type-Theory|Link]]

6. **Univalent Foundations and Homotopy Type Theory** : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
   - Homotopy propositions and propositional univalence : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
   - The univalence axiom and equivalences : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
   - Homotopy levels and h-sets : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
   - Higher inductive types : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
   - Synthetic homotopy theory : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
   - The structure identity principle : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]

7. **Cubical Type Theory** : [[Cubical-Type-Theory|Link]]
   - The interval pretype and dimension variables : [[Cubical-Type-Theory|Link]]
   - Path types as a mapping-in identity type : [[Type-Connectives-via-Universal-Properties|Link]]
   - Coercion and homogeneous composition : [[Cubical-Type-Theory|Link]]
   - Cofibrations and faces of cubes : [[Cubical-Type-Theory|Link]]
   - Computational univalence via the Glue type : [[Cubical-Type-Theory|Link]]
   - Canonicity and normalization for cubical type theory : [[Cubical-Type-Theory|Link]]

8. **Categorical Semantics of Type Theory** : [[Categorical-Semantics-of-Type-Theory|Link]]
   - Categories with families and natural models : [[Categorical-Semantics-of-Type-Theory|Link]]
   - Polynomial functors and pullback squares : [[Categorical-Semantics-of-Type-Theory|Link]]
   - Orthogonality and inductive types categorically : [[Categorical-Semantics-of-Type-Theory|Link]]
   - Locally cartesian closed categories : [[Categorical-Semantics-of-Type-Theory|Link]]
   - The coherence and strictness problem : [[Categorical-Semantics-of-Type-Theory|Link]]
   - Global and local universe constructions
   - Artin gluing and canonicity models : [[Categorical-Semantics-of-Type-Theory|Link]]
   - Generalized algebraic theories : [[Categorical-Semantics-of-Type-Theory|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–15)

**Summary:** Motivates full-spectrum dependent types from a programmer's perspective using Agda syntax — length-indexed vectors, a dependently-typed `sprintf`, and inductive proof of type equations — introducing definitional equality, propositional equality, and the Curry–Howard correspondence before the book switches to a purely mathematical presentation in Chapter 2.

**Key Definitions & Concepts by Section:**
- **1.1 Uniform dependency: length-indexed vectors** — a type system as a language's grammar, not an optional static analysis; uniform dependency (types/terms parameterized by types/terms whose head constructor does not vary, e.g. $\mathrm{Vec}\ A : \mathrm{Nat} \to \mathrm{Set}$); refinement-type alternative (Dependent ML, Liquid Haskell) as a simpler but strictly weaker approach.
- **1.2 Non-uniform dependency: computing arities** — full-spectrum dependency (a family of types whose head type constructor varies between indices, e.g. $\mathrm{nary}$); definitional equality as the congruence closure of $\beta\delta\zeta\iota$-reduction (plus $\eta$ at some types) that the type-checker must decide, including on open terms. : [[Full-Spectrum-Dependent-Types|Link]]
- **1.3 Proving type equations** — propositional equality $a \equiv b$ and $\mathrm{refl}$; $\mathrm{subst}$ as the dependent casting operation between provably-equal indices of a dependent type; the propositions-as-types (Curry–Howard) correspondence — dependent functions as universally quantified proofs, non-dependent functions as implications, products as conjunctions.

**Key Questions:**
1. Why can't the equation $\mathrm{filterLen}\ (\lambda x \to \mathrm{false})\ l \equiv 0$ be established by evaluation alone, and what role does $\mathrm{subst}$ play in casting around this gap?
2. What distinguishes uniform from non-uniform (full-spectrum) type dependency, and why does the refinement-type approach handle only the former?
3. In what sense are terms of type $a \equiv b$ different in kind from terms of type $\mathrm{Nat}$ or $A \to B$, even though the propositions-as-types correspondence treats both as "just types"?

---

### Chapter 2: Extensional type theory (pp. 17–88)

**Summary:** Defines extensional type theory (ETT) as a mathematical object built from four judgments (contexts, substitutions, types, terms) via an explicit substitution calculus, then populates it with connectives, arguing each is either a *mapping-in* (natural isomorphism) or *mapping-out* (initial-algebra-style) universal property internalizing some piece of judgmental structure. : [[Cubical-Type-Theory|Link1]], [[Categorical-Semantics-of-Type-Theory|Link2]], [[Extensionality-versus-Intensionality|Link3]], [[Metatheory-and-Implementation-of-Type-Theory|Link4]]

**Key Definitions & Concepts by Section:**
- **2.1 The simply-typed lambda calculus** — judgments $A\ \mathrm{type}$ and $\Gamma \vdash a : A$; introduction/elimination rules; $\beta/\eta$-equivalence as a quotient rather than an evaluation relation; preterms versus intrinsically-typed terms.
- **2.2 Towards the syntax of dependent type theory** — the context-relative type judgment $\Gamma \vdash A\ \mathrm{type}$; presuppositions; weakening made explicit via $-[p]$; de Bruijn indexing. : [[Full-Spectrum-Dependent-Types|Link1]], [[Categorical-Semantics-of-Type-Theory|Link2]], [[Metatheory-and-Implementation-of-Type-Theory|Link3]]
- **2.3 The calculus of substitutions** — the four basic and three equality judgments; a substitution $\Delta \vdash \gamma : \Gamma$ as "a term of type $\Gamma$"; the category of contexts and substitutions; weakening $\mathbf{p}$, the variable $\mathbf{q}$, the terminal substitution $\mathbf{!}$, and substitution extension $\gamma.a$; an informal first look at categories with families. : [[Judgments-and-the-Substitution-Calculus|Link]]
- **2.4 Internalizing judgmental structure: $\Pi, \Sigma, \mathrm{Eq}, \mathrm{Unit}$** — the slogan that a connective is a natural type-former together with a natural isomorphism to some judgmentally-determined structure; $\Pi$ internalizing the hypothetical judgment $\Gamma.A \vdash - : B$; $\Sigma$ internalizing pairs; $\mathrm{Eq}$ internalizing term equality via **equality reflection** (the rule that defines ETT); $\mathrm{Unit}$ internalizing the one-element judgment.
- **2.5 Inductive types: $\mathrm{Void}, \mathrm{Bool}, +, \mathrm{Nat}$** — the mapping-out characterization ("every type believes $X$ is empty / has two elements"); initial algebras for a signature, with $\mathrm{Nat}$ as the initial $(1 \sqcup -)$-algebra; displayed algebras and homomorphisms; unicity via $\mathrm{Eq}$ — the $\eta$-rules for inductive types are derivable from equality reflection and so need not be primitive.
- **2.6 Universes: $U_0, U_1, U_2, \dots$** — large elimination (a type-valued eliminator that fails to be structurally recursive for $\mathrm{Nat}$); universes à la Tarski ($U$, $\mathrm{El}$) versus à la Russell; Girard's paradox (a universe of itself, $U : U$, is inconsistent — Hurkens' construction); the universe hierarchy with strict lift operations and cumulativity.
- **2.7★ Propositions and propositional truncation** — propositions as some types: a proposition is a type whose terms are all equal ($\mathrm{isProp}$); universes of propositions $\mathrm{Prop}_i$; the illusion of choice — $\Sigma$-types are not existentials, since the naive type-theoretic axiom of choice is trivially provable but is not the real axiom of choice; propositional truncation $\mathrm{Trunc}(A)$ (a mapping-out construction to propositions only) recovering $\exists$ and $\vee$; impredicative universes of propositions; constructivity of type theory — LEM, double-negation elimination, and choice are independent, while Church's thesis is consistent but not classically true.

**Key Questions:**
1. Why must $\Sigma$-types fail to be existential quantifiers under "propositions as some types," and what specifically does propositional truncation add that $\Sigma$ lacks?
2. Why is the naive Σ-based "type-theoretic axiom of choice" trivially provable, and why does this not count as proving the real axiom of choice?
3. Why does removing the code-for-$U$-in-$U$ round-trip avoid Girard's paradox, and what does a universe hierarchy buy over a single universe?

---

### Chapter 3: Metatheory and implementation (pp. 89–131)

**Summary:** Bridges the mathematical definition of type theory to how proof assistants actually implement it, via elaboration algorithms, then studies the metatheoretic properties — normalization, invertibility, consistency, canonicity — needed for that implementation to be sound, culminating in two proofs that ETT's equality is undecidable, which motivates the shift to intensional type theory in Chapter 4. : [[Metatheory-and-Implementation-of-Type-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 A judgmental reconstruction of proof assistants** — proof assistants understood as elaborators; pretypes and preterms; algorithmic judgments $\Gamma \vdash \tau\ \mathrm{type} \rightsquigarrow A$ and $\Gamma \vdash e : A \rightsquigarrow a$; type-checking reduced to deciding type equality.
- **3.2 Metatheory for type-checking** — a normalization structure (an injective, computable pair of normal-form functions on types and terms) and the algorithmic equality it induces; bidirectional type-checking (checking on introduction forms, synthesizing on elimination forms) via $\Rightarrow$/$\Leftarrow$ judgments; injective and invertible type constructors. : [[Metatheory-and-Implementation-of-Type-Theory|Link]]
- **3.3★ A case study in elaboration: definitions** — singleton types $\mathrm{Sing}(A,a)$ used to encode named, typed definitions ("let is no longer $\lambda$") without breaking normalization.
- **3.4 Models for metatheory** — a general model of type theory (sets of contexts, substitutions, types, terms plus operations, closed under every rule); homomorphisms of models; the syntactic model as the initial model; consistency (no closed term of $\mathrm{Void}$); canonicity (every closed $\mathrm{Bool}$ term is $\mathrm{true}$ or $\mathrm{false}$); canonicity models understood as "gluing models."
- **3.5★ The set model of type theory** — Grothendieck universes, circumventing "the set of all sets"; an $(\omega{+}1)$-indexed hierarchy $V_0 \in \cdots \in V_\omega$; contexts as sets, types as indexed families, terms as sections; establishes the consistency of ETT (Martin-Löf); shows ETT lacks injective $\Pi$-types.
- **3.6 Equality in extensional type theory is undecidable** — two proofs: encoding SK-combinator convertibility into judgmental equality and using the set model to show completeness of that encoding; Hofmann's proof via recursively inseparable sets and a Turing-machine interpreter written in type theory, showing that normalization itself fails for ETT. : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link1]], [[Metatheory-and-Implementation-of-Type-Theory|Link2]], [[Extensionality-versus-Intensionality|Link3]]

**Key Questions:**
1. Why does possessing a normalization structure suffice to make judgmental equality decidable, and why is this equivalent to (not just sufficient for) decidability?
2. Why is exhibiting any nontrivial model of type theory enough to prove consistency, while canonicity requires a special gluing model rather than an arbitrary one?
3. How do the two undecidability proofs of Section 3.6 differ in what they assume — existence of a model versus mere consistency — and in what they conclude?

---

### Chapter 4: Intensional type theory (pp. 133–158)

**Summary:** Removes equality reflection, motivated by Chapter 3's undecidability results, and replaces $\mathrm{Eq}$-types with intensional identity ($\mathrm{Id}$) types defined by a mapping-out eliminator, recovering normalization, canonicity, consistency, and invertibility — at the cost of function extensionality and uniqueness of identity proofs, whose independence is proved via the groupoid model; Hofmann's conservativity theorem shows that ITT plus both axioms is exactly as strong as ETT. : [[Cubical-Type-Theory|Link1]], [[Categorical-Semantics-of-Type-Theory|Link2]], [[Extensionality-versus-Intensionality|Link3]], [[Metatheory-and-Implementation-of-Type-Theory|Link4]]

**Key Definitions & Concepts by Section:**
- **4.1 Programming with propositional equality** — informal $\mathrm{Id}$, $\mathrm{refl}$, and $\mathrm{subst}$ (derived from $\mathrm{Id}$ and a motive); derived $\mathrm{sym}$, $\mathrm{trans}$, $\mathrm{cong}$; propositional singleton types $[a]$, distinct from Chapter 3's definitional singletons; singleton contractibility ($\mathrm{uniq}$), needed for identifications of identifications. : [[Full-Spectrum-Dependent-Types|Link1]], [[Univalent-Foundations-and-Homotopy-Type-Theory|Link2]]
- **4.2 Intensional identity types** — an intensional identity type as $\mathrm{Id}$ together with $\mathrm{refl}$, $\mathrm{subst}$, $\mathrm{uniq}$, and their defining equations; the formal $J$-eliminator ("pattern matching on $\mathrm{refl}$"), interprovable with $\mathrm{subst}$ plus $\mathrm{uniq}$. : [[Extensionality-versus-Intensionality|Link]]
- **4.3 Limitations of the intensional identity type** — a translation-based independence framework from ITT to ETT; function extensionality ($\mathrm{Funext}$) and uniqueness of identity proofs (UIP), both provable in ETT but independent of ITT; the groupoid model (Hofmann–Streicher), which refutes UIP; Axiom K (equivalent to UIP, and incompatible with pure pattern-matching); the hierarchy $\mathrm{U(IP)}_n$ foreshadowing homotopy levels; Hofmann's conservativity theorem — ITT plus $\mathrm{Funext}$ plus UIP proves exactly what ETT proves. : [[Extensionality-versus-Intensionality|Link]]
- **4.4★ Observational type theory (draft)** — a stub section pointing to further reading; not yet drafted in this version of the book.

**Key Questions:**
1. Why can identity types not be given a mapping-in universal property analogous to $\mathrm{Eq}$-types, forcing the move to a mapping-out, eliminator-based definition?
2. What does the groupoid model reveal about why UIP fails in ITT, and how does its structure foreshadow the $\infty$-groupoid interpretation of Chapter 5?
3. In what precise sense is ITT weaker than ETT, and why does this make postulating $\mathrm{Funext}$ and UIP as axioms a common practical compromise?

---

### Chapter 5: Univalent type theories (pp. 161–216)

**Summary:** Introduces Voevodsky's univalence axiom, first for propositions and then in full, as a third missing reasoning principle characterizing the identity type of universes; develops homotopy type theory (homotopy levels, higher inductive types) on top of ITT plus univalence; and, because the axiomatic approach breaks canonicity, reconstructs everything inside cubical type theory, which redefines identity as a mapping-in Path type over a new judgmental interval structure, recovering canonicity and normalization while validating univalence computationally. : [[Cubical-Type-Theory|Link1]], [[Univalent-Foundations-and-Homotopy-Type-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **5.1 Propositional univalence** — homotopy propositions ($\mathrm{IsHProp}$, types with at most one element up to $\mathrm{Id}$) versus strict propositions; the principle that interprovable propositions are identified; universes of propositions ($\mathrm{IsUnivalent}$, $\mathrm{IsAdequate}$); propositional resizing (impredicativity); recovering propositional truncation and LEM-consistency from resizing. : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
- **5.2 Homotopy type theory** — $\mathrm{IsEquiv}$ (contractible fibers) versus $\mathrm{HasInverse}$; the univalence axiom, stating that $\mathrm{idtoequiv}$ is itself an equivalence; homotopy type theory defined as ITT plus $\mathrm{Funext}$ plus univalence; univalence implies both $\mathrm{Funext}$ and propositional univalence, and refutes UIP; homotopy levels ($\mathrm{IsOfHLevel}$, $n$-types, h-sets); higher inductive types — the circle $S^1$ ($\mathrm{pt}$, $\mathrm{loop}$), suspensions, set truncation; applications including synthetic homotopy theory ($\pi_1(S^1) \simeq \mathbb{Z}$), descent, and the structure identity principle. : [[Univalent-Foundations-and-Homotopy-Type-Theory|Link]]
- **5.3★ Cubical type theory (draft)** — the interval pretype $I$ (dimension terms and variables, not a genuine type); Path types $\mathrm{Path}(A,a,b)$ as a mapping-in identity type over $I$; the coercion operator $\mathrm{coe}$, a type-directed generalization of substitution; cofibrations ($\Gamma \vdash \varphi\ \mathrm{cof}$, $\Gamma \vdash \varphi\ \mathrm{true}$) isolating the faces of a cube; homogeneous composition $\mathrm{hcomp}$.
- **5.4★ Computing with coercions and compositions (draft)** — worked $\mathrm{coe}$/$\mathrm{hcomp}$ derivations for $\Pi$, $\Sigma$, and Path types; the $V$ type (a Glue-type analogue) implementing univalence computationally; the resulting theorem that cubical type theory enjoys consistency, canonicity, and normalization.

**Key Questions:**
1. Why does the univalence axiom specifically require $\mathrm{idtoequiv}$ to be an *equivalence*, rather than merely requiring some map in the reverse direction to exist, and what goes wrong if $\mathrm{HasInverse}$ is used instead?
2. In what precise sense does cubical type theory's Path type resolve the tension between canonicity and univalence that plain axiomatic HoTT cannot?
3. Why must higher inductive types such as the circle exist to obtain types of no finite homotopy level, when univalent universes alone are not enough?

---

### Chapter 6: Semantics of type theory (draft) (pp. 219–298)

**Summary:** Systematically re-derives the general notion of a model of type theory using category theory, arriving at the compact notion of a category with families (or natural model); reformulates every connective as either a pullback square (mapping-in) or an orthogonality/algebra condition (mapping-out); connects categories with families to locally cartesian closed categories via a coherence theorem solving the strictness mismatch; and finally proves ETT's canonicity via an Artin gluing construction combining the syntactic and set models. : [[Categorical-Semantics-of-Type-Theory|Link1]], [[Extensionality-versus-Intensionality|Link2]]

**Key Definitions & Concepts by Section:**
- **6.1 Categories with families** — $\mathrm{Cx}_M$ as a category; $\mathrm{Ty}$ and $\mathrm{Tm}$ as presheaves over $\mathrm{Cx}$ and its category of elements; context extension as a representability structure on $\pi : \mathrm{Tm}^\bullet \to \mathrm{Ty}$; a category with families defined as a category with terminal object, $\pi$, and representability. : [[Categorical-Semantics-of-Type-Theory|Link1]], [[Judgments-and-the-Substitution-Calculus|Link2]]
- **6.2 Pullback squares and $\Pi, \Sigma, \mathrm{Eq}, \mathrm{Unit}$** — the slogan that mapping-in connectives are pullback squares of formation/introduction data against $\pi$; polynomial functors used to encode "hypothesize over a variable" for $\Pi$/$\Sigma$ formation data.
- **6.3 Orthogonality and $\mathrm{Void}, \mathrm{Bool}, +, \mathrm{Nat}$** — orthogonality $i \pitchfork f$, formalizing "every type believes the gap map is an isomorphism"; the slogan that non-recursive inductive types are a commuting square plus orthogonality of the gap map; $\mathrm{Nat}$ requiring initial-algebra machinery, the categorical analogue of Chapter 2's mapping-out characterization; stable weak orthogonality for types without $\eta$-laws, compatible with ITT; the intensional $\mathrm{Id}$ type as a commuting square plus stable orthogonality restricted to fixed formation data.
- **6.4 Cwf morphisms and $U_0, U_1, U_2, \dots$** — homomorphisms of models reformulated categorically as a functor plus a commuting square plus preservation of context extension; universes as sub-models, with a canonical morphism from the universe's model into the ambient model. : [[Categorical-Semantics-of-Type-Theory|Link]]
- **6.5 Locally cartesian closed categories and coherence** — democratic models (every context of the form $1.A$); the theorem that the context category of a democratic model is locally cartesian closed with finite coproducts, a stably initial $(1 \sqcup -)$-algebra, and a universe hierarchy; the strictness/coherence problem (slicing is only pseudo-functorial); two solutions — the universe construction (requiring a sufficiently large universe in the ambient category) and the local universes construction (Lumsdaine–Warren/Awodey, which delays substitution to preserve strict functoriality without needing a top universe); presheaf models with fiberwise-small universes (Hofmann–Streicher). : [[Categorical-Semantics-of-Type-Theory|Link]]
- **6.6 Canonicity via gluing** — Artin gluing $\mathrm{Gl}(F)$; the canonicity model as the syntactic model glued along the global-sections functor with the set model; the three-step recipe (construct the glued model, a morphism to the syntactic model, and a section from initiality) proving canonicity for $\mathrm{Bool}$ and generalizing to universe elements; pseudo-morphisms of models generalizing the technique. : [[Categorical-Semantics-of-Type-Theory|Link]]

**Key Questions:**
1. Why does defining a connective via a pullback square automatically encode both the elimination rule and all substitution/naturality equations, without stating them separately?
2. What exactly goes wrong — the strictness problem — when trying to define the types over a context directly as the objects of its slice category in an arbitrary locally cartesian closed category, and how do the universe and local-universes constructions each work around it?
3. In the canonicity gluing proof, why is it essential that the glued model come with a morphism *to* the syntactic model rather than from it, and how does initiality of the syntactic model turn that into a section?

---

### Appendices (pp. 301–340)

**Summary:** Appendix A collects, for reference, every inference rule of the base substitution calculus and its ETT- and ITT-tagged extensions from Chapters 2 and 4. Appendix B is a short, still-draft treatment of generalized algebraic theories — the logical-framework machinery (generalized algebraic signatures, models, the initial LF algebra) underlying the "syntax is the initial model" claims used throughout Chapters 3 and 6. Appendix C is an answer key to selected exercises and introduces no new concepts. : [[Categorical-Semantics-of-Type-Theory|Link1]], [[Extensionality-versus-Intensionality|Link2]]

**Key Definitions & Concepts:**
- **Appendix A** — the complete formal rule set for Martin-Löf type theory as presented in this book, organized by judgment.
- **Appendix B** — generalized algebraic signatures and their models; the initial LF algebra as the mathematical object underlying quotient inductive-inductive presentations of syntax.

**Key Questions:**
1. Why is it useful to state type theory's rules as a generalized algebraic theory rather than only as an inductively-defined syntax, given the "syntax as initial model" theme running through Chapters 3 and 6?
