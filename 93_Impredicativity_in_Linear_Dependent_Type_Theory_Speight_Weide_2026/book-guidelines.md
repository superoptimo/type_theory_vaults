# Impredicativity in Linear Dependent Type Theory — Guidelines

## Header

**Title:** Impredicativity in Linear Dependent Type Theory
**Author(s):** Sam L. Speight, Niels van der Weide
**Publication:** arXiv:2602.08846v1 [cs.LO], 9 Feb 2026 (20-page conference-style paper)

**Brief Summary:**
The paper constructs a realizability model of linear dependent type theory (LDTT) built from a linear combinatory algebra (LCA), and uses this model to justify extending LDTT with a Tarski-style universe $U$ that is impredicative for *both* cartesian and linear dependent products — a single universe with two decoding operations, $\mathrm{El}_C$ and $\mathrm{El}_L$. It also adds an injectivity rule for the modality $M$ (linear-to-cartesian) and equalizer types on the linear side. As a case study, the impredicative universe is used to encode the initial algebra of lists over a linear type, adapting the Awodey–Frey–Speight refinement technique (equalizer-as-subtype) to the linear setting, and the whole realizability construction is formalized in Rocq/UniMath.

**Intent of the Author:**
The authors want to show that impredicativity is consistent with linear dependent type theory by giving it a concrete categorical/realizability semantics, and to demonstrate that this impredicativity is not merely decorative — it lets one recover genuine (not just weakly-initial) inductive types for linear data via the equalizer-refinement method, extending prior cartesian-only results to the linear setting.

---

## Topic List

1. **Linear Dependent Type Theory (LDTT)** : [[Linear-Dependent-Type-Theory|Link]]
   - Cartesian contexts vs. mixed (cartesian + linear) contexts
   - Cartesian types and terms vs. linear types and terms
   - Dual-context presentation of linearity
   - Multiplicative and additive linear connectives : [[Impredicative-Encoding-of-Linear-Lists|Link]]
   - Linear dependent products and linear dependent sums : [[Realizability-Models-via-Assemblies|Link]]
   - The modalities $M$ and $L$ connecting linear and cartesian sides : [[Realizability-Models-via-Assemblies|Link1]], [[Comprehension-Categories-and-Fibrations|Link2]]
   - Injectivity of the modality $M$ : [[Linear-Dependent-Type-Theory|Link]]
   - Derived identity types for linear terms via $M$
   - Equality reflection and its interaction with linear equality
   - Function extensionality for dependent linear functions : [[Linear-Dependent-Type-Theory|Link]]
   - Equalizer types on the linear side : [[Linear-Dependent-Type-Theory|Link]]

2. **Impredicativity and Impredicative Universes** : [[Impredicativity-and-Impredicative-Universes|Link]]
   - Impredicativity as closure of a universe under large products : [[Linear-Dependent-Type-Theory|Link1]], [[Impredicativity-and-Impredicative-Universes|Link2]]
   - Tarski-style universes and decoding operations
   - A single universe with two decodings, $\mathrm{El}_C$ and $\mathrm{El}_L$
   - Impredicative universes closed under large cartesian and linear dependent products
   - Internal vs. external type formers and their isomorphism
   - Impredicative encodings of inductive types via the recursion principle
   - Weak initiality versus true initiality of impredicative encodings : [[Related-Formalisms-and-Positioning|Link]]
   - Refining impredicative encodings via equalizer subtypes : [[Impredicative-Encoding-of-Linear-Lists|Link]]
   - Parametricity as an alternative route to initiality

3. **Combinatory Algebra and Combinatory Completeness** : [[Combinatory-Algebra-and-Combinatory-Completeness|Link]]
   - Applicative structures and application : [[Combinatory-Algebra-and-Combinatory-Completeness|Link]]
   - Cartesian combinatory algebras and the $S', K'$ combinators : [[Combinatory-Algebra-and-Combinatory-Completeness|Link]]
   - Linear combinatory algebras and the $B, I, C, W, K, D, \delta, F$ combinators : [[Combinatory-Algebra-and-Combinatory-Completeness|Link]]
   - The exponential modality $!$ and guarded arguments
   - Correspondence between LCA combinators and linear logic principles
   - From an LCA to its associated cartesian combinatory algebra $A_!$ : [[Combinatory-Algebra-and-Combinatory-Completeness|Link]]
   - Polynomials and !-polynomials, linear versus non-linear variables : [[Combinatory-Algebra-and-Combinatory-Completeness|Link1]], [[Comprehension-Categories-and-Fibrations|Link2]]
   - Combinatory completeness for CCAs and linear combinatory completeness for LCAs : [[Combinatory-Algebra-and-Combinatory-Completeness|Link]]

4. **Realizability Models via Assemblies** : [[Realizability-Models-via-Assemblies|Link]]
   - Assemblies and realizability relations : [[Realizability-Models-via-Assemblies|Link]]
   - Categories of assemblies and assembly morphisms
   - Families of assemblies as dependent types : [[Realizability-Models-via-Assemblies|Link]]
   - The realizability model of Martin-Löf type theory from a CCA : [[Realizability-Models-via-Assemblies|Link]]
   - Families of linear assemblies from an LCA : [[Realizability-Models-via-Assemblies|Link]]
   - Modest sets and partial equivalence relations : [[Realizability-Models-via-Assemblies|Link]]
   - Equivalence of modest sets and PERs as the basis for an impredicative universe : [[Realizability-Models-via-Assemblies|Link]]

5. **Comprehension Categories and Fibrations** : [[Comprehension-Categories-and-Fibrations|Link]]
   - Grothendieck fibrations and cartesian morphisms
   - Comprehension categories and the comprehension functor : [[Comprehension-Categories-and-Fibrations|Link]]
   - Fullness of a comprehension category : [[Comprehension-Categories-and-Fibrations|Link]]
   - Strong dependent sum types and the Beck–Chevalley condition
   - Symmetric monoidal closed fibrations : [[Comprehension-Categories-and-Fibrations|Link1]], [[Realizability-Models-via-Assemblies|Link2]]
   - Linear comprehension categories with an adjunction between linear and cartesian types : [[Comprehension-Categories-and-Fibrations|Link]]
   - Fibrewise equalizers and their preservation under substitution : [[Comprehension-Categories-and-Fibrations|Link]]
   - Linear-non-linear models of linear exponentiation

6. **Impredicative Encoding of Linear Lists** : [[Impredicative-Encoding-of-Linear-Lists|Link]]
   - The Church/Girard-style polymorphic encoding of lists : [[Impredicative-Encoding-of-Linear-Lists|Link]]
   - List constructors nil and cons under the encoding
   - The list recursor and definitional computation rules
   - Algebras and algebra morphisms for the list signature
   - Cartesian terms under the modality $M$ representing linear structure maps
   - Constructing an equalizer subtype to recover the true initial algebra
   - Proof that the refined list type is an initial algebra

7. **Related Formalisms and Positioning** : [[Related-Formalisms-and-Positioning|Link]]
   - Comparison with Krishnaswami–Pradic–Benton's LDTT
   - Comparison with Lundfall's and Vákár's categorical models of LDTT : [[Related-Formalisms-and-Positioning|Link]]
   - Quantitative type theory as a semiring-graded generalization of linearity : [[Related-Formalisms-and-Positioning|Link]]
   - Ribbon, planar, and monadic combinatory algebras : [[Related-Formalisms-and-Positioning|Link]]
   - Rocq/UniMath formalization of the model : [[Related-Formalisms-and-Positioning|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–2)

**Summary:** Motivates impredicativity in higher-order type theory (as in the calculus of constructions), notes the lack of set-theoretic models for such theories, and frames realizability as the standard technique for building models; states the paper's goal of extending realizability to linear dependent type theory with impredicativity, culminating in an impredicative encoding of linear lists.

**Key Definitions & Concepts:**
- **Impredicativity** — a universe closed under functions from any type into a small type; small types are closed under "large" products.
- **Impredicative encodings** — using an impredicative universe to translate System F–style polymorphic definitions into (dependent) function types, guaranteeing $\beta$-computation but not, in general, the induction principle.
- **Linearity** — a discipline in which functions must use each argument exactly once (no deletion or duplication).
- **Linear dependent type theory (LDTT)** — the target formalism combining dependent typing with linear typing, per Cervesato–Pfenning, Krishnaswami–Pradic–Benton, Vákár, and Lundfall.

**Key Questions:**
1. Why can impredicative higher-order type theories not be modeled by ordinary set theory, and what role does realizability play as an alternative?
2. What is the precise sense in which impredicative encodings of inductive types are only "weakly" initial, and why does that matter?

---

### Chapter 2: Linear Dependent Type Theory (pp. 2–5)

**Summary:** Recalls the syntax of LDTT (judgement forms, dual cartesian/mixed contexts, type formers on both the cartesian and linear sides, the modality $M$), then introduces the paper's novel additions: linear equalizer types, an injectivity rule for $M$, derived identity types and function extensionality for linear dependent functions, and the impredicative universe $U$ with its two decoding operations. : [[Linear-Dependent-Type-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **Judgement forms** — cartesian context ($\vdash \Gamma\ \mathrm{context}$), mixed context ($\vdash \Gamma \mid \Xi\ \mathrm{context}$), cartesian/linear type formation, cartesian term typing ($\Gamma \vdash a:A$), linear term typing ($\Gamma \mid \Xi \vdash a:A$).
- **Cartesian and linear type formers** — unit, $\Pi$-, $\Sigma$-types, and identity types (with equality reflection) on the cartesian side; multiplicative ($\multimap, \otimes$) and additive ($\oplus, \&$) connectives plus linear dependent products $\sqcap$ and sums $\sqsubset$ on the linear side.
- **Modality $M$** — sends linear types/terms (in the empty linear context) to cartesian types/terms, with formation, introduction $M(a)$, elimination $\mu(a)$, and $\beta/\eta$ rules (Figure 2).
- **Equalizer types** — $\mathrm{Eq}(f,g)$ for parallel linear maps $f,g : A \multimap B$, with formation, introduction, elimination map $\iota_{f,g}$, and $\beta/\eta$ rules.
- **$M$-inj** — injectivity of $M$: $M(a) \equiv M(a') \Rightarrow a \equiv a'$; semantically corresponds to faithfulness of the functor $M$.
- **Derived linear identity types** — $a =_L a'$ defined as $M(a) = M(a')$; combined with equality reflection and $M$-inj, yields equality reflection for linear identity types.
- **Function extensionality for $\sqcap$** — $\mathrm{FunExt}$, derived from $\sqcap$-$\eta$ plus equality reflection.
- **Impredicative universe $U$** — a cartesian type with two decodings, $\mathrm{El}_C(A)$ (cartesian type) and $\mathrm{El}_L(A)$ (linear type), closed under large cartesian products ($\widehat{\Pi}$-f) and large linear products ($\widehat{\sqcap}$-f), with internal ($\widehat{(-)}$-decorated) and external type formers related by isomorphism (Equation 1).

**Key Questions:**
1. Why must the indexing type $A$ in $\sqcap_{x:A} B$ and $\sqsubset_{x:A} B$ be cartesian rather than linear?
2. How does combining $M$-inj with equality reflection yield equality reflection for the *derived* linear identity type $=_L$, and why is this only available in the empty linear context?
3. What is the practical difference between having one universe $U$ with two decoding operations $\mathrm{El}_C, \mathrm{El}_L$ versus having two separate cartesian and linear universes?

---

### Chapter 3: Linear Realizability (Combinatory Algebra) (pp. 5–7)

**Summary:** Recalls applicative structures, cartesian combinatory algebras (CCAs), and linear combinatory algebras (LCAs) — the latter axiomatizing the $!,\multimap$-fragment of linear logic — together with the combinatory-completeness theorems needed to construct realizers in the later model. : [[Combinatory-Algebra-and-Combinatory-Completeness|Link]]

**Key Definitions & Concepts:**
- **Applicative structure** — a set $A$ with a binary application operation $\bullet$.
- **Cartesian combinatory algebra (CCA)** — an applicative structure with combinators $S', K'$ satisfying $S'abc = ac(bc)$, $K'ab = a$.
- **Linear combinatory algebra (LCA)** — an applicative structure with a unary $!$ operation and combinators $B, I, C, W, K, D, \delta, F$ satisfying the identities of Table 2, each corresponding to a logical principle (cut, identity, exchange, contraction, weakening, dereliction, comultiplication, functoriality).
- **$A_!$** — the CCA $(A, \bullet_!)$ derived from an LCA $A$ by setting $a \bullet_! b := a \bullet\, !b$.
- **(!-)Polynomials** — terms built from variables, elements of $A$, application, and $!$; a variable is *linear* in a !-polynomial if it occurs exactly once and not under a $!$.
- **Combinatory completeness (Curry)** — a CCA is equivalent to being cartesian combinatory complete (every polynomial has a $\lambda^{*}$-abstraction).
- **Linear combinatory completeness (Simpson)** — an LCA is equivalent to admitting both linear ($\lambda^{*}$) and non-linear/guarded ($\lambda^{!*}$) abstraction operators satisfying the expected computation laws.

**Key Questions:**
1. Why does contraction ($W$) require its second argument to be guarded by $!$, and what does this reflect about linear logic's structural rules?
2. In what precise sense does linear combinatory completeness give two distinct abstraction operators, $\lambda^{*}$ and $\lambda^{!*}$, and what role does each play?

---

### Chapter 4: Linear Realizability Model (pp. 7–13)

**Summary:** The technical core of the paper: recalls comprehension categories and the standard realizability model of Martin-Löf type theory from a CCA, then generalizes to linear comprehension categories (a fibration over cartesian types paired with a symmetric-monoidal-closed fibration over linear types, connected by an adjunction $L \dashv M$), shows every LCA induces such a structure, and interprets all the type formers from Chapter 2 — including equalizers and the impredicative universe via the modest-sets/PER equivalence. : [[Realizability-Models-via-Assemblies|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Realizability models of type theory** — Grothendieck fibration (Def. 4.1); comprehension category $\chi: E \to B^{\to}$ over a fibration $p$ (Def. 4.2), required full (Remark 4.3); strong $\Sigma$-types via left adjoints to substitution functors satisfying Beck–Chevalley (Def. 4.4); the assembly category $\mathrm{Asm}(A)$ and family category $D\mathrm{Asm}_C(A)$ realizing MLTT from a CCA (Example 4.6). : [[Comprehension-Categories-and-Fibrations|Link1]], [[Realizability-Models-via-Assemblies|Link2]]
- **4.2 Linear comprehension categories** — symmetric monoidal closed fibration (Def. 4.7); linear comprehension category as a fibration $q$ over $B$ together with an adjunction $L \dashv M$ into a comprehension category over the same $B$ (Def. 4.9); the realizability instance $D\mathrm{Asm}_L(A)$ of families of linear assemblies over an LCA (Example 4.8); the syntax-to-semantics dictionary of Table 3; faithfulness of $M$ and $L$ (Example 4.11). : [[Comprehension-Categories-and-Fibrations|Link]]
- **4.3 Type formers in linear comprehension categories** — linear dependent products/sums as adjoints to substitution with Frobenius reciprocity (Def. 4.12, Example 4.13); fibrewise equalizers interpreting equalizer types (Def. 4.14, Example 4.15); modest sets and partial equivalence relations (Def. 4.16); Hyland's equivalence of modest sets and PERs for BI-algebras (Thm. 4.17); the impredicative universe $U$ as the PER family, closed under dependent products because modest sets are closed under (linear) dependent products (Example 4.18). : [[Comprehension-Categories-and-Fibrations|Link]]

**Key Questions:**
1. What extra structure does a *linear* comprehension category require beyond an ordinary comprehension category, and why must $q$ specifically be symmetric monoidal closed rather than just monoidal?
2. Why does Hyland's modest-sets/PER equivalence (Theorem 4.17) hold for the more general class of BI-algebras rather than only partial combinatory algebras, and why is that generality essential here?
3. Concretely, why does closure of modest sets under (linear) dependent products give the universe $U$ its impredicativity?

---

### Chapter 5: Impredicative Encodings (pp. 12–14)

**Summary:** Applies the impredicative universe to construct linear lists: first the standard (Girard-style) polymorphic encoding $\mathrm{List}^{*}(A)$, which is only weakly initial, then — following Awodey–Frey–Speight's refinement method adapted to the linear setting via equalizers instead of $\Sigma$-types — the genuinely initial algebra $\mathrm{List}(A) := \mathrm{Eq}(\varphi,\psi)$, with a full initiality proof. : [[Impredicative-Encoding-of-Linear-Lists|Link1]], [[Related-Formalisms-and-Positioning|Link2]]

**Key Definitions & Concepts:**
- **$\mathrm{List}^{*}(A)$** — $\sqcap_{X:U}\ \mathrm{El}_L(X) \multimap\ !(A \multimap \mathrm{El}_L(X) \multimap \mathrm{El}_L(X)) \multimap \mathrm{El}_L(X)$, the impredicative polymorphic encoding, with constructors $\mathrm{nil}^{*}$, $(::)^{*}$ and recursor $\mathrm{rec}_X$.
- **$\mathrm{Alg}$** — the type of list-algebras, $\Sigma_{X:U}\ M(\mathrm{El}_L(X)) \times M(!(A \multimap \mathrm{El}_L(X) \multimap \mathrm{El}_L(X)))$, using $M$ to package linear structure maps as cartesian data.
- **$\mathrm{Mor}(X,Y)$ / $\mathrm{IsMor}$** — algebra morphisms as cartesian terms $f$ satisfying the expected commuting-square conditions up to $=_L$.
- **$\varphi, \psi$** — the two "evaluate-at-every-algebra-morphism" maps out of $\mathrm{List}^{*}(A)$ whose equalizer cuts down to the well-behaved sublist type.
- **$\mathrm{List}(A) := \mathrm{Eq}(\varphi,\psi)$** — the refined list type, shown (Lemma 5.1) to carry an algebra structure and (Theorem 5.2) to be the *initial* algebra.

**Key Questions:**
1. Why can't $\Sigma$-types (used in the cartesian Awodey–Frey–Speight construction) be reused directly here, forcing the use of equalizer types instead?
2. Walk through why $\mathrm{List}^{*}(A)$ satisfies the recursion/$\beta$-rules for lists but not, in general, the induction principle — what exactly goes missing?
3. In the initiality proof (Theorem 5.2), what is the role of function extensionality for $\sqcap$ in showing uniqueness of the induced algebra morphism?

---

### Chapter 6: Related Work (pp. 14–16)

**Summary:** Situates the paper relative to prior work on linear combinatory algebras and linear realizability (Abramsky, Abramsky–Lenisa, Hoshino), other treatments of LDTT (Cervesato–Pfenning, Krishnaswami–Pradic–Benton, Vákár, Lundfall), quantitative type theory (Atkey), and prior impredicative-encoding refinement techniques (Awodey–Frey–Speight and successors), highlighting that no prior model combines realizability with impredicativity for linear dependent types. : [[Related-Formalisms-and-Positioning|Link]]

**Key Definitions & Concepts:**
- **Substructural combinatory algebras** — generalizations of LCAs such as ribbon and planar combinatory algebras, and structured-multicategory treatments of combinatory completeness.
- **Quantitative type theory** — a semiring-graded generalization of linear typing (Atkey's model via a quantitative combinatory algebra), contrasted with the present model's impredicativity, which Atkey's set-indexed assemblies cannot support.
- **Alternative routes to initiality** — internal parametricity as an alternative to the equalizer-refinement method for recovering initiality from impredicative encodings.

**Key Questions:**
1. Why, according to the authors, can Atkey's quantitative-type-theory model not support an impredicative universe, while the present LCA-based model can?
2. What is the key semantic difference between Lundfall's adjunction-based treatment of the linear modality and Vákár's comonad-based treatment?

---

### Chapter 7: Conclusion (p. 15)

**Summary:** Summarizes the contributions (a realizability model of impredicative LDTT, its Rocq formalization, and the initial linear-list algebra) and flags open directions: generalizing beyond lists to arbitrary inductive types, and adapting the (currently extensionality-dependent) injectivity axiom to intensional versions of LDTT.

**Key Definitions & Concepts:**
- No new formal definitions; restates the paper's dependence on extensionality and poses generalization to arbitrary inductive/coinductive types and to intensional LDTT as future work.

**Key Questions:**
1. Why is the current injectivity axiom for $M$ described as "tailored" to the extensional setting, and what would have to change to adapt it intensionally?

---
