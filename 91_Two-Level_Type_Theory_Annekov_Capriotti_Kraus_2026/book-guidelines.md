# Two-Level Type Theory and Applications — Guidelines

## Header

**Title:** Two-Level Type Theory and Applications
**Author(s):** Danil Annenkov, Paolo Capriotti, Nicolai Kraus, Christian Sattler
**Publication:** arXiv:1705.03307 (research paper, 58 pages; this version dated 2026)

**Brief Summary:**
The paper defines and develops two-level type theory (2LTT), a system combining an "inner" level (homotopy type theory, with univalent universes and possibly higher inductive types) and an "outer" level (a traditional Martin-Löf type theory validating uniqueness of identity proofs), related by a conversion function from inner to outer types. 2LTT is motivated by results in HoTT that are meta-theoretic in nature — most famously the construction of semisimplicial types — which cannot be expressed inside HoTT itself but can be formalised and proved once an external/outer layer is available. After specifying 2LTT syntactically and semantically (as a category of models) and proving a conservativity result over HoTT, the paper builds up a toolkit of fibrant/cofibrant types and fibrations/cofibrations, then applies it to develop the theory of Reedy fibrant diagrams over inverse categories, culminating in an internal definition of semi-Segal types and univalent $(\infty,1)$-categories.

**Intent of the Author:**
The authors want to give a minimal, model-theoretically justified specification of 2LTT (deliberately weaker than Voevodsky's Homotopy Type System, HTS) and to demonstrate, via the Reedy fibrant diagrams application, that it is a genuinely useful language for meta-theoretic HoTT developments — one where internal and external reasoning "go hand in hand" instead of forcing a shift to a fully categorical style of exposition.

---

## Topic List

1. **Two-Level Type Theory (2LTT) Foundations** : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
   - Inner and outer levels of type theory : [[Fibrancy-and-Cofibrancy|Link]]
   - The conversion function from inner to outer types : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
   - Syntax and judgments for two-level type theory : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
   - Uniqueness of identity proofs and function extensionality at the outer level
   - Semantic models via categories with families : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
   - Voevodsky's Homotopy Type System
   - Strengthenings and additional axioms for 2LTT : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
   - Conservativity of 2LTT over HoTT : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
   - Presheaf, simplicial-set, and cubical-set models of 2LTT
   - The impossibility of an internal fibrant replacement operation : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]

2. **Fibrancy and Cofibrancy** : [[Fibrancy-and-Cofibrancy|Link]]
   - Fibrant and trivially fibrant types : [[Fibrancy-and-Cofibrancy|Link]]
   - Fibrations and trivial fibrations : [[Fibrancy-and-Cofibrancy|Link1]], [[Reedy-Fibrant-Diagrams|Link2]]
   - The Leibniz construction and pullback exponentials : [[Fibrancy-and-Cofibrancy|Link]]
   - Cofibrations and cofibrant types : [[Fibrancy-and-Cofibrancy|Link]]
   - Anodyne maps and lifting properties
   - Equivalences between fibrant types : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]

3. **Category Theory Internal to the Outer Level** : [[Category-Theory-Internal-to-the-Outer-Level|Link]]
   - Categories, functors, and natural transformations defined internally : [[Category-Theory-Internal-to-the-Outer-Level|Link]]
   - Finite types and inner-vs-outer finiteness : [[Category-Theory-Internal-to-the-Outer-Level|Link]]
   - Size issues and the notion of smallness : [[Category-Theory-Internal-to-the-Outer-Level|Link]]
   - Inverse categories and rank functors : [[Category-Theory-Internal-to-the-Outer-Level|Link]]
   - The category of elements and Grothendieck constructions : [[Category-Theory-Internal-to-the-Outer-Level|Link]]
   - Reduced coslices and abstract boundaries : [[Category-Theory-Internal-to-the-Outer-Level|Link]]

4. **Reedy Fibrant Diagrams** : [[Reedy-Fibrant-Diagrams|Link]]
   - Matching objects : [[Reedy-Fibrant-Diagrams|Link]]
   - Reedy fibrations and Reedy fibrant diagrams : [[Reedy-Fibrant-Diagrams|Link]]
   - Admissible inverse categories : [[Reedy-Fibrant-Diagrams|Link]]
   - Fibrant limits of Reedy fibrant diagrams : [[Reedy-Fibrant-Diagrams|Link]]
   - Anodyne maps and Reedy fibrant factorisations : [[Reedy-Fibrant-Diagrams|Link]]
   - Reedy fibrant replacement : [[Reedy-Fibrant-Diagrams|Link1]], [[Two-Level-Type-Theory-(2LTT)-Foundations|Link2]]
   - Strict fibrations and classifiers for Reedy fibrations : [[Reedy-Fibrant-Diagrams|Link]]
   - Reedy cofibrations and exponentials of diagrams : [[Reedy-Fibrant-Diagrams|Link]]

5. **Semisimplicial Types and $(\infty,1)$-Categories** : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]
   - Semisimplicial types : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]
   - The semisimplicial category $\Delta_+^{op}$ : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]
   - Semi-Segal types and the Segal condition : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]
   - Equivalences within a semi-Segal type : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]
   - Completeness and univalent $(\infty,1)$-categories : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]
   - The semisimplicial nerve construction : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]
   - The $(\infty,1)$-category of types (TYPE) and its universal fibration : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]

6. **Formalisation of 2LTT in Proof Assistants** : [[Formalisation-of-2LTT-in-Proof-Assistants|Link]]
   - Encoding fibrancy via type classes in Lean : [[Formalisation-of-2LTT-in-Proof-Assistants|Link]]
   - Loss of definitional computation for the fibrant identity type eliminator
   - Alternative implementation strategies (Agda strict sets, Coq private inductive types)

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 2–6)

**Summary:** Motivates 2LTT through the open problem of internally constructing a function $S : \mathbb{N} \to \mathcal{U}$ encoding semisimplicial types of every level, contrasts the "formalise for each externally fixed $n$" question with the "extend the theory so $S$ itself exists" question, and surveys prior two-level systems (Voevodsky's HTS, Maietti's minimalist foundation, cartesian cubical type theory) before outlining the paper's own minimal, conservativity-preserving version of 2LTT.

**Key Definitions & Concepts by Section:**
- **1.1 Context of this paper and related work** — Homotopy Type System (HTS, an extension of MLTT with "exact equalities" internalising judgmental equality), Maietti's minimalist two-level foundation, cartesian cubical type theory as a two-level system, synthetic $\infty$-categories (Riehl–Shulman) as an alternative approach to question 2.
- **1.2 Outline** — inner level (HoTT, "fibrant" types) vs. outer level (traditional MLTT with UIP); the conversion function $c$ from inner to outer types; three equivalent ways to think about 2LTT (inner-as-primary, outer-as-primary, or side-by-side coexistence).

**Key Questions:**
1. What are the two open problems (formalising $S_k$ for each externally fixed $k$, versus constructing $S$ itself) that motivate 2LTT, and how does 2LTT address each one differently?
2. How does 2LTT's intended conservativity property distinguish its goals from those of Voevodsky's HTS?
3. Why do the authors adopt the "outer level as default type theory" convention rather than treating the inner (HoTT) level as primary?

---

### Chapter 2: Two-level type theory (pp. 6–24)

**Summary:** Gives the formal syntax of 2LTT (paired outer/inner type formers related by a conversion operator $c$), defines models of 2LTT semantically via categories with families, proves which type formers $c$ preserves up to isomorphism, catalogues optional strengthenings and axioms (recovering HTS as their strongest combination), works through several example models, proves a conservativity theorem over HoTT, and shows that an internal fibrant-replacement type former is impossible without collapsing the inner level to UIP. : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Syntax** — outer judgment $\Gamma \vdash A \, \mathrm{type}_j$ vs. inner judgment $\Gamma \vdash A \, \mathrm{type}^i_j$; paired type formers $\Pi/\Pi^i$, $\Sigma/\Sigma^i$, $+/+^i$, $1/1^i$, $0/0^i$, $\mathbb{N}/\mathbb{N}^i$, $=/=^i$ (path-equality); the conversion operator $c$ turning inner types into outer types; uniqueness of identity proofs (UIP) and function extensionality assumed at the outer level; univalence assumed for inner universes.
- **2.2 Semantics** — category with families (cwf); cwf hierarchy (cumulative tower of cwf structures); model of Martin-Löf type theory (a cwf hierarchy plus universes); model of set type theory (UIP + funext); model of homotopy type theory (univalent universes); two-level model (inner model, outer model, and a conversion morphism $c$ of cwf hierarchies sharing one category of contexts); model of two-level type theory (inner = HoTT model, outer = set-theory model).
- **2.3 Preservation of type formers by conversion** — Lemma 2.11: $c$ preserves $1$, $\Sigma$, $\Pi$ up to natural isomorphism, but only gives one-directional comparison maps for $+$, $0$, $\mathbb{N}$, and equality (the "positive" type formers), reflecting that meta-theoretic statements cannot always be internalised.
- **2.4 Strengthenings and extensions** — metatheoretic strengthenings (M1)–(M2) (mono step maps; Russell-style universes); strictness axioms (T1)–(T3) on the conversion morphism $c$ (mono on types; on-the-nose preservation of $1/\Sigma/\Pi$; repleteness of inner types); semantic axioms (A1)–(A6) (positive type formers preserved up to iso; fibrant limits of towers; cofibrant/fibrant outer naturals; fibrant outer universes; equality reflection; extra type formers); HTS identified as 2LTT with (T1), (T2), (A1), (A4), (A5) in strongest form. : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
- **2.5 Example models** — presheaf models over a category $C$ (Hofmann–Streicher-style universes); the simplicial-set model (inner types = Kan fibrations); the cubical-set model (Kan lifts as structure, invalidating (T1)); the presheaf model over an arbitrary model of HoTT (weak morphisms of cwfs, the 2-category of cwfs, Yoneda-induced inner cwf structure $\mathrm{Ty}^i$, Proposition 2.13/Corollary 2.14); the modified presheaf model of Proposition 2.16 achieving strict (T1)/(T2). : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
- **2.6 Conservativity** — conservative cwf morphism (Definition 2.17: reflects inhabitation of terms); Proposition 2.18 (2LTT is conservative over HoTT via the presheaf-model construction); Proposition 2.19 (strengthened conservativity for 2LTT with (T1)/(T2)).
- **2.7 On the possibility of a fibrant replacement** — candidate fibrant-replacement type former $R$ with rules `form-R`/`intro-R`/`elim-R`/`comp-R`; Theorem 2.20 (assuming such an $R$ forces the inner level to satisfy UIP, destroying its homotopical content) — the paper's key negative/impossibility result. : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]
- **2.8 Notational conventions** — omission of $\mathrm{El}$ and universe indices; internal definitions $\mathrm{Prop}^i$ and $\mathrm{Prop}$; isomorphism type $A \simeq B$ for outer types vs. equivalence type $A \simeq^i B$ for inner types. : [[Two-Level-Type-Theory-(2LTT)-Foundations|Link]]

**Key Questions:**
1. Why can inner "positive" type formers ($0$, $+$, $\mathbb{N}$, equality) not be expected to be preserved up to isomorphism by the conversion function $c$, even with $\eta$-laws, in contrast to $1$, $\Sigma$, and $\Pi$?
2. What does it mean for the conversion morphism $c$ to satisfy (T1) and (T2), and why does HTS correspond to assuming the strongest forms of these together with (A1), (A4), (A5)?
3. What does Theorem 2.20 show about internalising fibrant replacement as a type former, and why is this compatible with homotopical models still possessing an external (non-natural) fibrant replacement operation?

---

### Chapter 3: Basic tools: categories, fibrations, and cofibrations (pp. 24–34)

**Summary:** Develops the internal category theory needed for the rest of the paper (categories, finite types, size conventions) and introduces the paper's core technical vocabulary — fibrant/cofibrant types and fibrations/cofibrations defined via fibres and the Leibniz (pullback-exponential) construction — establishing their closure properties. : [[Fibrancy-and-Cofibrancy|Link1]], [[Reedy-Fibrant-Diagrams|Link2]]

**Key Definitions & Concepts by Section:**
- **3.1 Preliminaries** — category (Definition 3.1, matching the HoTT book's precategories since UIP makes truncation unnecessary); finite type $\mathrm{Fin}_n$ (outer) vs. $\mathrm{Fin}^i_n$ (inner); the category $\mathcal{U}$ of types; conventions for "smallness" via relative universe level.
- **3.2 Fibrant types** — (trivially) fibrant type (Definition 3.4: isomorphic to an inner type, with the inner type contractible in the trivial case); $\mathcal{U}_{\mathrm{fib}}$, the type of fibrant types; closure of fibrant types under $1$, $\Sigma$, $\Pi$ (Lemma 3.5); equivalence between fibrant types (Definition 3.6, defined via the underlying inner equivalence). : [[Fibrancy-and-Cofibrancy|Link]]
- **3.3 Fibrations** — fibre of a map; (trivial) fibration (Definition 3.7: fibres are (trivially) fibrant); closure under pullback, finite composition, finite products (Lemma 3.10); every trivial fibration has a section (Lemma 3.11); a map between fibrant types is a trivial fibration iff it is a fibration and an equivalence (Lemma 3.12).
- **3.4 Cofibrations** — Leibniz construction / pushout product / pullback exponential $\widehat{\exp}$; (trivial) cofibration (Definition 3.13, dualising fibrations via the pullback exponential); (trivially) cofibrant type; anodyne maps introduced by contrast (Remark 3.16); closure of cofibrations under pushout, composition, coproducts (Lemma 3.21); fibrant types are cofibrant, finite types are cofibrant, cofibrant types closed under $\Sigma$ and finite products (Lemma 3.25). : [[Fibrancy-and-Cofibrancy|Link]]

**Key Questions:**
1. How does the internal definition of fibration (fibres are fibrant) relate to, and differ from, the external notion of Kan fibration in the simplicial-set model?
2. What is the pullback exponential (Leibniz construction), and why is it the right dual gadget for defining cofibrations from fibrations?
3. Why are all fibrant types automatically cofibrant, and why does this fact matter for building up examples of cofibrant types (finite types, $\Sigma$-types)?

---

### Chapter 4: Reedy fibrant diagrams (pp. 34–54)

**Summary:** Applies the fibrancy/cofibrancy toolkit to internalise Shulman's theory of Reedy fibrant diagrams over inverse categories, proving that such diagrams have fibrant limits, constructing Reedy fibrant replacements and classifiers, and using the machinery to give an internal definition of semi-Segal types and univalent $(\infty,1)$-categories. : [[Reedy-Fibrant-Diagrams|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Motivation** — the category $\Delta^{<3}_+$ as a running example; the naive "9-tuple" strict encoding of a diagram (not fibrant) versus the 3-component $(A_0, A_1, A_2)$ encoding expressible in the inner theory (fibrant, but not isomorphic to the strict version).
- **4.2 Inverse categories** — inverse category (Definition 4.1, via a rank functor $\varphi : C^{op} \to \omega$ reflecting identities); category of elements $F/C$; reduced coslice $x \diagdown C$ (Definition 4.2, excluding the identity arrow); abstract boundary $\partial C[x]$ of a representable diagram. : [[Category-Theory-Internal-to-the-Outer-Level|Link1]], [[Reedy-Fibrant-Diagrams|Link2]]
- **4.3 Reedy fibrations** — matching object $M_z^X$ (Definition 4.4, a limit over the reduced coslice); Reedy (trivial) fibration (Definition 4.6: $X_z \to M_z^X \times_{M_z^X} X_z$ is a (trivial) fibration for all $z$); Theorem 4.8 (Reedy fibrant diagrams over a finite inverse category have fibrant limits); change of base along discrete Grothendieck fibrations (Lemma 4.10). : [[Reedy-Fibrant-Diagrams|Link]]
- **4.4 Reedy fibrant factorisations** — anodyne map (Definition 4.11, left lifting property against fibrations); mapping cocylinder (Corollary 4.18); admissible inverse category (Definition 4.19: reduced coslices have fibrant limits), with $\Delta_+^{op}$ as the key example (Definition 4.21); factorisation of any map into pointwise fibrant diagrams as anodyne-then-Reedy-fibration (Lemma 4.26); Reedy fibrant replacement (Corollary 4.27). : [[Reedy-Fibrant-Diagrams|Link]]
- **4.5 Classifiers for Reedy fibrations** — strict fibration (Definition 4.29, a family of inner types); strict Reedy fibration (Definition 4.31); the classifying diagram $\mathcal{V}$ (Definition 4.35) with $\mathrm{Nat}(B, \mathcal{V}) \cong \mathrm{Reedy}_C(B)$ (Lemma 4.36); the type of strictly Reedy fibrant diagrams as $\lim \mathcal{V}$ (Lemma 4.38), fibrant when $C$ is admissible. : [[Reedy-Fibrant-Diagrams|Link]]
- **4.6 Exponents of diagrams** — Reedy (trivial) cofibration (Definition 4.40, dualising Reedy fibrations); Theorem 4.42 (pointwise cofibrations of diagrams are Reedy cofibrations). : [[Reedy-Fibrant-Diagrams|Link]]
- **4.7 Complete semi-Segal types** — semisimplicial type (diagram over $\Delta_+^{op}$); semi-Segal type (Definition 4.46: Reedy fibrant and local with respect to all inner horn inclusions); equivalence in a semi-Segal type (Definition 4.47); univalent $(\infty,1)$-category (Definition 4.48, the completeness condition that the source map from equivalences to vertices is an equivalence); the semisimplicial nerve $N_+(C)$ of an ordinary category; the $(\infty,1)$-category $\mathrm{TYPE}$ of fibrant types and its universal fibration $\mathrm{TYPE}^\bullet$. : [[Semisimplicial-Types-and-(∞,1)-Categories|Link]]

**Key Questions:**
1. Why does the naive "9-tuple" encoding of a diagram over $\Delta_+^{<3}$ fail to be fibrant, and how does the matching-object-based notion of Reedy fibrancy address this?
2. What role does admissibility of an inverse category play in guaranteeing fibrant limits for Reedy fibrant diagrams, and why is $\Delta_+^{op}$ the paper's central example?
3. How do the semi-Segal condition (locality with respect to inner horn inclusions) and the completeness condition (Definition 4.48) combine to give a definition of univalent $(\infty,1)$-category purely internal to 2LTT?

---

### Chapter 5: Conclusions (pp. 54–55)

**Summary:** Recaps 2LTT's suitability as a framework for meta-theoretic HoTT results, notes that using only "basic" 2LTT (no strengthenings) transfers results back to HoTT automatically via conservativity when the relevant bound is an outer natural number, and describes the paper's partial formalisation in Lean along with directions for future work on internal $(\infty,1)$-category theory.

**Key Definitions & Concepts:**
- Flat list (chapter has no subsections): coherence towers and their dependence on axioms (A1)–(A3); the Lean 2 formalisation strategy (type classes tracking fibrancy on top of an ordinary type theory with UIP, postulating the fibrant identity type and its non-computing $J$-rule).

**Key Questions:**
1. Why does using only "basic" 2LTT (without strengthenings) automatically transfer a result back to HoTT via conservativity, whereas relying on axioms like (A2) or (A3) does not carry the same guarantee?
2. What compromise did the Lean formalisation of 2LTT have to make regarding the computation rule for the fibrant identity type eliminator, and why did this not obstruct the formalisation of Theorem 4.8?

---
