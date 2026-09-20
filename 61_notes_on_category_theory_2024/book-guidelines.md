# Notes on Category Theory — Guidelines

## Header

**Title:** Notes on Category Theory (with examples from basic mathematics)
**Author(s):** Paolo Perrone
**Publication:** arXiv:1912.10642v7 [math.CT], unrevised version last updated February 2021 (originally developed as lecture notes for a course at the Max Planck Institute of Leipzig, Summer semester 2019)

**Brief Summary:**
A self-contained introduction to category theory built from lecture notes, assuming only linear algebra as background. It develops categories, functors, and natural transformations from several complementary intuitions (relations, operations, structured spaces), then builds up through the Yoneda lemma and universal properties to limits/colimits, adjunctions, and monads/comonads treated on an equal footing. Throughout, abstract constructions are grounded in concrete worked examples from group theory, topology, linear algebra, probability, and graph theory — most notably a running example relating categories and directed multigraphs.

**Intent of the Author:**
The author wrote these notes to make category theory accessible to a scientifically varied audience (algebraic geometers, topologists, computer scientists, physicists, chemists) without assuming prior exposure to the fields where category theory is traditionally applied, emphasizing intuition alongside rigorous proofs and a thorough, example-driven treatment of the Yoneda lemma and of comonads (often neglected as "just dual to monads").

---

## Topic List

1. **Categories and Their Basic Structure** : [[Categories-and-Their-Basic-Structure|Link]]
   - Objects morphisms composition and identities : [[Categories-and-Their-Basic-Structure|Link]]
   - Categories from relations groups and monoids : [[Categories-and-Their-Basic-Structure|Link]]
   - Isomorphisms and groupoids : [[Categories-and-Their-Basic-Structure|Link]]
   - The opposite category and duality : [[Categories-and-Their-Basic-Structure|Link]]
   - Monomorphisms and epimorphisms : [[Categories-and-Their-Basic-Structure|Link]]
   - Split monomorphisms and split epimorphisms : [[Categories-and-Their-Basic-Structure|Link]]

2. **Functors** : [[Functors|Link]]
   - Functors preserving relations and operations : [[Functors|Link]]
   - Forgetful functors : [[Functors|Link]]
   - Contravariant functors and presheaves : [[Functors|Link]]
   - Functors detecting complexity : [[Functors|Link]]
   - Continuous and cocontinuous functors : [[Functors|Link]]

3. **Natural Transformations** : [[Natural-Transformations|Link]]
   - Natural transformations and naturality squares : [[Natural-Transformations|Link]]
   - Natural isomorphisms : [[Natural-Transformations|Link1]], [[Categories-and-Their-Basic-Structure|Link2]]
   - Functor categories : [[Natural-Transformations|Link1]], [[Studying-Categories-via-Functors|Link2]]
   - Diagrams as functors : [[Natural-Transformations|Link]]
   - Whiskering and horizontal composition : [[Natural-Transformations|Link]]

4. **Studying Categories via Functors** : [[Studying-Categories-via-Functors|Link]]
   - Subcategories : [[Studying-Categories-via-Functors|Link]]
   - Faithful full and essentially surjective functors : [[Studying-Categories-via-Functors|Link]]
   - Equivalence of categories : [[Studying-Categories-via-Functors|Link]]

5. **Representable Functors and Presheaves** : [[Representable-Functors-and-Presheaves|Link]]
   - Representable functors : [[Functors|Link1]], [[Limits-and-Colimits|Link2]], [[Representable-Functors-and-Presheaves|Link3]]
   - The Yoneda embedding theorem : [[Representable-Functors-and-Presheaves|Link]]

6. **The Yoneda Lemma** : [[The-Yoneda-Lemma|Link]]
   - Statement and proof of the Yoneda lemma : [[The-Yoneda-Lemma|Link]]
   - Particular cases and applications : [[The-Yoneda-Lemma|Link]]

7. **Universal Properties** : [[Universal-Properties|Link]]
   - Universal property of the cartesian product : [[Universal-Properties|Link]]
   - Universal property of the tensor product : [[Universal-Properties|Link]]

8. **Limits and Colimits** : [[Limits-and-Colimits|Link]]
   - Cones cocones and universal cones : [[Limits-and-Colimits|Link]]
   - Limits and colimits as constrained optimization : [[Limits-and-Colimits|Link]]
   - Invariants and orbits of a group action : [[Limits-and-Colimits|Link]]
   - Products and coproducts : [[Limits-and-Colimits|Link]]
   - Equalizers and coequalizers : [[Limits-and-Colimits|Link]]
   - Pullbacks and pushouts : [[Limits-and-Colimits|Link]]
   - Initial and terminal objects : [[Limits-and-Colimits|Link]]
   - Completeness of the category of sets : [[Limits-and-Colimits|Link]]

9. **Adjunctions** : [[Adjunctions|Link]]
   - Adjoint functors and hom-set bijections : [[Adjunctions|Link]]
   - Free-forgetful adjunctions : [[Adjunctions|Link]]
   - Galois connections : [[Adjunctions|Link]]
   - Unit and counit of an adjunction : [[Monads-Comonads-and-Adjunctions|Link1]], [[Adjunctions|Link2]]
   - Triangle identities : [[Adjunctions|Link]]
   - Adjunctions preserve limits and colimits : [[Adjunctions|Link]]
   - The adjoint functor theorem for preorders : [[Adjunctions|Link]]

10. **Monads** : [[Monads|Link]]
    - Monad as an extension of spaces : [[Monads|Link]]
    - Kleisli morphisms and the Kleisli category : [[Monads|Link]]
    - The Kleisli adjunction : [[Comonads|Link1]], [[Monads-Comonads-and-Adjunctions|Link2]], [[Monads|Link3]]
    - Closure operators and idempotent monads : [[Monads|Link]]
    - Monad as a theory of operations : [[Monads|Link]]
    - Algebras of a monad and free algebras : [[Monads|Link1]], [[Monads-Comonads-and-Adjunctions|Link2]]
    - The Eilenberg-Moore adjunction : [[Monads-Comonads-and-Adjunctions|Link1]], [[Monads|Link2]]

11. **Comonads** : [[Comonads|Link]]
    - Comonad as extra information : [[Comonads|Link]]
    - Co-Kleisli morphisms and the co-Kleisli category : [[Monads|Link]]
    - The co-Kleisli adjunction : [[Comonads|Link]]
    - Comonad as a process on spaces : [[Comonads|Link]]
    - Coalgebras of a comonad : [[Comonads|Link]]
    - The adjunction of coalgebras : [[Comonads|Link]]

12. **Monads Comonads and Adjunctions** : [[Monads-Comonads-and-Adjunctions|Link]]
    - Every adjunction induces a monad and a comonad : [[Monads-Comonads-and-Adjunctions|Link]]
    - Monadicity of an adjunction : [[Monads-Comonads-and-Adjunctions|Link]]
    - The adjunction between categories and multigraphs is monadic : [[Monads-Comonads-and-Adjunctions|Link1]], [[Categories-and-Their-Basic-Structure|Link2]]

---

## Chapter Summaries

### Chapter 1: Basic concepts (pp. 8–66)

**Summary:** Introduces the foundational vocabulary of category theory — categories, functors, and natural transformations — building each concept from several complementary intuitions (relations, operations, structured spaces) and grounding it in examples from set theory, group theory, topology, and linear algebra.

**Key Definitions & Concepts by Section:**
- **1.1 Categories** — Category $\mathcal{C}$ (objects, morphisms, composition, identities, unitality, associativity); composite read right-to-left ("$g$ after $f$"); preorder/equivalence relation/order relation as categories; group and monoid as delooping $B G$; hom-set $\mathrm{Hom}_{\mathcal C}(X,Y)$; small vs. locally small categories; isomorphism (two-sided invertible pair); groupoid (all morphisms invertible); core of a category; commutative diagram; opposite category $\mathcal C^{op}$ and the duality principle : [[Studying-Categories-via-Functors|Link]]
- **1.2 Mono and epi** — Monomorphism (left-cancellable, generalizes injective maps); split monomorphism/retraction (left inverse); epimorphism (right-cancellable, generalizes surjective maps); split epimorphism/section (right inverse); retract; mono+split epi (or epi+split mono) $\Rightarrow$ isomorphism : [[Functors|Link]]
- **1.3 Functors and functoriality** — Functor $F:\mathcal C\to\mathcal D$ (object map + morphism map preserving identities and composition); functors preserve commutative diagrams, isomorphisms, split mono/epi (used to detect non-existence of retractions/sections); forgetful functor; linear/permutation representation of a group; cocycle condition as another name for functoriality; contravariant functor $\mathcal C^{op}\to\mathcal D$; presheaf (a functor $\mathcal C^{op}\to\mathrm{Set}$) : [[Representable-Functors-and-Presheaves|Link]]
- **1.4 Natural transformations** — Natural transformation $\alpha:F\Rightarrow G$ (components satisfying the naturality square); natural isomorphism; equivariant maps as natural transformations between group-action functors; canonical/basis-independent maps (e.g. $V\to V^{**}$) vs. non-natural ones (e.g. $V\to V^*$, the no-cloning theorem); functor category $[\mathcal C,\mathcal D]$; diagram (rigorously, a functor $I\to\mathcal C$ from a small shape category $I$); whiskering and horizontal composition : [[Natural-Transformations|Link]]
- **1.5 Studying categories by means of functors** — The category $\mathrm{Cat}$; subcategory, wide subcategory, full subcategory; faithful, full, fully faithful, essentially surjective functors; equivalence of categories (pseudoinverse functors with natural isomorphisms to the identities); Theorem 1.5.16 (fully faithful + essentially surjective $\iff$ equivalence); $\mathrm{FVect}\simeq\mathrm{Mat}$ : [[Studying-Categories-via-Functors|Link]]

**Key Questions:**
1. Why does category theory prefer isomorphism of objects and equality of morphisms over equality of objects, and how does this explain why functors carry three independent properties (faithful, full, essentially surjective) instead of the two that suffice for functions?
2. What distinguishes a monomorphism from a split monomorphism, and why does the distinction collapse in $\mathrm{Set}$ but not in $\mathrm{Top}$ or $\mathrm{Grp}$?
3. What makes a map "natural" (e.g. $V\to V^{**}$) as opposed to well-defined but basis-dependent (e.g. $V\to V^*$), and how does the naturality square formalize "independence from a choice of coordinates"?

---

### Chapter 2: Universal properties and the Yoneda lemma (pp. 67–82)

**Summary:** This chapter introduces representable functors and presheaves, culminating in the Yoneda lemma and Yoneda embedding theorem, then shows how these give rise to the notion of a universal property, illustrated with the cartesian product and tensor product. : [[Universal-Properties|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 Representable functors and the Yoneda embedding theorem** — Functors/presheaves as feature-extractors from an object (e.g. $U$, $\mathrm{Curve}$, $\mathrm{Loop}$, $\pi_0$, $O$ on $\mathbf{Top}$); representable functor: $F: \mathcal{C} \to \mathbf{Set}$ naturally isomorphic to $\mathrm{Hom}_\mathcal{C}(S,-)$ for some representing object $S$ (dually for presheaves via $\mathrm{Hom}_\mathcal{C}(-,S)$); intuition of $S$ as a "probe"/"screen"; worked representability examples in $\mathbf{Top}$, $\mathbf{MGraph}$, $\mathbf{Grp}$, $BG$; Yoneda embedding theorem: $\mathrm{Hom}_\mathcal{C}(X,Y) \cong \mathrm{Hom}_{[\mathcal{C}^{op},\mathbf{Set}]}(\mathrm{Hom}_\mathcal{C}(-,X), \mathrm{Hom}_\mathcal{C}(-,Y))$; consequence that objects are uniquely determined (up to iso) by what they represent / by how they interact with the rest of the category. : [[Representable-Functors-and-Presheaves|Link1]], [[Functors|Link2]], [[Limits-and-Colimits|Link3]]
- **2.2 The Yoneda lemma** — Yoneda lemma: natural bijection $\mathrm{Hom}_{[\mathcal{C}^{op},\mathbf{Set}]}(\mathrm{Hom}_\mathcal{C}(-,X), F) \cong FX$ via $\alpha \mapsto \alpha_X(\mathrm{id}_X)$, natural in both $X$ and $F$; full bijectivity/naturality proof; particular cases worked out for $\mathbf{Par}$ (multigraphs), $BG$ (recovering Cayley's theorem), and the matrix category $\mathbf{Mat}$ (row operations as matrices). : [[The-Yoneda-Lemma|Link]]
- **2.3 Universal properties** — Universal property of $X$: a functor $F$ or presheaf $P$ together with a chosen natural isomorphism $\mathrm{Hom}_\mathcal{C}(X,-) \Rightarrow F$ or $\mathrm{Hom}_\mathcal{C}(-,X) \Rightarrow P$; reading a universal property as existence-and-uniqueness of a map into/out of $X$ (dashed-arrow notation); the universal property of the cartesian product $X \times Y$ in $\mathbf{Top}$ (with projections $p_1, p_2$) as representing $\mathrm{Hom}(-,X) \times \mathrm{Hom}(-,Y)$; the universal property of the tensor product $V \otimes W$ in $\mathbf{Vect}$ as representing bilinear maps $\mathrm{Bilin}(V,W;-)$; note that the universal property includes the specified maps ($p_1,p_2$, or $q$), not just existence of an isomorphism. : [[Universal-Properties|Link]]

**Key Questions:**
1. Why must both existence *and* uniqueness of the mediating map hold for an object to satisfy a universal property, and what breaks if only existence holds?
2. How does the Yoneda lemma explain, intuitively, why the "self-observation" $\mathrm{id}_X$ is enough to recover all information about $X$ from $\mathrm{Hom}_\mathcal{C}(-,X)$?
3. In what sense are the cartesian product and tensor product both instances of the same general pattern (representing a functor built from $X$ and $Y$), despite one being a product-type construction and the other built from bilinear maps?

---

### Chapter 3: Limits and colimits (pp. 83–108)

**Summary:** Develops limits and colimits as universal cones/cocones representing the presheaf/functor of cones over a diagram, then works out what this means concretely in a sequence of settings — posets, group actions, products/coproducts, equalizers/coequalizers, pullbacks/pushouts, and initial/terminal objects — before studying which functors preserve (co)limits and proving that $\mathrm{Set}$ is complete. : [[Adjunctions|Link1]], [[Limits-and-Colimits|Link2]]

**Key Definitions & Concepts by Section:**
- **3.1 General definitions** — Constant diagram at $X$; cone over a diagram $F$ (natural transformation from the constant diagram to $F$) and cocone (the dual); presheaf $\mathrm{Cone}(-,F):\mathcal C^{op}\to\mathbf{Set}$ and functor $\mathrm{Cone}(F,-):\mathcal C\to\mathbf{Set}$; limit $\lim F$ (object representing $\mathrm{Cone}(-,F)$, with its universal cone) and colimit $\mathrm{colim}\,F$ (object representing $\mathrm{Cone}(F,-)$); complete/cocomplete category (every diagram has a limit/colimit) : [[Functors|Link1]], [[Natural-Transformations|Link2]]
- **3.2 Particular limits and colimits** — Poset case: cone = lower bound, limit = greatest lower bound/infimum/meet $\inf S$; cocone = upper bound, colimit = supremum/join $\sup S$; limits/colimits as constrained optimization. Group case (diagrams $BG\to\mathbf{Set}$, i.e. $G$-sets): limit = set of $G$-invariant elements; colimit = set of orbits (finest invariant partition). Products/coproducts: limit/colimit of a discrete diagram, e.g. cartesian product $A\times B$ in $\mathbf{Set}$, coproduct/disjoint union $A\sqcup B$. Equalizers/coequalizers: limit/colimit of a parallel pair $f,g:A\to B$, i.e. largest subset where $f,g$ agree / quotient by the equivalence relation generated by $f,g$. Pullbacks/pushouts: limit/colimit of a cospan/span, fibered product $A\times_C B$ and pushout $B\sqcup_A C$; kernel pair and cokernel pair characterizing mono/epi. Initial and terminal objects: limit/colimit of the empty diagram, terminal object $1$ and initial object $0$; zero object. Slice category $\mathcal C/D$ (limit cone of $D$ as its terminal object) and coslice category. : [[Limits-and-Colimits|Link1]], [[Adjunctions|Link2]]
- **3.3 Functors, limits and colimits** — Continuous functor (preserves all existing limits) and cocontinuous functor (preserves all existing colimits); forgetful functors that preserve some but not all (co)limits (e.g. $\mathrm{Vect}\to\mathbf{Set}$ preserves products/terminal objects but not coproducts/initial objects); power set functor $P$ and probability functor $\mathcal P$ as functors failing to preserve products/coproducts, interpreted as "detecting complexity" (mixed subsets, statistical interaction); Theorem 3.3.16 (representable functors are continuous) and its dual (representable presheaves turn colimits into limits); continuity/cocontinuity is preserved under natural isomorphism, composition, and equivalence of categories : [[Limits-and-Colimits|Link1]], [[Adjunctions|Link2]]
- **3.4 Limits and colimits of sets** — Explicit construction of the limit of a diagram of sets as a subset $S$ of the big product $P=\prod_I D I$ cut out by compatibility equations (Lemma 3.4.1); Theorem 3.4.2: $\mathbf{Set}$ is complete; every limit is expressible as an equalizer of products, every colimit as a coequalizer of coproducts; full general proof of Theorem 3.3.16 via the explicit set-limit construction : [[Limits-and-Colimits|Link]]

**Key Questions:**
1. How does viewing limits and colimits through the poset case (infima/suprema, constrained optimization) and the group case (invariants/orbits) illuminate what a universal cone is doing in general?
2. Why do the power set and probability functors fail to preserve products and coproducts, and what does this reveal about the relationship between composing objects and probing/observing them?
3. Why does Theorem 3.3.16 (representable functors are continuous) follow essentially for free once limits in $\mathbf{Set}$ are constructed explicitly, and what does this say about $\mathbf{Set}$'s role as a target category for probing objects?

---

### Chapter 4: Adjunctions (pp. 109–131)

**Summary:** Defines adjunctions between functors as natural bijections between hom-sets, gives concrete free-forgetful examples (Set/Top, Set/Vect) and the order-theoretic special case of Galois connections, then develops the unit-counit characterization and triangle identities as an equivalent, more workable definition. Closes by showing adjoints interact cleanly with (co)limits and proving the adjoint functor theorem for preorders, illustrated throughout with the categories-vs-multigraphs adjunction. : [[Adjunctions|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 General definitions** — Adjunction $F \dashv G$ (natural bijection $\mathrm{Hom}_\mathcal D(FC,D) \cong \mathrm{Hom}_\mathcal C(C,GD)$), left-adjoint/right-adjoint, transpose/adjunct maps ($f^\sharp$, $f^\flat$); free-forgetful adjunctions (discrete topology functor $\dashv$ forgetful $\mathrm{Top}\to\mathrm{Set}$; free vector space functor $\dashv$ forgetful $\mathrm{Vect}\to\mathrm{Set}$); Galois connection/correspondence (adjunction between posets), lower adjoint / upper adjoint, convex hull as a lower adjoint example : [[Functors|Link1]], [[Natural-Transformations|Link2]]
- **4.2 Unit and counit as universal arrows** — Unit $\eta_C : C \to GFC$ and counit $\varepsilon_D : FGD \to D$ as universal arrows arising via the Yoneda lemma; naturality lemma for transposes; triangle identities; alternative definition of an adjunction as a pair $(\eta,\varepsilon)$ satisfying the triangle identities; extended worked example — the adjunction $P \dashv U$ between categories and multigraphs (free/path category $P(G)$, underlying-multigraph functor $U$) : [[Adjunctions|Link]]
- **4.3 Adjunctions, limits and colimits** — Right-adjoints are continuous (preserve limits), left-adjoints are cocontinuous (preserve colimits); proof via a bijection of cones $\mathrm{Cone}(LC,E)\cong\mathrm{Cone}(C,R\circ E)$; examples (forgetful functors on $\mathrm{Top}$, $\mathrm{Vect}$, $\mathrm{Grp}$ preserving limits/colimits; product/coproduct of categories via the multigraph adjunction) : [[Adjunctions|Link]]
- **4.4 The adjoint functor theorem for preorders** — Adjoint functor theorem: a meet-preserving monotone map $g:Y\to X$ (with $Y$ having all infima) has a lower adjoint $f(x)=\inf\{y\in Y \mid x \le g(y)\}$; dual statement for suprema; applied to convex hulls and topological closure as canonical examples of Galois-connection constructions : [[Adjunctions|Link]]

**Key Questions:**
1. Why must an adjunction be defined by a *natural* bijection of hom-sets rather than a mere pointwise bijection, and how does the Yoneda lemma force the unit and counit to satisfy the triangle identities?
2. In what precise sense do left-adjoints "not lose information" about how complex objects are built from simple ones, and why is this exactly what lets the adjoint functor theorem reconstruct a left-adjoint from limit-preservation alone?
3. Using the categories-multigraphs adjunction $P \dashv U$, what concretely do the unit and counit represent (in terms of "primitive morphisms" vs. actual composition), and how does this generalize the earlier free-vector-space example?

---

### Chapter 5: Monads and comonads (pp. 132–179)

**Summary:** This chapter introduces monads and comonads from two complementary angles — as consistent ways of extending spaces with generalized elements/functions (Kleisli side) and as theories of algebraic operations with results (Eilenberg-Moore side) — mirroring the same duality for comonads as carriers of extra information and as generators of processes/coalgebras. It closes by showing every adjunction induces a monad and comonad, and that the two constructions bracket every adjunction between the Kleisli and Eilenberg-Moore extremes, culminating in the monadicity of the categories–multigraphs adjunction. : [[Monads-Comonads-and-Adjunctions|Link]]

**Key Definitions & Concepts by Section:**
- **5.0 (chapter opening)** — Monad $(T,\eta,\mu)$: endofunctor $T$ with unit $\eta: \mathrm{id} \Rightarrow T$ and multiplication $\mu: TT \Rightarrow T$ satisfying unitality and associativity; comonad $(C,\varepsilon,\nu)$ defined dually as a monad on $\mathcal{C}^{op}$, with counit $\varepsilon$ and comultiplication $\nu$.
- **5.1 Monads as extensions of spaces** — Idea: a monad consistently extends spaces with generalized elements/functions. Examples: power set monad $(P,\sigma,\cup)$, distribution/Giry/Radon monads, list monad, writer monad $T_M$ (monoid-indexed "side effects"). : [[Monads|Link]]
  - **5.1.1 Kleisli morphisms** — Kleisli morphism $k: X \to TY$ ("generalized function"); Kleisli composition via $\mu \circ Th \circ k$; Kleisli category $\mathcal{C}_T$; examples: relations (power set), stochastic maps/Markov kernels (Chapman–Kolmogorov formula), writer-monad Kleisli morphisms as "logging" computations. : [[Comonads|Link1]], [[Monads|Link2]]
  - **5.1.2 The Kleisli adjunction** — Functors $L_T: \mathcal{C} \to \mathcal{C}_T$ (identity on objects, $\eta \circ f$) and $R_T: \mathcal{C}_T \to \mathcal{C}$ ($\mu \circ Tk$); $R_T \circ L_T \cong T$, $L_T \dashv R_T$, unit of adjunction $=\eta$. : [[Comonads|Link1]], [[Monads-Comonads-and-Adjunctions|Link2]], [[Monads|Link3]]
  - **5.1.3 Closure operators and idempotent monads** — Closure operator on a poset (monotone, extensive, idempotent); idempotent monad: $\mu$ is a natural isomorphism; examples: Cauchy completion, quotient by equivalence relation, Kolmogorov quotient, abelianization. : [[Monads|Link]]
- **5.2 Monads as theories of operations** — Idea: a monad is a consistent choice of formal expressions with a way to evaluate them. Free commutative monoid monad $F$ (formal sums), list monad as free monoid monad, "formal convex combinations" reading of the distribution monad. : [[Monads|Link]]
  - **5.2.1 Algebras of a monad** — $T$-algebra (Eilenberg-Moore algebra) $(A, e: TA \to A)$ satisfying unit and composition axioms; morphism of $T$-algebras; Eilenberg-Moore category $\mathcal{C}^T$; examples: algebras of $F$ = commutative monoids, algebras of list monad = monoids, algebras of distribution monad = convex spaces, algebras of writer monad $T_M$ = $M$-sets ($M$-actions); the algebra structure map is a coequalizer of $\mu, Te$. : [[Monads|Link]]
  - **5.2.2 Free algebras** — Free $T$-algebra $(TX,\mu)$; examples: $LX$ (lists/words), $FX$ (formal sums), $\mathcal{P}X$ (simplices, with extreme points as $\delta(X)$). : [[Monads-Comonads-and-Adjunctions|Link1]], [[Monads|Link2]]
  - **5.2.3 The Eilenberg-Moore adjunction** — Forgetful functor $R^T: \mathcal{C}^T \to \mathcal{C}$; free functor $L^T: \mathcal{C} \to \mathcal{C}^T$, $X \mapsto (TX,\mu)$; $R^T \circ L^T \cong T$, $L^T \dashv R^T$ with unit $\eta$, counit given by algebra structure maps $e$; universal property: every $f: X \to A$ into a $T$-algebra factors uniquely through $\eta$, recovering universal properties of free vector spaces, free monoids, and the simplex/expectation-value construction. : [[Monads-Comonads-and-Adjunctions|Link1]], [[Monads|Link2]]
- **5.3 Comonads as extra information** — Idea: a comonad equips spaces with extra information that some morphisms can access. Reader comonad $C_E$ ($X \mapsto X\times E$, discard/copy); stream comonad $S$ (infinite sequences, "history"); universal covering comonad on pointed path-connected locally contractible spaces (idempotent). : [[Comonads|Link]]
  - **5.3.1 Co-Kleisli morphisms** — Co-Kleisli morphism $k: CX \to Y$ ("function needing extra information/context"); co-Kleisli composition via $\nu, Ck, h$; co-Kleisli category $\mathcal{C}^C$; examples: reader comonad ⇒ functions needing an extra argument, stream comonad ⇒ history-dependent (non-Markovian) processes, complex logarithm as a co-Kleisli morphism of the universal covering comonad, Bloch-wave functions in a periodic crystal. : [[Comonads|Link]]
  - **5.3.2 The co-Kleisli adjunction** — Functors $R^C: \mathcal{C} \to \mathcal{C}^C$ and $L_C: \mathcal{C}^C \to \mathcal{C}$; $L_C \circ R^C \cong C$, $L_C \dashv R^C$, counit $=\varepsilon$ — the co-Kleisli adjunction, with left/right roles reversed relative to the Kleisli case. : [[Comonads|Link]]
- **5.4 Comonads as processes on spaces** — Idea: a comonad constructs processes of a given structure together with default strategies/trajectories. Stream comonad as a dynamical system (shift map); rooted-tree comonad $U$ on pointed multigraphs (walks from a base point; idempotent; a.k.a. discrete universal covering comonad). : [[Comonads|Link]]
  - **5.4.1 Coalgebras of a comonad** — $C$-coalgebra $(A, i: A \to CA)$ satisfying counit and comultiplication ("coalgebra square") axioms; examples: coalgebras of stream comonad = dynamical systems, coalgebras of rooted-tree comonad = rooted trees, coalgebras of universal covering comonad = simply connected locally contractible spaces, coalgebras of reader comonad = sets with a default value $e: A \to E$; morphism of $C$-coalgebras; co-Eilenberg-Moore category $\mathcal{C}_C$; a comonad is idempotent iff all coalgebra structure maps are isomorphisms. : [[Comonads|Link]]
  - **5.4.2 The adjunction of coalgebras** — Forgetful functor $L_C: \mathcal{C}_C \to \mathcal{C}$ has right adjoint $R^C: \mathcal{C} \to \mathcal{C}_C$, $X \mapsto (CX,\nu)$ ("cofree" coalgebra); universal property as "lifting to the dynamics"; homotopy lifting property for the universal covering comonad. : [[Comonads|Link]]
- **5.5 Adjunctions, monads and comonads** — Every adjunction $F \dashv G$ induces a monad $G F$ on $\mathcal{C}$ and a comonad $FG$ on $\mathcal{D}$; comparison functors $J: \mathcal{C}_T \to \mathcal{D}$ and $K: \mathcal{D} \to \mathcal{C}^T$ making the Kleisli/Eilenberg-Moore triangles commute, so every adjunction inducing $T$ factors between $\mathcal{C}_T$ and $\mathcal{C}^T$; monadic adjunction/monadic functor: $K$ is an equivalence of categories; the Kleisli category embeds as the full subcategory of free algebras in $\mathcal{C}^T$; Beck's monadicity theorem mentioned but not proved. Closing worked example (**5.5.1**): the adjunction between categories and multigraphs is monadic — $T$-algebras of the induced monad are exactly small categories, and $T$-algebra morphisms are exactly functors. : [[Monads-Comonads-and-Adjunctions|Link]]

**Key Questions:**
1. Why do the Kleisli category and the Eilenberg-Moore category of the same monad $T$ represent "opposite extremes" among all adjunctions inducing $T$, and in what sense does every such adjunction factor through both via the comparison functors?
2. For the power set monad, the distribution monad, and the writer monad $T_M$, what concretely is a Kleisli morphism, its composition, and its algebras — and how do these recover relations, stochastic maps, and monoid actions respectively?
3. What does it mean for a monad or comonad to be idempotent, and why does this force every $T$-algebra structure map (resp. $C$-coalgebra structure map) to be an isomorphism?

---
