# Categorical Logic and Type Theory — Guidelines

## Header

**Title:** Categorical Logic and Type Theory
**Author(s):** Bart Jacobs
**Publication:** Studies in Logic and the Foundations of Mathematics, Volume 141, Elsevier Science B.V., 1999

**Brief Summary:**
This book gives a systematic, unified presentation of logic and type theory from a categorical perspective, using the notion of a *fibred category* as the single organizing concept. It develops fibred category theory from scratch and then reconstructs, on top of it, simple type theory, equational logic, first and higher order predicate logic, polymorphic type theory, dependent type theory, and their higher order combinations (up to the Calculus of Constructions), together with concrete models drawn from sets, domains, realizability (PERs, $\omega$-sets, the effective topos) and toposes. The organizing thesis is that "a logic is always a logic over a type theory," which categorically becomes one fibration sitting on top of another.

**Intent of the Author:**
Jacobs, building on his PhD thesis on categorical semantics of type theories via fibred categories, wrote the book to fully exploit and make explicit the connections between logic, type theory, and fibred category theory that his thesis had not yet drawn out — aiming it at logicians, type theorists, category theorists, and theoretical computer scientists who want a single framework for comparing these systems.

---

## Topic List

1. **Fibred Category Theory** : [[Fibred-Category-Theory|Link]]
   - Fibrations and Cartesian morphisms : [[Fibred-Category-Theory|Link]]
   - Cloven versus split fibrations : [[Fibred-Category-Theory|Link]]
   - Substitution, reindexing, and change-of-base functors : [[Fibred-Category-Theory|Link]]
   - Weakening and contraction as special substitutions : [[Fibred-Category-Theory|Link]]
   - Composition of fibrations : [[Fibred-Category-Theory|Link]]
   - Categories and 2-categories of fibrations : [[Fibred-Category-Theory|Link]]
   - Fibrewise structure and fibred Cartesian closed categories : [[Fibred-Category-Theory|Link]]
   - Fibred products, coproducts, and the Beck–Chevalley condition : [[Fibred-Category-Theory|Link]]
   - The Frobenius law : [[Fibred-Category-Theory|Link]]
   - Complete and cocomplete fibrations : [[Fibred-Category-Theory|Link]]
   - Opfibrations and bifibrations : [[Fibred-Category-Theory|Link]]
   - Fibred spans : [[Fibred-Category-Theory|Link]]
   - Category theory over a fibration : [[Fibred-Category-Theory|Link]]
   - Locally small and definable fibrations : [[Fibred-Category-Theory|Link]]

2. **Indexed Categories and the Grothendieck Construction** : [[Indexed-Categories-and-the-Grothendieck-Construction|Link]]
   - Indexed categories as pseudo-functors into $\mathbf{Cat}$ : [[Indexed-Categories-and-the-Grothendieck-Construction|Link]]
   - Split indexed categories : [[Indexed-Categories-and-the-Grothendieck-Construction|Link]]
   - The Grothendieck construction : [[Indexed-Categories-and-the-Grothendieck-Construction|Link]]
   - Equivalence between indexed categories and split fibrations : [[Indexed-Categories-and-the-Grothendieck-Construction|Link]]
   - Opposite of an indexed category versus opposite of a fibration : [[Indexed-Categories-and-the-Grothendieck-Construction|Link]]

3. **Standard Fibrations Used Throughout the Book** : [[Standard-Fibrations-Used-Throughout-the-Book|Link]]
   - The family fibration : [[Standard-Fibrations-Used-Throughout-the-Book|Link]]
   - The codomain fibration : [[Fibred-Category-Theory|Link1]], [[Standard-Fibrations-Used-Throughout-the-Book|Link2]]
   - The subobject fibration : [[Nuclei-Separated-Objects-and-Sheaves|Link1]], [[Standard-Fibrations-Used-Throughout-the-Book|Link2]], [[Subset-Types-and-Quotient-Types|Link3]]
   - The simple fibration and simple slices : [[Standard-Fibrations-Used-Throughout-the-Book|Link]]
   - CT-structures : [[Nuclei-Separated-Objects-and-Sheaves|Link1]], [[First-Order-Predicate-Logic|Link2]], [[Functorial-Lawvere-Semantics|Link3]]
   - Fibrations of relations and partial equivalence relations : [[Standard-Fibrations-Used-Throughout-the-Book|Link]]
   - Fibrations of signatures : [[Standard-Fibrations-Used-Throughout-the-Book|Link]]

4. **Realizability Models: $\omega$-Sets and PERs** : [[Realizability-Models-Omega-Sets-and-PERs|Link]]
   - $\omega$-sets and existence predicates : [[Realizability-Models-Omega-Sets-and-PERs|Link]]
   - Partial equivalence relations : [[Realizability-Models-Omega-Sets-and-PERs|Link1]], [[Standard-Fibrations-Used-Throughout-the-Book|Link2]]
   - Tracking and codes for morphisms : [[Realizability-Models-Omega-Sets-and-PERs|Link]]
   - Reflective subcategory relationships among sets, $\omega$-sets, and PERs : [[Realizability-Models-Omega-Sets-and-PERs|Link]]
   - Kleene realisability and partial combinatory algebras : [[Realizability-Models-Omega-Sets-and-PERs|Link]]

5. **Functorial (Lawvere) Semantics** : [[Functorial-Lawvere-Semantics|Link1]], [[Simple-Type-Theory|Link2]]
   - Many-typed signatures : [[Functorial-Lawvere-Semantics|Link]]
   - Classifying categories and term models : [[Equational-Logic|Link]]
   - Models as product-preserving functors : [[Functorial-Lawvere-Semantics|Link]]
   - The generic model : [[Functorial-Lawvere-Semantics|Link1]], [[Simple-Type-Theory|Link2]], [[Toposes|Link3]]
   - Adjunction between signatures and categories with finite products : [[Functorial-Lawvere-Semantics|Link]]

6. **Simple Type Theory** : [[Simple-Type-Theory|Link]]
   - Contexts, typing judgements, and structural rules : [[Simple-Type-Theory|Link]]
   - Weakening, contraction, and exchange : [[Fibred-Category-Theory|Link]]
   - Cartesian closed and bicartesian closed categorical semantics : [[Simple-Type-Theory|Link]]
   - Exponents as simple products in a simple fibration : [[Simple-Type-Theory|Link]]
   - The untyped lambda calculus as a degenerate simple type theory : [[Simple-Type-Theory|Link]]
   - Data types with simple parameters : [[Simple-Type-Theory|Link]]
   - Hagino signatures for inductive and co-inductive types : [[Polymorphic-Type-Theory|Link]]
   - Algebras, coalgebras, and Lambek's Lemma

7. **Propositions as Types** : [[Propositions-as-Types|Link]]
   - The Curry–Howard correspondence : [[Propositions-as-Types|Link]]
   - Proofs as terms and propositions as objects : [[Propositions-as-Types|Link]]
   - Beta and eta conversion as proof normalization : [[Propositions-as-Types|Link]]

8. **Equational Logic** : [[Equational-Logic|Link]]
   - Sequents with explicit type and proposition contexts
   - Internal versus external equality : [[Equational-Logic|Link]]
   - Lawvere's equality as a left adjoint to contraction : [[Equational-Logic|Link]]
   - Algebraic and conditional equations : [[Equational-Logic|Link]]
   - Classifying categories of algebraic specifications : [[Equational-Logic|Link1]], [[Functorial-Lawvere-Semantics|Link2]]
   - Eq-fibrations and fibred equality : [[Equational-Logic|Link]]
   - Very strong equality : [[Equational-Logic|Link1]], [[Nuclei-Separated-Objects-and-Sheaves|Link2]], [[Subset-Types-and-Quotient-Types|Link3]]

9. **First Order Predicate Logic** : [[First-Order-Predicate-Logic|Link]]
   - Signatures with predicate symbols : [[First-Order-Predicate-Logic|Link]]
   - Regular, coherent, and full first order logic : [[First-Order-Predicate-Logic|Link]]
   - Existential and universal quantification as adjoints to weakening : [[Fibred-Category-Theory|Link]]
   - Regular, coherent, and first order fibrations : [[First-Order-Predicate-Logic|Link]]
   - Internal language and internal logic of a fibration : [[First-Order-Predicate-Logic|Link]]
   - Models of predicate logic (set-theoretic, Kripke, realisability, cylindric algebra)

10. **Regular and Coherent Categories** : [[Regular-and-Coherent-Categories|Link]]
    - Images and stable image factorisation : [[Regular-and-Coherent-Categories|Link]]
    - Covers as regular epimorphisms : [[Regular-and-Coherent-Categories|Link]]
    - The mono-cover factorisation system : [[Regular-and-Coherent-Categories|Link]]
    - Coherent categories and distributive joins : [[Regular-and-Coherent-Categories|Link]]
    - Logoses : [[Toposes|Link]]

11. **Subset Types and Quotient Types** : [[Subset-Types-and-Quotient-Types|Link]]
    - Formation, introduction, and elimination rules for subset types : [[Subset-Types-and-Quotient-Types|Link]]
    - Comprehension with unit : [[First-Order-Dependent-Type-Theory|Link]]
    - Formation, introduction, and elimination rules for quotient types : [[Subset-Types-and-Quotient-Types|Link]]
    - Duality between subset types and quotient types : [[Subset-Types-and-Quotient-Types|Link]]
    - Effective quotients and exact categories : [[Subset-Types-and-Quotient-Types|Link]]
    - Unique choice and logical characterisation of subobject fibrations : [[Subset-Types-and-Quotient-Types|Link]]

12. **Higher Order Predicate Logic** : [[Higher-Order-Predicate-Logic|Link]]
    - A distinguished type of propositions : [[Higher-Order-Predicate-Logic|Link]]
    - Extensionality of entailment : [[Higher-Order-Predicate-Logic|Link]]
    - Leibniz equality : [[Higher-Order-Predicate-Logic|Link]]
    - Power types and membership : [[Higher-Order-Predicate-Logic|Link]]
    - Generic objects and the fibred Yoneda lemma : [[Higher-Order-Predicate-Logic|Link]]

13. **Toposes** : [[Toposes|Link]]
    - Higher order fibrations and triposes : [[Toposes|Link]]
    - The logical definition of a topos via subobject fibrations : [[Subset-Types-and-Quotient-Types|Link1]], [[Fibred-Category-Theory|Link2]], [[Toposes|Link3]], [[Standard-Fibrations-Used-Throughout-the-Book|Link4]]
    - The elementary definition of a topos : [[Toposes|Link]]
    - Powerobjects and Kock's characterisation of a topos : [[Toposes|Link]]
    - Local Cartesian closedness of a topos : [[Toposes|Link]]
    - Well-powered fibrations : [[Standard-Fibrations-Used-Throughout-the-Book|Link1]], [[First-Order-Predicate-Logic|Link2]], [[Toposes|Link3]], [[Fibred-Category-Theory|Link4]]
    - Logical morphisms and geometric morphisms : [[Nuclei-Separated-Objects-and-Sheaves|Link]]

14. **Nuclei, Separated Objects, and Sheaves** : [[Nuclei-Separated-Objects-and-Sheaves|Link]]
    - Lawvere-Tierney topologies : [[Toposes|Link1]], [[Nuclei-Separated-Objects-and-Sheaves|Link2]]
    - The double negation nucleus : [[Nuclei-Separated-Objects-and-Sheaves|Link1]], [[The-Effective-Topos|Link2]]
    - Grothendieck topologies and sites : [[Nuclei-Separated-Objects-and-Sheaves|Link]]
    - Closed and dense subobjects : [[Nuclei-Separated-Objects-and-Sheaves|Link]]
    - Separated objects and sheaves : [[Nuclei-Separated-Objects-and-Sheaves|Link]]
    - Sheafification and separated reflection

15. **The Effective Topos** : [[The-Effective-Topos|Link]]
    - Realizability semantics and the Set($p$) construction : [[Realizability-Models-Omega-Sets-and-PERs|Link1]], [[The-Effective-Topos|Link2]]
    - Canonically separated objects, sheaves, and modest sets : [[Nuclei-Separated-Objects-and-Sheaves|Link]]
    - Global sections functor : [[The-Effective-Topos|Link]]
    - Natural numbers object and recursive mathematics : [[The-Effective-Topos|Link]]
    - Church's Thesis, Markov's Principle, and the Uniformity Principle
    - PERs as subquotients of the natural numbers object : [[The-Effective-Topos|Link]]

16. **Internal Category Theory** : [[Internal-Category-Theory|Link]]
    - Internal categories, functors, and natural transformations : [[Internal-Category-Theory|Link]]
    - Internal adjunctions and internal limits and exponents : [[First-Order-Predicate-Logic|Link1]], [[First-Order-Dependent-Type-Theory|Link2]], [[Equational-Logic|Link3]]
    - Externalisation of an internal category : [[Full-Higher-Order-Dependent-Type-Theory|Link1]], [[Internal-Category-Theory|Link2]], [[First-Order-Predicate-Logic|Link3]]
    - Small fibrations and full internal categories : [[Indexed-Categories-and-the-Grothendieck-Construction|Link]]
    - Internal diagrams : [[Internal-Category-Theory|Link]]
    - Completeness of small fibred categories : [[Fibred-Category-Theory|Link1]], [[Full-Higher-Order-Dependent-Type-Theory|Link2]]

17. **Polymorphic Type Theory** : [[Polymorphic-Type-Theory|Link]]
    - First, second, and higher order polymorphic lambda calculus
    - Type variables and kind contexts
    - Polymorphic signatures : [[Polymorphic-Type-Theory|Link]]
    - ML-style let polymorphism : [[Polymorphic-Type-Theory|Link]]
    - Encoding of inductive and co-inductive types via weak (co)initiality : [[Polymorphic-Type-Theory|Link]]
    - Reynolds' impossibility theorem for set-theoretic models : [[First-Order-Predicate-Logic|Link]]
    - Polymorphic fibrations and PER models : [[Polymorphic-Type-Theory|Link]]
    - Relational parametricity : [[Polymorphic-Type-Theory|Link]]
    - Logic over polymorphic type theory : [[Polymorphic-Type-Theory|Link]]

18. **First Order Dependent Type Theory** : [[First-Order-Dependent-Type-Theory|Link]]
    - Dependent product and dependent sum types
    - Equality (identity) types : [[Polymorphic-Type-Theory|Link1]], [[Strength-of-Sum-and-Equality-Types|Link2]], [[Subset-Types-and-Quotient-Types|Link3]]
    - Weak versus strong elimination rules : [[Equational-Logic|Link1]], [[First-Order-Dependent-Type-Theory|Link2]]
    - Dependent type theory as a logical framework : [[First-Order-Dependent-Type-Theory|Link1]], [[Full-Higher-Order-Dependent-Type-Theory|Link2]], [[Polymorphic-Dependent-Type-Theory|Link3]], [[Dependent-Predicate-Logic|Link4]]
    - Term models and display maps : [[First-Order-Dependent-Type-Theory|Link]]
    - Comprehension categories : [[First-Order-Dependent-Type-Theory|Link1]], [[Polymorphic-Dependent-Type-Theory|Link2]]
    - Closed comprehension categories : [[First-Order-Dependent-Type-Theory|Link]]
    - Domain theoretic models of dependent types : [[First-Order-Dependent-Type-Theory|Link1]], [[Polymorphic-Dependent-Type-Theory|Link2]], [[Full-Higher-Order-Dependent-Type-Theory|Link3]], [[First-Order-Predicate-Logic|Link4]]

19. **Dependent Predicate Logic** : [[Dependent-Predicate-Logic|Link]]
    - Propositions and types both indexed by term variables : [[First-Order-Dependent-Type-Theory|Link1]], [[Polymorphic-Type-Theory|Link2]]
    - Dependent subset types : [[Dependent-Predicate-Logic|Link]]
    - Dependent quotient types : [[Dependent-Predicate-Logic|Link]]
    - DPL-structures : [[Dependent-Predicate-Logic|Link]]

20. **Polymorphic Dependent Type Theory** : [[Polymorphic-Dependent-Type-Theory|Link]]
    - Kinds over kinds, types over types, and types over kinds combined : [[Polymorphic-Type-Theory|Link]]
    - PDTT-structures : [[Polymorphic-Dependent-Type-Theory|Link]]
    - The higher order axiom Type over Kind : [[Dependent-Predicate-Logic|Link1]], [[Toposes|Link2]], [[Higher-Order-Predicate-Logic|Link3]]
    - Ideal models : [[Polymorphic-Dependent-Type-Theory|Link]]

21. **Strength of Sum and Equality Types** : [[Strength-of-Sum-and-Equality-Types|Link]]
    - Weak, strong, and very strong sums
    - Weak, strong, and very strong equality : [[Equational-Logic|Link1]], [[First-Order-Dependent-Type-Theory|Link2]], [[Nuclei-Separated-Objects-and-Sheaves|Link3]], [[Subset-Types-and-Quotient-Types|Link4]]
    - Orthogonality of canonical comparison maps
    - Transfer of strength between sum types over different universes

22. **Full Higher Order Dependent Type Theory** : [[Full-Higher-Order-Dependent-Type-Theory|Link]]
    - The dependency relation between syntactic universes : [[Full-Higher-Order-Dependent-Type-Theory|Link]]
    - Classification of type theories by dependency : [[Full-Higher-Order-Dependent-Type-Theory|Link]]
    - The Calculus of Constructions : [[First-Order-Predicate-Logic|Link]]
    - Kinds depending on types : [[Polymorphic-Type-Theory|Link]]
    - Fibred reflection between types and kinds : [[Full-Higher-Order-Dependent-Type-Theory|Link]]
    - Girard's paradox : [[First-Order-Dependent-Type-Theory|Link1]], [[Polymorphic-Type-Theory|Link2]], [[Strength-of-Sum-and-Equality-Types|Link3]]
    - FhoDTT-structures and realizability models : [[Full-Higher-Order-Dependent-Type-Theory|Link]]
    - Completeness of PERs in the effective topos : [[Full-Higher-Order-Dependent-Type-Theory|Link1]], [[The-Effective-Topos|Link2]]

---

## Chapter Summaries

### Chapter 0: Prospectus (pp. 1–18)

**Summary:** This introductory chapter sets out the book's central thesis — "a logic is always a logic over a type theory" — and previews how fibred category theory will unify the treatment of simple, dependent, and polymorphic type theories and the logics built on top of them, illustrated concretely by working out the fibred structure of ordinary sets (predicates, quantifiers, comprehension, quotients, higher order logic).

**Key Definitions & Concepts by Section:**
- **0.1 Logic, type theory, and fibred category theory** — type theory as a "theory of sorts" classifying values via an inhabitation relation $t:\sigma$; three basic type theories: simple type theory (STT, no indexing), dependent type theory (DTT, types indexed by term variables), polymorphic type theory (PTT, types indexed by type variables); simple/dependent/polymorphic predicate logic (SPL/DPL/PPL) as logic "plugged onto" a type theory; a fibration $p:\mathbb{E}\to\mathbb{B}$ as a total category $\mathbb{E}$ (logic or dependent structure) varying over a base category $\mathbb{B}$ (type theory); the family fibration $\mathrm{Fam}(\mathbb{C})\to\mathbf{Sets}$ as the standard example; six recurring categorical phenomena: contexts-as-indices, substitution functors (with weakening/contraction as special cases along projections/diagonals), logical operations as adjoints, type dependency as indexed/fibred categories, functorial semantics via classifying categories, and propositions-as-types via type-indexed substitution functors; the fundamental adjunctions $\exists,\Sigma \dashv \text{weakening} \dashv \forall,\Pi$, $\text{equality}\dashv\text{contraction}$, $\text{truth}\dashv\text{comprehension}$, $\text{quotients}\dashv\text{equality}$. : [[Fibred-Category-Theory|Link]]
- **0.2 The logic and type theory of sets** — the fibration $\mathbf{Pred}\to\mathbf{Sets}$ of predicates (subsets) over sets, with substitution/weakening/contraction functors $u^{*}$; fibrewise Boolean algebra structure of $\mathbf{Pred}$ corresponding to propositional connectives; quantifiers $\exists,\forall:P(I\times J)\to P(I)$ as left/right adjoints to weakening $\pi^{*}$, via $\exists\dashv\pi^{*}\dashv\forall$; equality $\mathrm{Eq}(X)$ as left adjoint to the contraction functor $\delta^{*}$; comprehension $\{-\}:\mathbf{Pred}\to\mathbf{Sets}$ as right adjoint to the truth functor $\mathbb{1}:\mathbf{Sets}\to\mathbf{Pred}$; quotients $I/R$ as left adjoint to the equality functor $\mathrm{Eq}:\mathbf{Sets}\to\mathbf{Rel}$; characteristic morphisms into $2=\{0,1\}$ making $\mathbf{Sets}$ a topos (higher order logic); the family fibration $\mathrm{Fam}(\mathbf{Sets})\to\mathbf{Sets}$ and dependent sum/product $\coprod,\prod$ as left/right adjoints to "dependent" weakening along $\pi:\{I\mid X\}\to I$. : [[Polymorphic-Type-Theory|Link1]], [[Propositions-as-Types|Link2]]

**Key Questions:**
1. In what precise sense does the slogan "a logic is always a logic over a type theory" get cashed out categorically as one fibration sitting on top of another?
2. Why are the quantifiers $\exists,\forall$ and equality described as adjoints to *weakening* and *contraction* specifically, rather than to arbitrary substitution functors — and how does this refine Lawvere's original formulation?
3. How does the fibration $\mathbf{Pred}\to\mathbf{Sets}$ already contain, in miniature, all the ingredients (propositional structure, quantification, comprehension, quotients, characteristic morphisms) that the rest of the book will axiomatize abstractly?

---

### Chapter 1: Introduction to fibred category theory (pp. 19–118)

**Summary:** This chapter develops the basic machinery of fibred category theory that underlies the whole book: what a fibration is, how it can be presented in cloven/split form or equivalently as an indexed category, how fibrations combine (change-of-base, composition, morphisms of fibrations), and how ordinary categorical structure (products, coproducts, adjunctions) generalizes fibrewise and "between fibres." : [[Fibred-Category-Theory|Link1]], [[Internal-Category-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **1.1 Fibrations** — pointwise indexing $(X_i)_{i\in I}$ vs. display indexing $\varphi:X\to I$ of families, and their equivalence; codomain functor $\mathrm{cod}:\mathbf{Sets}^{\to}\to\mathbf{Sets}$; fibre category $\mathbb{E}_I=p^{-1}(I)$; a **Cartesian morphism** $f:X\to Y$ over $u:I\to J$ as a universal lifting of $u$ (unique factorization property); a **fibration** $p:\mathbb{E}\to\mathbb{B}$ as a functor with Cartesian liftings of every $u:I\to pY$; slice category $\mathbb{B}/I$ and the codomain fibration on a category with pullbacks; Cartesian liftings unique up to vertical isomorphism. : [[Fibred-Category-Theory|Link1]], [[Standard-Fibrations-Used-Throughout-the-Book|Link2]], [[Full-Higher-Order-Dependent-Type-Theory|Link3]], [[Realizability-Models-Omega-Sets-and-PERs|Link4]]
- **1.2 Some concrete examples: sets, ω-sets and PERs** — the family fibration $\mathrm{Fam}(\mathbb{C})\to\mathbf{Sets}$; **ω-sets** $(X,E)$ with existence predicate $E(x)\subseteq\mathbb{N}$ and morphisms tracked by a recursive code; category $\omega\text{-}\mathbf{Sets}$ has finite limits and exponents; **partial equivalence relations (PERs)** on $\mathbb{N}$, with domain $|R|$, quotient $\mathbb{N}/R$; category $\mathbf{PER}$ has finite limits/exponents; reflective subcategory chain $\mathbf{Sets}\hookrightarrow\omega\text{-}\mathbf{Sets}\hookleftarrow\mathbf{PER}$. : [[Fibred-Category-Theory|Link]]
- **1.3 Some general examples** — **simple fibration** $s(\mathbb{B})\to\mathbb{B}$ on a category with products, with simple slice $\mathbb{B}/\!/I$; **CT-structure** $(\mathbb{B},T)$ (category of contexts + collection of types) and the associated simple fibration $s(T)\to\mathbb{B}$; fibration of **monos** $\mathrm{Mono}(\mathbb{B})\to\mathbb{B}$ and the derived **subobject fibration** $\mathrm{Sub}(\mathbb{B})\to\mathbb{B}$ (preordered/fibred-preorder); the three "type theoretic" fibrations singled out for the whole book: simple, codomain, subobject; category $\mathrm{Rel}(\mathbb{B})$ of relations $R\rightarrowtail I\times I$, with reflexive/symmetric/transitive defined diagrammatically, giving equivalence-relation and PER fibrations. : [[Realizability-Models-Omega-Sets-and-PERs|Link1]], [[First-Order-Dependent-Type-Theory|Link2]]
- **1.4 Cloven and split fibrations** — a **cleavage** (chosen Cartesian liftings) makes a fibration **cloven**, inducing substitution/reindexing functors $u^{*}$; a fibration is **split** if $\mathrm{id}^{*}\cong\mathrm{id}$ and $u^{*}v^{*}\cong(v\circ u)^{*}$ hold as actual identities (not just natural isos); **indexed category** as a pseudo-functor $\Phi:\mathbb{B}^{op}\to\mathbf{Cat}$, **split indexed category** as an honest functor; every fibration is fibred-equivalent to a split one. : [[Fibred-Category-Theory|Link]]
- **1.5 Change-of-base and composition for fibrations** — pulling back a fibration $p$ along $K:\mathbb{A}\to\mathbb{B}$ yields a new fibration $K^{*}(p)$ (cloven/split if $p$ is); composition of fibrations is again a fibration. : [[Fibred-Category-Theory|Link]]
- **1.6 Fibrations of signatures** — a many-typed **signature** $\Sigma=(T,\mathcal{F})$ with function symbols $F:\sigma_1,\dots,\sigma_n\to\sigma_{n+1}$; category $\mathbf{Sign}$ of signatures as a split fibration over $\mathbf{Sets}$ via change-of-base from $\mathrm{Fam}(\mathbf{Sets})$; term calculus and free/bound variables, substitution; **model (algebra)** for $\Sigma$ as a family of carrier sets plus interpretations of function symbols; category $\mathbf{S}\text{-}\mathbf{Model}$ of set-theoretic models, fibred over $\mathbf{Sign}$ over $\mathbf{Sets}$. : [[Standard-Fibrations-Used-Throughout-the-Book|Link]]
- **1.7 Categories of fibrations** — morphisms of fibrations (Cartesian-morphism-preserving functors) organized into 2-categories $\mathbf{Fib}$, $\mathbf{Fib}(\mathbb{B})$, $\mathbf{Fib}_{\mathrm{split}}$; pullback-preserving functors extend to morphisms between subobject/codomain fibrations; 2-cells as pairs of natural transformations. : [[Fibred-Category-Theory|Link1]], [[Indexed-Categories-and-the-Grothendieck-Construction|Link2]]
- **1.8 Fibrewise structure and fibred adjunctions** — **fibred (fibrewise) structure**: a fibration has fibred $\Diamond$'s if every fibre has $\Diamond$'s and reindexing preserves them; **(split) fibred CCC** = fibred finite products + exponents; codomain fibration is a fibred CCC iff the base is locally Cartesian closed (LCCC); fibred adjunctions as adjunctions internal to $\mathbf{Fib}(\mathbb{B})$. : [[Fibred-Category-Theory|Link]]
- **1.9 Fibred products and coproducts** — **simple products/coproducts**: right/left adjoints $\prod_{(I,J)},\coprod_{(I,J)}$ to weakening functors $\pi_J^{*}$ along Cartesian projections, subject to the **Beck–Chevalley condition**; general **products/coproducts** as adjoints $\prod_u,\coprod_u$ to arbitrary substitution functors $u^{*}$, again with Beck–Chevalley; a fibration is **complete** if it has products $\prod_u$ and fibred finite limits (dually **cocomplete**); the **Frobenius** law $\coprod_{(I,J)}(Y\times Z)\cong Y\times\coprod_{(I,J)}(Z)$ for fibred CCCs with coproducts. : [[Fibred-Category-Theory|Link]]
- **1.10 Indexed categories** — the **Grothendieck construction** turning an indexed category $\Phi:\mathbb{B}^{op}\to\mathbf{Cat}$ into a fibration $\int\Phi\to\mathbb{B}$; equivalence theorem $\mathbf{ICat}\simeq\mathbf{Fib}_{\mathrm{split}}$ over $\mathbf{Cat}$; morphisms and 2-cells (modifications) of split indexed categories; opposite of an indexed category (fibrewise $\mathrm{op}$) vs. the more intricate opposite $p^{op}$ of a fibration (reversing vertical maps, due to Bénabou). : [[Fibred-Category-Theory|Link1]], [[Indexed-Categories-and-the-Grothendieck-Construction|Link2]]

**Key Questions:**
1. What exactly does a Cartesian morphism guarantee that an arbitrary lifting does not, and why does this universal property suffice to define "the" (up to iso) substitution functor $u^{*}$?
2. Why does the distinction between a fibration merely being *cloven* versus *split* matter in practice — what goes wrong (or becomes awkward) if one only has natural isomorphisms $u^{*}v^{*}\cong(vu)^{*}$ rather than equalities?
3. How do "simple" products/coproducts (adjoints to weakening along projections) differ from the general fibred products/coproducts (adjoints to arbitrary substitution), and why does the book need both notions for later chapters on type theory versus dependent type theory?

---

### Chapter 2: Simple type theory (pp. 119–168)

**Summary:** This chapter gives the syntax of simple type theory (STT) via classifying categories built from many-typed signatures, develops Lawvere's functorial semantics (models as product-preserving functors), and then gives a purely fibred account of exponent types as simple products in a simple fibration — recovering the untyped λ-calculus and parametrised (co)inductive data types as special/derived cases. : [[Simple-Type-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **2.1 The basic calculus of types and terms** — contexts $\Gamma=(v_1:\sigma_1,\dots,v_n:\sigma_n)$; typing judgement $\Gamma\vdash M:\sigma$ via identity, function-symbol, weakening, contraction, and exchange rules; substitution and the derived substitution rule; the **classifying category (term model)** $\mathfrak{C}(\Sigma)$ with contexts as objects and tuples of terms as morphisms; $\mathfrak{C}(\Sigma)$ has finite products (concatenation of contexts). : [[Simple-Type-Theory|Link]]
- **2.2 Functorial semantics** — Lawvere's **functorial semantics**: a $\Sigma$-model in $\mathbf{Sets}$ corresponds to a finite-product-preserving functor $\mathfrak{C}(\Sigma)\to\mathbf{Sets}$; generalized to a **model of $\Sigma$ in $\mathbb{B}$** as any product-preserving functor $\mathfrak{C}(\Sigma)\to\mathbb{B}$; the **generic model** (identity functor on $\mathfrak{C}(\Sigma)$); adjunction $\mathfrak{C}(-)\dashv \mathrm{Sign}(-)$ between signatures and categories with finite products; category $\mathbf{Sign}_{tr}$ of signatures and **translations** (types to contexts, function symbols to terms) as the Kleisli category of the induced monad. : [[Equational-Logic|Link1]], [[First-Order-Predicate-Logic|Link2]], [[Functorial-Lawvere-Semantics|Link3]], [[Simple-Type-Theory|Link4]]
- **2.3 Exponents, products and coproducts** — three calculi $\lambda1$ (exponents only), $\lambda1_\times$ (+finite products), $\lambda1_{(\times,+)}$ (+finite coproducts), with $\beta$/$\eta$-conversion; classifying categories $\mathfrak{C}\lambda1(\Sigma)$, $\mathfrak{C}\lambda1_\times(\Sigma)$ (Cartesian closed), $\mathfrak{C}\lambda1_{(\times,+)}(\Sigma)$ (bicartesian closed, i.e. a BiCCC); the **propositions-as-types / proofs-as-terms** correspondence (Curry–Howard) linking derivability in minimal intuitionistic logic to inhabitation of $\lambda1$-types, and $\beta/\eta$-conversion to proof normalization; **distributive signatures** and **Hagino signatures** $\sigma(X)\xrightarrow{\text{constr}} X$ / $X\xrightarrow{\text{destr}}\sigma(X)$ for (co)inductive types (naturals, lists, streams); type-theoretic coproducts are automatically distributive and coprojections are automatically injective. : [[Fibred-Category-Theory|Link1]], [[Propositions-as-Types|Link2]], [[Simple-Type-Theory|Link3]]
- **2.4 Semantics of simple type theories** — models of $\lambda1_\times$/$\lambda1_{(\times,+)}$ as (Bi)CCC-preserving functors, with a signature–model correspondence theorem; **simple $T$-products/coproducts** relative to a CT-structure $(\mathbb{B},T)$ (quantifying only over the designated types $T$, not all contexts); a **λ1-category** = a non-trivial CT-structure whose simple fibration has split simple $T$-products (i.e. exponents as simple products); Lemma: $(\mathbb{B},T)$ is a λ1-category iff $T$ is closed under exponents $X\Rightarrow Y$ with the expected universal evaluation/abstraction maps — giving exponents *without* assuming product types. : [[Simple-Type-Theory|Link]]
- **2.5 Semantics of the untyped lambda calculus as a corollary** — the untyped λ-calculus recovered as the single-type case ($T=\{\Omega\}$, $\Omega\cong\Omega\to\Omega$); **λ-category**: a category with finite products and a distinguished reflexive-type object $\Omega$ admitting `app`/`abs` operations; examples: the pure closed-term model, Scott's reflexive dcpo $D_\infty$, and any CCC with a reflexive object $\Omega\cong(\Omega\Rightarrow\Omega)$; non-extensional λ-categories via semi-adjunctions. : [[Simple-Type-Theory|Link]]
- **2.6 Simple parameters** — data types "with simple parameters" described fibrewise in the simple fibration $s(\mathbb{B})\to\mathbb{B}$: distributive coproducts (fibred coproducts) via distributivity $(I\times X)+(I\times Y)\cong I\times(X+Y)$; NNO with simple parameters as a fibred natural numbers object; **strong functors** $T:\mathbb{B}\to\mathbb{B}$ (with strength $\mathrm{st}$) shown (Plotkin) to correspond bijectively to split endofunctors of the simple fibration; **algebras/coalgebras** for a functor $T$, Lambek's Lemma (an initial algebra is a fixed point / isomorphism); initiality "with simple parameters" for Hagino signatures via strong polynomial functors. : [[Simple-Type-Theory|Link]]

**Key Questions:**
1. Why is it categorically awkward to interpret the minimal calculus $\lambda1$ (exponents only, no products) directly as exponents in a CCC, and how does casting exponents as *simple products* in a simple fibration sidestep the need for product types?
2. In what precise sense is the untyped λ-calculus "just" a simply typed calculus with one type $\Omega$ satisfying $\Omega\cong\Omega\to\Omega$, and what extra condition (non-emptiness / reflexivity) is needed to make this work categorically?
3. What does it mean for a data type (e.g. coproducts, an NNO, or a Hagino-signature algebra) to be defined "with simple parameters," and why does this fibrewise formulation (via strong functors on the simple fibration) generalize the ordinary non-parametrised notion?

---

### Chapter 3: Equational Logic (pp. 169–218)

**Summary:** This chapter begins the categorical treatment of logic by studying equational logic over simple type theory (STT), where the only atomic propositions are equations $M =_\sigma M'$ between terms; it culminates in Lawvere's description of equality as a left adjoint to contraction functors, which generalizes to all subsequent logics in the book. : [[Equational-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Logics** — specification (signature + axioms), theory (specification closed under derivability); context rules (weakening, contraction, exchange, cut, substitution) common to all logics; the classifying fibration of contexts $\mathcal{E}(\Sigma,\square) \to Cl(\Sigma)$, whose fibres are preorders of derivability and which has fibred finite products; substitution functors, and weakening/contraction as special substitution functors $\pi^*$, $\delta^*$.
- **3.2 Specifications and theories in equational logic** — internal equality $M =_\sigma M'$ (propositional) vs. external equality/conversion $M = M'$ (type-theoretic); $\Sigma$-equation, algebraic (non-conditional) vs. conditional equation; equational/algebraic specification and theory; **Lawvere equality (mate) rule** — reflexivity, symmetry, transitivity, replacement are jointly equivalent to a single adjoint "mate" rule involving contraction; categories $\mathbf{EqSpec}$, $\mathbf{AlgSpec}$. : [[Equational-Logic|Link]]
- **3.3 Algebraic specifications** — validity of an (algebraic/conditional) equation in a model $M$ (equalizer-based for conditional equations); soundness; classifying category $Cl(\Sigma,A)$ of an algebraic specification as a quotient of $Cl(\Sigma)$; models as finite-product-preserving functors; completeness theorem; every category with finite products is (equivalent to) the classifying category of its own algebraic theory (Lawvere's classical result). : [[Equational-Logic|Link]]
- **3.4 Fibred equality** — parametrised diagonal $\delta(I,J)$; a fibration has **(simple) equality** if each contraction functor $\delta(I,J)^*$ has a left adjoint $\mathrm{Eq}_{I,J}$ satisfying Beck–Chevalley; **equality satisfying Frobenius**; internal vs. external equality of parallel morphisms $u,v$; **very strong equality** (internal implies external); standard equality combinators (reflexivity, symmetry, transitivity, replacement, substitution); a fibration with coproducts satisfying Frobenius automatically has equality satisfying Frobenius. : [[Equational-Logic|Link1]], [[First-Order-Dependent-Type-Theory|Link2]]
- **3.5 Fibrations for equational logic** — **Eq-fibration** (fibred preorder + fibred/base finite products + equality with Frobenius); validity of a conditional equation in an Eq-fibration; examples showing different fibrations over the *same* base category (Dcpo, REL) encode different notions of equality between continuous functions / relations; soundness and completeness for equational logic w.r.t. Eq-fibrations. : [[Equational-Logic|Link]]
- **3.6 Fibred functorial semantics** — morphism of Eq-fibrations (preserves base/fibred products and equality); model of an equational specification as a morphism of Eq-fibrations into $p$; signature-with-axioms $(\mathrm{Sign}(\mathbb B),\mathcal H(p))$ associated to an Eq-fibration; bijective correspondence between models and morphisms of specifications; quotient Eq-fibration $p/\mathrm{Eq}$ forcing internal = external equality, universal among such quotients. : [[Equational-Logic|Link]]

**Key Questions:**
1. Why does presenting equality as a left adjoint to a contraction functor (Lawvere's approach) unify reflexivity, symmetry, transitivity and replacement into a single rule, and what role does the Beck–Chevalley condition play in making substitution "commute" with equality?
2. In what sense can the *same* base category (e.g. Dcpo or REL) carry genuinely different logics of equality, and what does this reveal about the necessity of the fibred (as opposed to purely categorical) approach to logic?
3. Why is the correspondence between algebraic specifications and categories with finite products (Theorem 3.3.8) only an equivalence for *non-conditional* equations, and what extra structure (from Chapter 4) is needed to capture arbitrary predicates?

---

### Chapter 4: First Order Predicate Logic (pp. 219–310)

**Summary:** This chapter extends equational logic to full (many-typed) first order predicate logic over STT, modeling connectives and quantifiers as fibred categorical structure (products/coproducts/exponents in fibres, and left/right adjoints to weakening functors for $\exists$/$\forall$), then specializes to subobject fibrations and to the fundamental adjoint constructions of subset types and quotient types. : [[First-Order-Predicate-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Signatures, connectives and quantifiers** — signature with predicates $(\Sigma,\Pi)$; atomic/regular/coherent/full first order propositions and logics ($\{=,\wedge,\top,\exists\}$, $\{=,\wedge,\top,\vee,\bot,\exists\}$, full with $\supset,\forall$); natural deduction rules (Fig. 4.1); reductio ad absurdum / excluded middle for classical logic; **mate reformulations**: equality as Lawvere adjunction, $\exists$ as left adjoint and $\forall$ as right adjoint to weakening ($\pi^*$); the "empty type" subtlety invalidating unrestricted strengthening.
- **4.2 Fibrations for first order predicate logic** — **regular fibration** (Eq-fibration + simple coproducts $\coprod$ with Frobenius, models $\exists$), **coherent fibration** (regular + fibrewise-distributive fibred coproducts $\bot,\vee$), **first order fibration** (coherent + fibred CCC + simple products $\prod$, models $\forall,\supset$); syntactic classifying-fibration examples; set-theoretic, Kripke-model, order-theoretic (frame/locale), realisability ($\mathrm{UFam}(\mathcal{PN})$, Kleene), recursive-enumerability, and cylindric-algebra models of these logics. : [[First-Order-Predicate-Logic|Link]]
- **4.3 Functorial interpretation and internal language** — validity of a sequent/predicate in a model; morphisms of regular/coherent/first order fibrations; model of a specification as a morphism of fibrations; soundness/completeness; **internal language/logic** of a fibration $p$ built from $(\mathrm{Sign}(\mathbb B),\Pi(p),\mathcal A(p))$, letting one reason in $p$ using ordinary logical notation; every $u^*$ has a left (and, in first order fibrations, right) adjoint; category $\mathrm{Rel}(p)$/$\mathrm{FRel}(p)$ of (functional) relations built from the internal language; internally injective/surjective morphisms.
- **4.4 Subobject fibrations I: regular categories** — images and stable images; **regular category** (finite limits + stable images); Theorem: $\mathbb B$ regular $\iff$ $\mathrm{Sub}(\mathbb B)$ has coproducts with Frobenius $\iff$ $\mathrm{Sub}(\mathbb B)$ is a regular fibration; **cover** (extremal epi / regular epi, several equivalent characterizations); (Monos, Covers) factorisation system; internal injectivity = mono, internal surjectivity = cover, in subobject fibrations. : [[Standard-Fibrations-Used-Throughout-the-Book|Link]]
- **4.5 Subobject fibrations II: coherent categories and logoses** — **coherent category** (regular + stable binary joins + strict initial object); **logos** (coherent category where each $u^*:\mathrm{Sub}(J)\to\mathrm{Sub}(I)$ has a right adjoint) $\iff$ subobject fibration is first order; $\mathbf{Sets}$, $\mathbf{PER}$, and $\mathrm{Fam}(A)$ for a frame $A$ are logoses; regular subobjects in $\mathbf{PER}$ correspond to saturated subsets of the underlying quotient and yield classical logic. : [[Regular-and-Coherent-Categories|Link1]], [[Standard-Fibrations-Used-Throughout-the-Book|Link2]]
- **4.6 Subset types** — formation/introduction/elimination rules for $\{x{:}\sigma \mid \varphi\}$ with in/out term operators $\iota,o$; **full subset types**; categorical account: fibration **has subsets** if the terminal-object functor $T:\mathbb B\to\mathbb E$ has a right adjoint $\{-\}$ ("$D$-category"/comprehension with unit); every subobject fibration has full subset types. : [[Dependent-Predicate-Logic|Link1]], [[Subset-Types-and-Quotient-Types|Link2]]
- **4.7 Quotient types** — formation/introduction/elimination rules for $\sigma/R$ with canonical map $[-]_R$ and `pick x from a in N(x)`; $(\beta)/(\eta)$-conversions; **effective (full) quotients**; extensionality of function-type equality follows from quotients (Lemma 4.7.1); worked example: constructing $\mathbb Z$ as $(\mathbb N\times\mathbb N)/\!\sim$ as the free abelian group on a commutative monoid. : [[Dependent-Predicate-Logic|Link1]], [[Subset-Types-and-Quotient-Types|Link2]]
- **4.8 Quotient types, categorically** — relation $\mathrm{Rel}(\mathbb E)$ as a fibration over $\mathbb B^\to$; kernel relation $\mathrm{Ker}(u)$; fibration **has quotients** if $\mathrm{Eq}:\mathbb B\to\mathrm{Rel}(\mathbb E)$ has a left adjoint $R\mapsto I/R$; duality between subset types (right adjoint to truth) and quotient types (left adjoint to equality) — subset types are equivalently a *right* adjoint to $\mathrm{Eq}$; **quotients satisfy Frobenius**; **effective/full quotients** (unit map is Cartesian); subobject fibration of a category with coequalisers has quotients, effective iff every equivalence relation is a kernel pair (i.e. category is *exact*). : [[Dependent-Predicate-Logic|Link]]
- **4.9 A logical characterisation of subobject fibrations** — single-valued relation; **unique choice** ($\exists!$); subobject fibrations always have unique choice (Prop. 4.9.2); very strong equality characterised via the canonical map $I \to \{\mathrm{Eq}(I)\}$; **Main theorem**: an Eq-fibration is (equivalent to) a subobject fibration on its base iff it has very strong equality, full subset types, and unique choice; a similar characterisation for *regular* subobject fibrations (every predicate is an equation). : [[Subset-Types-and-Quotient-Types|Link]]

**Key Questions:**
1. Why must existential and universal quantification be defined as adjoints to *weakening* functors rather than to reindexing along arbitrary morphisms, and what extra hypothesis (Beck–Chevalley) is needed to extend this to arbitrary morphisms?
2. What is lost/gained by treating subset types and quotient types as two instances of the same "adjoint to a distinguished functor" pattern (right adjoint to truth vs. left adjoint to equality), and why does Theorem 4.8.3 show they are secretly dual constructions on the *same* functor $\mathrm{Eq}$?
3. What exactly do "very strong equality," "full subset types," and "unique choice" jointly capture that makes Theorem 4.9.4 a *characterisation* (not just a sufficient condition) of subobject fibrations, and why does dropping the "full" or "unique choice" clauses fail to force this?

---

### Chapter 5: Higher Order Predicate Logic (pp. 311–372)

**Summary:** This chapter adds a distinguished type $\mathrm{Prop}$ of propositions to enable quantification over predicates, develops the categorical counterpart (generic objects) needed to make $\mathrm{Prop}$ meaningful in arbitrary fibrations, defines toposes both logically (via higher order subobject fibrations) and elementarily (finite limits + exponents + subobject classifier), and studies nuclei, separated objects and sheaves as the internal machinery behind the effective topos of the next chapter. : [[Higher-Order-Predicate-Logic|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Higher order signatures** — higher order signature with distinguished type $\mathrm{Prop}$; power type $P\sigma = \sigma \to \mathrm{Prop}$ with membership $\in_\sigma$ and inclusion $\subseteq_\sigma$; **extensionality of entailment** rule (equates logical equivalence with propositional equality on $\mathrm{Prop}$); Leibniz equality $M =_\sigma N \equiv \forall P{:}\sigma\to\mathrm{Prop}.\, PM \supset PN$ definable from $\forall,\supset$ alone; quotients become *automatically effective* under extensional entailment; least equivalence relation generated by an arbitrary relation, definable in higher order logic. : [[Dependent-Predicate-Logic|Link1]], [[Higher-Order-Predicate-Logic|Link2]], [[Full-Higher-Order-Dependent-Type-Theory|Link3]], [[Nuclei-Separated-Objects-and-Sheaves|Link4]]
- **5.2 Generic objects** — **split generic object** $\Omega$ (natural bijection $\mathbb B(I,\Omega)\cong \mathrm{Obj}\,\mathbb E_I$), reformulated via a distinguished object $T$ with $\forall X\,\exists! u.\, u^*(T)=X$; fibred Yoneda lemma (fibre $\mathbb E_I \simeq \mathrm{Hom}(\mathrm{dom}_I,p)$); **representable fibration**; weak / (ordinary) / strong generic object for non-split fibrations, matched to representability of the fibration of Cartesian (or all) objects. : [[Full-Higher-Order-Dependent-Type-Theory|Link1]], [[Higher-Order-Predicate-Logic|Link2]], [[Toposes|Link3]]
- **5.3 Fibrations for higher order logic** — **higher order fibration** (first order fibration + generic object + Cartesian closed base); **tripos** (higher order fibration over $\mathbf{Sets}$ with Beck–Chevalley for induced $\prod_u,\coprod_u$); triposes from partial combinatory algebras (PCAs), generalizing Kleene realisability; **topos** = category whose subobject fibration is a (split) higher order fibration; regular subobjects in $\omega$-Sets form a higher order fibration (classical logic), but regular subobjects in $\mathbf{PER}$ do not (cardinality obstruction, due to Streicher). : [[Higher-Order-Predicate-Logic|Link1]], [[Nuclei-Separated-Objects-and-Sheaves|Link2]], [[Toposes|Link3]]
- **5.4 Elementary toposes** — **(elementary) topos**: finite limits + exponents + subobject classifier $\mathrm{true}:1\rightarrowtail\Omega$; **logical morphism**; presheaf categories $\mathbf{Sets}^{C^{op}}$ as toposes (subobject classifier = sieves); powerobject $PI=\Omega^I$, membership $\in_I$, singleton map $\{-\}:I\to PI$; lift object $\bot I$ and the classification of *partial maps*; every topos is locally Cartesian closed (LCCC); equivalence of the "elementary" and "logical" definitions of topos. : [[Toposes|Link]]
- **5.5 Colimits, powerobjects and well-poweredness in a topos** — Kock's characterisation: $\mathbb B$ is a topos iff finite limits + powerobjects (with universal membership relation) exist; powerobject assignment is functorial (a monad); every topos has finite colimits (via disjointness of $\{-\}_I,0_I$ and via effective quotients), preserved by pullback and logical morphisms; epis in a topos = covers = regular epis; **well-powered fibration** (fibred representability of vertical-subobject functors); $\mathbb B$ is a topos iff its codomain fibration is well-powered. : [[Toposes|Link]]
- **5.6 Nuclei in a topos** — **nucleus / Lawvere–Tierney topology** $j:\Omega\to\Omega$ (preserves true, idempotent, commutes with $\wedge$); double-negation nucleus $\neg\neg$; correspondence between nuclei on a presheaf topos and Grothendieck topologies (sites, covers, sup topology, regular epi topology); **closed** / **dense** subobjects w.r.t. $j$; $j$-closed subobjects form a split higher order fibration with extensional entailment and generic object $\mathrm{true}:1\rightarrowtail\Omega_j$; almost monic / almost epic / bidense maps; for $j=\neg\neg$ the logic of closed subobjects is classical. : [[The-Effective-Topos|Link1]], [[Nuclei-Separated-Objects-and-Sheaves|Link2]]
- **5.7 Separated objects and sheaves in a topos** — dense partial map, extension; **separated object** (at most one extension of dense partial maps), **sheaf** (exactly one); $\mathrm{Sep}_j(\mathbb B)$, $\mathrm{Sh}_j(\mathbb B)$; separated object $\iff$ diagonal is closed (very strong equality in closed-subobject logic); $j$-singleton map and its use to construct **separated reflection** $s(-)$ and **sheafification** $a(-)$ as left adjoints to the inclusions; sheafification preserves finite limits; geometric morphism (adjoint pair with finite-limit-preserving inverse image) as a second, more important notion of morphism between toposes than "logical morphism"; $\mathrm{Sh}_j(\mathbb B)$ is again a topos (with classical logic when $j=\neg\neg$). : [[Nuclei-Separated-Objects-and-Sheaves|Link]]
- **5.8 A logical description of separated objects and sheaves** — functional relation in the internal language of closed subobjects, related to dense partial maps; **Main theorem**: $J$ is separated iff equality on $J$ is very strong (in the closed-subobject fibration), and $J$ is a sheaf iff unique choice holds on $J$ — giving a purely logical re-derivation (via Section 4.9's characterisation) of why $\mathrm{Sh}_j(\mathbb B)$ is a topos. : [[Nuclei-Separated-Objects-and-Sheaves|Link]]

**Key Questions:**
1. Why does making $\mathrm{Prop}$ an ordinary type (rather than an external syntactic category) force the introduction of "generic objects," and why is the split case (Definition 5.2.1) too simple to cover fibrations that arise in practice (necessitating the fibred Yoneda lemma)?
2. In what precise sense is a topos "the same thing" whether defined logically (higher order subobject fibration), elementarily (finite limits + exponents + $\Omega$), or via powerobjects (Kock's theorem) — and why does the equivalence of these definitions matter for later constructing the effective topos?
3. How does the passage from a topos $\mathbb B$ to its sheaves $\mathrm{Sh}_j(\mathbb B)$ via a nucleus $j$ "force" bidense maps to become isomorphisms, and why does the double-negation nucleus specifically restore classical logic in the resulting sheaf/separated-object subcategories?

---

### Chapter 6: The effective topos (pp. 373–406)

**Summary:** This chapter constructs and analyzes Hyland's effective topos $\mathrm{Eff}$, obtained by a general "Set$(p)$" tripos-to-topos construction applied to the realisability fibration, and shows how $\mathrm{Sets}$, $\omega$-Sets, and $\mathrm{PER}$ embed into it as (respectively) sheaves, separated objects, and modest sets for the double-negation topology. : [[The-Effective-Topos|Link]]

**Key Definitions & Concepts by Section:**
- **6.1 Constructing a topos from a higher order fibration** — Set($p$) construction: objects are pairs $(I, \approx_I)$ of a base object with an abstract (symmetric, transitive, not-necessarily-reflexive) equality predicate; morphisms are equivalence classes of extensional, strict, single-valued, total relations; strict predicate (a predicate compatible with $\approx$, used to characterize subobjects of Set($p$)); Set($p$) is shown to be a topos when $p$ is a higher order fibration (Prop 6.1.3, Cor 6.1.7); $\Omega$-set and effective topos $\mathrm{Eff}$ arise as instances of Set($-$) applied to a family fibration / the realisability fibration $\mathrm{UFam(PN)}$. : [[Nuclei-Separated-Objects-and-Sheaves|Link]]
- **6.2 The effective topos and its subcategories of sets, ω-sets, and PERs** — global elements (sections) functor $\Gamma: \mathrm{Eff} \to \mathrm{Sets}$; inclusion functors $\nabla: \mathrm{Sets} \hookrightarrow \mathrm{Eff}$ and $\omega\text{-Sets} \hookrightarrow \mathrm{Eff}$, both full and faithful with left adjoints; canonically separated / canonically a sheaf / modest (effective object) objects; double negation nucleus $\neg\neg$ on $\mathrm{Eff}$; Theorem 6.2.8: sheaves for $\neg\neg$ $\simeq \mathrm{Sets}$, separated objects $\simeq \omega\text{-Sets}$.
- **6.3 Families of PERs and ω-sets over the effective topos** — split fibrations $\mathrm{UFam(PER)}/\mathrm{Eff}$ and $\mathrm{UFam}(\omega\text{-Sets})/\mathrm{Eff}$ indexing PERs/$\omega$-sets by global sections of objects of $\mathrm{Eff}$; change-of-base relating indexing over $\mathrm{Eff}$ to indexing over $\omega$-Sets via the separated reflection functor $s$; separated families $\mathrm{FSep(Eff)}$. : [[The-Effective-Topos|Link]]
- **6.4 Natural numbers in the effective topos and some associated principles** — natural numbers object $N=(\mathbb{N},E)$ in $\mathrm{Eff}$ as a modest set; Theorem: morphisms $N \to N$ in $\mathrm{Eff}$ correspond exactly to total recursive functions ("$\mathrm{Eff}$ is the world of recursive mathematics"); Church's Thesis (internally provable in $\mathrm{Eff}$); Markov's Principle; Uniformity Principle; description of PERs (modest sets) as separated "subquotients" of $N$.

**Key Questions:**
1. In what precise sense does the effective topos combine "the ordinary set-theoretic world" with "the recursion-theoretic world," and how does the identification of $N \to N$ morphisms with total recursive functions make this precise?
2. Why is the double-negation nucleus, rather than some other topology, exactly the one that recovers $\mathrm{Sets}$ as sheaves and $\omega$-Sets as separated objects inside $\mathrm{Eff}$?
3. What role does the "strict predicate" concept play in bridging the internal logic of a higher order fibration and subobjects of the associated topos $\mathrm{Set}(p)$?

---

### Chapter 7: Internal category theory (pp. 407–440)

**Summary:** This chapter develops internal categories (categories defined diagrammatically inside an ambient category with finite limits) and shows that each internal category induces, by "externalisation," a split fibration over its ambient category; a fibration arising this way is called small, giving a third (internal) formalism for indexing alongside fibred and indexed categories. : [[Internal-Category-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **7.1 Definition and examples of internal categories** — internal category $\mathbf{C} = (C_1 \rightrightarrows C_0)$ in a base $\mathbb{B}$ with finite limits, given by domain/codomain/identity/composition morphisms satisfying the usual diagrams, expressible in the internal language of $\mathrm{Sub}(\mathbb{B})$; discrete internal category; small category as internal category in $\mathrm{Sets}$; the internal category $\mathrm{PER}$ in $\omega$-Sets and in $\mathrm{Eff}$; kernel-pair construction yielding an internal groupoid from a map $a: A \to B$; the "full" internal category $\mathrm{Full}_{\mathbb{B}}(a)$ associated to a morphism $a$ in a locally Cartesian closed category. : [[Subset-Types-and-Quotient-Types|Link1]], [[Internal-Category-Theory|Link2]]
- **7.2 Internal functors and natural transformations** — internal functor $F: \mathbf{C} \to \mathbf{D}$; internal natural transformation; category $\mathrm{cat}(\mathbb{B})$ of internal categories and functors, which is finitely complete (and Cartesian closed if $\mathbb{B}$ is); internal adjunction, internal terminal object/products/equalisers/exponents, defined via internal right adjoints to canonical functors like the diagonal $\Delta: \mathbf{C} \to \mathbf{C} \times \mathbf{C}$. : [[Internal-Category-Theory|Link]]
- **7.3 Externalisation** — externalisation $\mathrm{Fam}(\mathbf{C})/\mathbb{B}$ of an internal category $\mathbf{C}$, a split fibration with split generic object $C_0$; small fibration := equivalent to an externalisation; full internal category (one whose externalisation embeds fully and faithfully into $\mathbb{B}^\to$); Prop 7.3.6: full internal categories in a locally Cartesian closed category are exactly the $\mathrm{Full}(a)$'s; externalisation is a locally full-and-faithful 2-functor $\mathrm{cat}(\mathbb{B}) \to \mathrm{Fib}_{\mathrm{split}}(\mathbb{B})$ preserving finite products and exponents; Corollaries: $\mathbf{C}$ internally Cartesian closed / has internal simple (co)products iff its externalisation is a split CCC fibration / has split simple (co)products; internalisation (Prop 7.3.12) of a fibrewise-small split fibration as an internal category in a presheaf topos. : [[Full-Higher-Order-Dependent-Type-Theory|Link1]], [[Realizability-Models-Omega-Sets-and-PERs|Link2]]
- **7.4 Internal diagrams and completeness** — internal diagram of type $\mathbf{C}$ in a fibration $p$ (an object with a compatible "action" morphism), generalizing functors out of a small category; several equivalent formulations (as fibred functors out of $\mathrm{Fam}(\mathbf{C})$, as algebras of a coproduct-induced monad); $I$-parametrised internal diagrams and the fibred category $E^{\mathbf{C}}$ of internal diagrams; simple limits of type $\mathbf{C}$ (fibred right adjoint to the diagonal $E \to E^{\mathbf{C}}$); Theorem 7.4.9/7.4.10: a fibration with products $\Pi_u$ and fibred equalisers has all small limits, and (for small fibrations) this is equivalent to completeness — notably, small *and* complete fibred categories exist (e.g. $\mathrm{PER}$ in $\omega$-Sets), unlike the classical (Freyd) result that no ordinary category is both small and complete. : [[Internal-Category-Theory|Link]]

**Key Questions:**
1. How does "externalisation" make precise the sense in which internal category theory and fibred category theory are two views of the same indexing phenomenon, and what is lost or gained by preferring the external/fibred description?
2. Why can a fibred category be both small and complete when Freyd's theorem forbids this for ordinary categories — what exactly does "complete" mean at the fibred level that escapes the diagonal argument?
3. In what sense is an internal diagram a generalization of a presheaf/functor out of a small category, and why does the definition require an explicit action morphism rather than just an object?

---

### Chapter 8: Polymorphic type theory (pp. 441–508)

**Summary:** This chapter introduces polymorphic (second- and higher-order) type theory — first order $\lambda^{\to}$, second order $\lambda 2$, and higher order $\lambda\omega$ — built on type variables and polymorphic products/sums, shows Reynolds' negative result that impredicative polymorphic products have no naive set-theoretic model, and develops the fibred ($\lambda^\to$-, $\lambda2$-, $\lambda\omega$-fibration) semantics needed instead, with PER-indexed models over $\mathrm{Sets}$, $\omega$-Sets, and $\mathrm{Eff}$, plus a relationally parametric PER model and a sketch of "logic over polymorphic type theory." : [[Polymorphic-Dependent-Type-Theory|Link1]], [[Polymorphic-Type-Theory|Link2]]

**Key Definitions & Concepts by Section:**
- **8.1 Syntax** — type variables and kind contexts $\Xi$ vs. type contexts $\Gamma$; the three calculi $\lambda^\to$ (first order, only substitution into $\alpha \to \alpha$-style types), $\lambda2$ (with impredicative $\Pi\alpha{:}\mathrm{Type}.\sigma$ and $\Sigma\alpha{:}\mathrm{Type}.\sigma$, binding type variables), $\lambda\omega$ (many-kinded, kinds closed under $\times, \to$); polymorphic signature (a higher order signature of kinds plus, for each kind sequence, a signature of types); equality types $\mathrm{Eq}_A(\sigma,\tau)$ with symmetry/transitivity/replacement combinators derivable; propositions-as-types correspondence between higher order predicate logic and $\lambda\omega$ (propositions as types, types as kinds).
- **8.2 Use of polymorphic type theory** — ML-style ("let") polymorphism via type schemes $\Pi\alpha{:}\mathrm{Type}.\sigma$ restricted to the outside, contrasted with explicit $\lambda2$ typing; Hagino signatures and the encoding of inductive/co-inductive data types (Church numerals, streams) in $\lambda2$ via weakly initial algebras / weakly terminal co-algebras (Theorem 8.2.2); encapsulation of abstract types and object classes via sum types $\Sigma$. : [[Polymorphic-Type-Theory|Link]]
- **8.3 Naive set theoretic semantics** — naive set-theoretic model of a polymorphic signature via a set of sets $\mathcal{U}$; Freyd's Fact 8.3.2 (no small complete category but preorders); Fact 8.3.3 (Reynolds): no non-trivial set of sets closed under exponents and self-indexed dependent products; Proposition 8.3.4: no injection $P\sigma \hookrightarrow \sigma$ in higher order logic; Fact 8.3.5 generalizes the impossibility to any model of higher order logic with an object embedding $\mathrm{Prop}$ — explaining why $\mathrm{PER}$ models over $\omega$-Sets/$\mathrm{Eff}$ escape it (no mono $\mathrm{Prop} \hookrightarrow R$ for PER $R$). : [[Polymorphic-Type-Theory|Link]]
- **8.4 Fibrations for polymorphic type theory** — polymorphic fibration (fibration with generic object, fibred finite products, base finite products); $\lambda^\to$-/$\lambda2$-/$\lambda\omega$-fibration (adding fibred exponents; simple $\Omega$-products/coproducts; base exponents, respectively), each extendable with equality; PER-examples: $\mathrm{UFam(PER)}$ over $\mathrm{Sets}$, $\omega$-Sets, $\mathrm{Eff}$ as $\lambda\omega^=$-fibrations (uniform/tracked realizers), related by change-of-base; relationally parametric PER model $\mathrm{PFam(PER)}/\mathrm{PPER}$ (Def 8.4.8–8.4.9) satisfying "identity extension" and "abstraction" conditions, giving a $\lambda2$-fibration that is parametric in Reynolds' sense (Prop 8.4.10). : [[Polymorphic-Type-Theory|Link1]], [[Polymorphic-Dependent-Type-Theory|Link2]]
- **8.5 Small polymorphic fibrations** — internalisation of a (fibrewise small, split) polymorphic fibration as an internal category in a presheaf topos (Theorem 8.5.1); simple fibration $\mathrm{Sp}(E)$ on a fibration $p$ with fibred products, generalizing the ordinary "simple fibration" construction; Pitts' construction (Theorem 8.5.5/8.5.7) turning a $\lambda^\to$- or $\lambda2$-fibration into a small one via a full internal category, shown to coincide with an application of the standard (presheaf) internalisation to the simple fibration. : [[Polymorphic-Type-Theory|Link]]
- **8.6 Logic over polymorphic type theory** — polymorphic predicate logic (PPL): a "logic of kinds" (fibration on the base $\mathbb{B}$, reasoning about kinds/types, e.g. subtyping) versus a "logic of types" (fibration on the total category $E$, reasoning about type-inhabitants, with quantification $\exists x{:}\sigma.\varphi$/$\forall x{:}\sigma.\varphi$ over types and $\exists\beta{:}B.\varphi$/$\forall\beta{:}B.\varphi$ over kinds, the latter via "lifted simple" (co)products); relationally parametric $\lambda2$-fibration defined via a reflexive graph of $\lambda2$-fibrations (Def 8.6.2), instantiated concretely for $\mathrm{PFam(PER)}$ via a fibration of regular relations $\mathrm{RFam(PER)}/\mathrm{RPER}$ (Prop 8.6.3). : [[Polymorphic-Type-Theory|Link]]

**Key Questions:**
1. Exactly what feature of impredicative polymorphic products ($\Pi\alpha{:}\mathrm{Type}.\sigma(\alpha)$ ranging over all types including itself) drives Reynolds' negative result, and why do PER models over $\omega$-Sets or $\mathrm{Eff}$ escape it while naive $\mathrm{Sets}$-models cannot?
2. What is the difference between a PER model that is merely "parametric in the sense of Strachey" (uniform tracking by a single code) and one that is "relationally parametric in the sense of Reynolds," and why does the latter require an explicit logic of relations rather than following automatically from uniform realizability?
3. Why does encoding inductive/co-inductive types in $\lambda2$ only yield *weakly* initial algebras / *weakly* terminal co-algebras, and what extra ingredient (e.g. parametricity) is needed to upgrade weak to strict (co)initiality?

---

### Chapter 9: Advanced fibred category theory (pp. 509–580)

**Summary:** This chapter collects miscellaneous, more advanced topics in fibred category theory studied independently of any particular logic or type theory, most of which (especially the general notion of quantification in Section 9.3) will resurface as the technical backbone of the dependent type theory chapters that follow. : [[Fibred-Category-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **9.1 Opfibrations and fibred spans** — opfibration (a functor $p:\mathbb{E}\to\mathbb{B}$ that is a fibration when viewed as $p:\mathbb{E}^{op}\to\mathbb{B}^{op}$, i.e. has opcartesian liftings), opcartesian morphism, bifibration (a functor that is both a fibration and an opfibration), opreindexing/extension functor $u_!$ (left adjoint to substitution $u^*$), fibred span (a diagram $p$-fibred and $q$-opfibred with compatibility conditions between Cartesian and opcartesian maps), generalised Grothendieck construction relating split fibred spans to functors $\mathbb{A}^{op}\times\mathbb{B}\to\mathbf{Cat}$. : [[Fibred-Category-Theory|Link]]
- **9.2 Logical predicates and relations** — construction of finite products/coproducts/exponents in a total category $\mathbb{E}$ from fibrewise ($\top,\wedge,\bot,\vee,\supset$) structure and vice versa (Propositions 9.2.1–9.2.4), "logical predicates"/"logical relations" as the total-category BiCCC structure of a coherent predicate logic, inductive initial algebra (an initial algebra $a:T(K)\to K$ whose lifted image $\mathrm{Pred}(T)(TK)\to TK$ is again initial, giving an induction principle), the result that comprehension automatically makes every initial algebra inductive. : [[First-Order-Predicate-Logic|Link1]], [[Fibred-Category-Theory|Link2]], [[Realizability-Models-Omega-Sets-and-PERs|Link3]], [[Full-Higher-Order-Dependent-Type-Theory|Link4]]
- **9.3 Quantification** — weakening and contraction comonad $(W,\varepsilon,\delta)$ on a fibration's total category, $W$-products/coproducts/equality (right/left adjoints to weakening/contraction functors $p(\varepsilon_X)^*,p(\delta_X)^*$ satisfying Beck–Chevalley, optionally Frobenius), comprehension category (a functor $\mathcal{V}:\mathbb{E}\to\mathbb{B}^\to$ with $\mathrm{cod}\circ\mathcal{V}$ a fibration and $\mathcal{V}$ sending Cartesian maps to pullbacks) shown to correspond bijectively to weakening-and-contraction comonads (Theorem 9.3.4), quantification ($\mathcal{P}$-products/coproducts/equality) defined abstractly with respect to a comprehension category, simple/codomain/subobject comprehension categories as key examples. : [[First-Order-Predicate-Logic|Link1]], [[Regular-and-Coherent-Categories|Link2]], [[Standard-Fibrations-Used-Throughout-the-Book|Link3]]
- **9.4 Category theory over a fibration** — 2-categorical definition of "fibration" via a right-adjoint-right-inverse to an induced map on arrow/comma objects, "fibration over a fibration" in $\mathrm{Fib}(\mathbb{B})$ and in $\mathrm{Fib}$, simple and codomain fibrations lifted to fibrations-over-fibrations, examples: logic-of-types over a polymorphic fibration, deliverables category $\mathrm{Del}(\mathbb{B})$. : [[Fibred-Category-Theory|Link]]
- **9.5 Locally small fibrations** — local smallness for a fibration (representability of the vertical-homset functor $(\mathbb{B}/I)^{op}\to\mathbf{Sets}$), $\mathrm{Hom}_I(X,Y)\to I$ as the representing object, intrinsic reformulation via universal spans (Lemma 9.5.4), Full($U$) internal category construction from any object of a locally small fibration, small = locally small + generic object (Corollary 9.5.6). : [[Fibred-Category-Theory|Link]]
- **9.6 Definability** — a collection $P$ of objects of $\mathbb{E}$ closed under substitution; $P$ definable if every object has a "best approximation" in $P$ via a universal Cartesian map, equivalently a representing mono $\{X\in P\}\rightarrowtail I$; definability of isomorphisms, equality, monomorphisms, terminal objects; definable subfibration; a definable subfibration of a small fibration is again small (Corollary 9.6.11). : [[Full-Higher-Order-Dependent-Type-Theory|Link1]], [[Realizability-Models-Omega-Sets-and-PERs|Link2]]

**Key Questions:**
1. Why does the correspondence between weakening-and-contraction comonads and comprehension categories (Theorem 9.3.4) let the book replace the more intuitive comonad formulation by the more "elementary" comprehension-category formulation for the rest of the book?
2. In what precise sense does comprehension (a right adjoint to the terminal-object functor) automatically upgrade an initial algebra into an "inductive" one, and why does this matter for justifying induction as a derived — rather than assumed — principle?
3. Why is "small = locally small + has a generic object" (Corollary 9.5.6) the fibred analogue of "small = small set of objects + small set of morphisms," and how does definability interact with this decomposition to guarantee that definable subfibrations of small fibrations stay small?

---

### Chapter 10: First order dependent type theory (pp. 581–644)

**Summary:** This chapter introduces dependent type theory (DTT), in which term variables may occur inside types (as in $n:\mathbb{N} \vdash \mathrm{NatList}(n):\mathrm{Type}$), develops its syntax and term-model category of contexts, and identifies "comprehension categories" as the right abstract categorical structure — refined into "closed comprehension categories" (CCompCs) modeling unit, dependent product $\Pi$, and strong dependent sum $\Sigma$ — with several concrete (family, topos, domain-theoretic, PER) models given at the end. : [[First-Order-Dependent-Type-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **10.1 A calculus of dependent types** — dependent product $\Pi x{:}\sigma.T(x)$, dependent sum $\Sigma x{:}\sigma.T(x)$, equality/identity type $\mathrm{Eq}_\sigma(x,x')$, well-formed contexts with variable dependency constraints, weak vs. strong elimination rules for sum and equality (strong = elimination motive may depend on the sum/equality term itself), extensional DTT (strong equality with $\eta$) vs. intensional DTT, weak vs. strong coproduct types. : [[Dependent-Predicate-Logic|Link1]], [[First-Order-Dependent-Type-Theory|Link2]], [[Full-Higher-Order-Dependent-Type-Theory|Link3]], [[Polymorphic-Dependent-Type-Theory|Link4]]
- **10.2 Use of dependent types** — dependent tuple encodings (e.g. type `date` via nested $\Sigma$), propositions-as-types à la Howard (inhabitants of $\Pi,\Sigma$ as proofs, Brouwer–Heyting–Kolmogorov reading) vs. à la de Bruijn (DTT as a *logical framework*, with a type $\Omega:\mathrm{Type}$ of propositions and a lifting operator $T(-)$), encapsulation via dependent sum types (e.g. $\mathrm{Mon}(\sigma)$ of monoid structures), Geach's "donkey sentence" as an illustration of dependent quantification. : [[Dependent-Predicate-Logic|Link1]], [[First-Order-Dependent-Type-Theory|Link2]], [[Full-Higher-Order-Dependent-Type-Theory|Link3]], [[Polymorphic-Dependent-Type-Theory|Link4]]
- **10.3 A term model** — category of contexts $\mathcal{C}$ with context morphisms as simultaneous substitutions, display maps / (dependent) projections $\pi:(\Gamma,x{:}\sigma)\to\Gamma$ stable under pullback (Lemma 10.3.1), correspondence of unit type / dependent product / (weak, strong) dependent sum with terminal-object functor / fibred products $\Pi$ / fibred coproducts $\coprod$ (with strength = an iso condition) with respect to display maps (Propositions 10.3.2–10.3.3). : [[Dependent-Predicate-Logic|Link1]], [[Equational-Logic|Link2]], [[First-Order-Dependent-Type-Theory|Link3]]
- **10.4 Display maps and comprehension categories** — display map category $(\mathbb{B},\mathcal{D})$ (a pullback-closed class of maps) with (unit)/(product)/(weak sum)/(strong sum)/(weak equality)/(strong equality) conditions, relatively Cartesian closed category (RCCC), comprehension category $\mathcal{V}:\mathbb{E}\to\mathbb{B}^\to$ (repeated from 9.3.4) and its full/split variants, comprehension category *with unit* (a fibration whose terminal-object functor $1$ has a right adjoint $\{-\}$), fibrations with subset types as a special preorder case, local smallness $\Leftrightarrow$ comprehension for a fibred CCC (Corollary 10.4.11). : [[First-Order-Dependent-Type-Theory|Link]]
- **10.5 Closed comprehension categories** — admits products / admits (strong) coproducts with respect to a comprehension category itself; closed comprehension category (CCompC) = full comprehension category with unit, products, and strong coproducts, with terminal object in the base; underlying fibration of a CCompC is Cartesian closed with $X\times Y=\coprod_X(\pi_X^*Y)$, $X\Rightarrow Y=\prod_X(\pi_X^*Y)$; term-model CCompC from $\Pi,\Sigma,1$; strong equality $\Leftrightarrow$ fibred equalisers (Theorem 10.5.10); topos models via the split "$\mathcal{T}(\mathbb{B})$" presentation of a codomain fibration. : [[First-Order-Dependent-Type-Theory|Link]]
- **10.6 Domain theoretic models of type dependency** — $\mathrm{Dcpo}^{ep}$ (embedding–projection pairs), continuous functor $\phi:A\to\mathrm{Dcpo}^{ep}$, category $\mathrm{CFam}(\mathrm{Dcpo})$ of continuous families of dcpos over dcpos as a split CCompC (via Grothendieck completion $\{\phi\}$, strong coproducts, and dependent products), and the "closures indexed by closures" model $\mathrm{Fam}(\mathrm{Clos})$ over the category $\mathbf{Clos}$ built from $P\omega$, which realizes $\vdash\mathrm{Type}{:}\mathrm{Type}$ (hence is inconsistent as a foundational system, cf. Girard's paradox). : [[First-Order-Dependent-Type-Theory|Link]]

**Key Questions:**
1. Why must "concatenation of contexts" in DTT be modeled by pullbacks along display maps rather than by Cartesian products, and how does this force the shift from CT-structures (used for STT/PTT) to display-map/comprehension categories?
2. What exactly distinguishes weak, strong, and (in the next chapter) very strong dependent sums and equality types, and why does the strength of sum/equality hinge on whether the elimination motive is allowed to mention the sum/equality-typed variable itself?
3. Why does the closure model of Section 10.6 (with $\vdash\mathrm{Type}{:}\mathrm{Type}$) serve as a cautionary bridge to Chapter 11's discussion of Girard's paradox, and what property of a CCompC would have to fail to block that inconsistency?

---

### Chapter 11: Higher order dependent type theory (pp. 645–716)

**Summary:** The final chapter combines everything developed so far into three higher order dependent type theories — dependent predicate logic (DPL), polymorphic dependent type theory (PDTT), and full higher order dependent type theory (FhoDTT, essentially the Calculus of Constructions) — classified via an abstract "dependency" relation between syntactic universes, and gives their categorical semantics (DPL-, PDTT-, FhoDTT-structures) together with realizability models, culminating in a study of the (weak) completeness of PERs in the effective topos. : [[Full-Higher-Order-Dependent-Type-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **11.1 Dependent predicate logic** — DPL: predicate logic over DTT where term variables may occur in both propositions $\varphi(x){:}\mathrm{Prop}$ and types $\tau(x){:}\mathrm{Type}$, enabling dependent subset types $\{x{:}\sigma\mid\varphi(x)\}$ and dependent quotient types $\sigma/R$ with a proper (non-empty) type context, higher order axiom $\vdash\mathrm{Prop}{:}\mathrm{Type}$, term-model fibrations of types $\mathcal{T}\to\mathcal{C}^\to$ and propositions $\mathbb{P}\to\mathcal{C}$. : [[Dependent-Predicate-Logic|Link]]
- **11.2 Dependent predicate logic, categorically** — DPL-structure (a preorder fibration $q$ of propositions over a closed comprehension category $\mathcal{P}:\mathbb{E}\to\mathbb{B}^\to$ of types, with $q$ admitting $\mathcal{P}$-products/coproducts/equality and, for higher order, a generic object $\Omega$), dependent subset types (fibred right adjoint $\{-\}$ to a terminal-object-induced functor $T$), dependent quotient types (fibred left adjoint $Q$ to an equality functor $\mathrm{Eq}$), topos models automatically have full dependent subset and quotient types. : [[Dependent-Predicate-Logic|Link]]
- **11.3 Polymorphic dependent type theory** — PDTT: kinds over kinds (dependent) plus types over kinds (polymorphic) plus types over types (dependent) but not kinds over types; PDTT-structure (nested comprehension categories $\mathcal{Q}:\mathbb{D}\to\mathbb{A}^\to$ over $\mathcal{P}:\mathbb{E}\to\mathbb{B}^\to$ via a fibration $r:\mathbb{A}\to\mathbb{B}$, with polymorphic quantification defined via change-of-base/lifting of $\mathcal{P}$ along $r$), higher order axiom $\vdash\mathrm{Type}{:}\mathrm{Kind}$ captured via a generic object, "ideal model" example built from a reflexive dcpo. : [[Polymorphic-Dependent-Type-Theory|Link]]
- **11.4 Strong and very strong sum and equality** — weak/strong/very strong $(s_1,s_2)$-sums and equality classified by which dependency ($s_2\succ s_1$, $s_2\succ s_2$, $s_1\succ s_2$) the elimination motive is allowed to use; canonical map $\kappa:\{A\}\to\{\coprod_X(A)\}$ orthogonal to all projections (strong) vs. an isomorphism (very strong); theorem that strong dependent sums of types over types automatically force polymorphic sums of types over kinds to be strong (Proposition 11.4.3). : [[Equational-Logic|Link1]], [[Nuclei-Separated-Objects-and-Sheaves|Link2]], [[Subset-Types-and-Quotient-Types|Link3]]
- **11.5 Full higher order dependent type theory** — dependency relation $s_2\succ s_1$ ("$s_2$ is indexed by $s_1$") as the organizing notion classifying STT/DTT/PTT/PDTT/FhoDTT by which of $\mathrm{Type}\succ\mathrm{Kind}$, $\mathrm{Kind}\succ\mathrm{Type}$, $\mathrm{Type}\succ\mathrm{Type}$, $\mathrm{Kind}\succ\mathrm{Kind}$ hold; FhoDTT (all four dependencies, based on the Calculus of Constructions), fibred reflection $\mathcal{I}\dashv\mathcal{R}$ between types and kinds induced by unit types and (very strong) sums, Girard's paradox from very strong (Kind,Type)-sums (Exercise 11.5.3, à la Mirimanoff). : [[Full-Higher-Order-Dependent-Type-Theory|Link]]
- **11.6 Full higher order dependent type theory, categorically** — (weak) FhoDTT-structure (a closed comprehension category $\mathcal{P}:\mathbb{E}\to\mathbb{B}^\to$ of kinds together with a fibred reflection $\mathbb{D}\rightleftarrows\mathbb{E}$ of types-in-kinds and a generic object), strong FhoDTT-structure (types comprehension category also closed), degenerate topos and closure models, realizability models (PERs over $\omega$-Sets, PERs over $\mathbf{Eff}$, ExPERs over $\omega$-Sets — the last a genuinely *weak* FhoDTT-structure by Streicher's counterexample showing (Type,Type)-sums fail to be strong there), theorem that the fibration of types in a weak FhoDTT-structure is a fibred CCC and the externalisation of a full internal category (Theorem 11.6.9), and a fibred-adjoint-functor-theorem-style construction turning completeness of that internal category into the reflection (Theorem 11.6.10). : [[Full-Higher-Order-Dependent-Type-Theory|Link]]
- **11.7 Completeness of the category of PERs in the effective topos** — stacks (w.r.t. the regular-epi topology) and stack completion of a subfibration of a codomain fibration; weakly complete fibration (its stack completion is complete); orthogonality of an object to $A$ (every map $A\to X$ is constant); Freyd's theorem that an $\omega$-set is a modest set (PER) iff it is orthogonal to $V2$; main results that $\omega$-sets over $\mathbf{Eff}$ are weakly complete with stack completion = separated families, and PERs over $\mathbf{Eff}$ are weakly complete with stack completion = separated families orthogonal to $V2$. : [[Full-Higher-Order-Dependent-Type-Theory|Link1]], [[Regular-and-Coherent-Categories|Link2]]

**Key Questions:**
1. Why does the "dependency" relation $\succ$ between syntactic universes (Definition 11.5.1) provide a uniform classification of STT, DTT, PTT, PDTT, and FhoDTT, and why does adding the fourth dependency $\mathrm{Kind}\succ\mathrm{Type}$ push FhoDTT to the edge of inconsistency (Girard's paradox) unless (Kind,Type)-sums are kept merely strong rather than very strong?
2. How does the ExPERs-over-$\omega$-Sets example demonstrate that "strong coproducts are not transported along a reflector" even though the underlying fibration's coproducts are preserved as ordinary coproducts — and what does this reveal about the gap between weak and strong FhoDTT-structures?
3. In what sense is the "weak completeness" of PERs over the effective topos (via stack completion to separated-and-orthogonal families) a genuinely internal, choice-free substitute for ordinary completeness, and why does Beck–Chevalley failure for $\prod$ along arbitrary EfF-maps force this weaker notion?

---
