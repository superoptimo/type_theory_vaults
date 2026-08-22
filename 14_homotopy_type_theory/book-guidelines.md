# Homotopy Type Theory: Univalent Foundations of Mathematics — Guidelines

## Header

**Title:** Homotopy Type Theory: Univalent Foundations of Mathematics

**Author(s):** The Univalent Foundations Program (Steve Awodey, Thierry Coquand, Vladimir Voevodsky, and contributors from the IAS Special Year on Univalent Foundations 2012–13)

**Publication:** Institute for Advanced Study, 2013. First edition. Licensed under Creative Commons Attribution-ShareAlike 3.0. MSC 2010: 03-02, 55-02, 03B15.

**Brief Summary:**
This book develops homotopy type theory (HoTT), a new branch of mathematics that reveals a deep connection between homotopy theory and Martin-Löf dependent type theory. Its central thesis is that types can be interpreted as spaces (or $\infty$-groupoids), equality as paths, and that Voevodsky's univalence axiom — $(A = B) \simeq (A \simeq B)$ — together with higher inductive types provides a new foundation for mathematics with intrinsic homotopical content. The book is divided into a foundational part (Chapters 1–7) developing the core theory, and a mathematical applications part (Chapters 8–11) demonstrating the theory in homotopy theory, category theory, set theory, and real analysis.

**Intent of the Author:**
The authors aim to present a first systematic exposition of univalent foundations as a viable alternative to set theory, written in an informal mathematical style accessible without knowledge of formal logic or proof assistants. They want the reader to come away with the ability to do mathematics in this new system, understanding both its foundational principles and its capacity to unify homotopy-theoretic and type-theoretic reasoning.

---

## Topic List

1. **[[Type-Theory-as-a-Foundational-System|Type Theory as a Foundational System]]**
   - [[Type-Theory-as-a-Foundational-System|Type theory versus set theory as foundational languages]]
   - [[Type-Theory-as-a-Foundational-System|Judgmental equality versus propositional equality]]
   - [[The-Propositions-as-Types-Correspondence|Contexts and dependent types]]
   - [[Type-Theory-as-a-Foundational-System|Universes and cumulativity]]
   - [[Type-Theory-as-a-Foundational-System|Rules versus axioms in deductive systems]]

2. **[[Type-Formers-and-Their-Universal-Properties|Type Formers and Their Universal Properties]]**
   - [[Type-Formers-and-Their-Universal-Properties|Function types and $\lambda$-abstraction]]
   - [[Type-Formers-and-Their-Universal-Properties|Dependent function types ($\Pi$-types)]]
   - [[Type-Formers-and-Their-Universal-Properties|Product types and dependent pair types ($\Sigma$-types)]]
   - [[Type-Formers-and-Their-Universal-Properties|Coproduct types and the empty type]]
   - [[Type-Formers-and-Their-Universal-Properties|The unit type and the type of booleans]]
   - [[Type-Formers-and-Their-Universal-Properties|Natural numbers and primitive recursion]]
   - [[Type-Formers-and-Their-Universal-Properties|$W$-types as well-founded trees]]

3. **[[The-Propositions-as-Types-Correspondence|The Propositions as Types Correspondence]]**
   - [[The-Propositions-as-Types-Correspondence|Logical connectives as type constructors]]
   - [[The-Propositions-as-Types-Correspondence|Existential quantification as $\Sigma$-types]]
   - [[The-Propositions-as-Types-Correspondence|Universal quantification as $\Pi$-types]]
   - Constructive logic and proof relevance
   - [[Inductive-Definitions-and-Initial-Algebras|Truncated logic of mere propositions]]

4. **[[Identity-Types-and-Path-Structure|Identity Types and Path Structure]]**
   - [[Identity-Types-and-Path-Structure|Identity types as path spaces]]
   - [[Higher-Inductive-Types|Path induction and based path induction]]
   - [[Identity-Types-and-Path-Structure|Higher-dimensional path structure and $\infty$-groupoids]]
   - [[Homotopy-n-Types-and-Truncation-Levels|Path concatenation inversion and associativity]]
   - [[Identity-Types-and-Path-Structure|The Eckmann–Hilton argument]]

5. **[[Homotopical-Interpretation-of-Type-Theory|Homotopical Interpretation of Type Theory]]**
   - Types as spaces or higher groupoids
   - Functions as continuous maps and functors
   - [[Homotopical-Interpretation-of-Type-Theory|Type families as fibrations with transport]]
   - [[Homotopical-Interpretation-of-Type-Theory|Homotopies between functions]]
   - [[Homotopy-n-Types-and-Truncation-Levels|Loop spaces and iterated loop spaces]]

6. **[[The-Univalence-Axiom-and-Its-Consequences|The Univalence Axiom and Its Consequences]]**
   - [[Equivalences-and-Their-Characterizations|Equivalence of types and the map $\mathrm{idtoeqv}$]]
   - [[The-Univalence-Axiom-and-Its-Consequences|The univalence axiom $(A =_{\mathcal{U}} B) \simeq (A \simeq B)$]]
   - [[The-Univalence-Axiom-and-Its-Consequences|Transport along paths in the universe]]
   - [[The-Univalence-Axiom-and-Its-Consequences|Lifting equivalences across structures]]
   - [[The-Univalence-Axiom-and-Its-Consequences|Equality of structures via univalence]]

7. **[[Equivalences-and-Their-Characterizations|Equivalences and Their Characterizations]]**
   - Quasi-inverses and their insufficiency
   - [[Equivalences-and-Their-Characterizations|Half adjoint equivalences]]
   - [[Equivalences-and-Their-Characterizations|Bi-invertible maps]]
   - [[Equivalences-and-Their-Characterizations|Contractible fibers as a definition of equivalence]]
   - [[Equivalences-and-Their-Characterizations|Surjections and embeddings]]

8. **[[Inductive-Definitions-and-Initial-Algebras|Inductive Definitions and Initial Algebras]]**
   - [[Inductive-Definitions-and-Initial-Algebras|General syntax of inductive definitions]]
   - [[Identity-Types-and-Path-Structure|Strict positivity condition]]
   - [[Connectedness-and-Orthogonal-Factorization|Induction principles and recursion principles]]
   - [[Inductive-Definitions-and-Initial-Algebras|Homotopy-initial algebras and universal properties]]
   - [[Inductive-Definitions-and-Initial-Algebras|Homotopy-inductive types with propositional computation]]

9. **[[Higher-Inductive-Types|Higher Inductive Types]]**
   - [[Higher-Inductive-Types|Point constructors and path constructors]]
   - [[Connectedness-and-Orthogonal-Factorization|The circle $S^1$ and its induction principle]]
   - [[Higher-Inductive-Types|Suspensions and spheres]]
   - [[Higher-Inductive-Types|Pushouts and cell complexes]]
   - [[Homotopical-Interpretation-of-Type-Theory|Hubs and spokes construction]]
   - [[Higher-Inductive-Types|Quotients and truncations as higher inductives]]

10. **[[Homotopy-n-Types-and-Truncation-Levels|Homotopy $n$-Types and Truncation Levels]]**
    - [[The-Propositions-as-Types-Correspondence|Mere propositions as $(-1)$-types]]
    - Sets as $0$-types and contractible types as $(-2)$-types
    - [[Homotopy-n-Types-and-Truncation-Levels|Recursive definition of $n$-types]]
    - [[Higher-Inductive-Types|$n$-truncation as a higher inductive type]]
    - [[Homotopy-n-Types-and-Truncation-Levels|Hedberg's theorem and uniqueness of identity proofs]]

11. **[[Connectedness-and-Orthogonal-Factorization|Connectedness and Orthogonal Factorization]]**
    - [[Synthetic-Homotopy-Theory|$n$-connected types and functions]]
    - [[Connectedness-and-Orthogonal-Factorization|$n$-truncated maps]]
    - [[Connectedness-and-Orthogonal-Factorization|The $n$-image factorization]]
    - [[Connectedness-and-Orthogonal-Factorization|Orthogonal factorization systems]]
    - [[Connectedness-and-Orthogonal-Factorization|Modalities and reflective subuniverses]]

12. **[[Synthetic-Homotopy-Theory|Synthetic Homotopy Theory]]**
    - [[Synthetic-Homotopy-Theory|The fundamental group of the circle $\pi_1(S^1) \cong \mathbb{Z}$]]
    - [[Synthetic-Homotopy-Theory|The encode-decode method]]
    - [[Synthetic-Homotopy-Theory|Connectedness of suspensions]]
    - [[Synthetic-Homotopy-Theory|The Hopf fibration]]
    - [[Synthetic-Homotopy-Theory|The Freudenthal suspension theorem]]
    - [[Synthetic-Homotopy-Theory|The van Kampen theorem]]
    - [[Synthetic-Homotopy-Theory|Whitehead's principle for $n$-types]]

13. **[[Univalent-Category-Theory|Univalent Category Theory]]**
    - Precategories and categories
    - Equality of objects as isomorphism
    - [[Univalent-Category-Theory|Functors and natural transformations]]
    - Equivalences versus weak equivalences of categories
    - [[Sets-in-Univalent-Foundations|The Yoneda lemma in univalent foundations]]
    - [[Univalent-Category-Theory|The Rezk completion]]
    - [[Univalent-Category-Theory|The structure identity principle]]

14. **[[Sets-in-Univalent-Foundations|Sets in Univalent Foundations]]**
    - [[Sets-in-Univalent-Foundations|The category $\mathbf{Set}$ as a $\Pi W$-pretopos]]
    - [[Sets-in-Univalent-Foundations|Images and regular epimorphisms]]
    - [[Sets-in-Univalent-Foundations|Quotients and effective equivalence relations]]
    - [[Sets-in-Univalent-Foundations|Cardinal and ordinal numbers]]
    - [[Sets-in-Univalent-Foundations|The cumulative hierarchy satisfying ZFC]]

15. **[[Real-Numbers-and-Analysis|Real Numbers and Analysis]]**
    - [[Real-Numbers-and-Analysis|The field of rational numbers $\mathbb{Q}$]]
    - [[Real-Numbers-and-Analysis|Dedekind reals as cuts in $\mathbb{Q}$]]
    - [[Real-Numbers-and-Analysis|Cauchy reals as a higher inductive-inductive type]]
    - Comparison of Cauchy and Dedekind reals
    - Compactness of the interval
    - [[Real-Numbers-and-Analysis|The surreal numbers as a higher inductive-inductive type]]

16. **[[Formal-Metatheory|Formal Metatheory]]**
    - Formal syntax and typing rules
    - [[Type-Theory-as-a-Foundational-System|Judgmental equality and conversion]]
    - [[Formal-Metatheory|Normalization and canonicity]]
    - Logical consistency relative to ZFC
    - Models in Kan simplicial sets

---

## Chapter Summaries

### Introduction (pp. 1–14)

**Summary:** Presents the motivation and overview of homotopy type theory as a new foundation for mathematics combining homotopy theory and type theory, introducing the univalence axiom and higher inductive types as its two central innovations.

**Key Definitions & Concepts:**
- Homotopy type theory (types interpreted as spaces, equality as paths)
- Univalence axiom ($(A = B) \simeq (A \simeq B)$, identity is equivalent to equivalence)
- Higher inductive types (inductively defined spaces with point and path constructors)
- Informal type theory (mathematics in univalent foundations readable by humans)
- Proof relevance (propositions and proofs as first-class mathematical objects)
- Constructivity and the spectrum between classical and constructive logic

**Key Questions:**
1. How does the homotopical interpretation of identity types as path spaces differ from the set-theoretic notion of equality?
2. Why is the univalence axiom incompatible with the naive propositions-as-types form of excluded middle?
3. What role do higher inductive types play in providing direct descriptions of homotopy-theoretic constructions?

---

### Chapter 1: Type Theory (pp. 17–58)

**Summary:** Introduces the basic type theory prior to any homotopical interpretation, presenting all fundamental type formers, the propositions-as-types correspondence, and the identity type with its induction principle.

**Key Definitions & Concepts by Section:**
- **1.1 Type theory versus set theory** — Judgment ($a : A$), judgmental equality ($a \equiv b : A$), propositional equality, context, definitional equality ($:\equiv$)
- **1.2 Function types** — Function type $A \to B$, $\lambda$-abstraction ($\lambda x. \Phi$), computation rule ($(\lambda x. \Phi)(a) \equiv \Phi[a/x]$), uniqueness principle ($f \equiv \lambda x. f(x)$), currying
- **1.3 Universes and families** — Universe $\mathcal{U}_i$, cumulativity, typical ambiguity, type family ($B : A \to \mathcal{U}$), small type
- **1.4 Dependent function types ($\Pi$-types)** — $\Pi$-type $\prod_{(x:A)} B(x)$, dependent function, polymorphic function
- **1.5 Product types** — Cartesian product $A \times B$, unit type $\mathbf{1}$, pairing constructor $(a,b)$, projections $\mathrm{pr}_1, \mathrm{pr}_2$, recursor $\mathrm{rec}_{A \times B}$, induction $\mathrm{ind}_{A \times B}$
- **1.6 Dependent pair types ($\Sigma$-types)** — $\Sigma$-type $\sum_{(x:A)} B(x)$, dependent pairing, projections for $\Sigma$, type-theoretic axiom of choice
- **1.7 Coproduct types** — Coproduct $A + B$, empty type $\mathbf{0}$, injections $\mathrm{inl}, \mathrm{inr}$, case analysis, ex falso quodlibet
- **1.8 The type of booleans** — Type $\mathbf{2}$ with constructors $0_{\mathbf{2}}, 1_{\mathbf{2}}$, recursor as if-then-else
- **1.9 The natural numbers** — Type $\mathbb{N}$, constructors $0$ and $\mathrm{succ}$, primitive recursion, recursor $\mathrm{rec}_{\mathbb{N}}$, induction $\mathrm{ind}_{\mathbb{N}}$
- **1.10 Pattern matching and recursion** — Definition by pattern matching, recursive calls, structural recursion
- **1.11 Propositions as types** — Curry-Howard correspondence, $\neg A :\equiv A \to \mathbf{0}$, constructive logic, proof-relevance
- **1.12 Identity types** — Identity type $\mathrm{Id}_A(a,b)$ or $a =_A b$, reflexivity $\mathrm{refl}_a : a = a$, path induction, based path induction, indiscernibility of identicals, disequality

**Key Questions:**
1. What is the essential difference between judgmental equality $a \equiv b$ and propositional equality $a = b$?
2. How does the propositions-as-types interpretation translate logical connectives into type constructors?
3. Why can path induction not prove that all loops are reflexivity?
4. How do $\Sigma$-types generalize both products and existential quantification?

---

### Chapter 2: Homotopy Type Theory (pp. 59–106)

**Summary:** Introduces the homotopical viewpoint on type theory, showing that types behave as $\infty$-groupoids, functions as functors, and type families as fibrations, culminating in the function extensionality and univalence axioms.

**Key Definitions & Concepts by Section:**
- **2.1 Types are higher groupoids** — Symmetry ($p^{-1}$), transitivity/concatenation ($p \cdot q$), higher coherence laws, loop space $\Omega(A,a) :\equiv (a =_A a)$, Eckmann–Hilton argument, pointed type, iterated loop space $\Omega^n(A,a)$
- **2.2 Functions are functors** — Action on paths $\mathrm{ap}_f : (x =_A y) \to (f(x) =_B f(y))$, functoriality of $\mathrm{ap}$
- **2.3 Type families are fibrations** — Transport $p_* : P(x) \to P(y)$, path lifting property, dependent map $\mathrm{apd}_f$, dependent path
- **2.4 Homotopies and equivalences** — Homotopy $(f \sim g) :\equiv \prod_{x:A} (f(x) = g(x))$, quasi-inverse $\mathrm{qinv}(f)$, equivalence $(A \simeq B) :\equiv \sum_{f:A \to B} \mathrm{isequiv}(f)$
- **2.5 The higher groupoid structure of type formers** — Characterization of identity types for each type former, need for axioms for $\Pi$-types and universes
- **2.6 Cartesian product types** — $\mathrm{pair}^=$, componentwise characterization $(x =_{A \times B} y) \simeq (\mathrm{pr}_1(x) = \mathrm{pr}_1(y)) \times (\mathrm{pr}_2(x) = \mathrm{pr}_2(y))$
- **2.7 $\Sigma$-types** — Paths in $\Sigma$-types: $(w = w') \simeq \sum_{(p:\mathrm{pr}_1(w)=\mathrm{pr}_1(w'))} p_*(\mathrm{pr}_2(w)) = \mathrm{pr}_2(w')$
- **2.8 The unit type** — $(x = y) \simeq \mathbf{1}$ for $x, y : \mathbf{1}$
- **2.9 $\Pi$-types and the function extensionality axiom** — $\mathrm{happly} : (f = g) \to \prod_{x:A}(f(x) = g(x))$, Axiom 2.9.3 (function extensionality), $\mathrm{funext}$
- **2.10 Universes and the univalence axiom** — $\mathrm{idtoeqv} : (A =_{\mathcal{U}} B) \to (A \simeq B)$, univalence axiom ($\mathrm{idtoeqv}$ is an equivalence), $\mathrm{ua} : (A \simeq B) \to (A =_{\mathcal{U}} B)$
- **2.11 Identity type** — Transport in families of paths, characterization of paths in path types
- **2.12 Coproducts** — Encode-decode for coproducts, disjointness of injections
- **2.13 Natural numbers** — Encode-decode for $\mathbb{N}$, $0 \neq \mathrm{succ}(n)$, injectivity of $\mathrm{succ}$
- **2.14 Example: equality of structures** — Lifting equivalences along univalence, equality of semigroups as isomorphism
- **2.15 Universal properties** — Universal property of products, $\Sigma$-types, type-theoretic axiom of choice as equivalence

**Key Questions:**
1. How does the transport operation $p_* : P(x) \to P(y)$ generalize the substitution of equals for equals?
2. Why is the type of quasi-inverses $\mathrm{qinv}(f)$ poorly behaved, motivating a better notion of equivalence?
3. What does the univalence axiom imply about the relationship between equality and equivalence of types?
4. How does the Eckmann–Hilton argument show that $\Omega^2(A)$ is commutative?

---

### Chapter 3: Sets and Logic (pp. 107–128)

**Summary:** Develops the logical structure of homotopy type theory, defining sets, mere propositions, and contractible types as the lower rungs of the $n$-type hierarchy, and showing how classical logic can be consistently added.

**Key Definitions & Concepts by Section:**
- **3.1 Sets and $n$-types** — Set ($\mathrm{isSet}(A) :\equiv \prod_{x,y:A} \prod_{p,q:x=y} (p = q)$), $1$-type, hierarchy of $n$-types
- **3.2 Propositions as types?** — Incompatibility of $\mathrm{LEM}_\infty$ with univalence, no Hilbert-style choice operator
- **3.3 Mere propositions** — Mere proposition ($\mathrm{isProp}(P) :\equiv \prod_{x,y:P} (x = y)$), logical equivalence implies equivalence for mere propositions
- **3.4 Classical vs. intuitionistic logic** — $\mathrm{LEM} :\equiv \prod_{A:\mathcal{U}} (\mathrm{isProp}(A) \to (A + \neg A))$, decidable type, decidable equality
- **3.5 Subsets and propositional resizing** — Subset $\{x : A \mid P(x)\}$, subtype, propositional resizing axiom
- **3.6 The logic of mere propositions** — Preservation of mere propositions by type formers
- **3.7 Propositional truncation** — $\|A\|$, constructors $|a| : \|A\|$ and $x = y$ for $x,y:\|A\|$, recursion principle
- **3.8 The axiom of choice** — $\mathrm{AC}$: $(\prod_{x:X} \|\sum_{a:A(x)} P(x,a)\|) \to \|\sum_{g:\prod_{x:X}A(x)} \prod_{x:X} P(x,g(x))\|$
- **3.9 The principle of unique choice** — If $P(x)$ is a mere proposition and $\|P(x)\|$, then $P(x)$
- **3.10 When are propositions truncated?** — Untruncated logic as default, adverb "merely" for truncation
- **3.11 Contractibility** — Contractible type ($\mathrm{isContr}(A) :\equiv \sum_{a:A} \prod_{x:A} (a = x)$), center of contraction, $(-2)$-type

**Key Questions:**
1. Why is the untruncated form of excluded middle inconsistent with univalence?
2. What is the difference between saying a type is inhabited and saying it is merely inhabited?
3. How does propositional truncation allow a more classical form of reasoning while maintaining constructivity?
4. Why is the axiom of choice not provable in truncated logic but trivially true in untruncated propositions-as-types?

---

### Chapter 4: Equivalences (pp. 129–148)

**Summary:** Studies in detail several equivalent definitions of "equivalence" for functions between types, showing that half adjoint equivalences, bi-invertible maps, and contractible maps all satisfy the desired properties and are pairwise equivalent.

**Key Definitions & Concepts by Section:**
- **4.1 Quasi-inverses** — $\mathrm{qinv}(f) \simeq \prod_{x:A}(x = x)$ when $f$ is an equivalence, counterexample showing $\mathrm{qinv}$ is not a mere proposition
- **4.2 Half adjoint equivalences** — $\mathrm{ishae}(f)$, coherence condition $\tau : \prod_{x:A} f(\eta_x) = \epsilon_{f(x)}$, fibers of equivalences are contractible
- **4.3 Bi-invertible maps** — $\mathrm{biinv}(f) :\equiv \mathrm{linv}(f) \times \mathrm{rinv}(f)$, left inverse, right inverse
- **4.4 Contractible fibers** — $\mathrm{isContr}(f) :\equiv \prod_{y:B} \mathrm{isContr}(\mathrm{fib}_f(y))$, fiber $\mathrm{fib}_f(y) :\equiv \sum_{x:A} (f(x) = y)$
- **4.5 On the definition of equivalences** — $\mathrm{isequiv}(f) :\equiv \mathrm{ishae}(f)$ chosen as canonical definition
- **4.6 Surjections and embeddings** — Surjection ($\|\mathrm{fib}_f(b)\|$ for all $b$), embedding ($\mathrm{ap}_f$ is an equivalence), equivalence iff surjective and embedding
- **4.7 Closure properties of equivalences** — 2-out-of-3 property, retracts of equivalences, fiberwise equivalences, total space equivalence
- **4.8 The object classifier** — $(\sum_{A:\mathcal{U}} (A \to B)) \simeq (B \to \mathcal{U})$, object classifier as pullback
- **4.9 Univalence implies function extensionality** — Weak function extensionality, proof that univalence implies full function extensionality

**Key Questions:**
1. Why does $\mathrm{qinv}(f)$ fail to be a mere proposition, and how do half adjoint equivalences fix this?
2. What is the relationship between contractible fibers and the existence of a quasi-inverse?
3. How does the object classifier theorem relate type families to maps into the universe?
4. Why does univalence imply function extensionality?

---

### Chapter 5: Induction (pp. 149–178)

**Summary:** Studies inductive definitions in general, including their universal properties as homotopy-initial algebras, the general syntax with strict positivity, and generalizations such as inductive families and mutual induction.

**Key Definitions & Concepts by Section:**
- **5.1 Introduction to inductive types** — Constructors, induction principle, computation rules, free generation
- **5.2 Uniqueness of inductive types** — Isomorphic definitions yield equivalent types, transfer along univalence
- **5.3 $W$-types** — $W_{(a:A)} B(a)$, constructor $\mathrm{sup}$, well-founded trees, labels and arities
- **5.4 Inductive types are initial algebras** — $\mathbb{N}$-algebra, $\mathbb{N}$-homomorphism, homotopy-initial (h-initial) algebra, polynomial functor
- **5.5 Homotopy-inductive types** — Propositional computation rules, equivalence of characterizations $\mathrm{Wd} \simeq \mathrm{Ws} \simeq \mathrm{Wh}$
- **5.6 The general syntax of inductive definitions** — Strict positivity, covariance, ban on negative occurrences, finite list of constructors
- **5.7 Generalizations of inductive types** — Inductive families (vectors), mutual induction, inductive-inductive definitions, inductive-recursive definitions
- **5.8 Identity types and identity systems** — Identity types as inductive families, identity system, pointed predicate, equivalence induction, homotopy induction

**Key Questions:**
1. Why is strict positivity necessary for the consistency of inductive definitions?
2. How does the notion of homotopy-initial algebra capture the universal property of inductive types?
3. What is the relationship between path induction and the freeness of the identity type family?
4. How do inductive-inductive definitions generalize mutual induction?

---

### Chapter 6: Higher Inductive Types (pp. 179–220)

**Summary:** Introduces higher inductive types, which generalize inductive types by allowing constructors that generate not only points but also paths and higher paths, providing direct logical descriptions of spaces like spheres, pushouts, quotients, and truncations.

**Key Definitions & Concepts by Section:**
- **6.1 Introduction** — Point constructors, path constructors, free generation of $\infty$-groupoids, dimension of constructors
- **6.2 Induction principles and dependent paths** — Dependent path $(u =^P_p v) :\equiv (\mathrm{transport}^P(p,u) = v)$, induction principle for $S^1$, propositional computation rules for path constructors
- **6.3 The interval** — Interval type $I$ with $0_I, 1_I : I$ and $\mathrm{seg} : 0_I =_I 1_I$, contractibility of $I$, proof of function extensionality
- **6.4 Circles and spheres** — $S^1$ generated by $\mathrm{base}$ and $\mathrm{loop}$, $S^2$ generated by $\mathrm{base}$ and $\mathrm{surf} : \mathrm{refl}_{\mathrm{base}} = \mathrm{refl}_{\mathrm{base}}$, nontriviality of $\mathrm{loop}$
- **6.5 Suspensions** — Suspension $\Sigma A$ with $N, S : \Sigma A$ and $\mathrm{merid} : A \to (N = S)$, $\Sigma \mathbf{2} \simeq S^1$, adjunction $\mathrm{Map}_*(\Sigma A, B) \simeq \mathrm{Map}_*(A, \Omega B)$
- **6.6 Cell complexes** — Torus $T^2$ as a higher inductive type, CW-complexes as HITs
- **6.7 Hubs and spokes** — Reducing higher path constructors to 1-dimensional path constructors via cone points
- **6.8 Pushouts** — Pushout $A \sqcup^C B$ with $\mathrm{inl}, \mathrm{inr}, \mathrm{glue}$, universal property, join, wedge, smash product
- **6.9 Truncations** — Propositional truncation as HIT, $0$-truncation, induction principle for truncations
- **6.10 Quotients** — Set-quotient $A/R$ as HIT, quotient by equivalence relation, equivalence classes, integers as quotient
- **6.11 Algebra** — Free group as HIT, free monoid as $\mathrm{List}(A)$, colimits of algebraic structures, group presentations
- **6.12 The flattening lemma** — Type families defined by recursion over HITs, total space as flattened HIT
- **6.13 The general syntax of higher inductive definitions** — Ordering of constructors, source and target expressions, naturality condition

**Key Questions:**
1. Why are computation rules for path constructors only propositional rather than judgmental?
2. How does the induction principle for $S^1$ encode the idea of a section of a fibration over the circle?
3. What is the universal property of the pushout and how does it specialize to suspensions, joins, and wedges?
4. How do higher inductive types allow construction of free algebraic structures without explicit normal forms?

---

### Chapter 7: Homotopy $n$-Types (pp. 221–255)

**Summary:** Develops the general theory of homotopy $n$-types, their closure properties, truncations, connectedness, and the orthogonal factorization system formed by $n$-connected and $n$-truncated maps, generalizing to arbitrary modalities.

**Key Definitions & Concepts by Section:**
- **7.1 Definition of $n$-types** — Recursive definition: $(-2)$-type is contractible, $(n+1)$-type has $n$-type identity types, $\mathrm{is}\text{-}n\text{-}\mathrm{type}(X)$, $n\text{-}\mathrm{Type} :\equiv \sum_{X:\mathcal{U}} \mathrm{is}\text{-}n\text{-}\mathrm{type}(X)$
- **7.2 Uniqueness of identity proofs and Hedberg's theorem** — UIP, Axiom K, Hedberg's theorem (decidable equality implies set), reflexive relation implying identity
- **7.3 Truncations** — $n$-truncation $\|A\|_n$ via hub-and-spoke construction, universal property, path spaces of truncations, functoriality, cumulation
- **7.4 Colimits of $n$-types** — Pushouts in $n$-types by truncating homotopy pushouts
- **7.5 Connectedness** — $n$-connected function ($\|\mathrm{fib}_f(b)\|_n$ contractible), $n$-connected type, induction principle for connected maps
- **7.6 Orthogonal factorization** — $n$-truncated map, $n$-image $\mathrm{im}_n(f) :\equiv \sum_{b:B} \|\mathrm{fib}_f(b)\|_n$, unique factorization, orthogonality
- **7.7 Modalities** — Reflective subuniverse, modality ($\# : \mathcal{U} \to \mathcal{U}$ with $\eta_A : A \to \#A$), $\#$-modal types, $\#$-connected and $\#$-truncated maps, left exact modalities

**Key Questions:**
1. How does the recursive definition of $n$-types starting from contractible types unify the hierarchy?
2. Why does Hedberg's theorem show that decidable equality implies all identity proofs are trivial?
3. What is the universal property of $n$-truncation and how does it make $n$-types a reflective subcategory?
4. How does the orthogonal factorization system generalize the image factorization of functions between sets?

---

### Chapter 8: Homotopy Theory (pp. 259–306)

**Summary:** Develops synthetic homotopy theory within type theory, computing homotopy groups of spheres using the encode-decode method, proving the Freudenthal suspension theorem, the van Kampen theorem, and constructing the Hopf fibration.

**Key Definitions & Concepts by Section:**
- **8.1 $\pi_1(S^1)$** — Universal cover $\mathrm{code} : S^1 \to \mathcal{U}$, encode-decode proof, homotopy-theoretic proof via contractibility of total space, $\Omega(S^1) \simeq \mathbb{Z}$, $\pi_1(S^1) = \mathbb{Z}$
- **8.2 Connectedness of suspensions** — If $A$ is $n$-connected then $\Sigma A$ is $(n+1)$-connected, $S^n$ is $(n-1)$-connected
- **8.3 $\pi_{k \leq n}$ of an $n$-connected space** — $\pi_k(S^n) = 1$ for $k < n$
- **8.4 Fiber sequences and the long exact sequence** — Fiber sequence, long exact sequence of homotopy groups, boundary maps
- **8.5 The Hopf fibration** — $H$-space, Hopf construction, $S^1 * S^1 \simeq S^3$, fibration over $S^2$ with fiber $S^1$ and total space $S^3$, $\pi_2(S^2) \cong \mathbb{Z}$, $\pi_3(S^2) \cong \mathbb{Z}$
- **8.6 The Freudenthal suspension theorem** — $\sigma : X \to \Omega\Sigma X$ is $2n$-connected if $X$ is $n$-connected, stability of homotopy groups of spheres, $\pi_n(S^n) = \mathbb{Z}$
- **8.7 The van Kampen theorem** — Fundamental groupoid $\Pi_1 X$, path codes as alternating sequences, set of basepoints, $\pi_1$ of pushouts
- **8.8 Whitehead's theorem and Whitehead's principle** — Truncated Whitehead's principle, $\infty$-connected maps, hypercomplete types
- **8.9 A general statement of the encode-decode method** — Encode-decode for loop spaces, encode-decode for truncations of loop spaces
- **8.10 Additional results** — $\pi_{n+1}(S^n) = \mathbb{Z}_k$ for $n \geq 3$, Blakers–Massey theorem, Eilenberg–Mac Lane spaces, covering spaces

**Key Questions:**
1. How does the encode-decode method characterize path spaces of higher inductive types?
2. Why is univalence essential for computing $\pi_1(S^1)$?
3. How does the Freudenthal suspension theorem imply stability of homotopy groups of spheres?
4. Why does Whitehead's theorem fail in general but hold for $n$-types?

---

### Chapter 9: Category Theory (pp. 307–340)

**Summary:** Develops 1-category theory in univalent foundations where equality of objects is identified with isomorphism, proving that fully faithful and essentially surjective functors are equivalences without the axiom of choice, and constructing the Rezk completion.

**Key Definitions & Concepts by Section:**
- **9.1 Categories and precategories** — Precategory (type of objects with set-valued homs), isomorphism $a \cong b$, $\mathrm{idtoiso} : (a = b) \to (a \cong b)$, category (precategory where $\mathrm{idtoiso}$ is an equivalence), preorder, poset, groupoid
- **9.2 Functors and transformations** — Functor, natural transformation, functor precategory $B^A$, Theorem 9.2.5 ($B^A$ is a category if $B$ is)
- **9.3 Adjunctions** — Left adjoint, unit, counit, triangle identities, uniqueness of adjoint structure
- **9.4 Equivalences** — Equivalence of categories (adjoint equivalence with isomorphism unit/counit), fully faithful, essentially surjective, weak equivalence, isomorphism of categories, $(A = B) \simeq (A \simeq B)$ for categories
- **9.5 The Yoneda lemma** — Yoneda embedding $y : A \to \mathbf{Set}^{A^{\mathrm{op}}}$, Yoneda lemma $\mathrm{hom}(ya, F) \cong Fa$, representability
- **9.6 Strict categories** — Strict category (precategory with set of objects), Galois theory example
- **9.7 $\dagger$-categories** — $\dagger$-precategory, unitary morphism, $\dagger$-category, example of $\mathbf{Hilb}$
- **9.8 The structure identity principle** — Notion of structure $(P,H)$, standard notion of structure, $\mathrm{Str}_{(P,H)}(X)$ is a category if $X$ is
- **9.9 The Rezk completion** — Weak equivalence sees categories, construction via Yoneda embedding, construction via higher inductive type, $\hat{A}_0$ with $j : (a \cong b) \to (ia = ib)$

**Key Questions:**
1. Why is the statement "every fully faithful and essentially surjective functor is an equivalence" provable without choice for categories but not for strict categories?
2. How does the univalence axiom for categories identify equality with isomorphism?
3. What is the universal property of the Rezk completion?
4. How does the structure identity principle generalize univalence to arbitrary algebraic structures?

---

### Chapter 10: Set Theory (pp. 341–372)

**Summary:** Shows that the category of sets in univalent foundations has the expected properties of a $\Pi W$-pretopos, develops cardinal and ordinal numbers using univalence and truncation, and constructs the cumulative hierarchy of ZF set theory as a higher inductive type.

**Key Definitions & Concepts by Section:**
- **10.1 The category of sets** — Limits and colimits in $\mathbf{Set}$, images and regular epimorphisms, quotients and effective equivalence relations, $\Pi W$-pretopos, elementary topos (with resizing), AC implies LEM (Diaconescu)
- **10.2 Cardinal numbers** — $\mathrm{Card} :\equiv \|\mathbf{Set}\|_0$, cardinality $|A|_0$, addition, multiplication, exponentiation, Schroeder–Bernstein, Cantor's theorem
- **10.3 Ordinal numbers** — Accessibility, well-foundedness, well-founded induction, extensional relation, simulation, ordinal (extensional well-founded transitive relation), $(\mathrm{Ord}, <)$ is an ordinal
- **10.4 Classical well-orderings** — Trichotomy under LEM, well-ordering, AC implies every set merely admits ordinal structure
- **10.5 The cumulative hierarchy** — $V$ as HIT with $\mathrm{set}(A,f)$ constructor, membership $x \in v$, bisimulation $\sim$, ZFC axioms, separation, replacement, power sets under AC

**Key Questions:**
1. How does univalence eliminate the need for canonical representatives of cardinal and ordinal numbers?
2. Why is the category $\mathbf{Set}$ a $\Pi W$-pretopos but not necessarily an elementary topos?
3. How does the higher inductive construction of the cumulative hierarchy differ from the iterative set-theoretic construction?
4. What role does Diaconescu's theorem play in relating AC to LEM?

---

### Chapter 11: Real Numbers (pp. 373–422)

**Summary:** Constructs the rational, Dedekind, and Cauchy real numbers, showing that the Cauchy reals can be defined as a higher inductive-inductive type avoiding countable choice, compares the two constructions, discusses compactness of the interval, and constructs Conway's surreal numbers.

**Key Definitions & Concepts by Section:**
- **11.1 The field of rational numbers** — $\mathbb{Q} :\equiv (\mathbb{Z} \times \mathbb{N})/\!\approx$, decidable equality and order
- **11.2 Dedekind reals** — Dedekind cut $(L,U)$, inhabited, rounded, disjoint, located, $R_d$, algebraic structure, archimedean property, Cauchy completeness, Dedekind completeness, final archimedean ordered field
- **11.3 Cauchy reals** — Cauchy approximation $x : \mathbb{Q}_+ \to R_c$, higher inductive-inductive definition of $R_c$ and $\sim_\epsilon$, $(R_c, \leq, <)$-induction, algebraic structure, Cauchy completeness, initial Cauchy complete archimedean ordered field
- **11.4 Comparison of Cauchy and Dedekind reals** — $R_c \hookrightarrow R_d$, coincidence under LEM or countable choice
- **11.5 Compactness of the interval** — Metric compactness (complete and totally bounded), Bolzano–Weierstraß implies LPO, Heine–Borel compactness via inductive covers
- **11.6 The surreal numbers** — Surreal $\{x_L \mid x_R\}$, higher inductive-inductive definition of $\mathbf{No}$ with $\leq$ and $<$, simplicity theorem, addition, negation, embedding of ordinals and reals

**Key Questions:**
1. Why does the higher inductive-inductive construction of Cauchy reals avoid the need for countable choice?
2. What is the relationship between the Cauchy reals and Dedekind reals constructively?
3. How does the inductive cover notion recover Heine–Borel compactness constructively?
4. Why is the simultaneous definition of surreals with their ordering naturally expressed as a higher inductive-inductive type?

---

### Appendix A: Formal Type Theory (pp. 425–441)

**Summary:** Presents two formal presentations of the type theory: one based on untyped $\lambda$-calculus with constants and defining equations, and one as a natural deduction system with explicit contexts, followed by the extensions for homotopy type theory and basic metatheoretic properties.

**Key Definitions & Concepts by Section:**
- **A.1 The first presentation** — Syntax of terms, explicit defined constants, total recursive definitions, convertibility $t \downarrow t'$, judgmental equality from convertibility
- **A.2 The second presentation** — Contexts $\Gamma$, judgments $\Gamma \vdash a : A$ and $\Gamma \vdash a \equiv b : A$, inference rules (formation, introduction, elimination, computation), structural rules (substitution, weakening)
- **A.3 Homotopy type theory** — Function extensionality as axiom, univalence as axiom, higher inductive type rules (example: $S^1$)
- **A.4 Basic metatheory** — Normalization, confluence, decidability of type-checking, logical consistency, canonicity

**Key Questions:**
1. What are the metatheoretic properties guaranteed for the base type theory without univalence?
2. Why does adding univalence break canonicity, and what is Voevodsky's conjecture regarding this?
3. How do the two presentations of type theory relate to each other?