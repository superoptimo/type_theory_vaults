# The Constraint Satisfaction Problem: Complexity and Approximability — Guidelines

## Header

**Title:** The Constraint Satisfaction Problem: Complexity and Approximability
**Author(s):** Andrei Krokhin and Stanislav Živný (Editors); 20 contributing chapter authors
**Publication:** Dagstuhl Follow-Ups, Vol. 7 (Schloss Dagstuhl — Leibniz-Zentrum für Informatik, 2017; ISBN 978-3-95977-003-3), based on Dagstuhl Seminar 15301

**Brief Summary:**
This volume collects twelve peer-reviewed survey articles growing out of Dagstuhl Seminar 15301, presenting the state of the art on the computational complexity and approximability of the Constraint Satisfaction Problem (CSP) — the unifying framework, discovered independently in AI, database theory, and graph theory, for problems that ask whether variables can be assigned values subject to a set of constraints. The central organizing idea is the algebraic approach: the complexity of CSP over a fixed constraint language is controlled entirely by the language's polymorphisms (higher-arity symmetries), and this single idea drives classification results across decision CSP, optimization (valued CSP), counting CSP, quantified CSP, parameterized CSP, and approximation algorithms.

**Intent of the Author:**
The editors intend the volume as a focused follow-up to two earlier Dagstuhl seminars on CSP complexity and approximability (2009, 2012), commissioning surveys precisely where prior literature was missing or outdated, so that researchers already working in one subarea of CSP (universal-algebraic, combinatorial, geometric, or probabilistic) could access adjacent research directions in a common vocabulary. The introductory first chapter is written to require no prior universal-algebra background, while the remaining eleven chapters are aimed at readers who already know the algebraic-CSP basics.

---

## Topic List

1. **The Algebraic Approach to CSP** : [[The-Algebraic-Approach-to-CSP|Link]]
   - Constraint languages and CSP over a fixed language : [[The-Algebraic-Approach-to-CSP|Link]]
   - Primitive positive definitions, interpretations, and constructions : [[The-Algebraic-Approach-to-CSP|Link]]
   - The pp-constructibility poset : [[The-Algebraic-Approach-to-CSP|Link]]
   - Polymorphisms and clones : [[CSP-over-Infinite-and-Numeric-Domains|Link1]], [[Digraph-CSP|Link2]], [[The-Algebraic-Approach-to-CSP|Link3]], [[Valued-CSP|Link4]]
   - The Galois connection between relations and operations : [[The-Algebraic-Approach-to-CSP|Link]]
   - The Feder–Vardi Dichotomy Conjecture and the Bulatov–Jeavons–Krokhin Tractability Conjecture
   - Taylor, weak near-unanimity, cyclic, and Siggers polymorphisms

2. **Absorption Theory** : [[Absorption-Theory|Link]]
   - Absorbing subalgebras and the star composition : [[Absorption-Theory|Link]]
   - Propagating absorption via subpowers : [[Absorption-Theory|Link]]
   - Prague instances and local consistency : [[Absorption-Theory|Link]]
   - Jónsson absorption and congruence distributivity
   - The Absorption Theorem and the Loop Lemma : [[Absorption-Theory|Link]]
   - Conservative CSPs : [[Absorption-Theory|Link]]

3. **CSP over Infinite and Numeric Domains** : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
   - First-order reducts of a base structure : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
   - Omega-categoricity and the Ryll-Nardzewski characterization : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
   - Hilbert's Tenth Problem as a CSP : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
   - Convexity and the midpoint polymorphism : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
   - Max and min as polymorphisms over ordered domains : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
   - Non-dichotomy results : [[Counting-CSP|Link]]

4. **Hybrid Tractability** : [[Hybrid-Tractability|Link]]
   - Independent language and structural restrictions : [[Hybrid-Tractability|Link]]
   - Even Delta-matroids and planar Boolean CSP : [[Hybrid-Tractability|Link]]
   - Bounded occurrence and edge CSPs : [[Hybrid-Tractability|Link]]
   - Forbidden patterns : [[Hybrid-Tractability|Link]]
   - Lifted languages : [[Hybrid-Tractability|Link]]

5. **Backdoor Sets and Fixed-Parameter Tractability** : [[Backdoor-Sets-and-Fixed-Parameter-Tractability|Link]]
   - Strong versus weak backdoor sets : [[Backdoor-Sets-and-Fixed-Parameter-Tractability|Link]]
   - Islands of tractability : [[Backdoor-Sets-and-Fixed-Parameter-Tractability|Link]]
   - Backdoor detection as a parameterized problem : [[Backdoor-Sets-and-Fixed-Parameter-Tractability|Link]]
   - Base classes defined by polymorphism types : [[Backdoor-Sets-and-Fixed-Parameter-Tractability|Link]]
   - Above-guarantee parameterization

6. **Holant Problems** : [[Holant-Problems|Link]]
   - Signature grids and the Holant sum : [[Holant-Problems|Link]]
   - Symmetric signatures and degeneracy : [[Holant-Problems|Link]]
   - Holographic reductions : [[Holant-Problems|Link]]
   - Graph matching as a complexity landmark : [[Holant-Problems|Link]]
   - Planar Holant problems : [[Holant-Problems|Link]]

7. **Counting CSP** : [[Counting-CSP|Link]]
   - The complexity class sharp-P : [[Counting-CSP|Link]]
   - The Creignou–Hermann affine dichotomy : [[Counting-CSP|Link]]
   - Product-type and pure affine functions : [[Counting-CSP|Link]]
   - Weighted counting CSP and partition functions : [[Counting-CSP|Link]]
   - Negative weights and parity of subgraphs : [[Counting-CSP|Link]]

8. **Valued CSP** : [[Valued-CSP|Link]]
   - Cost functions and the VCSP objective : [[Valued-CSP|Link]]
   - Feasibility versus optimization in VCSP : [[Valued-CSP|Link]]
   - Submodularity : [[Valued-CSP|Link]]
   - The Potts model and multiway cut : [[Valued-CSP|Link]]
   - Fractional polymorphisms : [[Valued-CSP|Link]]

9. **Digraph CSP** : [[Digraph-CSP|Link]]
   - CSP as the digraph homomorphism problem : [[Digraph-CSP|Link]]
   - Cores and homomorphic equivalence : [[Digraph-CSP|Link]]
   - The retraction problem and list homomorphism : [[Valued-CSP|Link]]
   - Structural digraph properties: posets, oriented cycles, tournaments
   - Cyclic and conservative polymorphisms on digraphs : [[Valued-CSP|Link]]

10. **Approximation Algorithms for CSP** : [[Approximation-Algorithms-for-CSP|Link]]
    - Maximization, near-satisfiability, and minimization objectives
    - Semidefinite programming relaxations : [[Valued-CSP|Link]]
    - Randomized rounding on the sphere : [[Holant-Problems|Link]]
    - Iterative rounding for non-Boolean domains : [[Approximation-Algorithms-for-CSP|Link]]
    - The Unique Games Conjecture : [[Approximation-Algorithms-for-CSP|Link]]

11. **Quantified CSP** : [[Quantified-CSP|Link]]
    - Positive conjunctive logic : [[Holant-Problems|Link]]
    - The quantifier alternation hierarchy
    - Surjective polymorphisms and their Galois connection : [[Quantified-CSP|Link]]
    - The collapse to the Pi-2 fragment
    - Relativized (list) QCSP : [[Quantified-CSP|Link]]

12. **Counting, Parameterization, and Optimization Variants of CSP** : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link]]
    - MaxSAT and Max-Lin parameterized above a tight bound : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link]]
    - Kernelization
    - Ordering CSPs and approximation resistance : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link]]
    - Model counting and sharp-P-completeness

---

## Chapter Summaries

### Chapter 1: Polymorphisms, and How to Use Them (pp. 1–44)

**Summary:** An introductory survey of the algebraic approach to the decision CSP over a fixed finite constraint language, explaining how symmetries of a language called polymorphisms determine its computational complexity, and how they are used both to prove hardness/tractability classification results and, in some algorithms, directly in the algorithm's execution. : [[CSP-over-Infinite-and-Numeric-Domains|Link1]], [[The-Algebraic-Approach-to-CSP|Link2]]

**Key Definitions & Concepts by Section:**
- **2. CSP over a fixed constraint language** — an instance $P=(V,D,C)$ (variables, domain, constraints, each a scope-relation pair); decision/optimization/counting variants; a constraint language $\mathcal{D}$ and $\mathrm{CSP}(\mathcal{D})$; worked examples: 3-SAT, 1-in-3-SAT, HORN-3-SAT, $k$-COLORING, $H$-COLORING (graph homomorphism), 3-LIN($p$), $s,t$-connectivity, each cast as $\mathrm{CSP}(\mathcal{D})$ for a specific language, with known complexities (NP-complete, P, NL-complete, L-complete, $\mathrm{Mod}_pL$-complete); the Dichotomy Conjecture of Feder and Vardi (every $\mathrm{CSP}(\mathcal{D})$ is in P or NP-complete); CSP as Boolean conjunctive query evaluation and as the homomorphism problem between relational structures. : [[The-Algebraic-Approach-to-CSP|Link]]
- **3. Reductions between constraint languages** — primitive positive (pp-) formulas/definitions ($\mathcal{D}$ pp-defines $\mathcal{E}$ via gadgets); pp-interpretation (generalizing pp-definition to different domains via an onto map $f$ and $f$-preimages); pp-power; pp-constructibility ($\mathcal{D}$ pp-constructs $\mathcal{E}$ via a chain of pp-interpretations, homomorphic equivalences, and singleton expansions), each giving a reduction $\mathrm{CSP}(\mathcal{E})\le\mathrm{CSP}(\mathcal{D})$; cores, endomorphisms, singleton expansions, idempotent languages; the pp-constructibility poset and the Tractability Conjecture (Bulatov–Jeavons–Krokhin: $\mathrm{CSP}(\mathcal{D})\in$ P unless $\mathcal{D}$ pp-constructs 3-SAT's language, the poset's least element); reduction to idempotent languages, to binary-relation languages, and to a single digraph edge relation.
- **4. Polymorphisms as classifiers** — an $n$-ary operation $f$ is a polymorphism of relation $R$ (equivalently $R$ is invariant under $f$) if applying $f$ column-wise to any $n$ rows of $R$ stays in $R$; worked examples (majority operation on 2-SAT, $\min$ on Horn-SAT, affine combination on 3-LIN($p$), the dual discriminator); the clone $\overline{\mathcal{D}}$ of all polymorphisms of $\mathcal{D}$ (contains projections, closed under composition); the Galois correspondence: $\mathcal{D}$ pp-defines $\mathcal{E}$ iff $\overline{\mathcal{D}}\subseteq\overline{\mathcal{E}}$, so complexity of $\mathrm{CSP}(\mathcal{D})$ depends only on the clone $\overline{\mathcal{D}}$; height-1 identities and pp-constructibility (an algebraic characterization of the pp-constructibility order); the Taylor polymorphism, weak near-unanimity (WNU), cyclic, and Siggers polymorphisms as equivalent characterizations of the tractable side of the Tractability Conjecture; analogous algebraic characterizations for languages avoiding 3-LIN($p$) or both 3-LIN($p$) and HORN-3-SAT. : [[The-Algebraic-Approach-to-CSP|Link]]
- **5. Polymorphisms guaranteeing algorithm correctness** — linear programming relaxations and symmetric polymorphisms; a characterization of bounded width (solvability by local consistency checking) in terms of polymorphisms; sufficient levels of consistency; results on linear and symmetric width. : [[The-Algebraic-Approach-to-CSP|Link]]
- **6. An algorithm using polymorphisms directly** — the Few Subpowers property (polynomially many, polynomially-generated subpowers, equivalently the existence of a $k$-edge operation) and the Few Subpowers Algorithm; its limits; combining algorithms via pp-definable auxiliary problems. : [[Valued-CSP|Link]]

**Key Questions:**
1. Why does the complexity of $\mathrm{CSP}(\mathcal{D})$ depend only on the clone $\overline{\mathcal{D}}$ of polymorphisms rather than on the specific relations in $\mathcal{D}$, and how does the Galois correspondence (Theorem 32) make this precise?
2. How does the chain pp-definition $\subseteq$ pp-interpretation $\subseteq$ pp-construction let one compare the complexity of CSPs over *different* domains, and why is each successive notion strictly more general than the last?
3. Why do so many seemingly different algebraic conditions (Taylor, WNU, cyclic, Siggers polymorphisms) all turn out to be equivalent characterizations of the same tractability boundary — what does this convergence suggest about the naturalness of the underlying dividing line?

---
### Chapter 2: Absorption in Universal Algebra and CSP (pp. 45–77)

**Summary:** Introduces absorption — a simple algebraic concept resembling near-unanimity operations — and shows how it has driven major results in both universal algebra and CSP complexity, including the dichotomy theorem for digraphs with no sources or sinks, characterizations of when local consistency algorithms solve a CSP, and the identification of cyclic operations as the conjectured tractable/NP-complete borderline. : [[Absorption-Theory|Link]]

**Key Definitions & Concepts by Section:**
- **1. Introduction** — relational structure $\mathbf{A}=(A;R_1,\dots,R_k)$; pp-formulas/CSP($\mathbf{A}$); equational conditions (existence of term operations satisfying identities, e.g. a Mal'tsev term $m(x,x,y)=y=m(y,x,x)$ characterizing permutable compatible equivalences); the Pol–Inv Galois connection (complexity of CSP($\mathbf{A}$) depends only on the algebra $\mathrm{Pol}(\mathbf{A})$) and the Mod-Id Galois connection (only the equational conditions the algebra satisfies matter); absorption's three-part usefulness: it *transfers connectivity*, connectivity is *common* (reflected structurally by equational conditions, and provided algorithmically by local consistency checking), and absorption itself is *common* (mild assumptions force either a strong structural restriction or an interesting absorption). : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2. Worked example** — the triangle-with-constants structure $\mathbf{K}^c_3$ (complete graph on 3 vertices plus singleton constants) is shown step by step to have no polymorphisms beyond projections, hence pp-defines every relation on $\{0,1,2\}$ and is maximally hard; illustrates how one/two-element subsets are forced to be subuniverses, unary/binary polymorphisms are forced trivial, and higher-arity polymorphisms decompose via binary "traces" $f_i(x,y)=f(x,\dots,x,y,x,\dots,x)$. : [[Absorption-Theory|Link1]], [[Valued-CSP|Link2]]
- **3. Absorption fundamentals** — Definition: subalgebra $B\le A$ is absorbing w.r.t. $n$-ary term $f$ (written $B\trianglelefteq_fA$) if $f(a_1,\dots,a_n)\in B$ whenever at most one $a_i\notin B$; two-element algebras with a non-affine operation always have an absorbing singleton (explaining Horn-SAT's and 2-SAT's polynomial-time algorithms); near-unanimity operations make every singleton absorbing (and conversely); the star composition $f\star g$ combining two witnessing operations into one, showing absorption is transitive and closed under intersection; propagating absorption between subuniverses via compatible relations (subpowers). : [[Absorption-Theory|Link]]
- **4. Connectivity applications** — absorbing linkedness; Prague instances as a connectivity condition central to characterizing when local consistency algorithms (e.g. (2,3)-minimality, Singleton Arc Consistency) solve a CSP.
- **5. Structural characterizations** — decomposable relations and near-unanimity; rectangular relations and the Mal'tsev term; congruence distributivity via Jónsson terms and (directed) Jónsson absorption. : [[Absorption-Theory|Link]]
- **6. The Absorption Theorem and its consequences** — the Loop Lemma; the Siggers term and cyclic terms as the conjectured tractable/NP-complete dividing line; application to conservative CSPs (structures containing all unary relations). : [[Absorption-Theory|Link]]
- **7. Consistency and Prague instances** — local consistency checking and consistency notions for general instances. : [[Absorption-Theory|Link]]
- **8. Abelianness and higher-arity absorption** — abelianness as an obstruction to absorption; the Absorption Theorem generalized to relations of higher arity. : [[Absorption-Theory|Link]]

**Key Questions:**
1. Why does the definition of absorption ("at most one coordinate outside $B$") generalize the near-unanimity property, and how does the two-element-algebra case (Horn-SAT via a $\min$/$\max$ absorbing singleton, 2-SAT similarly) illustrate absorption's connection to known tractability results?
2. In the worked $\mathbf{K}^c_3$ example, why does forcing all one- and two-element subsets to be subuniverses of $\mathrm{Pol}(\mathbf{K}^c_3)$, combined with the fact that the clone's binary operations are all projections, suffice to show that *every* polymorphism of any arity must be a projection?
3. What does it mean for absorption to "transfer connectivity," and why does the chapter argue this is the essential mechanism by which local-consistency-checking results (Prague instances, robust approximation) were proved using absorption rather than direct combinatorial arguments?

---
### Chapter 3: Constraint Satisfaction Problems over Numeric Domains (pp. 79–111)

**Summary:** Surveys CSP over infinite numeric domains ($\mathbb{Z},\mathbb{Q},\mathbb{R},\mathbb{C}$) with constraints first-order definable from addition and multiplication, showing that while no general complexity classification is possible for infinite-domain CSP (every computational problem is polynomial-time equivalent to some $\mathrm{CSP}(\Gamma)$), a "bottom-up" approach classifying first-order reducts of progressively richer base structures ($(\mathbb{Q};<)$, $(\mathbb{Z};\mathrm{Succ})$, etc.) has yielded systematic dichotomy results extending the finite-domain algebraic approach. : [[CSP-over-Infinite-and-Numeric-Domains|Link]]

**Key Definitions & Concepts by Section:**
- **Introduction** — $\mathrm{CSP}(\Gamma)$ for a template $\Gamma$ with finite relational signature $\tau$; Hilbert's 10th problem as $\mathrm{CSP}(\mathbb{Z};R_+,R_*,R_{=1})$, shown undecidable by Matiyasevich; linear programming feasibility as $\mathrm{CSP}(\mathbb{Q};\le,R_+,R_{=1})$, polynomial via Khachiyan's ellipsoid method; domain choice can leave complexity unchanged (rationals vs. reals for linear constraints) or change it dramatically (integers vs. reals/complex numbers for polynomial constraints, the latter reducing to the decidable existential theory of the reals/complex numbers); linear Diophantine systems (polynomial via Smith normal form) and difference logic (polynomial via shortest paths) as tractable integer CSPs; first-order reducts $\Gamma$ of a structure $\Delta$ (relations of $\Gamma$ first-order definable in $\Delta$) as the "bottom-up" classification strategy; the complete dichotomy for first-order reducts of $(\mathbb{Q};<)$ (Bodirsky–Kára), enabled by $\omega$-categoricity (Ryll-Nardzewski: finitely many orbits of $k$-tuples under the automorphism group for every $k$) letting the finite-domain polymorphism machinery transfer; numeric structures like $(\mathbb{Z};\mathrm{Succ})$ are typically *not* $\omega$-categorical, requiring passage to a richer-polymorphism structure with the same CSP (e.g. $(\mathbb{Q};\{(x,y):x=y+1\})$ in place of $(\mathbb{Z};\mathrm{Succ})$) to recover an algebraic classification; key polymorphisms over numeric domains: the midpoint operation $(x,y)\mapsto(x+y)/2$ (characterizing convexity of all relations) and $\max$/$\min$ (guaranteeing polynomial-time solvability for finite structures, $(\mathbb{Q};<)$-reducts, and $(\mathbb{Z};\mathrm{Succ})$-reducts, but open in general — connecting to open problems like the $\mu$-calculus model-checking problem, mean payoff games, and simple stochastic games); the proven *non-existence* of a complexity dichotomy for first-order reducts of $(\mathbb{Z};+,*)$.
- **2.1–2.2 Primitive positive formulas and polymorphisms** — pp-formulas $\exists x_1,\dots,x_n(\psi_1\wedge\cdots\wedge\psi_m)$; the Jeavons–Cohen–Gyssens lemma extended to infinite structures (pp-definable relation additions are CSP-equivalence-preserving); polymorphisms $f:B^k\to B$ preserving a relation, generalizing the finite-domain notion.

**Key Questions:**
1. Why is a *general* complexity classification impossible for infinite-domain CSP (every computational problem reduces to some $\mathrm{CSP}(\Gamma)$), and how does the "bottom-up" strategy of classifying first-order reducts of a fixed, progressively richer base structure sidestep this while still yielding real dichotomy theorems?
2. Why does $\omega$-categoricity (via Ryll-Nardzewski's finitely-many-orbits characterization) play the same structural role for infinite-domain CSP that finiteness plays for the classical algebraic approach, and why do numeric structures like $(\mathbb{Z};\mathrm{Succ})$ typically fail to have it?
3. What does it mean that whether $\max$ as a polymorphism guarantees tractability is *open* for reducts of $(\mathbb{Q};<,+,1)$, and why would resolving it also resolve several seemingly unrelated open problems (µ-calculus model checking, mean payoff games, simple stochastic games)?

---
### Chapter 4: Hybrid Tractable Classes of Constraint Problems (pp. 113–135)

**Summary:** Surveys "hybrid" tractable classes of (V)CSPs — classes defined by restrictions that are neither purely language-based nor purely structure-based — covering independent language-and-structure restrictions, forbidden patterns, consistency-based restrictions, microstructure graph properties, and search-tree-size bounds, since these five families do not yet share a unifying theory.

**Key Definitions & Concepts by Section:**
- **1. Introduction** — CSP/VCSP as generic frameworks; language-based tractable classes (fixed constraint language $\Gamma$) vs. structure-based tractable classes (restricted hypergraph of constraint scopes) as the two classical, well-studied restriction types; hybrid classes as everything else, illustrated by two motivating examples (a bonus-assignment problem and a staffing/cost problem) each falling into a hybrid tractable class; five identified ways to define a hybrid class: independent language+structure restrictions, forbidden patterns (excluding generic sub-instances), post-preprocessing consistency properties, (weighted) microstructure graph properties, and instances so strongly (or weakly) constrained that search-tree size is polynomially bounded. : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2. Independent language and structure restrictions** — a CSP instance $\langle X,D,C\rangle$; constraint language $\Gamma$ and $\mathrm{CSP}(\Gamma)$; CSP as a homomorphism problem (language-based = fixed target structure, structure-based = restricted source-structure class). : [[Hybrid-Tractability|Link]]
- **2.1 Planarity** — the incidence graph of an instance; $\mathrm{CSP}_p(\Gamma)$ (planar-incidence-graph Boolean instances with clockwise scope ordering); even $\Delta$-matroids (via self-complementary relations and the $\oplus$-difference transform $d\Gamma$) as exactly the tractability boundary for planar Boolean CSPs; the perfect-matching-in-graphs problem modeled via the language $\Gamma_{pm}$ built from exactly-one-hot relations $M_k$.
- **2.2 Bounded occurrence** — $\mathrm{CSP}_k(\Gamma)$ (each variable in at most $k$ constraints); Feder's result that $\mathrm{CSP}_3(\Gamma)$ is as hard as $\mathrm{CSP}(\Gamma)$ for Boolean languages with constants; edge CSPs / Holant problems ($\mathrm{CSP}_e(\Gamma)$, every variable in exactly two constraints) tractable exactly for (even) $\Delta$-matroids, again capturing perfect matching. : [[Hybrid-Tractability|Link]]
- **2.3 Lifted languages** — shifting the complexity analysis of structurally-restricted instances (hypergraphs closed under inverse homomorphisms, e.g. acyclic or $k$-colourable graphs) to a derived "lifted" constraint language $\Gamma'$, reusing the algebraic machinery of language-based classification. : [[Hybrid-Tractability|Link]]
- **(remaining sections, by known structure)** — forbidden-pattern-based tractable classes; consistency-based hybrid classes; microstructure-based tractability; strongly/weakly constrained instance classes with bounded search trees.

**Key Questions:**
1. Why does the tractability boundary for *planar* Boolean CSPs (even $\Delta$-matroids) differ from the tractability boundary for unrestricted Boolean CSPs, and what role does the clockwise-scope-ordering condition in the planar-incidence-graph definition play in making this boundary well-defined?
2. Why does bounding variable occurrence to $k=3$ already make $\mathrm{CSP}_3(\Gamma)$ "as hard as" the unrestricted $\mathrm{CSP}(\Gamma)$ (for Boolean languages with constants), while occurrence exactly $2$ (edge CSPs / Holant problems) yields a genuinely restricted and sometimes tractable class?
3. What does the chapter mean by "lifting" a structural restriction into a derived constraint language $\Gamma'$, and why does this let the *language-based* algebraic classification machinery (built for language-only restrictions) apply to a class defined by a *structural* restriction (closure under inverse homomorphisms)?

---
### Chapter 5: Backdoor Sets for CSP (pp. 137–157)

**Summary:** Surveys the parameterized complexity of backdoor sets for CSP — sets of variables whose instantiation moves an instance into a tractable "island of tractability" — covering how backdoor size gives a fixed-parameter-tractable algorithmic handle on instances that are "close to" a tractable class, for base classes defined via single, finite, and infinite sets of constraint languages (via polymorphism types). : [[Backdoor-Sets-and-Fixed-Parameter-Tractability|Link]]

**Key Definitions & Concepts by Section:**
- **1. Introduction** — islands of tractability defined via a fixed constraint language $\Gamma$ (Schaefer's dichotomy for 2-element domains, Bulatov's for 3-element domains, the general Feder–Vardi Dichotomy Conjecture); a strong backdoor set $B$: every instantiation of $B$'s variables reduces the instance into class $H$; a weak backdoor set: at least one instantiation reduces to a *satisfiable* instance in $H$; solving via a strong backdoor of size $k$ over domain size $d$ costs $d^k\cdot p(|I|)$ — exponential only in $d,k$, not instance size, i.e. fixed-parameter tractable (FPT); the two-part backdoor approach: (1) detect a small backdoor set, (2) exploit it to solve the instance; the central question of when backdoor-set *detection* itself is FPT in the backdoor size. : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2.1 Constraint satisfaction preliminaries** — a constraint $(S,R)$ of arity $\rho$; scope $\mathrm{var}(C)$; assignment restriction $C|_\alpha$ (filtering tuples consistent with $\alpha$, then dropping assigned coordinates); a constraint language $\Gamma$ globally tractable (poly-time solvable) and efficiently recognizable (poly-time checkable membership).
- **2.2 Polymorphisms** — a relation $R$ closed under an $n$-ary operation $\varphi$ (component-wise application of $\varphi$ to any $n$ tuples of $R$ stays in $R$); $\Gamma(\varphi)$ (all relations closed under $\varphi$) and $\mathrm{CSP}(\varphi):=\mathrm{CSP}(\Gamma(\varphi))$; $\varphi$ tractable if $\Gamma(\varphi)$ is globally tractable; extending closedness to constraints/instances. : [[Digraph-CSP|Link]]
- **2.3 Base classes** — using single constraint languages, or polymorphism *types* (constant, idempotent, conservative, min/max, and others) to characterize infinite families of tractable constraint languages as backdoor targets. : [[Backdoor-Sets-and-Fixed-Parameter-Tractability|Link]]
- **3–6 (by known structure)** — backdoor sets into a single fixed base language; backdoor sets into base classes defined by finite/infinite sets of constraint languages (via polymorphism types), with FPT detection results; extension to Valued CSP; exploiting large backdoor sets whose induced graph has simple structure.
- **7–8 Related work and conclusion.**

**Key Questions:**
1. Why does knowing a strong backdoor set of size $k$ into a tractable class $H$ make an otherwise-intractable CSP instance solvable in time exponential only in $k$ and the domain size $d$ (not the instance size), and why is this specifically what "fixed-parameter tractable" means?
2. What is the practical difference between a *strong* and a *weak* backdoor set in terms of what solving the original instance via the backdoor actually requires, and why does detecting a satisfying assignment via a weak backdoor still require solving *all* reduced instances rather than just one?
3. Why does characterizing infinite families of tractable constraint languages via *polymorphism types* (e.g. "having a conservative polymorphism") let the backdoor-set approach scale beyond backdoors into a single fixed base language, to backdoors into an entire class of base languages at once?

---
### Chapter 6: On the Complexity of Holant Problems (pp. 159–177)

**Summary:** Surveys the Holant framework — a generalization of CSP (and of counting CSP) that natively expresses problems like graph matching that CSP cannot — covering the decision, exact-counting, and approximate-counting complexity of Holant problems, motivated by graph matching's history as a recurring boundary case between tractability and intractability. : [[Holant-Problems|Link]]

**Key Definitions & Concepts by Section:**
- **1. Introduction** — Ladner's theorem (an infinite hierarchy of intermediate problems if P$\ne$NP) motivating the search for restricted subclasses with dichotomy theorems; the graph matching problem's rich complexity landscape as motivation: perfect matching decision is polynomial (Edmonds' blossom algorithm, the paper that proposed P as *the* class of tractable problems), counting perfect matchings is #P-complete (Valiant), counting perfect matchings on *planar* graphs is polynomial (the FKT algorithm, also the computational primitive behind holographic algorithms), matching parity is polynomial (via permanent $\equiv$ determinant mod 2), and approximate counting has an FPRAS for general graphs (matchings) and for bipartite perfect matchings/permanents but not (yet) for general perfect matchings; CSP as a special case of Holant assuming equality relations of every arity are always freely available; Holant's greater expressiveness (captures matchings, which CSP cannot) and additional structure (new tractable cases via holographic algorithms) for the same constraint language. : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2. Definitions and background** — a signature grid $\Omega=(G,F,\pi)$ (graph, function set, vertex-to-function assignment matching arity to vertex degree); the Holant value $\mathrm{Holant}_\Omega=\sum_\sigma\prod_{v\in V}f_v(\sigma|_{E(v)})$ summing over edge-assignments; $\mathrm{Holant}(F)$ as the counting problem parameterized by function set $F$; $\mathrm{Pl}\text{-}\mathrm{Holant}(F)$ for planar instances; a function/signature (viewed as a tensor); symmetric functions and their compact signature notation $[f_0,\dots,f_k]$ (value by Hamming weight); $=_k$, $\Delta_s$, and $\mathrm{ExactOne}_k$ as named signatures, with $\mathrm{Holant}(EO)$ exactly counting perfect matchings; signature equivalence under nonzero scalar multiplication (projective view) and degeneracy (decomposability into a tensor product of unary signatures); the bipartite form $\mathrm{Holant}(F\mid G)$.
- **2.1 Holographic reductions** — the 2-stretch transformation turning any graph into a bipartite (edge-vertex incidence) graph while preserving the Holant value, using the binary equality signature $=_2=[1,0,1]$ on new vertices; the linear-transformation technique $TF=\{g:g=T^{\otimes n}f,f\in F\}$ (and $FT$) underlying holographic reductions, letting problems be related via a change of tensor basis rather than a combinatorial gadget reduction. : [[Holant-Problems|Link]]
- **3–5 (by known structure)** — decision-version dichotomies for Holant problems; the main exact-counting dichotomy results (the survey's central focus, given recent rapid progress); approximate-counting results for Holant problems.

**Key Questions:**
1. Why can graph matching (perfect matchings) be naturally expressed in the Holant framework but not in ordinary CSP, and what does this reveal about what "assuming equality relations of every arity are freely available" (CSP as a Holant special case) actually costs in expressive power?
2. What does a holographic reduction (via the linear transformation $T^{\otimes n}$) accomplish that a standard combinatorial gadget reduction cannot, and why does this technique specifically unlock new tractable cases not visible from the CSP viewpoint?
3. Given the graph-matching complexity landscape summarized in the introduction (P for decision, #P-complete for exact counting, P again for planar exact counting, open for general-graph approximate counting), what does this progression suggest about why matching problems are treated as a critical test case for any proposed Holant dichotomy theorem?

---
### Chapter 7: Parameterized Constraint Satisfaction Problems: a Survey (pp. 179–203)

**Summary:** Surveys CSPs parameterized *above or below a guaranteed (tight) bound* — rather than by a raw solution-size parameter — for MaxSAT, Max-Lin2, and Ordering CSP variants, showing this reframing is what makes the parameter meaningfully small and the resulting problems worth studying via fixed-parameter algorithms and polynomial kernels. : [[Quantified-CSP|Link]]

**Key Definitions & Concepts by Section:**
- **1. Introduction** — the standard parameterization $k$-MaxSAT (satisfy at least $k$ clauses) is not "in the spirit" of parameterized complexity because every instance already trivially satisfies $m/2$ clauses, so only $k>m/2$ is interesting — but then $k$ is too large for FPT algorithms to be useful; this motivates parameterization *above the tight bound*: satisfy at least $m/2+k$ clauses, with $k$ now meaningfully small; the tightness of $m/2$ shown via pairs of complementary unit clauses; MaxLin2-AA, Max-$r$-Lin2-AA, Max-$r$-SAT-AA, and the general Max-$r$-CSP-AA as instances of this "above guarantee" (AG) parameterization scheme; Ordering CSPs parameterized above the average value, connected to approximation-resistance results under the Unique Games Conjecture. : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2. Basics** — a parameterized problem as a set of pairs $(I,k)$; fixed-parameter tractability (FPT): solvable in $O(f(k)|I|^c)$; kernelization (polynomial-time-computable equivalent instance of size bounded by a function of $k$ alone).
- **3. The Strictly-Above-Below-Expectation Method (SABEM)** — a technique combining probabilistic method and harmonic analysis tools to prove FPT/kernelization results for above-guarantee parameterizations. : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link]]
- **4. Maximum $r$-CSPs above average** — Max-$r$-CSP-AA (satisfy weight $\ge A+k$ where $A$ is the average over random assignments); Max-$r$-Lin2-AA's quadratic kernel and the alternative $(2k-1)^r$-variable kernel; the reduction-based proof that Max-$r$-CSP-AA has a polynomial (degree unknown) kernel via a bikernel through Max-$r$-Lin2-AA. : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link]]
- **5. MaxLin2 parameterizations** — MaxLin2-AA (unbounded equation arity) shown FPT with a polynomial-variable kernel, resolving an open question; the "below" parameterization (satisfy weight $\ge W-k$) shown W[1]-hard in general, with a classification of tractable/W[1]-hard special cases. : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link]]
- **6. Further MaxSAT parameterizations** — MaxSAT-A($m/2$); Max-$r(n)$-SAT-AA with $r$ depending on $n$, and ETH-based bounds separating FPT from non-FPT regimes; $t$-satisfiable-formula-based "stronger" parameterizations (linear-variable kernels for $t=2,3$); 2-SAT parameterized below the clause-count upper bound, shown FPT.
- **7. Ordering CSPs above average** — approximation-resistance under UGC for Ordering CSPs of arity $\ge2$ contrasted with FPT-above-average results (2-Linear Ordering, arity-3 Ordering CSPs, and eventually all arities); the Betweenness-above-average result resolving an open question of Chor. : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link]]
- **8. Open problems.** : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link1]], [[Digraph-CSP|Link2]]

**Key Questions:**
1. Why is the *standard* parameterization $k$-MaxSAT ("satisfy at least $k$ clauses") not meaningful in the spirit of parameterized complexity, and how does reparameterizing *above the guaranteed bound* $m/2$ fix this while still capturing the interesting instances?
2. Why is the $m/2$ bound for MaxSAT "tight" (illustrated by complementary unit-clause pairs), and what does tightness have to do with the reasonableness of using $k$ (the excess over $m/2$) as a parameter?
3. How does the "above guarantee" parameterization scheme connect approximation-resistance results (e.g. Ordering CSPs being hard to beat the random-assignment baseline under UGC) to parameterized tractability results (the same problems being FPT above that same baseline) — are these in tension, or complementary?

---
### Chapter 8: Counting Constraint Satisfaction Problems (pp. 205–231)

**Summary:** Surveys counting CSPs (#CSP) — computing the number of satisfying assignments rather than deciding existence — for both unweighted relations and weighted function-based generalizations (motivated by statistical physics), organized primarily along the exact-vs-approximate-computation divide, and explicitly excluding holants (covered separately).

**Key Definitions & Concepts by Section:**
- **1. Introduction** — $\#\mathrm{CSP}(\Gamma)$: given constraints $(R_i,\mathbf{x}_i)$ from language $\Gamma$, count satisfying assignments $\sigma:X\to D$; counting is never easier than deciding but can be strictly harder — illustrated by $\Gamma=\{\mathrm{NAND}\}$, whose decision problem (independent set exists) is trivial but whose counting problem (count independent sets) is #P-complete, and even approximating it within relative error is intractable unless RP=NP; the weighted generalization replacing relations with functions $f:D^k\to R$ into a commutative semiring $R$ (e.g. $\mathbb{C},\mathbb{R},\mathbb{R}_{\ge0}$), with output the partition-function-like sum $Z(X,C)=\sum_{\sigma:X\to D}\prod_if_i(\sigma(\mathbf{x}_i))$ — recovering classical decision CSP via the Boolean semiring and VCSP via the $(\min,+)$ tropical semiring; holants excluded as a separate, more general "read-twice" framework (can express things #CSP cannot, e.g. the perfect-matching generating function/dimer model). : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2. Exact computation** — the complexity class #P (accepting-computation counts of an NP machine); #P-hardness/completeness via Turing reductions; weighted #CSP over rational/algebraic weights lands in $\mathrm{FP}^{\#P}$ rather than #P itself (non-integer outputs).
- **2.1 Boolean #CSPs** — Creignou–Hermann dichotomy: for $\Gamma$ on $\{0,1\}$, $\#\mathrm{CSP}(\Gamma)\in\mathrm{FP}$ if every relation is affine (solution set of linear equations over $\mathbb{F}_2$), else #P-complete — a much more pessimistic dichotomy than Schaefer's decision-CSP one, since bijunctive/0-valid/1-valid/Horn/dual-Horn conditions (each sufficient for decision tractability) are *not* sufficient for counting tractability (the IMP relation is bijunctive, 0-valid, 1-valid, Horn, *and* dual-Horn, yet $\#\mathrm{CSP}(\{\mathrm{IMP}\})$ is #P-complete, being equivalent to counting downsets in a poset); proof idea: affine instances reduce to computing the dimension $d$ of a solution affine subspace (answer $2^d$), while non-affine languages can implement NAND, OR, or IMP; the weighted extension (Dyer–Goldberg–Jerrum): $\#\mathrm{CSP}(F)\in\mathrm{FP}$ iff $F$ consists of product-type functions ($\mathcal{P}$: products of nullary/unary/equality/disequality functions) or pure affine functions ($\mathcal{A}$: 0,1-valued affine-relation indicators scaled by a constant), else #P-hard; the function $H_2$ (counting even/odd-edge induced subgraphs) as the first hint that *negative* real weights introduce genuinely new phenomena beyond the non-negative-weight case. : [[Approximation-Algorithms-for-CSP|Link]]

**Key Questions:**
1. Why is it possible for a decision CSP to be trivial (every instance is a "yes" instance) while its counting analogue is #P-complete, as illustrated by NAND/independent sets — what does this reveal about the relationship between "does a solution exist" and "how many solutions exist" as computational questions?
2. Why does the Creignou–Hermann dichotomy require the much stronger condition "affine" for counting tractability, when several weaker conditions (bijunctive, 0/1-valid, Horn, dual-Horn) each suffice for decision tractability — what does the IMP-relation counterexample show about why these conditions fail to transfer to counting?
3. Why does moving from non-negative real weights to weights that can be *negative* (as in the $H_2$ function counting even/odd-edge subgraphs) introduce fundamentally new complexity phenomena not seen in the non-negative-weight dichotomy?

---
### Chapter 9: The Complexity of Valued CSPs (pp. 233–266)

**Summary:** Surveys Valued CSP (VCSP) — the generic optimization framework generalizing CSP by summing real-valued cost functions rather than conjoining Boolean relations — covering the algebraic approach to identifying tractable and NP-hard valued constraint languages, with concrete examples spanning satisfiability, graph cuts, and statistical-mechanics models. : [[Valued-CSP|Link1]], [[Counting-CSP|Link2]]

**Key Definitions & Concepts by Section:**
- **1. Introduction** — VCSP as a common framework for Gibbs energy minimization, Markov/Conditional Random Fields, Min-Sum problems, Minimum Cost Homomorphism, and general Constraint Optimisation; a cost function $\varphi:D^m\to\overline{\mathbb{Q}}=\mathbb{Q}\cup\{\infty\}$; a valued constraint $\varphi(\mathbf{x})$; a VCSP instance's objective $\Phi(x_1,\dots,x_n)=\sum_i\varphi_i(\mathbf{x}_i)$, to be minimized; infinite cost encodes infeasibility; finite-valued instances reduce to pure optimization, $\{0,\infty\}$-valued instances reduce to pure feasibility (i.e. classical CSP), and "general-valued" instances mix both. : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2. Problems captured by VCSP** — a valued constraint language $\Gamma\subseteq\Phi_D$ and $\mathrm{VCSP}(\Gamma)$; tractability/NP-hardness of $\Gamma$ defined via all its finite subsets (making the definition independent of explicit-vs-oracle cost-function representation); worked examples each realized as $\mathrm{VCSP}(\Gamma)$ for a specific language: 1-in-3-SAT ($\Gamma_{1\text{-}in\text{-}3}$, NP-hard), Not-All-Equal-SAT / 3-uniform hypergraph 2-colorability ($\Gamma_{nae}$, NP-hard), Maximum $k$-Cut ($\Gamma_{xor}$, NP-hard for all $|D|\ge2$), the Potts model from statistical mechanics ($\Gamma_{Potts}$: tractable for $|D|=2$ via submodularity, NP-hard for $|D|>2$ via reduction from multiway cut), and $(s,t)$-Min-Cut ($\Gamma_{cut}$, via unary "must-be-$d$" cost functions $\eta_d^c$ and directed-edge cost functions $\varphi_{cut}^w$). : [[Digraph-CSP|Link]]
- **3–4 Algebraic tractability theory** — algebraic properties of cost functions (generalizing polymorphisms to weighted settings, e.g. submodularity) used to identify tractable cases; the general algebraic theory (fractional polymorphisms) for analyzing VCSP complexity.
- **5–6 Tractable and intractable cases** — applying the algebraic theory to classify specific valued languages.
- **7. The oracle model** — representing cost functions implicitly via value oracles rather than explicit tables. : [[Valued-CSP|Link]]
- **8. Summary and open problems.** : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link1]], [[Digraph-CSP|Link2]], [[Holant-Problems|Link3]]

**Key Questions:**
1. How does the choice of cost-function range in a VCSP instance (finite values only, vs. only $\{c,\infty\}$ per constraint, vs. genuinely mixed) determine whether the instance reduces to pure optimization, pure feasibility (classical CSP), or requires handling both simultaneously?
2. Why does the Potts model's tractability depend so sharply on domain size — tractable for $|D|=2$ via submodularity but NP-hard for $|D|>2$ via a reduction from multiway cut — and what does this reveal about how binary-domain algebraic structure can fail to generalize?
3. Why does defining a valued constraint language's tractability in terms of *all its finite subsets* (rather than the possibly-infinite language directly) make the tractability classification independent of how cost functions are represented (explicit tables vs. oracles)?

---
### Chapter 10: Algebra and the Complexity of Digraph CSPs: a Survey (pp. 267–285)

**Summary:** Surveys how algebraic (polymorphism-based) and graph-theoretic techniques interact in the study of CSPs whose fixed template is a digraph — chosen as a test bed because digraphs are simple, drawable, admit rich combinatorial subfamilies (posets, tournaments, oriented trees, etc.), and are flexible enough to encode hard problems — covering the three main digraph-CSP variants and known dichotomy/characterization results for them.

**Key Definitions & Concepts by Section:**
- **1. Introduction** — the general algebraic-CSP paradigm (polymorphisms obeying nice identities $\Rightarrow$ tractability; their absence $\Rightarrow$ hardness) specialized to digraph templates; four categories of digraph CSP: (i) plain $\mathrm{CSP}(H)$, (ii) CSP with constants / retraction problem / one-or-all list homomorphism $\mathrm{CSP}(H^{+c})$ (all singleton unary relations added), (iii) list homomorphism / conservative CSP $\mathrm{CSP}(H^{+l})$ (all non-empty unary relations added), (iv) variants with input restrictions (largely unexplored algebraically); guiding questions: are dichotomy conjectures proved for a given digraph class, and are there combinatorial characterizations of digraphs admitting particular polymorphisms? : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2.1 Relational structures and digraphs** — structure $\mathbf{H}=\langle H;\theta_1,\dots,\theta_r\rangle$; structure product $\mathbf{H}_1\times\mathbf{H}_2$ and powers $\mathbf{H}^k$; homomorphism $f:\mathbf{G}\to\mathbf{H}$; homomorphic equivalence; core (every self-homomorphism is a bijection; every structure has a core, unique up to isomorphism); $\mathrm{CSP}(\mathbf{H})$ as the structures admitting a homomorphism to $\mathbf{H}$, invariant under replacing $\mathbf{H}$ with its core; $\mathbf{H}^{+c}$/$\mathbf{H}^{+l}$ formalizing the homomorphism-extension (retraction) problem and the list-homomorphism (conservative CSP) problem respectively — both are cores by construction. : [[Digraph-CSP|Link]]
- **2.2 Digraphs** — vertices/arcs, in-/out-neighbours; connectivity and strong connectivity, (strong) connected components; bipartite, reflexive, symmetric (= graph), antisymmetric, transitive digraphs; a poset as a reflexive antisymmetric transitive digraph; oriented paths/cycles, net (algebraic) length, balanced vs. unbalanced cycles, directed cycles, oriented trees. : [[Digraph-CSP|Link]]
- **2.3 Polymorphisms** — a polymorphism of arity $k$ as a homomorphism $\mathbf{H}^k\to\mathbf{H}$; idempotent and conservative polymorphisms; linear identities (universally-quantified equalities between term expressions); semilattice operations (associative, idempotent, commutative); cyclic operations $f(x_1,\dots,x_k)\approx f(x_k,x_1,\dots,x_{k-1})$. : [[Digraph-CSP|Link]]
- **3–6 (by known structure)** — the general CSP results and dichotomy conjectures oriented toward digraphs; results on plain digraph CSPs and notable subfamilies; results on digraphs-with-constants (retraction) CSPs; results on list-homomorphism (conservative) CSPs.
- **7. Open problems.** : [[Counting,-Parameterization,-and-Optimization-Variants-of-CSP|Link1]], [[Digraph-CSP|Link2]]

**Key Questions:**
1. Why do digraphs serve as an especially productive test bed for CSP dichotomy conjectures — what combination of simplicity (drawability), combinatorial richness (many natural subfamilies), and expressive power (encoding hard problems) makes them uniquely suited to this role?
2. What is the essential difference in what an instance specifies among plain $\mathrm{CSP}(H)$, the retraction problem $\mathrm{CSP}(H^{+c})$ (pre-colored elements), and the list-homomorphism problem $\mathrm{CSP}(H^{+l})$ (per-element candidate lists), and why does adding "all singletons" vs. "all non-empty subsets" as extra unary relations produce genuinely different computational problems?
3. Why must $\mathbf{H}^{+c}$ and $\mathbf{H}^{+l}$ always be cores by construction, and what does this guarantee about applying the standard "reduce to the core" simplification when studying these variants?

---
### Chapter 11: Approximation Algorithms for CSPs (pp. 287–325)

**Summary:** A technique-focused survey of approximation algorithms for CSPs, centered on semidefinite programming (SDP) relaxation-and-rounding as the dominant tool, distinguishing three genuinely different approximation objectives, and building up SDP complexity from Boolean 2-CSPs through non-Boolean 2-CSPs to general arity-$k$ CSPs. : [[Approximation-Algorithms-for-CSP|Link]]

**Key Definitions & Concepts by Section:**
- **1. Introduction** — a $k$-CSP (arity-$\le k$ constraints); $(1-\varepsilon)$-satisfiable instance; approximation factor $\alpha$ for max/min problems; three distinct objectives with very different achievable guarantees: (1) maximize satisfied constraints (an $\alpha$-approximation for OPT constraints, meaningful even on far-from-satisfiable instances), (2) satisfy $1-f(\varepsilon)$ fraction given $(1-\varepsilon)$-satisfiability with $f\to0$ as $\varepsilon\to0$ (meaningful mainly for near-satisfiable instances), (3) minimize unsatisfied-constraint fraction, satisfying $\ge1-\alpha\varepsilon$ given $(1-\varepsilon)$-satisfiability with $\alpha$ possibly depending on $n$ — illustrated via Max-2-Lin(2), where the three objectives yield genuinely incomparable guarantees (0.87856-approximation vs. $1-O(\sqrt\varepsilon)$-satisfaction vs. $O(\sqrt{\log n})$-approximation for minimization), each best suited to a different regime of $\varepsilon$. : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **SDP techniques for Boolean 2-CSPs** — encoding $x_i$ as a unit vector $\bar u_i$ (intended: $\bar v_0$ if true, $-\bar v_0$ if false); the SDP objective as a sum of per-constraint contributions expressed via inner products $\langle\bar u_i,\bar u_j\rangle,\langle\bar u_i,\bar v_0\rangle$; randomized rounding via a random origin-symmetric partition of the unit sphere, assigning $x_i$ by which side $\bar u_i$ falls on; the approximation-guarantee proof reducing to bounding how the random partition separates pairs of vectors by their angles.
- **SDP techniques for non-Boolean 2-CSPs** — $d$ SDP vectors $\bar u_{i1},\dots,\bar u_{id}$ per variable (intended: $\bar v_0$ for the true label, $0$ otherwise), with orthogonality and sum-to-$\bar v_0$ constraints interpretable as a probability distribution over labels; the added rounding difficulty (no simple partition scheme picks exactly one of $d>2$ orthogonal vectors) resolved via an iterative rounding procedure that assigns a variable only when a random subset $A$ contains exactly one of its label-vectors, repeating on unassigned variables — reducing the analysis to pairwise conditional probabilities $\Pr(\bar u_{i_2j_2}\in A\mid\bar u_{i_1j_1}\in A)$.
- **SDP techniques for arity-$k>2$ CSPs** — additional per-constraint, per-satisfying-tuple SDP vectors $\bar v_{(i_1,j_1),\dots,(i_k,j_k)}$; the added challenge of analyzing the joint spatial configuration of all $dk$ label vectors plus the constraint vector, illustrated by Max-$k$-And.
- **Metric embedding techniques** (mentioned, not detailed) — used for Min UnCut, Min 2CNF Deletion, and Unique Games (all minimization objectives).
- **1.1 Overview of known results** — a survey table/discussion of approximation results across CSP types (continues in subsequent sections, not detailed here).

**Key Questions:**
1. Why do the three approximation objectives (maximize satisfied, satisfy near-all given near-satisfiability, minimize unsatisfied given near-satisfiability) require fundamentally different — and often incomparable — algorithms and guarantees, as the Max-2-Lin(2) example shows?
2. Why does rounding an SDP solution become qualitatively harder when moving from Boolean 2-CSPs (pick a side of a random hyperplane) to non-Boolean 2-CSPs with domain size $d>2$ (no simple random subset selects exactly one of $d$ orthogonal vectors), and how does the iterative "leave unassigned and repeat" procedure work around this?
3. What role does the per-constraint, per-satisfying-tuple vector $\bar v_{(i_1,j_1),\dots,(i_k,j_k)}$ play in the arity-$k>2$ SDP relaxation that the simpler per-label vectors $\bar u_{ij}$ alone cannot capture?

---
### Chapter 12: Quantified Constraints in Twenty Seventeen (pp. 327–346)

**Summary:** Surveys the Quantified Constraint Satisfaction Problem (QCSP) — the logical generalization of CSP restoring the universal quantifier to primitive positive logic — covering classical complexity classifications, parameterized complexity, and algorithms/proof theories for non-Boolean QCSPs, framed as a harder and less "clean" but still algebraically tractable cousin of CSP.

**Key Definitions & Concepts by Section:**
- **1. Introduction** — QCSP as CSP's "dissolute younger brother": its algebraic theory is less clean because surjective operations are not closed under composition; the fully-relativized ("list"/conservative) variant of QCSP is fully classified; Boolean QCSP is essentially QBF (out of scope, covered elsewhere); the chapter targets genuinely non-Boolean, non-relativized QCSP, a niche mostly of theoretical interest whose classifications nonetheless mix combinatorial and algebraic techniques; a classification of QCSP complexity would embed a classification of CSP complexity (since CSP is a QCSP special case with no universal quantifiers). : [[CSP-over-Infinite-and-Numeric-Domains|Link]]
- **2. Preliminaries** — constraint language as a relational structure $\mathbf{B}$; primitive positive (pp) logic ($\exists,\wedge,=$) for CSP vs. positive conjunctive logic ($\forall$ restored) for QCSP, called by many names in the literature (positive Horn, quantified conjunctive-positive, etc.); $\mathrm{QCSP}(\mathbf{B})$: does sentence $\varphi$ hold on $\mathbf{B}$; uniform QCSP (input is the pair $(\varphi,\mathbf{B})$) vs. non-uniform $\mathrm{QCSP}(\mathbf{B})$ (right-hand restriction) vs. left-hand restrictions (limiting $\varphi$'s form); the quantifier-alternation hierarchy $\Pi_{2k}$ (prenex, starting universal, at most $2k-1$ alternations) and $\Pi_{2k}\text{-}\mathrm{CSP}(\mathbf{B})$; homomorphism, endomorphism, core (all endomorphisms are automorphisms); CSP $\equiv$ homomorphism problem via the canonical-query/canonical-database correspondence; polymorphism $f$ preserving relation $R$; $\mathrm{Pol}(\mathbf{B})$ as a clone; surjective polymorphisms $s\mathrm{Pol}(\mathbf{B})$ and the surjective-restricted clone $s(\langle A\rangle)$; the two parallel Galois correspondences — $\mathrm{Inv}(\mathrm{Pol}(\mathbf{B}))=\langle\mathbf{B}\rangle_{pp}$ for CSP and $\mathrm{Inv}(s\mathrm{Pol}(\mathbf{B}))=\langle\mathbf{B}\rangle_{pc}$ for QCSP, the latter showing positive conjunctive logic on finite structures collapses to its $\Pi_2$ fragment; consequence: $\mathrm{Pol}(\mathbf{B})\subseteq\mathrm{Pol}(\mathbf{B}')\Rightarrow\mathrm{CSP}(\mathbf{B}')\le_{\log}\mathrm{CSP}(\mathbf{B})$, and similarly for $s\mathrm{Pol}$ and QCSP; $\mathrm{CSP}(\mathbf{B})\in$ NP, $\Pi_{2k}\text{-}\mathrm{CSP}(\mathbf{B})\in\Pi_{2k}^P$, $\mathrm{QCSP}(\mathbf{B})\in$ PSPACE for finite $\mathbf{B}$.
- **2.1 More algebra** — idempotent, majority, Mal'tsev, semilattice (and 2-semilattice), set operations; idempotent-trivial algebras/languages (only projections are idempotent); near-unanimity and weak near-unanimity (WNU) operations generalizing majority; the Taylor operation (a system of mixed-variable identities), with WNU as a special case; a generating-function invariant $f_A(n)$ (minimal generating-set size of $A^n$) and the "g-GP" (generating-polynomial-bound) property. : [[Absorption-Theory|Link]]
- **4–6 (by known structure)** — classical complexity classifications for QCSP (the chapter's Section 4); parameterized complexity of QCSPs (Section 5); new algorithms and proof theories for QCSP evaluation (Section 6).

**Key Questions:**
1. Why does the algebraic theory of QCSP have to work with *surjective* polymorphisms rather than all polymorphisms, and why does the resulting failure of closure under composition make QCSP's algebraic objects, in the chapter's words, "unwieldy" compared to CSP's clones?
2. How does the pair of Galois correspondences ($\mathrm{Inv}(\mathrm{Pol}(\mathbf{B}))=\langle\mathbf{B}\rangle_{pp}$ vs. $\mathrm{Inv}(s\mathrm{Pol}(\mathbf{B}))=\langle\mathbf{B}\rangle_{pc}$) explain why CSP and QCSP complexity are each controlled by a different notion of "the polymorphisms that matter," and what does the resulting collapse of positive conjunctive logic to its $\Pi_2$ fragment tell us about the expressive richness QCSP actually adds over CSP on finite structures?
3. Why does the chapter claim a full complexity classification of QCSP would be "more important" than one for CSP, given that QCSP has comparatively few real applications outside the Boolean (QBF) case?

---
