# Abstract Domains in Constraint Programming — Guidelines

## Header

**Title:** Abstract Domains in Constraint Programming
**Author(s):** Marie Pelleau
**Publication:** ISTE / Wiley, February 15, 2015 (published PhD thesis)

**Brief Summary:**
This book sits at the interface of Constraint Programming (CP) and Abstract Interpretation (AI), two research areas that both aim to compute over-approximations of hard or undecidable spaces — solution sets in CP, program semantics in AI. Its central thesis is that CP's rigid, Cartesian-only domain representations (boxes over integers or reals) can be replaced by AI's richer notion of abstract domains, yielding a single, uniform solving method that no longer depends on the variable type (discrete or continuous) or on the shape of the domain representation. The book develops this idea in two complementary directions: first, importing AI's abstract domains into CP (illustrated concretely with the octagon abstract domain and an octagonal solver built on Ibex), and second, going the opposite way and re-expressing CP's own solving process entirely in AI terms, culminating in a prototype abstract solver, AbSolute, built on the Apron abstract-domain library.

**Intent of the Author:**
Pelleau's stated aim is to design new CP solving techniques capable of uniformly handling mixed problems (both integer and real variables) and non-Cartesian domain shapes, by systematically cross-pollinating AI's theory of abstract domains with CP's propagation-and-search solving machinery — something neither field had a native way to do on its own.

---

## Topic List

1. **Abstract Interpretation Foundations** : [[Abstract-Interpretation-Foundations|Link]]
   - Posets lattices and complete lattices : [[Abstract-Interpretation-Foundations|Link1]], [[The-Octagon-Abstract-Domain|Link2]]
   - Galois connections between concrete and abstract domains : [[The-Octagon-Abstract-Domain_alt|Link1]], [[Abstract-Interpretation-Foundations|Link2]]
   - Concrete versus abstract semantics : [[Abstract-Interpretation-Foundations|Link]]
   - Transfer functions for program instructions : [[Abstract-Interpretation-Foundations|Link]]
   - Fixpoints and iterative computation schemes : [[Abstract-Interpretation-Foundations|Link]]
   - Jacobi and Gauss-Seidel iteration strategies
   - Widening operators for accelerating fixpoint convergence
   - Narrowing operators for refining over-approximations : [[Abstract-Interpretation-Foundations|Link]]
   - Local iterations and lower closure operators : [[Abstract-Interpretation-Foundations|Link]]
   - Static program analysis and runtime error proving

2. **Abstract Domains in Abstract Interpretation** : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - Non-relational relational and weakly relational domain families : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - The intervals abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]
   - The polyhedra abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - The ellipsoids abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - The octahedra and zonotopes abstract domains : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - Required operators of an abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link]]
   - Disjunctive completion : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link2]]
   - Reduced products and domain combination : [[Abstract-Domains-in-Abstract-Interpretation|Link]]

3. **Constraint Satisfaction Problem Foundations** : [[Constraint-Satisfaction-Problem-Foundations|Link]]
   - Definition of a constraint satisfaction problem : [[Constraint-Satisfaction-Problem-Foundations|Link]]
   - Discrete versus continuous domains : [[Constraint-Satisfaction-Problem-Foundations|Link1]], [[Exploration-and-Search-in-Constraint-Programming|Link2]]
   - Domain representations as integer Cartesian products integer boxes and boxes : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Interval arithmetic for continuous constraints : [[Constraint-Satisfaction-Problem-Foundations|Link1]], [[The-AbSolute-Solver|Link2]], [[Consistency-and-Propagation-in-Constraint-Programming|Link3]]
   - True false and maybe constraint evaluation
   - Soundness and completeness of approximations : [[Constraint-Satisfaction-Problem-Foundations|Link]]
   - Over-approximation and under-approximation : [[Constraint-Satisfaction-Problem-Foundations|Link]]

4. **Consistency and Propagation in Constraint Programming** : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Support for a value with respect to a constraint : [[Octagonal-Constraint-Solving|Link]]
   - Generalized arc-consistency : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Bound-consistency : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Hull-consistency : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - The HC4-Revise propagation algorithm : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Propagators and the propagation loop : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
   - Arc-consistency algorithm family AC1 through AC2001
   - Complexity of consistency algorithms

5. **Exploration and Search in Constraint Programming** : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Choice points and the search tree : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Backtracking and backjumping : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Variable choice heuristics including first-fail and dom over wdeg : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Value choice heuristics : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Domain splitting heuristics for continuous variables : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Discrete versus continuous resolution schemes : [[Exploration-and-Search-in-Constraint-Programming|Link]]
   - Solving mixed discrete-continuous problems : [[Exploration-and-Search-in-Constraint-Programming|Link]]

6. **Links Between Abstract Interpretation and Constraint Programming** : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Shared lattice and fixpoint theoretical framework : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Consistency as a form of narrowing : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Differences in accuracy and completeness philosophy : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Differences in domain representation richness : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
   - Connections to satisfiability solving : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]

7. **Unified Abstract Domains for Constraint Programming** : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - E-consistency as a generalization of existing consistencies
   - The generic splitting operator : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - Formal definition of an abstract domain for constraint programming : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - The unified abstract solving algorithm : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - Termination and completeness conditions for the unified solver : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]
   - Recovering classical CP solvers as instances of the unified framework : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]

8. **The Octagon Abstract Domain** : [[The-Octagon-Abstract-Domain|Link]]
   - Octagonal constraints and their geometric shape : [[The-Octagon-Abstract-Domain_alt|Link]]
   - Closure of octagons under intersection : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The difference bound matrix representation : [[The-Octagon-Abstract-Domain|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]
   - The modified Floyd-Warshall algorithm for octagons : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The intersection of boxes representation : [[The-Octagon-Abstract-Domain|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]
   - Rotated bases and rotated variables : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The octagonal splitting operator : [[The-Octagon-Abstract-Domain_alt|Link]]
   - The octagonal precision function : [[The-Octagon-Abstract-Domain_alt|Link]]
   - Partial octagons : [[The-Octagon-Abstract-Domain|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]

9. **Octagonal Constraint Solving** : [[Octagonal-Constraint-Solving|Link]]
   - Construction of an octagonal CSP from a CSP : [[Octagonal-Constraint-Solving|Link]]
   - Rotated constraints : [[Octagonal-Constraint-Solving|Link]]
   - Oct-consistency : [[Octagonal-Constraint-Solving|Link]]
   - The combined propagation scheme for octagonal and rotated constraints
   - Variable choice heuristics LargestFirst LargestCanFirst LargestOctFirst and Oct-Split
   - Octagonalization heuristics ConstraintBased Random StrongestLink and Promising
   - Experimental comparison of octagons versus intervals on continuous benchmarks : [[Octagonal-Constraint-Solving|Link]]

10. **Abstract Interpretation Reformulation of Constraint Programming** : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - Constraint solving as concrete semantics : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - CP domain representations recast as abstract domains : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - The disjunctive completion of an abstract domain : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[The-Octagon-Abstract-Domain|Link2]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link3]], [[The-Octagon-Abstract-Domain_alt|Link4]]
    - The split operator and the choice operator : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
    - Compatibility of the precision function and the splitting operator : [[The-Octagon-Abstract-Domain|Link1]], [[The-AbSolute-Solver|Link2]], [[The-Octagon-Abstract-Domain_alt|Link3]]
    - The generic abstract solving algorithm and its termination proof : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]

11. **The AbSolute Solver** : [[The-AbSolute-Solver|Link]]
    - Implementation on top of the Apron abstract domain library : [[The-AbSolute-Solver|Link]]
    - Problem modelization with mixed integer and real environments : [[The-AbSolute-Solver|Link]]
    - Abstraction and consistency via Apron transfer functions : [[The-AbSolute-Solver|Link]]
    - Linearization of non-linear constraints : [[The-AbSolute-Solver|Link]]
    - The naive splitting operator : [[The-AbSolute-Solver|Link]]
    - Handling the polyhedron abstract domain in practice : [[The-AbSolute-Solver|Link]]
    - Experimental results on continuous and mixed benchmarks : [[The-AbSolute-Solver|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 15–19)

**Summary:** Introduces Constraint Programming and Abstract Interpretation as two research areas that independently developed methods for over-approximating hard or undecidable spaces, and motivates bringing AI's abstract domains into CP to obtain a uniform solving method for both discrete and continuous (and mixed) problems, while also introducing the octagon domain and the AbSolute solver as the book's two main contributions.

**Key Definitions & Concepts:**
- Constraint Programming (CP) — declarative formalism solving combinatorial problems via constraints over discrete or continuous variables, using consistency and propagation for Cartesian over-approximations.
- Abstract Interpretation (AI) — theory of semantic approximation used to prove program properties by computing an over-approximation of a program's concrete semantics using non-Cartesian shapes (octagons, ellipsoids, etc.).
- Mixed problem — a problem containing both integer and real variables, historically handled only through ad hoc transformations in CP.
- Book's twofold contribution — (1) redefining CP tools using AI's abstract domains, illustrated with the octagon domain and an Ibex-based octagonal solver; (2) redefining CP itself as an abstract operation in AI, yielding the AbSolute solver over Apron.

**Key Questions:**
1. Why do CP and AI, despite differing goals (solving vs. program verification), share a common technical need for over-approximation?
2. What specific limitation of CP (regarding variable types and domain shapes) does the book aim to remove?

---

### Chapter 2: State of the Art (pp. 21–61)

**Summary:** Surveys the theoretical foundations of both Abstract Interpretation (lattices, Galois connections, transfer functions, fixpoints, widening/narrowing, abstract domain taxonomy) and Constraint Programming (CSP definition, domain representations, consistency notions, propagation, exploration, resolution schemes, heuristics), then closes with a synthesis identifying deep similarities (shared lattice/fixpoint framework) and differences (finite vs. infinite lattices, decreasing vs. possibly increasing approximations, implicit vs. explicit precision) between the two fields.

**Key Definitions & Concepts by Section:**
- **2.1 Abstract Interpretation** — Poset (reflexive, antisymmetric, transitive relation), lattice (pair has lub/glb), complete lattice, Galois connection $D_1 \leftrightarrows D_2$ via abstraction $\alpha$ and concretization $\gamma$, concrete domain $D^\flat$ vs. abstract domain $D^\sharp$, transfer function $\{|C|\}$, fixpoint ($\mathrm{lfp}$, $\mathrm{gfp}$), Jacobi vs. Gauss-Seidel iteration, widening operator $\triangledown^\sharp$ (ensures termination on infinite chains), narrowing operator $\triangle^\sharp$ (refines after widening), lower closure operator $\rho$ (monotonic, reductive, idempotent) and local iterations, non-relational/relational/weakly-relational abstract domain families (intervals, octagons, polyhedra, ellipsoids), required abstract-domain operators (concretization/abstraction, $\bot^\sharp$/$\top^\sharp$, transfer functions, meet/join, widening, narrowing). : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[Abstract-Interpretation-Foundations|Link2]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link3]], [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link4]]
- **2.2 Constraint Programming** — Constraint Satisfaction Problem (CSP) with variables, domains, and constraints; integer Cartesian product, integer box, and box domain representations; constraint answers true/false (discrete) or true/false/maybe (continuous, via interval arithmetic); approximation, soundness, and completeness; support, generalized arc-consistency (GAC), bound-consistency (BC), Hull-consistency (HC); the HC4-Revise propagator (tree-based, two-pass); propagation loop and propagator ordering independence; exploration via choice points, backtracking/backjumping; variable heuristics (first-fail, dom+deg, dom/deg, dom/wdeg) and value/splitting heuristics (largest-first, round-robin, Max-smear); handling mixed discrete/continuous problems via discretization or added integrity constraints. : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link1]], [[Consistency-and-Propagation-in-Constraint-Programming|Link2]], [[Exploration-and-Search-in-Constraint-Programming|Link3]], [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link4]]
- **2.3 Synthesis** — Shared lattice/fixpoint theoretical basis; consistency as a CP analogue of AI's narrowing; key differences: AI lattices are typically infinite vs. CP's always-finite lattices, CP approximations strictly decrease vs. AI's may increase (e.g., via widening on loops), CP pursues completeness through refinement vs. AI's acceptance of incompleteness, CP has explicit user-set precision vs. AI's implicit precision (determined by domain/operator choice).

**Key Questions:**
1. How do widening and narrowing operators trade off termination guarantees against precision, and why is narrowing far less studied than widening?
2. In what precise sense are GAC, BC, and HC each an instance of a general "smallest element of $E$ containing all solutions" pattern, and why does this pattern fail for polyhedra?
3. What conceptual differences between CP's and AI's treatment of completeness and precision explain why CP solvers are tied to a single domain representation while AI analyzers freely mix abstract domains?

---

### Chapter 3: Abstract Interpretation for the constraints (pp. 63–75)

**Summary:** Generalizes CP's consistency, splitting operator, and domain representation into unified, representation-independent definitions inspired by AI's abstract domains, and uses them to define a single abstract solving algorithm that recovers the classical discrete and continuous CP solvers as special cases while also allowing genuinely new, non-Cartesian domain representations. : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link1]], [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link2]]

**Key Definitions & Concepts by Section:**
- **3.2.1 Consistency and Fixpoint** — $E$-consistency: for constraint $C$, the least element of $E$ (a subset of $P(\hat{D})$ closed under intersection) containing all solutions $S_C$; propositions showing $S$-consistency = GAC, $IB$-consistency = BC, $B$-consistency = HC; $E$-consistency for a conjunction of constraints, and the resulting lattice of consistent elements. : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link]]
- **3.2.2 Splitting Operator** — Generic splitting operator $\oplus: E \to P(E)$ satisfying finiteness, coverage (no lost solutions), non-emptiness, and non-triviality conditions; shown to generalize both discrete instantiation and continuous interval splitting. : [[The-AbSolute-Solver|Link1]], [[The-Octagon-Abstract-Domain|Link2]], [[The-Octagon-Abstract-Domain_alt|Link3]], [[Unified-Abstract-Domains-for-Constraint-Programming|Link4]]
- **3.2.3 Abstract Domains** — Abstract Domain for Constraint Programming: a complete lattice $E$, a Galois connection $\gamma/\alpha$ to the search space, a computer-representable normal form, a sequence of splitting operators, and a monotonic size function $\tau$ with $\tau(e)=0 \iff e=\emptyset$. : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[Abstract-Interpretation-Foundations|Link2]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link3]], [[The-AbSolute-Solver|Link4]]
- **3.3 Unified Solving** — Algorithm 3.1: generic solve loop alternating $E$-consistency and splitting until elements are solutions or below precision $r$; termination/completeness proven under hypotheses (H1) $E$ closed by intersection, (H2) no infinite decreasing chain, (H3) $r \in \tau(E^f)$; classical integer, integer-box, and box-based solvers recovered as instances. : [[Unified-Abstract-Domains-for-Constraint-Programming|Link]]

**Key Questions:**
1. Why must the definition of $E$-consistency restrict to sets $E$ closed under intersection, and what breaks (concretely, for polyhedra) when this fails?
2. What do the four conditions on a splitting operator each individually guard against in the solving process (non-termination, lost solutions, wasted work, non-progress)?
3. How does defining abstract domains "for Constraint Programming" as a 5-tuple (lattice, Galois connection, normal form, splits, size function) let the book treat interval and integer solvers as two instances of one algorithm?

---

### Chapter 4: Octagons (pp. 77–90)

**Summary:** Defines the octagon abstract domain (points satisfying conjunctions of constraints of the form $\pm v_i \pm v_j \le c$) for Constraint Programming, giving two equivalent computer representations (a difference bound matrix and an intersection-of-rotated-boxes representation), and equips octagons with a splitting operator, a relation-aware precision function, and a Galois connection to boxes, thereby establishing octagons as a full abstract domain per Chapter 3's definition. : [[The-Octagon-Abstract-Domain_alt|Link]]

**Key Definitions & Concepts by Section:**
- **4.1 Definitions** — Octagonal constraint $\pm v_i \pm v_j \le c$; octagon as the set of points satisfying a conjunction of octagonal constraints; octagons closed under intersection ($O \cap O' = \{\pm v_i \pm v_j \le \min(c,c')\}$) but not under union (smallest enclosing octagon uses $\max$).
- **4.2 Representations** — Difference constraint $w - w' \le c$ and the difference bound matrix (DBM) encoding, via variable-splitting into positive/negative forms $w_{2i-1}, w_{2i}$; the modified Floyd-Warshall algorithm (Algorithm 4.1) computing the tightest DBM in $O(n^3)$; the rotated basis $B_\alpha^{i,j}$ (rotation by $\pi/4$) and the intersection-of-boxes representation, proven equivalent to the DBM representation (Proposition 4.2.1). : [[Links-Between-Abstract-Interpretation-and-Constraint-Programming|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]]
- **4.3 Abstract Domains Components** — Octagonal splitting operator $\oplus_o$ cutting along a variable in any basis, followed by a Floyd-Warshall repropagation; octagonal precision function $\tau_o(O) = \min_{i,j} \max_k (\overline{I_k^{i,j}} - \underline{I_k^{i,j}})$, capturing correlation between variables (Proposition 4.3.1: every point is within $\tau_o(O)$ of a solution). : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[Abstract-Interpretation-Foundations|Link2]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link3]], [[The-AbSolute-Solver|Link4]]
- **4.4 Abstract Domains** — Proof that octagons form a complete lattice $O$; Galois connection $O \leftrightarrows B$ between octagons and floating-point boxes; formal Octagon Abstract Domain definition; Partial Octagon (Definition 4.4.2), restricting the generated bases to index subsets $J, K$, to control the $O(n^2)$ basis blowup. : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[Abstract-Interpretation-Foundations|Link2]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link3]], [[The-AbSolute-Solver|Link4]]

**Key Questions:**
1. Why does representing an octagon via difference constraints on doubled variables $w_{2i-1}, w_{2i}$ let the Floyd-Warshall shortest-path algorithm serve as an optimal closure operator for octagonal constraints?
2. In what sense does the octagonal precision function $\tau_o$ capture information that a per-axis (non-relational) precision measure would miss?
3. Why are partial octagons introduced, and what tradeoff do they navigate between expressiveness and the $n(n+1)/2$ basis blowup of full octagons?

---

### Chapter 5: Octagonal Solving (pp. 91–110)

**Summary:** Builds a concrete octagonal solving method by translating a continuous CSP into an equivalent "octagonal CSP" with rotated variables and constraints, defining Oct-consistency and a combined propagation scheme interleaving Hull-consistency propagators with the modified Floyd-Warshall algorithm, then evaluates a prototype (built on Ibex) against classical interval solving on the Coconut benchmark using several variable-choice and octagonalization heuristics. : [[Octagonal-Constraint-Solving|Link]]

**Key Definitions & Concepts by Section:**
- **5.1 Octagonal CSP** — Rotated constraint $C^{i,j}$ obtained by substituting rotated-basis expressions for $v_i, v_j$; construction of the full octagonal CSP (original + rotated variables, constraints, domains, DBM); Proposition 5.1.1: the octagonal CSP's solution set restricted to original variables equals the original CSP's solution set. : [[Octagonal-Constraint-Solving|Link]]
- **5.2 Octagonal Consistency and Propagation** — Oct-consistency: the unique smallest octagon containing all solutions of a constraint (or constraint sequence); Proposition 5.2.2: Oct-consistent octagon = intersection of Hull-consistent boxes in every rotated basis; Algorithm 5.1, the propagation scheme interleaving initial/rotated-constraint propagators with the refined Floyd-Warshall algorithm, proven correct (Proposition 5.2.3) with time complexity $O(n^3+pn^2)$. : [[Octagonal-Constraint-Solving|Link1]], [[Consistency-and-Propagation-in-Constraint-Programming|Link2]]
- **5.3 Octagonal Solver** — Variable heuristics: LargestFirst (LF), LargestCanFirst (LCF, restricted to canonical-basis variables), LargestOctFirst (LOF, restricted to rotated variables), Oct-Split (OS, picks the tightest basis then its worst variable); octogonalization heuristics: ConstraintBased (CB), Random (R), StrongestLink (SL), Promising Scheme and Promising Heuristic (P, favoring expressions like $\pm v_i \pm v_j$ or $\pm v_i \times v_j$ that simplify nicely under rotation). : [[Octagonal-Constraint-Solving|Link1]], [[The-Octagon-Abstract-Domain_alt|Link2]], [[The-AbSolute-Solver|Link3]]
- **5.4 Experimental Results** — Implementation atop Ibex with HC4-Revise and Mathematica-based constraint simplification; Coconut benchmark methodology; results show octagons often find a first solution faster than intervals (closer approximation) but can be slower to find all solutions (multiple-occurrence blowup after rotation); Oct-Split usually the best variable heuristic; StrongestLink often the best octagonalization heuristic, contrary to the authors' expectation that Promising would win. : [[The-AbSolute-Solver|Link]]

**Key Questions:**
1. Why is a split-then-repropagate step (Floyd-Warshall) mandatory after the octagonal splitting operator, whereas ordinary interval splitting needs no such step?
2. What causes the paradox that octagons often reach a first solution faster than intervals but can be slower to enumerate all solutions?
3. Why did the StrongestLink octagonalization heuristic outperform the Promising heuristic, against the authors' own expectations, and what does that suggest about what actually drives octagonal propagation quality?

---

### Chapter 6: An Abstract Solver: AbSolute (pp. 111–131)

**Summary:** Reverses the direction of Chapters 3–5 by re-expressing Constraint Programming entirely within the Abstract Interpretation framework — treating CP domain representations as AI abstract domains, propagators as lower closure operators, and defining a novel split operator and choice operator (absent from classical AI) — culminating in AbSolute, a prototype solver built on the Apron abstract-domain library that natively handles integer, real, and mixed problems using intervals, octagons, or polyhedra. : [[The-AbSolute-Solver|Link]]

**Key Definitions & Concepts by Section:**
- **6.1.1 Concrete Solving as Concrete Semantics** — CSP solving recast as computing $S = \rho^\flat(\hat{D})$ where $\rho^\flat = \rho_1^\flat \circ \cdots \circ \rho_p^\flat$ is a composition of lower closure operators (propagators); solutions as the greatest fixpoint $\mathrm{gfp}_{\hat{D}}\, \rho^\flat$. : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link]]
- **6.1.2–6.1.3 Abstract Domains and Operators** — Integer Cartesian products $S^\sharp$, integer boxes $I^\sharp$, boxes $B^\sharp$, the octagon domain $O^\sharp$, the polyhedron domain $P^\sharp$ (no Galois connection; uses double-description with vertices/rays), and the mixed box domain $M^\sharp$, each given explicit Galois connections and monotonic size functions $\tau$.
- **6.1.4 Constraints and Consistency** — Perfect propagator semantics $\alpha \circ \rho^\flat \circ \gamma$; identification of CP propagation with Granger's local iterations, and of HC4-Revise with forward-backward abstract test transfer functions. : [[Consistency-and-Propagation-in-Constraint-Programming|Link]]
- **6.1.5 Disjunctive Completion and Split** — Disjunctive completion $E^\sharp = P_{\text{finite}}(D^\sharp)$ of pairwise-incomparable elements, ordered by the Smyth order $\sqsubseteq_E^\sharp$; Split Operator (Definition 6.1.5), a new AI construct (finite, contracting, exact under $\gamma$) instantiated for $S^\sharp, I^\sharp, B^\sharp, O^\sharp, P^\sharp, M^\sharp$; Choice Operator $\pi$ selecting an element above precision $r$; compatibility of $\tau$ and $\oplus$ ensuring termination. : [[Abstract-Domains-in-Abstract-Interpretation|Link1]], [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link2]]
- **6.1.6 Abstract Solving** — Algorithm 6.1, the generic abstract solver (pop, consistency, discard/keep/split); termination via König's lemma (Proposition 6.1.1) and correctness (Proposition 6.1.2). : [[Abstract-Interpretation-Reformulation-of-Constraint-Programming|Link1]], [[Unified-Abstract-Domains-for-Constraint-Programming|Link2]]
- **6.2 The AbSolute Solver** — OCaml implementation atop Apron; problem modelization via integer/real variable environments; abstraction via per-domain "managers"; consistency via bounded local iterations (default 3) with linearization of non-linear constraints for domains lacking native non-linear support; a domain-agnostic (naive, largest-dimension) splitting operator; a facet-count cap for the polyhedron domain to control blowup; experimental comparison on Coconut (continuous) and MinLPLib-derived (mixed) benchmarks showing AbSolute competitive with Ibex on inequalities but slower on equalities, and uniquely capable of solving genuinely mixed integer/real problems. : [[The-AbSolute-Solver|Link]]

**Key Questions:**
1. How does recasting CP propagators as AI lower closure operators let the authors reuse Granger's local-iteration theory to justify AbSolute's bounded (3-iteration) consistency loop?
2. Why does Abstract Interpretation need a genuinely new "split operator" and "choice operator" that have no classical AI counterpart, and what three conditions make a split operator sound?
3. What practical cost does AbSolute pay for propagating *all* constraints at each local iteration (rather than only those touched by the last change), and how does this explain its timeouts on problems like brent-10?

---

### Chapter 7: Conclusion and Perspectives (pp. 133–140)

**Summary:** Recaps the book's two complementary contributions — unifying CP's domain representations under an AI-style abstract-domain framework (illustrated by the octagon domain and its solver) and conversely re-expressing CP itself in AI terms (yielding AbSolute) — and lays out short-, medium-, and long-term research directions, including richer heuristics and reduced products for AbSolute, extending the framework to further AI domains like polyhedra and ellipsoids, and eventually connecting CP's under-approximations to AI's widening theory.

**Key Definitions & Concepts:**
- Recap of abstracting CP's domain notion into a solver parameter, enabling relational representations (e.g., polyhedra capturing linear relationships) within a variable-type-independent unified solving method.
- Recap of the octagon domain's optimal consistency (via adapted lower closure/Floyd-Warshall) and search guided by inter-variable relationships.
- Recap of recasting CP as AI (concrete domain = solution set) to directly reuse existing AI abstract domains via Apron, yielding AbSolute.
- Short-term perspectives — better heuristics, splitting operators, and propagation-loop tuning for AbSolute; reduced products between integer and real domains; real-world mixed-problem applications (e.g., post-disaster power-grid repair).
- Medium-term perspectives — extending the framework to interval polyhedra, zonotopes, ellipsoids, requiring new consistencies, splitting operators, and effective (quasi-)linearization for non-linear constraints.
- Long-term perspective — exploiting the link between CP's under-approximations and AI's widening operator to design inner-approximation solving methods.

**Key Questions:**
1. Why does the author view "redefine appropriate splitting operators and consistencies for each new domain" as the central obstacle blocking wider adoption of relational abstract domains in CP?
2. What is the significance of pursuing both directions (CP-into-AI and AI-into-CP) rather than settling on just one unifying framework?
