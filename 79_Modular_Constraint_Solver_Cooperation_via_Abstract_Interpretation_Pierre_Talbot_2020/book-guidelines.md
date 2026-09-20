# Modular Constraint Solver Cooperation via Abstract Interpretation — Guidelines

## Header

**Title:** Modular Constraint Solver Cooperation via Abstract Interpretation
**Author(s):** Pierre Talbot, Éric Monfroy, Charlotte Truchet
**Publication:** Theory and Practice of Logic Programming (TPLP), submitted 2020 (17-page research paper)

**Brief Summary:**
This paper reformulates constraint solver cooperation as a problem of combining abstract domains under abstract interpretation. It argues that existing cooperation schemes (e.g. SMT's Nelson-Oppen) hard-wire the cooperation strategy into the solver, and proposes instead a modular framework in which both solvers and cooperation schemes are first-class, composable "domain transformers." Two novel domain transformers are introduced — the interval propagators completion (IPC), which lets abstract domains exchange bound constraints, and the delayed product (DP), which lets one domain incrementally hand off (over-approximated) constraints to a more specialized domain once variables become sufficiently instantiated — plus the shared product, a mechanism for combining domain transformers that share underlying abstract domains without duplicating state. The framework is validated on the flexible job shop scheduling problem using the AbSolute solver.

**Intent of the Author:**
The authors want to show that abstract interpretation is not just a static-analysis technique but a genuine unifying theory for constraint solver cooperation, expressive enough to also capture *operational* aspects of solving (like delayed goals from logic programming), and that this theory translates almost directly into a modular, extensible implementation (via OCaml functors) rather than remaining a purely mathematical abstraction.

---

## Topic List

1. **Abstract Interpretation as a Foundation for Constraint Solving** : [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link]]
   - Concrete domain vs abstract domain vs syntax (the $\Phi$, $D^\flat$, $D^\sharp$ triangle)
   - Concretization function $\gamma$ and the abstraction relationship
   - Under-approximation vs over-approximation of solution sets : [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link]]
   - Soundness of an abstract computation w.r.t. the concrete semantics

2. **Abstract Domains for Constraint Programming** : [[Abstract-Domains-For-Constraint-Programming|Link]]
   - Lattice-based definition of an abstract domain (bottom, top, join) : [[Abstract-Domains-For-Constraint-Programming|Link]]
   - The state function and Kleene logic (true, false, unknown)
   - The interpretation function mapping formulas into an abstract domain : [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link]]
   - Closure as an extensive fixpoint operator eliminating inconsistent values
   - Split as branching/case division of an abstract element
   - The generic propagate-and-search solving algorithm : [[Abstract-Domains-For-Constraint-Programming|Link1]], [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link2]]
   - The box abstract domain over interval lattices : [[Abstract-Domains-For-Constraint-Programming|Link1]], [[Domain-Transformers|Link2]]
   - The octagon abstract domain and difference-bound matrices : [[Abstract-Domains-For-Constraint-Programming|Link1]], [[Domain-Transformers|Link2]]
   - Complexity of closure operators (Floyd-Warshall, incremental variants)

3. **Domain Transformers** : [[Domain-Transformers|Link]]
   - Domain transformers as functors constructing new abstract domains from existing ones
   - Logic completion for adding logical connectors to a constraint language
   - Direct product and coordinatewise combination of abstract domains
   - Formula annotation to route sub-formulas to specific product components
   - Limitation of the direct product: no information exchange between components

4. **Interval Propagators Completion (IPC)** : [[Interval-Propagators-Completion-IPC|Link]]
   - Propagators as extensive, sound functions implementing a single constraint : [[Interval-Propagators-Completion-IPC|Link]]
   - The projection function mapping abstract elements to variable intervals
   - The embed function to avoid spuriously adding variables to unrelated domains
   - Propagator completion as pairing an abstract domain with a set of propagators
   - Soundness of IPC over a direct product of over-approximating domains

5. **Delayed Product (DP)** : [[Delayed-Product-DP|Link]]
   - Delayed goals in logic programming as the inspiration for the delayed product : [[Delayed-Product-DP|Link]]
   - Variable instantiation and constraint rewriting under a fixed value
   - Transferring a constraint from a general domain to a more efficient specialized domain
   - Over-approximated early transfer before full instantiation : [[Delayed-Product-DP|Link]]
   - Partial vs full transfer of a constraint between domains

6. **Shared Product and Modular Composition** : [[Shared-Product-and-Modular-Composition|Link]]
   - Motivation: sharing vs duplicating underlying abstract domains across transformers
   - Named abstract domain declarations and dependencies : [[Domain-Transformers|Link1]], [[Abstract-Domains-For-Constraint-Programming|Link2]], [[Shared-Product-and-Modular-Composition|Link3]]
   - Projection and join functions for dependencies ($\pi$ and $\kappa$)
   - The reduction operator interleaved with closure
   - Fixed-point merging of shared components and the Knaster-Tarski theorem
   - Pointer-based implementation of sharing

7. **Case Study: Flexible Job Shop Scheduling** : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Job shop scheduling as an NP-hard combinatorial problem : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Precedence, non-overlap, and machine-alternative constraints
   - Flexible job shop as a generalization with decision variables for machine assignment : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Crafting abstract domains (FJS1, FJS2) by distributing constraints across components : [[Case-Study-Flexible-Job-Shop-Scheduling|Link]]
   - Static vs dynamic dispatch of constraints via the delayed product

8. **Implementation and Empirical Evaluation** : [[Implementation-and-Empirical-Evaluation|Link]]
   - The AbSolute solver implemented in OCaml using functors
   - Comparison against GeCode and Chuffed on scheduling benchmarks
   - The dms (domain-min-size / first-fail) search strategy
   - Interpreting $\Delta LB$ bound-quality results across edata and rdata instance sets
   - Trade-offs between cooperation granularity and solving efficiency

9. **Relation to Other Cooperation Frameworks** : [[Relation-to-Other-Cooperation-Frameworks|Link]]
   - Nelson-Oppen theory combination in SMT as a reduced product : [[Relation-to-Other-Cooperation-Frameworks|Link]]
   - Abstract conflict driven clause learning (ACDCL) as fixpoint computation over abstract domains
   - Constraint logic programming (CLP) bridges between uninterpreted-function and arithmetic domains
   - Lazy clause generation as a SAT/propagation hybrid cooperation scheme : [[Relation-to-Other-Cooperation-Frameworks|Link]]

---

## Chapter Summaries

### Chapter 1: Introduction (pp. 1–3)

**Summary:** Motivates the need for constraint solver cooperation when a problem mixes constraint types no single solver handles efficiently, surveys existing cooperation approaches (SMT/Nelson-Oppen, lazy clause generation, black-box combination, CLP), and states the paper's core move: model cooperation schemes themselves as abstract domain combinations (domain transformers), introducing IPC, the delayed product, and the shared product.

**Key Definitions & Concepts:**
- Constraint solver cooperation — combining specialized solvers to handle problems spanning multiple constraint languages
- Nelson-Oppen scheme — the fixed theory-combination method underlying most SMT solvers
- Lazy clause generation — hybrid SAT/propagation cooperation, state of the art for many scheduling problems
- Domain transformer — a functor constructing an abstract domain from one or more abstract domains (the paper's central organizing device)
- Black box approach — combining solvers without modifying their internals

**Key Questions:**
1. Why does the paper claim that SMT and CLP cooperation schemes are less "modular" than the framework proposed here?
2. In what sense does viewing cooperation schemes as abstract domain combinations change what counts as a "solver" versus a "cooperation scheme"?

---

### Chapter 2: Abstract Interpretation for Constraint Programming (pp. 3–7)

**Summary:** Introduces the formal machinery reused throughout the paper: the concrete domain (powerset lattice of CSP solutions), the definition of an abstract domain for constraint programming (Definition 1) with its required operations, the generic propagate-and-search `solve` algorithm, and two concrete instances — boxes and octagons — plus the first domain transformer, logic completion, and the direct product for combining domains. : [[Abstract-Domains-For-Constraint-Programming|Link1]], [[Abstract-Interpretation-as-a-Foundation-for-Constraint-Solving|Link2]]

**Key Definitions & Concepts:**
- **Concrete domain** — the powerset lattice $D^\flat = \langle \mathcal{P}(D), \supseteq \rangle$ of CSP solution sets, ordered by inclusion
- **Abstract domain (Def. 1)** — a lattice $\langle A, \leq \rangle$ with $\bot$, $\top$, join $\sqcup$, concretization $\gamma$, `state` (Kleene true/false/unknown), interpretation $\llbracket \cdot \rrbracket$, `closure`, and `split`
- **Under-/over-approximation** — $\gamma(a) \subseteq \llbracket\varphi\rrbracket^\flat$ (under) vs $\gamma(a) \supseteq \llbracket\varphi\rrbracket^\flat$ (over)
- **`solve` algorithm** — closure then, on `unknown` state, split and recurse; the standard propagate-and-search pattern
- **Box abstract domain** $B$ — partial functions from variables to intervals; supports $x \leq b, x \geq b, x = b$; closure is the identity since interpretation is already exact
- **Octagon abstract domain** $O$ (Miné 2006) — supports $\pm x \pm y \leq c$; represented as a difference-bound matrix; closure via Floyd-Warshall, $O(n^3)$ general / $O(n^2)$ incremental
- **Logic completion** $L(A)$ — a domain transformer adding logical connectors (e.g. disjunction) over $A$'s constraint language
- **Direct product (Def. 2)** — coordinatewise combination $A_1 \times \dots \times A_n$; formula annotation $\varphi{:}i$ routes a sub-formula to component $i$

**Key Questions:**
1. Why is `closure` the identity function for boxes but a nontrivial Floyd-Warshall computation for octagons — what property of boxes' interpretation function explains this?
2. What specific limitation of the direct product motivates everything introduced in Chapter 3 (IPC and the delayed product)?
3. Why does the abstract domain definition include both a `state` function and a `closure` function rather than folding satisfiability checking into closure alone?

---

### Chapter 3: Domain Transformers for Cooperation Schemes (pp. 7–14)

**Summary:** The technical core of the paper. Introduces the interval propagators completion (IPC), which equips any abstract domain with sound bound-propagation exchanged via a shared interval projection; the delayed product (DP), which delays interpreting a constraint in an expressive-but-slow domain until instantiation lets it be rewritten into a cheaper domain's language; and the shared product, which lets multiple domain transformers reference the same underlying abstract domain without duplicating or losing synchronization of its state. : [[Domain-Transformers|Link]]

**Key Definitions & Concepts by Section:**
- **3.1 Interval propagators completion** — `project : (A × V) → I` (over-approximates a variable's interval in $a$); propagator $p : A \to A$ (extensive, sound function implementing one constraint); `embed` function (prevents a propagator from spuriously introducing unrelated variables into a domain); $IPC(A) = \langle A \times Pr, \leq \rangle$ pairing an abstract domain with a propagator set; Lemma 3 (IPC over a direct product of over-approximating domains is itself sound) : [[Interval-Propagators-Completion-IPC|Link]]
- **3.2 Delayed product** — `fix(a, x)` (variable $x$ is instantiated in $a$); rewriting function $\varphi \to_a \varphi'$ substituting instantiated variables; $FT = [\Phi \rightharpoonup Bool]$ (transfer-status lattice tracking which formulas have moved to the target domain); $DP(A_1, A_2)$ construction and its `closure_one` transfer rule; Lemma 4 and the $\rightsquigarrow$ over-approximating rewrite (transfers a constraint early via its bound, before full instantiation) : [[Case-Study-Flexible-Job-Shop-Scheduling|Link1]], [[Delayed-Product-DP|Link2]]
- **3.3 Combining domain transformers** — the sharing problem when two transformers each wrap their own copy of the same underlying domain; **shared product (Def. 5)** — named abstract domain declarations with explicit dependencies; projection $\pi$ and join $\kappa$ functions per component; reduction operator $\rho_i$ interleaved with closure; fixed point of $\rho_1 \circ \dots \circ \rho_n$ as the least fixed point (Knaster-Tarski) merging shared state; pointer-based implementation of sharing in practice : [[Domain-Transformers|Link]]

**Key Questions:**
1. Why must the `embed` function check `vars(a2) ⊆ vars(a1)` before joining — what would go wrong in the propagator $p_{\geq}$ example without it?
2. In the delayed product, what is the practical difference between a constraint being fully transferred ($\varphi \mapsto true$) versus partially transferred via the over-approximating rewrite ($\rightsquigarrow$)?
3. Why does the shared product need a *fixed point* of the reduction operator $\rho$ rather than a single pass — what could be left inconsistent after only one application of $\rho_1 \circ \dots \circ \rho_n$?
4. How does the shared product's dependency mechanism let two octagon elements be kept separate (for complexity reasons) while two box-based transformers share the same box?

---

### Chapter 4: Case Study and Evaluation (pp. 14–17)

**Summary:** Applies the framework to the flexible job shop scheduling problem: precedence, non-overlap, and machine-alternative constraints are distributed across boxes, octagons, IPC, and the delayed product to build two abstract domains, FJS1 (static dispatch) and FJS2 (dynamic dispatch via the delayed product PREC domain). Both are implemented in the AbSolute solver (OCaml, functor-based) and benchmarked against GeCode and Chuffed on the edata/rdata instance sets. : [[Case-Study-Flexible-Job-Shop-Scheduling|Link1]], [[Delayed-Product-DP|Link2]]

**Key Definitions & Concepts:**
- Flexible job shop scheduling — generalization of job shop scheduling where each task can run on a set of candidate machines with machine-dependent durations
- Precedence constraints, non-overlap (disjunctive) constraints, machine-alternative constraints (Eqs. 1, 2, 4) and the makespan objective (Eq. 3)
- **FJS1** — $L(IPC(B \times O))$-based domain with statically distributed constraints between box and octagon components
- **FJS2** — uses $PREC = DP(IPC(B \times O), O)$ to dynamically move precedence constraints into octagons once durations are fixed during search
- AbSolute — the OCaml constraint solver implementing these domains via functors, benchmarked against GeCode and Chuffed
- $\Delta LB$ — percentage gap from the best known lower bound, the paper's efficiency/quality metric
- `dms` search strategy — domain-min-size / first-fail variable selection, fixing durations before machines before start dates

**Key Questions:**
1. Why does FJS2's dynamic dispatch via the delayed product yield only a modest improvement over FJS1's static dispatch under the `dms` search strategy specifically — what property of `dms` limits the benefit?
2. What does AbSolute's relatively worse performance on rdata (versus edata) reveal about the cost of *not* having a dedicated global constraint for machine assignment?

---

### Chapter 5: Conclusion and Future Work (p. 17)

**Summary:** Summarizes the contributions (IPC, delayed product, shared product as a unifying modular framework for solver cooperation) and outlines three future directions: incorporating conflict-driven learning (à la ACDCL/lazy clause generation) into AbSolute, automatically inferring which abstract domain should interpret a given formula, and integrating customizable search strategies via spacetime programming.

**Key Definitions & Concepts:**
- ACDCL (abstract conflict driven clause learning) as a target for future integration of conflict learning into the framework
- Automatic abstract-domain inference — an open problem balancing expressiveness against efficiency when a formula fits multiple domains
- Spacetime programming (Talbot 2019) — a synchronous, concurrent search-strategy language over lattices, proposed as the vehicle for integrating flexible search into this framework

**Key Questions:**
1. Why do the authors single out conflict learning (ACDCL-style) as the most important gap in AbSolute's efficiency, given the rest of the paper's focus on cooperation rather than search?

---

### Appendix A: FJS1 in AbSolute (p. 17)

**Summary:** Shows the OCaml functor code that realizes FJS1's abstract domain composition, demonstrating that the paper's mathematical constructions (direct product, propagator completion, logic completion, shared product) map almost one-to-one onto implementation-level module composition.

**Key Definitions & Concepts:**
- `Direct_product`, `Propagator_completion`, `Logic_completion`, `Shared_product` — OCaml functors directly mirroring the paper's domain transformer definitions
- Variable domain parameter of `Propagator_completion` — determines the numeric domain (integer, float, rational) in which propagation is evaluated when component domains differ

**Key Questions:**
1. What does the near-direct correspondence between the paper's mathematical definitions and these functor signatures suggest about the design goal of keeping the implementation "close to the theory"?
