# Better Together: Unifying Datalog and Equality Saturation — Guidelines

## Header

**Title:** Better Together: Unifying Datalog and Equality Saturation
**Author(s):** Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker, Eli Rosenthal, Zachary Tatlock, Max Willsey
**Publication:** Proc. ACM Program. Lang. 7, PLDI, Article 125 (2023); also arXiv:2304.04332 [cs.PL]

**Brief Summary:**
This paper introduces egglog, a fixpoint reasoning system that unifies Datalog and equality saturation (EqSat) into a single language and implementation. It shows that EqSat's strengths (efficient congruence closure, e-matching, term extraction) and Datalog's strengths (composable semantic analyses, lattices, incremental semi-naïve evaluation) are complementary, and that unifying them is possible by making equality a first-class, extensible relation over a Datalog-style functional database, with a novel "merge expression" mechanism to repair functional-dependency violations. Two case studies — a Steensgaard-style points-to analysis and Herbie's floating-point rewriter — demonstrate that egglog implementations are simultaneously faster, simpler, and more correct than the original EqSat- or Datalog-only systems.

**Intent of the Author:**
The authors want to close a gap they observed developing independently in the databases/Datalog community and the programming-languages/EqSat community: each tool was hitting limitations that the other had already solved. They present egglog as a Datalog engine extended with a built-in extensible equivalence relation and uninterpreted functions with user-defined merge behavior, arguing this construction subsumes and exceeds both EqSat and Datalog-with-lattices, and they want readers to see equality saturation as fundamentally a relational/database problem rather than a separate paradigm requiring its own bespoke data structure.

---

## Topic List

1. **Fixpoint Reasoning Frameworks** : [[Fixpoint-Reasoning-Frameworks|Link]]
   - Datalog as a bottom-up recursive query language over relations : [[Fixpoint-Reasoning-Frameworks|Link1]], [[Related-Formalisms-and-Positioning|Link2]]
   - The immediate consequence operator : [[Formal-Semantics-of-egglog|Link]]
   - Least fixpoint semantics of Datalog programs : [[Formal-Semantics-of-egglog|Link]]
   - Equality saturation as term rewriting without destructive replacement
   - Phase-ordering problem in traditional term rewriting
   - Shared setup of rules plus initial facts driving both paradigms

2. **The E-Graph Data Structure** : [[The-E-Graph-Data-Structure|Link]]
   - E-nodes as function symbols over e-classes : [[The-E-Graph-Data-Structure|Link]]
   - E-classes as sets of equivalent e-nodes : [[The-E-Graph-Data-Structure|Link]]
   - Terms represented compactly via shared e-classes
   - Congruence induced by e-graph equivalence : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - E-matching as pattern matching modulo equality : [[The-E-Graph-Data-Structure|Link]]
   - Multi-patterns for simultaneous pattern matching : [[The-E-Graph-Data-Structure|Link]]
   - E-class analyses for semantic abstraction over terms : [[The-E-Graph-Data-Structure|Link1]], [[Fixpoint-Reasoning-Frameworks|Link2]]
   - Limitations of single, upward-only e-class analyses in egg

3. **The egglog Language Model** : [[The-egglog-Language-Model|Link]]
   - Functions as maps enforcing functional dependency : [[Equivalence-and-Canonicalization|Link]]
   - Relations as functions to the unit type : [[The-egglog-Language-Model|Link]]
   - The merge expression for functional-dependency repair : [[Equivalence-and-Canonicalization|Link]]
   - Default expressions and get-or-make-set semantics : [[The-egglog-Language-Model|Link]]
   - Sorts as uninterpreted domains of opaque ids
   - The union action for asserting equivalence : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Datatypes as sugar for sorts and constructor functions
   - Rewrite rules desugaring to query-and-union rules
   - Rules as query plus actions rather than body plus head : [[The-egglog-Language-Model|Link]]

4. **Equivalence and Canonicalization** : [[Equivalence-and-Canonicalization|Link]]
   - Union-find as the backing structure for sorts : [[Equivalence-and-Canonicalization|Link]]
   - Canonical representatives and canonicalization functions : [[Equivalence-and-Canonicalization|Link]]
   - Congruence closure via functional-dependency conflicts : [[Equivalence-and-Canonicalization|Link]]
   - The rebuilding procedure and its relation to e-graph rebuilding : [[Equivalence-and-Canonicalization|Link]]
   - Iterating rebuilding to a fixpoint : [[Equivalence-and-Canonicalization|Link]]
   - Avoiding joins modulo equivalence through active canonicalization : [[Equivalence-and-Canonicalization|Link]]

5. **Formal Semantics of egglog** : [[Formal-Semantics-of-egglog|Link]]
   - Core egglog syntax of programs, rules, atoms, and patterns
   - Instances as a database paired with an equivalence relation : [[Formal-Semantics-of-egglog|Link]]
   - The inflationary immediate consequence operator : [[Formal-Semantics-of-egglog|Link]]
   - Pre-instances and the need for rebuilding : [[Formal-Semantics-of-egglog|Link]]
   - The expanded database ordering over instances
   - Monotonic convergence of the immediate-consequence-then-rebuild sequence
   - The inductive fixpoint as program meaning
   - Under-approximating an infinite fixpoint by bounded iteration

6. **Incremental Evaluation** : [[Incremental-Evaluation|Link]]
   - Semi-naïve evaluation and differential databases : [[Formal-Semantics-of-egglog|Link1]], [[Incremental-Evaluation|Link2]]
   - Delta rules derived from ordinary rules
   - Equivalence of semi-naïve and naïve evaluation results : [[Incremental-Evaluation|Link1]], [[Formal-Semantics-of-egglog|Link2]]
   - Incremental e-matching as a byproduct of semi-naïve evaluation : [[Query-Evaluation-and-E-Matching|Link1]], [[Incremental-Evaluation|Link2]]

7. **Query Evaluation and E-Matching** : [[Query-Evaluation-and-E-Matching|Link]]
   - Relational e-matching reducing pattern matching to database queries : [[Query-Evaluation-and-E-Matching|Link]]
   - Worst-case optimal join algorithms (Generic Join) : [[Query-Evaluation-and-E-Matching|Link]]
   - The dual-representation problem in prior relational e-matching : [[Query-Evaluation-and-E-Matching|Link]]
   - Functional database design avoiding e-graph/database synchronization

8. **Language-Based System Design** : [[Language-Based-System-Design|Link]]
   - Typechecked rules versus host-language guard code : [[Language-Based-System-Design|Link]]
   - Multiple datatypes and multiple analyses versus a single ad-hoc type
   - egglog as both a language and a library : [[The-egglog-Language-Model|Link]]

9. **Case Study: Unification-Based Points-to Analysis** : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Steensgaard-style analysis as nearly linear unification-based points-to analysis : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Andersen-style subset-based analysis as precise but quadratic
   - Join modulo equivalence as a Datalog performance pathology : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
   - Union-find–backed relations in Souffle (eqrel) : [[Equivalence-and-Canonicalization|Link]]
   - Choice domain and subsumptive rules as a complex Datalog encoding of Steensgaard analysis
   - Soundness bugs from ad hoc equivalence encodings

10. **Case Study: Sound Floating-Point Rewriting** : [[Case-Study-Sound-Floating-Point-Rewriting|Link]]
    - Herbie's use of equality saturation for floating-point accuracy : [[Fixpoint-Reasoning-Frameworks|Link]]
    - Unsound rewrite rules and their validation/discard workaround
    - Interval analysis for bounding terms during rewriting : [[Case-Study-Sound-Floating-Point-Rewriting|Link]]
    - Not-equals analysis built on interval analysis and rewriting facts : [[Case-Study-Sound-Floating-Point-Rewriting|Link]]
    - Composable multiple analyses versus a fused monolithic analysis

11. **Unification and Logic Programming in egglog** : [[Unification-and-Logic-Programming-in-egglog|Link]]
    - Fresh ids as logic variables representing unknown information : [[Unification-and-Logic-Programming-in-egglog|Link1]], [[The-E-Graph-Data-Structure|Link2]]
    - Demand-driven top-down simulation without explicit demand relations
    - Injectivity rules propagating unification through inductive types : [[Unification-and-Logic-Programming-in-egglog|Link]]
    - Occurs check implemented independently of the unification mechanism
    - Hindley-Milner type inference via unification of type variables : [[Unification-and-Logic-Programming-in-egglog|Link]]
    - Contrast with Prolog-style backtracking and SMT-style theory combination

12. **Related Formalisms and Positioning** : [[Related-Formalisms-and-Positioning|Link]]
    - The chase and tuple/equality-generating dependencies
    - Datalog with lattices and recursive aggregates (Flix) : [[Related-Formalisms-and-Positioning|Link]]
    - egglog's relation to concurrent categorical formalizations of Datalog with equality
    - Termination as an open problem for egglog : [[Related-Formalisms-and-Positioning|Link]]
    - Congruence closure as dual to unification : [[Related-Formalisms-and-Positioning|Link]]

---

## Chapter Summaries

### 1. Introduction (pp. 1–3)

**Summary:** Motivates egglog by showing that EqSat (Herbie) and Datalog (cclyzer++) each hit real limitations solvable by the other paradigm's techniques, then sketches egglog's two core extensions — extensible equality and functions with merge expressions — as the unifying mechanism.

**Key Definitions & Concepts:**
- **Equality saturation (EqSat)** — a term-rewriting technique that keeps all rewritten and original terms via a compact e-graph structure, avoiding phase-ordering problems.
- **Datalog** — a declarative, bottom-up recursive query language over relations, popular for large-scale program analyses.
- **egglog** — a fixpoint reasoning system, essentially a Datalog engine extended with built-in extensible equality and uninterpreted functions.
- **Merge expression** — a user-specified expression that resolves functional-dependency violations by combining two conflicting output values for the same input.
- **Unsound rewrite** — a rewrite applied without proof that its precondition holds (e.g. $x/x \to 1$ requires $x \neq 0$); Herbie relies on these and must validate/discard results.
- **Join modulo equivalence** — the expensive extra join over an explicit equivalence relation that classical Datalog encodings of union-find require.

**Key Questions:**
1. Why do EqSat and Datalog fail on the *same underlying problem* — efficient equational reasoning combined with rich semantic analysis — from opposite directions?
2. What exactly does a merge expression let egglog express that a Datalog lattice join alone cannot?

---

### 2. Background (pp. 3–5)

**Summary:** Introduces Datalog's immediate consequence operator and lattice extension, then introduces e-graphs, e-matching, e-class analyses, and multi-patterns as the corresponding EqSat machinery, setting up the vocabulary the rest of the paper unifies.

**Key Definitions & Concepts by Section:**
- **2.1 Datalog** — rule (conjunctive query with head/body), immediate consequence operator $T_p$ (function from database to database), least fixpoint as program result, lattice-generalized Datalog rules with a join ($\sqcup$) operator for functions into a lattice.
- **2.2 Equality Saturation** — e-graph (set of e-classes of e-nodes), e-node (function symbol with e-class children), congruence (an e-graph representing $a\equiv b$ implies representing $f(\dots a \dots) \equiv f(\dots b \dots)$), e-matching, e-class analyses (semi-lattice values propagated bottom-up), multi-patterns, relational e-matching and its "dual representation" problem. : [[Fixpoint-Reasoning-Frameworks|Link1]], [[The-egglog-Language-Model|Link2]]

**Key Questions:**
1. In what precise sense is Datalog's fixpoint computation ($T_p$) analogous to EqSat's e-graph saturation?
2. Why does the "dual representation" problem limit relational e-matching's practical benefit even though it speeds up matching itself?

---

### 3. egglog (pp. 5–10)

**Summary:** Builds up the egglog language incrementally — from plain Datalog rules, to functions with `:merge` for lattice-style reasoning, to uninterpreted sorts with `union` for equality, to full term construction and rewriting that recovers equality saturation — showing each feature as a small, composable extension of Datalog.

**Key Definitions & Concepts by Section:**
- **3.1 Datalog in egglog** — s-expression syntax; a rule's query (body) and actions (head) roles. : [[Formal-Semantics-of-egglog|Link]]
- **3.2 Functions and :merge** — functional database (map, not set) enforcing input→output functional dependency; `:merge` resolving conflicting old/new outputs (e.g. `min` for shortest paths); relations desugar to functions returning unit.
- **3.3 Sorts and Equality** — uninterpreted sort as ids plus a union-find-backed equivalence relation; `union` action; `:default` expressions giving total-function ("get-or-make-set") semantics; ids correspond to e-class ids.
- **3.4 Terms and Equality Saturation** — `datatype` sugar for sort + constructor functions; `rewrite` desugars to `(rule ((= v p1)) ((union v p2)))`; constructors' default `:merge` is `union`, giving a congruence relation; `extract` returns the smallest equivalent term. : [[Fixpoint-Reasoning-Frameworks|Link1]], [[The-egglog-Language-Model|Link2]]
- **3.5 Beyond EqSat** — unification-based analyses and Datalog-side applications hinted at (pointer analysis, EqSat-assisting analyses) beyond either paradigm alone.

**Key Questions:**
1. How does replacing "relation as a set" with "function as a map with `:merge`" let egglog subsume Datalog's lattice extension *and* EqSat's congruence closure with the same mechanism?
2. Why must egglog canonicalize its database with respect to the union-find before querying, and what would break if it queried a stale (non-canonical) database?

---

### 4. Semantics of egglog (pp. 10–13)

**Summary:** Gives a formal, non-monotone fixpoint semantics for a "core" fragment of egglog (single-atom heads, no `union` sugar, `:merge` restricted to union-on-ids or lattice-join), defining the immediate consequence operator, the rebuilding operator that restores functional-dependency validity, and semi-naïve evaluation, then states (and later proves) that semi-naïve and naïve evaluation agree.

**Key Definitions & Concepts by Section:**
- **4.1 Syntax** — program/rule/atom/pattern/term grammar; distinguishes interpreted constants $C$ from uninterpreted constants $N$ (which play the role of e-class ids / labelled nulls from the chase).
- **4.2 Semantics** — instance $I=(DB,\equiv)$; canonicalization function $\lambda_\equiv$; inflationary immediate consequence operator $T_P^\uparrow$; pre-instance (may violate functional dependencies); rebuilding operator $R$ restoring validity by merging conflicting outputs via `merge`$_{f,\equiv}$; iterated rebuilding $R^\infty$; one evaluation round $F_P = R^\infty \circ T_P^\uparrow$; the database ordering $\sqsubseteq_I$; the inductive fixpoint $[\![P]\!] = F_P^\infty(I_\bot)$.
- **4.3 Semi-naïve Evaluation** — differential database $\Delta DB_i$; delta rules; the semi-naïve algorithm $F_P^{SN}$; Theorem 4.1 (semi-naïve produces the same database as naïve). : [[Formal-Semantics-of-egglog|Link1]], [[Incremental-Evaluation|Link2]]

**Key Questions:**
1. Why is $T_P^\uparrow$ defined to be inflationary (union with the old database) in egglog when standard Datalog's immediate consequence operator is not — what specific non-monotone rule pattern forces this?
2. What invariant does the rebuilding operator $R$ restore that a plain Datalog database never needs to worry about, and why can rebuilding require more than one iteration?

---

### 5. Implementation (pp. 12–14)

**Summary:** Describes egglog's ~4,200-line Rust implementation: a functional (map-backed) database, a rebuilding procedure inherited from egg's congruence-closure algorithm, a Generic-Join-based query engine reusing relational e-matching, and a language-first design (versus embedded EqSat libraries) that enables static typechecking of rules and unrestricted conditional rewrites.

**Key Definitions & Concepts by Section:**
- **5.1 Components** — functional database and get-or-default term evaluation; two sources of function conflicts (explicit `set` collisions vs. union-induced congruence violations); rebuilding as generalized e-graph rebuilding / e-class analysis propagation; query engine using Generic Join (worst-case optimal join).
- **5.2 Language-based Design** — statically typechecked rules vs. egg's opaque Rust guard code; unrestricted conditions in queries (no special "conditional rewrite" construct needed); support for multiple datatypes/functions/analyses vs. egg's single ad-hoc type and single analysis. : [[Language-Based-System-Design|Link]]

**Key Questions:**
1. Why does egglog's "database-native" design let it add semi-naïve evaluation for free, whereas Zhang et al.'s prior relational e-matching could not exploit this as easily?
2. What structural limitation of egg's Rust-embedded design (single type, single analysis) does egglog's language-based approach remove, and at what cost?

---

### 6. Case Studies (pp. 14–19)

**Summary:** Reports two empirical case studies: a Steensgaard-style unification-based points-to analysis reimplemented in egglog and benchmarked against several Soufflé-Datalog encodings, and a soundness overhaul of Herbie's floating-point EqSat rewriter using egglog's composable interval and not-equals analyses; both egglog reimplementations are faster, simpler, and fix real bugs.

**Key Definitions & Concepts by Section:**
- **6.1 Unification-Based Points-to Analysis** — Steensgaard (unification-based, near-linear) vs. Andersen (subset-based, precise but quadratic) points-to analysis; `eqrel`-backed union-find relations in Soufflé; the "join modulo equivalence" performance pathology; cclyzer++'s choice-domain/subsumptive-rule encoding and its two independent soundness bugs; egglog's canonicalization eliminating the extra join; benchmark result: 4.96× speedup over the fastest sound Soufflé baseline (`patched`). : [[Case-Study-Unification-Based-Points-to-Analysis|Link]]
- **6.2 Herbie: Making an EqSat Application Sound** — interval analysis (`lo`/`hi` functions merged by max/min) enabling sound division rewrites; not-equals analysis built compositionally on top; the $\sqrt[3]{v+1}-\sqrt[3]{v}$ cancellation example resolved soundly; aggregate result: sound analysis is both faster overall (73.91 vs 81.91 minutes) and sometimes more accurate (104 improved cases) than the unsound ruleset.

**Key Questions:**
1. Why does a plain `eqrel` relation fail to give Steensgaard analysis its expected near-linear performance, even though it solves the space blowup of representing equivalence explicitly?
2. What specific property of e-class analyses (single analysis, upward-only propagation) makes Herbie's original architecture unable to combine interval and not-equals reasoning cleanly, and how does egglog's rule-based approach avoid that limitation?

---

### 7. Related Work (pp. 19–22)

**Summary:** Situates egglog against e-graph/EqSat history (Nelson, Downey et al., egg, relational e-matching), Datalog/database theory (Flix, recursive aggregates, the chase, TGDs/EGDs, Datalog±, concurrent work by Bidlingmaier), and logic programming/automated reasoning (Prolog, SMT solvers, magic-set transformation), clarifying what egglog borrows, generalizes, or deliberately omits (e.g. backtracking).

**Key Definitions & Concepts:**
- **Tuple-generating dependencies (TGDs)** — rule heads that can generate fresh ids, which is how egglog rewrite rules generalize plain Datalog rules.
- **Equality-generating dependencies (EGDs)** — dependencies asserting equalities between columns, generalizing functional dependencies; egglog's `union`-only fragment corresponds to a model-semantics subset of the chase.
- **The chase** — a family of algorithms reasoning about TGDs and EGDs together; a candidate future framework for understanding egglog's termination.
- **Magic-set transformation** — a technique for demand-driven, top-down-style evaluation inside a bottom-up language, related to how egglog simulates functional-program evaluation via fresh ids.
- Contrast with Prolog: egglog forgoes backtracking (hence no persistent/backtrackable union-find) in favor of monotonicity and efficiency for tasks like equality saturation and pointer analysis.
- Contrast with SMT solvers: egglog's output is minimal/universal, better suited to extraction-based optimization than SMT's richer but non-extraction-oriented reasoning.

**Key Questions:**
1. In what precise sense does egglog's `union`-only fragment coincide with a model semantics of the classical database chase, and where does egglog deliberately diverge (e.g. via `:merge` beyond union)?
2. Why does giving up backtracking (unlike Prolog) actually make egglog's core data structure (union-find) simpler and faster rather than just less expressive?

---

### 8. Conclusion (p. 22)

**Summary:** Restates egglog's contribution from both a Datalog programmer's perspective (adds fast, extensible equivalence with preserved query planning and semi-naïve evaluation) and an EqSat user's perspective (adds composable analyses, extensible functions, incremental e-matching), identifying merge expressions as the key unifying mechanism.

**Key Questions:**
1. Why do the authors single out the merge expression, specifically, as "the key technical mechanism" rather than the union-find-backed equality relation itself?

---

### Appendix A: egglog by Example (pp. 26–33)

**Summary:** A worked tour of egglog's expressive range beyond the core case studies: simulating top-down/demand-driven evaluation of functional programs using fresh ids instead of manual demand relations, encoding simply-typed and Hindley-Milner type inference via unification and injectivity rules, and several self-contained "pearls" (multivariable equation solving, compressed Datalog proof terms via proof irrelevance, and matrix/Kronecker-product algebra with dimension-checked guarded rewrites).

**Key Definitions & Concepts by Section:**
- **A.1 Functional Programming with egglog** — demand relations as the traditional Datalog workaround for top-down evaluation; fresh ids as implicit "holes" that later rewriting fills, avoiding manual demand transformation.
- **A.2 Simply Typed Lambda Calculus** — free-variable analysis as ordinary egglog rules (not a host-language e-class analysis) with `:merge` as set-intersection; capture-avoiding substitution via skolemized fresh variables; type inference requiring top-down context propagation, which e-class analyses cannot express but Datalog-style demand rules can.
- **A.3 Type Inference Beyond STLC** — Hindley-Milner inference via a single injectivity rule unioning corresponding argument/result types; type generalization/instantiation at let-bindings; occurs check implemented as an independent, modular relation rather than baked into the unification mechanism.
- **A.4 Other egglog Pearls** — equation solving by rewriting whole equations (variable isolation rules) rather than one-directional term rewriting; proof datatypes with proof irrelevance (equivalent proofs merged, aiding termination and compactness); matrix/Kronecker-product algebra where a rewrite's soundness depends on symbolic dimension equality, requiring the "analysis" (dimension) itself to be rewritten algebraically rather than merely propagated.

**Key Questions:**
1. Why can egglog encode top-down, demand-driven functional-program evaluation without an explicit demand relation, when Datalog fundamentally cannot avoid one?
2. Why is dimension-checking for the Kronecker-product rewrite rule impossible to express faithfully as a conventional e-class analysis, and what does egglog's "just another function" treatment buy back?

---

### Appendix B: Correctness of the Semi-Naïve Algorithm (p. 33)

**Summary:** Proves Theorem 4.1/B.1 by induction: the semi-naïve evaluation sequence $I_i^{SN}$ coincides with the naïve evaluation sequence $I_i^N$ at every iteration, using monotonicity of $T_P$ and an idempotence-like identity for repeated rebuilding ($R^\infty(R^\infty(I)\cup DB) = R^\infty(I \cup DB)$).

**Key Definitions & Concepts:**
- **Inductive step structure** — assumes agreement up to iteration $i$, derives agreement at $i+1$ via set-containment reasoning on $\Delta DB_i$ and monotonicity of $T_P$ with respect to $\subseteq$.

**Key Questions:**
1. Where exactly in the proof does monotonicity of $T_P$ get used, and why would the proof fail if $T_P$ itself (rather than only the outer $F_P$ sequence) were non-monotone?
