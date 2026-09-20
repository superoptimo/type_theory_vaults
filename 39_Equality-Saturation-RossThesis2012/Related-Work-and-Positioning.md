---
title: Related Work and Positioning
source: "Equality Saturation: Using Equational Reasoning to Optimize Imperative Functions (Ross Tate, PhD Thesis, UC San Diego, 2012)"
chapters: "Chapter 19, Related Work (pp. 221–229); Chapter 20, Conclusion (pp. 230–232)"
tags: [compilers, equality-saturation, program-optimization, e-graphs, peg, related-work, superoptimization, dataflow-languages, explanation-based-learning]
---

[[book-guidelines|↩ Back to guidelines]]

# Related Work and Positioning

## Why a lineage chapter matters here

Every idea in this thesis — additive equality reasoning, PEGs with no intermediate variables, generalizing rules from proofs — reads as more inevitable once you see what it's a *response to*. Chapter 19 is the author's own account of that lineage: eight prior research threads, each of which got one piece right and one piece wrong, and PEGs/equality saturation as the point in design space that keeps the right pieces from all eight while discarding the wrong ones. This isn't a citation dump; the author is using "here's specifically what breaks in the prior approach" as the argument for why the thesis's design choices are forced, not arbitrary.

The throughline worth tracking as you read: almost every prior IR that tried to be "fully functional" (VDGs, dataflow languages, even lambda calculus itself) reached for **variable binding** to represent loops or control flow. The thesis's central technical bet — argued explicitly in this chapter — is that variable binding is exactly the wrong tool once your goal is *equality saturation* specifically (as opposed to just "a clean functional representation"), because reasoning about substitution during saturation is where the technique becomes intractable. Keep this lens on as each prior IR shows up below.

## Superoptimizers: the ancestor of "compute a set, then choose"

**What they got right.** A superoptimizer's core move — instead of picking one rewrite and committing, enumerate a *set* of equivalent programs and pick the best one at the end — is structurally the same move equality saturation makes. The thesis names **Denali** as the direct inspiration: Denali builds an expression graph over a basic block, applies axioms to grow an **E-graph** (a data structure representing many equal ways of computing the same values), and then calls a SAT solver repeatedly to extract the cheapest way to compute the block given everything the E-graph now knows is equal.

If you haven't seen an E-graph before, the concrete picture is: nodes are operations (e.g. `+`, `*`, a variable read), and nodes get grouped into *equivalence classes* whenever an axiom proves two of them compute the same value — `a * 2` and `a + a` end up as two nodes in the same class, both still present, neither one privileged as "the" representation. That's the "additive" idea in miniature, and it's exactly what the E-PEG in this thesis specializes and extends.

**What they got wrong (for this thesis's purposes).** Superoptimizers scale only to small, straight-line code — a basic block, not a whole function with loops and branches. The reason is the search space: superoptimizers typically search over *all instruction sequences up to some length*, which blows up combinatorially the moment control flow (and hence exponentially many paths) enters the picture. The thesis's answer is a different lever entirely: don't search over instruction sequences, search over *equalities* provable from a fixed axiom set, and represent loops/branches natively in the IR (via $\theta$/eval/pass, covered in [[Program-Expression-Graphs-(PEGs)|the PEGs article]]) so equality saturation applies to entire control-flow graphs. The tradeoff the author is explicit about: Denali's cost model is *more precise* than the thesis's, because it can cost entire instruction sequences at once (capturing scheduling and register-allocation effects), whereas this thesis's cost model is coarser, node-by-node.

**[[Domain-Independent-Applications-of-Generalization#Grounding|Grounding]].** Think of an E-graph as a Rust-shaped union-find over expression nodes:

```rust
struct EClassId(u32);

enum ENode {
    Add(EClassId, EClassId),
    Mul(EClassId, EClassId),
    Const(i64),
    Var(String),
}

struct EGraph {
    classes: Vec<Vec<ENode>>,      // eclass id -> all nodes proven equal
    union_find: UnionFind<EClassId>,
}
```

Adding an axiom instance doesn't replace an `ENode` — it calls `union_find.merge(class_of(a), class_of(b))`, and both representations survive in the same class. Extraction (picking the best member of each class under a cost function) is a separate, final pass — precisely the "choose only at the end" idea shared with superoptimizers.

## Rewrite-based optimizers and the phase-ordering problem

**What they got right.** Systems like TAMPR, ASF+SDF, the Visser et al. ML compiler, and Stratego popularized axioms/rewrite rules as *the* way to express an optimization: a pattern on the left, a replacement on the right. This is a genuinely good idea for *expressing* an optimization — the thesis keeps it (its own axioms have exactly this shape; see Appendix A of the source, e.g. `if invariant_ℓ(A), then eval_ℓ(A, P) = A`).

**What they got wrong.** These systems apply rewrites *destructively*, one at a time, in an order controlled by a strategy language the compiler writer has to design and tune. This is the seam where the **phase-ordering problem** lives (covered at length in [[Equality-Saturation|the Equality Saturation article]]): a rewrite applied now can permanently destroy the syntactic pattern a later, more profitable rewrite needed to match on. The thesis's contrast is stated flatly in the text: "we instead simultaneously explore all possible optimization orderings, while avoiding redundant work" — no strategy language needed, because nothing is ever destroyed, so order becomes irrelevant rather than merely hard to tune. A companion research thread the chapter cites — automated techniques for finding good rewrite *sequences*, and manual/automated techniques for combining analyses with optimizations — attacks the same phase-ordering symptom from the opposite side: better sequencing of a destructive process, rather than making the process non-destructive in the first place.

**Grounding.** In Rust terms, a destructive rewrite pass is a `fn optimize(ir: &mut Ir)` that mutates in place — once it runs, the "before" form is unrecoverable except by literally re-deriving it. Equality saturation instead looks like `fn saturate(egraph: &mut EGraph)`, which only ever calls `.merge(...)`; nothing is deleted, so a later axiom can still see and match on the "before" form even after an earlier axiom already matched on it and asserted an equality with an "after" form.

## Value Dependence Graphs: the closest prior IR, and where it breaks

This is the chapter's most load-bearing comparison, and the thesis spends the most space on it.

**What VDGs got right.** Like PEGs, the **Value Dependence Graph** is a *complete, fully functional* representation — no imperative statements, no explicit control-flow edges, just a graph of value dependencies. This functional purity is exactly the property that makes equational reasoning natural (an equation $a = b$ can only be sound if $a$ and $b$ denote values, not effectful statements — see [[Representing-Effects-in-PEGs|the Effects article]] for how this thesis handles the one place where that purity is genuinely hard, side effects).

**Where VDGs break.** VDGs represent loops using **$\lambda$-abstraction** — ordinary function abstraction, `λx. e_body`, applied to an argument `e_arg`. This is the natural functional-programming move for "a value that depends on something varying" — and it is precisely what the thesis argues is fatal for *efficient equality saturation specifically* (not for functional representations in general). The argument has two layers:

1. **Direct cost.** Reasoning about $\lambda$s requires reasoning about **substitution** — when do you actually replace `x` with `e_arg` inside `e_body`? This is doable during saturation, but expensive, because saturation is *also* optimizing the body of the $\lambda$ at the same time it's deciding whether/when to substitute. Every future version of the body — and equality saturation is, by design, accumulating many versions of everything simultaneously — potentially needs the substitution re-applied.
2. **A prior, harder problem: when to abstract at all.** Before you can even ask "when do we substitute," you need to have decided *when to introduce* a $\lambda$ in the first place — i.e., turn some expression $e$ into $(\lambda x. e_{body})(e_{arg})$, which means recognizing that $e_{arg}$ should be pulled out of $e$ as a separate binding. Determining when this transformation is profitable is itself hard, and doing it *soundly across all currently-known-equivalent forms of $e$ and $e_{arg}$* — remember, equality saturation is tracking many equivalent forms simultaneously — compounds the difficulty.

The thesis then generalizes this into the chapter's real thesis-statement-within-a-thesis-statement: *the problem isn't $\lambda$ specifically, it's intermediate variables.* Any construct that introduces a named intermediate — $\lambda$ parameters, but also monads or continuation-passing style from the functional-languages world — adds a layer of indirection that costs reasoning overhead under saturation. This is stated explicitly as the reason the thesis represents effects via an **effect witness** (see the Effects article) rather than monads/CPS, and the reason it uses genuinely recursive expressions rather than syntactic fixpoint operators. PEGs' $\theta$/eval/pass triple (see the PEGs article) is the alternative: loop-varying values are represented *without* introducing a bound variable for "the current iteration's value" — the loop-iteration index is implicit in the semantics, not a name you have to substitute for.

**Grounding — why this is a real engineering tradeoff, not just aesthetics.** In Lean terms, this is exactly the distinction between a *de Bruijn representation requiring `instantiate`/substitution calls* and a *substitution-free combinator calculus*. Lean's kernel actually pays this substitution cost constantly (`Expr.instantiate1` walks and rebuilds terms under binders); the thesis's bet is that paying this cost repeatedly, once per saturation step, across every live equivalent form of a loop body, is a cost a compiler can't afford the way a proof kernel — which typically substitutes once, when actually applying a term — can. In Rust, the same tension shows up as the difference between representing a loop body as a `Box<dyn Fn(Value) -> Value>` (a real closure — capturing a value means you're now doing substitution-like work whenever you specialize it) versus representing "the value on iteration $i$" as data indexed directly by $i$, with no closure and no capture at all — closer to what `θ_ℓ(base, step)` is doing.

## Program Dependence Graphs, Dependence Flow Graphs, and SSA-family IRs

The chapter places PEGs against a cluster of statement-oriented or partially-functional IRs, in increasing order of how close they get to PEGs' design:

- **SSA / gated SSA / thinned gated SSA.** The gated-SSA $\mu$ function is structurally similar to PEGs' $\theta$, and the gated-SSA $\eta$ function is similar to the eval/pass pair. The decisive difference: SSA-family nodes are *inserted into the CFG* — the control-flow graph is still there, and SSA decorates it. PEGs drop the CFG entirely. This cuts both ways. Dropping the CFG removes placement constraints on IR nodes, so restructuring the CFG becomes just a matter of manipulating the PEG (the subject of [[Converting-Between-Imperative-Code-and-PEGs|the conversion article]]) — but it also means going *back* from PEG to CFG is hard, since explicit control information has to be reconstructed. (Converting an SSA program back to imperative code, by contrast, is nearly free: for each $\phi$-node `x := φ(a, b)`, just insert `x := a` and `x := b` at the ends of the two predecessor blocks — the CFG never left.)
- **Program Dependence Graph (PDG).** Groups operations that execute in the same control region, but remains **statement-based** — it doesn't achieve the fully-functional/value-oriented uniformity PEGs have. Consequence: each analysis and optimization on a PDG has to be built as its own separate algorithm, whereas the thesis's claim is that PEG-based analyses and optimizations fall out of *one* unified reasoning mechanism (equality saturation itself).
- **Program Dependence Web (PDW).** Combines PDG with gated SSA; its conversion algorithms resemble this thesis's PEG-conversion algorithms. But the PDW still keeps *explicit PDG control edges* — again making the return trip to a CFG easier than PEGs' return trip, at the cost of not being purely functional.
- **Dependence Flow Graphs (DFGs).** A complete, *executable* dependency-based representation — closer to PEGs in spirit — but DFGs use a **side-effecting store operation**, i.e. an imperative model of memory. PEGs are entirely functional, which the thesis argues is what makes equational reasoning "natural" (an equation about a side-effecting store operation needs much more care to state soundly than an equation about pure values).

**Grounding.** The PDG-vs-PEG contrast maps cleanly onto a familiar Rust distinction: a PDG is like a set of `impl` blocks, one trait implementation per analysis, each hand-written against the same underlying statement graph. A PEG-plus-equality-saturation system is more like deriving all those analyses as *consequences* of a single generic algorithm (union-find plus axiom application) parameterized only by which axioms you load — closer to how a single `derive` macro can generate many trait impls from one shared structural description, rather than writing `impl ConstantFold`, `impl DeadCodeElim`, `impl Licm` by hand as separate passes.

## Lucid: the dataflow language that got the shape right but the goal wrong

**Lucid** is the closest linguistic relative to PEGs' loop primitives. Its `first`/`next` operators are directly analogous to $\theta$, and its `as soon as` operator is analogous to the eval/pass pair. Lucid variables are literally maps from iteration counts to (possibly undefined) values — which is exactly the semantic model PEGs use for loop-varying quantities.

**Where it diverges.** Lucid was designed as a language *to make formal correctness proofs easy* — it's a proof/specification tool. Peggy (this thesis's system) uses the same kind of node-equivalence machinery to *optimize* code written in an existing imperative language, not to specify new code from scratch. A more technical difference the thesis flags: the PEG semantics incorporate a **monotonize** function, which guarantees correctness when converting to and from CFGs containing loops — a concern Lucid, as a from-scratch proof language rather than a compilation target for existing imperative code, doesn't need to solve the same way.

**Why this matters for positioning.** Lucid is evidence that the $\theta$/eval/pass *shape of idea* isn't new — dataflow languages had already discovered that "a variable is a stream indexed by iteration count" is a clean way to give loops a functional semantics. What's new in this thesis is repurposing that same semantic shape as the *substrate for an E-graph*, engineered specifically so that adding equalities over it stays tractable — a goal Lucid's designers never had.

## Theorem proving and E-graphs: the direct ancestor of E-PEGs

The chapter is explicit that this is the most direct technical lineage: "our work is related to the broad area of automated theorem proving. The theorem prover that most inspired our work is **Simplify**, with its E-graph data structure for representing equalities." E-PEGs are, in the author's own words, "in essence specialized E-graphs for reasoning about PEGs" — i.e., not a new data structure so much as an E-graph whose nodes are PEG operators (including $\theta$/eval/pass) rather than generic terms.

A second, more subtle connection: the way separate analyses in this thesis's system *communicate with each other through shared equality facts* is conceptually the same move made by **Nelson-Oppen** combination procedures for theorem provers — different decision procedures (for linear arithmetic, uninterpreted functions, etc.) stay decoupled except for propagating equalities they've each derived into a shared pool, letting each procedure benefit from facts discovered by the others without needing to understand each other's internal reasoning. In this thesis, that shared pool is the E-PEG itself, and the "decision procedures" are the different optimization analyses.

**Grounding.** In Lean terms, this is the closest thing in the whole chapter to a literal correspondence worth naming: an E-graph's congruence closure — merging `f(a)` and `f(b)` automatically once `a = b` is known — is exactly what Lean's `isDefEq`/definitional-equality checking is doing when it decides two terms reduce to the same normal form, except an E-graph does it *eagerly and persistently* (maintaining the closure as a data structure you can query cheaply later) rather than *on-demand* (re-deriving it fresh at each `isDefEq` call). If you're building a theorem-prover-style kernel, this chapter is effectively saying: an E-graph is a cache-and-amortize strategy for congruence closure that a batch compiler pass can afford to build once and reuse, in a way a kernel doing one-off equality checks typically doesn't bother to.

## Explanation-based learning and machine-learned heuristics

Two distinct "learning" comparisons, and the chapter is careful to keep them apart — this distinction is worth being precise about since it's easy to conflate.

**Explanation-based learning (EBL).** The thesis's rule-generalization technique (see [[Learning-Optimizations-from-Proofs|the Learning from Proofs article]]) is explicitly positioned as an *instance* of EBL from the AI-research literature: learning a general rule from a *single* example, using an **explanation** of why that example holds. EBL has prior applications in Prolog optimization, logic-circuit design, and software reuse, many via unification-based or Prolog-based algorithms — and the thesis notes its own framework can encode Prolog's declarative components by combining categories of expressions with categories of relations (see [[Domain-Independent-Applications-of-Generalization|the generalization-applications article]] for where this shows up concretely, e.g. the database-query and type-debugging applications). The closest single prior work is Dietzen and Pfenning, who extended EBL to higher-order and modal logic using $\lambda$Prolog and applied it to program transformations — but relying on the *user* to prove correctness via tactics, with no automatic decomposition into sub-optimizations (since a user manually writing the proof already does that decomposition by hand) and no experimental demonstration of amortizing superoptimizer cost or extending a compiler automatically, both of which this thesis provides.

**Machine learning in compilers.** A separate, non-overlapping research thread: genetic algorithms, reinforcement learning, and supervised learning have all been used to learn **profitability heuristics** — when/where to apply instruction scheduling, register allocation, prefetching, loop-unroll factors, or optimization ordering decisions. The chapter's key positioning move: this is *complementary*, not competing, because it learns *heuristics* (when to fire a rule), while this thesis learns *the transformation rules themselves* (what rule to fire), using a single global profitability heuristic uniformly across all of them. A second contrast: statistical ML methods need large datasets; the EBL-based approach here can learn correctly from a single example, because it's exploiting the *proof structure* of that one example rather than statistical regularities across many.

**Optimization Inference — the closest prior generalization work.** Superoptimizer-based prior work (including Bansal and Aiken's) has explored *discovering* optimizations, and Bansal and Aiken's superoptimizer specifically achieves a simple form of generalization: abstracting away concrete register names and constants. The thesis's generalization is qualitatively different — it generalizes based on *the proof-theoretic reasons* the original and transformed programs are provably equivalent (formalized via the pushout/pullback categorical framework covered in [[Domain-Independent-Applications-of-Generalization|the earlier chapter]]), not just syntactic abstraction of literals.

**Grounding.** In Rust/Python terms: a machine-learned heuristic is a function `fn should_apply(rule: RuleId, context: Context) -> bool` fit from data — it decides *when*. This thesis's EBL-style learning instead *derives a new `Rule` value itself* — a new left-hand-side/right-hand-side pattern pair with a soundness proof — from a single `(before, after)` example, by walking that example's equivalence proof and finding the most general premises under which each proof step still goes through. These are genuinely orthogonal axes: you could plug a learned heuristic on top of learned rules, and the chapter is flagging that as unexplored future overlap rather than existing competition.

## Open challenges: what the thesis explicitly leaves unsolved

Chapter 20's Conclusion closes the thesis by naming, in the author's own words, the two obstacles blocking **interprocedural** optimization — i.e., extending equality saturation across function-call boundaries, not just within one function's control-flow graph:

1. **No known algebraic, intermediate-variable-free interprocedural representation.** Everything in this thesis works because PEGs eliminate intermediate variables *intraprocedurally* (that's the whole VDG critique above). But function **parameters** are themselves a form of intermediate variable, and no one — including this thesis — has found an interprocedural analogue of the $\theta$/eval/pass trick that avoids reintroducing them. The author calls this obstacle "fundamentally insurmountable" as currently understood — a strong claim, and one the Key Questions in the guidelines flag as worth interrogating: why does *this* obstacle read as harder than the second one below, rather than as "just" a bigger version of the same substitution-cost problem VDGs already have?
2. **Combinatorial explosion with insufficient guidance.** Even setting aside representation, interprocedural programs are large, and equality saturation's search space grows correspondingly, with little available information about *where* an interprocedural transformation is actually likely to pay off. Unlike obstacle (1), the author treats this one as the place future effort should focus — e.g., collecting interprocedural information like aliasing and applying it intraprocedurally (today's common strategy), or letting programmers annotate code to flag where interprocedural optimization is worth attempting.

A third, more practical gap the Conclusion names as arguably "the greatest weakness" of the whole line of work: this approach has no known way to **cooperate with conventional (destructive, pass-ordered) optimizers** inside a real production pipeline. Equality saturation as presented is an all-or-nothing alternative architecture, not (yet) a drop-in pass you can interleave with a conventional GCC/LLVM-style pipeline — closing that gap is named as the author's own intended next step.

## Synthesis: how this chapter closes the thesis

```
Superoptimizers ──(additive equality, but only straight-line code)──┐
                                                                      │
Rewrite-based optimizers ──(axioms, but destructive + ordered)──────┼──► Equality Saturation
                                                                      │    (additive + branches/loops)
Theorem provers / E-graphs ──(congruence closure over equalities)───┘         │
                                                                                │
VDGs / Lucid / PDG / PDW / DFG / SSA ──(functional or dependency-based        │
        IRs for loops & control, but λ-bound or statement-based)──► PEG ──────┤
                                                                    (no        │
                                                                intermediate   │
                                                                  variables)   │
                                                                                ▼
                                                                          E-PEG (E-graph
                                                                          specialized to PEGs)
                                                                                │
Explanation-based learning ──(generalize from one example + explanation)──────┤
Machine-learned heuristics ──(complementary: learns WHEN, not WHAT)───────────┘
                                                                                │
                                                                                ▼
                                                            Generalizing rules from proofs
                                                    (categorical pushout/pullback framework)
                                                                                │
                                                                                ▼
                                            open: interprocedural PEGs, search guidance,
                                              integration with conventional pipelines
```

Reading this chapter alongside the rest of the thesis, the pattern is: PEGs (intraprocedural, no intermediate variables) are the representation that makes E-PEGs (E-graphs specialized to that representation) tractable, and E-PEGs are what makes equality saturation (additive, phase-ordering-free optimization search) actually scale past straight-line code — solving superoptimizers' scaling problem while keeping their "compute a set, choose at the end" idea. The learning results (generalizing optimization rules from single proofs, covered in the Learning from Proofs and Domain-Independent Applications articles) are then presented as a second payoff *of the same representation*: because PEG equivalence proofs are structured objects (built from the same axioms saturation uses), they can be walked and generalized the same way a theorem's proof can be generalized in EBL — which is precisely why the author frames this as complementary to, not competing with, statistically-learned compiler heuristics.

**For the standing project (dependent/refinement-type compiler with an embedded prover):** the two connections worth carrying forward explicitly are (1) the E-graph/congruence-closure correspondence to `isDefEq`-style definitional equality checking — an E-graph is what you get if you decide to cache and persist congruence closure rather than re-deriving it per query, which is a real architectural choice for a kernel doing heavy elaboration; and (2) the "intermediate variables are the recurring tax on automated reasoning" thesis, which generalizes past loops — it's the same tax substitution/context management pays in a Hoare-logic soundness proof, and the same tax metavariable instantiation pays during unification. A representation that minimizes named intermediates (PEGs' answer here) is one instance of a strategy that shows up again anywhere reasoning has to happen *underneath* a binder — including your elaborator's metavariable contexts.

**[[Domain-Independent-Applications-of-Generalization#Where this leads|Where this leads]]:** this is the thesis's final substantive chapter before the appendix of axioms — there is no later chapter this feeds into. Its role is entirely retrospective: it is the argument that everything built in Chapters 2–18 occupies a genuinely distinct point in a well-explored design space, not a novel restatement of any one prior thread.
