---
title: Related Formalisms and Positioning
source: "Better Together: Unifying Datalog and Equality Saturation"
chapters: "7. Related Work (pp. 19–22), 8. Conclusion (p. 22)"
tags: [egglog, datalog, equality-saturation, chase, automated-reasoning]
---

[[book-guidelines|↩ Back to guidelines]]

# Related Formalisms and Positioning

Every new formalism owes the reader two things: what problem it solves, and *where it sits* relative to the formalisms that already existed. egglog's own related-work section is unusually candid about this — it doesn't just cite prior art, it uses each comparison to sharpen what egglog actually is. This article works through four of those comparisons: the database-theoretic **chase**, **Datalog-with-lattices** systems like Flix, a **concurrent, independently-discovered categorical formalization** of the same idea, and the **logic-programming/SMT** family (Prolog, theorem provers). Along the way we pick up the one open problem the paper is honest about leaving unsolved: **termination**.

## Why "where does this sit" is itself a technical question

It would be easy to read egglog as "Datalog, but you can also say two things are equal." That description is true but useless — it doesn't tell you what egglog *can't* do that a more general system can, or what egglog gives up on purpose to be fast. The related-work section is where the paper earns the right to make precise claims like "our `union`-only fragment coincides with a model semantics of the chase" instead of hand-wavy claims like "this is chase-like." Precision here matters because it's what lets a reader import decades of existing theory — chase termination conditions, TGD/EGD complexity results — instead of starting from scratch.

**What breaks without this comparison work:** without it, egglog would be an island. A practitioner hitting a divergence bug would have nowhere to look for termination conditions; a database theorist would have no way to tell whether egglog's rebuilding procedure is "just" a known algorithm in disguise (it mostly is — a form of the chase) or something genuinely new (the efficient, syntactically-restricted evaluation strategy is).

## The chase, TGDs, and EGDs

The **chase** is a family of database algorithms, going back decades, for reasoning about two kinds of dependency between relations:

- **Tuple-generating dependencies (TGDs)** — rules whose *head* is allowed to invent brand-new rows, potentially containing fresh, previously-unseen identifiers (called *labelled nulls* in the database literature). Formally, a TGD looks like $\forall \bar x.\, \varphi(\bar x) \rightarrow \exists \bar y.\, \psi(\bar x, \bar y)$ — the existential $\bar y$ is exactly the "invent something new" part.
- **Equality-generating dependencies (EGDs)** — rules that don't invent anything, but *assert equalities* between existing values. A plain functional dependency, $R(x_1,\dots,x_i,\dots,x_k) \wedge R(x_1,\dots,x_i',\dots,x_k) \rightarrow x_i = x_i'$, is the simplest example: if two rows agree on the key columns, they must agree on the dependent column too. EGDs generalize this to *any* pair of columns across *any* rows, not just a single functional-dependency slot.

If you've been reading this vault in order, both of these should feel immediately familiar, just under unfamiliar names:

| Database-theory term | egglog concept |
|---|---|
| TGD (head invents fresh values) | A `rewrite` rule generating a fresh e-class id for a new subterm — see [[The-egglog-Language-Model]] |
| EGD (asserts equality between columns) | The `:merge` expression resolving a functional-dependency conflict, or a plain `union` action — see [[Equivalence-and-Canonicalization]] |
| The chase (iteratively applies TGDs/EGDs until a fixpoint) | egglog's evaluation loop: immediate consequence, then rebuild, repeat — see [[Formal-Semantics-of-egglog]] |

This isn't a loose analogy — the paper states it precisely: **the model semantics of the chase directly gives a model semantics of the subset of egglog where `union` is the only `:merge` operation.** That's a strong, checkable claim, not a vibe. It means that for the "pure equality" fragment of egglog (no lattice joins, no custom merge functions — just asserting that things are equal), decades of chase theory apply directly.

Where egglog *diverges* from the general chase is exactly where you'd expect from a system built for speed rather than maximal generality: egglog imposes syntactic restrictions so that rule application is **deterministic and efficient**. The general chase allows nondeterministic choices (which dependency to apply next, how to satisfy an existential) that can blow up the search space; egglog's `:merge` mechanism resolves every functional-dependency conflict with a fixed, user-specified function, so there's never a branching decision to make. You trade some of the chase's generality (arbitrary TGDs/EGDs, nondeterministic satisfaction) for a system where every rewrite step is a deterministic database operation you can actually implement efficiently.

**What breaks without this restriction:** an unrestricted chase can require search — trying different ways to satisfy an EGD — which is exactly the kind of backtracking egglog is built to avoid (see the Prolog comparison below). By fixing `:merge` in advance, egglog turns "which equality do I choose?" from a runtime search problem into a compile-time function definition.

## Datalog with lattices: Flix and the recursive-aggregates lineage

The **`:merge` expression** — egglog's mechanism for repairing a functional-dependency conflict when a function is written to twice with different outputs — didn't appear from nowhere. The paper is explicit that it's **directly inspired by Flix**, a Datalog extension that lets relations be annotated with a **lattice**: instead of storing plain facts, a Flix relation can store elements of a partially ordered set with a join operation ($\sqcup$), and repeated derivations of the "same" fact get combined via that join rather than either overwriting or duplicating.

The classic example — which you've already seen in [[Fixpoint-Reasoning-Frameworks]] — is shortest-path search: instead of a boolean "there is a path from $a$ to $b$," you track the *minimum-weight* path, and when two different derivations produce two different weights for the same $(a,b)$ pair, you keep the minimum. That "keep the minimum" step is a lattice join. egglog can simulate this exact pattern by setting a function's `:merge` to the lattice-join operator (e.g. `min`).

What egglog buys beyond Flix is generality of *what* the merge does. Flix's lattice-join must be, well, a lattice join — associative, commutative, idempotent, with a well-defined ordering. egglog's `:merge` is an arbitrary expression. Setting it to `min` recovers Flix-style shortest-path reasoning; setting it to `union` (the union-find merge) recovers equality saturation; setting it to something else entirely (like the interval-bound merge in [[Case-Study-Sound-Floating-Point-Rewriting]], which takes the *tighter* of two bounds) recovers custom semantic analyses that don't fit the lattice mold as cleanly. Flix sits in a broader lineage of systems trying to find a principled theoretical foundation for **recursive aggregates** in Datalog — a notoriously delicate topic, since naive aggregation (like `COUNT` or `SUM` inside a recursive rule) can break monotonicity and hence break the guarantee that a least fixpoint even exists. Other systems in this lineage include Bloom$^L$ (a similar lattice-based take), and industrial engines like LogicBlox and Rel that support recursive aggregates directly.

**What breaks without this generalization:** if `:merge` had to be restricted to genuine lattice joins (as in Flix), egglog couldn't express `union`-based congruence closure as "just another merge" — union isn't well-typed as a lattice join over an arbitrary domain in the way `min` or `max` are. Unifying Datalog-with-lattices and equality saturation under one mechanism specifically *requires* `:merge` to be more general than a lattice join.

```rust
// A sketch of ":merge" as a Rust trait — the same interface handles
// three semantically different repair strategies.
trait MergeStrategy<V> {
    fn merge(&self, old: V, new: V) -> V;
}

struct ShortestPath; // Flix-style lattice join
impl MergeStrategy<u32> for ShortestPath {
    fn merge(&self, old: u32, new: u32) -> u32 { old.min(new) }
}

struct UnionFind; // equality-saturation-style congruence
impl MergeStrategy<EClassId> for UnionFind {
    fn merge(&self, old: EClassId, new: EClassId) -> EClassId {
        union(old, new) // asserts old == new, returns the representative
    }
}

struct TighterInterval; // Herbie-style semantic-analysis repair
impl MergeStrategy<(f64, f64)> for TighterInterval {
    fn merge(&self, old: (f64, f64), new: (f64, f64)) -> (f64, f64) {
        (old.0.max(new.0), old.1.min(new.1)) // intersect the bounds
    }
}
```

One `trait`, three unrelated-looking use cases — that's the same move egglog makes by letting `:merge` be an arbitrary expression rather than a fixed lattice-join primitive.

## Concurrent, independent convergence: Bidlingmaier's categorical formalization

One of the more interesting related-work entries isn't a predecessor at all — it's a **concurrent, independent rediscovery**. Martin Bidlingmaier formalized "Datalog with equality" — the same core idea as egglog — as **relational Horn logic** and **partial Horn logic**, and studied its properties from a **categorical** point of view, with a follow-up paper describing an evaluation algorithm resembling the chase.

This is worth pausing on, because it's a genuine data point about the idea's naturalness: two groups, coming from different communities (egglog from programming languages and program optimization; Bidlingmaier from category theory and logic), arrived at structurally the same core insight — that equality saturation is really "Datalog plus a first-class equivalence relation" — via completely different formal vocabularies. The egglog authors are explicit about the difference in motivation and emphasis: their work is driven by **practical applications** (program optimization, pointer analysis) and focuses on a **simpler operational model**, whereas Bidlingmaier's categorical treatment goes for **theoretical generality and abstract structure**.

If you've read [[Categorical-Logic-Type-Theory]]-style material elsewhere in this vault's other books, this should ring a bell: the same underlying phenomenon (equational reasoning over a relational structure) admits both an *operational* description (egglog's rules, actions, rebuilding procedure) and a *categorical* one (Bidlingmaier's Horn-logic-as-a-category treatment). Neither is more "correct" — they're different lenses trading legibility for generality, exactly the kind of duality proof theory and category theory constantly surface.

## Termination: the open problem

Datalog's termination story is well understood: as long as rule heads only ever produce facts drawn from a fixed, finite universe of constants (no fresh-id generation), the immediate consequence operator is monotone over a finite lattice, so it *must* reach a fixpoint in finitely many steps — see [[Fixpoint-Reasoning-Frameworks]] for why monotone operators over finite domains are guaranteed to converge.

egglog gives up that guarantee on purpose. Because `rewrite` rules can generate **fresh ids** (the TGD-style existential from earlier in this article), a naive egglog program can grow its universe of ids without bound — which is precisely what happens in ordinary equality saturation: rewriting `x` to `x + 0` to `x + 0 + 0` to ... never stops unless something external (a size bound, an iteration budget) cuts it off. The paper is candid that egglog's termination condition is **"quite open"** — unlike Datalog, where the finite-universe restriction gives you termination for free, egglog's added expressiveness (fresh-id generation via TGD-like rules) means termination is no longer automatic, and the paper doesn't claim to have solved it.

What the paper *does* offer is a research direction rather than a solved problem: lean on the egglog–chase correspondence established earlier in this article. The database-theory community has spent years establishing termination conditions for the chase under various restrictions on TGDs and EGDs (e.g. results from Bellomarini et al., Calì et al., Fagin et al.). If egglog's rewrite rules and functional dependencies can be faithfully translated into TGDs and EGDs, those existing chase-termination results become *candidates* for egglog-termination results — not automatically applicable, but a concrete place to start rather than an open void. Meanwhile, the pragmatic reality is that "nearly all instantiations of equality saturation in practice will diverge" if left unbounded — practitioners already rely on external stopping criteria (iteration counts, e-graph size limits, timeout budgets), and egglog inherits that same practical discipline by design rather than by accident.

**What breaks without acknowledging this:** a system that silently promised termination it couldn't deliver would be far more dangerous than one that's honest about running until an external budget cuts it off. egglog's design — allowing divergence by design, as a direct consequence of generalizing equality saturation — is the honest choice given that the underlying problem (does this set of rewrite rules reach a fixpoint?) is, in general, undecidable.

## Congruence closure as the dual of unification

The paper draws one more comparison worth isolating on its own, because it's the cleanest bridge to logic programming: **congruence closure is a dual procedure to unification** (a result due to Kanellakis and Revesz).

Both are algorithms about equality between terms, but they run in opposite directions:

- **Unification** starts with two terms containing *unknowns* (variables) and asks: what's the most general substitution that makes them equal? It moves from "these could be equal under the right assignment" to "here is the assignment."
- **Congruence closure** starts with a set of *known* equalities between ground (variable-free) terms and asks: what other equalities are logically forced? It moves from "these specific things are equal" to "here is everything else that must also be equal, by congruence."

Unification *discovers* an equality by solving for unknowns; congruence closure *propagates* a given equality outward through term structure. egglog's fresh ids play the role of unification's variables — an id that isn't yet constrained to any particular structure represents "unknown information," exactly like a Prolog logic variable (this is developed further in [[Unification-and-Logic-Programming-in-egglog]]). Meanwhile the union-find-backed equivalence relation and the rebuilding procedure from [[Equivalence-and-Canonicalization]] are the congruence-closure half. A single egglog program can run both simultaneously — fresh ids standing in for unknowns while rewrite rules propagate congruence around them — because the two procedures are complementary rather than competing.

## Positioning against Prolog and SMT solvers

Two last comparisons sharpen what egglog is by contrast with what it deliberately isn't.

**Against Prolog:** egglog forgoes backtracking entirely. In Prolog, unification variables can be bound and later *unbound* on backtracking, which means Prolog's union-find-like binding structure must be **backtrackable/persistent** — every binding has to be undoable. egglog never backtracks (it's a bottom-up, monotone, Datalog-style evaluator, not a top-down search procedure), so its union-find never needs that undo capability. This isn't just a minor implementation simplification — persistent/backtrackable union-find data structures carry real overhead (path compression becomes harder to do soundly, for instance), so giving up backtracking is precisely what lets egglog's union-find stay simple and fast for tasks that are naturally monotone, like equality saturation and pointer analysis. The trade-off is expressiveness: Prolog's `cut` operator (which prunes choice points) has no direct analog in egglog, because there are no choice points to prune in the first place. egglog does retain some imperative machinery from EqSat practice — rule scheduling, for fine control over execution order — but that's a different axis of control than backtracking search.

**Against SMT solvers:** SMT solvers decide satisfiability over rich combined theories (linear arithmetic, bitvectors, arrays, uninterpreted functions) and can express things egglog cannot, like disjunction. But there's a structural difference in what the two systems are *for*: an SMT solver's output is a model or an unsat proof — rich, but not naturally suited to "give me the smallest equivalent term." egglog's output is **minimal** (or, in database terms, **universal**) — it's built around producing exactly the fixpoint database, which is exactly what [[The-E-Graph-Data-Structure]]'s `extract` operation needs to pull out an optimal term. It's technically possible to repurpose an SMT solver as an ad hoc equality-saturation engine, but the paper calls this "arcane and not officially supported" — the fit is forced, not natural. This is the same reason `egraph`-native extraction (see [[The-egglog-Language-Model]]) exists as a first-class operation in egglog but not as a natural SMT-solver feature.

## Where this leads

This article is deliberately the paper's own "here's the map" chapter, and it closes the loop the rest of this vault's articles opened: the chase and TGDs/EGDs give the [[Formal-Semantics-of-egglog]] article's fixpoint definitions a decades-old theoretical home; Flix and lattice-Datalog explain where `:merge` came from and why it had to be more general than a lattice join to also cover [[Equivalence-and-Canonicalization]]'s union-find repairs; the congruence-closure/unification duality is the conceptual bridge into [[Unification-and-Logic-Programming-in-egglog]]; and the open termination question is the honest asterisk on every fixpoint claim made throughout this vault's egglog articles. For the `automated-reasoning` Focus Area specifically, the chase-as-proof-procedure framing and the congruence-closure/unification duality are the two threads most worth carrying forward — they're the same machinery underlying trusted-kernel proof reconstruction and metavariable unification in dependently-typed elaborators elsewhere in this vault.
