---
title: "Case Study: Unification-Based Points-to Analysis"
source: "Better Together: Unifying Datalog and Equality Saturation"
chapter: "6.1 Unification-Based Points-to Analysis"
pages: "14–17"
tags: [datalog, equality-saturation, egglog, points-to-analysis, union-find, static-analysis]
---

[[book-guidelines|↩ Back to guidelines]]

## What breaks without fast equivalence

Points-to analysis answers a deceptively simple question about a program: for a pointer `p`, what set of memory allocations could `p` point to at run time? Every alias analysis, every "can this write clobber that read" check, every points-to-driven optimization in a compiler rests on the answer. Most implementations of it live in Datalog — the declarative style keeps the analysis rules readable, and decades of relational query optimization make the execution fast even on big codebases.

There are two classic styles. **Andersen-style** analysis is subset-based: `p` points to a *set* of allocations, and the analysis tracks subset relationships between these sets as the program's assignments and dereferences are processed. It is precise, because it never conflates two allocations that a real execution could distinguish — but the sets can grow large, and the algorithm is worst-case quadratic in the number of pointers. **Steensgaard-style** analysis takes the opposite bet: the moment the analysis learns that `p` *might* point to two different allocations `a1` and `a2`, it declares `a1` and `a2` equivalent and merges them into one class, forever. From then on `p` points to *the equivalence class*, not to a set. This is a strictly coarser approximation — real executions that Andersen's analysis would keep apart get conflated — but the payoff is that the whole analysis runs in nearly linear time, because there's only ever one representative to track per pointer, never a growing set.

So Steensgaard's analysis is, at its mathematical core, a **unification** problem: "these two things must be treated as the same" is exactly the operation a union-find structure was built for (this is the same "assert two things equal, and everything downstream should stop distinguishing them" move you'll recognize from [[Equivalence-and-Canonicalization|canonicalization]] and, more distantly, from unification in a type checker's constraint solver — see [[Unification-and-Logic-Programming-in-egglog]]). The question this case study answers is: can classical Datalog actually deliver on that near-linear promise, or does encoding "these are now equivalent" in a language built around static relations quietly reintroduce the cost the whole style was designed to avoid?

## Datalog's equivalence problem

The naive way to represent "$a_1$ and $a_2$ are equivalent" in Datalog is a plain relation `eq(a1, a2)`, populated and closed under reflexivity, symmetry, and transitivity by ordinary rules. That's disastrous: closing an equivalence relation with explicit transitivity rules blows the relation up to quadratic size in the number of equivalent elements, which defeats the entire point of using a unification-based (i.e., supposedly cheap) analysis in the first place.

Soufflé, a mature Datalog engine, addressed this with a special relation kind: `eqrel`. A relation marked `eqrel` is stored using an actual union-find data structure under the hood, so the equivalence closure is maintained automatically and efficiently — no explicit transitivity rule, no quadratic blowup in the equivalence relation itself.

That sounds like it should solve the problem outright. It doesn't, because of how that equivalence relation has to be *used* by the rest of the analysis.

### Join modulo equivalence

Consider a rule (adapted directly from the book, §6.1) that propagates points-to information through a load-then-store pattern — `*x = y` followed by `p = *q` should mean "`x` and `q` now point to the same set of allocations":

```
eql(yAlloc, pAlloc) :-
    store(x, y), vpt(x, xAlloc), vpt(y, yAlloc),
    load(p, q),  vpt(p, pAlloc), vpt(q, qAlloc),
    eql(xAlloc, qAlloc).
```

Focus on the subquery `vpt(x, xAlloc), vpt(q, qAlloc), eql(xAlloc, qAlloc)`. Even though `xAlloc` and `qAlloc` are *already known* to be equivalent — that's the entire premise of the rule — Soufflé still has to perform an explicit join against the `eql` relation to confirm it. The union-find backing makes membership checks in `eql` themselves cheap, but the query planner still treats `eql` as just another relation to join against, on every single rule invocation that needs to compare two allocation ids for equivalence. The book gives this pattern a name: **join modulo equivalence**. It shows up constantly in practice, and it is expensive enough that in `cclyzer++` — a real, production-grade Datalog encoding of Steensgaard analysis discussed below — profiling identified a single rule doing this join as an order of magnitude slower than every other rule in the analysis.

The root cause is structural, not incidental: Datalog relations store *tuples of raw ids*. `eqrel` makes checking "are these two ids equivalent?" fast, but it does nothing to stop `vpt` (the points-to relation itself) from accumulating multiple, individually-tracked, equivalent-but-not-identical allocation ids for the same pointer. If `p` can point to `a1` and later learns `a1 ≡ a2`, a plain Datalog encoding doesn't rewrite the existing `vpt(p, a1)` tuple in place — it just now also knows `a1 ≡ a2` as a separate fact, and every future rule that reads `vpt(p, ⋅)` has to rejoin against `eql` to notice. The analysis has fast *equivalence checking* but not fast *canonicalization* — there's no cheap way to collapse "the many allocations pointed to by the same pointer" down to one representative before that blow-up propagates to every pointer downstream.

### How far Datalog engineers have to go to work around it

`cclyzer++`, a real points-to analysis tool built on Soufflé, has to manually engineer around this gap using two of Soufflé's most advanced (and newest) features together: a **choice domain** (Soufflé's mechanism for restricting a relation to at most one output per key, used here to keep only one canonical allocation per pointer) and **subsumptive rules** (rules that let a newly derived fact retract/subsume weaker existing facts, used to implement a hand-rolled notion of "this fact replaces that one" on top of ordinary Datalog semantics). Together these let `cclyzer++` fake canonicalization: track *a* canonical representative per equivalence class, updated manually as new equivalences are discovered.

This works, but it is exactly the kind of ad hoc equivalence encoding that is easy to get subtly wrong — and the book reports that it *was* gotten wrong, independently, twice. Two separate soundness bugs were found in `cclyzer++`'s hand-rolled equivalence machinery, each capable of producing an unsound (i.e., incomplete/incorrect) points-to result. Fixing them required bringing Soufflé's `eqrel` relations back into the mix on top of the choice-domain/subsumptive-rule encoding — so the "patched" version ends up combining *three* of Soufflé's most sophisticated, newest features (choice domain, subsumptive rules, and `eqrel`) simultaneously, an interaction the paper's authors describe from direct experience as "extremely tricky to debug."

That is the real cost this case study is pointing at: it's not just that join-modulo-equivalence is slow, it's that *removing* it requires bolting together enough special-case machinery that the resulting encoding becomes a soundness liability in its own right.

## egglog's answer: canonicalize, don't just check

egglog sidesteps the problem entirely, and the fix follows directly from [[Fixpoint-Reasoning-Frameworks#The mechanism|the mechanism]] covered in [[Equivalence-and-Canonicalization]]: instead of treating "is `a` equivalent to `b`?" as a relation to be joined against, egglog maintains a canonical representative for every equivalence class via union-find and **actively rewrites every tuple to use canonical ids** as part of rebuilding. Two elements are equivalent *if and only if* they have the same canonical representative — that's the entire equivalence check, and it's already implicit in how the tuples are stored.

Concretely: the user declares `vpt` as a function (pointer → allocation-equivalence-class) with functional-dependency repair set to unify the violating ids on conflict — the exact `:merge`-with-union pattern from [[The-egglog-Language-Model]]. When the analysis learns that pointer `p` points to both `a1` and `a2`, egglog's functional-dependency machinery unifies `a1` and `a2` automatically, and rebuilding canonicalizes every existing tuple that mentioned either id. The load/store propagation rule from earlier becomes a plain equality join — `vpt(x, xAlloc), vpt(q, qAlloc)` with `qAlloc = xAlloc` — because canonicalization already guarantees that equivalent allocations share an id. There is no `eql` relation to join against at all, because there's nothing left for it to check that isn't already baked into the tuples themselves.

This is a direct payoff of the design decision covered in [[Fixpoint-Reasoning-Frameworks]] and [[Formal-Semantics-of-egglog]]: unifying Datalog's query engine with the e-graph's rebuilding discipline means "equivalent" and "identical-after-canonicalization" become the same thing by construction, rather than two separately-maintained facts that have to be reconciled by an extra join on every query.

## The benchmark: does it actually pay off?

The paper reimplements a subset of `cclyzer++`'s Steensgaard-style analysis (context-, flow-, path-insensitive, field-sensitive) in egglog and benchmarks it against real programs from `postgresql-9.5.2`, with a 20-second timeout, against four points of comparison:

- **`eqrel`** — the naive encoding using Soufflé's `eqrel` relation directly (no canonical representative, so `vpt` can hold multiple equivalent allocations per pointer).
- **`cclyzer++`** — the original choice-domain/subsumptive-rule encoding (unsound, due to the two bugs above).
- **`patched`** — the authors' own fix to `cclyzer++`, restoring soundness by reintroducing `eqrel` alongside choice domain and subsumptive rules — the fastest *sound* Soufflé-based baseline available.
- **`egglogNI`** — egglog with semi-naïve evaluation disabled, isolating how much of egglog's advantage comes from canonicalization alone versus from [[Incremental-Evaluation|incremental evaluation]].

The results confirm the mechanism argument directly: `eqrel` times out on nearly every benchmark (join modulo equivalence dominates), and `cclyzer++` — despite being the fastest of the Soufflé variants — times out on three benchmarks and is unsound on the rest. `egglog` beats `patched`, the fastest *sound* Soufflé baseline, by **4.96× on average**; it beats `cclyzer++` (unsound but fast) by 1.94×; and it beats its own non-incremental variant `egglogNI` by 1.59×, showing that canonicalization and semi-naïve evaluation are both pulling real, independent weight.

## Where this leads

This case study is the concrete payoff of two mechanisms introduced earlier in the book: canonicalization (§4, [[Equivalence-and-Canonicalization]]) eliminates join-modulo-equivalence by construction, and semi-naïve evaluation ([[Incremental-Evaluation]]) compounds that advantage further. If you're building a static analysis with an equivalence-heavy fixpoint — alias analysis, congruence-based abstract interpretation, anything where "these things are now indistinguishable" is a first-class fact the analysis discovers at run time — this is the concrete argument for why a canonicalizing Datalog-like engine beats a plain relational encoding, independent of any equality-saturation use case. The companion case study, [[Case-Study-Sound-Floating-Point-Rewriting]], shows the same underlying machinery paying off from the opposite direction: not a Datalog analysis that needed equivalence, but an equality-saturation tool that needed composable Datalog-style analyses.
