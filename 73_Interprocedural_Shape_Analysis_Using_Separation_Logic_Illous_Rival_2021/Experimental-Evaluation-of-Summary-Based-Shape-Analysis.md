---
title: Experimental Evaluation of Summary-Based Shape Analysis
source: "Interprocedural Shape Analysis Using Separation Logic-based Transformer Summaries (Illous, Lemerre, Rival, SAS 2020)"
chapters: "Section 8: Experimental Evaluation (pp. 17–19, Appendix A); Section 9: Related Works and Conclusion (pp. 19–20)"
tags: [static-analysis, separation-logic, shape-analysis, benchmarking, interprocedural-analysis]
---

# Experimental Evaluation of Summary-Based Shape Analysis

[[book-guidelines|↩ Back to guidelines]]

## Why this section exists at all

Everything up to this point in the paper is a stack of *claims that could be false in practice even if true on paper*. The composition algorithm ($\#$, [[Abstract-Intersection-and-Composition-Algorithms|Chapter 6]]) is proved sound — but soundness only says the analysis never lies, not that it says anything useful. The top-down modular call algorithm ([[Modular-Interprocedural-Call-Analysis|Chapter 7]]) is proved to preserve summaries across calls — but nothing in that proof bounds how often a summary actually needs to be recomputed, or whether the widening steps that guarantee termination shred away so much precision that the whole exercise becomes pointless. A relational, transformation-based abstraction sounds more expressive than the call-string (inlining) alternative — but "more expressive on paper" and "actually faster in a compiler you'd want to ship" are different claims, and only one of them is testable by proof.

So Section 8 exists to answer three very concrete questions that no soundness theorem in the paper answers:

1. **Precision** — does working with abstract *transformations* instead of abstract *states* cost you anything? A transformation only sees a call site's local footprint; does that locality blind it to invariants a whole-state analysis would catch?
2. **Scalability** — is the modular analysis actually faster than inlining every call (the call-string baseline), and by how much, and where does the gain concentrate?
3. **Reuse effectiveness** — the entire performance argument for procedure summaries rests on an empirical bet: that a context summary, once inferred, gets *reused* far more often than it gets *recomputed*. If summaries needed constant regeneralization, the top-down protocol from Chapter 7 would degenerate into something not much better than reanalyzing from scratch. Is that bet actually true on real code?

If you don't have honest answers to these three questions, everything in Sections 3–7 is an elegant abstract machine that might be worthless in the one dimension (engineering tradeoffs) the whole paper was motivated by in the first place — recall Chapter 1's opening argument was explicitly about *why relational domains compose better*, a claim about practice, not just about semantics.

## The experimental setup

The authors built a **Frama-C plugin** implementing the interprocedural analysis from Section 7, targeting a substantial fragment of C: standard control-flow constructs, parameterized by an inductive definition of the heap structure under analysis (as in prior work by Chang and Rival). Notably out of scope: recursive structures interleaved with non-inductive data (strings, arrays, numeric types) — the tool is deliberately scoped to the shape-analysis core the paper is about, not a general-purpose C verifier.

To get a meaningful comparison, they *also* implemented a second Frama-C plugin: a **call-string-based analysis** that inlines procedures at every call site. This is the natural competitor — it's what you get if you take a whole-state separation-logic analysis and make it interprocedural the "obvious" way, by unrolling the call graph instead of building composable summaries. Every comparison in this section is summary-based analysis vs. this inlining baseline, run on the same machine (an Intel Core i7 laptop @ 2.3GHz, 16GB RAM) so the timings are directly comparable.

Two experiments were run:

- **Experiment 1 (real code):** a ~3kLOC fragment of GNU Emacs 25.3 — specifically the 22 functions implementing the `Fx_show_tip` feature (tooltip display), which manipulates Lisp object descriptions built as Cons pairs. This is not synthetic benchmark code; it's a real feature from a real, widely-used codebase, chosen because it's heap-manipulation-heavy (lots of list traversal and construction) — exactly the workload the shape-analysis machinery targets.
- **Experiment 2 (recursive structures):** a battery of classical recursive algorithms over lists and trees — length, allocation, deallocation, concatenation, map, deep copy, filter for lists; visit, size, search, deallocation, insertion, deep copy for trees — to specifically stress-test the recursive-call handling from the end of Chapter 7 (the fixpoint-over-context-summaries mechanism), which the main Emacs benchmark barely exercises.

## Precision: does modularity cost anything?

The precision check is a direct comparison: for each of the 22 `Fx_show_tip` functions, take the transformation the summary-based analysis computed for the *whole procedure body*, starting from the entry abstract state stored as the first component of its context summary — recall from Chapter 4 that a context summary is a pair $(h^\sharp_f, t^\sharp_f)$, precondition heap plus transformation — and check whether it is at least as precise as the postcondition the state-based (call-string) analysis independently computed for the same entry state.

The result: **15 of the 22 functions contain nested calls and are directly comparable — for all 15, the summary-based result is exactly as precise as the state-based result.** The other 7 functions have no calls at all in their bodies, so the comparison is marked "irrel." (irrelevant) — there's nothing about interprocedural composition to test in a function with no callees.

This is the load-bearing empirical result for the whole approach: **zero precision loss, across every comparable function, from switching to a relational, footprint-local abstraction.** That's not something the soundness theorems (Theorem 1–3) guarantee — soundness only forbids *false* claims, it says nothing about how *tight* those claims are. A relational abstraction could in principle be sound but systematically coarser than tracking the whole state (this is exactly the failure mode the paper worries the relevance-slicing operator $R[\ldots]$ from Chapter 7 might introduce, by only exposing the callee-relevant fragment of the heap rather than the whole thing). The experiment says: in practice, on this codebase, it doesn't happen.

## Scalability: the headline number

The single most quoted number in the paper: **total analysis time was 14.20 seconds for the transformation-based (summary) analysis versus 877.12 seconds for the state-based (call-string) analysis** on the full `Fx_show_tip` fragment — roughly a **62× speedup**.

But the paper is careful not to stop there, because a single aggregate ratio hides where the win actually comes from. Figure 8 in the paper is a per-function scatter plot (log-log axes, summary-based runtime on the vertical axis, state-based runtime on the horizontal axis) comparing the *average* analysis time per call for each function (not total time spent — that's a distinct metric, addressed separately under "Effectiveness" below). The per-function raw data, from Appendix A:

| Function | State time (s) | Summary time (s) | Precision | Call-graph depth |
|---|---|---|---|---|
| Fcons | 0.33 | 0.34 | irrel. | 8 |
| list2 | 0.32 | 0.32 | as precise | 7 |
| list4 | 0.33 | 0.32 | as precise | 7 |
| Fassq | 2.16 | 6.46 | irrel. | 6 |
| Fcar | 0.32 | 0.33 | irrel. | 3 |
| Fcdr | 0.33 | 0.33 | irrel. | 2 |
| Fnthcdr | 0.33 | 0.34 | irrel. | 3 |
| Fnth | 0.34 | 0.34 | as precise | 2 |
| make_monitor_attribute_list | 0.33 | 0.74 | as precise | 6 |
| check_x_display_info | 0.33 | 0.33 | irrel. | 3 |
| Fx_display_monitor_attributes_list | 0.41 | 0.86 | as precise | 2 |
| x_get_monitor_for_frame | 0.40 | 0.37 | irrel. | 6 |
| x_make_monitor_attribute_list | 0.47 | 0.87 | as precise | 5 |
| x_get_monitor_attributes_fallback | 0.35 | 1.01 | as precise | 4 |
| x_get_monitor_attributes | 0.35 | 1.11 | as precise | 3 |
| x_get_arg | 11.82 | 8.76 | as precise | 5 |
| x_frame_get_arg | 21.75 | 8.87 | as precise | 4 |
| x_default_parameter | 23.00 | 8.91 | as precise | 3 |
| compute_tip_xy | 38.24 | 16.80 | as precise | 1 |
| x_default_font_parameter | 39.06 | 7.17 | as precise | 2 |
| x_create_tip_frame | 321.77 | 6.96 | as precise | 1 |
| Fx_show_tip | 877.12 | 14.20 | as precise | 0 |

Reading the "Depth" column against the speedup ratio is the key move: **depth 0 is the entry point** (`Fx_show_tip` itself — the root of the call graph), and depth increases as you move toward leaf functions. The pattern is unambiguous:

- **Near the leaves (high depth, e.g. Fcons at depth 8, Fassq at depth 6)**, the two analyses cost about the same, or the transformation analysis is actually a bit *slower* (Fassq: 2.16s state vs. 6.46s summary — a 3× *slowdown*).
- **Near the root (low depth, e.g. `x_create_tip_frame` at depth 1, `Fx_show_tip` at depth 0)**, the transformation analysis wins by 1–2 orders of magnitude (`x_create_tip_frame`: 321.77s → 6.96s, a ~46× speedup; the full program: 877.12s → 14.20s).

**Why this shape, mechanically:** a leaf function is called with few or no nested calls beneath it, so there's little reanalysis for a summary to save you from — but building and widening the abstract transformation still carries its own bookkeeping overhead (constructing $t^\sharp$, maintaining the identity/input-output structure, running the composition machinery from Chapter 6 even when the payoff is small). That overhead is a pure cost with no offsetting benefit at the leaves. Conversely, a function high in the call graph triggers many nested calls transitively — every one of which the state-based analysis must *re-walk from scratch* every single time it's reached (this is exactly the "reanalyze `append`'s body once per call" problem the Overview chapter opened with), while the summary-based analysis pays the summary's cost once and then applies it — a $O(1)$-ish composition — at every subsequent occurrence. **The gain is proportional to how much reanalysis a summary actually eliminates, which scales with position in the call graph, not with raw function size.**

This is a genuinely important qualification the paper is honest about: summary-based interprocedural analysis is not a free win everywhere — it's a trade of small constant overhead per call for large savings on repeated reanalysis, and that trade only pays off where reanalysis would otherwise be expensive.

## Effectiveness: how often do summaries actually need to be recomputed?

This is the metric that validates the *mechanism* from Chapter 7 specifically — the coverage test $h^\sharp_{in,f} \sqsubseteq_H h^\sharp_f$ that decides whether an existing context summary already covers a new call, versus needing to widen and reanalyze (lines 4–6 of the algorithm in Figure 7, reproduced from the source: `if ¬(h_in,f ⊑_H h_f) then h_f ← h_f ▽_H h_in,f; t_f ← [[C]]^T#(Id(h_f))`).

Four columns matter here, from the Appendix A reanalysis-count table:

| Function | #state | #total | #recomp | #reuse |
|---|---|---|---|---|
| Fcons | 296 | 47 | 3 | 44 |
| list2 | 12 | 2 | 1 | 1 |
| list4 | 24 | 4 | 1 | 3 |
| Fassq | 64 | 16 | 1 | 15 |
| Fcar | 24 | 1 | 1 | 0 |
| Fcdr | 12 | 4 | 1 | 3 |
| Fnthcdr | 24 | 1 | 1 | 0 |
| Fnth | 24 | 8 | 1 | 7 |
| make_monitor_attribute_list | 6 | 2 | 1 | 1 |
| check_x_display_info | 3 | 1 | 1 | 0 |
| Fx_display_monitor_attributes_list | 3 | 1 | 1 | 0 |
| x_get_monitor_for_frame | 6 | 2 | 1 | 1 |
| x_make_monitor_attribute_list | 3 | 1 | 1 | 0 |
| x_get_monitor_attributes_fallback | 3 | 1 | 1 | 0 |
| x_get_monitor_attributes | 3 | 1 | 1 | 0 |
| x_get_arg | 19 | 5 | 1 | 4 |
| x_frame_get_arg | 15 | 1 | 1 | 0 |
| x_default_parameter | 15 | 15 | 1 | 14 |
| compute_tip_xy | 3 | 3 | 1 | 2 |
| x_default_font_parameter | 1 | 1 | 1 | 0 |
| x_create_tip_frame | 1 | 1 | 1 | 0 |
| Fx_show_tip | 1 | 1 | 1 | 0 |

where **#state** is how many times the *state*-based analysis had to reanalyze that function's body (its baseline reanalysis count), **#total** is how many times the *summary*-based analysis's call-site encounters that function, **#recomp** is how many of those encounters forced a summary recomputation (the widen-and-reanalyze branch), and **#reuse** is how many encounters were satisfied by simply applying (composing) the existing summary with no reanalysis at all.

Two things jump out, and the guidelines' own Key Questions for this chapter point straight at them:

**First, almost every function needed its context summary recomputed exactly once.** Only `Fcons` needed more than one recomputation — 3 times, against 44 clean reuses. Every other function in the table shows `#recomp = 1`: the very first time a function is analyzed, a context summary doesn't exist yet (recall context summaries start at $(\bot, \bot)$, so the very first encounter unconditionally takes the widen-and-reanalyze branch — this matches the paper's own note in Section 7 that the branch "necessarily occurs whenever a procedure is analyzed for the first time"). After that one unavoidable bootstrap cost, the summary generalizes enough to cover everything else thrown at it. This is a direct, empirical confirmation of Example 10's `append(a,b); append(a,c)` scenario from Chapter 7: a summary inferred from a narrow context (list of length exactly 1) gets widened once to something general (list segment of *any* length) and then stays valid.

**Second, for functions called at more than one site, reuse dominates recomputation heavily** — 8 functions were reused 3 to 44 times each, with only that single mandatory recomputation as overhead. (11 of the 22 functions are called at only a single site, so `#reuse = 0` for them by construction — there's no second call to reuse the summary at.) Contrast this against the state analysis's #state column: `x_default_parameter` needed 15 full reanalyses, `Fcons` needed 296. **The state analysis is paying full reanalysis cost every single time; the summary analysis is paying it effectively once per function** — this is the mechanical reason behind the aggregate 62× speedup, restated at the granularity of individual call sites rather than aggregate time.

The paper's own gloss on this: "the near-universal computed-once, reused-many-times pattern... [shows] how quickly top-down context summaries tend to stabilize in practice" — and explicitly connects it back to the claim that even small functions benefit ("the summary-based analysis provides significant gain even for small functions"), which nuances the depth-based scalability story above: it's not just deep call trees that benefit, reuse frequency matters independently of depth.

## Validation on recursive structures

The Emacs benchmark, despite being real production code, barely exercises the recursive-call handling sketched at the end of Chapter 7 (the fixpoint over context summaries needed when a procedure calls itself, where both $h^\sharp_f$ and $t^\sharp_f$ must be widened and the body reanalyzed until the transformation stabilizes). So the authors ran a second experiment specifically targeting recursion: classical algorithms over singly-linked lists and binary trees.

| Structure | Function | Time (ms) |
|---|---|---|
| List | length | 1.256 |
| List | get_n | 2.179 |
| List | alloc | 1.139 |
| List | dealloc | 0.842 |
| List | concat | 1.833 |
| List | map | 0.904 |
| List | deep_copy | 1.540 |
| List | filter | 3.357 |
| Tree | visit | 1.078 |
| Tree | size | 1.951 |
| Tree | search | 3.818 |
| Tree | dealloc | 1.391 |
| Tree | insert | 5.083 |
| Tree | deep_copy | 2.603 |

Every single one of these — including tree `insert`, the slowest at 5.083ms — completes in **under 5 milliseconds**. There's no baseline comparison column here (the paper doesn't report call-string timings for these), so this table isn't making a *comparative* speedup claim the way the Emacs data does. Its job is narrower and more structural: it demonstrates that the fixpoint-over-summaries mechanism for recursive calls — which the main text admits "would [need] significantly heavier formalization" and is left informal in the paper — actually *converges*, and converges fast, on the canonical recursive shapes (list segments, binary trees) that the whole summary predicate vocabulary ($lseg$, inductive tree predicates) was built to describe in the first place. It's a sanity check on soundness-by-construction more than a performance claim: the widening-based termination argument from Chapter 5/7 isn't just theoretically guaranteed to terminate, it terminates *fast* on exactly the structures this analysis exists for.

## Synthesis: what these results validate, and what's left open

Section 8 closes the loop the paper opened in Chapter 1. The motivating argument there was that relational (transformation-based) domains compose more gracefully than tabulated state pre/post-condition pairs — illustrated with a numeric polyhedra-vs-intervals analogy, not a proof. Section 8 is where that analogy gets cashed out on real code: precision matches the state-based baseline exactly wherever the two are comparable (15/15), the aggregate speedup is roughly 62× on real production heap-manipulation code, and the mechanism that's supposed to make composability *pay off* — summaries stabilizing after one recomputation and then being reused — is confirmed at the level of individual call sites, not just as an aggregate number.

What the results also *qualify*, honestly, rather than oversell: the speedup is not uniform. It concentrates at high positions in the call graph and can be a net loss at the leaves, because the bookkeeping cost of maintaining and composing abstract transformations is a fixed overhead that only earns its keep when it's actually preventing repeated reanalysis. A reader building intuition for when to reach for a relational/summary-based interprocedural analysis versus a simpler inlining approach should take this as the real lesson: the technique wins specifically on *deep call graphs with call-site reuse*, and this paper is careful to report exactly the data that lets you see that shape rather than hiding it behind one headline ratio.

Section 9 (Related Works and Conclusion) situates this empirical result within the broader interprocedural-analysis literature — Sharir and Pnueli's original relational framework, TVLA's primed-variable technique for relational shape analysis, tabulation-based separation-logic summaries (Gulavani et al., Calcagno et al.) — and its verdict is that transformation-based summaries solve a problem tabulation-based summaries structurally can't: tables of separation-logic pre/post-condition pairs "need to grow large to precisely characterize the effect of procedures," while a single transformation gives "a more local description of the relation between procedure input and output states." The chapter doesn't claim to have closed every question, though — it explicitly flags **bi-abduction** (precondition inference, currently only implemented on state domains, argued to be "orthogonal" to the state/transformation choice but not actually demonstrated on transformations here), **bottom-up summary inference** as a complement to the paper's top-down protocol, and **cut-point-based stack/heap abstraction** as compatible techniques left for future combination. These are the open threads a reader should treat as genuinely unresolved by this paper, not settled — the experimental chapter validates the mechanism that exists, not the larger design space around it.
