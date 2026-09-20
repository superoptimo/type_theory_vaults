---
title: Modular Interprocedural Call Analysis
source: "Interprocedural Shape Analysis Using Separation Logic-based Transformer Summaries (Illous, Lemerre, Rival, SAS 2020)"
chapter: "Chapter 7, Interprocedural Analysis Based on Function Summaries (pp. 13–17)"
tags: [static-analysis, abstract-interpretation, separation-logic, shape-analysis, interprocedural-analysis, fixpoint-iteration]
---

[[book-guidelines|↩ Back to guidelines]]

## Why call analysis needs to be its own algorithm

Everything up to this chapter has been building parts: Chapter 3 gave you abstract transformations and their concretization, Chapter 4 gave you the two-part notion of a *context summary* $(h^\sharp_f, t^\sharp_f)$ (a precondition paired with a transformation sound relative to it), Chapter 5 showed how to compute a transformation by walking a procedure body, and Chapter 6 gave you $\sqcap$ and $\#$ as the reasoning primitives for reconciling and sequencing abstract heaps and transformations. Chapter 7 is where these parts get assembled into an actual **procedure-call analysis algorithm** — the piece that decides, every time the analysis reaches a call site, whether it can reuse an existing summary or must first extend/recompute one.

This is the paper's central engineering payoff. A naive interprocedural analysis reanalyzes a callee's body from scratch at every call site (call-string / inlining), which is precise but scales badly — the Emacs benchmark in Chapter 8 shows the state-based baseline taking 877 seconds against 14 seconds for the summary-based approach on the same fragment. The entire point of *summaries* is to pay the cost of analyzing a procedure body once, then discharge subsequent calls to it cheaply. Chapter 7 formalizes exactly what "cheaply" means and exactly when a summary must be regenerated instead of reused.

**What breaks without a coverage test:** a summary computed for one calling context is not automatically valid for a different one — a summary derived assuming the first argument is a single-cell list says nothing sound about a call where that argument is a five-cell list. If the analysis just blindly reused whatever summary it had on file, it would be unsound. The whole chapter's algorithmic core exists to answer, precisely and soundly, "does my existing summary already cover this new context, and if not, how do I extend it?"

## The four-step shape of one call-site analysis

For a procedure `proc f(p0,...,pk){C}` with an existing context summary $(h^\sharp_f, t^\sharp_f)$, analyzing a call `f(x0,...,xk)` given the pre-transformation $t^\sharp_{pre}$ (everything computed up to the call) proceeds in four steps:

1. **Parameter passing** — bind actual arguments to formal parameters.
2. **Footprint extraction** — figure out which part of the heap $f$ can actually see and touch.
3. **Coverage test** — check whether the existing summary's precondition subsumes this call's actual footprint.
4. **Apply or recompute** — if covered, apply the summary by composition; if not, widen the precondition and reanalyze the body first (Section 7.2), *then* apply.

Each step reuses machinery from earlier chapters directly — this section is genuinely a synthesis chapter, not new primitive theory.

### Step 1 — parameter passing, as ordinary transfer functions

Parameter passing is nothing more than the Chapter 5 toolkit applied in sequence: introduce the formal parameters as fresh variables, then assign each actual argument into its formal:

$$t^\sharp_{pars} = (\![p_k = x_k]\!^{T\sharp} \circ \ldots \circ [\![p_0 = x_0]\!]^{T\sharp} \circ newV_T^\sharp[p_0,\ldots,p_k])(t^\sharp_{pre})$$

This is exactly the pattern Chapter 5 flagged $newV_T^\sharp$/$delV_T^\sharp$ as existing for — a reminder that the earlier chapter's "bookkeeping" transfer functions were being set up specifically for this moment.

### Step 2 — footprint extraction: projection then relevance slicing

Having bound parameters, the analysis needs to know what abstract state actually enters $f$'s body. Two sub-steps:

**Projection $O: T \to H$.** This operator strips a transformation down to just its "output" abstract heap:

$$O(Id(h^\sharp)) = h^\sharp \qquad O([h^\sharp_0 \dashrightarrow h^\sharp_1]) = h^\sharp_1 \qquad O(t^\sharp_0 *_T t^\sharp_1) = O(t^\sharp_0) *_S O(t^\sharp_1) \qquad O(t^\sharp \wedge c^\sharp) = O(t^\sharp) \wedge c^\sharp$$

Read it as: for anything that's unchanged, the output is just what's there; for anything modified, take the *post*-side; and both connectors distribute structurally. $O(t^\sharp_{pars})$ over-approximates the full set of states at the moment control enters $f$'s body — but "full" is the wrong granularity to test coverage against, because it includes heap fragments $f$ never touches (e.g. a sibling variable `c` in a three-argument call where `f` only uses two).

**Relevance slicing $R$.** This is where the algorithm gets genuinely precise. The relevant symbolic names are defined inductively:

$$\frac{}{(\&p_i) \in R[h^\sharp]} \qquad \frac{n \in R[h^\sharp] \qquad h^\sharp \text{ contains a term } n\cdot f \mapsto n' \text{ or } lseg(n,n')}{n' \in R[h^\sharp]}$$

In words: the addresses bound to formal parameters are relevant by definition, and relevance propagates along points-to and segment edges — exactly a reachability closure over the heap graph, seeded at the call's arguments. Given the least solution to these rules, $R[p_0,\ldots,p_k](h^\sharp)$ is the sub-heap built only from relevant-only terms, and $I[p_0,\ldots,p_k](h^\sharp)$ is everything else, with $h^\sharp = R[\ldots](h^\sharp) *_S I[\ldots](h^\sharp)$ — a clean separating-conjunction split, guaranteed disjoint because relevance is computed structurally over the same separated heap.

**Rust framing.** The relevance rules are a textbook reachability BFS/DFS over a heap-as-graph:

```rust
// h^# as a graph: nodes are symbolic names, edges are points-to / lseg facts.
fn relevant_names(h: &AbsHeap, params: &[Sym]) -> HashSet<Sym> {
    let mut relevant: HashSet<Sym> = params.iter().copied().collect();
    let mut frontier: Vec<Sym> = params.to_vec();
    while let Some(n) = frontier.pop() {
        for n_prime in h.successors_of(n) {  // points-to target, or lseg's end symbol
            if relevant.insert(n_prime) { frontier.push(n_prime); }
        }
    }
    relevant
}

fn slice(h: &AbsHeap, params: &[Sym]) -> (AbsHeap /* R */, AbsHeap /* I */) {
    let rel = relevant_names(h, params);
    h.partition_terms(|term| term.names().all(|n| rel.contains(&n)))
}
```

Set $h^\sharp_{in,f} = R[p_0,\ldots,p_k](O(t^\sharp_{pars}))$ (the callee-relevant footprint) and $h^\sharp_{rem} = I[p_0,\ldots,p_k](O(t^\sharp_{pars}))$ (the remainder, preserved untouched by the call).

**Why relevance slicing, and not just projection, matters (Key Question territory):** if the coverage test in Step 3 ran directly against the whole $O(t^\sharp_{pars})$ instead of just $h^\sharp_{in,f}$, the summary would need to account for every variable visible at the call site — including ones $f$ never reads — which means two calls to the *same* function with *identical* relevant arguments but *different* irrelevant local variables would spuriously fail coverage, forcing needless summary recomputation. Slicing is what makes the summary genuinely reusable *across* call sites with different surrounding state, which is the entire premise of a modular analysis.

### Step 3 — coverage test

$$h^\sharp_{in,f} \sqsubseteq_H h^\sharp_f$$

using the sound abstract-state inclusion test $\sqsubseteq_H$ (built, as Chapter 6's synthesis noted, on the same rewriting vocabulary as $\sqcap$). If this holds, the existing summary already accounts for every concrete state that could reach $f$'s body in this call's context, and the analysis can go straight to application. If it doesn't hold, Section 7.2's recomputation path (below) fires first.

### Step 4a — summary application (the covered case)

$$delV_T^\sharp[p_0,\ldots,p_k]\big(comp^\sharp(t^\sharp_{pars},\; t^\sharp_f *_T Id(h^\sharp_{rem}))\big)$$

Unpack this from the inside out: $t^\sharp_f *_T Id(h^\sharp_{rem})$ pairs the callee's known effect on the relevant fragment with an explicit *identity* on the remainder — a formal statement that everything the call analysis sliced away as irrelevant is provably untouched. $comp^\sharp$ (Chapter 6) then sequences the parameter-passing transformation with this combined effect — this is composition doing real interprocedural work, not just intraprocedural sequencing. Finally $delV_T^\sharp$ drops the now-irrelevant formal parameters from the output, since they go out of scope on return.

**Worked example (Example 9).** With the `append` context summary from Example 3 ($h^\sharp = \&l_0 \mapsto \alpha_0 *_S lseg(\alpha_0,\alpha_1) *_S \alpha_1 \cdot n \mapsto 0x0 *_S \&l_1 \mapsto \alpha_2 *_S list(\alpha_2)$, $t^\sharp$ as in Example 2) and a call `append(a,b)` where `c` is untouched, projection and slicing yield exactly $h^\sharp_{in,f}$ included in $h^\sharp$ — so coverage succeeds — and composition with the summary produces a transformation that correctly threads `a`'s and `b`'s effect while leaving `&c ↦ α3` completely alone via the $Id$ conjunct. This is the concrete payoff: `c` never had to be reasoned about at all, precisely because relevance slicing excluded it upstream.

### Step 4b — new-summary inference (the uncovered case, Section 7.2)

When $h^\sharp_{in,f} \sqsubseteq_H h^\sharp_f$ fails, the algorithm doesn't just discard the old summary — it **generalizes** it:

$$h^\sharp_f \leftarrow h^\sharp_f \triangledown_H h^\sharp_{in,f} \qquad\qquad t^\sharp_f \leftarrow [\![C]\!]^{T\sharp}\big(Id(h^\sharp_f \triangledown_H h^\sharp_{in,f})\big)$$

Widen the precondition (state-level widening $\triangledown_H$) to a new abstract heap general enough to cover both the previously-known context and the new one, then *reanalyze the callee body from scratch* — invoking Chapter 5's own $[\![C]\!]^{T\sharp}$ machinery, starting from $Id$ of the newly-widened precondition. Once this new summary is installed, by construction it satisfies the coverage test (the new $h^\sharp_f$ is, by definition of widening, a superset-in-concretization of $h^\sharp_{in,f}$), so application proceeds exactly as in Step 4a.

The full algorithm, as the paper lays it out (Figure 7):

```
Data: existing context summary (h_f#, t_f#) for f
Data: input transformation t_pre# (computation before the call)
Result: output transformation t_post#
Result: possibly-updated context summary for f

1  t_pars# <- [p_k=x_k]  o ... o [p_0=x_0]  o newV#[p0..pk] (t_pre#)
2  h_in,f#  <- R[p0..pk](O(t_pars#))
3  h_rem#   <- I[p0..pk](O(t_pars#))
4  if not (h_in,f# ⊑_H h_f#) then
5      h_f# <- h_f# ∇_H h_in,f#
6      t_f# <- [[C]]^T#( Id(h_f#) )
7  end
8  t_post# <- delV#[p0..pk]( comp#( t_pars#, t_f# *_T Id(h_rem#) ) )
```

Note that lines 5–6 fire whenever coverage fails, and line 8 (application) always runs afterward — the "recompute" branch is a *prelude* to application, not an alternative to it. This is also why every procedure's very first analyzed call necessarily takes the recompute branch: context summaries start at $(\bot,\bot)$, which trivially fails any coverage test.

### Theorem 3 — soundness of the whole call analysis

Given the algorithm's output $t^\sharp_{post}$ for a call to $f$ with input $t^\sharp_{pre}$, and the resulting updated context summary $(h^\sharp_f, t^\sharp_f)$: for any concrete $(\sigma_0,\sigma_1,\nu) \in \gamma_T(t^\sharp_{pre})$, any concrete parameter-passing result $\sigma_1'$, any concrete body execution $\sigma_2' \in [\![C]\!]^T(\{\sigma_1'\})$, and any concrete return state $\sigma_2 \in delV[\ldots](\{\sigma_2'\})$:

$$(\sigma_0,\sigma_2,\nu) \in \gamma_T(t^\sharp_{post}) \;\wedge\; (\sigma_1',\nu) \in \gamma_H(h^\sharp_f) \;\wedge\; (\sigma_1',\sigma_2',\nu) \in \gamma_T(t^\sharp_f)$$

Three separate claims bundled into one theorem, and it's worth naming all three: (1) the returned post-transformation is a sound over-approximation of the call's effect on the *caller's* side; (2) the updated summary's precondition really does account for this call's entry state; (3) the updated summary's transformation really is sound relative to that entry state. Claim (1) is "the immediate answer is right"; claims (2)–(3) are "the summary I'm caching for next time is still a valid summary" — soundness of the *cache*, not just soundness of the *query*. The paper notes this also entails Equation 1 (Chapter 5's soundness statement) specifically for procedure calls, closing the gap between the intraprocedural and interprocedural soundness stories.

## Recursive calls: fixpoint iteration on summaries

The paper handles recursion by extending, not replacing, Figure 7's algorithm — this is presented informally (full formalization is left out as "significantly heavier") but the mechanism is precise:

- **On encountering a recursive call whose context isn't covered** (line 4 evaluates false): widen $h^\sharp_f$ as before, but *use the current $t^\sharp_f$ directly* rather than reanalyzing the body immediately — you can't reanalyze a body you're still in the middle of analyzing.
- **At the end of one pass through the body**, widen the resulting $t^\sharp_f$ against its *previous* value, and iterate the whole body analysis again, until $t^\sharp_f$ stabilizes.

This is textbook fixpoint iteration, just lifted to operate over *pairs* — $(h^\sharp_f, t^\sharp_f)$ jointly, rather than over a single abstract state as in ordinary loop analysis. And that's exactly why widening has to apply to **both** components independently: widening only $h^\sharp_f$ would guarantee the precondition stabilizes but leaves nothing forcing $t^\sharp_f$ itself to converge (a recursive call could keep discovering "one more level of unfolding" in the *transformation* even after the precondition stopped changing); widening only $t^\sharp_f$ has the symmetric gap on the precondition side. Convergence needs both widenings pulling their own component toward a fixpoint simultaneously.

## Worked example: summary generalization across calls (Example 10)

Consider `append(a,b); append(a,c);` where `a`, `b`, `c` start as length-1 lists, analyzed starting from the empty summary $(\bot,\bot)$ for `append`:

1. **First call.** No summary exists, so line 4's coverage test trivially fails; the algorithm computes a fresh context summary $(h^\sharp, t^\sharp)$ whose precondition assumes the *first* argument is exactly one cell: $h^\sharp \approx \&l_0 \mapsto \alpha_0 *_S \alpha_0 \cdot n \mapsto 0x0 *_S \&l_1 \mapsto \alpha_1 *_S \ldots$.
2. **Second call.** By now `a` has grown to length 2 (the first `append` extended it). This context's $h^\sharp_{in,f}$ describes a two-cell first argument, which does **not** satisfy $\sqsubseteq_H$ against the length-exactly-1 precondition from step 1 — coverage fails again. The algorithm widens: $h^\sharp \triangledown_H h^\sharp_{in,f}$ produces a precondition of the form $\&l_0 \mapsto \alpha_0 *_S lseg(\alpha_0,\alpha_1) *_S \alpha_1 \cdot n \mapsto 0x0 *_S \&l_1 \mapsto \alpha_1 *_S \ldots$ — the first argument generalized from "exactly one cell" to "a segment of unknown length," via a genuine `lseg` summary predicate rather than a fixed-size fact.

The paper's own closing remark on this example is instructive: even this widened summary may still be less general than what Example 9 used (an already-fully-generalized `lseg`-based precondition) — generalization is incremental, driven by whatever contexts have actually been observed so far, and may need further widening at later call sites before it stabilizes to its most general useful form. This is the concrete texture behind Chapter 8's later observation that most procedures need only a handful of recomputations (e.g. `Fcons`: 3 recomputations against 44 reuses) — summaries tend to generalize quickly and then get reused heavily, which is precisely this widening process converging fast in practice.

## Where this leads

```
Ch. 4  context summary (h_f#, t_f#)         <- the object being maintained/looked up
Ch. 5  [[C]]^{T#}                            <- reinvoked on line 6 to recompute t_f#
Ch. 6  comp#, sqcap (-> sqsubseteq_H)        <- line 8 application; line 4 coverage test
        |         \
        v          v
Ch. 7  Modular interprocedural call analysis (Figure 7)
        |
        v
Ch. 8  Experimental evaluation: measures how well this converges in practice
       (#recomp vs. #reuse; 14.2s vs. 877.1s on the Emacs benchmark)
```

This chapter is the paper's synthesis point — every prior formal device (transformations, context summaries, composition, intersection/inclusion, widening) reappears here as a *line in an algorithm*, not as an abstract definition. For the standing project, this is a directly transferable blueprint for **Static Analysis & Abstract Interpretation** (`static-analysis`): it's a concrete, soundness-proved recipe for turning per-function analysis results into cacheable, composable Hoare-style contracts — precisely the shape your compiler's automated Hoare-contract / Horn-clause invariant generation will need, since a context summary $(h^\sharp_f, t^\sharp_f)$ *is* a `requires`/`ensures` pair with an explicit domain of validity, generalized on demand rather than fixed up front. The relevance-slicing step is also a clean, minimal instance of the workbench's recurring **Galois Connection, abstract lattices and domain propagation** thread: slicing is exactly "project the abstract domain object down to the sub-lattice actually observable through this interface," which is the same move a modular verifier needs whenever it wants to hide a callee's private state from its public contract. And the fixpoint-over-a-pair mechanism for recursive summaries is a useful cautionary template for any invariant-generation pass in your compiler that needs two co-evolving abstractions (e.g. a precondition lattice and a relational-effect lattice) to converge jointly rather than independently.
