---
title: "Case Study: Sound Floating-Point Rewriting"
source: "Better Together: Unifying Datalog and Equality Saturation"
chapter: "6.2 Herbie: Making an EqSat Application Sound"
pages: "17–19"
tags: [datalog, equality-saturation, egglog, e-class-analysis, herbie, floating-point, static-analysis]
---

[[book-guidelines|↩ Back to guidelines]]

## What breaks without sound rewriting

Herbie is a real, widely-deployed tool: give it a floating-point expression, and it searches for an equivalent expression that computes the same mathematical quantity with less rounding error. Under the hood it runs equality saturation — grow an [[The-E-Graph-Data-Structure|e-graph]] of everything the input expression could be rewritten into, then extract the most numerically accurate variant. The rewrite rules Herbie uses are algebraic identities: $a - b \iff -(b-a)$, $\sqrt{x^2} \iff |x|$, and so on. Over the *real numbers* these hold unconditionally. Over *floating-point numbers* they usually do too — rounding error is exactly the small print Herbie exists to manage — but a handful of them silently fail on specific inputs, most commonly division by zero.

Take the rule in Figure 9a of the paper: $\frac{a \cdot b}{c} \iff \frac{a}{c} \cdot b$. This is sound only if $c \neq 0$; apply it blindly and Herbie can rewrite a perfectly well-defined expression into one containing an undefined division. This is not a hypothetical edge case — the paper reports that unsound rules like this one have caused real, repeated bugs in Herbie over its history. The obvious fix — just delete the unsound rules — is not an option: Figure 9b shows a rule derived from the factorization $x^3 - y^3 = (x-y)(x^2+xy+y^2)$, sound whenever $x \neq 0$ or $y \neq 0$, that is *critical* to Herbie's ability to find more accurate programs on a large fraction of its benchmark suite. Deleting it recovers soundness by making Herbie substantially less useful. What Herbie actually needs is a way to apply the rule exactly when its side condition holds — which means it needs to *know*, for every term flowing through the e-graph, whether that term could be zero.

That's an analysis problem, not a rewriting problem: computing safe over-approximations of runtime facts (bounds, sign, non-zero-ness) about program terms as they're derived. And this is precisely where the case study connects back to a structural limit of the classic `egg` architecture, covered in [[The-E-Graph-Data-Structure]]: `egg`'s e-class analyses are single, upward-only, and fused into one monolithic lattice per e-graph. Herbie's original implementation tried to build exactly this kind of soundness analysis on top of `egg` and found it "nearly impossible" — not because the *idea* of interval bounds is hard, but because bolting a second, interacting analysis (non-zero-ness, which needs interval information as an input) onto an architecture built for one analysis at a time has nowhere clean to go.

## Interval analysis: bounding terms compositionally

egglog's answer is to implement the soundness analysis the ordinary way any egglog program implements anything: as functions with merge semantics, populated and refined by rules, running to a fixpoint alongside the rest of the e-graph's rewriting. Figure 10 of the paper shows the core of it — two functions tracking, for every term (e-class) in the e-graph, a conservative lower and upper bound on its real-valued interpretation:

```
(function lo (Math) Rational :merge (max old new))
(function hi (Math) Rational :merge (min old new))
```

This single line is worth pausing on, because it's a direct, concrete use of the [[The-egglog-Language-Model|`:merge` expression]] from earlier in the book. When two different derivations produce two different candidate lower bounds for the *same* e-class — because equality saturation discovered two syntactically different but equal ways to express the term — `:merge` resolves the conflict by taking the tighter of the two bounds (`max` for lower bounds, `min` for upper bounds), rather than erroring out on the functional-dependency violation the way a plain database function would. The interval analysis isn't a special extension egglog had to add — it's an ordinary egglog program that happens to compute intervals, because functions-with-merge already *is* a general mechanism for "combine conflicting facts about the same equivalence class soundly."

Populating the intervals is just ordinary rules querying and asserting facts, e.g. propagating bounds through `sqrt`:

```
(rule ((= e (Sqrt a)))
      ((set (lo e) (rational 0 0))))

(rule ((= e (Sqrt a))
       (= loa (lo a)))
      ((set (lo e) (sqrt loa))))
```

The first rule says: whatever `a` is, the square root of it is at least zero (since `Sqrt` is defined to be non-negative). The second says: once we know a lower bound on the argument `a`, we can push it through the (monotonic) square-root function to get a tighter lower bound on the result. Neither rule needs to know anything about how `a` itself was derived, or about any other analysis running in the same e-graph — this is what "compositional" means concretely. With interval bounds available, egglog can finally apply rules like the one in Figure 9a *conditionally*: a rule's query can check `(!= (lo c) (rational 0 0))` (or the symmetric check on `hi`) as an ordinary query atom, exactly the way any other Datalog-style condition works, gating the rewrite on the side condition it actually needs.

## Not-equals: an analysis built on an analysis

Interval bounds alone aren't enough for every case Herbie needs. The paper's running example is the classic cancellation benchmark $\sqrt[3]{v+1} - \sqrt[3]{v}$: naive floating-point evaluation loses almost all precision here because the two cube roots are very close together, and the rule from Figure 9b — the $x^3 - y^3$ factorization — is exactly the rewrite that fixes it. But that rule's soundness condition is $x \neq 0 \lor y \neq 0$, a *disequality* fact, not directly an interval fact.

egglog's fix is to add a second analysis, "not-equals," built as ordinary egglog rules layered *on top of* the interval analysis and the facts equality saturation itself discovers along the way:

1. The interval analysis proves $\sqrt[3]{v+1} \neq \sqrt[3]{v}$ is implied once intervals show the two arguments' ranges can't overlap in a way that would force equality (informally: if $a$'s interval and $b$'s interval are provably disjoint, $a \neq b$).
2. A not-equals propagation rule — $a \neq b \implies \sqrt[3]{a} \neq \sqrt[3]{b}$ — pushes that fact through the cube-root function, using monotonicity the same way the interval rules did.
3. With $\sqrt[3]{v+1} \neq \sqrt[3]{v}$ now a known fact, the factorization rule's side condition is satisfied, and the rewrite from Figure 9b fires — substituting $\sqrt[3]{v+1}$ for $x$ and $\sqrt[3]{v}$ for $y$ — reducing the expression's error from extremely high to near zero.

The paper is explicit about why this layering matters architecturally, not just as a Herbie implementation detail: in a framework limited to one fused e-class analysis (the `egg` architecture again), interval reasoning and not-equals reasoning would have to be implemented as a *single* combined analysis, with the interaction between "bounds" and "disequality" hard-coded into one lattice and one merge function. In egglog, they're two independent, composable pieces — the not-equals rules simply *query* `lo`/`hi` the way any rule queries any relation, with no special-case plumbing required to let one analysis read another's results. This is the same principle raised in [[Language-Based-System-Design]] about multiple datatypes and analyses coexisting cleanly rather than being crammed into one ad hoc type — here it shows up as multiple *analyses* coexisting cleanly instead of one hand-fused monolith.

## Does soundness actually cost anything?

The natural worry with adding soundness machinery is that it slows things down or makes Herbie worse at its job — that's usually the tradeoff analyses impose. The paper's evaluation, run across Herbie's full benchmark suite of 289 floating-point programs, says the opposite on both counts:

- **Speed:** using egglog's sound analysis instead of the unsound ruleset makes Herbie *faster* overall — 73.91 minutes versus 81.91 minutes across the suite — because the unsound ruleset wastes search time generating and exploring unsound candidate programs that then have to be discarded.
- **Accuracy:** in 104 cases, the sound analysis actually finds a *more* accurate program than the unsound ruleset did; in 135 cases the unsound ruleset still wins (soundness necessarily forecloses some rewrites the unsound version was willing to risk); the remainder are ties. One outlier benchmark — $9x^4 - y^2(y^2-2)$ — the unsound ruleset can't solve at all, while the sound analysis finds a solution via algebraic rearrangement and a fused multiply-add.

In other words: the soundness analysis isn't a tax paid for correctness. It's close to a free win, because the thing it removes — the search cost of exploring rewrites that turn out to be unsound and have to be walked back — was already a real cost the unsound version was quietly paying.

## Where this leads

Both case studies in the book are demonstrations of the same underlying claim from two opposite directions. [[Case-Study-Unification-Based-Points-to-Analysis]] shows a Datalog analysis (Steensgaard's) that needed egglog's fast, canonicalizing equivalence — something plain Datalog struggles to provide efficiently. This case study shows the mirror image: an equality-saturation application (Herbie) that needed egglog's *Datalog-style* composable, multi-analysis rule engine — something the single-analysis `egg` architecture, covered in [[The-E-Graph-Data-Structure]], struggled to provide at all. The `:merge` mechanism from [[The-egglog-Language-Model]] is the specific hinge both analyses in this case study turn on: it's what lets "combine two conflicting facts about the same e-class" be handled uniformly, whether the facts are interval bounds, non-zero witnesses, or (in the points-to case) allocation identities. If you're building a rewriting or optimization system where soundness depends on side conditions the rewriter itself has to prove — a term-rewriting compiler pass, a peephole optimizer with algebraic identities, anything doing equality saturation over a domain with partial functions — this is the concrete argument for treating "prove the side condition" as its own composable analysis layer rather than baking ad hoc guard code into the rewrite rules themselves.
