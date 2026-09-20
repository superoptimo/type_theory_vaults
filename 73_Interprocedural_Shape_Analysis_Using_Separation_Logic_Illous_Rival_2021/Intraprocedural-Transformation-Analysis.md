---
title: Intraprocedural Transformation Analysis
source: "Interprocedural Shape Analysis Using Separation Logic-based Transformer Summaries (Illous, Lemerre, Rival, SAS 2020)"
chapter: "Chapter 5, Intraprocedural Analysis (pp. 9–10), with grounding from Chapter 4 (Definitions 1–2) and Chapter 2 (Overview example)"
tags: [static-analysis, abstract-interpretation, separation-logic, shape-analysis, widening]
---

[[book-guidelines|↩ Back to guidelines]]

## Why analyze *transformations* instead of states?

Ordinary abstract interpretation walks a command $C$ forward over an abstract **state**: you have an abstract heap $h^\sharp$ describing "what might be true right now," and each statement rewrites it into a new abstract heap describing "what might be true after." That's the standard shape-analysis recipe — and it works fine *inside* one procedure, in isolation.

The trouble starts the moment you want to reuse the result of analyzing a procedure body across several call sites. A state-based analysis only ever produces a post-state relative to *one specific* input state. If you want a reusable summary, you need something that describes the whole *input → output relation* of the code, not a single point evaluated at one precondition. That's exactly what the paper's abstract transformations $t^\sharp$ are for (built up in Chapter 3 out of $Id(h^\sharp)$, $[h^\sharp_i \dashrightarrow h^\sharp_o]$, and the transformation-level separating conjunction $*_T$) — and Chapter 5 is where the paper shows you *compute* them: not by running a state analysis and packaging the result afterward, but by literally doing the forward abstract interpretation directly on the transformation object itself.

**What breaks without this:** if you abstractly interpreted states and only converted to a transformation at the very end, you'd lose the fine-grained information about *which* fragment of the heap was touched and which was passed through untouched — precisely the information a caller needs to compose this procedure's effect with what came before and what comes after. Chapter 6 (abstract composition) later depends on transformations carrying that structure all the way through the analysis, not just at the boundary.

## The core idea: the transformer takes a transformation, not a state

The abstract semantics of a command $C$, written $[\![C]\!]^{T\sharp}$, has type $T \to T$ — it consumes an abstract transformation describing *everything computed so far* (from the procedure's entry up to the point just before $C$), and produces a new transformation that additionally covers $C$'s effect.

The book's own framing is worth sitting with: the input to $[\![C]\!]^{T\sharp}$ can be viewed as **the dual of a continuation**. A continuation says "here's what happens *after* this point"; here, the argument says "here's everything that happened *before* this point, all the way back to entry." The transformer's job is to extend that backward-looking summary by one more command.

This is why the whole intraprocedural pass produces one running $t^\sharp$ per program point, threaded forward, rather than a state $h^\sharp$: by the time you exit the procedure, that single $t^\sharp$ *is* the candidate global summary (Chapter 4's $Id/[\dashrightarrow]$-shaped $t^\sharp$, over-approximating $[\![C]\!]^T$).

### Soundness: Equation 1

The paper pins this down formally. For any abstract transformation $t^\sharp$:

$$\forall (\sigma_0, \sigma_1, \nu) \in \gamma_T(t^\sharp),\; \sigma_2 \in M,\; (\sigma_1, \sigma_2) \in [\![C]\!]^T \implies (\sigma_0, \sigma_2, \nu) \in \gamma_T([\![C]\!]^{T\sharp}(t^\sharp)) \tag{1}$$

Read it left to right: if $t^\sharp$ already soundly describes some concrete run from $\sigma_0$ to $\sigma_1$ (under valuation $\nu$), and $C$'s *concrete* semantics can carry $\sigma_1$ to $\sigma_2$, then the *new* transformation — $[\![C]\!]^{T\sharp}$ applied to $t^\sharp$ — must soundly describe the composite run from $\sigma_0$ all the way to $\sigma_2$, under the *same* valuation $\nu$. That last clause matters: $\nu$ is not re-derived, it's carried through, which is exactly what lets the transformation-level abstraction stay relational across the whole procedure instead of collapsing into a sequence of disconnected snapshots.

**Rust framing.** If you were implementing this as a compiler pass, Equation 1 is precisely the contract you'd put on a fold:

```rust
// Each command's abstract transformer refines the running summary.
// `AbsTransform` is roughly: Id(AbsHeap) | InOut(AbsHeap, AbsHeap) | Star(Box<Self>, Box<Self>)
trait AbstractTransformer {
    // Soundness contract (Eq. 1): for every concrete (sigma0, sigma1, nu) captured
    // by `acc`, and every (sigma1, sigma2) in this command's concrete semantics,
    // the returned transformation must capture (sigma0, sigma2, nu).
    fn apply(&self, acc: AbsTransform) -> AbsTransform;
}

fn analyze_body(cmds: &[Command], entry: AbsHeap) -> AbsTransform {
    cmds.iter().fold(AbsTransform::Id(entry), |acc, cmd| cmd.transformer().apply(acc))
}
```

The `fold` is the whole intraprocedural analysis in miniature: start from $Id(h^\sharp_{entry})$ (nothing has happened yet, so input equals output), and thread the accumulator through each command's transformer. Contrast this with a state-based `fold` that would carry an `AbsHeap` accumulator instead — you'd get the final heap, but you'd have thrown away the "what's preserved vs. what's touched" structure that composition needs later.

## Localization and mutation: how assignment actually gets analyzed

The mechanics for a concrete statement make the abstract picture concrete. Consider the assignment `x -> n = y` (writing the value of `y` into the `n`-field of the cell `x` points to), analyzed against a pre-transformation $t^\sharp$.

**Step 1 — localization.** Before you can describe a mutation, you have to find the cell being mutated inside $t^\sharp$'s current shape. The analysis rewrites $t^\sharp$ into a form that exposes both `x` and `y` at the top level:

$$Id(\&x \mapsto \alpha_0 *_S \&y \mapsto \alpha_1) *_T t^\sharp_0 \qquad \text{or} \qquad [(\ldots) \dashrightarrow (\&x \mapsto \alpha_0 *_S \&y \mapsto \alpha_1)] *_T t^\sharp_0$$

and then searches $t^\sharp_0$ for the symbolic name $\alpha_0$ — i.e., for whatever the `x`-cell's pointer field currently describes.

**Step 2 — the two cases.**

- *Cell already exposed.* If $t^\sharp_0$ already contains $Id(\alpha_0 \cdot n \mapsto \alpha_2)$ or $[(\ldots) \dashrightarrow (\alpha_0 \cdot n \mapsto \alpha_2)]$, the analysis just mutates that term in place, producing $[(\ldots) \dashrightarrow (\alpha_0 \cdot n \mapsto \alpha_1)]$ — an $Id$ becomes a genuine $[\dashrightarrow]$ the moment something inside it actually changes.
- *Cell hidden inside a summary.* If instead $t^\sharp_0$ contains $Id(h^\sharp_0)$ or $[(\ldots) \dashrightarrow h^\sharp_0]$ where $h^\sharp_0$ is a `list`$(\alpha_0)$ or `lseg`$(\alpha_0, \ldots)$ predicate, the target cell is folded up inside an inductive summary and can't be mutated directly. The analysis must first **unfold** the summary via the rewrite relation $\to_U$ (from Chapter 3) to peel off one concrete cell, and only then apply the mutation case above.

If localization can't find `x -> n` at all, that's the analysis's signal that the program may be dereferencing an invalid pointer — a genuinely useful side effect of formalizing the search this precisely.

**What breaks without unfolding:** without step 2's fallback, the analysis could only ever mutate cells that happen to already be represented as individual points-to facts. Since real list-manipulating code constantly walks into the middle of a summarized segment, most useful mutations would simply fail to localize. Unfolding is what lets the abstraction "zoom in" on demand.

```python
# Sketch of localization + mutation, illustrative only (not literal comp^# machinery)
def analyze_assignment(t, x, field, y):
    t0 = localize(t, x, y)              # exposes &x -> a0, &y -> a1 at top level
    a0 = symbolic_addr_of(x, t0)
    if not contains_cell(t0, a0, field): 
        t0 = unfold_summary(t0, a0)     # -> peel list(a0)/lseg(a0,...) one step (rewrite ->_U)
    return mutate_cell(t0, a0, field, symbolic_addr_of(y, t0))
```

## Weakening: widening lifted to the transformation level

Loops require widening, same as any abstract-interpretation loop analysis — but here widening, $t^\sharp_0 \triangledown_T t^\sharp_1$, has to operate on transformations, not states, and that means it has two jobs at once.

1. **Commute where possible.** Widening tries to push itself structurally inside $Id$ and $*_T$: if both arguments are $Id(\cdot)$ or both are $*_T$-conjunctions with matching shape, widen the state-level components with the *state*-level widening $\triangledown_H$ and rebuild the same connector.
2. **Weaken otherwise.** Where the shapes don't line up — typically because one loop iteration left something as $Id$ while the next mutated it into $[\dashrightarrow]$ — widening gives up trying to preserve the connector and **weakens** the conjunct into $[h^\sharp_i \dashrightarrow h^\sharp_o]$ form, the least-structured shape that can absorb both possibilities.

Crucially, widening at the transformation level also has to introduce **summary predicates on the state side** (turning finite unfoldings like $\alpha \cdot n \mapsto \alpha' \wedge \ldots$ into `lseg`/`list` predicates) — this is what guarantees the widening sequence actually terminates, exactly as it does for ordinary state-level shape widening. If widening only touched the $Id/[\dashrightarrow]/*_T$ connectors and never introduced summaries, you could keep discovering "one more concrete cell" every iteration forever; the fixpoint would never stabilize.

### Worked example: the `append` loop

Chapter 2's running example is `append` (Figure 1):

```c
void append(list *l0, list *l1) {
  assume(l0 != NULL); list *c = l0;
  while (c->n != NULL) { c = c->n; }
  c->n = l1;
}
```

Chapter 5's Example 5 walks the loop at line 4, tracking only the part of memory reachable from `c`.

- **Before the loop body:** $Id(\&l_0 \mapsto \alpha *_S \&c \mapsto \alpha *_S list(\alpha)) \wedge \alpha \neq 0$. Nothing has happened yet, so this is a pure identity transformation — the whole reachable region is preserved, entry-to-current-point.
- **After one iteration of the body** (`c = c->n` forces unfolding `list(α)` by one cell): $Id(\&l_0 \mapsto \alpha *_S \alpha \cdot n \mapsto \alpha' *_S list(\alpha')) *_T [(\&c \mapsto \alpha) \dashrightarrow (\&c \mapsto \alpha')] \wedge \alpha \neq 0$. Now `c`'s own pointer *has* changed — hence the $[\dashrightarrow]$ conjunct for it — while $l_0$ and everything reachable from the (unfolded, then re-folded) list stays under $Id$.
- **Widening these two** produces $Id(\&l_0 \mapsto \alpha *_S lseg(\alpha,\alpha') *_S list(\alpha')) *_T [(\&c \mapsto \alpha) \dashrightarrow (\&c \mapsto \alpha')] \wedge \alpha \neq 0$ — and this *is* the loop invariant; it already stabilizes at this step. Notice how the single concrete cell $\alpha \cdot n \mapsto \alpha'$ from the second transformation got folded back into the summary predicate $lseg(\alpha, \alpha')$: that's the "introduce a summary predicate" half of weakening doing its termination-guaranteeing work, while the $[\dashrightarrow]$ on `c` stays exactly as precise as it needs to be.

This is a nice miniature of the whole chapter: localization/mutation handles straight-line code, weakening handles the loop, and the two together compute a $t^\sharp$ that (by Equation 1) is a sound description of `append`'s entire loop — ready to become the raw material for a global summary.

## Variable introduction and removal

Two more transfer functions round out the intraprocedural toolkit: $newV_T^\sharp[x_0,\ldots,x_n]$ and $delV_T^\sharp[x_0,\ldots,x_n]$, which respectively add and remove variables $x_0,\ldots,x_n$ from a transformation's *output* state, over-approximating the concrete operations $newV$/$delV$. These look like bookkeeping compared to localization and weakening, but they turn out to be exactly the machinery Chapter 7 needs for parameter passing at a call site (binding formal parameters on entry, dropping them again on return) — a preview of how tightly Chapters 5–7 are meant to fit together.

## Where this leads

```
Ch. 3 (Id / [->] / *_T, gamma_T)         <- vocabulary this chapter computes IN
        |
        v
Ch. 5 Intraprocedural analysis  --produces-->  candidate global summary t#
   (localization, mutation,
    unfolding, weakening)
        |
        v
Ch. 6 Abstract composition (#)   <- needs t# built exactly this way to
   (needs precise Id/[->]/*_T       compose one procedure's t# with another's,
    structure to match rules)        or with a call-site precondition
        |
        v
Ch. 7 Interprocedural analysis   <- reuses newV_T#/delV_T# for parameter passing,
   via function summaries           and calls JCK^{T#} again when a summary
                                     needs to be recomputed (widened precondition)
```

Everything downstream depends on this chapter's central discipline: never abstract away *what changed vs. what didn't* by collapsing to a plain post-state. That discipline is what makes $t^\sharp$ composable at all, and composability is the entire point of the paper — it's the mechanism that lets `double_append` reuse `append`'s summary twice instead of reanalyzing its body twice.

For the standing project, this chapter is a direct, load-bearing illustration of **Static Analysis & Abstract Interpretation** (`static-analysis`): it's abstract interpretation with widening and a soundness invariant (Equation 1), but run over a *relational* domain instead of a plain reachable-states domain — precisely the shape a Hoare-triple / pre-post-condition invariant generator in your compiler will eventually need, since a `requires`/`ensures` contract *is* an input–output relation, not a single reachable-states abstraction. The localization/unfolding mechanism is also a concrete, non-toy instance of "domain propagation with an inductively-summarized domain" — worth keeping in mind alongside the workbench's automata/DFA-shaped abstract-data-structure domains, since inductive summary predicates here play a structurally similar role to states in a DFA-based shape domain.
