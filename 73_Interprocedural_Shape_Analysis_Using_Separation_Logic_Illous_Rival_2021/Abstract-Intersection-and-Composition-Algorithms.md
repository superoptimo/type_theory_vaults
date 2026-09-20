---
title: Abstract Intersection and Composition Algorithms
source: "Interprocedural Shape Analysis Using Separation Logic-based Transformer Summaries (Illous, Lemerre, Rival, SAS 2020)"
chapter: "Chapter 6, Abstract Composition (pp. 10–13)"
tags: [static-analysis, automated-reasoning, separation-logic, shape-analysis, rewriting-systems, proof-search]
---

[[book-guidelines|↩ Back to guidelines]]

## Why the paper needs two new operators, not one

Chapter 2's Overview already promised two operations on transformations: **application** (run a transformation against a concrete precondition to get a post-condition) and **composition** (sequence two transformations end-to-end to get a summary of "do this, then that"). Chapter 6 is where both get built — but the paper makes a sharp observation first: application is not actually a separate primitive. Applying $t^\sharp$ to an abstract state $h^\sharp$ is exactly the special case of composing $Id(h^\sharp)$ with $t^\sharp$, because $Id(h^\sharp)$ denotes precisely the set of pairs $(\sigma, \sigma)$ described by $h^\sharp$ — "nothing happens, starting from $h^\sharp$." Composing that with $t^\sharp$ sequences "do nothing" then "do $t^\sharp$'s effect," which is just applying $t^\sharp$ to $h^\sharp$.

So the chapter really only needs to define **one** new operator at the transformation level — composition, $\#$ — plus a supporting operator at the state level: **intersection**, $\sqcap$. Intersection turns out to be unavoidable because composition has to match up the *output* description of one transformation against the *input* description of the next, and those two descriptions were derived independently (different call sites, different loop iterations) — they won't be syntactically identical, so "matching them up" is itself a nontrivial reasoning problem over separation-logic-shaped abstract heaps. This is the chapter's central architectural point: **composition is built on top of intersection**, not alongside it.

**What breaks without intersection as a separate step:** if composition tried to match output-vs-input heaps by literal syntactic equality, it would only succeed when a procedure's exact prior output happens to coincide with the exact form of some other procedure's precondition — an accident that essentially never occurs across independently-derived abstract shapes (e.g. one might describe a segment as `lseg(α0,α1)` while the other has already unfolded one cell off it). You need a genuine unification-like reasoning step that recognizes when two structurally different-looking heaps in fact describe overlapping concrete states.

## Abstract intersection: reasoning about overlapping heaps

### The judgment and its reading

The paper defines a ternary relation $h^\sharp_0 \sqcap h^\sharp_1 \sqcap H$, read as: *the intersection of $h^\sharp_0$ and $h^\sharp_1$ may be described by the disjunction of abstract heaps $H$*. The "may be" and the disjunction both matter — unlike concrete set intersection, which is a single answer, abstract intersection is a search problem with potentially several valid (and differently precise) outcomes, because there may be several ways to derive a sound over-approximation.

This is worth pausing on if you're used to Galois-connection-style abstract operators defined as closed-form functions on a lattice: intersection here isn't $f(h^\sharp_0, h^\sharp_1) = h^\sharp_2$, it's a **proof-search relation**, closer in spirit to a resolution procedure in automated theorem proving than to a lattice meet. That's exactly the `automated-reasoning` angle this topic carries: you are, in effect, running a small rewriting-based prover whose goal formula is "these two heaps overlap in region $H$."

### The five rewriting rules (Figure 5)

Each rule is a Horn-clause-shaped inference: premises above the line, conclusion below, read bottom-up as "to intersect the conclusion's two heaps, discharge the premises."

- **$\sqcap_{*_S}$ (local reasoning).** Given $(h^\sharp_{0,0} *_S h^\sharp_{0,1})$ and $(h^\sharp_{1,0} *_S h^\sharp_{1,1})$, if you can intersect the two "left halves" (getting $H_0$) and the two "right halves" (getting $H_1$) independently, the whole intersection is the pointwise conjunction $\{h^\sharp_0 *_S h^\sharp_1 \mid h^\sharp_0 \in H_0, h^\sharp_1 \in H_1\}$. This is separation logic's frame-rule spirit showing up inside an *analysis* operator, not just inside program-logic proof rules: because $*_S$ demands disjoint regions, reasoning about disjoint sub-heaps really can be done independently and then recombined.
- **$\sqcap_=$ (identical-term shortcut).** If $h^\sharp$ is a basic term (`emp`, a points-to fact $n \cdot f \mapsto n'$, or a summary `list`/`lseg`) and both arguments are syntactically the same such term, the intersection is trivially that term itself — $h^\sharp \sqcap h^\sharp \sqcap \{h^\sharp\}$.
- **$\sqcap_{[l,s]}$ (list-vs-segment structural match).** If one side is `list`$(\alpha_0)$ and the other decomposes as `lseg`$(\alpha_0,\alpha_1) *_S h^\sharp_1$, and you can recursively intersect `list`$(\alpha_1)$ with $h^\sharp_1$ to get $H$, then the whole thing intersects to $\{lseg(\alpha_0,\alpha_1) *_S h^\sharp \mid h^\sharp \in H\}$ — intuitively, "a complete list starting at $\alpha_0$ certainly contains a segment up to $\alpha_1$ plus whatever's left, since a segment is a prefix of a list."
- **$\sqcap_{[s,s]}$ (segment-vs-segment structural match).** Symmetric reasoning for two segments sharing a start point but ending differently ($\alpha_2 \neq \alpha_1$): `lseg`$(\alpha_0,\alpha_2)$ against `lseg`$(\alpha_0,\alpha_1) *_S h^\sharp_1$ recurses into intersecting `lseg`$(\alpha_1,\alpha_2)$ with $h^\sharp_1$.
- **$\sqcap_\sqcap$ (forced unfolding).** When neither structural rule applies directly — $h^\sharp_0$ contains a summary at $\alpha_0$ but $h^\sharp_1$ carries no summary there — the rule falls back to unfolding $h^\sharp_0$ one step via $\to_{U[\alpha_0]}$ (the same relation from Chapter 3) and retrying intersection on the unfolded form. This is the rule that guarantees the search always has *somewhere to go*: structural matching alone would get stuck the moment representations diverge even slightly; unfolding lets the proof search "zoom in" until a match becomes visible.

**Rust framing.** This reads naturally as a small proof-search function over an enum:

```rust
enum AbsHeap { Emp, PointsTo(Sym, Field, Sym), List(Sym), Lseg(Sym, Sym), Star(Box<Self>, Box<Self>) }

// Returns one or more sound over-approximations of the intersection (a disjunction).
fn intersect(h0: &AbsHeap, h1: &AbsHeap) -> Vec<AbsHeap> {
    // sqcap_= : identical basic terms
    if h0.is_basic_term() && h0 == h1 { return vec![h0.clone()]; }
    // sqcap_*S : local/independent reasoning on disjoint sub-heaps
    if let (AbsHeap::Star(a0, a1), AbsHeap::Star(b0, b1)) = (h0, h1) {
        let h_left = intersect(a0, b0);
        let h_right = intersect(a1, b1);
        return cartesian_star(h_left, h_right);
    }
    // sqcap_[l,s] / sqcap_[s,s]: structural list-vs-segment matching (elided)
    // sqcap_sqcap : fall back to unfolding one summary and retrying
    if let Some(unfolded) = try_unfold_one_summary(h0) {
        return intersect(&unfolded, h1);
    }
    vec![] // proof search failed to find a derivation
}
```

### Definition 3 and Theorem 1: the algorithm and its guarantee

$inter^\sharp$ is the *partial function* obtained by running proof search over Figure 5's rules (up to a standard, unshown commutativity rule) on a specific pair $(h^\sharp_0, h^\sharp_1)$. It's explicitly **partial**: the rule system doesn't cover every case, and when the search fails to find a derivation, the algorithm just returns either input argument unchanged, which remains sound (a trivially safe, maximally imprecise fallback) but loses precision.

**Theorem 1 (soundness of abstract intersection):**
$$\gamma_H(h^\sharp_0) \cap \gamma_H(h^\sharp_1) \subseteq \gamma_H(inter^\sharp(h^\sharp_0, h^\sharp_1))$$

This is the standard abstract-interpretation soundness shape — the abstract operator's concretization over-approximates the concrete operation — but notice what makes it nontrivial here: it has to hold *for every possible derivation* the rewriting system might produce, since the rules don't determine a unique proof. That's why the paper is candid that the result can differ depending on rule-application order (e.g. $\sqcap_{*_S}$ can split the same heap into different left/right halves, changing what's derivable), and why their actual implementation follows a *precision-oriented strategy* — favoring $\sqcap_=$ wherever possible — rather than an arbitrary search order. Soundness is unconditional; precision is a heuristic on top of it.

### Worked example (Example 6)

$$h^\sharp_0 = \&x \mapsto \alpha_0 *_S \&y \mapsto \alpha_2 *_S lseg(\alpha_0,\alpha_2) *_S \alpha_2 \cdot n \mapsto \alpha_3 *_S list(\alpha_3)$$
$$h^\sharp_1 = \&x \mapsto \alpha_0 *_S \&y \mapsto \alpha_2 *_S lseg(\alpha_0,\alpha_1) *_S \alpha_1 \cdot n \mapsto \alpha_2 *_S list(\alpha_2)$$

$inter^\sharp(h^\sharp_0,h^\sharp_1)$ returns $\&x \mapsto \alpha_0 *_S \&y \mapsto \alpha_2 *_S lseg(\alpha_0,\alpha_1) *_S \alpha_1 \cdot n \mapsto \alpha_2 *_S \alpha_2 \cdot n \mapsto \alpha_3 *_S list(\alpha_3)$ — derived via rule $\sqcap_{[s,s]}$ plus an unfolding step. Notice the result is **strictly more precise than either input**: $h^\sharp_0$ said "the segment from $x$ to $y$ might be empty," $h^\sharp_1$ said "the list from $y$ onward might be empty," but their conjunction pins down that the segment is *non-empty* (it has at least the cell at $\alpha_1$) *and* the tail from $y$ is *non-empty* too (at least $\alpha_2 \cdot n \mapsto \alpha_3$). This is the paper's own evidence that intersection isn't just bookkeeping — genuinely combining two independently-derived heap descriptions can sharpen the analysis's knowledge exactly where a naive "just keep both" join-style operator would not.

## Abstract composition: sequencing transformations

### The judgment

Composition mirrors intersection's shape exactly: $t^\sharp_0 \# t^\sharp_1 \# T$ means "applying $t^\sharp_0$ then $t^\sharp_1$ can be over-approximated by some member of disjunction $T$." Read $\#$ as sequential composition — "first do the effect $t^\sharp_0$ describes, then do the effect $t^\sharp_1$ describes."

### The rewriting rules (Figure 6)

- **$\#_{*_T}$ (local reasoning at the transformation level).** Same structure as $\sqcap_{*_S}$: if $(t^\sharp_{0,0} *_T t^\sharp_{0,1})$ composes with $(t^\sharp_{1,0} *_T t^\sharp_{1,1})$ componentwise, combine the pieces. This is what lets composition scale to large heaps without re-deriving everything monolithically each time — the transformation-level separating conjunction earns its keep here.
- **$\#_{Id}$ (matching identities).** $Id(h^\sharp_0) \# Id(h^\sharp_1)$ reduces to *intersecting* the two preserved regions: if nothing changed on either side, composing them still changes nothing, but you need $\sqcap$ to reconcile the two (possibly differently-phrased) descriptions of "what's preserved." This is the clearest illustration of "composition is built on intersection."
- **$\#_{\dashrightarrow}$ (matching modifications).** $[h^\sharp_{0,i} \dashrightarrow h^\sharp_{0,o}] \# [h^\sharp_{1,i} \dashrightarrow h^\sharp_{1,o}]$ requires the *output* of the first, $h^\sharp_{0,o}$, to intersect nontrivially ($H \neq \emptyset$) with the *input* of the second, $h^\sharp_{1,i}$ — that's the handoff point — and the result chains straight through: $[h^\sharp_{0,i} \dashrightarrow h^\sharp_{1,o}]$, discarding the intermediate state entirely, exactly as function composition $g \circ f$ discards $f$'s codomain once you've used it to feed $g$.
- **$\#_{Id,\dashrightarrow,l}$ (mixed identity/modification).** Handles the case where the first transformation preserved a region that the second one modifies: intersect $h^\sharp_0$ against $h^\sharp_{1,i}$, then re-tag the result as the input side of the modification. A symmetric right-version ($\#_{Id,\dashrightarrow,r}$) handles the mirror case and is elided from the figure for brevity.
- **$\#_{weak,Id,l}$ and $\#_{weak,*_T,l}$ (weakening rules).** These are the rules that make matching possible when the two sides are structured *differently* even though they describe compatible effects:
  - $\#_{weak,Id,l}$ rewrites $Id(h^\sharp_0) *_T [h^\sharp_{0,i} \dashrightarrow h^\sharp_{0,o}]$ into the single merged modification $[(h^\sharp_0 *_S h^\sharp_{0,i}) \dashrightarrow (h^\sharp_0 *_S h^\sharp_{0,o})]$, using the semantic inclusion $\gamma_T(Id(t^\sharp)) \subseteq \gamma_T([t^\sharp \dashrightarrow t^\sharp])$ — an $Id$ is *always* a special case of a $[\dashrightarrow]$ that happens not to change anything, so it's always sound to view it that way, you just lose the "definitely unchanged" information that $Id$ carried.
  - $\#_{weak,*_T,l}$ merges two separate $[\dashrightarrow]$ conjuncts under $*_T$ into one combined $[(h^\sharp_{0,i} *_S h^\sharp_{1,i}) \dashrightarrow (h^\sharp_{0,o} *_S h^\sharp_{1,o})]$ — collapsing structure that was tracked separately into one coarser modification.
- **$\#_{unf,l}$ (unfolding to enable a match).** Exactly parallel to $\sqcap_\sqcap$: if $t^\sharp_0$ contains an unresolved `list`/`lseg` term blocking a match, unfold it one step ($\to_{U[\alpha_0]}$) and retry.

Every "$l$" rule has an unshown, systematically-derivable "$r$" mirror, so the rule set is really doubled in practice but singled in presentation.

### Definition 4 and Theorem 2

$comp^\sharp$, like $inter^\sharp$, is a *partial function* computed by proof search over Figure 6, again up to commutativity, again with implementation-level precision heuristics (maximize use of $\#_{Id}$, the most information-preserving rule, before falling back to weakening).

**Theorem 2 (soundness of abstract composition):** given $comp^\sharp(t^\sharp_0, t^\sharp_1)$ evaluating to $T$,
$$(\sigma_0,\sigma_1,\nu) \in \gamma_T(t^\sharp_0) \wedge (\sigma_1,\sigma_2,\nu) \in \gamma_T(t^\sharp_1) \implies \exists t^\sharp \in T,\ (\sigma_0,\sigma_2,\nu) \in \gamma_T(t^\sharp)$$

Same shape as Theorem 1, transported one level up: any two concrete runs that chain through a shared intermediate state $\sigma_1$ *under the same valuation* $\nu$ are captured by some element of the returned disjunction.

### Worked example: list reversal (Example 7)

The in-place reverse loop body `c = l->n; l->n = x; x = l; l = c;` is analyzed statement-by-statement in Chapter 5's style, giving two transformations for the first two statements:

$$t^\sharp_0 = Id(\&l \mapsto \alpha_0 *_S \alpha_0 \cdot n \mapsto \alpha_1 *_S \&x \mapsto \alpha_2 *_S list(\alpha_1) *_S list(\alpha_2)) *_T [(\&c \mapsto \alpha_3) \dashrightarrow (\&c \mapsto \alpha_1)]$$
$$t^\sharp_1 = Id(\&l \mapsto \alpha_0 *_S \&x \mapsto \alpha_2 *_S \&c \mapsto \alpha_1 *_S list(\alpha_1) *_S list(\alpha_2)) *_T [(\alpha_0 \cdot n \mapsto \alpha_1) \dashrightarrow (\alpha_0 \cdot n \mapsto \alpha_2)]$$

Composing $t^\sharp_0 \# t^\sharp_1$ requires the weakening rules to line up terms that sit under $Id$ in one transformation but under $[\dashrightarrow]$ in the other, and produces:

$$Id(\&l \mapsto \alpha_0 *_S \&x \mapsto \alpha_2 *_S list(\alpha_1) *_S list(\alpha_2)) *_T [(\&c \mapsto \alpha_3) \dashrightarrow (\&c \mapsto \alpha_1)] *_T [(\alpha_0 \cdot n \mapsto \alpha_1) \dashrightarrow (\alpha_0 \cdot n \mapsto \alpha_2)]$$

The paper's own gloss is important: this is a *very precise* account of the two-statement sequence, and it demonstrates that composition isn't only for interprocedural summaries — it can substitute for ordinary sequential statement-by-statement intraprocedural analysis too. Chapters 5 and 6 aren't really separate machines; composition is a strictly more general operation that subsumes the sequencing step of the intraprocedural pass.

### Worked example: application-as-composition (Example 8)

With $t^\sharp$ the `append` summary and $h^\sharp$ a pre-state where the caller's segment happens to be terminated ($\alpha_3 = 0x0$), $Id(h^\sharp) \# t^\sharp$ returns exactly the post-state a state-based shape analysis would compute directly. This closes the loop on the chapter's opening claim: application really is nothing but composition with an $Id$-wrapped state.

## The proof-search character of both operators — why this is also `automated-reasoning`

Step back and look at the shape of $\sqcap$ and $\#$ together: both are relations (not functions) defined by a small set of Horn-clause-style rewriting rules, computed by proof search up to some equivalence (commutativity, here), partial (the algorithm can fail to find a derivation and falls back to a conservative default), and non-confluent (different rule-application orders yield different, differently-precise answers, so the implementation needs a deliberate *strategy*, not just "run the rules"). That is structurally the same problem shape as a resolution-based prover choosing a clause-selection strategy, or a unification algorithm choosing which occurs-check/decomposition order to apply first. If you squint, $\sqcap_=$ is playing the role that syntactic unification's "identical terms" base case plays in a unifier, and $\sqcap_\sqcap$'s forced unfolding is playing the role that a "expand a definition when stuck" step plays in proof search over inductively-defined predicates. This is precisely why the book's own guidelines tag this topic under both `static-analysis` and `automated-reasoning`: the *operator* is doing abstract-interpretation work (soundly over-approximating concrete intersection/composition), but the *algorithm* that computes it is doing classical proof-search work (rewriting toward a goal, backtracking, forced expansion to unstick a derivation).

For the standing project this dual character is worth naming explicitly. Your CSP kernel's job — searching for concrete counterexamples via domain/lattice propagation, including over automata/DFA-shaped abstract data-structure domains — is structurally close to what $\sqcap_\sqcap$ and $\#_{unf,l}$ are doing here: both are "unfold/expand an inductively-summarized domain object just enough to make a local match possible," which is the same move CEGAR-style refinement makes when an abstract counterexample needs concretizing against a richer domain. And the `automated-reasoning` thread on **proof search, clause simplification, and unification of terms** maps almost one-to-one onto this chapter's rewriting systems: $\sqcap$/$\#$ are, in effect, two custom unification-like procedures specialized to separation-logic-shaped terms rather than first-order terms — worth remembering when you design your own theorem prover's clause/resolution engine, since "which structural matching rule fires, and when do you fall back to expanding an inductive definition" is exactly the kind of strategy decision you'll face there too.

## Where this leads

```
Ch. 5 Intraprocedural analysis
   produces t# per procedure body
        |
        v
Ch. 6 Abstract intersection (sqcap)  ---is used inside--->  Abstract composition (#)
   (state-level: reconciling             (rules #_Id, #_Id,->,l all
    two independently-derived              invoke sqcap internally)
    heap descriptions)
        |                                        |
        +----------------- both feed ------------+
                             |
                             v
                Ch. 7 Interprocedural analysis:
                - coverage test (sqsubseteq_H, built from sqcap machinery)
                - summary application = comp#(t_pars, t_f *_T Id(h_rem))
                - sequencing a call's effect with surrounding code
```

Composition is the linchpin operator the whole modular, top-down interprocedural protocol (Chapter 7) is assembled from: applying an existing summary at a call site, and sequencing a callee's effect with the caller's surrounding code, are both literally invocations of $comp^\sharp$. Intersection, in turn, is composition's own internal dependency — every time two independently-phrased heap fragments need to be reconciled, whether inside $\#_{Id}$'s matching-identities case or inside Chapter 7's context-summary coverage test, $\sqcap$ (or the closely related inclusion test $\sqsubseteq_H$ built on the same rule vocabulary) is what does the reconciling. This chapter is therefore the one place in the paper where "the theory" (Chapters 3–4's definitions) turns into "the algorithm" (something you could actually implement as proof search) — which is exactly why it carries both Focus Areas: it's abstract interpretation's soundness discipline wrapped around automated reasoning's proof-search machinery.
