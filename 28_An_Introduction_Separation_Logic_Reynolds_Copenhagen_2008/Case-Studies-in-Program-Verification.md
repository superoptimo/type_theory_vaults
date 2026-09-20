---
title: "Case Studies in Program Verification"
book: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 1 §1.9; Chapter 4 §4.7; Chapter 6 §6.3–6.4, §6.7"
pages: "26–27, 133–145, 184–198"
tags: [separation-logic, schorr-waite, mergesort, quicksort, sharing, case-studies]
---

# Case Studies in Program Verification

[[book-guidelines|↩ Back to guidelines]]

> **Scope note.** This topic is explicitly cross-chapter in the book's own Topic List, and the four case studies live in four different places: Schorr-Waite's proof sketch is only in the Chapter 1 overview (§1.9, pp. 26–27) — I confirmed the PDF is 204 pages total with no later chapter revisiting it, so this compressed treatment genuinely is everything the book says about Schorr-Waite; mergesort is worked in full in Chapter 4 (§4.7, pp. 133–145); quicksort is worked in full in Chapter 6 (§6.3–6.4, pp. 184–188); and the LISP subset-list program is worked in full in Chapter 6 (§6.7, pp. 192–198). This article synthesizes all four, in the order the book itself increases their difficulty: from a proof sketch of the hardest classical algorithm, to two full, symmetrical sorting proofs, to the single most sharing-heavy case study in the book.

## Why these four, and what they're testing

Every earlier chapter built one piece of machinery — the frame rule, inductive segment predicates, procedures with hypothetical specifications, the iterated conjunction. These case studies are where the book cashes out that machinery against real, historically significant programs, each chosen because it stresses a *different* combination of the tools:

- **Schorr-Waite** stresses separating implication ($\mathbin{-\!*}$) and reasoning about a heap whose links get **reversed in place** during traversal — arguably the hardest classical benchmark for any pointer-reasoning logic, because of cycles, sharing, and destructive mutation all at once.
- **Mergesort** stresses recursive procedures with hypothetical specifications and the discipline of "prove the segment-composition law by using the very program you're verifying."
- **Quicksort** stresses the `array`/iterated-conjunction machinery from the previous chapter, and a genuinely nontrivial termination argument.
- **The subset-list program** stresses characterizing **complex, intentional sharing** — not preventing it (as most of the book does), but proving something precise about a structure that *deliberately* shares substructure to save space.

## Case study 1: the Schorr-Waite marking algorithm (§1.9)

### The problem

Schorr-Waite marks every node reachable from a root in a heap that may contain **arbitrary cycles and sharing**, without using auxiliary storage proportional to the structure's size — the trick (a decades-old classic in pointer algorithms) is to **reverse links as you descend**, using the reversed links themselves as an implicit stack, and restore them as you backtrack. This makes it notoriously difficult to verify: the heap's shape is changing destructively at every step, in a way that must nonetheless be provably restorable to the original shape by the time the algorithm finishes.

### The invariant, read as a story about ownership and restoration

Since this proof (originally Yang's, using the older field-arithmetic-free form of the logic where addresses refer to whole 4-field records) predates the address-arithmetic generalization used elsewhere in the book, records are addressed wholesale, with helper definitions like

$$
\mathrm{allocated}(x) \stackrel{\mathrm{def}}{=} x \mapsto -,-,-,- \qquad \mathrm{noDangling}(x) \stackrel{\mathrm{def}}{=} (x = \mathrm{nil}) \vee \mathrm{allocated}(x)
$$

The main invariant is:

$$
\begin{aligned}
&\mathrm{noDanglingR} \wedge \mathrm{noDangling}(t) \wedge \mathrm{noDangling}(p) \ \wedge \\
&\big(\mathrm{listMarkedNodesR}(\mathit{stack}, p) * (\mathrm{restoredListR}(\mathit{stack}, t) \mathbin{-\!*} \mathrm{spansR}(\mathit{STree}, \mathit{root}))\big) \ \wedge \\
&\big(\mathrm{markedR} * (\mathrm{unmarkedR} \wedge (\forall x.\ \mathrm{allocated}(x) \Rightarrow (\mathrm{reach}(t,x) \vee \mathrm{reachRightChildInList}(\mathit{stack}, x))))\big)
\end{aligned}
$$

This is dense, but every piece maps onto a concrete part of the algorithm's state, and the whole thing is best read as **three separate claims, conjoined**:

1. **Sanity** — nothing dangles: every allocated record's child fields are either `nil` or point at another allocated record.
2. **The reversibility claim, using `−∗` as its central device.** At any point mid-traversal, there is a "spine" — the path from `root` down to the current node `t` — whose links have been **reversed** (so that following them now leads back toward `root`, not forward). The abstract ghost variable `stack` records exactly the information needed to reconstruct this spine. `restoredListR(stack, t)` describes the *hypothetical* state where the spine has been put back the right way round; `listMarkedNodesR(stack, p)` describes the *actual*, currently-reversed state. The separating implication then says: **if you (hypothetically) extend the current heap with a spine restored to its original orientation, the result has the same spanning tree (`STree`) as the structure had at the very start.** This is exactly what $-\!*$ is for: it lets the invariant talk about a heap that *doesn't currently exist* (the restored spine) as a proof-relevant hypothetical, without the invariant needing to actually construct it. Reynolds calls this out explicitly as, to his knowledge, the **first genuinely conceptual use of separating implication in verifying an actual program** — as opposed to its formal role in backward-reasoning rules and weakest preconditions, which is comparatively mechanical.
3. **Partition into marked/unmarked, with a reachability guarantee threaded through the unmarked side.** The heap splits (via `*`) into marked and unmarked records. Every *active* unmarked record is reachable from `t` or from a designated field in the spine — and because this reachability clause sits inside the *unmarked* side of the `*`-partition, **the paths witnessing that reachability must themselves consist entirely of unmarked records.** This is the same trick separating conjunction always plays: a syntactic partition of the assertion becomes a semantic constraint on which addresses can appear in a sub-formula's proof, entirely for free.

### Why this is worth dwelling on

The Schorr-Waite proof is presented as an existence proof of scale, not as a tutorial you're meant to fully reconstruct from two pages — Reynolds's own text says as much ("anyone who has tried to verify this kind of graph traversal ... will appreciate the extraordinary succinctness"). The one idea worth internalizing permanently is: **`−∗` becomes essential exactly when an invariant needs to talk about a heap state that is temporarily not the current one** — here, "the spine as it will look once un-reversed." This is the closest this book comes to a genuinely modal use of separating implication (compare: a Kripke-style "in every future/extended state" reading), and it's the reason $-\!*$ earns its place in the logic beyond being just the right-adjoint that makes currying/decurrying lemmas provable.

## Case study 2: mergesort (§4.7) — recursion on list segments, by length not by shape

### The setup problem: you can't split a list segment "in half" for free

Dividing an *array* in half is $O(1)$ arithmetic on indices; dividing a *linked list segment* in half requires either walking it (which the book avoids by passing lengths explicitly as ghost-adjacent integer parameters) or accepting $O(n)$ overhead per level of recursion (which would destroy the $n \log n$ bound). Reynolds is explicit that this program is chosen specifically because — unlike most textbook merge-sort-on-lists examples — it achieves genuine $n\log n$ efficiency *and* is in-place, by threading explicit length parameters (`n`, `n1`, `n2`) alongside the pointers.

### Two mutually-recursive-shaped specifications

$$
H_{\mathrm{mergesort}} \stackrel{\mathrm{def}}{=} \{\mathrm{lseg}_\alpha(i,j_0) \wedge \#\alpha = n \wedge n \ge 1\}\ \mathrm{mergesort}(i,j;n)\{\alpha,j_0\}\ \{\exists\beta.\ \mathrm{lseg}_\beta(i,-) \wedge \beta\sim\alpha \wedge \mathrm{ord}\,\beta \wedge j=j_0\}
$$

$$
H_{\mathrm{merge}} \stackrel{\mathrm{def}}{=} \{(\mathrm{lseg}_{\beta_1}(i_1,-)\wedge\mathrm{ord}\,\beta_1\wedge\#\beta_1{=}n_1\wedge n_1{\ge}1) * (\mathrm{lseg}_{\beta_2}(i_2,-)\wedge\mathrm{ord}\,\beta_2\wedge\#\beta_2{=}n_2\wedge n_2{\ge}1)\}\ \mathrm{merge}(\ldots)\{\beta_1,\beta_2\}\ \{\exists\beta.\ \mathrm{lseg}_\beta(i,-)\wedge\beta\sim\beta_1{\cdot}\beta_2\wedge\mathrm{ord}\,\beta\}
$$

where `ord α` means $\alpha$ is sorted (non-strict increasing) and `β ∼ α` means $\beta$ is a **rearrangement** (permutation) of $\alpha$ — both defined via small algebraic laws (e.g. $\mathrm{ord}\,\alpha{\cdot}\beta \Leftrightarrow \mathrm{ord}\,\alpha \wedge \mathrm{ord}\,\beta \wedge \{\alpha\}\le^{*}\{\beta\}$, using the pointwise-extended order $\le^{*}$ on the *images* — sets of values — of the two sequences) that get used as an algebraic toolkit throughout the proof, the same way `#`/`∼`/`⊆` facts get chained in an ordinary algorithm-correctness proof, just phrased with sequences instead of sets.

### The proof's core move: the frame rule chaining two recursive calls

The body's key step (after splitting the input length `n` into `n1 = n÷2`, `n2 = n - n1`, with a short arithmetic lemma establishing $1 \le n_1, n_2 \le n-1$ so both halves are always nonempty and strictly smaller — this is what makes the recursion terminate) is:

$$
\{\mathrm{lseg}_{\alpha_1}(i_1,i_2) \wedge \#\alpha_1{=}n_1{\ge}1\}\ \mathrm{mergesort}(i_1,i_2;n_1)\{\alpha_1,i_2\}\ \{\exists\beta_1.\ \mathrm{lseg}_{\beta_1}(i_1,-)\wedge\beta_1\sim\alpha_1\wedge\mathrm{ord}\,\beta_1\wedge i_2{=}i_2\}
$$

is derived from the hypothesis $H_{\mathrm{mergesort}}$ via `GCALL` (general call), then the **frame rule** adds back the untouched second half `lseg_{α2}(i2, j0)` as a disjoint conjunct, and the existential-quantification rule packages `α1, α2, i2` as ghosts — precisely the same "prove the small local fact, then frame it up to the ambient context" rhythm you've seen throughout the book, here applied *twice in sequence* (once per recursive call) before the two sorted halves are handed to `merge`. This is worth noting as a template: **recursive divide-and-conquer proofs in separation logic are, structurally, just repeated applications of the frame rule around each recursive call, composed with the procedure-call rule** — nothing more exotic is needed even for a genuinely nontrivial algorithm.

### Two implementations of `merge`, same specification

The book gives `merge` twice: first as a **tail-recursive** procedure calling a helper `merge1` (whose specification threads five existentially-quantified ghost sequences through each step — the two "already merged" prefixes, the two remaining suffixes, and a case analysis on which input's head is smaller), and second, more efficiently, using **`goto` commands** instead of recursion. The `goto` version is the more interesting proof-engineering point: Reynolds shows that Hoare-logic-style annotation extends to labeled jumps completely straightforwardly — **associate an assertion with every label** (the precondition of whatever follows it), make that assertion the precondition of every `goto` targeting the label, and give `goto` itself the postcondition `false` (since it never returns control) — and that the two labels' assertions are *exactly* the preconditions of the two recursive calls in the recursive version. This is a clean illustration that **recursion and iteration-via-jumps are, at the level of Hoare-logic annotation, interconvertible without any new proof principle** — the "recursive call precondition" and "label precondition" are the same syntactic object playing two different operational roles.

```rust
// The mergesort/merge specification's shape, made concrete: sorting a
// singly-linked segment of known length, splitting by length (not by
// walking), the same way the book avoids an O(n) list-halving step.
#[derive(Debug)]
struct Node { val: i64, next: Option<Box<Node>> }

fn mergesort(mut list: Option<Box<Node>>, n: usize) -> (Option<Box<Node>>, Option<Box<Node>>) {
    // returns (sorted_head, remainder_after_n_nodes) — the j0 ghost, made real
    if n == 1 {
        let mut node = list.take().unwrap();
        let rest = node.next.take();
        return (Some(node), rest);
    }
    let n1 = n / 2;
    let n2 = n - n1;
    let (sorted1, remainder) = mergesort(list, n1);   // {lseg α1(i1,i2)} ...
    let (sorted2, rest_after) = mergesort(remainder, n2); // frame rule: α2 untouched by call 1
    (merge(sorted1, sorted2), rest_after)
}

fn merge(mut a: Option<Box<Node>>, mut b: Option<Box<Node>>) -> Option<Box<Node>> {
    // merge(i; n1, n2, i1, i2){β1, β2} — same ord/∼ postcondition, expressed
    // as: the result is sorted and is a permutation of a's and b's elements.
    match (a.take(), b.take()) {
        (None, y) => y,
        (x, None) => x,
        (Some(mut x), Some(mut y)) => {
            if x.val <= y.val {
                x.next = merge(x.next.take(), Some(y));
                Some(x)
            } else {
                y.next = merge(Some(x), y.next.take());
                Some(y)
            }
        }
    }
}
```

## Case study 3: quicksort (§6.3–6.4) — arrays, and a genuinely subtle termination fix

### Partition

`partition(c; a, b, r)` rearranges `array_α(a,b)` around a pivot value `r`, using two inward-moving pointers `c` (from the left) and `d` (from the right), each step justified entirely by `array`'s composition and splitting laws from the [[The-Iterated-Separating-Conjunction|iterated separating conjunction]] chapter — e.g. the loop invariant

$$
\exists \alpha_1,\alpha_2,\alpha_3.\ (\mathrm{array}_{\alpha_1}(a,c) * \mathrm{array}_{\alpha_2}(c{+}1,d{-}1) * \mathrm{array}_{\alpha_3}(d,b)) \wedge \alpha_1{\cdot}\alpha_2{\cdot}\alpha_3 \sim \alpha \wedge \{\alpha_1\}\le^{*} r \wedge \{\alpha_3\} >^{*} r
$$

is a three-way `array` split — smaller-or-equal elements settled on the left, larger on the right, the unexamined middle still to be processed — with the frame rule silently doing the work of letting each single-cell read/write (`x := [c+1]`, `[c+1] := y`) reason only about the one cell it touches while the rest of the invariant rides along unchanged.

### Quicksort itself, and the termination trap

The specification looks like the obvious formalization of "sorting":

$$
\{\mathrm{array}_\alpha(a,b)\}\ \mathrm{quicksort}(;a,b)\{\alpha\}\ \{\exists\beta.\ \mathrm{array}_\beta(a,b)\wedge\beta\sim\alpha\wedge\mathrm{ord}\,\beta\}
$$

But a **naive** quicksort — partition around an arbitrary pivot, recurse on both halves — can fail to terminate: if every element in the array is equal, a pivot chosen from inside the array can produce one empty partition and one partition containing the *entire* array, and the recursion never shrinks. Reynolds's fix, worth remembering as a general algorithm-design lesson and not just a proof technicality: **sort the two end elements of the array first, use their mean as the pivot, and partition only the array's interior** —

```
if a < b then newvar c in
  (x1 := [a]; x2 := [b];
   if x1 > x2 then ([a] := x2; [b] := x1) else skip;
   r := (x1 + x2) ÷ 2;
   partition(c; a+1, b-1, r);
   quicksort(a, c); quicksort(c+1, b))
else skip
```

Since `x1 ≤ r ≤ x2` after the sort-and-average step, and `partition` only ever touches the strictly interior range `[a+1, b-1]`, **both recursive calls are guaranteed to receive a strictly smaller range than `[a,b]`** — the endpoints themselves settle the pivot's bounds and are never re-examined, so the pathological all-equal-elements case can no longer produce a degenerate partition. This is a nice example of a correctness proof **driving an algorithmic fix**, not just documenting a pre-existing algorithm: the naive version doesn't satisfy the total-correctness specification, and the fix that repairs the proof is exactly the fix that repairs the algorithm.

```python
# The array-splitting shape of the proof, and the endpoint-sorting fix
# that makes both recursive ranges strictly shrink — illustrative only.
def quicksort(a, lo, hi):
    if lo < hi:
        if a[lo] > a[hi]:
            a[lo], a[hi] = a[hi], a[lo]
        pivot = (a[lo] + a[hi]) / 2
        c = partition(a, lo + 1, hi - 1, pivot)  # only the interior is touched
        quicksort(a, lo, c)
        quicksort(a, c + 1, hi)
```

## Case study 4: the LISP subset-list program (§6.7) — proving something precise about deliberate sharing

### Why this is the hardest case study to *specify*, not just to prove

Every earlier structure in the book (trees, dags, even the doubly-linked segments) treated sharing as something to either forbid (`*`) or carefully permit in a controlled, acyclic way (`dag`, with field counts to rule out "skewed sharing"). The subset-list algorithm is different in kind: given a list representing a set (or multiset) of $n$ elements, it computes **all of its sub-multisets**, and it is historically important precisely because its output sublists **share storage extensively** — a naive implementation representing each of the $2^n$ subsets independently would need exponential storage, but structural sharing between subsets (a subset and the "same subset plus one more element" can share almost their entire representation) reduces this to a much lower order of complexity. Verifying this program means proving something the book has spent five chapters *avoiding* having to prove: **an exact characterization of how much sharing exists**, precise enough to pin down the output's size.

### Building the specification: three predicates, layered

The output type itself needs a new predicate: $\mathrm{ss}(\alpha,\sigma)$ asserts that $\sigma$ (a sequence of *sequences*) is exactly the sequence of subsets of $\alpha$, in a specific canonical order, defined inductively via a helper $\mathrm{ext}_a\,\sigma$ that prefixes $a$ onto every element of $\sigma$:

$$
\mathrm{ss}(\varepsilon,\sigma) \stackrel{\mathrm{def}}{=} \sigma = [\,] \qquad \mathrm{ss}(a{\cdot}\alpha,\sigma) \stackrel{\mathrm{def}}{=} \exists \sigma'.\ \mathrm{ss}(\alpha,\sigma') \wedge \sigma = (\mathrm{ext}_a\,\sigma')^\dagger \cdot \sigma'
$$

— this alone is purely about the *abstract* combinatorics (which subsets exist, in which order) and says nothing about the heap yet. The heap-level claim is split into two orthogonal predicates, connected by the iterated conjunction from the previous topic:

$$
Q(\sigma,\beta) \stackrel{\mathrm{def}}{=} \#\beta = \#\sigma \wedge \forall_{i=1}^{\#\beta}(\mathrm{list}_{\sigma_i}(\beta_i) * \mathrm{true}) \qquad R(\beta) \stackrel{\mathrm{def}}{=} (\beta_{\#\beta}{=}\mathrm{nil}\wedge\mathrm{emp}) * \underset{i=1}{\overset{\#\beta-1}{\Large\ast}}(\exists a,k.\ i{<}k{\le}\#\beta \wedge \beta_i \mapsto a,\beta_k)
$$

`Q` says each address in `β` heads a list representing the corresponding subset in `σ` (using `* true` because those lists may overlap with *other* content in the heap — this is deliberately weak, existential-style containment, not exclusive ownership). `R` is where the sharing structure is actually pinned down precisely: it says the *outer* list of sublist-headers `β` is built from records whose data field can point at **any later element of `β` itself** — i.e., each subset's representation is literally "one element, followed by a pointer to (the representation of) some other, already-computed subset." This is the formal expression of "subsets share tails with other subsets," using the iterated conjunction to range over all $\#\beta - 1$ of these possibly-forward-pointing links at once.

### The workhorse lemma: $W$, and the "extend by one element" step

$$
W(\beta,\gamma,a) \stackrel{\mathrm{def}}{=} \#\gamma = \#\beta \wedge \underset{i=1}{\overset{\#\gamma}{\Large\ast}} \gamma_i \mapsto a, (\beta^\dagger)_i
$$

$W$ describes a *freshly allocated* parallel sequence of addresses `γ`, each holding `a` followed by (the reflection of) the corresponding entry of `β` — exactly the record you'd build when extending every existing subset by prepending a new element `a`. The two propositions proved about it,

$$
Q(\sigma,\beta) * W(\beta,\gamma,a) \Rightarrow Q((\mathrm{ext}_a\,\sigma)^\dagger{\cdot}\sigma,\ \gamma{\cdot}\beta) \qquad R(\beta)*W(\beta,\gamma,a) \Rightarrow R(\gamma{\cdot}\beta)
$$

are each proved by a chain of applications of the iterated-conjunction axiom schemata (splitting a range, shifting an index, the semidistributive law for `*` over `∀`) from the previous topic — this is the payoff those algebraic laws were built for: **each step of the outer/inner while-loop in the actual program corresponds to exactly one application of these two propositions**, extending the invariant's `Q ∧ R` characterization by one newly-allocated sublist at a time, while the iterated conjunction keeps precise, checkable track of exactly which addresses are involved and how they're linked. The double nested `while`-loop's full invariant — reproduced in the book in complete annotated detail — is the single most heap-structurally intricate assertion in the entire book, and it is only tractable *because* `Q`, `R`, and `W` were engineered as separate, independently-composable pieces rather than one monolithic invariant.

### Why this matters beyond this one program

The subset-list case study is the book's answer to a question every earlier chapter dodges: *can separation logic reason about programs whose entire point is to create rich, intentional heap sharing, with the same precision it brings to programs that forbid sharing?* The answer — yes, provided you're willing to build predicates like `Q`/`R`/`W` that separate "which addresses are shared" from "what they contain" from "how they're threaded together" — is a genuinely important data point about the logic's expressiveness, not just a hard exercise.

## Where this leads

Read together, these four case studies trace an arc: Schorr-Waite shows separating implication earning its place on the hardest possible pointer-reversal problem; mergesort and quicksort show the frame rule and (respectively) `lseg` and `array` composition scaling cleanly to genuinely nontrivial recursive algorithms, including a case where the correctness proof *fixes* a latent bug (quicksort's termination); the subset-list program shows the logic's full expressive reach on a problem that is fundamentally *about* sharing rather than about avoiding it.

For a Rust-based verifier with an eye toward abstract interpretation and invariant generation: these are precisely the caliber of programs where **automatic** invariant inference (rather than hand-supplied annotations, as Reynolds gives throughout) would need to discover facts like "both recursive calls receive strictly smaller ranges" (quicksort's termination argument) or "this predicate's disjointness structure corresponds to the reachable-sharing pattern of a recursive data-sharing algorithm" (the subset-list `Q`/`R`/`W` decomposition) — exactly the kind of shape-analysis and separation-logic-based abstract domain that tools in the CEGAR/predicate-abstraction tradition, or a bi-abduction-style automatic frame inference engine, are built to automate. The Schorr-Waite invariant in particular remains, to this day, a canonical stress test for automated separation-logic verifiers.
