---
title: "Abstract Data Types via Inductive Predicates"
source: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 4, §4.1–4.4"
pages: "111–121"
tags: [separation-logic, inductive-predicates, list-segments, preciseness, abstract-data-types]
---

# Abstract Data Types via Inductive Predicates

[[book-guidelines|↩ Back to guidelines]]

## The gap between "what a list is" and "what a program touches"

Chapter 1 gave you `list α i`: a heap satisfies it iff it represents the *whole* sequence $\alpha$ from address $i$ down to `nil`. That's enough to specify a program that operates on entire lists, like `LREV`. But almost no realistic list-manipulating program only ever touches whole lists. Insertion, deletion, and traversal all need to talk about a *fragment* — "the part of the list from here to there, before I've reached the end." If your only predicate is "the whole list," you're stuck re-deriving ad hoc reasoning about partial structures every time, exactly the kind of unscalable case-by-case reasoning separation logic was introduced to avoid in Chapter 1.

The fix is to generalize the predicate so it names *both endpoints*, not just the start: an inductively-defined predicate over the *abstract value* (a sequence, later an S-expression) that also parameterizes over where the corresponding heap region ends. This is the real content of this topic — not "how do you define a linked list," but **how do you build a family of composable inductive predicates that describe partial, in-progress heap structures**, so that a program's proof can be built up region by region and stitched together with the separating conjunction.

## `lseg`: parameterizing the boundary

Where `list α i` fixed the endpoint at `nil`, the list-segment predicate `lseg α (i, j)` leaves it as a second parameter $j$:
$$
\mathrm{lseg}_\varepsilon(i,j) \iff \mathrm{emp} \wedge i = j
\qquad\qquad
\mathrm{lseg}_{a\cdot\alpha}(i,k) \iff \exists j.\ i \mapsto a, j * \mathrm{lseg}_\alpha(j,k)
$$
— structural induction on the sequence, exactly like `list`, except the base case identifies $i$ with the segment's *end* $j$ rather than with `nil`. Immediate consequences: `lseg` of a singleton sequence is just a points-to fact, and — this is the property that makes the predicate compositional — segments **concatenate**:
$$
\mathrm{lseg}_{\alpha\cdot\beta}(i,k) \iff \exists j.\ \mathrm{lseg}_\alpha(i,j) * \mathrm{lseg}_\beta(j,k).
$$
This composition law is the whole payoff of the generalization. It says a segment representing the concatenation of two sequences is *exactly* the separating conjunction of two smaller segments meeting at a shared midpoint. Proving it is a genuine structural induction (worth walking through once): the base case ($\alpha=\varepsilon$) unfolds $\mathrm{lseg}_\varepsilon(i,j)$ to $\mathrm{emp}\wedge i=j$, uses $\mathrm{emp}$ as $*$'s neutral element and $\varepsilon$ as the sequence-concatenation identity to collapse the existential; the inductive case peels one cell off the front of $\alpha$, applies the hypothesis to the tail, and reassembles using associativity of $\cdot$ on sequences matching associativity of $*$ on heaps. That parallel — algebraic structure on the abstract value tracking algebraic structure on the heap assertion — is the pattern to internalize: it's what makes an inductive heap predicate a genuine *representation* of an abstract data type rather than an arbitrary heap shape.

## Touching vs. nontouching: when "empty" stops being decidable

A subtlety `list` never exposed: is a segment with $i=j$ necessarily the empty one? For `list`, yes — $\mathrm{list}_\alpha\, i \Rightarrow (i=\mathrm{nil} \Leftrightarrow \alpha=\varepsilon)$, because `nil` isn't an address a `cons` cell can occupy. But for `lseg`, $i=j$ can happen two ways: the segment is genuinely empty, *or* the segment loops back and **touches** its own endpoint — e.g. if the heap satisfies $i \mapsto a, j$ then both $\mathrm{lseg}_{[a]}(i,j)$ and (for a different, smaller subheap — the empty one) $\mathrm{lseg}_\varepsilon(i,j)$ hold. This means $\exists\alpha.\ \mathrm{lseg}_\alpha(i,j)$ is **ambiguous about which heap it describes** — a fact that matters enormously once you ask about preciseness (next section). In general, for $\mathrm{lseg}_{a_1\cdots a_n}(i_0,i_n)$ the intermediate addresses $i_0,\dots,i_{n-1}$ are forced distinct, but $i_n$ is unconstrained and may coincide with any of them.

The remedy is a second predicate, **nontouching** list segments, ruling this out by fiat:
$$
\mathrm{ntlseg}_{a\cdot\alpha}(i,k) \;\stackrel{\text{def}}{\iff}\; i\ne k \wedge i+1\ne k \wedge \exists j.\ i\mapsto a,j * \mathrm{ntlseg}_\alpha(j,k),
$$
equivalently $\mathrm{lseg}_\alpha(i,j) \wedge \neg\, j \hookrightarrow -$ ("$j$ doesn't point to anything, i.e. nothing extends past the claimed endpoint"). For nontouching segments, emptiness *is* decidable from the endpoints alone: $\mathrm{ntlseg}_\alpha(i,j) \Rightarrow (\alpha=\varepsilon \Leftrightarrow i=j)$. And there are common situations that automatically guarantee nontouching-ness — a segment immediately followed by a full list, or by a cell that's provably allocated ($j \hookrightarrow -$), is forced nontouching, because a real list or a real allocated cell can't coincide with the segment's own interior. But touching segments genuinely arise in practice — the cyclic buffer below is exactly such a case — so the extra bookkeeping (knowing the length, in that example) is unavoidable when you can't rule touching out structurally.

## A worked composite: the cyclic buffer (§4.2)

This is the payoff example for *why* you want two-endpoint segments rather than only `list`. A cyclic buffer is two list segments sharing the same underlying storage in a ring: an active segment $\mathrm{lseg}_\alpha(i,j)$ (the buffer's current contents) and an inactive segment $\mathrm{lseg}_\beta(j,i)$ (free capacity), with a fixed total capacity $n$ and a length counter $m$:
$$
\exists\beta.\ (\mathrm{lseg}_\alpha(i,j) * \mathrm{lseg}_\beta(j,i)) \wedge m = \#\alpha \wedge n = \#\alpha + \#\beta.
$$
Here $i=j$ is genuinely ambiguous (full vs. empty buffer) — this is a touching-segment situation by construction, which is exactly why the invariant needs the extra bookkeeping variable $m$: the heap shape alone can't distinguish the two cases. Inserting an element ($[j] := x$, then $j := [j+1]$, then $m := m+1$) is proved by peeling one cell off the inactive segment (instantiating $\beta = b\cdot\beta'$), applying the mutation and lookup rules cell-by-cell, and re-folding the result into $\mathrm{lseg}_{\alpha\cdot x}$ via the composition law above. Every step is local — the rule for `[j] := x` only ever needs to know about the single cell at $j$, with the composition law responsible for stitching that local fact back into the two-segment global invariant.

## Preciseness, formally (§4.3): language vs. metalanguage

Section 2.3.3 defined **precise** assertions: $p$ is precise iff, for any heap $h$ and any two subheaps $h_0, h_1 \subseteq h$ both satisfying $p$ (under the same store), $h_0 = h_1$ — i.e., $p$ pins down *exactly* which cells belong to it, given the values of its free variables. Reynolds proves, in full formal detail, **Proposition 15**: both $\mathrm{list}_\alpha\,i$ and $\exists\alpha.\ \mathrm{list}_\alpha\,i$ are precise. This proof is worth understanding not for the result (unsurprising) but for the *technique*, because the technique is the one you'd reach for to prove preciseness of any inductively-defined heap predicate.

The delicate point is a language/metalanguage distinction: $\alpha$ is a sequence *variable* inside the assertion language, but the induction proving preciseness is a structural induction on sequences carried out in the *metalanguage* (mathematical induction on the actual sequence value a store assigns to $\alpha$). Concretely, the proof establishes two auxiliary facts by unfolding [[Doubly-Linked-and-Xor-Linked-List-Segments#The definition|the definition]] under a specific store $[i{:}i \mid \alpha{:}\varepsilon]$ or $[i{:}i\mid\alpha{:}a\cdot\alpha']$: (a) if the store maps $\alpha$ to $\varepsilon$, the heap is forced empty and $i=\mathrm{nil}$; (b) if the store maps $\alpha$ to $a\cdot\alpha'$, the heap is forced to split as $[i{:}a \mid i{+}1{:}j]\cdot h'$ for some $j,h'$ with the tail satisfying `list` at $j$. Then, given two witnessing subheaps $h_0,h_1\subseteq h$ for $\exists\alpha.\ \mathrm{list}_\alpha\,i$, a structural induction on the *sequence value* $\alpha_0$ that $h_0$ realizes shows $h_0=h_1$ cell-by-cell: the base case uses (a) (both forced empty), the inductive case uses (b) to show $h_0,h_1$ must agree on their first two cells (since both are subsets of the same $h$, hence agree wherever both are defined), then applies the induction hypothesis to the tails. Finally, preciseness of $\exists\alpha.\ \mathrm{list}_\alpha\,i$ transfers to $\mathrm{list}_\alpha\,i$ itself for free, using the general lemma "if $p\Rightarrow q$ is valid and $q$ is precise, so is $p$" (since $\mathrm{list}_\alpha\,i \Rightarrow \exists\alpha.\,\mathrm{list}_\alpha\,i$ trivially).

Compare this to `lseg`: $\mathrm{list}_\alpha\,i$, $\mathrm{lseg}_\alpha(i,j)$, and $\mathrm{ntlseg}_\alpha(i,j)$ are *all* precise (the sequence is given, so the induction goes through identically). But $\exists\alpha.\ \mathrm{lseg}_\alpha(i,j)$ is **not** precise — exactly because of the touching phenomenon above: when $i=j$, both the empty subheap and a full-loop subheap can independently satisfy the existential, giving two different witnessing subheaps of the same larger heap. $\exists\alpha.\ \mathrm{ntlseg}_\alpha(i,j)$, by contrast, *is* precise, because nontouching-ness rules out exactly this ambiguity. The moral: preciseness of an inductive predicate is not automatic from "it's defined by structural induction" — it can fail exactly at the point where the induction's base case becomes ambiguous about which subheap it's claiming.

## Bornat lists: representing addresses, not values (§4.4)

A final generalization, due to Richard Bornat: instead of a list representing a sequence of *values*, `listN σ i` represents a sequence $\sigma$ of *addresses* — the list's own cell addresses, not their contents:
$$
\mathrm{listN}_\varepsilon\, i \iff \mathrm{emp}\wedge i=\mathrm{nil}
\qquad\qquad
\mathrm{listN}_{a\cdot\sigma}\,i \iff a=i \wedge \exists j.\ i{+}1 \mapsto j * \mathrm{listN}_\sigma\, j.
$$
The heap this describes contains *only the link fields*, never the data fields — a strictly weaker footprint than `list`. This is a genuinely different abstraction of the same physical structure: `list` abstracts "what values are stored here," `listN` abstracts "what addresses this chain visits." Reynolds re-proves list reversal against this new abstraction and gets a *stronger* result almost for free — the postcondition $\mathrm{listN}_{\sigma_0^\dagger}\, j$ says not just "the output is the reflected sequence of values" but "the output occupies exactly the reflected sequence of *addresses*," i.e., the algorithm provably reuses the original cells in place rather than allocating new ones. That's a genuinely different (and stronger) specification obtained purely by choosing a different inductive abstraction of the same code — a preview of the same idea Chapter 6 exploits (§6.6) to relate `list` and `listN` views of the same structure via [[The-Iterated-Separating-Conjunction|the iterated separating conjunction]].

## Grounding

**Rust.** An inductive heap predicate is, informally, the *invariant a smart pointer type is supposed to uphold* — but Rust's ownership/borrowing discipline enforces list-segment-like reasoning structurally, for free, rather than via an explicit assertion language. A doubly-ended cursor into a linked list — think `Vec::split_at_mut` or a custom cursor API — is exactly an `lseg`: it names two boundary pointers and claims (via the borrow checker) that the region between them is disjoint from everything else reachable. The composition law $\mathrm{lseg}_\alpha(i,j) * \mathrm{lseg}_\beta(j,k) \Leftrightarrow \mathrm{lseg}_{\alpha\cdot\beta}(i,k)$ is precisely what licenses splitting a mutable slice in two and handing the halves to different closures/threads — `split_at_mut`'s soundness argument *is* this composition law, just checked by the type system instead of stated as a lemma:
```rust
// lseg_alpha(i, j) * lseg_beta(j, k)  ~=~  a mutable slice split at an index
fn insert_front(list: Option<Box<Node>>, a: i64) -> Box<Node> {
    Box::new(Node { data: a, next: list }) // CONSG-style: allocate, then link
}
```

**Lean.** `list α i` and `lseg α (i, j)` are structurally-recursive inductive predicates over a sequence — the exact shape of an inductive *family* indexed by both an abstract value and (for `lseg`) an extra endpoint index, the same pattern as defining `Vector α n` indexed by length, or a `Path a b` type indexed by both endpoints in a graph formalization:
```lean
inductive Lseg (i j : Addr) : List Val → Heap → Prop
  | nil  (h : Heap) : h = Heap.emp → i = j → Lseg i j [] h
  | cons (a : Val) (α : List Val) (k : Addr) (h1 h2 : Heap) :
      PointsTo i a k h1 → Lseg k j α h2 → h1.disjointUnion h2 = some h →
      Lseg i j (a :: α) h
```
The preciseness proof in §4.3 is a direct analogue of proving an inductive family is a *subsingleton* relative to a fixed index — showing `Lseg i j α h0` and `Lseg i j α h1` (same $\alpha$) force `h0 = h1` is the separation-logic version of proving an inductive relation is functional/deterministic, done by the same recursor-based structural induction Lean would use to prove, say, that a `Vector`-indexed relation is a partial function. The touching/nontouching distinction maps onto a familiar type-theory phenomenon too: $\exists\alpha.\ \mathrm{lseg}_\alpha(i,j)$ failing to be precise is exactly a *proof-irrelevance-vs-not* issue — the existential erases exactly the information (which $\alpha$, hence which subheap) needed to pin down a unique witness, the same way projecting out of a `Subtype`/`Exists` can lose definitional information a dependent match wouldn't.

**Python**, as an operational sketch making the abstraction concrete without the proof layer:
```python
class Node:
    def __init__(self, val, nxt=None):
        self.val, self.next = val, nxt

def lseg_values(i, j):        # walk from i to j, collecting the "alpha" this segment represents
    out, cur = [], i
    while cur is not j:
        out.append(cur.val)
        cur = cur.next
    return out
```

## Where this leads

Two-endpoint inductive predicates and the preciseness discipline established here are used unmodified for the rest of the book's data-structure work: Chapter 5's `tree τ(i)` and `dag τ(i)` are the exact same structural-induction-on-the-abstract-value pattern applied to S-expressions instead of sequences (with preciseness of `tree` following the same argument, and its *failure* for `dag` — because `dag` deliberately drops `emp` from its base case to permit sharing — driving that chapter's central technical problem). The doubly- and xor-linked segments of §4.8–4.9 are `lseg` generalized to carry a second, backward-pointing field. If you're designing a verifier: the pattern to take away is that an inductive predicate representing an abstract type needs to be **parameterized by every boundary the surrounding program might reason about locally** (not just "the whole structure"), and that preciseness — the property making a predicate usable as a footprint in the frame rule — has to be checked per-predicate by exhibiting exactly where structural induction pins down a unique subheap; it isn't a free consequence of "the definition looks inductive."
