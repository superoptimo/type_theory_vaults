---
title: "The Iterated Separating Conjunction"
book: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 6, §6.1, 6.2, 6.5, 6.6"
pages: "181–183, 189–191"
tags: [separation-logic, arrays, iterated-conjunction, binding-operators, modular-arithmetic]
---

# The Iterated Separating Conjunction

[[book-guidelines|↩ Back to guidelines]]

## Why a fixed-arity `*` isn't enough for arrays

Every predicate built so far — `list`, `lseg`, `dlseg`, `tree`, `dag` — describes a structure whose *shape* is determined recursively, one cons-cell of separating conjunction at a time. That works beautifully for linked structures, where the number of `*`-conjuncts equals the number of nodes and is discovered by induction on the abstract sequence or tree. But an **array** is a block of $n$ contiguous heap cells where $n$ is a runtime value, not something you can pattern-match on structurally the way you pattern-match on a sequence being empty or `a·α`. You need an assertion that says "these $n$ cells are all disjoint from each other, and disjoint from everything else," for an $n$ that's a variable, not a fixed number written in the assertion's own syntax.

You could imagine trying to write this out as `(a ↦ x1) * (a+1 ↦ x2) * ... * (a+n-1 ↦ xn)` — but that's not a well-formed assertion at all, since ordinary `*` is a fixed binary (or n-ary, for a fixed literal $n$) connective, not something that can be "unrolled" a variable number of times inside the object language. What's needed is a genuinely new binding operator: a **quantifier-like form of `*`** that iterates the separating conjunction over an index range whose bounds are themselves expressions.

## The new binding form

Reynolds extends the assertion language with

$$
\underset{v=e}{\overset{e'}{\Large\ast}}\ p
$$

where the occurrence of $v$ in the subscript is a **binder** whose scope is $p$ — read it exactly the way you'd read $\sum_{i=1}^{n}$ or $\bigwedge_{i=1}^n$: a compile-time-unknown number of copies of a formula, one per value of the bound variable, conjoined (here, separatingly) together. Informally, it stands for:

$$
(p/v{\to}e) * (p/v{\to}e{+}1) * \cdots * (p/v{\to}e')
$$

The *formal* semantics has to say precisely what "all disjoint" means for a variable-length list of conjuncts, and this is where [[Doubly-Linked-and-Xor-Linked-List-Segments#The definition|the definition]] earns its keep: for a state $s, h$, let $m = [\![e]\!]_{\mathrm{exp}}\,s$ and $n = [\![e']\!]_{\mathrm{exp}}\,s$ be the bounds and $I = \{i \mid m \le i \le n\}$ the index set. Then

$$
s, h \models \underset{v=e}{\overset{e'}{\Large\ast}} p \iff \exists H \in I \to \mathrm{Heaps}.\ h = \bigcup_{i\in I} H_i \ \wedge\ (\forall i,j \in I.\ i \ne j \Rightarrow H_i \perp H_j) \ \wedge\ (\forall i \in I.\ [s \mid v{:}i], H_i \models p)
$$

This is exactly the same idea as ordinary `*`'s semantics ("there exist two disjoint sub-heaps satisfying the two conjuncts") generalized from a fixed pair of sub-heaps to an **indexed family** of them, with disjointness required pairwise across the whole family and their union required to reconstitute exactly $h$. If you've implemented a [[Case-Studies-in-Program-Verification#Partition|partition]]-refinement algorithm, a disjoint-set/union-find structure, or a `HashMap<Index, OwnedSlice>`-style sharded ownership scheme, this is precisely that idea, just phrased as existential quantification over the partition witness $H$.

```rust
// A direct operational reading of the semantics: proving the iterated
// separating conjunction holds means exhibiting a partition H of the
// heap indexed by I, pairwise disjoint, each satisfying p under [v:i].
use std::collections::HashMap;

type Addr = usize;
type Heap = HashMap<Addr, i64>;

/// Witness that `heap` can be partitioned as required by ⁎_{v=m}^{n} p,
/// where `holds` checks p under the binding [v: i] against a candidate sub-heap.
fn check_iterated_star(
    heap: &Heap,
    m: i64, n: i64,
    holds: impl Fn(i64, &Heap) -> bool,
    partition: impl Fn(i64) -> Vec<Addr>, // which addresses "belong" to index i
) -> bool {
    let mut seen = std::collections::HashSet::new();
    for i in m..=n {
        let cells = partition(i);
        for &a in &cells {
            if !seen.insert(a) { return false; } // disjointness (Hi ⊥ Hj) violated
        }
        let sub_heap: Heap = cells.iter().filter_map(|a| heap.get(a).map(|v| (*a, *v))).collect();
        if !holds(i, &sub_heap) { return false; } // [s|v:i], Hi ⊨ p
    }
    seen.len() == heap.len() // ⋃ Hi = h — nothing left over
}
```

## The axiom schemata: an algebra for splitting, shifting, and distributing

Once the binder is defined semantically, the book immediately gives a battery of derived equivalences that let you *manipulate* iterated-conjunction assertions symbolically, without going back to the raw partition semantics every time — exactly the role ordinary algebraic laws (associativity, distributivity) play for finite `*`. These are the actual working tools used throughout the array proofs:

$$
\begin{aligned}
m > n &\Rightarrow \left(\underset{i=m}{\overset{n}{\Large\ast}} p(i) \Leftrightarrow \mathrm{emp}\right) &&\text{(empty range is trivial)} \\[4pt]
m = n &\Rightarrow \left(\underset{i=m}{\overset{n}{\Large\ast}} p(i) \Leftrightarrow p(m)\right) &&\text{(singleton range degenerates to a single conjunct)} \\[4pt]
k \le m \le n{+}1 &\Rightarrow \left(\underset{i=k}{\overset{n}{\Large\ast}} p(i) \Leftrightarrow \left(\underset{i=k}{\overset{m-1}{\Large\ast}} p(i)\right) * \left(\underset{i=m}{\overset{n}{\Large\ast}} p(i)\right)\right) &&\text{(splitting a range at any interior point)} \\[4pt]
&\left(\underset{i=m}{\overset{n}{\Large\ast}} p(i) \Leftrightarrow \underset{i=m-k}{\overset{n-k}{\Large\ast}} p(i{+}k)\right) &&\text{(shifting the index by a constant)} \\[4pt]
m \le n &\Rightarrow \left(\left(\underset{i=m}{\overset{n}{\Large\ast}} p(i)\right) * q \Leftrightarrow \underset{i=m}{\overset{n}{\Large\ast}} (p(i) * q)\right), \ q\text{ pure}, i \notin FV(q) &&\text{(distributing a pure conjunct in)} \\[4pt]
m \le j \le n &\Rightarrow \left(\left(\underset{i=m}{\overset{n}{\Large\ast}} p(i)\right) \Rightarrow (p(j) * \mathrm{true})\right) &&\text{(any single element is "reachable" from the whole)}
\end{aligned}
$$

The splitting law is the workhorse: it's what lets you carve out exactly the one array cell (or the one sub-range) an assignment or lookup command actually touches, apply the ordinary points-to reasoning to it locally, and then reassemble the whole array assertion via the frame rule — the identical "local reasoning, then re-assemble" pattern as `lseg`'s composition law, just for a range instead of a linked chain. The shifting law (6.4) is specifically what makes **modular/cyclic indexing** tractable, as you'll see below.

## Arrays: giving the binder its main job

With the binder in hand, allocation gets a new command, `v := allocate e`, which allocates a block of size $e$ and assigns the address of its first cell to $v$ (the initial contents of the cells are unspecified — this mirrors `cons`'s indeterminacy about fresh addresses). Its local nonoverwriting rule is exactly what you'd expect once you see the shape:

$$
\{\mathrm{emp}\}\ v := \mathrm{allocate}\ e\ \{\underset{i=v}{\overset{v+e-1}{\Large\ast}} i \mapsto -\}, \qquad v \notin FV(e)
$$

— a direct generalization of `cons`'s local rule (`{emp} v := cons(...) {v ↦ ...}`) from "one fresh cell" to "$e$ fresh, pairwise-disjoint cells," with the disjointness of the whole freshly-allocated block coming for free from the iterated conjunction's semantics. The global, overwriting, and backward-reasoning forms (`ALLOCNOG`, `ALLOCL`, `ALLOCG`, `ALLOCBR`) follow the identical local/global/backward-reasoning pattern already established for `cons` in Chapter 3 — nothing new conceptually, just re-derived at the array's granularity.

The genuinely new predicate is `array`, which connects a heap range to an **abstract sequence** $\alpha$ (the same kind of abstract value used throughout `list`/`lseg`):

$$
\mathrm{array}_\alpha(a,b) \stackrel{\mathrm{def}}{=} \#\alpha = b - a + 1 \ \wedge\ \underset{i=a}{\overset{b}{\Large\ast}} i \mapsto \alpha_{i-a+1}
$$

Unlike `list` or `dlseg`, `array` is **not defined by structural induction on $\alpha$** — it's defined directly via the iterated conjunction, in one shot, over the whole range. This is a genuinely different flavor of predicate definition from everything in Chapters 4–5, and it's worth naming the distinction explicitly: `list`/`lseg`/`dlseg`/`tree` are inductive predicates whose recursive structure *is* the proof technique (structural induction on the abstract value drives every proof about them); `array` is instead a single closed-form assertion built from a primitive iterated operator, and its "recursive" properties (below) have to be *derived* as consequences, not read off the definition by cases.

Derived properties, following directly from the axiom schemata above:

$$
\begin{aligned}
\mathrm{array}_\varepsilon(a,b) &\Leftrightarrow b = a-1 \wedge \mathrm{emp} \\
\mathrm{array}_{x}(a,b) &\Leftrightarrow b=a \wedge a \mapsto x \\
\mathrm{array}_{x\cdot\alpha}(a,b) &\Leftrightarrow a \mapsto x * \mathrm{array}_\alpha(a{+}1,b) \\
\mathrm{array}_\alpha(a,c) * \mathrm{array}_\beta(c{+}1,b) &\Leftrightarrow \mathrm{array}_{\alpha\cdot\beta}(a,b) \wedge c = a + \#\alpha - 1
\end{aligned}
$$

That last line is `array`'s version of `lseg`'s composition law — and note it's an *equivalence with a side condition on $c$*, not a bare biconditional, precisely because (unlike a linked list, where the split point is wherever the "next" pointer happens to point) an array's split point is any arithmetic expression, and the assertion has to pin down which one.

```rust
// array_α(a,b) as a runtime-checkable invariant: a contiguous slice whose
// length matches an abstract sequence — this is precisely what a Rust
// slice-with-length already guarantees for free, by construction.
struct ArraySeg<'a> {
    heap: &'a [i64],   // the concrete cells
    a: usize, b: usize, // inclusive bounds — a to b represents the sequence
}

impl<'a> ArraySeg<'a> {
    fn represents(&self, alpha: &[i64]) -> bool {
        alpha.len() == self.b - self.a + 1
            && (self.a..=self.b).all(|i| self.heap[i] == alpha[i - self.a])
    }
    // The composition law above is exactly `slice.split_at(mid)`:
    // splitting one array_{α·β} into array_α(a,c) * array_β(c+1,b)
    // is a disjointness fact Rust's slice API gives you for free.
}
```

## Cyclic buffers: the shifting axiom earning its keep

Section 6.5 revisits the cyclic-buffer idea from Chapter 4 (there done with two `lseg`s), now representing it as a **fixed array** addressed **modulo its size** — the more realistic implementation, and the one where the iterated conjunction's shifting axiom (6.4) is not a nicety but the entire reason the proof goes through.

Setup: an $n$-element array allocated at `l`; define $x \oplus y \stackrel{\mathrm{def}}{=} x + y \bmod n$ (kept in range $[l, l+n)$); track `m` (count of active elements), `i` (pointer to the first active element), `j` (pointer to the first *inactive* slot). The buffer's shape invariant:

$$
R \stackrel{\mathrm{def}}{=} 0 \le m \le n \wedge l \le i < l+n \wedge l \le j < l+n \wedge j = i \oplus m
$$

and the full data invariant describing a buffer holding sequence $\alpha$:

$$
\left(\underset{k=0}{\overset{m-1}{\Large\ast}} i \oplus k \mapsto \alpha_{k+1}\right) * \left(\underset{k=0}{\overset{n-m-1}{\Large\ast}} j \oplus k \mapsto -\right) \ \wedge\ m = \#\alpha \wedge R
$$

Read this as two disjoint iterated blocks: the first $m$ slots (wrapping around via $\oplus$) hold the live elements of $\alpha$ in order; the remaining $n-m$ slots (also wrapping) are allocated-but-unused. The insertion proof for appending $x$ at the end proceeds by exactly the algebraic moves the axiom schemata license — split off a single cell from the "unused" block via (6.3)/(6.2), write into it, then use the **shift axiom (6.4)** to fold that single written cell back into the "live" block's range, since the live range's *index arithmetic itself* just grew by one slot: $j \oplus 0 \mapsto x$ becomes, after the write, exactly $i \oplus m \mapsto x$ — the same physical cell, described under two different index parameterizations of the same modular scheme, unified by the shift law. This is a clean illustration of why the shifting axiom needed to exist as a *primitive* law rather than being derivable from splitting alone: splitting only rearranges *which* conjuncts group together; shifting is what lets you *reindex* a range, which is exactly what "the buffer's logical start moved by one slot" means arithmetically.

```python
# Mirroring the modular-indexing discipline the shift axiom licenses:
# growing the "live" range by reindexing rather than re-partitioning.
class CyclicBuffer:
    def __init__(self, n):
        self.n, self.data = n, [None] * n
        self.m = self.i = self.j = 0  # count, head, first-free-slot

    def push(self, x):
        assert self.m < self.n
        self.data[self.j] = x          # write into slot j (⊕-addressed)
        self.m += 1
        self.j = (self.j + 1) % self.n # index arithmetic — the shift axiom's role
```

## `list` and `listN` reconciled via iterated conjunction (§6.6)

A short but conceptually important closing example shows the iterated conjunction isn't only for *arrays*: it also gives a clean bridge between two representations of the same singly-linked list. `listN σ i` (from Chapter 4's Bornat lists) describes only the **link structure** — a sequence of *addresses* `σ`, one per node — leaving the *data* fields untouched by the predicate; `list α i` describes the same nodes' *data contents* directly. The book shows:

$$
\mathrm{list}_\alpha(i) \Leftrightarrow \exists \sigma.\ \#\sigma = \#\alpha \ \wedge\ \left(\mathrm{listN}_\sigma(i) * \underset{k=1}{\overset{\#\alpha}{\Large\ast}} \sigma_k \mapsto \alpha_k\right)
$$

— proved by structural induction on $\alpha$. Read this as: "a list is exactly its link-skeleton (`listN`), separately conjoined with an iterated block asserting that each node's data-field, addressed via the skeleton's own address sequence $\sigma$, holds the corresponding element of $\alpha$." This is a genuinely nice illustration of **separating a structure's topology from its payload** as two independently-composable separation-logic assertions, glued by nothing more than the iterated `*` — a decomposition that will recur, in a much higher-stakes form, in Chapter 6's subset-list case study, where the *sharing structure* of sublists needs to be characterized completely independently of which elements they contain.

## Where this leads

The binder and its axiom schemata are pure infrastructure — this section builds no programs, proves no algorithms correct. Its payoff is entirely downstream: the `array` predicate and the splitting/shifting laws are the load-bearing machinery behind the **Partition and Quicksort proofs** (§6.3–6.4) and the **LISP subset-list case study** (§6.7), both covered in [[Case-Studies-in-Program-Verification|Case Studies in Program Verification]] — Quicksort's recursive calls repeatedly split one `array` assertion into two via exactly the composition law derived here, and the subset-list proof's $W(\beta,\gamma,a)$ predicate is itself built as an iterated conjunction over a sequence of addresses, reusing the same binder for a purpose (characterizing sharing structure) quite far from arrays.

For a checker/verifier project: the iterated separating conjunction is separation logic's answer to needing a **quantified frame** — a footprint whose size is a runtime value rather than syntactically fixed. Any Rust verifier reasoning about slices, `Vec`s, or dynamically-sized arrays needs an assertion form exactly this shape (this is, in fact, essentially how tools like Viper's `forperm`/quantified permissions, or Dafny's `forall` over array indices with `reads`/`requires` clauses, address the same problem) — and the axiom schemata here (split at an interior point, shift the index, distribute a pure fact) are precisely the rewrite rules such a checker's automation would need to implement to make quantified-frame reasoning tractable rather than requiring a fresh existential witness at every step.
