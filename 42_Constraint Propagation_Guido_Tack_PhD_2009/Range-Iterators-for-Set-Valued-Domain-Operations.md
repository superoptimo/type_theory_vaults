---
title: Range Iterators for Set-Valued Domain Operations
source: "Constraint Propagation: Models, Techniques, Implementation — Guido Tack (2009)"
chapters: "Chapter 10: Range Iterators (pp. 133–143)"
tags: [sat-smt-csp, static-analysis]
---

[[book-guidelines|↩ Back to guidelines]]

# Range Iterators for Set-Valued Domain Operations

## The problem: domains aren't single values

Every propagator discussed so far — in [[The-Denotational-and-Operational-Model-of-Constraint-Propagation|the propagation model]] and in [[Views-and-Derived-Propagators|the views machinery]] — is a function on whole domains, $p \in \mathrm{Dom}\to\mathrm{Dom}$. But *implementing* one usually means touching a domain a piece at a time: "raise the lower bound to 5," "remove the value 3." Single-value operations like `adjust_min`, `adjust_max`, `remove_value` are cheap and easy to reason about, and they're exactly what earlier chapters' worked examples use.

They stop being cheap the moment a propagator needs to manipulate a *whole set* at once — which is the normal case for domain reasoning on integer variables and for essentially every operation on set variables (recall the set-interval approximation $[\mathrm{glb}(d(x)), \mathrm{lub}(d(x))]$ from [[Propagation-Strength-and-Domain-Approximations|Chapter 4]]). Tack makes the cost concrete: suppose a variable's domain is stored as a linked list of $k$ maximal ranges (its *range sequence*). Removing one value takes $O(k)$ — you walk the list — and might split a range, growing the list by one. Remove $l$ values one at a time and you pay $O(l(k+l))$: the list keeps growing as you go. Do the same removal as a *single* set-valued update — "intersect the domain with this set" — and it's one linear pass: $O(k+l)$.

So there's a real algorithmic reason to want set-valued domain operations as first-class citizens, not just derived from repeated single-value calls. But that raises an implementation question of its own: what's the *interface* for "here is a set, do something with it"? An explicit set data structure (an array, a bitset, a materialized list of ranges) is the obvious answer — and the wrong one, as this chapter shows. Materializing a set costs memory management, and worse, it forces every consumer of that set to agree on one concrete representation, which is exactly the kind of rigidity views (Chapters 7–8) were built to avoid.

**[[The-Denotational-and-Operational-Model-of-Constraint-Propagation#What breaks without this|What breaks without this]]:** without a shared abstraction for "a set, handed to you piece by piece," every propagator, every view, and every specialized data structure (adjacency lists, automaton layers, sorted arrays) would need its own conversion code to talk to variable domains — an $O(n^2)$ integration problem across the solver's constraint library, mirroring exactly the "combinatorial explosion" problem that views solved for propagator *variants*.

## Range sequences: the canonical shape of a finite integer set

Before the interface, the book pins down the data it ranges over.

**Definition.** A *range* $[m\mathinner{..}n]$ denotes the set of integers $\{l \in \mathbb Z \mid m \le l \le n\}$.

**Definition (range sequence).** For a finite set $S \subseteq \mathbb Z$, the range sequence $\mathrm{ranges}(S)$ is the *shortest* sequence
$$
s = \langle [m_1\mathinner{..}n_1], \dots, [m_k\mathinner{..}n_k]\rangle
$$
such that $S = \bigcup_{i=1}^k [m_i\mathinner{..}n_i]$ and the ranges are ordered by their smallest elements ($m_i \le m_{i+1}$). Write $\mathrm{set}(s) := \bigcup_i [m_i\mathinner{..}n_i]$ for the set a sequence covers.

Minimality forces a normal form: no range is empty, and consecutive ranges can't be merged, i.e. $n_i + 1 < m_{i+1}$ for all $i < k$. This is why the range sequence of a set is *unique* — it's the "collapse every run of consecutive integers into one interval" decomposition, and there's only one way to do that. $\{1,2,3,7,9,10\}$ has range sequence $\langle[1..3],[7..7],[9..10]\rangle$; there's no shorter or different valid decomposition.

This is the same shape of object the set-interval domain system from Chapter 4 already works with — a set variable's domain $[\mathrm{glb}, \mathrm{lub}]$ is bounded by two sets, and both are naturally represented (and manipulated) as range sequences rather than bit-per-element sets, which is why this chapter's machinery pays off just as much for set variables as for integer-variable domain reasoning.

## The range iterator interface

Here's the move that gives the chapter its name: instead of handing around a materialized range sequence, hand around an *object that can produce one on demand, one range at a time*.

**Definition (range iterator).** A range iterator for a sequence $s = \langle[m_i\mathinner{..}n_i]\rangle_{i=1}^k$ supports four operations:
- `r.done()` — have all ranges been consumed?
- `r.next()` — advance to the next range.
- `r.min()`, `r.max()` — the bounds of the *current* range.

$\mathrm{set}(r)$ denotes the set an iterator $r$ produces — it must coincide with $\mathrm{set}(s)$.

The book's own C++ sketch of the obvious implementation — an index into an array — makes the interface's minimality obvious:

```cpp
class RangeIterator {
public:
  bool done(void) { return i > k; }
  int min(void)  { return m_i; }
  int max(void)  { return n_i; }
  void next(void) { i++; }
};
```

Four methods, no mutation of the underlying data, one range visible at a time. That last property is the whole point: **an iterator hides its implementation.** It can walk an array, as above, but equally a linked list, the leaves of a balanced tree, or — this is where the chapter goes in §10.3 and §10.6 — it can be a *computation* that has no backing storage at all. This is exactly the same design move as an object-oriented `Iterator` trait/interface (the book explicitly credits C++'s STL, Boost, and Java's collection iterators as prior art) — but applied somewhere those libraries never went: as the *sole* channel for reading and writing a constraint variable's domain.

```rust
// The chapter's interface, transcribed directly. Note there is no
// `values()` or `to_vec()` — nothing forces materialization.
trait RangeIterator {
    fn done(&self) -> bool;
    fn next(&mut self);
    fn min(&self) -> i64; // valid only while !done()
    fn max(&self) -> i64;
}
```

## Set-valued operations for integer variables

With the interface in hand, §10.2 defines the two basic domain operations for an integer variable $x$:

- `x.getdom()` returns a range iterator for $\mathrm{ranges}(d(x))$ — read the whole domain.
- `x.setdom(r)` updates $d(x)$ to $\mathrm{set}(r)$, **provided** $\mathrm{set}(r) \subseteq d(x)$.

That proviso is a sharp edge: `setdom` is *unchecked*. It doesn't verify containment; the caller must guarantee it, because contraction — $p(d) \subseteq d$, the very first property required of a propagator — has to hold for the propagator to remain sound. This is why §10.3 immediately builds two safer, self-evidently-contracting operations on top:

$$
x.\mathrm{adjdom}(r) := x.\mathrm{setdom}(\mathrm{iinter}(x.\mathrm{getdom}(), r)) \qquad \text{— intersect: } d(x)\cap\mathrm{set}(r)
$$
$$
x.\mathrm{excdom}(r) := x.\mathrm{setdom}(\mathrm{iminus}(x.\mathrm{getdom}(), r)) \qquad \text{— exclude: } d(x)\setminus\mathrm{set}(r)
$$

`adjdom`/`excdom` can never violate contraction by construction, because they're always intersecting or subtracting from the *current* domain rather than replacing it outright — `setdom` is the unsafe primitive these are safely built from.

Note also that `setdom` is **parametric in `r`** — any type implementing the range-iterator interface can be passed, and (per [[Views-and-Derived-Propagators|Chapter 9's discussion of parametricity]]) Gecode realizes this with C++ templates and monomorphization, the same zero-overhead mechanism used for views themselves.

## Computing directly with iterators — no materialization required

This is the chapter's central technical payoff, and the part that most distinguishes range iterators from a garden-variety collection-iterator pattern: **set operations compose iterators into new iterators, without ever building the intermediate set.**

Consider propagating $x = y$ — the simplest possible equality propagator:
$$
p(d)(z) = \begin{cases} d(x)\cap d(y) & z = x \text{ or } z = y \\ d(z) & \text{otherwise}\end{cases}
$$
To implement this you need "the intersection of two iterators, as an iterator" — an `IntersectionIterator`. Its logic (Figure 10.1 in the book) walks both inputs in lockstep, skipping ranges that don't overlap and emitting the overlapping portion:

```cpp
template <class A, class B>
class IntersectionIterator {
private:
  int m, n; A a; B b;
public:
  IntersectionIterator(A a, B b) : a(a), b(b) { next(); }
  bool done(void) { return a.done() || b.done(); }
  int min(void) { return m; }
  int max(void) { return n; }
  void next(void) {
    if (a.done() || b.done()) return;
    do { while (!a.done() && (a.max() < b.min())) a.next();
         if (a.done()) return;
         while (!b.done() && (b.max() < a.min())) b.next();
         if (b.done()) return;
    } while (a.max() < b.min());
    m = std::max(a.min(), b.min()); n = std::min(a.max(), b.max());
    if (a.max() < b.max()) { a.next(); } else { b.next(); }
  }
};
```

The `x = y` propagator now reads almost like pseudocode over the model: `rx = x.getdom(); ry = y.getdom(); ri = iinter(rx, ry); x.setdom(ri); y.setdom(x.getdom())`. There is no array or list built anywhere in between — `IntersectionIterator` is a *view onto a computation*, generated lazily as `next()` is called. Because `A` and `B` are themselves template parameters, you get intersection-of-three-iterators for free by nesting `IntersectionIterator<IntersectionIterator<A,B>, C>` — composability comes from the same parametric-polymorphism trick that made view *composition* free in Chapter 9.

```rust
// The same idea in Rust: an intersection "iterator" that computes lazily,
// generic over whatever two range iterators it's fed.
struct Intersection<A: RangeIterator, B: RangeIterator> { a: A, b: B, m: i64, n: i64 }

impl<A: RangeIterator, B: RangeIterator> RangeIterator for Intersection<A, B> {
    fn done(&self) -> bool { self.a.done() || self.b.done() }
    fn min(&self) -> i64 { self.m }
    fn max(&self) -> i64 { self.n }
    fn next(&mut self) {
        if self.done() { return; }
        loop {
            while !self.a.done() && self.a.max() < self.b.min() { self.a.next(); }
            if self.a.done() { return; }
            while !self.b.done() && self.b.max() < self.a.min() { self.b.next(); }
            if self.b.done() { return; }
            if self.a.max() >= self.b.min() { break; }
        }
        self.m = self.a.min().max(self.b.min());
        self.n = self.a.max().min(self.b.max());
        if self.a.max() < self.b.max() { self.a.next() } else { self.b.next() }
    }
}
```

The same pattern gives `iunion(a, b)`, `iminus(a, b)` (set difference), and `icompl(a)` (complement w.r.t. a fixed universe) — every Boolean set operation a propagator could need, all realized as iterator-to-iterator transformations rather than set-to-set functions.

**What breaks without this:** if every set operation had to materialize its result before the next operation could consume it, a chain like "intersect, then complement, then union" would allocate and populate an intermediate collection at *every* step, even though the final consumer only ever reads the result once, range by range. Iterator composition collapses the whole chain into one pass with no allocation.

**Cache iterators.** Sometimes an iterator's output genuinely needs to be reused (e.g. read twice, or the underlying computation is expensive to redo). The book's answer is a *cache iterator*: it drains an arbitrary iterator once into an array and re-serves from that array, with an explicit `reset()` so the costly input is touched exactly once. This is the escape hatch back to "explicit set data structure" — used deliberately and locally, not as the default.

**Value vs. range iterators.** Not every consumer wants ranges; some propagators are simplest written value-by-value. The book defines the adaptor pair: a *range-to-value* iterator unpacks a range sequence into individual values, and a *value-to-range* iterator repacks values into ranges. Both directions exist so that any propagator can pick whichever granularity is most convenient to *write*, while the domain-update interface underneath always stays range-based (since ranges, not values, are what make bulk operations cheap — the $O(k+l)$ argument from §10.2 depends on it).

## Views get set-valued operations too

Chapter 9 established that views are zero-overhead for *single-value* operations. §10.4–10.5 close the loop by giving every view kind from [[Views-and-Derived-Propagators|Chapters 7–8]] a set-valued counterpart, each realized as its own small iterator adaptor:

| View | Set-valued realization |
|---|---|
| Constant view (value $k$) | `getdom()` returns the singleton sequence $\langle[k..k]\rangle$; `setdom(r)` just checks $\mathrm{set}(r)$ is empty or $=\{k\}$, to detect failure. |
| Offset view ($\varphi_x(v)=v+c$) | An *offset iterator* $o = \mathrm{ioffset}(r,c)$: `o.min() = r.min()+c`, `o.max() = r.max()+c`, `done()`/`next()` pass through unchanged. `setdom` on the view calls `x.setdom(ioffset(r, -c))`. |
| Minus view ($\varphi_x(v) = -v$) | The range sequence $\langle[m_i..n_i]\rangle_{i=1}^k$ becomes $\langle[-n_{k-i+1}..-m_{k-i+1}]\rangle_{i=1}^k$ — reversed *and* sign-flipped, since negating flips ordering. The book flags this as the fiddliest of the adaptors precisely because it changes iteration *direction*. |
| Scale view ($\varphi_x(v)=a\times v$, $a>1$) | No longer range-preserving in general: scaling $[m_i..n_i]$ by $a$ yields the *singleton* values $\{am_i\},\{a(m_i+1)\},\dots,\{an_i\}$ — a range only survives scaling if $a=1$. The inverse direction (updating $x$'s domain from a scaled set $S$) computes $[\lceil m_i/a\rceil .. \lfloor n_i/a\rfloor]$ per range of $S$, then must skip empty results and merge adjacent/overlapping ones to restore a valid range sequence. |

For set variables the same treatment applies to the set-interval bounds themselves: `x.glb()`/`x.lub()` return range iterators for the greatest-lower-bound and least-upper-bound sets, and `x.adjglb(r)`/`x.adjlub(r)` tighten them (intersecting/unioning against the incoming iterator). A **complement view** on a set variable is then just `icompl` swapped between `glb`/`lub`:
$$
v.\mathrm{glb}() := \mathrm{icompl}(x.\mathrm{lub}()) \qquad v.\mathrm{adjglb}(r) := x.\mathrm{adjlub}(\mathrm{icompl}(r))
$$
and a **singleton view** (the integer-to-set type-conversion view from §8.4, letting an integer variable masquerade as a set variable so that, e.g., $x \in y$ can be expressed as $\{x\}\subseteq y$) reuses the integer variable's own iterators directly, with a case split for the empty-glb corner case.

The uniform shape across this whole table is the point: every view — transformation, generalization, specialization, type conversion — reduces to "wrap the parent's iterator in a small adaptor iterator." Set-valued operations didn't need a *different* mechanism from single-value ones; they needed the same idea ([[Views-and-Derived-Propagators#Views as input/output transformations|views as input/output transformations]]) applied to a richer notion of "input/output."

## Iterators as adaptors to arbitrary data structures

§10.3's insight — "compute an iterator without materializing a set" — generalizes past pure set algebra. Global-constraint propagators keep their *own* specialized data structures internally (they're not domain approximations at all), and range iterators turn out to be the right bridge back from those structures to variable domains, too:

- **All-different** (Régin's algorithm) maintains a variable–value bipartite graph; after pruning inconsistent edges, an adaptor iterates the values still adjacent to a variable's node, fed through a value-to-range iterator into `x.setdom(...)`.
- **`regular`** (Pesant's algorithm) unfolds a DFA into a layered graph, one layer per sequence position; an adaptor iterates the values in layer $i$ still lying on some accepting path, and prunes $x_i$'s domain accordingly.
- **`element`** ($a_x = y$) keeps two doubly-linked lists of the constants $a_i$ (sorted by index, sorted by value); two adaptors transfer surviving indices back to $x$'s domain and surviving values back to $y$'s.
- **Channeling** ($\bigwedge_i (x=i)\leftrightarrow b_i$) uses a value iterator listing which $i$ still have $b_i$ possibly $1$, through a value-to-range adaptor into $x$'s domain.

None of these internal structures are range sequences, arrays, or anything iterator-shaped by nature — a graph and a linked list are not sequences of ranges. What makes the pattern work is that *every* such structure can be wrapped in something exposing `done`/`next`/`min`/`max`, because that interface only demands "produce elements in increasing order, one chunk at a time" — a requirement almost any propagation data structure can satisfy cheaply. The iterator interface is doing real work here as an abstraction boundary: it decouples "how a propagator's internals are shaped" from "how domains get updated," the same decoupling views achieve for propagator *variants*.

## What the numbers say — and where this hits a wall

§10.7 validates two claims empirically, on the same Gecode benchmark suite used throughout the dissertation ([[Implementation-Architecture-of-a-Propagation-Kernel|§6.9]]/Appendix A).

**Claim 1 — iterators beat explicit sets.** Wrapping every iterator in a cache iterator (Table 10.1) emulates what a design using explicit set data structures would cost. For integer-only benchmarks the overhead is negligible (roughly 98–102% of baseline — noise). For set-constraint benchmarks it's substantial: up to **766%** (Social Golfers 8-4-9). The explanation tracks directly to §10.2's complexity argument: set propagators lean on set-valued operations far more heavily than integer propagators do, so the cost of materializing intermediate sets compounds.

**Claim 2 — but views over set operations hit a real limit.** This is the chapter's most important negative result, and it's the one the guidelines flag as motivating Chapter 11. Consider a hand-written propagator for ternary intersection $x = y\cap z$: it does one inference, `x.adjglb(y.glb() ∩ z.glb())`. Now derive a propagator for $x = y\cup z$ *for free* by composing views — wrap $x$, $y$, $z$ in complement views and reuse the intersection propagator (De Morgan: $y\cup z = \overline{\overline y\cap\overline z}$). Mechanically this produces
$$
x.\mathrm{adjglb}(\overline{\mathrm{lub}(y)}\cap\overline{\mathrm{lub}(z)}) \quad\text{i.e., computing}\quad x.\mathrm{adjlub}\bigl(\mathrm{lub}(y)\cap\mathrm{lub}(z)\bigr)\text{'s complement}
$$
but the *semantically equivalent and cheaper* operation is directly `x.adjlub(lub(y) ∪ lub(z))` — three fewer set operations. No compiler finds this rewrite, because doing so requires knowing the *algebraic semantics* of intersection/union/complement as set operations, not just inlining and constant-folding template instantiations (which is all a C++ compiler's optimizer does, per Chapter 9). Table 10.2 measures the gap directly — a dedicated $x\cup y=z$ propagator versus the view-composed one: **16–47% overhead**, real but "not completely useless."

This is a genuinely different failure mode from anything earlier chapters hit. Chapter 8's views had *sharp, provable* limits (non-injective views, multi-variable views breaking contraction) — failures in the *model*. This is a failure of the *implementation strategy*: the views are mathematically perfect (Chapter 7's theorems still hold), but perfect propagation strength doesn't guarantee optimal runtime, because "optimal" here requires algebraic knowledge no general-purpose compiler pass has. The book's own closing line names the fix directly: *"the next chapter solves this problem by generating set propagators directly from specifications of the constraints"* — i.e., instead of composing existing propagators via views and hoping the compiler simplifies the composition, compile the *constraint's own algebraic description* straight into a propagator, which is exactly [[book-guidelines|Chapter 11's]] Boolean-set-constraint specification technique.

## Where this leads

Range iterators are the load-bearing interface underneath both halves of the dissertation's Part II. [[Views-and-Derived-Propagators|Views]] (Chapters 7–9) needed a way to give every derived propagator honest, efficient domain access — this chapter supplies it, and shows it costs nothing for single-value operations but a measurable amount for set-valued ones. That measured cost is precisely the empirical motivation for Chapter 11's Boolean-set-constraint compilation, which sidesteps view composition altogether for set operations by generating propagators directly from a specification language.

For the `sat-smt-csp` focus area, the direct payoff is **`adjdom`/`excdom`/`iinter`/`iunion` as the general pattern for how any CSP engine represents and manipulates its own "current possible values" efficiently** — this is precisely the operational counterpart to abstract-domain narrowing in the `static-analysis` sense: a range sequence *is* an interval-abstraction of a finite integer set, and `adjglb`/`adjlub` are literally the meet/join operations of a Galois-connection-style narrowing step on that abstraction, performed lazily via iterator composition rather than eagerly on materialized sets. The chapter's central lesson — that an abstraction boundary (the iterator interface) can be zero-cost for one class of operations (single-value, per Ch. 9) while still leaking real cost for another (set-valued composition, per this chapter's Table 10.2) — is a concrete instance of the general tension between compositional software architecture and optimal generated code, worth keeping in mind wherever domain propagation and abstract interpretation are implemented as composable passes rather than monolithic specialized algorithms.
