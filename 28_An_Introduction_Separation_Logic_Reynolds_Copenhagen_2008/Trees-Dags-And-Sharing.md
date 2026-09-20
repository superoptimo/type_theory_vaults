---
title: "Trees, Dags, and Sharing"
source: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 5, §5.1–5.2, §5.6"
pages: "161–169, 177–180"
tags: [separation-logic, trees, dags, sharing, intuitionistic-assertions, preciseness, heap-auxiliaries]
---

# Trees, Dags, and Sharing

[[book-guidelines|↩ Back to guidelines]]

## From sequences to S-expressions, and the fork in the road

Chapter 4 built its whole apparatus — `list`, `lseg`, preciseness — over sequences, a purely linear abstract type. Real programs also manipulate branching data: LISP's S-expressions, the founding example, defined as the least set where an S-expression is either an atom or an ordered pair $(\tau_1\cdot\tau_2)$ of S-expressions. The moment you ask "how do I represent this in the heap," you immediately face a choice that sequences never posed: **do two occurrences of the same subexpression share one heap region, or get independent copies?** For a sequence this question doesn't really arise (a sequence has no internal branching to share between). For a tree-shaped value it's the central representational decision, and Reynolds's whole point in this chapter is that separation logic's connectives — separating conjunction versus ordinary conjunction — are exactly expressive enough to state the two answers as *two different one-symbol changes to the same inductive definition*, and exactly precise enough that the difference between them produces a completely different soundness story for a "copy" procedure.

## Trees: no sharing, defined by structural induction (§5.1)

A **tree** is a heap representation of an S-expression in which no two subexpressions occupy overlapping storage. Defined by structural induction on $\tau$, exactly the way `list` was defined on sequences:
$$
\mathrm{tree}_a(i) \iff \mathrm{emp}\wedge i=a \quad(a \text{ an atom})
\qquad\qquad
\mathrm{tree}_{(\tau_1\cdot\tau_2)}(i) \iff \exists i_1,i_2.\ i\mapsto i_1,i_2 * \mathrm{tree}_{\tau_1}(i_1) * \mathrm{tree}_{\tau_2}(i_2).
$$
The separating conjunction between the two subtree obligations is doing exactly the work you'd expect: it forces the heap regions representing $\tau_1$ and $\tau_2$ to be *disjoint* — no cell can belong to both. As with `list`, both $\mathrm{tree}_\tau(i)$ and $\exists\tau.\ \mathrm{tree}_\tau(i)$ are precise, by the same style of induction as §4.3's proof for `list`.

The chapter's first real example, `copytree(j; i)`, nondestructively copies the tree at `i` to a fresh tree at `j`:
$$
\{\mathrm{tree}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau\}\ \{\mathrm{tree}_\tau(i) * \mathrm{tree}_\tau(j)\}.
$$
Its proof is a direct instance of the recursive-procedure machinery from the previous topic (SRPROC): assume the specification above as the recursion hypothesis, split on whether `i` is an atom (base case: `j := i`, trivial) or a pair (recursive case: read off both children, recursively copy each into fresh cells `j1`, `j2`, then `cons` them together), and the two recursive calls' postconditions combine via $*$-introduction to reassemble $\mathrm{tree}_\tau(i) * \mathrm{tree}_\tau(j)$ for the whole pair. This proof goes through cleanly with **no surprises** — and that absence of surprise is itself the point of doing `tree` first: it sets up the expectation that the *identical* specification should work for the sharing-permitting version too, an expectation that then fails in an instructive way in §5.2.

## Dags: one symbol changed, sharing permitted (§5.2)

A **dag** ("directed acyclic graph") allows two occurrences of the same subexpression to be represented by the *same* heap cells — legitimate acyclic sharing, not aliasing bugs. [[Doubly-Linked-and-Xor-Linked-List-Segments#The definition|The definition]] changes exactly one connective from `tree`:
$$
\mathrm{dag}_a(i) \iff i=a
\qquad\qquad
\mathrm{dag}_{(\tau_1\cdot\tau_2)}(i) \iff \exists i_1,i_2.\ i\mapsto i_1,i_2 * (\mathrm{dag}_{\tau_1}(i_1) \wedge \mathrm{dag}_{\tau_2}(i_2)).
$$
Ordinary $\wedge$ replaces the inner $*$: the two subdag facts must both hold of the *same* heap region rather than of disjoint regions, which is exactly what permits (but doesn't require) $i_1$ and $i_2$'s substructures to overlap. Two consequences follow immediately from dropping the atom case's `emp` conjunct (note `dag_a(i)` no longer asserts the heap is empty, only that $i=a$): `dag τ(i)` is not claiming *this heap and nothing else* is the dag — it's claiming a dag representing $\tau$ occurs *somewhere within* the heap. That weaker reading is deliberate and forced: if `dag` kept `emp` in the atom case the way `tree` does, then $\mathrm{dag}_{\tau_1}(i_1)\wedge\mathrm{dag}_{\tau_2}(i_2)$ would force $\tau_1=\tau_2$ (both conjuncts would have to describe *the entire* heap), which is absurd for two genuinely different shared subexpressions.

**Proposition 16** proves both $\mathrm{dag}_\tau(i)$ and $\exists\tau.\ \mathrm{dag}_\tau(i)$ are **intuitionistic**: $p$ is intuitionistic iff $p * \mathrm{true} \Rightarrow p$, i.e. truth of $p$ is preserved when the heap grows (monotone under heap extension — recall from Chapter 2 that this models "a property that only asserts presence, never absence, of storage"). The proof is a clean induction on $\tau$: for an atom, $\mathrm{dag}_a(i)*\mathrm{true}\Rightarrow i=a*\mathrm{true}\Rightarrow i=a$ (pure facts survive extension trivially); for a pair, you push $*\,\mathrm{true}$ inward through the existential and the points-to, distribute it across the $\wedge$ (splitting `true` itself in two, since `true` is trivially satisfiable by any heap split), and apply the induction hypothesis to both conjuncts. This is the general reason ordinary conjunction, not separating conjunction, is the right connective for "these two facts may be about overlapping resources."

**Proposition 17** goes further: `dag τ(i)` is **precise** *and* **supported** — supported meaning that among all subheaps of a given heap satisfying the assertion, there's a *least* one (contained in every other satisfying subheap), proved here via a genuinely nontrivial structural induction showing that if $h_0\cup h_1$ is a function (i.e. they agree wherever both are defined) and both witness `dag τ(i)` for the *same* $\tau$, then $h_0\cap h_1$ also witnesses it — meaning you can always shrink to the intersection without losing the property. This licenses applying the **precising operation** from §2.3.6, $\mathrm{Pr}\,p \stackrel{\text{def}}{=} p \wedge \neg(p * \neg\,\mathrm{emp})$, to manufacture the precise assertion "the heap contains exactly this dag and nothing more" out of the merely-supported "a dag occurs somewhere in the heap."

## Where the naive proof of `copytree` for dags breaks

Here is the chapter's central technical event. You would expect the identical specification to carry over: $\{\mathrm{dag}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau\}\ \{\mathrm{dag}_\tau(i) * \mathrm{tree}_\tau(j)\}$ — and this specification *is* in fact true. But attempting the SRPROC proof with this exact statement as the recursion hypothesis **fails at the first recursive call**. Concretely, for the pair case you need
$$
\{i\mapsto i_1,i_2 * (\mathrm{dag}_{\tau_1}(i_1)\wedge\mathrm{dag}_{\tau_2}(i_2))\}\ \mathrm{copytree}(j_1;i_1)\{\tau_1\}\ \{i\mapsto i_1,i_2 * (\mathrm{dag}_{\tau_1}(i_1)\wedge\mathrm{dag}_{\tau_2}(i_2)) * \mathrm{tree}_{\tau_1}(j_1)\},
$$
but the assumed hypothesis $\{\mathrm{dag}_{\tau_1}(i_1)\}\ \mathrm{copytree}(j_1;i_1)\{\tau_1\}\ \{\mathrm{dag}_{\tau_1}(i_1)*\mathrm{tree}_{\tau_1}(j_1)\}$ **is not strong enough to derive it**. Reynolds gives a concrete counterexample: with $\tau_1 = ((3\cdot4)\cdot(5\cdot6))$ and $\tau_2=(5\cdot6)$ sharing the $(5\cdot6)$ subdag, the hypothesis permits (as far as it *says*) a hypothetical execution of `copytree(i1, τ; j1)` that overwrites the shared $(5\cdot6)$ node — because nothing in the hypothesis's postcondition says the shared portion is *preserved*, only that a dag for $\tau_1$ exists somewhere afterward. The frame rule can't rescue this either: framing on $\mathrm{dag}_{\tau_2}(i_2)$ would require it as an untouched conjunct, but since `dag τ2(i2)` and `dag τ1(i1)` aren't asserted as *disjoint* resources (that's the whole point of using $\wedge$), the frame rule's disjointness-based footprint reasoning doesn't apply to the shared region at all.

The diagnosis: the specification needs to additionally say "and nothing about the state *outside* what I'm claimed to touch gets disturbed" — but stating "outside" requires quantifying over *arbitrary* heap properties, not just a fixed assertion. Reynolds sketches three fixes — ghost heap variables, fractional/read-only permissions, and (the one the book pursues) an **assertion variable**: a ghost parameter ranging over heap *properties* rather than values, letting the specification say "whatever else was true of the heap before, is still true of it (outside the new copy) afterward," for *any* such property $p$ simultaneously. That mechanism — and the strengthened, successful proof it enables — is the direct continuation of this topic, covered in the companion article on [[Assertion-Variables|assertion variables]].

## Skewed sharing: when the bare definition is *too* permissive (§5.6)

Even setting aside the copy-proof problem, the bare `dag` definition has a second defect: it permits **skewed sharing** — two multi-field records whose storage *overlaps without being identical*. Reynolds's example: $\mathrm{dag}_{((1\cdot2)\cdot(2\cdot3))}(i)$ is satisfied by a heap where one two-cell record's second field is the *first* field of another two-cell record — the records interleave rather than either coinciding exactly or being disjoint. Algorithms that only *read* a dag (like `copytree`, once fixed) never notice this, since they never rely on record boundaries. But any algorithm that *mutates* a dag or needs to reason about "this is one atomic record" (allocate it, free it, mutate it as a unit) is broken by skewed sharing, because the bare heap model has no notion of "these $n$ cells were allocated together as one record" — only individual cell facts.

The fix is a **heap auxiliary**: an attribute of the state — here, a **field count** function $\phi$ mapping addresses to naturals — that assertions can describe but that plays *no role in command execution* (this is the crucial discipline: $\phi$ is bookkeeping for the *proof*, invisible to the *program*, the same status ghost variables and assertion variables already have). When `cons` allocates an $n$-field record starting at $a$, $\phi$ is extended so $\phi(a)=n$ and $\phi(a{+}1)=\cdots=\phi(a{+}n{-}1)=0$ — marking the first cell as "the start of an $n$-record" and the rest as "not a record start." A new assertion form $e \xrightarrow{[\hat e]} e'$ additionally asserts the field count at $e$ is (the value of) $\hat e$, with derived rules like
$$
e \xrightarrow{[m]} - \;\wedge\; e \xrightarrow{[n]} - \;\Rightarrow\; m=n,
\qquad
e\overset{!}{\hookrightarrow}\vec{e_1} \wedge e'\overset{!}{\hookrightarrow}\vec{e_2} \wedge e\ne e' \Rightarrow e\overset{!}{\mapsto}\vec{e_1} * e'\overset{!}{\mapsto}\vec{e_2} * \mathrm{true}
$$
— that last schema is the one that explicitly rules out skewed sharing: two records with recorded field counts, at different addresses, must occupy genuinely disjoint storage. Allocation, mutation, and lookup rules survive essentially unchanged (now decorated with field-count bookkeeping), but **deallocation must become atomic**: `dispose(e, n)` frees an entire $n$-field record in one step, rather than one field at a time, because freeing a single field and letting the allocator reuse just that address (while the rest of the old record's fields remain live under the old field-count) is *precisely* the mechanism that manufactures skewed sharing in the first place — Reynolds gives a four-line command sequence that does exactly this if single-field disposal were allowed.

## Grounding

**Rust.** `tree`'s no-sharing discipline is Rust's default: `Box<Node>` gives you exactly one owner per subtree, so a `tree`-shaped algebraic data type is unrepresentable any other way without explicit sharing types:
```rust
enum Sexp { Atom(i64), Pair(Box<Sexp>, Box<Sexp>) } // tree_tau(i): unique ownership per subtree
```
`dag`'s sharing, by contrast, needs `Rc<Sexp>` (or `Arc`) — and the copy-proof failure mode has a precise Rust analogue: a naive `fn copy(t: &Sexp) -> Sexp` that recurses structurally will, if you instead try to write a version that *mutates in place* while following `Rc` pointers, silently corrupt shared substructure exactly the way the naive `copytree` proof was unable to rule out — because `Rc<T>`'s shared ownership deliberately forbids `&mut` access precisely to prevent this, the same guarantee the assertion-variable fix has to *manufacture logically* since separation logic's base heap model has no built-in notion of "shared and therefore immutable." The field-count discipline of §5.6 maps onto `Layout`/`alloc`'s bookkeeping: Rust's allocator API requires you to deallocate with the *same* `Layout` (size/count) used to allocate, for exactly the reason `dispose(e,n)` must be atomic — partial deallocation of a multi-field record is undefined behavior in both settings, for the same underlying reason.

**Lean.** `Sexp`/S-expressions are literally Lean's `inductive` mechanism at its simplest — an initial algebra with atoms and one binary constructor, no laws, which is exactly how Lean would define it:
```lean
inductive Sexp where
  | atom : Nat → Sexp
  | pair : Sexp → Sexp → Sexp
```
The tree-vs-dag distinction is the separation-logic mirror of a distinction Lean's own term representation cares about deeply: a `Sexp` value built by ordinary constructor application is tree-shaped (fully unshared) at the level of the *inductive type*, but Lean's actual runtime and elaboration-time term representations use **hash-consing / maximal sharing** internally (the same subterm, e.g. a repeated type-class instance or a shared subproof, is physically one node referenced from multiple places) — i.e., real Lean terms are represented as *dags* over what the type theory presents as *trees*. The copy-proof failure mode has a direct elaborator analogue: a term-transformation pass that "copies while mutating" a shared subterm without being sharing-aware will silently duplicate work, or worse, apply an update meant for one occurrence to all of them — exactly the disaster the assertion-variable fix in §5.3–5.4 is built to prove *cannot* happen. `dag τ(i)` being intuitionistic ($p * \mathrm{true}\Rightarrow p$) also has a direct proof-theoretic parallel: it's a monotonicity property under context/store extension, structurally the same shape as weakening lemmas in a sequent calculus — "this judgment survives adding more (disjoint) assumptions/resources" is a property proved by the identical style of structural induction in both settings.

**Python**, as an operational sketch of skewed sharing (deliberately buggy, to make the phenomenon concrete):
```python
# A 2-field record overlapping another's boundary: skewed sharing.
# Without field counts, nothing in the heap model forbids this.
heap = {10: 1, 11: 2, 11: 2, 12: 3}   # cell 11 is the "2" of one record
                                      # AND the shared middle of another
```

## Where this leads

The proof gap exposed here — `copytree`'s naive dag specification not surviving its own recursive call — is resolved by **assertion variables** (§5.3), which parameterize the recursion hypothesis over an arbitrary heap property $p$ instead of a fixed assertion, giving the strengthened specification $\{p\wedge\mathrm{dag}_\tau(i)\}\ \mathrm{copytree}(j;i)\{\tau,p\}\ \{p * \mathrm{tree}_\tau(j)\}$ used successfully in §5.4 and reused for `subst1` in §5.5 — that mechanism is this topic's direct sequel. Field counts and skewed-sharing prevention (§5.6) close out Chapter 5 and quietly become a running assumption for every subsequent multi-field-record example in the book (arrays in Chapter 6 are, after all, large multi-field records). If you're building a verifier: the tree/dag split is the cleanest illustration in the whole book of why $*$ and $\wedge$ are *not* interchangeable connectives even though both look like "and" — $*$ encodes disjoint-resource composition (frame-rule-friendly, footprint-decomposable) while $\wedge$ encodes possibly-overlapping-resource composition (intuitionistic, not decomposable by the frame rule) — and any refinement-type or contract system that wants to reason about aliasable, shared heap structures (rather than assuming Rust-style unique ownership away [[Case-Studies-in-Program-Verification#The problem|the problem]]) will need this same two-connective vocabulary to state what a "copy" or "in-place update" procedure is actually allowed to assume about the rest of the heap.
