---
title: Coinduction and Infinite Types
source: "Types and Programming Languages, Benjamin C. Pierce (2002)"
chapter: "Chapter 21, Metatheory of Recursive Types"
pages: "281–312"
tags: [type-theory, coinduction, recursive-types, subtyping, regular-trees, decidability, TAPL]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem [[Metatheory-and-Algorithms-for-Subtyping]] can't solve

[[Subtyping]] and its algorithmic chapter gave you a clean recipe: write down inference rules, strip out `S-Refl`/`S-Trans` because they're admissible, and you get a terminating, syntax-directed checker. That recipe assumed something you probably didn't notice assuming: that every derivation is *finite*. Ordinary structural induction — "assume the property for the immediate subderivations, prove it for the whole derivation" — only makes sense if you eventually bottom out at a leaf with no premises.

Equi-[[Recursive-Types|recursive types]] break that assumption on purpose. Recall from [[Metatheory-and-Algorithms-for-Subtyping]]'s sibling chapter (Ch. 20) that under the equi-recursive reading, $\mu X.T$ *is*, definitionally, the same type as its unfolding $[X \mapsto \mu X.T]T$ — no `fold`/`unfold` term needed to convert between them. Now ask: is $\mu X. X{\to}X$ a subtype of itself? Chasing the naive rule for arrows,

$$
\frac{T_1 <: S_1 \quad S_2 <: T_2}{S_1{\to}S_2 <: T_1{\to}T_2}
$$

you'd want to unfold both sides and recurse: "$\mu X.X{\to}X <: \mu X.X{\to}X$ holds if $X{\to}X <: X{\to}X$ holds, which holds if $X <: X$ holds, which is exactly the goal we started with." The derivation never terminates — it's a single rule applied forever, cycling back to its own premise. An *inductive* definition of subtyping (smallest relation closed under the rules) simply doesn't contain this pair, because there is no finite derivation tree witnessing it. But intuitively this subtyping judgment is exactly the one you want to hold — it's the whole point of treating $\mu X.T$ as literally equal to its unfolding.

So the chapter's job is to build a mathematical foundation in which "the derivation goes on forever, and that's fine" is not a bug but the intended reading — and then, separately, to show that a finite, terminating *algorithm* can still decide this seemingly-infinite question. Those are two different problems, and the chapter solves them in that order: first **coinduction** (§21.1–§21.4), the proof theory of infinite objects and infinite derivations; then **decidable membership-checking algorithms** (§21.5–§21.10) that exploit finiteness hiding inside the infinite trees; then a note connecting back to the iso-recursive world (§21.11).

## §21.1 — Induction and coinduction, side by side

### The shared machinery: generating functions and fixed points

Fix some universe $U$ — "everything in the world" the definition could be talking about. A **generating function** $F \in \mathcal{P}(U) \to \mathcal{P}(U)$ takes a set of "already-known facts" and produces the set of facts that follow from them in one step. $F$ is required to be **monotone**: $X \subseteq Y \implies F(X) \subseteq F(Y)$ — knowing more premises never costs you a conclusion.

Two properties of a set $X \subseteq U$ matter:

- $X$ is **$F$-closed** if $F(X) \subseteq X$ — every conclusion you can derive from $X$ is already in $X$. Nothing new to add.
- $X$ is **$F$-consistent** if $X \subseteq F(X)$ — every member of $X$ is itself justified by (other) members of $X$. $X$ is "self-supporting."

These are almost opposite conditions, and that asymmetry is the whole chapter in miniature. The **Knaster–Tarski theorem** (21.1.4) says:

1. The intersection of all $F$-closed sets is the *least* fixed point of $F$, written $\mu F$.
2. The union of all $F$-consistent sets is the *greatest* fixed point of $F$, written $\nu F$.

From this falls out the pair of reasoning principles that structure everything downstream:

$$
\textbf{Induction: } X \text{ is } F\text{-closed} \implies \mu F \subseteq X
\qquad\qquad
\textbf{Coinduction: } X \text{ is } F\text{-consistent} \implies X \subseteq \nu F
$$

Read as proof techniques: to show a property $P$ (viewed as its characteristic set) holds of *everything* in the inductively-defined set $\mu F$, show $P$'s set is closed under $F$ — this is ordinary "prove it for the premises, get it for the conclusion" induction. To show a *specific element* $x$ belongs to the coinductively-defined set $\nu F$, you don't need to unwind an infinite justification — you need to exhibit *some* self-consistent set $X$ containing $x$. That's it. The infinite regress is discharged in one shot by finding a set closed under "being justified," not by literally walking down the infinite tree.

**Why this matters for the cycling subtyping example above:** the inductive relation (smallest set closed under the rules) rejects $\mu X.X{\to}X <: \mu X.X{\to}X$ because there's no finite closed derivation. But take $X = \{(\mu X.X{\to}X,\ \mu X.X{\to}X)\}$: is $X$ *consistent* — is the pair justified by (that very) set $X$? Yes: unfolding both sides and applying the arrow rule to $(\mu X.X{\to}X, \mu X.X{\to}X) \in X$ regenerates exactly the same pair. $X$ is self-consistent, so by coinduction $X \subseteq \nu F$, so the pair is in the *greatest* fixed point. Coinduction is precisely "circular reasoning, but rigorously licensed" — provided the circle closes on itself without contradiction.

### Grounding: closure vs. consistency as code

The distinction reads directly as two different search strategies. Closure ($F(X) \subseteq X$) is what a **terminating recursive function** computes: it consumes a derivation from the leaves up and never revisits a node. Consistency ($X \subseteq F(X)$) is what a **memoized/assumption-based search** computes: it's allowed to *assume* the very goal it's trying to prove, provided that assumption never gets contradicted before the recursion closes the loop — this is precisely what makes cyclic-reference type checkers, unification with occurs-check-free recursive bindings, and bisimulation-based equivalence checkers (used for concurrency and, not coincidentally, for many practical implementations of recursive-type equality) all work.

```rust
// Inductive style: prove-then-cache. This terminates only if the
// recursion is genuinely finite (well-founded).
fn prove_inductive(goal: Goal) -> bool {
    // must recurse into strictly smaller premises with no cycles
    goal.premises().iter().all(prove_inductive)
}

// Coinductive style: assume the goal while proving it, and only
// fail if a *contradiction* (an unsupported / unjustified leaf) is found.
// This is what makes cyclic recursive-type checks terminate.
fn prove_coinductive(goal: Goal, assumed: &mut HashSet<Goal>) -> bool {
    if assumed.contains(&goal) {
        return true; // self-consistency: the cycle closes, no contradiction found
    }
    assumed.insert(goal.clone());
    match goal.support() {
        None => false,               // unsupported: F-inconsistent, fails
        Some(premises) => premises.into_iter().all(|p| prove_coinductive(p, assumed)),
    }
}
```

`prove_coinductive` *is* §21.5's `gfp`/`gfp^t` algorithms in embryo — the rest of the chapter is this idea, made precise and proved correct.

Lean's kernel, by contrast, is fundamentally an *inductive* engine: `Nat.rec`, structural recursion, and well-founded recursion all require the "prove-then-cache" shape above, terminating by construction. Lean 4's own coinductive support (e.g. `Stream'`, corecursive definitions via `partial def` or the QPF-based coinductive machinery in `Mathlib`) exists precisely because plain inductive datatypes cannot represent something like an infinite tree type without a manufactured escape hatch — this is the same tension the chapter is resolving mathematically.

```lean
-- Lean has no *native* general coinductive definition mechanism the way
-- Coq does; the standard workaround is `partial def` (unchecked termination,
-- trusted) or building on a coinductive primitive like `Stream'`.
-- Below: an infinite tree type as a `Stream'`-style corecursive value,
-- echoing Top→(Top→(Top→...)) from Figure 21-1.
partial def infiniteArrowTower : Stream' Unit :=
  Stream'.corec (fun _ => ((), ())) ()
-- `partial` is Lean's admission that this isn't structurally decreasing —
-- exactly the situation coinduction is built to formalize honestly instead
-- of trusting.
```

## §21.2 — Types as trees, finite and infinite

To apply the induction/coinduction machinery to subtyping, Pierce first needs a precise notion of "infinite type." He restricts to three constructors ($\to$, $\times$, $\mathrm{Top}$) for the chapter and represents a type as a **tree**: formally, a partial function $T \in \{1,2\}^* \rightharpoonup \{\to, \times, \mathrm{Top}\}$ from *paths* (sequences of left/right choices) to node labels, satisfying the obvious well-formedness constraints (the root is defined; if a node is defined its ancestors are; $\to$/$\times$ nodes have exactly two children; $\mathrm{Top}$ nodes have none).

$$
(\mathrm{Top}\times\mathrm{Top})\to\mathrm{Top}
\qquad\text{vs.}\qquad
\mathrm{Top}\to(\mathrm{Top}\to(\mathrm{Top}\to\cdots))
$$

The first is a finite tree (five nodes); the second is genuinely infinite — an infinite right-leaning spine of arrows, each with a $\mathrm{Top}$ hanging off its left child. Crucially, **the same generating-function trick used for subtyping applies to the types themselves**: the grammar $T ::= \mathrm{Top} \mid T{\times}T \mid T{\to}T$, read as a generating function on trees, has $\mathcal{T}_f$ (finite trees) as its *least* fixed point and $\mathcal{T}$ (all trees, finite or infinite) as its *greatest* fixed point. Induction gives you finite types; coinduction gives you all of them, for free, from the same grammar — you're just choosing which fixed point to take.

## §21.3 — Subtyping, defined twice, in exactly the same shape

Now the generating function for subtyping itself. On finite trees, subtyping is the *least* fixed point of

$$
\mathcal{S}_f(R) = \{(T,\mathrm{Top}) \mid T \in \mathcal{T}_f\} \;\cup\; \{(S_1{\times}S_2,\, T_1{\times}T_2) \mid (S_1,T_1),(S_2,T_2)\in R\} \;\cup\; \{(S_1{\to}S_2,\, T_1{\to}T_2) \mid (T_1,S_1),(S_2,T_2)\in R\}
$$

— exactly the familiar `S-Top`/`S-Prod`/`S-Arrow` rules (contravariant domain, covariant range), reformulated as one set-transformer instead of three inference rules. On *all* trees (finite and infinite), subtyping is the **greatest** fixed point of the identical-looking function $\mathcal{S}$ (same clauses, just quantified over the bigger universe $\mathcal{T}\times\mathcal{T}$). This is the chapter's central move, stated plainly: *the inference rules don't change at all going from finite to infinite subtyping — only the choice of fixed point does.* Finite types get induction (build up from the leaves); infinite types get coinduction (self-consistency, no leaves required).

**Why this has to be the greatest, not least, fixed point:** the least fixed point of $\mathcal{S}$ over the infinite universe would again only capture pairs with a *finite* justifying derivation — but most interesting subtyping facts about infinite regular trees (like $\mu X.X{\to}X <: \mu X.X{\to}X$ above) only have infinite ones.

Transitivity of this infinite-tree subtype relation is not optional — Pierce spells out why via a preservation argument identical in spirit to [[Type-Safety]]'s: if $S <: T <: U$ but not $S <: U$, then a value of type $S$ passed through subsumption twice types-checks as $U$, and a one-step reduction can produce an ill-typed term. The proof that $\nu\mathcal{S}$ is transitive (21.3.6–21.3.7) is a genuinely coinductive argument: show that $\mathrm{TR}(\mathcal{S}(R)) \subseteq \mathcal{S}(\mathrm{TR}(R))$ for the "transitive-closure" generator $\mathrm{TR}$, and coinduction upgrades that one-step fact into "the whole transitive closure of $\nu\mathcal{S}$ is already inside $\nu\mathcal{S}$" — without ever exhibiting an actual derivation, finite or infinite.

## §21.4 — Why you can't just add a transitivity *rule* here

[[Metatheory-and-Algorithms-for-Subtyping]] and Ch. 16's `S-Trans` rule worked as a convenience: because subtyping there is an inductive (least-fixed-point) definition, Proposition 21.4.1 shows that unioning two rule sets $F, G$ and taking the least fixed point of the union gives you exactly the smallest relation closed under *both* — so adding `S-Trans` to the rule set for finite subtyping is harmless; it doesn't change what's in $\mu F$ beyond baking in a fact that was already implicit (transitivity was admissible, recall Ch. 16).

That trick **fails outright** for coinductive definitions. If you union in a transitivity generator $\mathrm{TR}$ and take the *greatest* fixed point $\nu(F \cup \mathrm{TR})$, Exercise 21.4.2 shows you get the **total relation** on $U \times U$ — everything related to everything. Intuitively: greatest-fixed-point membership only demands *some* self-consistent justification exists, and once transitivity is available as a generating rule, any pair $(x,y)$ can trivially "justify" itself by picking an arbitrary intermediate $z$ and asserting $(x,z)$ and $(z,y)$ are also in the (same, self-justifying) set — the self-consistency requirement, which was doing real work for the finite/inductive rules, becomes vacuous once transitivity gives you a free wildcard connector. This is why the algorithmic presentations for infinite/coinductive subtyping — including everything from §21.5 onward — never include a transitivity rule; they can't, structurally.

## §21.5–§21.6 — From "is it in $\nu F$?" to an algorithm

Coinduction tells you *how to prove* an element is in $\nu F$ (exhibit a consistent set containing it) but not how to *search for* one mechanically. That's the gap §21.5 closes.

### Support functions: running $F$ backwards

For most generating functions of interest (including subtyping's), each element $x$ has at most one *minimal* set $X$ such that $x \in F(X)$ — call $F$ **invertible**, and call that minimal set $\mathrm{support}_F(x)$. Concretely for subtyping's $\mathcal{S}$: the support of $(S_1{\to}S_2, T_1{\to}T_2)$ is $\{(T_1,S_1), (S_2,T_2)\}$ — read literally as "to justify this pair, I need exactly these two smaller pairs," which is nothing but the premises of the `S-Arrow` rule, reified as a function you can call. An element with $\mathrm{support}(x) = \uparrow$ (undefined) is **unsupported** — no rule justifies it at all (e.g. $(\mathrm{Top}, S_1{\to}S_2)$, since only `T <: Top` matches on the right, and the shapes don't line up).

This gives a graph-reachability picture (Figure 21-2): draw an edge from $x$ to each element of $\mathrm{support}(x)$. Then $x \in \nu F$ iff no unsupported node is reachable from $x$ — you can walk forever through cycles without ever hitting a dead end.

### The `gfp` family: four algorithms, same correctness argument, increasing efficiency

The book gives four versions, all provably equivalent, that differ only in *how* they avoid recomputing support sets already explored:

$$
\mathrm{gfp}(X) = \begin{cases}
\text{false} & \text{if } \mathrm{support}(X) \uparrow \\
\text{true} & \text{if } \mathrm{support}(X) \subseteq X \\
\mathrm{gfp}(\mathrm{support}(X)\cup X) & \text{otherwise}
\end{cases}
$$

is the naive version (Definition 21.5.5): grow $X$ by repeatedly unioning in its own support, fail the moment something unsupported shows up, succeed the moment the set stops growing (that's exactly $X$ becoming self-consistent). Theorem 21.5.9 proves this **sound and complete relative to termination** — `true` implies $X \subseteq \nu F$, `false` implies $X \not\subseteq \nu F$ — but says nothing about whether it terminates at all, because in general $\mathrm{reachable}(X)$ can be infinite.

Termination is rescued by restricting to **finite-state** generating functions — ones where $\mathrm{reachable}(x)$ is always finite (Definition 21.5.11, Theorem 21.5.12): then the search space is finite and `gfp` provably halts.

The three refinements — $\mathrm{gfp}^a$ (thread an assumption set $A$ so support is computed once per element, not once per recursive call), $\mathrm{gfp}^s$ (process one goal at a time instead of a whole set), and $\mathrm{gfp}^t$ (non-tail-recursive, uses the call stack itself to hold pending subgoals, threading the accumulated assumption set through) — are all the *same* algorithm engineering-wise: memoize on the assumption set to avoid recomputation, exactly the technique any implementer reaches for independently when they discover a naive recursive equivalence-checker looping on cyclic types.

```rust
// gfp^t (Definition 21.6.4), specialized to a subtyping-shaped Goal.
// This is a direct, load-bearing translation: it is essentially the
// only way to implement equi-recursive-type subtyping in a real checker.
use std::collections::HashSet;

fn gfp_t(goal: (Ty, Ty), assumed: &mut HashSet<(Ty, Ty)>) -> bool {
    if assumed.contains(&goal) {
        return true; // already assumed; cycle closes without contradiction
    }
    let Some(premises) = support(&goal) else {
        return false; // unsupported: definitely not in the subtype relation
    };
    assumed.insert(goal.clone());
    premises.into_iter().all(|p| gfp_t(p, assumed))
}

fn is_subtype(s: &Ty, t: &Ty) -> bool {
    gfp_t((s.clone(), t.clone()), &mut HashSet::new())
}
```

```python
# gfp^a (Definition 21.6.1) as a short illustrative sketch — process a
# whole frontier set at once, tracking what's already been assumed.
def gfp_a(assumed, frontier, support):
    while frontier:
        new_support = set()
        for x in frontier:
            s = support(x)
            if s is None:
                return False           # unsupported element found
            new_support |= s
        assumed |= frontier
        frontier = new_support - assumed
    return True
```

## §21.7 — Regular trees: the finiteness that makes this decidable at all

Instantiating `gfp`/`gfp^t` with $\mathcal{S}$ terminates only on **finite-state** inputs — but subtyping's universe is *all* trees, most of which have infinitely many distinct subtrees, so termination isn't automatic. The rescue: restrict to **regular trees** — trees with only finitely many distinct subtrees (Definition 21.7.2), written $\mathcal{T}_r$.

$\mathrm{Top}\times(\mathrm{Top}\times(\mathrm{Top}\times\cdots))$ is regular (only two distinct subtrees ever occur: itself and $\mathrm{Top}$) even though it's infinite. By contrast, a tree like $B\times(A\times(B\times(A\times(A\times(B\times\cdots$ where consecutive $B$s get separated by ever-more $A$s is *not* regular — every subtree is syntactically distinct from every other, so an unbounded number of states would need to be explored to verify even a single subtyping fact about it. Regularity is exactly "finitely representable" — it's the tree-level analogue of a finite-state automaton's transition graph vs. an unbounded one. Proposition 21.7.4 makes the connection precise: restricting $\mathcal{S}$ to regular trees makes it finite-state, because $\mathrm{reachable}_{\mathcal{S}_r}(S,T) \subseteq \mathrm{subtrees}(S) \times \mathrm{subtrees}(T)$, and both factors are finite by definition of regularity.

## §21.8 — $\mu$-types: the finite syntax for regular trees

Regularity tells you *which* infinite trees are well-behaved; it doesn't yet tell you how to *write one down* in a program. That's what $\mu$-types are for — Pierce's familiar $\mu X.T$ notation, now given a formal semantics as a *name* for an infinite regular tree.

A raw $\mu$-type is generated by $T ::= X \mid \mathrm{Top} \mid T{\times}T \mid T{\to}T \mid \mu X.T$. Not every such expression denotes a sensible tree, though — $\mu X.X$ unfolds to itself forever without ever producing a node label, so there's no tree to read off. The fix is **contractivity** (Definition 21.8.2): every bound variable occurrence must be guarded by at least one $\to$ or $\times$ between it and its binder. Contractive (i.e. well-formed) $\mu$-types are exactly the ones for which the function

$$
\mathrm{treeof}(\mu X.T) = \mathrm{treeof}([X \mapsto \mu X.T]T)
$$

is well-defined by induction on the lexicographic pair (path length so far, number of leading $\mu$-binders remaining) — each recursive step either descends into a $\to$/$\times$ child (shrinking the first component) or unfolds one $\mu$ (shrinking the second, without growing the first). This is a genuinely inductive, terminating definition of a function that *produces an infinite object* — a useful reminder that induction and coinduction aren't "finite vs. infinite" in some naive sense; you can define, by ordinary structural induction, a function whose output happens to be an infinite tree.

Subtyping on $\mu$-types themselves is given by a new generating function $\mathcal{S}_m$ — the same three tree-level clauses, plus two "unfold-and-recurse" clauses corresponding to the *folding* rules

$$
\frac{S <: [X\mapsto\mu X.T]T}{S <: \mu X.T} \qquad\qquad \frac{[X\mapsto\mu X.S]S <: T}{\mu X.S <: T}
$$

with a deliberate asymmetry added (the second clause explicitly excludes $T = \mathrm{Top}$ or $T$ starting with $\mu$) purely to keep $\mathcal{S}_m$ invertible — otherwise the two folding clauses could both fire on the same pair and $\mathrm{support}$ wouldn't be a well-defined (unique) function. This is a nice, honest bit of engineering pragmatism inside a "pure" mathematical definition: the theory bends slightly to keep the *algorithm* implementable.

The **soundness/completeness theorem** tying it all together (21.8.7):

$$
(S,T) \in \nu\mathcal{S}_m \iff \mathrm{treeof}(S,T) \in \nu\mathcal{S}
$$

— subtyping *syntax* on finite $\mu$-expressions agrees exactly with subtyping *semantics* on the infinite trees they denote. This is the theorem that licenses everything downstream: you're now free to reason about $\mu$-types with a finite algorithm and know it computes the "real," infinite-tree answer.

## §21.9–§21.10 — Why the algorithm actually terminates (and a cautionary tale about how *not* to write it)

Instantiating `gfp^t` with $\mathrm{support}_{\mathcal{S}_m}$ gives the concrete `subtype` algorithm of Figure 21-4 — the pseudocode you'd actually type into a compiler. Termination needs $\mathrm{reachable}_{\mathcal{S}_m}(S,T)$ to be finite for *any* pair of $\mu$-types, which is not obvious by inspection: unfolding $\mu X.T$ substitutes a whole type for a variable, and naive structural induction on the substituted body doesn't visibly decrease.

Pierce's proof (following Brandt and Henglein 1997) threads a needle: define **top-down subexpressions** ($S \sqsubseteq T$, generated by literally following the same unfold-then-descend path the algorithm takes) and **bottom-up subexpressions** ($S \unlhd T$, which instead collect subexpressions of the *unsubstituted* body first, and only apply the unfolding substitution afterward). The bottom-up notion is trivially finite by ordinary structural induction (Lemma 21.9.8) — it never has to "look inside" an unfolding. The top-down notion is what the algorithm actually explores. The technical core of the section (Lemma 21.9.9, Proposition 21.9.10) is a substitution lemma showing every top-down subexpression is *also* a bottom-up one — so top-down subexpressions inherit finiteness for free, and with it, termination of `subtype` (Proposition 21.9.11).

§21.10 is a worked cautionary example: a version of the same algorithm (`subtype_ac`, Amadio and Cardelli's original 1993 algorithm) that drops the *returned* assumption set and instead only threads assumptions downward through recursive calls, never merging results back up across sibling calls. It computes the identical relation, but on the family $S_n = \mu X.\mathrm{Top}\times X$ growing linearly and matched against a similarly-linear $T_n$, checking $S_n <: T_n$ costs $O(2^n)$ recursive calls instead of $O(n^2)$ — a vivid demonstration that *what* you memoize (per-element assumptions, threaded and merged, vs. nothing) is the entire difference between a practical algorithm and an exponential one, even when both are "obviously" correct and terminating.

## §21.11 — Back to iso-recursive types: the Amber rule

Equi-recursive types treat $\mu X.T$ and its unfolding as outright identical, which is what licensed the coinductive "unroll to the limit" story above. Iso-recursive types (the `fold`/`unfold`-witnessed presentation from Ch. 20) keep $\mu$ *rigid* — it matters syntactically where a $\mu$ sits — so subtyping needs its own rule rather than reducing to infinite unrolling:

$$
\frac{\Sigma,\, X<:Y \;\vdash\; S <: T}{\Sigma \;\vdash\; \mu X.S <: \mu Y.T} \;\text{(S-Amber)}
\qquad\qquad
\frac{(X<:Y)\in\Sigma}{\Sigma \vdash X <: Y} \;\text{(S-Assumption)}
$$

named for Cardelli's Amber language (1986). $\Sigma$ here plays exactly the role the assumption set $A$ played in `gfp^t`/`subtype` — but notice the crucial difference: `S-Amber` recurses on the *bodies* $S, T$ with fresh *type variables* $X, Y$ standing in for the recursive occurrences, never substituting the whole recursive type back into itself the way the equi-recursive `subtype` algorithm does. That's a strictly cheaper (and trivially terminating, no §21.9-style finiteness proof required) approximation of the same idea — the price is that it's typically less complete than full equi-recursive subtyping (Exercise 21.11.1 asks you to find a witnessing pair), since the equi-recursive relation gets to unfold arbitrarily far and compare structurally, while Amber-style subtyping only ever compares one unfolding "layer" against a coinductive assumption. The notes flag that this is also the shape nominal subtyping (Featherweight Java, [[Nominal versus Structural Typing]]) takes.

## Where this leads

```
   Ch. 20 Recursive Types (iso- vs. equi-, fold/unfold)
                    |
                    v
   Ch. 21 THIS CHAPTER: coinduction as the proof theory
   for "definitionally equal to its own unfolding"
     |                                  |
     v                                  v
  §21.1-4 coinduction,            §21.5-10 membership-checking
  finite/infinite trees,          algorithms (gfp family),
  subtyping as nu(S)              regular trees, mu-types,
                                  termination proof
                    |
                    v
   §21.11 Amber rule -> nominal subtyping (Ch. 19, FJ)
                    |
                    v
   Ch. 28 Metatheory of Bounded Quantification
   (undecidability results reuse this chapter's finite-state /
   reachability vocabulary to show *when* a similar algorithm
   provably cannot exist)
```

This chapter is a direct hit on the checker/verifier side of the standing project: the `gfp`/`gfp^t` family *is* the general algorithmic pattern for deciding membership in any coinductively-specified relation — which is exactly the shape a Rust type-checker needs for recursive/cyclic type equality, and the shape a proof search engine needs whenever a goal can legitimately depend on itself (mutually recursive lemmas, cyclic coinductive proofs, bisimulation-based equivalence). The assumption-threading trick (`gfp^a`/`gfp^t`, and Amber's $\Sigma$) is the same "assume the goal, discharge by non-contradiction" move that shows up under different names in cycle detection for unification variables and in coalgebraic/bisimulation proofs of process equivalence — worth recognizing on sight, since it will recur any time "equality up to unfolding" needs to be checked mechanically rather than just stated.

The one place this chapter *doesn't* reach, deliberately: it never needs metavariables or a `?`-style incomplete term the way unification/elaboration does — every $\mu$-type here is fully concrete. The connection to the elaborator side of the standing project is looser here than for, say, [[The-Curry-Howard-Correspondence]] or unification-flavored chapters; treat the assumption-set technique as the transferable mechanism, not the specific subtyping content.
