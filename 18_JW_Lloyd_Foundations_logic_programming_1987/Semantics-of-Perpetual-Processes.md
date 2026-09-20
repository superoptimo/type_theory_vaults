---
title: Semantics of Perpetual Processes
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 6, §25–27 (pp. 173–194)
tags: [infinite-terms, compactness, complete-herbrand-universe, coinduction, greatest-fixpoint]
---

[[book-guidelines|↩ Back to guidelines]]

## The loose thread this book has been carrying since chapter 1

Two loose threads, both flagged early and left unresolved until now, get tied off in this final chapter. First, [[The-Occur-Check-Problem]]: naive [[Unification|unification]] without an occur check can produce a binding like $x = f(x)$ — not a well-formed *finite* term, and simply forbidden throughout chapters 1–5. Second, [[Fixpoint-Theory]] and [[Declarative-Semantics-of-Definite-Programs]] both flagged, and left mysterious, the fact that $\mathrm{gfp}(T_P) \ne T_P{\downarrow}\omega$ in general — an asymmetry between least and greatest fixpoints with no explanation given at the time. This chapter reveals both loose ends are the *same* phenomenon: the ordinary (finite-term) Herbrand universe is missing exactly the objects — infinite terms — that would make both problems disappear. Rather than dismissing infinite terms as pathological, Lloyd builds them a rigorous home: a **compact metric space** of possibly-infinite terms, in which greatest fixpoints behave exactly as nicely as least fixpoints do in the finite case, and in which some previously-forbidden circular bindings turn out to have a legitimate, useful meaning after all.

**Why this belongs at the center of your own project:** this chapter is the cleanest worked example in the entire book of **coinductive reasoning about infinite/non-terminating computation**, treated with full topological and fixpoint-theoretic rigor rather than hand-waved. If your compiler will ever need to reason about non-terminating processes (a server loop, a reactive system, a lazily-unfolded infinite proof object, a coinductive stream type), this chapter's machinery — compactness as the tool that makes greatest fixpoints computable, and a precise "computable at infinity" criterion distinguishing genuine productive infinite computation from mere non-termination — is the right formal template.

## Infinite terms as labelled trees, and why compactness is the missing ingredient

A **term** (Lloyd's generalized definition, chapter 6 only) is formalized as a function from a *tree* domain $\subseteq \omega^*$ (finite lists of naturals, satisfying prefix-closure and bounded-branching) into the signature — literally, a term is its own **abstract syntax tree**, now permitted to be infinite. The **truncation** $\sigma_n(t)$ cuts $t$ at depth $n$, marking cut branches with a fresh symbol $\Omega$. This licenses a genuine **metric** on terms: $d(s,t) = 2^{-\alpha(s,t)}$ where $\alpha(s,t)$ is the least depth at which $s,t$'s truncations first differ — an **ultrametric** (satisfying the strengthened triangle inequality $d(x,z) \le \max(d(x,y), d(y,z))$), the standard way to metrize a space of trees/sequences by "how long do they agree before diverging," familiar from $p$-adic numbers or from any coinductive-stream bisimulation-distance construction.

**Proposition 25.2 is the load-bearing fact of the entire chapter**: this space of terms is **compact** *iff the underlying signature is finite*. Compactness — every sequence has a convergent subsequence — is exactly the topological property that makes an infinite iterative process (like building up an infinite term one level at a time via a "fair" derivation) *guaranteed to converge to an actual point in the space*, rather than merely approaching a limit that doesn't exist within the space. This is precisely why the book restricts attention throughout to finite signatures (finitely many constants/function/predicate symbols) — it's not a simplifying assumption made for convenience, it's the *exact* hypothesis compactness needs.

## Why compactness fixes the $\mathrm{gfp} \ne T_P{\downarrow}\omega$ asymmetry

Recall (from [[Fixpoint-Theory]]) that Kleene's theorem gives $\mathrm{lfp}(T) = T{\uparrow}\omega$ for *any* continuous $T$ on *any* complete lattice — no compactness needed, because $\mathrm{lub}$ over a directed *ascending* chain never "loses" information the way a descending intersection can. The dual direction is harder: $\mathrm{gfp}(T) = T{\downarrow}\omega$ needs the descending chain $T{\downarrow}0 \supseteq T{\downarrow}1 \supseteq \cdots$ to not "lose" limit points as it shrinks — and that's exactly what compactness guarantees. Lloyd's **Theorem 26.5** (Closedness of $T'_P$: closed sets map to closed sets) plus **Theorem 26.7** (Weak Continuity, via the limit-superior of a sequence of sets) combine in **Corollary 26.8** to give exactly the missing ingredient — an *intersection property* for $T'_P$ that ordinary $T_P$ lacks — and **Theorem 26.9(a)** delivers the payoff: $\mathrm{gfp}(T'_P) = T'_P{\downarrow}\omega$, the exact symmetric counterpart to Kleene's theorem, now holding because the space is compact.

This is worth internalizing as a general principle, not just a fact about this one book: **greatest fixpoints of a monotone operator are well-behaved (computable by simple iteration) exactly when the underlying space is compact** — compactness is doing for descending iteration what directedness alone does for ascending iteration. Any time you reason coinductively about infinite objects (streams, infinite proof traces, bisimilarity as a greatest fixpoint of a "matching" relation), ask whether your domain has this compactness property; if it doesn't, expect the same pathologies Lloyd catalogs (his three counterexamples showing $\mathrm{gfp}(T_P) \ne T_P{\downarrow}\omega$ persist even in the *ordinary*, non-compact finite-term setting).

## "Computable at infinity": productivity, made precise

A **perpetual process** is a definite program that runs forever while still doing "useful" computation — but "useful" needs a precise definition, or every non-terminating program would qualify trivially. Lloyd's answer: a (possibly infinite) atom $A$ is **computable at infinity** if there's a finite atom $B$ and an infinite *fair* derivation $\leftarrow B = G_0, G_1, \ldots$ with mgu's $\theta_1,\theta_2,\ldots$ such that $d(A, B\theta_1\cdots\theta_k) \to 0$ as $k \to \infty$ — the successive partial answers *genuinely converge* to $A$ in the metric.

Worked examples make this concrete and connect it directly to lazy/coinductive programming idioms you already know:
```prolog
fib(X) :- fib1(0,1,X).
fib1(X,Y,Z.W) :- plus(X,Y,Z), fib1(Y,Z,W).
```
computes the *infinite* Fibonacci stream — this is literally Haskell's `fibs = 0 : 1 : zipWith (+) fibs (tail fibs)`, expressed as a perpetual logic-program process instead of a lazily-evaluated corecursive stream definition. The **Hamming numbers** example (merging three filtered streams of multiples of 2, 3, 5) is the classic coinductive-stream textbook example, again reappearing here in Horn-clause form decades before it became a standard functional-programming exercise.

**Why "converges to" and not merely "is a member of the intersection of possible answers" (Proposition 27.1's careful equivalent reformulation, and the counterexample motivating it):** Lloyd shows a *weaker*, membership-only definition would wrongly certify `p(f(x)) :- p(f(x)).` as computing `p(fff...)` "at infinity" — but this program does no actual work; it just loops rewriting the same finite prefix forever without ever committing more information. Requiring genuine **metric convergence** (equivalently, Prop 27.1: the intersection of successive answer sets shrinks to the *singleton* $\{A\}$, not just *contains* $A$ among other possibilities) is exactly what rules this out. **This convergence criterion is precisely a productivity check** — the same discipline a coinductive/corecursive definition needs to be admitted as well-formed in a proof assistant (Coq's guardedness condition, Agda's sized types, Lean's `Stream'`/`WellFounded`-adjacent machinery all exist to enforce, syntactically, exactly the semantic property this metric convergence condition checks directly): *each step of unfolding must genuinely produce new, determined information*, not merely mark time.

## Soundness without completeness — and why that's the honest final word

**Theorem 27.2**, the chapter's main result: $C_P \subseteq \mathrm{gfp}(T'_P)$ — every atom computable at infinity really is in the greatest complete-Herbrand-model fixpoint. This is a clean, provable soundness result. Completeness — $C_P = \mathrm{gfp}(T'_P) \setminus B_P$ — **fails**, and Lloyd gives three sharp counterexamples pinpointing exactly why: a unit fact `p(f(X)).` puts $p(fff\ldots)$ in $\mathrm{gfp}(T_P)$ trivially (it's a fixpoint witness) without any derivation *converging* to it (there's no finite starting atom whose successive resolvents approach it); a program exploiting the occur-check gap (`p(X,f(X)) :- p(X,X).`) puts a circular-looking atom in $\mathrm{gfp}(T_P)$ purely because $T'_P$ doesn't itself enforce the occur check, with no genuine derivation behind it at all.

**The book ends, deliberately, without full resolution** — Lloyd names $\mathrm{gfp}(T'_P)$ as the right *candidate* intended interpretation for a perpetual process (the coinductive analogue of $\mathrm{lfp}(T_P) = M_P$ for terminating programs) but is explicit that it "generally contains infinite atoms which are not intuitively computable at infinity," leaving full completeness (and a semantics for genuine inter-process communication/concurrency) as open research. **This is worth sitting with as a model of intellectual honesty in a foundations text**: a soundness theorem plus a precisely-diagnosed completeness gap, rather than a false claim of a fully closed theory — exactly the standard you should hold your own verifier's documentation to when a checking procedure is sound but not complete (which, for any realistic refinement-type system reasoning about Turing-complete programs, it inevitably will be, by Rice's theorem).

## Grounding: coinduction and greatest fixpoints in practice

```rust
// A lazy/corecursive stream, exactly mirroring the fib/1 perpetual process —
// each `next()` call is one step of the "fair derivation" converging toward
// the infinite intended value, just as d(A, Bθ1...θk) -> 0 in the chapter.
struct Fib { a: u64, b: u64 }
impl Iterator for Fib {
    type Item = u64;
    fn next(&mut self) -> Option<u64> {
        let r = self.a;
        (self.a, self.b) = (self.b, self.a + self.b);
        Some(r) // productivity: each call genuinely advances toward more info
    }
}

// A "productivity" checker in the spirit of Prop. 27.1's convergence
// criterion: reject a corecursive definition unless each unfolding step
// is guaranteed to expose strictly more of the result (a guardedness check).
fn is_productive(step: &CorecStep) -> bool {
    matches!(step, CorecStep::Cons(_, _)) // must produce a head constructor
    // vs. CorecStep::Loop(_) which corresponds to p(f(X)) :- p(f(X)).
    // — spins without ever committing new information: rejected.
}
```

**In Lean**, this chapter's entire arc — greatest fixpoints, compactness-as-the-key-hypothesis, and a precise productivity criterion distinguishing genuine corecursion from mere non-termination — is the exact conceptual territory of **coinductive types and guarded corecursion**. Lean's `codata`/`Stream'`-style coinductive definitions (and the general theory of *bisimulation as a greatest fixpoint* of a matching relation on process behaviors) are the direct type-theoretic descendants of $\mathrm{gfp}(T'_P)$ here — where Lloyd needs compactness of an infinite-term metric space to make greatest-fixpoint iteration well-behaved, a dependently-typed kernel instead enforces a **syntactic guardedness condition** (every corecursive call must occur under a constructor) as a cheaper, decidable proxy for the same semantic productivity guarantee. If you ever implement coinductive/lazy verification objects in your own compiler (e.g. streaming symbolic execution over a possibly-infinite trace, or a lazily-unfolded invariant proof for an unbounded loop), this chapter is the rigorous semantic foundation underneath whatever syntactic guardedness check you end up enforcing.

## Where this leads

- **This chapter closes the book's two oldest open threads** — [[The-Occur-Check-Problem]]'s "circular bindings are simply forbidden" and [[Fixpoint-Theory]]/[[Declarative-Semantics-of-Definite-Programs]]'s unexplained $\mathrm{gfp}(T_P) \ne T_P{\downarrow}\omega$ asymmetry — by showing both are symptoms of reasoning within a non-compact space, and building the compact space where both resolve cleanly.
- **Directly load-bearing:** if your toolchain ever needs to reason about non-terminating reactive processes, streaming verification, or coinductive specifications (liveness properties, fairness assumptions, infinite trace semantics for a Hoare-logic-with-liveness extension), this chapter's pairing of *compactness* (for a computable greatest fixpoint) and *convergence-based productivity* (for distinguishing genuine progress from spinning) is the correct formal lens — reach for it before inventing an ad hoc guardedness check from scratch.
- The soundness-without-completeness ending is a fitting final data point in the book's running theme (see [[SLD-Resolution]], [[Negation-in-Logic-Programs]], [[Declarative-Error-Diagnosis]]) of proving exactly how far a sound procedure falls short of complete, and precisely characterizing the gap rather than glossing over it — the discipline this entire book models for how to present a verification technique's real, honest guarantees.
