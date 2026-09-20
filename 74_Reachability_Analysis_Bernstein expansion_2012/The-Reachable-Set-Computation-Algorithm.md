---
title: The Reachable Set Computation Algorithm
source: "Reachability Analysis for Polynomial Dynamical Systems Using the Bernstein Expansion (Dang & Testylier, 2012)"
chapter: "Sections 5.1–5.2 (context), 6.1–6.2, 7 (partial) — paper pp. 10–14"
tags: [static-analysis, sat-smt-csp, reachability-analysis, abstract-interpretation, linear-programming, bernstein-expansion, polynomial-optimization]
---

# The Reachable Set Computation Algorithm

[[book-guidelines|↩ Back to guidelines]]

## The problem this section actually has to close

By the time the paper reaches Section 6, it has assembled three separate pieces of machinery, each solved in isolation:

1. **Template polyhedra** ($\S$2.2) give you a fixed-shape convex set $\langle H, c \rangle$ — a conjunction $\bigwedge_i H^i x \le c_i$ over a *fixed* matrix $H$, where only the coefficient vector $c$ varies. Cheap to intersect, union, and order ($c \preceq c'$), unlike general polyhedra.
2. **The Bernstein expansion** ($\S$3.1) gives you, for a polynomial on the unit box $B = [0,1]^n$, a set of control points whose convex hull contains the polynomial's graph — hence a cheap way to *bound* a polynomial's range.
3. **Bound-function construction** ($\S$4) turns those control points into actual affine (linear) functions $l(x) \le p(x) \le u(x)$, and ($\S$5) extends this from "domain is the unit box" to "domain is an arbitrary bounded polyhedron $P$," via either a box approximation or an exact change of variables.

None of these three pieces, alone, computes a reachable set. What's still missing is the glue: given a polynomial map $\pi$, a template $H$, and a current polyhedron $X_k$, how do you actually produce the *next* polyhedron $X_{k+1} \supseteq \pi(X_k)$, one number $c_i$ at a time, without ever solving a polynomial optimization problem? That glue is exactly what Chapter 6 supplies — and it's the payoff the whole paper has been building toward. If you're going to remember one thing from the paper's engineering core, this is where it happens.

**What breaks without this step:** you could have perfect template polyhedra and perfect Bernstein bound functions and still be stuck, because nobody has told you *how many* bound-function problems to solve, in what order, with what objective, or why solving them at all gives you a valid over-approximation rather than an accidental one. Sections 6.1–6.2 answer exactly that — they're the wiring diagram, not new machinery.

---

## 1. Restating the target as polynomial optimization (Eq. 3–4, recap)

Recall the actual goal, stated back in Section 3: given the current polyhedron $P$ and the polynomial map $\pi$, find a coefficient vector $c$ such that

$$\pi(P) \subseteq \langle H, c\rangle. \tag{3}$$

A sufficient condition for (3) is $\forall x \in P: H\pi(x) \le c$ — check every row of $H$ against every point of the (transformed) polyhedron. That licenses turning this into $m$ independent scalar optimization problems, one per template row $i \in \{1,\dots,m\}$:

$$\forall i \in \{1,\dots,m\}, \quad c_i = \max_{x \in P}\; \sum_{k=1}^n H^i_k\, \pi_k(x). \tag{4}$$

This is honest and correct, but computationally hostile: the objective $s_i(x) = \sum_k H^i_k \pi_k(x)$ is a genuine multivariate polynomial (a weighted sum of the polynomial components of $\pi$), and maximizing a polynomial over a polyhedron is, in general, an NP-hard nonconvex problem. Solving $m$ of these — one per template facet — at every reachability step is the "expensive polynomial optimization" the paper wants to eliminate. This is precisely the point where the Bernstein machinery from Sections 3–5 is supposed to pay off: instead of solving (4) directly, replace $s_i$ with a cheap linear surrogate.

**Why not just plug in an affine bound function for $s_i$ directly?** You could — compute one affine upper bound for the *composite* polynomial $s_i = \sum_k H^i_k \pi_k$ and maximize that instead. The paper actually mentions this is possible but deliberately avoids it: forming $s_i$ requires *composing* $n$ polynomials with the row $H^i$, which multiplies out into more monomial terms than any single $\pi_k$ had on its own — and more monomials means more Bernstein coefficients, which is exactly the cost the paper is trying to keep down. Section 6.1's actual move is more clever: decompose the bound *before* composing the polynomial.

---

## 2. Decoupling: bounding each $\pi_k$ separately (Eq. 9–10)

Rewrite the row-wise optimization from Eq. 4 for clarity as

$$\forall i \in \{1,\dots,m\}: \quad c_i = \max_{x \in P} s_i(x), \qquad s_i = \sum_{k=1}^n H^i_k \pi_k. \tag{9}$$

Now, instead of computing one bound function for the whole sum $s_i$, compute — **once, up front, independent of $i$** — an upper bound function $u_k(x)$ and a lower bound function $l_k(x)$ for *each individual component* $\pi_k$, $k = 1, \dots, n$, all with respect to the domain $P$. This only requires $n$ polynomials' worth of Bernstein-coefficient machinery, not $m$ potentially-larger composite ones.

Then, for each template row $i$, instead of re-optimizing a polynomial, assemble the bound *arithmetically* from pieces you already have:

$$\forall i \in \{1,\dots,m\}: \quad c_i = \sum_{k=1}^n H^i_k\, \omega_k, \tag{10}$$

where the per-term contribution $H^i_k \omega_k$ is defined by a sign case-split:

- If $H^i_k > 0$: $\;H^i_k \omega_k = H^i_k \cdot \max_{x \in P} u_k(x)$
- If $H^i_k \le 0$: $\;H^i_k \omega_k = H^i_k \cdot \min_{x \in P} l_k(x)$

**Why the sign split, precisely.** You're trying to *upper-bound* $s_i(x) = \sum_k H^i_k \pi_k(x)$. For a positive coefficient $H^i_k$, the term $H^i_k \pi_k(x)$ is largest when $\pi_k(x)$ is largest — so you want $\pi_k$'s *upper* bound $u_k$, and you maximize it (multiplying by a positive constant preserves direction). For a negative coefficient, multiplying by $H^i_k$ *flips* the inequality direction, so the term $H^i_k \pi_k(x)$ is largest when $\pi_k(x)$ is *smallest* — hence you want $\pi_k$'s *lower* bound $l_k$, and you take its minimum. This is the same sign bookkeeping you'd do by hand computing $\max(-3y)$ from bounds on $y$: you don't re-derive it each time, but every implementation of this has to get the four-way case (positive/negative coefficient × max/min) right, or the "over-approximation" silently becomes an under-approximation on some rows.

Each of the $n$ scalar problems $\max_{x\in P} u_k(x)$ or $\min_{x \in P} l_k(x)$ is now maximizing/minimizing an *affine* function over a polyhedron — a linear program. That's the whole trick: Eq. 9's $m$ polynomial optimizations become Eq. 10's $2n$ linear programs (one max and one min needed per component $k$, computed once and reused across however many template rows need that sign of $H^i_k$), each solvable in polynomial time by Simplex or an interior-point method.

---

## 3. Lemma 4 — why the decoupled bound is still sound

It isn't obvious for free that swapping (9) for (10) still gives a valid over-approximation — you've replaced one optimization with a different, structurally unrelated one. The paper closes this gap directly.

**Lemma 4.** *If a polyhedral coefficient vector $c \in \mathbb{R}^m$ satisfies (10), then $\pi(P) \subseteq \langle H, c \rangle$.*

**The proof idea**, spelled out from the source: because $u_k$ and $l_k$ are genuine upper/lower bound functions for $\pi_k$ on $P$ (Definition 1: $\forall x \in P, l_k(x) \le \pi_k(x) \le u_k(x)$), each term $H^i_k \omega_k$ computed by the sign rule is, by construction, an upper bound on $H^i_k \pi_k(x)$ for *every* $x \in P$ — that's exactly what the sign case-split guarantees. Summing valid termwise upper bounds gives a valid upper bound on the sum:

$$\forall x \in P: \quad s_i(x) = \sum_k H^i_k \pi_k(x) \;\le\; \sum_k H^i_k \omega_k = c_i.$$

So the solution $c_i$ to (10) is $\ge$ the solution to (9) (looser or equal, never tighter) — and since (9)'s solution already satisfies (3)/(4) by construction, (10)'s solution does too, just possibly with more conservative facets. In matrix form, $\forall x \in P: H\pi(x) \le c$, i.e. $\pi(P) \subseteq \langle H, c\rangle$. $\blacksquare$

**What you pay for this soundness.** The lemma's proof is exactly the reason (10) is *looser* than (9): summing independently-worst-case bounds is pessimistic whenever the true worst case of $s_i$ doesn't occur at the same $x$ that maximizes every individual $\pi_k$ (or minimizes it, per sign) simultaneously. If $\pi_1(x)$ peaks at $x = x^{(1)}$ and $\pi_2(x)$ peaks at $x = x^{(2)} \ne x^{(1)}$, decoupled bounding still adds $u_1(x^{(1)})$ and $u_2(x^{(2)})$ as if they co-occurred — Eq. 9's direct composition would never overshoot like that, because it optimizes the *actual* sum at one $x$. This is the tradeoff named explicitly in the guidelines' Key Question for this chapter: decoupling buys you tractability (LP instead of polynomial optimization) at the cost of tightness. It's the same phenomenon as "interval arithmetic overestimates because it forgets correlations between variables" — if you've hit that before in abstract-interpretation contexts, this is the identical failure mode, just applied to a sum of bounded terms instead of a product or difference.

---

## 4. Algorithm 1 — the full iteration

Everything above computes *one* template-coefficient row. Algorithm 1 wraps this into the actual reachability loop, over the discrete-time system $x[k+1] = \pi(x[k])$ with initial polyhedron $X_0$ and a fixed template $H$ (either user-supplied or forming a "regular" direction set) as an input, not something the algorithm derives.

Reproduced from the paper (variable names preserved):

```text
Algorithm 1  Reachable set computation
Inputs: convex polyhedron X0, polynomial π, templates H

k = 0
repeat
    β = UnitBoxMap(Xk)        // map the unit box B onto Xk (§5: box approx. or change of variables)
    γ = π ∘ β                  // compose π with that map — γ is a polynomial on B
    (u, l) = BoundFunctions(γ) // affine upper/lower bound functions of γ, per component, over B (§4)
    c̄ = PolyApp(u, l, H)      // solve the 2n LPs of Eq. 10 per template row (§6.1)
    Xk+1 = ⟨H, c̄⟩             // new template polyhedron
    k++
until k = kmax
```

Reading it against the pieces already built:

- **`UnitBoxMap`** is Section 5's contribution — it produces $\beta$, standing generically for *either* the affine box-approximation map $\tau$ (Lemma 3) *or* the vertex-based change-of-variables map $\nu$ (with the redundant $\alpha_l$ eliminated). The algorithm is written generically over $\beta$ precisely so both routes plug into the same loop — a genuine "strategy pattern" at the level of the pseudocode.
- **`γ = π ∘ β`** re-expresses $\pi$, which is only Bernstein-expandable over the unit box, as a polynomial that genuinely *lives* on the unit box, by pulling the current polyhedron $X_k$ back through $\beta$.
- **`BoundFunctions`** is Sections 3–4's machinery, applied component-wise to $\gamma$: for each of the $n$ components $\gamma_k$, compute Bernstein coefficients over $B$ and derive an affine $u_k, l_k$ pair (via the convex-hull-facet method or the least-squares method).
- **`PolyApp`** is exactly Section 6.1: given the $n$ bound-function pairs and the template $H$, solve the $2n$ linear programs of Eq. 10 and assemble each $c_i$.
- The loop terminates after a fixed number of steps $k_{\max}$ — there's no automatic convergence or fixpoint check here; the horizon is an input, matching how bounded-time safety verification is normally posed.

**Theorem 1 (Correctness).** *Let $\langle H, \bar c \rangle$ be the template polyhedron returned by Algorithm 1. Then $\pi(P) \subseteq \langle H, \bar c\rangle$.*

This is not a new proof — it's Lemma 3 (soundness of the unit-box mapping, $\pi(P) \subseteq \gamma(B)$) composed with Lemma 4 (soundness of the decoupled LP bound) composed with Lemma 2 (bound functions computed on a superset domain remain valid on any subset). Each stage of the pipeline is individually over-approximating and sound; the theorem is just the observation that composing sound over-approximations yields a sound over-approximation. This is the same discipline you'd expect from a Galois-connection-based abstract interpreter — every abstract transformer $\alpha \circ f \circ \gamma$ step is separately proven monotone/sound, and the whole-analysis soundness theorem is free once each piece is.

---

## 5. The refinement remark: bounding on $\tau^{-1}(X_k)$ instead of all of $B$

The paper closes Section 6.2 with an accuracy improvement that's easy to miss but genuinely useful, and worth stating precisely because it's a clean instance of "reuse an existing lemma to get a free tightening."

When $\beta$ is the box-approximation map $\tau$ (not the change-of-variables map), the bound functions $u, l$ computed by `BoundFunctions` are valid upper/lower bounds for $\gamma$ *over the entire unit box $B$* — because that's the domain the Bernstein expansion formula (Eq. 6) requires. But the actual polyhedron of interest is $X_k$, mapped backward through $\tau^{-1}$. Since $\tau$ maps $B$ onto (an over-approximating box around) $X_k$, and $X_k$ itself may occupy only a small, awkwardly-shaped region of that box, it follows that

$$\tau^{-1}(X_k) \subseteq B.$$

Now invoke **Lemma 2** — monotonicity of bound functions under domain inclusion: a bound function valid over a superset ($B$) remains valid over any subset ($\tau^{-1}(X_k)$), and in general becomes *tighter* there, since a bound only has to dominate the function on a smaller region. So instead of solving the LPs of Eq. 10 with $x$ ranging over all of $B$, you can restrict the optimization domain to $\tau^{-1}(X_k)$ — often strictly smaller than $B$ — and, by Lemma 4, the resulting polyhedron is *still* a valid over-approximation of $\pi(X_k)$, just a tighter one, for free (no extra bound-function recomputation, only a change in the LP's feasible region).

**What this buys you, concretely:** the accuracy gap between box approximation and change-of-variables (which the paper's later experiments consistently find in change-of-variables' favor) is partly attributable to $\tau^{-1}(X_k)$ being a much smaller subset of $B$ than $X_k$ was of the bounding box $\overline B$ — box approximation is "wasting" bound-function looseness on parts of $B$ that $X_k$ doesn't actually occupy. This remark recovers some of that lost precision without paying change-of-variables' vertex-enumeration cost.

---

## A Rust-shaped reading of Algorithm 1

The pseudocode is already close to code — worth making that literal, since seeing the soundness argument survive translation is the best test that you actually understood it (and this is exactly the "how you'd implement/check it" reading this topic calls for). A sketch, with the sign case-split from Eq. 10 made explicit as the load-bearing detail an implementation cannot get wrong:

```rust
/// A polynomial component πₖ, abstracted behind whatever internal
/// representation (power-base coefficients, etc.) the Bernstein
/// machinery needs.
trait Polynomial {
    /// Compose with an affine (or general) map β, producing γ = self ∘ β.
    fn compose(&self, beta: &AffineMap) -> Self;
    /// §3–4: compute an affine (lower, upper) bound-function pair over
    /// the unit box, via the convex-hull-facet or least-squares method.
    fn bound_functions(&self) -> (AffineFn, AffineFn);
}

/// Either strategy from §5 — deliberately unified behind one interface,
/// mirroring how Algorithm 1 is written generically over β.
trait UnitBoxMap {
    fn map(&self, x_k: &TemplatePolyhedron) -> AffineMap; // box approx. or change of vars
}

struct TemplatePolyhedron {
    h: Matrix,      // fixed template matrix H
    c: Vec<f64>,    // current coefficient vector c
}

fn poly_app(
    bounds: &[(AffineFn, AffineFn)], // (l_k, u_k) for k = 1..n
    h: &Matrix,                       // template, m x n
    domain: &Polyhedron,              // optimization domain for the LPs
) -> Vec<f64> {
    let m = h.rows();
    let n = h.cols();
    let mut c = vec![0.0; m];

    for i in 0..m {
        let mut c_i = 0.0;
        for k in 0..n {
            let h_ik = h[(i, k)];
            let (l_k, u_k) = &bounds[k];
            // Eq. 10's sign case-split — the one place a soundness bug hides.
            c_i += if h_ik > 0.0 {
                h_ik * lp_maximize(u_k, domain) // max u_k(x), x ∈ domain
            } else {
                h_ik * lp_minimize(l_k, domain) // min l_k(x), x ∈ domain
            };
        }
        c[i] = c_i;
    }
    c
}

fn reachable_set_step(
    x_k: &TemplatePolyhedron,
    pi: &[impl Polynomial],           // the n components of π
    unit_box_map: &impl UnitBoxMap,
) -> TemplatePolyhedron {
    let beta = unit_box_map.map(x_k);                       // UnitBoxMap
    let gamma: Vec<_> = pi.iter().map(|p| p.compose(&beta)).collect(); // γ = π ∘ β
    let bounds: Vec<_> = gamma.iter().map(|g| g.bound_functions()).collect(); // BoundFunctions
    let c_bar = poly_app(&bounds, &x_k.h, &unit_box(x_k.h.cols())); // PolyApp, Eq. 10
    TemplatePolyhedron { h: x_k.h.clone(), c: c_bar }        // X_{k+1} = ⟨H, c̄⟩
}
```

The type-level point worth dwelling on: `UnitBoxMap` as a trait object is a direct implementation-level echo of the paper's own remark that it "unifies two methods... in the same abstract algorithm" — the box-approximation route and the change-of-variables route are genuinely interchangeable behind that interface, and Theorem 1's correctness proof goes through *for either implementation*, because the proof only used the two properties any `UnitBoxMap` implementation must supply: $\pi(X_k) \subseteq \gamma(B)$ (Lemma 3's role) and validity of $\gamma$'s bound functions over $B$. That is a soundness argument stated *against an interface*, not a concrete implementation — precisely the shape a trusted-kernel-style soundness proof for an abstract interpreter needs to take if you want to swap analysis strategies without re-proving the whole pipeline.

---

## Where this leads

Algorithm 1 and Theorem 1 are the paper's central deliverable — everything in Chapters 2–5 (template polyhedra, the Bernstein expansion, bound-function construction, the two unit-box mappings) exists solely to make `UnitBoxMap`, `BoundFunctions`, and `PolyApp` computable and cheap. Downstream, Chapter 7's complexity and quadratic-convergence analysis (Lemma 5) is a direct statement about how tight `BoundFunctions`' output gets as the unit box shrinks — i.e., a quantitative version of the tightness/cost tradeoff this article's Lemma 4 discussion raised qualitatively — and Chapter 8's experiments are simply running this exact loop on concrete systems and measuring where the $2n$-LPs-per-step cost actually goes.

For the standing goals this vault tracks under **Static Analysis & Abstract Interpretation**: this algorithm *is* an abstract interpreter in miniature — a sound over-approximating transformer ($X_{k+1} = \pi^\sharp(X_k)$, with $\pi^\sharp$ built from `UnitBoxMap` + `BoundFunctions` + `PolyApp`) iterated over a fixed abstract domain (template polyhedra), with a correctness theorem assembled compositionally from per-stage soundness lemmas — exactly the proof architecture you'll want for the Hoare-contract / Horn-clause invariant generation pass in your own compiler's abstract-interpretation module. Under **SAT/SMT/CSP**: the reduction from polynomial optimization to $2n$ linear programs is a concrete, worked instance of "replace a hard combinatorial/nonlinear search with a tractable relaxation plus a soundness argument for the relaxation" — the same move your CSP kernel's domain/lattice propagation will need whenever a nonlinear constraint has to be soundly linearized before a solver can touch it.
