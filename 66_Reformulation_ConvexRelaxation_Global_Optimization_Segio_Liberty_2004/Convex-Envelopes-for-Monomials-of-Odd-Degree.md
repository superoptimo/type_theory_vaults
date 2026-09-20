---
title: "Convex Envelopes for Monomials of Odd Degree"
book: "Reformulation and Convex Relaxation Techniques for Global Optimization (Liberti, 2004)"
chapter: "Chapter 4, pp. 90-104"
tags: [optimization, convex-relaxation, global-optimization, spatial-branch-and-bound, real-analysis, galois-theory, numerical-methods]
---

# Convex Envelopes for Monomials of Odd Degree

[[book-guidelines|↩ Back to guidelines]]

## The gap this fills

Spatial Branch-and-Bound (sBB) solves nonconvex nonlinear programs to *global* optimality by
repeatedly replacing nonconvex terms with convex relaxations, solving the relaxed (easy) problem
for a valid lower bound, and shrinking the search boxes until that bound closes in on the true
optimum. The entire method lives or dies on one thing: how tight the relaxation is. A loose
relaxation gives a lower bound so far below the truth that sBB has to explore enormous swaths of
the search tree before it can rule anything out.

By 2004, tight convex underestimators already existed for the recurring nonconvex building
blocks — bilinear terms $xy$ (McCormick envelopes), fractional terms, and plain convex or concave
univariate functions (secant overestimation, tangent underestimation). But one very ordinary term
had no good answer: $x^n$ for odd $n$ — $x^3$, $x^5$, $x^7$, ... — on a range $[\ell, u]$ that
straddles zero. This shows up constantly (cubic and higher-order terms in chemical engineering
and process models, polynomial objective terms, anything with an odd power of a variable that can
be positive or negative). Liberti's Chapter 4 is the fix.

### Why odd degree and zero-straddling is genuinely hard

Consider $x^3$. For $x>0$ it's convex ($6x>0$); for $x<0$ it's concave ($6x<0$). A single power
term is therefore **neither convex nor concave** on any interval that contains the origin — it
inflects there. Every earlier technique the thesis surveys (chord underestimation, McCormick,
$\alpha$BB's diagonal shift) is built for a function with one fixed curvature sign across the
whole domain. None of them was designed for a term that flips curvature mid-interval, so applying
them naively — or reaching for the generic $\alpha$BB underestimator — throws away a large amount
of exploitable structure. The function is *piecewise* convex and concave, and a truly tight
envelope has to be piecewise too: follow the curve exactly where it's already convex (no relaxation
needed there at all), and only replace the concave part with something cheaper.

**What breaks without this:** if you don't build a piecewise envelope, your two choices are (a)
a single global secant line from endpoint to endpoint — hugely loose in the middle, where you throw
away all curvature information — or (b) $\alpha$BB's uniform "add a downward/upward-bending quadratic
until the second derivative is forced to a single sign everywhere" trick, which necessarily
overcorrects on the *already-convex* half of the domain to fix the concave half. Either way sBB
branches far more than it needs to.

## 4.1 The shape of the underestimator: tangent lines meeting the curve

Let $z = x^n$ with $n = 2k+1$ odd, $x \in [a,b]$, $a < 0 < b$ (Liberti writes the half-degree as
$k$; I'll keep that notation, since the source's own polynomial $Q^k$ is indexed by $k$ — this is
exactly the same object the guidelines call $Q_n$, with $n=2k+1$).

Picture the graph of $x^{2k+1}$ with $A = (a, a^{2k+1})$ on the concave-left branch and
$B = (b, b^{2k+1})$ on the convex-right branch. From $A$, draw the line tangent to the curve where
it *re-enters* the convex region — call the tangent point $C = (c, c^{2k+1})$. Symmetrically, from
$B$ draw the tangent to where the curve re-enters the concave region, at $D = (d, d^{2k+1})$.

The convex underestimator's shape now depends on where $c$ falls relative to $b$:

- **If $c < b$:** the underestimator is *the tangent line from $A$ to $C$, followed by the curve
  itself from $C$ to $b$.* On $[c,b]$ the function is already convex, so nothing beats the function
  itself; on $[a,c]$ the function is concave, and the tightest convex minorant of a concave arc that
  must also touch the curve at the endpoint $a$ is exactly its tangent line from that endpoint.
- **If $c \geq b$** (the tangent from $A$ doesn't re-touch the curve until past $b$): the whole
  interval is dominated by the concave branch, and the tightest convex underestimator collapses to
  the single **secant line through $A$ and $B$.**

The concave overestimator is the mirror image, built from $B$ and $D$. Note (Liberti flags this
explicitly) that the two "degenerate to a straight line" conditions — $c>b$ and $d<a$ — can never
both hold at once, so there's always a genuinely nonlinear region on at least one side.

## 4.2 Finding the tangent point: the polynomial $Q^k$

The tangent point $c$ is pinned down by a tangency condition: the slope of the secant $\overline{AC}$
must equal the derivative of $x^{2k+1}$ at $x=c$:

$$
\frac{c^{2k+1} - a^{2k+1}}{c - a} = (2k+1)c^{2k} \tag{4.1}
$$

Clearing denominators, $c$ is a root of

$$
P^k(x,a) \equiv (2k)x^{2k+1} - a(2k+1)x^{2k} + a^{2k+1} \tag{4.2}
$$

This still has the "extra" free parameter $a$ (the left endpoint) baked in — which would mean
re-solving a fresh $(2k+1)$-degree polynomial for every possible interval. Liberti eliminates that
dependence with a substitution: by induction on $k$,

$$
P^k(x,a) = a^{2k-1}(x-a)^2\, Q^k\!\left(\frac{x}{a}\right), \qquad
Q^k(x) \equiv 1 + \sum_{i=2}^{2k} i\, x^{i-1} \tag{4.3, 4.4}
$$

This is the crucial move: it factors out the *scale* ($a$) from the *shape*. $Q^k$ depends only on
$k$, not on the specific interval — solve it once per degree, and every tangent point for every
interval $[a,b]$ at that degree is just $c = r_k \cdot a$ (and, by the same construction,
$d = r_k \cdot b$) for the *same* root $r_k$. That's what makes a closed-form, reusable envelope
possible at all — without it, the sBB solver would need to numerically re-solve a degree-$(2k+1)$
polynomial at every single branching node.

### The obstruction: not solvable by radicals

$P^k(x,a)$ has one root at $x=a$ trivially (of no interest) plus the roots of $Q^k$. For low degree
this is easy: $Q^1(x) = 1+2x$ is linear, root $r_1 = -1/2$ exactly. $Q^2$ is cubic and solvable by
Cardano's formulas. But $Q^k$ has degree $2k-1$, and starting at $k=3$ (i.e. $n = 2k+1 = 7$) that
degree is $5$ — and **degree-5 polynomials are, in general, not solvable by radicals** (the
Abel–Ruffini theorem). Liberti gives the concrete witness: $Q^3(x) = 6x^5+5x^4+4x^3+3x^2+2x+1$ has
Galois group isomorphic to $S_5$, whose largest proper normal subgroup is $A_5$ — the smallest
non-solvable group. A polynomial's roots are expressible by radicals (nested $\sqrt[m]{\cdot}$
expressions built from the coefficients) if and only if its Galois group is a *solvable* group; $S_5$
is not, so there is provably no closed-form radical expression for $r_k$ once $k \geq 3$.

This is worth sitting with, because it's the whole reason the rest of the chapter has to work so
hard: you cannot write down $r_k$ as a formula. You have to prove, by other means, that it *exists*
and is *unique*, and then get it numerically.

## 4.3 Existence and uniqueness of $r_k$ — a self-contained analysis argument

The remarkable fact is that although $Q^k$'s roots resist an algebraic formula, its *existence and
uniqueness as a real root* is provable with nothing heavier than the intermediate value theorem
and induction. This is the load-bearing result of the chapter: without it, the envelope isn't
well-defined, because you wouldn't know the tangent point is unambiguous.

**Proposition 4.3.1.** For all $k \in \mathbb{N}$:
$$Q^k(0) = 1, \quad Q^k(-1) = -k \tag{4.5}$$
$$\forall x>0,\ \frac{dQ^k(x)}{dx} > 0 \tag{4.6}$$
$$\forall x \leq -1,\ Q^k(x) < 0 \tag{4.7}$$

The proof of (4.5) is direct substitution and a telescoping-sum computation. (4.6) follows because
$dQ^k/dx = \sum_{i=1}^{2k-1} i(i+1)x^{i-1}$ is a sum of positive terms for $x>0$. (4.7) rewrites
$Q^k(x) = \sum_{i=1}^{k} x^{2i-2}[2i(x+1)-1]$ for $x \neq 0$: each $x^{2i-2}$ is a positive even
power, and each bracket $2i(x+1)-1$ is negative whenever $x \leq -1$ (since $x+1 \leq 0$), so every
term of the sum is negative.

From these four facts plus continuity: (4.5) plus $Q^k(0)=1>0, Q^k(-1)=-k<0$ gives a sign change,
so **at least one root lies in $(-1,0)$**; (4.6) plus $Q^k(0)>0$ rules out any root for $x \geq 0$;
(4.7) rules out any root for $x \leq -1$. So far: at least one root, confined to $(-1,0)$.

**Lemma 4.3.2 (tightening the box).** All real roots of $Q^k$ lie in $\left[-1+\frac{1}{2k},
-\frac{1}{2}\right]$.

Proved by induction on $k$, using the recurrence $Q^k(x) = Q^{k-1}(x) + x^{2k-2}(2kx+2k-1)$ — each
step in $k$ only ever shrinks the interval a fixed root can occupy, because $x^{2k-2}\geq 0$ makes
the added term's sign track $x$ against the threshold $-1+\frac{1}{2k}$. The base case $k=1$ is
immediate since $Q^1$'s single root is exactly $-\tfrac12$.

**Theorem 4.3.3 (existence and uniqueness).** For all $k\in\mathbb{N}$, $Q^k(x)$ has *exactly one*
real root, lying in $\left[-1+\frac{1}{2k}, -\frac12\right]$.

This is where the two-polynomial trick pays off a second time. Rather than analyze $Q^k$'s
monotonicity directly (hard — it's not monotonic on all of $\mathbb{R}$), the proof goes back to
$P^k(x,1) = (x-1)^2 Q^k(x)$ (relation (4.3) with $a=1$). Since $(x-1)^2 > 0$ for $x<1$, $P^k(x,1)$
and $Q^k(x)$ share exactly the same roots below $x=1$ — so it suffices to show $P^k(x,1)$ has a
*unique* root in the interval Lemma 4.3.2 already pinned down. Now split
$P^k(x,1) = q_1^k(x) + q_2^k(x) + 1$ where $q_1^k(x)=2kx^{2k+1}$ and $q_2^k(x)=-(2k+1)x^{2k}$: $q_1^k$
is an *odd*-degree monomial with positive coefficient, hence monotonically increasing on $[-1,0]$;
$q_2^k$ is an *even*-degree monomial with *negative* coefficient, hence also monotonically
increasing on $[-1,0]$. A sum of two monotonically increasing functions is monotonically increasing
— so $P^k(x,1)$ is strictly increasing throughout $[-1+\tfrac{1}{2k},-\tfrac12]$, and a strictly
monotonic function can cross zero at most once. Combined with the existence argument above, $Q^k$
has exactly one real root $r_k$ in that interval, for every $k$.

The proof is elegant precisely because it never needs to *locate* $r_k$ — only to trap it in a
shrinking box and show the function can't wiggle back across zero inside that box. That's exactly
what makes $r_k$ safe to compute by bisection to arbitrary precision, even though no closed form
exists. The thesis tabulates $r_k$ for $k \leq 10$: $r_1=-0.5$ exactly, down to $r_{10}\approx
-0.8340533676$ — monotonically drifting toward $-1$ as $k$ grows (makes sense: higher powers have
sharper inflections, pushing the tangent point closer to the far end of the unit-scaled interval).

### Grounding: computing $r_k$ (Python) and checking the proof's bounding claims (Rust)

The existence/uniqueness proof licenses exactly one numerical method: bisection (or Newton, once
you know you're near a simple root) inside the box $[-1+\tfrac{1}{2k}, -\tfrac12]$.

```python
def Q(k: int, x: float) -> float:
    """Q^k(x) = 1 + sum_{i=2}^{2k} i * x**(i-1)"""
    return 1.0 + sum(i * x ** (i - 1) for i in range(2, 2 * k + 1))

def root_of_Q(k: int, tol: float = 1e-12) -> float:
    """Bisection inside the proven-unique-root box [-1+1/(2k), -1/2]."""
    lo, hi = -1.0 + 1.0 / (2 * k), -0.5
    assert Q(k, lo) < 0 < Q(k, hi) or Q(k, lo) > 0 > Q(k, hi)  # IVT sign change
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if (Q(k, lo) < 0) == (Q(k, mid) < 0):
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2

for k in range(1, 11):
    print(k, round(root_of_Q(k), 10))
# reproduces Table 4.1: k=1 -> -0.5, k=10 -> -0.8340533676, ...
```

Rust makes the "this is provably in a box, and monotone inside it" structure explicit as a typed
precondition rather than an assertion you hope holds:

```rust
/// Q^k(x) = 1 + sum_{i=2}^{2k} i * x^(i-1)
fn q(k: u32, x: f64) -> f64 {
    (2..=2 * k).map(|i| i as f64 * x.powi(i as i32 - 1)).sum::<f64>() + 1.0
}

/// The unique real root of Q^k, found by bisection inside the interval
/// that Proposition 4.3.1 + Lemma 4.3.2 prove contains exactly one root.
fn root_of_q(k: u32, tol: f64) -> f64 {
    let (mut lo, mut hi) = (-1.0 + 1.0 / (2.0 * k as f64), -0.5);
    let sign_lo = q(k, lo).is_sign_negative();
    while hi - lo > tol {
        let mid = (lo + hi) / 2.0;
        if q(k, mid).is_sign_negative() == sign_lo { lo = mid } else { hi = mid }
    }
    (lo + hi) / 2.0
}
```

And in Lean, the theorem is worth stating even without reproducing the full proof — it's a clean
target for anyone building a real-analysis proof library, since it's a textbook IVT-plus-monotonicity
argument:

```lean
-- Q^k as a real polynomial function; existence+uniqueness of its negative root.
def Qk (k : ℕ) (x : ℝ) : ℝ := 1 + ∑ i ∈ Finset.Icc 2 (2 * k), (i : ℝ) * x ^ (i - 1)

theorem Qk_unique_root (k : ℕ) (hk : 1 ≤ k) :
    ∃! r : ℝ, r ∈ Set.Icc (-1 + 1 / (2 * k : ℝ)) (-1 / 2) ∧ Qk k r = 0 := by
  sorry -- IVT gives existence; P^k(x,1) = (x-1)^2 * Qk k x plus monotonicity of
        -- q1 + q2 on the box gives uniqueness, exactly as in Theorem 4.3.3
```

## 4.4 The closed-form nonlinear envelope

Write $r_k$ for the unique root just established, so the tangent points are simply $c = r_k a$ and
$d = r_k b$. The lower and upper tangent lines are:

$$
a^{2k+1} + \frac{c^{2k+1}-a^{2k+1}}{c-a}(x-a) \qquad\text{(4.10, lower tangent)}
$$
$$
b^{2k+1} + \frac{d^{2k+1}-b^{2k+1}}{d-b}(x-b) \qquad\text{(4.11, upper tangent)}
$$

Introducing the constant $R_k \equiv \dfrac{r_k^{2k+1}-1}{r_k-1}$ (the slope factor baked out of
$c=r_ka$), the full piecewise envelope $l_k(x) \leq x^{2k+1} \leq u_k(x)$ is:

$$
l_k(x) = \begin{cases} a^{2k+1}\left(1+R_k\left(\frac{x}{a}-1\right)\right) & x < c \\ x^{2k+1} & x \geq c \end{cases} \quad\text{if } c<b,\qquad\text{else}\quad l_k(x)=a^{2k+1}+\frac{b^{2k+1}-a^{2k+1}}{b-a}(x-a)
$$
$$
u_k(x) = \begin{cases} x^{2k+1} & x \leq d \\ b^{2k+1}\left(1+R_k\left(\frac{x}{b}-1\right)\right) & x > d \end{cases} \quad\text{if } d>a,\qquad\text{else}\quad u_k(x)=a^{2k+1}+\frac{b^{2k+1}-a^{2k+1}}{b-a}(x-a)
$$

By construction these are continuous *and differentiable* everywhere — the tangency condition (4.1)
is exactly what forces the line to meet the curve with matching slope, so there's no kink at $c$ or
$d$.

**Theorem 4.4.1: these are the tightest possible.** The proof is short and worth internalizing
because it's a proof pattern that recurs constantly in convex analysis — "no tighter envelope
exists" arguments almost always split into "on the already-convex piece, the function *is* its own
tightest lower bound" plus "a local convexity check near the join point." Concretely: on $[c,b]$ the
underestimator *is* the curve, and nothing beats the function underestimating itself. On $[a,c]$ the
underestimator is a straight line through two points that both lie *on* the original curve — any
function agreeing with $x^{2k+1}$ at both endpoints while staying below it everywhere in between
can't beat a straight line there (concavity of the arc guarantees the chord is the pointwise
infimum of all such curves). The only nontrivial step is checking convexity is preserved in a
neighborhood straddling $c$ itself: take a small window $(c-\varepsilon, c+\varepsilon)$; the chord
on $(c, c+\varepsilon)$ lies above $l_k$ because $x^{2k+1}$ is convex there; extending the chord
back to $(c-\varepsilon, c+\varepsilon)$ only *decreases* its slope (because the new left endpoint
sits exactly on the tangent line, by construction of $c$), while the right endpoint is unchanged —
so the extended chord still lies above $l_k$ everywhere. Since $\varepsilon$ was arbitrary, $l_k$ is
convex in a full neighborhood of $c$, hence globally.

## 4.5 Linearizing the envelope for the sBB inner loop

sBB solves a fresh convex NLP at *every node* of its search tree. A nonlinear envelope is exact but
expensive to re-optimize repeatedly; a linear relaxation trades a little tightness for a much cheaper
LP (or, embedded in a larger problem, cheaper constraint set) at each node.

The straightforward linearization just drops the "follow the curve" segments and keeps only the two
tangent lines as bounds for the *entire* interval:

$$
a^{2k+1}\Big(1+R_k\big(\tfrac{x}{a}-1\big)\Big) \;\leq\; z \;\leq\; b^{2k+1}\Big(1+R_k\big(\tfrac{x}{b}-1\big)\Big) \tag{4.17}
$$

This can be tightened further by *also* adding the tangents to the curve at the endpoints $A,B$
themselves:

$$
(2k+1)b^{2k}x - 2kb^{2k+1} \;\leq\; z \;\leq\; (2k+1)a^{2k}x - 2ka^{2k+1} \tag{4.18}
$$

— i.e. the linear relaxation is the *intersection* of both pairs of half-planes, a small 4-constraint
polytope hugging the nonlinear envelope from outside. (When $c>b$ or $d<a$, the corresponding side
collapses to the single secant through $A$ and $B$, exactly as in Section 4.1 — Table 4.2 in the
source tabulates all three cases explicitly.)

## 4.6 How this compares to the alternatives available in 2004

### Bilinear-product reformulation

The obvious workaround, absent a dedicated envelope, is to reformulate exactly: introduce
$w = x^{2k}$ (a convex, even-degree, always-solvable-envelope term) and write $z = wx$ — a *bilinear*
product, for which McCormick envelopes are standard. Substituting McCormick's linear envelope for
$wx$ and the function/secant envelope for $w=x^{2k}$, then eliminating $w$ algebraically, yields a
genuine convex relaxation (equations 4.19–4.21 in the source). Figure 4.4 in the thesis compares
this against both the new nonlinear envelope and the new linear relaxation for $x^3$: the bilinear
reformulation has the *same qualitative shape* (line joined to curve) but is measurably looser
everywhere except two small sub-intervals near the tangent-intersection points — consistent with
Theorem 4.4.1's tightness claim, since this reformulation is *a* valid convex relaxation but not the
tightest one.

### $\alpha$BB-style underestimation

The generic $\alpha$BB technique underestimates any nonconvex term $f(x)$ by
$f(x) + \alpha(x-a)(x-b)$, choosing $\alpha$ large enough to force the second derivative
non-negative *across the whole interval*. For $x^{2k+1}$ this forces
$$
\alpha_k = k(2k+1)|a|^{2k-1}, \qquad \beta_k = k(2k+1)b^{2k-1} \tag{4.22, 4.23}
$$
Because $\alpha_k$ has to dominate the curvature at the *most concave* point in the whole interval
(not just locally), it massively overcorrects on the half of the domain that was already convex —
Figure 4.5 shows the resulting envelope for $x^3$ is visibly far looser than either the nonlinear
envelope or the tight linear relaxation. This is the clearest illustration of the chapter's core
insight: a *piecewise* technique that only spends "slack" where it's actually needed beats a
*uniform* technique that has to satisfy a worst-case condition everywhere.

### Computational payoff

Section 4.7 solves $\min_{x,y} x-y$ subject to $y=x^{2k+1}$, $-1\leq x,y\leq 1$ via sBB, comparing
the tight linear relaxation against the bilinear-product relaxation for $k=1,\dots,14$. The novel
relaxation needs consistently fewer branch-and-bound iterations (e.g. 7 vs. 25 for $k=10$) — because
its minimum over the relaxed feasible region sits much closer to the true minimum of the original
problem, so fewer branching splits are needed before the bound closes the gap. Geometrically
(Figures 4.6–4.7 in the source), the bilinear relaxation's optimum sits visibly farther from the
true curve than the tight relaxation's optimum, in the direction the objective is being minimized.

## Verifying tightness numerically

Because $Q^k$'s root only has a numerical value, "is this envelope actually tight and does it stay
above/below the curve everywhere" is itself worth checking computationally rather than trusting the
algebra alone — exactly the kind of sanity check a rigorous engineer builds once and reuses.

```python
import numpy as np

def envelope_bounds(k, a, b, r_k, xs):
    c, d = r_k * a, r_k * b
    R_k = (r_k**(2*k+1) - 1) / (r_k - 1)
    lo = np.where(xs < c, a**(2*k+1)*(1 + R_k*(xs/a - 1)), xs**(2*k+1))
    hi = np.where(xs > d, b**(2*k+1)*(1 + R_k*(xs/b - 1)), xs**(2*k+1))
    return lo, hi

k, a, b = 1, -1.0, 1.0
r_k = root_of_Q(k)          # -0.5 for k=1
xs = np.linspace(a, b, 2001)
lo, hi = envelope_bounds(k, a, b, r_k, xs)
assert np.all(lo <= xs**(2*k+1) + 1e-9) and np.all(xs**(2*k+1) <= hi + 1e-9)
```

## Where this leads

This chapter is the thesis's second novel contribution, standing on equal footing with Chapter 3's
reduction constraints, and both are folded into the $\mathcal{OS}$ software framework of Chapter 5:
Smith's sBB algorithm needs a convexification rule for *every* nonconvex term type it encounters
during standardization, and this envelope becomes the rule for odd-power univariate terms —
plugged into the same `convexifiermanager` machinery that dispatches McCormick envelopes for
bilinear terms. The chapter's real intellectual payload, though, is the proof method itself:
faced with a polynomial that provably has no closed-form root (Galois obstruction), the thesis
doesn't give up on rigor — it substitutes an *existence-and-uniqueness* argument (bounding boxes,
monotonicity, IVT) that is just as rigorous as an exact formula and *fully constructive* for
numerics (bisection converges inside a box you've proven contains exactly one root).

That pattern — replace "solve exactly" with "prove a unique fixed point exists in a bounded region,
then compute it iteratively" — is precisely the shape of bound/interval propagation in numerical
constraint programming and abstract interpretation: a CSP kernel doing domain propagation over a
non-linear polynomial constraint is, in effect, repeatedly tightening a box that's guaranteed (by an
argument of exactly this flavor) to still contain every solution. The tight envelope from this
chapter is a closed-form instance of exactly the sound-over-approximation move that a numeric
abstract domain needs when it hits a non-linear equation it can't solve exactly but must still
bound safely — the same tension between "no analytic solution" and "still need a certified enclosure"
that this chapter resolves for $x^{2k+1}$.
