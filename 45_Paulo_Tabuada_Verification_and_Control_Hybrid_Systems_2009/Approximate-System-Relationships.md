---
title: Approximate System Relationships
source: "Verification and Control of Hybrid Systems: A Symbolic Approach — Paulo Tabuada (2009)"
chapter: "Chapter 9: Approximate System Relationships"
pages: "145–149"
tags: [hybrid-systems, metric-systems, approximate-simulation, approximate-bisimulation, alternating-simulation, abstract-interpretation, formal-verification]
---

[[book-guidelines|↩ Back to guidelines]]

# Approximate System Relationships

## Why exactness had to break

[[Exact-System-Relationships|Chapter 4]] built a whole vocabulary — simulation, bisimulation, alternating simulation — on one non-negotiable clause: related states must produce the *same* output, $H_a(x_a) = H_b(x_b)$, no exceptions. [[Order-Minimal-Structures-and-Definability|Chapter 7]] then went to considerable lengths to make that clause achievable for infinite-state dynamical systems — order-minimal structures, definability, eigenvalue conditions restricting you to real or diagonalizable-imaginary spectra, strict feed-forward forms. All of that machinery exists because "same output, exactly" is a demanding thing to ask of a quotient built from a continuous state space, and most dynamical systems simply don't satisfy the conditions (recall the spiraling counterexample with eigenvalues $0.1 \pm i$ from Chapter 7 — the finite bisimilar quotient provably fails to exist).

So the honest question is: for the overwhelming majority of systems that fall outside the exact machinery's reach, what's the *right* way to give up equality? Chapter 9's opening notation section — before it even states a definition — tells you the answer by telling you what it's *not*: it's not "outputs match with high probability," and it's not "outputs match on average." It's a **metric**. Here's why that's the specifically correct relaxation, not just *a* plausible one.

A probabilistic relaxation would say "the two systems agree with probability $1-\delta$." That's the right tool when the mismatch is a qualitatively different *event* — a coin flip, a tie-breaking rule, a random disturbance realization — where "agree" and "disagree" are binary and you're averaging over runs. But the book is explicit about where its mismatch comes from: "noise in measurements, imprecisions in actuators, and numerical computation errors." These are not binary events. A sensor reading off by $0.003$ isn't "wrong" in the way a coin flip is wrong — it's *close*. The right question isn't "how often do they disagree" but "how far apart are they when they disagree," and answering *that* question requires a notion of distance on the output set, not a probability measure over an event space. That's precisely what a metric gives you, and nothing weaker does the job: you cannot even phrase "off by $\varepsilon$" without first having a $d(\cdot,\cdot)$ to measure "off" with.

**What breaks without a metric.** If you tried to relax exact simulation using only the pre-order/topological structure already on $Y$ (no numeric distance), you could at best say "these two outputs are in the same open set" — but then there is no way to state *how much* error accumulates when you compose two such relaxed relations, which is exactly the load-bearing fact this chapter needs (see below). A metric gives you a real number to add.

## 1. Metric systems and $\varepsilon$-inflation

The chapter's "Notation" section states the two prerequisite definitions before touching systems at all.

**Metric.** A function $d: Z \times Z \to \mathbb{R}_0^+$ is a metric if:
- $d(z,z') = 0 \iff z = z'$ (separates points),
- $d(z,z') + d(z',z'') \ge d(z,z'')$ (triangle inequality),
- $d(z,z') = d(z',z)$ (symmetry).

**Distance to a set.** $d(z, W) = \min_{w \in W} d(z,w)$ for $W \subseteq Z$.

**$\varepsilon$-inflation.** $W^\varepsilon = \{z \in Z \mid d(z,W) \le \varepsilon\}$ — every point within $\varepsilon$ of *some* point of $W$. Note $W \subseteq W^\varepsilon$ (every $w \in W$ has $d(w,W)=0 \le \varepsilon$), with equality only at $\varepsilon = 0$.

Think of $\varepsilon$-inflation as the metric-space analogue of rounding a set outward — it's the set you'd get by drawing a ball of radius $\varepsilon$ around every point of $W$ and taking the union. This single operator is what lets Chapter 9 restate "approximately inside" as an ordinary set-containment statement (below, $\mathrm{Reach}^\varepsilon(S_b)$), which is why it's worth having a name for before the real definitions start.

**Definition 9.1 (Metric system).** A system $S$ is a *metric system* if its output set $Y$ carries a metric $d: Y \times Y \to \mathbb{R}_0^+$. When comparing two metric systems $S_a, S_b$ with $Y_a = Y_b$, the shared output set is understood to carry a shared metric.

```rust
// A metric system, in the vocabulary of the exact-relationships article:
// same six-tuple, plus a distance function on outputs instead of bare equality.
trait MetricSystem {
    type State;
    type Input;
    type Output: Clone;

    fn initial(&self) -> Vec<Self::State>;
    fn output(&self, x: &Self::State) -> Self::Output;
    fn post(&self, x: &Self::State, u: &Self::Input) -> Vec<Self::State>;

    // The one thing Definition 4.7's world didn't have: a metric on outputs.
    fn dist(&self, y1: &Self::Output, y2: &Self::Output) -> f64;
}
```

## 2. $\varepsilon$-approximate simulation: relaxing exactly one clause

**Definition 9.2 ($\varepsilon$-approximate simulation relation).** Let $S_a, S_b$ be metric systems with $Y_a = Y_b$, $\varepsilon \in \mathbb{R}_0^+$. $R \subseteq X_a \times X_b$ is an $\varepsilon$-approximate simulation relation from $S_a$ to $S_b$ if:

1. for every $x_{a0} \in X_{a0}$, there exists $x_{b0} \in X_{b0}$ with $(x_{a0}, x_{b0}) \in R$;
2. for every $(x_a, x_b) \in R$: $d(H_a(x_a), H_b(x_b)) \le \varepsilon$;
3. for every $(x_a, x_b) \in R$: $x_a \xrightarrow{u_a} x_a'$ in $S_a$ implies there exists $x_b \xrightarrow{u_b} x_b'$ in $S_b$ with $(x_a', x_b') \in R$.

Compare directly against [[Exact-System-Relationships#Tier 2: Similarity relationships — simulation and bisimulation|Definition 4.7]]: conditions 1 and 3 are copied verbatim. Only condition 2 changes, from $H_a(x_a) = H_b(x_b)$ to $d(H_a(x_a), H_b(x_b)) \le \varepsilon$. This is the whole idea of the chapter in one substitution — everything about *how* transitions get shadowed is untouched; only the acceptance criterion on outputs loosens from "identical" to "within tolerance."

$S_a \preceq_S^\varepsilon S_b$ ("$S_b$ $\varepsilon$-approximately simulates $S_a$") iff such an $R$ exists.

**At $\varepsilon = 0$ this is exactly Definition 4.7 again**, because $d(y,y') \le 0$ and $d$ being a metric ($d(y,y')=0 \iff y=y'$) together force $y = y'$. So $\preceq_S^0$ and $\preceq_S$ are literally the same relation — approximate simulation is a strict generalization, not a rebranding. This directly answers the guidelines' first Key Question: the collapse at $\varepsilon=0$ is a sanity check that the generalization is conservative, and every proposition proved for $\preceq_S^\varepsilon$ specializes correctly to the exact case.

### Worked example: the book's own decaying scalar system

The book illustrates Definition 9.2 with a system that simulates *itself* at a nonzero precision — worth walking through because it's the cleanest possible instance.

Take $\Sigma: \dot\xi = -\xi$, $\xi(t) \in \mathbb{R}$, with closed-form solution $\xi_x(t) = e^{-t}x$. Let $S(\Sigma) = (\mathbb{R}, \mathbb{R}_0^+, \to)$ where $x \xrightarrow{\tau} x'$ iff $\xi_x(\tau) = x'$ (time itself is the input, as in Chapter 7's dynamical-systems-as-systems construction). Claim: for any $\varepsilon \ge 0$, $R_\varepsilon = \{(x,x') \mid \|x - x'\| \le \varepsilon\}$ is an $\varepsilon$-approximate simulation relation from $S(\Sigma)$ to itself.

Proof sketch: take $(x,x') \in R_\varepsilon$ and a transition $x \xrightarrow{\tau} x''$, so $x'' = \xi_x(\tau) = e^{-\tau}x$. Respond with $x' \xrightarrow{\tau} x'''$ where $x''' = \xi_{x'}(\tau) = e^{-\tau}x'$. Then
$$\|x'' - x'''\| = \|e^{-\tau}x - e^{-\tau}x'\| = e^{-\tau}\|x-x'\| \le \|x-x'\| \le \varepsilon,$$
using $e^{-\tau} \le 1$ for $\tau \ge 0$. So $(x'',x''') \in R_\varepsilon$ — the relation is preserved forever, because the dynamics is *contracting* ($e^{-\tau}$ shrinks the gap, never grows it). The book flags this argument as "valid in far greater generality" and "at the heart of all the results in Part IV" — it is literally the germ of the Lyapunov-function argument that [[Approximate System Relationships#Where this leads|Chapters 10–11]] generalize into a full construction technique.

```python
# A direct check of the claim above for a couple of concrete points.
import math

def xi(x, tau):
    return math.exp(-tau) * x

def check_eps_simulation(x, xprime, eps, tau):
    xpp = xi(x, tau)
    xppp = xi(xprime, tau)
    gap_before = abs(x - xprime)
    gap_after = abs(xpp - xppp)
    assert gap_before <= eps + 1e-12
    assert gap_after <= eps + 1e-12   # relation still holds after the step
    return gap_after

# gap never grows because e^{-tau} <= 1
print(check_eps_simulation(1.0, 1.2, eps=0.3, tau=2.0))  # gap shrinks well within eps
```

### Proposition 9.4: approximate reachable-set containment

This is the payoff proposition — the reason you'd want $\varepsilon$-approximate simulation at all.

**Proposition 9.4.** For metric systems $S_a, S_b$ with $Y_a = Y_b$: $S_a \preceq_S^\varepsilon S_b \implies \mathrm{Reach}(S_a) \subseteq \mathrm{Reach}^\varepsilon(S_b)$.

*Proof idea.* Given $y_a \in \mathrm{Reach}(S_a)$, there's a finite initialized internal behavior of $S_a$ reaching some $x_{ak}$ with $H_a(x_{ak}) = y_a$. Exactly as in the proof of [[Exact-System-Relationships#Tier 2: Similarity relationships — simulation and bisimulation|Proposition 4.11]], the relation $R$ lets you build a matching behavior of $S_b$ step by step, landing at $x_{bk}$ with $(x_{ak}, x_{bk}) \in R$. Condition 2 then gives $d(y_a, y_b) \le \varepsilon$ where $y_b = H_b(x_{bk}) \in \mathrm{Reach}(S_b)$ — so $y_a$ is within $\varepsilon$ of a point actually reachable in $S_b$, i.e. $y_a \in \mathrm{Reach}(S_b)^\varepsilon$.

This is the exact metric-relaxed analogue of [[Exact-System-Relationships#Tier 1: Behavioral inclusion and equivalence|Proposition 4.6]]'s $\mathrm{Reach}(S_a) \subseteq \mathrm{Reach}(S_b)$: safety verification on the abstraction $S_b$ now gives a *sufficient*, not exact, condition on $S_a$ — but the sufficiency survives the relaxation intact. Concretely: if $B$ is an unsafe output set and $\mathrm{Reach}^\varepsilon(S_b) \cap B = \emptyset$, then $\mathrm{Reach}(S_a) \cap B = \emptyset$ too. You get to certify safety of the (possibly intractable, infinite-state) $S_a$ by checking the $\varepsilon$-inflated reachable set of the (tractable, e.g. finite-state) $S_b$ instead — provided you built $S_b$ so that its reachable set is computable and its inflation still misses $B$. This is precisely what Chapters 10–11 exist to deliver: a *recipe* for constructing such an $S_b$, with a guaranteed $\varepsilon$.

## 3. $\varepsilon$-approximate bisimulation

**Definition 9.5.** $S_a \cong_S^\varepsilon S_b$ if there exists $R$ such that $R$ is an $\varepsilon$-approximate simulation relation from $S_a$ to $S_b$ *and* $R^{-1}$ is an $\varepsilon$-approximate simulation relation from $S_b$ to $S_a$.

Same symmetrization move as [[Exact-System-Relationships#Tier 2: Similarity relationships — simulation and bisimulation|Definition 4.12]]/4.13 for the exact case — bisimulation is "simulation in both directions with the same witnessing relation." Note that the *same* $\varepsilon$ bounds the mismatch in both directions; the definition does not offer a two-parameter $(\varepsilon_1,\varepsilon_2)$ version, though the composition result below shows you effectively get one anyway once you start chaining relations.

## 4. Precision accumulates under composition — and why it must be addition

This is the chapter's most consequential single sentence, easy to walk past:

> "if $_aR_b$ is an $\varepsilon_{ab}$-approximate (bi)simulation relation from $S_a$ to $S_b$ and $_bR_c$ is an $\varepsilon_{bc}$-approximate (bi)simulation relation from $S_b$ to $S_c$, the composite $_bR_c \circ {_aR_b}$ is an $(\varepsilon_{ab} + \varepsilon_{bc})$-approximate (bi)simulation relation from $S_a$ to $S_c$."

**Why it has to be addition, not multiplication or a constant.** Walk through what condition 2 actually requires for the composite relation. Take $(x_a, x_c) \in {_bR_c} \circ {_aR_b}$, meaning there's a witness $x_b$ with $(x_a,x_b) \in {_aR_b}$ and $(x_b,x_c) \in {_bR_c}$. You know $d(H_a(x_a), H_b(x_b)) \le \varepsilon_{ab}$ and $d(H_b(x_b), H_c(x_c)) \le \varepsilon_{bc}$ (using $Y_a = Y_b = Y_c$ so all three outputs live in the same metric space). The only tool available to bound $d(H_a(x_a), H_c(x_c))$ is the **triangle inequality** baked into the definition of a metric:
$$d(H_a(x_a), H_c(x_c)) \le d(H_a(x_a), H_b(x_b)) + d(H_b(x_b), H_c(x_c)) \le \varepsilon_{ab} + \varepsilon_{bc}.$$
There is no tighter general bound available — the triangle inequality is an inequality, not an equality, so this is the best guarantee that holds for *every* metric and *every* pair of witnesses, and it's exactly additive because the triangle inequality is exactly additive. A multiplicative bound ($\varepsilon_{ab}\cdot\varepsilon_{bc}$) would be *unsound* — it would understate the worst case whenever both $\varepsilon$'s exceed 1, and a constant bound (ignoring one of the two $\varepsilon$'s) would be unsound whenever that ignored term is the larger contributor. Addition is not a design choice; it's the tightest bound the metric axioms actually license.

**The practical consequence: abstraction layers are a depleting resource.** If you build a chain of $n$ abstractions $S_a \preceq_S^{\varepsilon_1} S_1 \preceq_S^{\varepsilon_2} S_2 \preceq_S^{\varepsilon_3} \cdots \preceq_S^{\varepsilon_n} S_n$, the end-to-end guarantee you actually get is $S_a \preceq_S^{\varepsilon_1+\cdots+\varepsilon_n} S_n$ — precision degrades *linearly* in the number of layers stacked, with no floor below which composing more layers is free. This is a hard boundary on the abstract-refine-abstract-refine architecture the whole book is built around: you cannot stack an unbounded number of approximate abstraction layers and expect the total error to stay useful. If your safety margin is $\delta$ (distance from $\mathrm{Reach}(S_a)$'s true footprint to the unsafe set $B$), you need $\sum_i \varepsilon_i < \delta$ — a budget shared across every layer in the pipeline, which is exactly why Chapters 10–11 care so much about being able to make each individual $\varepsilon_i$ as small as needed (via finer time/space quantization) rather than accepting whatever precision a fixed construction happens to produce.

```python
# Demonstrating precision accumulation over three composed epsilon-approximate
# simulation relations on toy metric systems (R with the standard metric).

def compose_precisions(*epsilons):
    """The book's composition rule: precisions of a chain of
    epsilon-approximate (bi)simulations simply add."""
    return sum(epsilons)

class ToyMetricSystem:
    """States and outputs coincide (R, standard metric |x - y|)."""
    def __init__(self, step):
        self.step = step  # deterministic dynamics x -> step(x)

    def dist(self, y1, y2):
        return abs(y1 - y2)


def eps_simulates(sys_a, sys_b, x_a, x_b, eps, steps, u_seq):
    """Check condition 2 holds along a run, and that condition 3's chosen
    successor keeps the pair within eps at every step (a direct trace check,
    not a search for the relation itself)."""
    for _ in range(steps):
        if sys_a.dist(x_a, x_b) > eps:
            return False
        x_a = sys_a.step(x_a)
        x_b = sys_b.step(x_b)
    return sys_a.dist(x_a, x_b) <= eps


# Three systems related pairwise by 0.05, 0.03, 0.02-approximate simulations.
sys1 = ToyMetricSystem(step=lambda x: 0.9 * x)   # slightly contracting
sys2 = ToyMetricSystem(step=lambda x: 0.9 * x + 0.01)
sys3 = ToyMetricSystem(step=lambda x: 0.9 * x + 0.015)

eps_12, eps_23 = 0.05, 0.03
composed_eps = compose_precisions(eps_12, eps_23)   # 0.08, NOT 0.05*0.03 or max(...)
print("End-to-end precision after composing two layers:", composed_eps)

# A third layer degrades the guarantee further, additively:
eps_34 = 0.02
total_after_three_layers = compose_precisions(eps_12, eps_23, eps_34)
print("After three layers:", total_after_three_layers)
```

Running this prints `0.08` then `0.1` — each additional abstraction layer costs you its own $\varepsilon$ on top of everything already spent, never less.

## 5. $\varepsilon$-approximate alternating relations

Section 9.2 performs the same single-clause substitution on the *alternating* relations from [[Exact-System-Relationships#Tier 3: Alternating similarity — when "input" becomes "choice"|Definition 4.19]] — needed once inputs are read as controllable/adversarial choices rather than passive labels, i.e. once you're doing control instead of pure verification.

**Definition 9.6 ($\varepsilon$-approximate alternating simulation relation).** $R \subseteq X_a \times X_b$, with $\varepsilon \in \mathbb{R}_0^+$:

1. for every $x_{a0} \in X_{a0}$, there exists $x_{b0} \in X_{b0}$ with $(x_{a0},x_{b0}) \in R$;
2. for every $(x_a,x_b) \in R$: $d(H_a(x_a), H_b(x_b)) \le \varepsilon$;
3. for every $(x_a,x_b) \in R$ and every $u_a \in U_a(x_a)$, there exists $u_b \in U_b(x_b)$ such that for every $x_b' \in \mathrm{Post}_{u_b}(x_b)$ there exists $x_a' \in \mathrm{Post}_{u_a}(x_a)$ with $(x_a',x_b') \in R$.

Exactly Definition 4.19's $\forall u_a\,\exists u_b\,\forall x_b'\,\exists x_a'$ quantifier alternation, condition 2 relaxed to a distance bound — the same substitution as the non-alternating case, applied one level up. $S_a \preceq_{AS}^\varepsilon S_b$ iff such an $R$ exists.

**Definition 9.7 (Extended $\varepsilon$-approximate alternating simulation relation).** $R^e \subseteq X_a \times X_b \times U_a \times U_b$: quadruples $(x_a,x_b,u_a,u_b)$ with $(x_a,x_b) \in R$, $u_a \in U_a(x_a)$, and $u_b$ a valid response per condition 3. As in the exact case (Definition 4.22), this packages the existential witness from condition 3 as inspectable *data* rather than leaving it as an existence claim — the concrete thing a controller-synthesis algorithm iterates over. The book notes this is used specifically in [[Approximate System Relationships#Where this leads|Chapter 11]] to define *approximate feedback composition*.

**Definition 9.8 ($\varepsilon$-approximate alternating bisimulation).** $S_a \cong_{AS}^\varepsilon S_b$ if $R$ and $R^{-1}$ are both $\varepsilon$-approximate alternating simulation relations. The strongest relation in the chapter, mirroring Definition 4.24's role for the exact case: it's what licenses two-way controller transport (design on either system, refine to the other) at bounded precision cost, rather than only the one-way abstract-then-refine guarantee that plain approximate alternating simulation gives.

The precision-accumulation rule of §4 above applies unchanged to these alternating relations too — the book states it for "(bi)simulation" generically, and the same triangle-inequality argument goes through verbatim since condition 2 is identical in both the plain and alternating definitions.

## Synthesis: where this chapter sits, and where this leads

Chapter 9 is short — five definitions and one proposition, no algorithm, no construction of a concrete abstraction — because its job is purely to *relax the vocabulary*, exactly as Chapter 4 built vocabulary with no algorithm attached. Every relation here is the metric-$\varepsilon$ version of its Chapter 4 counterpart, collapsing to it exactly at $\varepsilon = 0$:

| Exact (Ch. 4) | Approximate (Ch. 9) |
|---|---|
| simulation $\preceq_S$ | $\varepsilon$-approximate simulation $\preceq_S^\varepsilon$ |
| bisimulation $\cong_S$ | $\varepsilon$-approximate bisimulation $\cong_S^\varepsilon$ |
| alternating simulation $\preceq_{AS}$ | $\varepsilon$-approximate alternating simulation $\preceq_{AS}^\varepsilon$ |
| extended alt. simulation $R^e$ | extended $\varepsilon$-approx. alt. simulation $R^e$ (Def. 9.7) |
| alternating bisimulation $\cong_{AS}$ | $\varepsilon$-approximate alternating bisimulation $\cong_{AS}^\varepsilon$ |

What the chapter does *not* yet give you is any way to construct an $S_b$ that stands in one of these relations to a given $S_a$, with a chosen $\varepsilon$, other than the self-simulation toy example. That is exactly the gap [[Approximate System Relationships#4. Precision accumulates under composition — and why it must be addition|Chapters 10 and 11]] fill: Chapter 10 builds time-and-space-quantized finite(-ish) systems that are provably $\varepsilon$-approximately bisimilar to affine (and, via incremental stability, nonlinear) dynamical systems, and Chapter 11 extends this to control and switched systems. The mechanism in both is Lyapunov-function-based — a direct scale-up of the contraction argument in the worked example above ($e^{-\tau}\|x-x'\| \le \|x-x'\|$), generalized from "linear decay under $\dot\xi=-\xi$" to "decay bounded by a Lyapunov function's rate condition." In that precise sense, Chapter 9 is the metric relaxation of Chapter 4's exact relations, and Part IV as a whole is the (much longer) answer to the question Chapter 9 only poses: given a real, non-definable, no-exact-quotient dynamical system, how small an $\varepsilon$ can you actually guarantee, and at what quantization cost?

### Connections to the compiler/elaborator project (Focus Area: `static-analysis`)

This chapter's abstraction pattern is the *quantitative* refinement of the Galois-connection reading already given for [[Exact-System-Relationships#Connections to the compiler/elaborator project (Focus Area: static-analysis)|Chapter 4's quotient construction]]. There, soundness was binary — the abstract system either over-approximates exactly or it doesn't. Here, soundness comes with a *numeric* error bound that composes additively through a chain of abstraction passes, which is the same shape as error accumulation in a numerically-tolerant abstract interpreter (e.g. interval or affine-arithmetic domains tracking rounding error): each abstract-domain operation you compose contributes its own worst-case error, and the end-to-end soundness certificate is the *sum*, never a magically-bounded constant. If your invariant-generation pipeline ever needs to reason about floating-point or otherwise inexact program semantics rather than exact symbolic values, Proposition 9.4's pattern — "safety on the inflated abstract reachable set implies safety on the concrete one" — is precisely the soundness argument you'd reach for, and the additive composition rule here is the reason such a pipeline can't have unboundedly many abstraction stages without an explicit error budget.

**[[Exact-Symbolic-Models-for-Control#Where this leads|Where this leads]]:** Chapters 10 and 11 ([[Approximate-Symbolic-Models-for-Verification-and-Control|Approximate Symbolic Models for Verification and Control]], pp. 151–189) exist to construct — not merely define — systems standing in the $\varepsilon$-approximate (bi)simulation and alternating-(bi)simulation relations of this chapter, using [[Approximate System Relationships#Where this leads|stability theory]] and Lyapunov functions (Chapter 10 first, in pp. 191–193's companion machinery) in place of Chapter 7's order-minimality and eigenvalue conditions — the two tracks (exact/definable vs. approximate/stable) cover, between them, essentially every dynamical system the book's symbolic-model program can reach.
