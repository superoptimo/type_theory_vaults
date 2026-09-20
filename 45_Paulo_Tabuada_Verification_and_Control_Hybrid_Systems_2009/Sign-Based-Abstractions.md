---
title: "Sign-Based Abstractions"
source: "Verification and Control of Hybrid Systems: A Symbolic Approach (Tabuada, 2009)"
chapter: "Chapter 7, §7.4 (pp. 94–103)"
tags: [hybrid-systems, dynamical-systems, static-analysis, abstract-interpretation, reachability, sign-domain, lie-derivative, safety-verification]
---

[[book-guidelines|↩ Back to guidelines]]

## Why you need a fallback when the finiteness machinery doesn't apply

[[Order-Minimal-Structures-and-Definability|§7.3's order-minimal quotienting]] is powerful, but it has teeth only when your system's flow is *definable* in some order-minimal structure, and even then the Uniform Finiteness Theorem only guarantees a finite bisimilar quotient when the dynamics satisfies extra spectral conditions — Corollary 7.14's real-or-diagonalizable-imaginary eigenvalue requirement, tight enough that a linear system with eigenvalues $0.1 \pm i$ (a slowly spiraling focus) already breaks it. Most systems you actually care about — a nonlinear polynomial vector field guarding some unsafe region, say — simply don't come with a certificate that a finite exact quotient exists at all, let alone a recipe for building one.

So suppose you give up on getting a full finite bisimulation and ask a smaller question instead: you have a handful of functions $p_1, \dots, p_k : \mathbb{R}^n \to \mathbb{R}$ that matter to you — maybe $p$ carves out the boundary of a safe region, maybe it's a Lyapunov-like energy function — and you just want to know how the *sign* of each $p_i$ can evolve along trajectories. Can you build a finite-state abstraction from nothing more than these functions and the vector field, without ever solving for a single trajectory? That's what §7.4 delivers, and the mechanism it needs to make the answer sound — not just plausible — is the **Lie derivative**.

## The ternary partition induced by one function

Start with a single smooth function $p : \mathbb{R}^n \to \mathbb{R}$ on the state space of a dynamical system $\Sigma = (\mathbb{R}^n, f)$. It splits $\mathbb{R}^n$ into three pieces:

$$p^+ = \{x \in \mathbb{R}^n \mid p(x) > 0\}, \quad p^0 = \{x \in \mathbb{R}^n \mid p(x) = 0\}, \quad p^- = \{x \in \mathbb{R}^n \mid p(x) < 0\}.$$

Compose $p$ with a trajectory $\xi$ and you get $p \circ \xi : \mathbb{R} \to \mathbb{R}$, a smooth real function of time. Continuity of $p \circ \xi$ gives you one free fact for nothing: if $p \circ \xi$ is negative at some $\tau_1$ and positive at some later $\tau_2$, the intermediate value theorem forces some $\tau \in ]\tau_1, \tau_2[$ where $p \circ \xi(\tau) = 0$. A trajectory cannot teleport from $p^-$ to $p^+$ — it has to cross $p^0$ on the way. That's the entire seed of the construction: continuity constrains which *sequences* of signs are physically realizable, and those constraints are exactly what a finite-state model can encode.

## Sign conditions and the exact quotient they induce

Generalize to a finite collection $P = \{p_i\}_{i \in I}$ of smooth functions. A **sign condition** is a function $g : P \to \{1, 0, -1\}$ — think of it as a vector of "is $p_i$ positive, zero, or negative" answers, one per function. Each sign condition picks out a region

$$\langle g \rangle = \bigcap_{i \in I} \{x \in \mathbb{R}^n \mid \mathrm{sign}(p_i(x)) = g(p_i)\}.$$

The collection $\{\langle g \rangle\}_{g \in \{1,0,-1\}^P}$ partitions $\mathbb{R}^n$; call the induced equivalence relation $\sim_P$. (Notation for sets of sign conditions $G = \{g_1, \dots, g_k\}$ extends by $\langle G \rangle = \bigcup_j \langle g_j \rangle$.)

With two functions $p_1(x) = x_1, p_2(x) = x_2$ there are $3^2 = 9$ sign conditions — one per quadrant, axis-ray, and the origin. $g_3$, say, with $g_3(p_1)=1, g_3(p_2)=-1$, picks out $\langle g_3 \rangle = \{(x_1,x_2) \mid x_1 > 0 \wedge x_2 < 0\}$, the fourth quadrant.

This $\sim_P$ is just an ordinary finite equivalence relation, so plugging it into the [[Hybrid-Dynamical-Systems|Definition 7.2 machinery]] gives you the *exact* system $S_{\bar{P}}^L(\Sigma) := S_{\sim_P}^L(\Sigma)$: transitions sampled every time the sign vector changes, with the usual self-loop rule for trajectories that never leave a class. This system is exactly bisimilar in the trivial sense that it's *defined as* the quotient — but it's still generally infinite-state-flavored to *construct*, because building its transition relation requires knowing which $\langle g \rangle$ a trajectory actually visits next, which means solving the ODE. Nothing has been bought yet.

## Why sign alone isn't enough — you need to know which way things are moving

Here's the trap. Suppose you tried to build a finite abstraction using *only* the continuity fact from the ternary-partition argument above: "$g$ can transition to $g'$ whenever $\langle g \rangle$ and $\langle g' \rangle$ are adjacent (differ in one coordinate by exactly a sign-to-zero step)." This is sound — it's implied by nothing but continuity, so it can never miss a real transition — but it is also nearly useless. It says every region can reach every neighboring region, in both directions, regardless of the actual dynamics. A safety proof needs to show some bad region is *unreachable*; an abstraction that connects every region to its neighbors bidirectionally will almost never let you conclude that.

What you're missing is *directional* information: at a boundary point where $p_i = 0$, is the trajectory crossing from $p_i^-$ into $p_i^+$, or the reverse, or just grazing the boundary and turning back? That's precisely the question "is $p_i$ increasing or decreasing right now," and the answer is the **Lie derivative** of $p_i$ along $f$ — the one piece of *local, algebraic* information (no trajectory-solving required) that lets you rule out unsound direction assumptions.

## The Lie derivative

For $\Sigma = (\mathbb{R}^n, f)$ and a smooth $p : \mathbb{R}^n \to \mathbb{R}$, the **Lie derivative of $p$ along $f$** is

$$L_f p = \sum_{i=1}^n \frac{\partial p}{\partial x_i} f_i,$$

equivalently $L_f p(x) = \left.\frac{d}{dt}\right|_{t=0} p \circ \xi_x$, where $\xi_x$ is the trajectory through $x$. Geometrically it is exactly what it looks like from the second formula: the instantaneous rate of change of $p$ as you flow along $f$, i.e. $\nabla p(x) \cdot f(x)$, the directional derivative of $p$ in the direction the vector field is pushing you. Higher-order versions are defined recursively: $L_f^0 p = p$ and $L_f^{k+1}p = L_f(L_f^k p)$ — the $k$-th Lie derivative tells you about the $k$-th time-derivative of $p$ along the flow.

The key local fact: if $L_f p_i(x) > 0$ at a point where $p_i(x) = 0$, then for small $\varepsilon>0$, $p_i(\xi_x(\varepsilon)) > 0$ — the trajectory is *leaving* $p_i^0$ into $p_i^+$, not the other way. You get this without ever integrating the ODE; it's a purely algebraic consequence of the sign of a dot product.

## Definition 7.19: the sign-based system $S_{PL}(\Sigma)$

Given $\Sigma = (\mathbb{R}^n, f)$, a finite collection $P$ of smooth functions, the induced relation $\sim_P$, and a set of initial states $L$, the finite-state system $S_{PL}(\Sigma)$ has:

- $X = \{1, 0, -1\}^P$ (all sign conditions);
- $X_0 = \{g \in X \mid \langle g \rangle \cap L \ne \emptyset\}$;
- $U = \{*\}$ (one silent action label — this system only tracks *whether* a sign transition can happen, not what causes it);
- a transition $g \xrightarrow{*} g'$ whenever, **for every** $p_i \in P$, one of the following holds (writing $\mathrm{sign}(L_f p_i(\langle g \rangle))$ for the *set* of signs $L_f p_i$ can take as $x$ ranges over $\langle g \rangle$):
  1. If $g(p_i) = 1$: either (a) $\mathrm{sign}(L_f p_i(\langle g \rangle)) \subseteq \{1,0\}$ and $g'(p_i) = 1$, or (b) $\mathrm{sign}(L_f p_i(\langle g \rangle)) \supseteq \{-1\}$ and $g'(p_i) \in \{1,0\}$.
  2. If $g(p_i) = 0$: (a) sign is exactly $\{1\}$ and $g'(p_i)=1$; (b) sign is exactly $\{-1\}$ and $g'(p_i)=-1$; (c) sign is $\{1,-1\}$ (both occur, but never $0$, somewhere on the boundary set $\langle g \rangle$) and $g'(p_i) \in \{1,-1\}$; (d) sign includes $0$ and $g'(p_i) \in \{1,0,-1\}$ — no constraint at all.
  3. If $g(p_i) = -1$: mirror image of case 1.
- $Y = \mathbb{R}^n / \sim_P$;
- $H(g) = \langle g \rangle$.

Read the rules as: *if $L_f p_i$ has a determinate sign everywhere on $\langle g \rangle$, use it to rule out the physically impossible successor signs; if $L_f p_i$'s sign is ambiguous over $\langle g \rangle$ (the set $\mathrm{sign}(L_f p_i(\langle g \rangle))$ has more than one element), fall back to allowing every successor sign that continuity doesn't rule out.* This is exactly the "conservative when ambiguous" behavior of an abstract-interpretation transfer function: when you don't have enough local information to pin down the direction, you widen the set of possible successors rather than guess — and case 2(d) shows the worst case, where crossing a boundary with an indeterminate-sign derivative tells you nothing at all about which side you land on next.

**What breaks without the Lie derivative refinement.** If you dropped the $\mathrm{sign}(L_f p_i(\cdot))$ conditions entirely and kept only "adjacent classes may transition," you'd get the useless bidirectional-adjacency abstraction from the previous section. The Lie derivative conditions are what let a region genuinely have *no* outgoing edge to some neighbor — which is exactly what a safety proof needs.

### Worked example: a rotation

Take $f(x) = (x_2, -x_1)$ on $\mathbb{R}^2$ — clockwise circular motion around the origin — with $P = \{p_1, p_2\} = \{x_1, x_2\}$ (the same $P$ as the 9-region quadrant partition above) and $L = \{x_1>0 \wedge x_2>0\}$ (so $X_0 = \{g_1\}$, the first-quadrant sign condition). Compute:

$$L_f p_1 = \frac{\partial p_1}{\partial x_1}x_2 + \frac{\partial p_1}{\partial x_2}(-x_1) = x_2, \qquad L_f p_2 = \frac{\partial p_2}{\partial x_1}x_2 + \frac{\partial p_2}{\partial x_2}(-x_1) = -x_1.$$

On $\langle g_1 \rangle = \{x_1>0 \wedge x_2>0\}$: $L_f p_1 = x_2 > 0$ and $L_f p_2 = -x_1 < 0$. Since $g_1(p_1)=1$ and $L_f p_1 > 0$ everywhere on $\langle g_1\rangle$, case 1(a) forces $g'(p_1) = 1$. Since $g_1(p_2)=1$ and $L_f p_2 < 0$ everywhere, case 1(b) allows $g'(p_2) \in \{1,0\}$. The only sign conditions satisfying both are $g_1$ itself and $g_2$ (where $g_2(p_1)=1, g_2(p_2)=0$), giving exactly two transitions $g_1 \xrightarrow{*} g_1$ and $g_1 \xrightarrow{*} g_2$ — matching the geometric picture of a trajectory spiraling clockwise from the first quadrant, staying in $x_1>0$ the whole time, and eventually crossing the positive $x_1$-axis ($x_2=0$). Carrying the same computation around all nine regions reproduces the full cycle $g_1 \to g_2 \to g_3 \to \dots \to g_1$ (Tabuada's Figure 7.13) — the abstraction of a clockwise rotation is, unsurprisingly, a directed cycle through the sign regions in clockwise order, plus self-loops wherever the derivative's sign on that region is ambiguous.

## Proposition 7.21: soundness for safety

$$S_{\bar{P}}^L(\Sigma) \preceq_S S_{PL}(\Sigma)$$

Formally: the relation $R \subseteq \mathbb{R}^n \times \{1,0,-1\}^P$ defined by $(x, g) \in R \iff x \in \langle g \rangle$ is a simulation relation from the exact quotient system $S_{\bar{P}}^L(\Sigma)$ to the sign-based system $S_{PL}(\Sigma)$.

*Proof idea.* Take $(x,g) \in R$ and a transition $x \xrightarrow{\tau} x'$ in the exact system, coming from a trajectory $\xi$ with $\xi(0)=x, \xi(\tau)=x'$. Fix some $p_i \in P$ with, say, $g(p_i)=1$. Smoothness of $p_i \circ \xi$ leaves exactly three possibilities on $[0,\tau]$: (i) $p_i \circ \xi$ stays positive the whole interval; (ii) it's positive on $[0,\varepsilon[$ then hits zero and stays zero on $[\varepsilon,\tau]$; (iii) it's positive up through $\varepsilon$ then strictly negative after. In case (i), Definition 7.19's rules guarantee a transition to some $g'$ with $g'(p_i)=1$ *regardless of the Lie derivative's sign* — nothing to check. In cases (ii) and (iii), smoothness forces $\left.\frac{d}{dt}\right|_{t_0} p_i \circ \xi \le 0$ for some $t_0 \in [0,\varepsilon[$, i.e. $L_f p_i(x'') \le 0$ for $x'' = \xi(t_0)$ — witnessing that $-1 \in \mathrm{sign}(L_f p_i(\langle g \rangle))$ or the derivative vanishes there, which is exactly what Definition 7.19's case 1(b)/2(d) uses to license a transition to $g'(p_i) \in \{1,0\}$ or $\{1,0,-1\}$. Running the same case analysis for every $p_i$ and taking the conjunction shows some $g'$ with $(x', g') \in R$ is always reachable — $R$ is a simulation relation. $\blacksquare$

The practical payoff is in what each side of the relation costs to build. $S_{\bar{P}}^L(\Sigma)$ is defined *exactly*, but constructing its transitions needs the trajectories of $\Sigma$ — global, generally intractable information. $S_{PL}(\Sigma)$ needs only the *signs* of a finite set of Lie derivatives on a finite set of regions — local, algebraic information you can often get by inspection or a symbolic computer-algebra pass. Simulation in the direction $S_{\bar{P}}^L(\Sigma) \preceq_S S_{PL}(\Sigma)$ is precisely the property you need for **safety**: every behavior of the real system is matched by some behavior of the abstraction, so if the abstraction never reaches a "bad" sign condition, neither does the real system. (It says nothing about the converse — the abstraction may have spurious behaviors the real system doesn't, which is the price of soundness without tightness, addressed below.)

### Example 7.22: proving safety from three sign regions

Take $\Sigma$ from the earlier eigenvalue-spiral example and the single function

$$p(x) = 7x_1^2 - 6x_1 x_2 + 28x_2^2 - 320$$

(chosen, as Tabuada notes, because it will resurface as a barrier certificate — see "[[Exact-Symbolic-Models-for-Control#Where this leads|Where this leads]]" below). With $P = \{p\}$ there are three sign conditions $g_1$ ($p>0$), $g_2$ ($p=0$), $g_3$ ($p<0$), and $L_f p(x) < 0$ holds *everywhere* on $\mathbb{R}^2$ — a single global algebraic fact. Definition 7.19 then gives exactly the transitions $g_1 \to g_1$, $g_1 \to g_2$, $g_2 \to g_3$, $g_3 \to g_3$: a one-way street from $g_1$ toward $g_3$, with $g_1$ having no *incoming* edge from anywhere but itself. Since the initial set $L \subset \langle g_3 \rangle$, $g_1$ is unreachable in $S_{PL}(\Sigma)$, and by Proposition 7.21 it's therefore unreachable in the real system — safety of the region $\{p \ge 0\}$ is proved without ever computing a single trajectory of $\Sigma$.

## Closure/saturation: buying tightness back

Definition 7.19's rules are conservative exactly when $\mathrm{sign}(L_f p_i(\langle g \rangle))$ is not a singleton — when the sign of the Lie derivative isn't determined by $g$ alone. The fix follows the same idea abstract-interpretation domain refinement always uses: **add more information to the abstraction**. Concretely, if $L_f p_i$'s sign isn't constant on $\langle g \rangle$, throw $L_f p_i$ itself into $P$ as a new tracked function, recompute the partition (now finer, since you're also tracking the sign of $L_f p_i$), and repeat.

Call $P$ **closed with respect to the sign of the Lie derivative** when for every $p \in P$ and every $k \in \mathbb{N}$, the sign of $L_f^k p$ is constant on every $\langle g \rangle$ and determined by $g$ alone — i.e. the saturation process above has reached a fixed point. Example 7.23's $P = \{p_1, p_2\}$ from the rotation example is already closed: since $L_f p_1 = p_2$ and $L_f p_2 = -p_1$, you get $\mathrm{sign}(L_f p_1) = \mathrm{sign}(p_2)$ and $\mathrm{sign}(L_f p_2) = -\mathrm{sign}(p_1)$ directly from $g$, and by induction the same holds for every $L_f^k p_1, L_f^k p_2$ — the Lie derivative cycles back through functions already in $P$.

**Even closed $P$ doesn't give you exact bisimilarity**, only a tight *sandwich* on reachable sets. Example 7.24 makes the gap concrete: $\Sigma = (\mathbb{R}, -x)$, $P=\{p\}$ with $p(x)=x$ (trivially closed, since $L_f p = -p$). On $\langle g_1 \rangle = \{x>0\}$, $L_f p = -x < 0$, so Definition 7.19 licenses *both* $g_1 \to g_1$ and $g_1 \to g_2$ (the boundary $x=0$). But starting from any $x>0$, the real solution $\xi(t) = e^{-t}x$ decays toward $0$ *without ever reaching it* — the transition $g_1 \to g_2$ is a real edge in $S_{PL}(\Sigma)$ that has no counterpart in $S_{\bar{P}}^L(\Sigma)$. The abstraction is strictly larger than the truth here; it's sound, not exact.

### Theorem 7.25: tightness once closed

> Let $\Sigma = (\mathbb{R}^n,f)$, $P$ a finite collection of smooth functions with induced equivalence $\sim_P$, and $L$ a union of $\sim_P$-classes. If $P$ is closed with respect to the sign of the Lie derivative, then
> $$\bigcup_{Z \in \mathrm{Reach}(S_{\bar{P}}^L(\Sigma))} Z \;\subseteq\; \bigcup_{Z \in \mathrm{Reach}(S_{PL}(\Sigma))} Z \;\subseteq\; \overline{\bigcup_{Z \in \mathrm{Reach}(S_{\bar{P}}^L(\Sigma))} Z}.$$

The left inclusion is just Proposition 7.21 plus the general system-level fact that a simulated system's reachable set is contained in the simulator's — it holds unconditionally, closed or not. The right inclusion is what closure buys you, and it's a generalization of exactly the Example 7.24 pattern: it can be shown that a state reachable in $S_{PL}(\Sigma)$ but not in the exact system must sit on the *boundary* (a measure-zero, "thin" set) of the exact reachable region — equivalently, the two reachable sets have identical *interiors*. So the abstraction can only ever be wrong about a vanishingly thin sliver at the edge of the true reachable set; everywhere in the interior, sign-based abstraction and truth agree exactly. That is what "tight" means here: not bisimilar, but tight up to boundary effects.

**Caveats on closure.** Saturation is not guaranteed to terminate in general — repeatedly differentiating can generate infinitely many genuinely new functions. It terminates cleanly in special cases: for linear dynamics $f(x)=Ax$, picking $p(x) = v^Tx$ for $v$ an eigenvector of $A^T$ gives $L_f p = v^TAx = (A^Tv)^Tx = \lambda v^Tx = \lambda p$ — a *scalar multiple of $p$ itself*, so $\mathrm{sign}(L_f^k p) = \mathrm{sign}(\lambda)^k\,\mathrm{sign}(p)$ is determined after one derivative, and $P$ closes immediately. If $A$ is nilpotent, any affine $p$ eventually has $L_f^k p \equiv 0$ for large enough $k$, again terminating. And crucially: **even when saturation never terminates, the un-closed $S_{PL}(\Sigma)$ from whatever $P$ you stopped at is still a valid simulation** by Proposition 7.21 — you lose the tightness guarantee of Theorem 7.25, not the soundness guarantee. You can always stop early and still have a safety-valid (if possibly too-coarse-to-be-useful) abstraction.

## Grounding: computing Lie derivatives and building the transition graph

The whole construction is mechanical enough to automate directly. A symbolic pass computes $L_f p_i$ once per function; a numeric/algebraic pass then determines, per sign-region, whether that expression's sign is constant there.

```python
import sympy as sp

x1, x2 = sp.symbols('x1 x2', real=True)
X = [x1, x2]

# f(x) = (x2, -x1): the rotation from the worked example.
f = [x2, -x1]

def lie_derivative(p, f, X):
    return sum(sp.diff(p, xi) * fi for xi, fi in zip(X, f))

p1, p2 = x1, x2
Lf_p1 = sp.simplify(lie_derivative(p1, f, X))   # -> x2
Lf_p2 = sp.simplify(lie_derivative(p2, f, X))   # -> -x1

# Definition 7.19's per-function transition rule, specialized to the case
# where sign(Lf_p) is constant on the region (the "closed" case) — the
# general conservative fallback (2d) applies whenever this assumption fails.
def successors_for_function(g_pi: int, lf_sign: int) -> set[int]:
    if g_pi == 1:
        return {1} if lf_sign >= 0 else {1, 0}      # 1a / 1b
    if g_pi == -1:
        return {-1} if lf_sign <= 0 else {0, -1}     # mirror of 1a/1b
    # g_pi == 0
    if lf_sign == 1:   return {1}                    # 2a
    if lf_sign == -1:  return {-1}                   # 2b
    return {1, 0, -1}                                 # 2d: ambiguous -> no info

def region_sign(expr, region: dict[sp.Symbol, int]) -> int | None:
    """Evaluate expr's sign at a representative point of `region`
    (a dict mapping each variable to a signed unit). Returns None if
    sign isn't determined by the region alone (needs a real solver
    for the general nonlinear case; this is illustrative)."""
    sample = {v: sign for v, sign in region.items()}
    val = expr.subs({X[i]: sample[X[i]] for i in range(len(X))})
    return int(sp.sign(val))

# Build every sign condition g: {p1,p2} -> {1,0,-1} and the transitions
# out of it, mirroring Definition 7.19 for this (closed) P.
functions = [(p1, Lf_p1), (p2, Lf_p2)]
signs = [-1, 0, 1]
graph = {}
for g1 in signs:
    for g2 in signs:
        g = (g1, g2)
        region = {x1: g1 if g1 != 0 else 0, x2: g2 if g2 != 0 else 0}
        succ_sets = []
        for (p, lf_p), gi in zip(functions, g):
            lf_sign = region_sign(lf_p, region)
            succ_sets.append(successors_for_function(gi, lf_sign))
        # cartesian product of per-function successor sets = successors of g
        import itertools
        graph[g] = set(itertools.product(*succ_sets))

print(graph[(1, 1)])   # reproduces {(1,1), (1,0)} from the worked example
```

The transition-rule table itself — Definition 7.19's twelve cases — is a natural fit for a Rust state machine, since it's a total function from (current sign, Lie-derivative sign set) to a set of allowed next signs, exactly the shape of an abstract transformer in an abstract-interpretation lattice:

```rust
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sign { Pos, Zero, Neg }

/// The set of signs L_f p_i actually takes over a region — a singleton
/// when the region is "closed" for this function, {Pos,Neg} or a superset
/// containing Zero when it's ambiguous (forces the conservative case).
#[derive(Clone, Debug)]
struct LieSign(Vec<Sign>); // small set, no duplicates

impl LieSign {
    fn contains(&self, s: Sign) -> bool { self.0.contains(&s) }
    fn is_exactly(&self, s: Sign) -> bool { self.0 == [s] }
}

/// Definition 7.19: one function p_i's contribution to the transition rule.
/// Returns every g'(p_i) consistent with g(p_i) and the observed Lie-derivative signs.
fn successors(g_pi: Sign, lf: &LieSign) -> Vec<Sign> {
    use Sign::*;
    match g_pi {
        Pos => {
            // 1a: Lf ⊆ {Pos, Zero} -> stays Pos.
            // 1b: Lf ⊇ {Neg}       -> may fall to Pos or Zero.
            if lf.contains(Neg) { vec![Pos, Zero] } else { vec![Pos] }
        }
        Neg => {
            if lf.contains(Pos) { vec![Zero, Neg] } else { vec![Neg] }
        }
        Zero => {
            if lf.is_exactly(Pos)  { vec![Pos] }             // 2a
            else if lf.is_exactly(Neg)  { vec![Neg] }        // 2b
            else if lf.contains(Zero)   { vec![Pos, Zero, Neg] } // 2d: no info
            else { vec![Pos, Neg] }                          // 2c: both signs occur, never zero
        }
    }
}
```

The `enum Sign` plus exhaustive `match` is doing exactly what Definition 7.19's case split does on paper: the compiler enforces that every combination of current sign and Lie-derivative-sign-set is handled, and there is no representable "fourth" sign to accidentally admit — a soundness guarantee for free from the type system, the same way [[Timed-Automata-and-Quotient-Based-Abstraction|the timed-automaton `Reset` enum]] ruled out non-syntactic resets by construction.

## Connection: this is a hand-built abstract-interpretation domain

Everything above is a specific instance of a much more general move you'll recognize from static analysis: $\{1,0,-1\}^P$ is a finite abstract domain (a product of a three-valued sign lattice, one copy per tracked function), $\langle \cdot \rangle$ is the concretization map $\gamma$ of a Galois connection whose abstraction map $\alpha$ sends a concrete state to its sign vector, and Definition 7.19's transition rule is an **abstract transformer**: given an abstract state and the Lie-derivative information available, it computes the set of abstract successors, falling back to the top-of-the-lattice answer $\{1,0,-1\}$ whenever the available information is ambiguous — precisely how a real abstract interpreter handles a branch condition it can't statically resolve. The closure/saturation process is domain *refinement*: instead of accepting whatever precision the initial $P$ happens to give you, you add derived facts ($L_f p_i$ as new tracked quantities) until the domain is expressive enough to pin down every transition exactly — structurally the same "keep refining the abstraction until it's precise enough to answer the query" loop that drives CEGAR and predicate-abstraction refinement. If you're building a verification tool's invariant-generation pass, this is the same pattern: pick a small set of candidate predicates, propagate sign/derivative information through the dynamics, and saturate only as much as the property you're proving actually needs.

## Where this leads

Sign-based abstraction gets you a genuine finite-state symbolic model — you can hand $S_{PL}(\Sigma)$ to the fixed-point reachability algorithms of [[Fixed-Point-Methods-for-Verification]] just like any other finite system. But building it (and especially saturating it to tightness) is real work, and Example 7.22 already hints at something cheaper: if all you actually need is *one* safety proof for *one* unsafe region, rather than a reusable symbolic model for arbitrary future properties, you don't need the full transition-graph machinery at all. That's exactly the move §7.5 makes next — a **barrier certificate** is a single function $E$ satisfying a sign condition plus $L_f E \le 0$ that proves safety directly, using the same Lie-derivative arithmetic developed here but skipping the construction of $S_{PL}(\Sigma)$ entirely, and reducing to a convex (sum-of-squares) feasibility search rather than an explicit finite-state search. Sign-based abstraction is the general-purpose, reusable tool; barrier certificates are the specialized, cheaper one for when a single property is all you want.
