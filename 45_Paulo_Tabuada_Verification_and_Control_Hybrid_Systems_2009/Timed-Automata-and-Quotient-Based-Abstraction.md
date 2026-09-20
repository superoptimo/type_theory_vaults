---
title: "Timed Automata and Quotient-Based Abstraction"
source: "Verification and Control of Hybrid Systems: A Symbolic Approach (Tabuada, 2009)"
chapter: "Chapter 7, §7.2 (pp. 80–86)"
tags: [hybrid-systems, timed-automata, bisimulation, quotient-abstraction, sat-smt-csp, model-checking]
---

[[book-guidelines|↩ Back to guidelines]]

## Why an uncountable state space doesn't have to mean an infinite model

A timed automaton's state is a pair: a finite control mode, plus a handful of real-valued clocks. Even with just two clocks, the continuous part of the state space is $(\mathbb{R}_0^+)^2$ — uncountably many points. If you wanted to verify a safety property by exhaustively exploring reachable states, you'd be stuck: there's no way to enumerate an uncountable set.

The resolution is the one this book keeps returning to (see [[Hybrid-Dynamical-Systems]] for the general machinery of $S_Q^L(\Sigma)$): you don't need to track *every* clock value, only the clock values that are *distinguishable* by the automaton's own logic — its invariants, its guards, and how its resets and flows move points around. If you can build a finite equivalence relation $Q$ on the clock space such that (a) it separates every distinction the automaton can make, and (b) two clock valuations in the same class stay in lock-step forever — visiting the same classes at the same relative times — then the quotient $X/Q$ *is* a finite bisimilar model. Nothing about the original infinite-state behavior is lost; the automaton literally cannot tell $x$ and $x'$ apart if they're $Q$-equivalent.

The question §7.2 answers is: for timed automata specifically, does such a $Q$ always exist, and can you build it constructively? The answer is yes, and the *reason* it works is worth isolating carefully, because §7.3's order-minimal structures will later show it's really a special case of a much more general finiteness phenomenon — but for timed automata you can see the whole construction by hand.

## What makes a hybrid system a timed automaton (Definition 7.6)

Recall from [[Hybrid-Dynamical-Systems]] that a hybrid dynamical system is a quintuple $\Sigma = (S_a, \{\mathrm{In}_{x_a}\}, \{\mathrm{Gu}_{t_a}\}, \{\mathrm{Re}_{t_a}\}, \{f_{x_a}\})$: a finite-state "mode" automaton $S_a$, each mode $x_a$ carrying an invariant set $\mathrm{In}_{x_a} \subseteq \mathbb{R}^n$ it must stay inside, each discrete transition carrying a guard set (when the transition is enabled) and a reset map (how the continuous state jumps), and each mode carrying its own continuous dynamics $f_{x_a}$.

A **timed automaton** (Definition 7.6) is a hybrid dynamical system satisfying four syntactic restrictions on those ingredients:

1. Every invariant $\mathrm{In}_{x_a}$ is a finite conjunction of conditions $x_{b_i} \sim c$, with $\sim \in \{\le, <, =, >, \ge\}$ and $c \in \mathbb{Q}_0^+$ — a rational, non-negative constant.
2. Every guard $\mathrm{Gu}_{(x_a,u,x_a')}$ has exactly the same shape: a conjunction of $x_{b_i} \sim c$ conditions with rational constants.
3. Every reset $\mathrm{Re}_{(x_a,u,x_a')}$ sends each coordinate $x_{b_i}$ to *either* itself (unchanged) *or* to $0$ — nothing more elaborate, like $x_{b_i} \mapsto x_{b_i} - 3$ or $x_{b_i} \mapsto x_{b_j}$.
4. Every mode's dynamics has unit slope in every coordinate: $\pi_i \circ f_{x_a}(x_b) = 1$ for all $i$ — i.e. $\dot{x}_{b_i} = 1$. These are *clocks*, all ticking at the same rate.

Tabuada's running example (Figure 7.2, carried over from Chapter 1) is a periodic real-time task with two clocks $\xi_1, \xi_2$ and modes `sleep`, `awake`, `starting`, `execute`, `active`, `error`, `finished`, `expired`. The invariant on `active` is $0 \le \xi_1 \le D$ — condition 1. The guard on `active` $\xrightarrow{\text{expired}}$ `error` is $\xi_1 = D$ — condition 2. The transition `active` $\xrightarrow{\text{starting}}$ `execute` carries the reset $\xi_2 := 0$, i.e. $\mathrm{Re}(x_b) = (x_{b_1}, 0)$ — condition 3. And every mode has $\dot{\xi}_1 = 1, \dot{\xi}_2 = 1$ — condition 4.

**What breaks without these restrictions.** Each restriction is load-bearing for finiteness, not decoration:
- If constants could be arbitrary reals instead of rationals, comparisons like $x_{b_1} < \pi$ (irrational) would in principle require distinguishing infinitely many "how close to $\pi$" classes as the region construction below tries to make classes closed under the flow — rationality is what keeps the region boundaries commensurable with each other.
- If resets could shift by an arbitrary constant or copy one clock into another, the region construction's Step 3 below (making $Q$ respect resets) could churn forever, since a reset could always push you into a genuinely new fractional-part relationship between clocks.
- If clocks could run at different rates ($\dot{x}_{b_i} = k_i \ne 1$), the diagonal lines the flow traces through the clock space would no longer be parallel — comparisons like "which of $x_{b_1}, x_{b_2}$ reaches its next integer boundary first" would depend on real ratios, reintroducing uncountably many cases.

Grounding this as a type: in Rust, a clock constraint is naturally an enum over comparisons against a rational constant, and a timed automaton mode is a small struct pairing an invariant (a conjunction of such constraints) with unit-rate clocks implicit in the type:

```rust
#[derive(Clone, Copy, PartialEq)]
enum Cmp { Le, Lt, Eq, Gt, Ge }

struct ClockConstraint {
    clock_index: usize,
    cmp: Cmp,
    // rational constant, kept as (numerator, denominator) to stay exact —
    // condition 1/2 of Definition 7.6 requires c in Q, not just any real.
    bound: (i64, i64),
}

struct Mode {
    invariant: Vec<ClockConstraint>, // conjunction
}

enum Reset {
    Unchanged,
    ResetToZero,
} // condition 3: nothing else is allowed

struct Transition {
    guard: Vec<ClockConstraint>,
    resets: Vec<Reset>, // one per clock, condition 3
}
```

The type itself enforces conditions 1–3: there is no representable `ClockConstraint` with an irrational bound, and no representable `Reset` other than "leave it" or "zero it."

## Why the naive guard/invariant partition isn't enough

Take the concrete two-clock example Tabuada builds (§7.2, with $C=1, D=2, T=3$): partition $(\mathbb{R}_0^+)^2$ by literally following every threshold that appears in any invariant or guard — cut at $x_{b_1} \in \{0, 2, 3\}$ and $x_{b_2} \in \{0, 1\}$. This gives an equivalence relation $Q$ with 24 classes: six single points (the grid intersections), twelve open line segments (the grid edges), and six open 2-D rectangles (the grid cells) — see Figure 7.3.

$Q$ *does* respect every invariant and every guard, by construction — every invariant and guard boundary is one of the cut lines. But $Q$ **fails to respect the continuous flow**: two points in the same open rectangle, say $(0.5, 0.3)$ and $(1.5, 0.3)$, both in the class $\{0 < x_{b_1} < 2 \wedge 0 < x_{b_2} < 1\}$, do *not* stay together forever. Because both clocks tick at rate 1, the flow through $(x_{b_1}, x_{b_2})$ is the straight diagonal line $(x_{b_1}+t, x_{b_2}+t)$. Starting from $(0.5,0.3)$, after $t=0.7$ you're at $(1.2, 1.0)$, crossing the $x_{b_2}=1$ line — but starting from $(1.5,0.3)$, after the *same* $t=0.7$ you're at $(2.2, 1.0)$, which has *also* crossed $x_{b_1}=2$. Same starting class, different classes visited along the way, at different relative moments. That's exactly the property a bisimulation cannot have (Figure 7.4): if $Q$ can't guarantee "same class in $\Rightarrow$ same class out, forever," the quotient system's transitions would depend on which representative you picked, and it stops being deterministic-up-to-$Q$, i.e. it stops being a bisimulation.

**What breaks without flow-respecting refinement.** Without this step, the "abstraction" would be simulation at best — sound for proving some properties reachable, unsound for proving safety, since a real trajectory could visit a bad region that its abstract shadow never shows.

## The region-refinement construction

Tabuada's fix is the classical **clock-region construction**, presented here as an explicit sequence of refinements — this is the concrete recipe underlying "refining an equivalence relation to respect invariants, guards, resets, and flow" from the topic outline:

1. **Start:** $Q$ — respects invariants and guards (by construction, since it's built from their threshold lines), but not flow or resets.
2. **Refine for flow:** since every trajectory is a unit-slope diagonal, two points are flow-equivalent only if they lie on the same diagonal line *relative to the grid* — concretely, a class like the open rectangle $\{0 < x_{b_1} < 2, 0 < x_{b_2} < 1\}$ must be sliced further along diagonals so that all points in a sub-class reach the rectangle's boundary through the *same* edge at the *same* relative time. This yields $Q'$ (Figure 7.5) — every class of $Q'$ is now closed under "co-flow": any two points in a class visit the same sequence of $Q'$-classes under the flow.
3. **Check resets:** but $Q'$ is still not good enough, because resets can map a class to a set that isn't a $Q'$-class. Concretely, the reset $r_1(x_{b_1},x_{b_2}) = (x_{b_1}, 0)$ applied to the $Q'$-class $\{0 < x_{b_1} < 2 \wedge x_{b_2}=1\}$ produces $\{0 < x_{b_1} < 2 \wedge x_{b_2} = 0\}$ — which is *not* one of the classes shown in Figure 7.5 (that edge got sliced differently by the flow-refinement). So $Q'$ fails to respect resets.
4. **Refine for resets:** slice again so every class's image under every possible reset ($\mathbf{1}$, $r_1$, $r_2$, $r_{12}$) lands exactly on a class boundary. This yields $Q''$ (Figure 7.6) — but refining *this* way can re-break the flow property from step 2!
5. **Refine for flow again:** one more pass restores flow-respecting-ness without breaking the reset property, yielding $Q'''$ (Figure 7.7) — a fixed point where invariants, guards, resets, *and* flow are all simultaneously respected.

This alternating refine-for-flow / refine-for-resets / refine-for-flow pattern is exactly a fixed-point computation over a lattice of partitions — the same style of "iterate a monotone refinement operator until it stabilizes" that recurs throughout the book (see [[Fixed-Point-Methods-for-Verification]]). It terminates here because the source constants are rational: every new cut line the construction can ever introduce is at a rational offset from an existing one, so there are only finitely many possible cut lines to converge onto.

A Python sketch of the region-construction loop, restricted to interval-boundary bookkeeping for a small fixed set of rational constants (illustrative, not literally what the book does at the geometry level, but structurally the same fixed-point):

```python
from fractions import Fraction

def refine_for_flow(classes, dims=2):
    """Split every class so all points reach the same next boundary
    at the same relative time under the unit-slope diagonal flow."""
    refined = set()
    for cls in classes:
        # a class is a tuple of (lo, hi, closed_lo, closed_hi) per dim,
        # or a fixed point value; split along the diagonal so that the
        # "distance to the nearest boundary in each coordinate" agrees
        # across the whole class.
        refined |= split_along_diagonal(cls, dims)
    return refined

def refine_for_resets(classes, resets):
    """Split every class so that every listed reset map sends the
    class exactly onto a union of existing classes."""
    refined = set(classes)
    changed = True
    while changed:
        changed = False
        for cls in list(refined):
            for reset in resets:
                image = reset(cls)
                if not is_union_of(image, refined):
                    refined -= {cls}
                    refined |= split_to_match(cls, image, refined)
                    changed = True
    return refined

def region_construction(initial_classes, resets):
    classes = initial_classes
    while True:
        after_flow = refine_for_flow(classes)
        after_resets = refine_for_resets(after_flow, resets)
        if after_resets == classes:
            return classes          # Q''' — fixed point reached
        classes = after_resets
```

The `while True` loop is the operational content of "refine until invariants, guards, resets, and flow are all respected simultaneously" — and it halts precisely because rational constants and unit-slope flow guarantee only finitely many distinct boundaries can ever be introduced.

## Lemma 7.7: stitching local bisimulations into a global one

Region refinement gives you, for a *single* mode $x_a$, a finite equivalence relation $Q_{x_a}$ on $\mathrm{In}_{x_a}$ that is a bisimulation for the continuous dynamics alone. Lemma 7.7 is the general glue showing when a *family* $\{Q_{x_a}\}_{x_a \in X_a}$ of such per-mode relations combines into a single finite bisimulation for the whole hybrid system $S_Q(\Sigma)$. The three hypotheses are exactly the three properties region refinement was built to achieve:

1. $Q_{x_a}$ is a bisimulation relation between $S_{Q_{x_a}}(\mathrm{In}_{x_a}, f_{x_a})$ and itself — i.e. it respects the continuous flow within mode $x_a$.
2. $Q_{x_a}$ respects the guard sets of $x_a$'s outgoing transitions.
3. $Q_{x_a}$ is compatible with the reset maps: if $x_b, x_b'$ are $Q_{x_a}$-equivalent and both satisfy a guard, their images under the corresponding reset are $Q_{x_a'}$-equivalent in the target mode.

The proof (a direct consequence of Theorem 4.18 from [[Exact-System-Relationships]] — quotienting by a bisimulation relation always yields a bisimilar quotient system) defines $R \subseteq X \times X$ on the full state space $X = \{(x_a, x_b)\}$ by declaring $((x_a,x_b),(x_a',x_b')) \in R$ iff $x_a = x_a'$ and $(x_b,x_b') \in Q_{x_a}$ — literally "weave the per-mode relations together along the shared discrete-mode coordinate." Discrete transitions preserve $R$ because guards and resets are respected (hypotheses 2–3); continuous flows preserve $R$ because each $Q_{x_a}$ is itself a bisimulation for its mode's dynamics (hypothesis 1). One special case is worth flagging: **when all reset maps are constant** (mode-entry always resets to the same fixed point, regardless of where you came from), hypothesis 3 is automatic — you only need to solve the single-mode flow/guard problem per mode, which is a meaningfully easier design task than the general case.

## Theorem 7.8: quotient-based abstractions always exist for timed automata

Region refinement plus Lemma 7.7 combine into the chapter's payoff result:

> **Theorem 7.8.** Let $\Sigma$ be a timed automaton and $Q = \{Q_{x_a}\}$ a collection of finite equivalence relations on each $\mathrm{In}_{x_a}$, with equivalence classes defined by finite conjunctions of $x_{b_i} \sim c$ conditions ($c \in \mathbb{Q}_0^+$). Then there exists a finite-state system bisimilar to $S_Q(\Sigma)$.

Note what this theorem is really asserting: it's not merely "some finite bisimilar model exists for some clever choice of $Q$" — it's that *any* rational-threshold-defined finite equivalence relation can always be refined (by the region construction) into one satisfying Lemma 7.7's hypotheses, and the refinement process is guaranteed to terminate. This is what "quotient-based abstraction" means concretely: build a *finite* equivalence relation respecting everything the automaton can observe, and the quotient system inherits exact bisimilarity for free via Theorem 4.18. No approximation, no loss of information — this is the *exact* symbolic model the chapter's title promises, in contrast to the stability-based, genuinely lossy $\varepsilon$-approximate models of Part IV.

## The equivalence-relation-respects-flow property, formalized

The property doing all the real work above — "$Q$ is a bisimulation for the flow" — has a clean, type-theoretic shape: it says the quotient map $\pi_Q$ *commutes* with the flow up to $Q$-equivalence. Concretely: for all $x, x'$ with $x \sim_Q x'$, and all $t$ in the (possibly different) domains where the flow stays defined, $\theta(x,t) \sim_Q \theta(x',t)$ — or, phrased for timed automata specifically with region-indexed time, that $x$ and $x'$ cross region boundaries at the same instants. This is precisely a *congruence* condition on $\sim_Q$ with respect to the flow map, the same shape as "substitution respects definitional equality" in a type theory. A Lean sketch of the property (leaving the concrete region geometry abstract, since the point is the congruence shape, not the geometric proof):

```lean
-- A finite equivalence relation on the clock space, packaged with
-- the property that it is a congruence for the continuous flow.
structure FlowRespectingQuotient (Clocks : Type) (flow : Clocks → ℝ → Clocks) where
  Q : Clocks → Clocks → Prop
  equiv : Equivalence Q
  finite_classes : Finite (Quotient (Setoid.mk Q equiv))
  -- This is the load-bearing clause: Q is a congruence for `flow`.
  respects_flow : ∀ x x' t, Q x x' → Q (flow x t) (flow x' t)

-- Lemma 7.7's hypothesis 1, specialized: SQ(In, f) being a bisimulation
-- of itself under Q is exactly `respects_flow` plus finiteness.
theorem region_flow_congruence
    {Clocks : Type} (flow : Clocks → ℝ → Clocks)
    (Q : FlowRespectingQuotient Clocks flow)
    (x x' : Clocks) (h : Q.Q x x') (t : ℝ) :
    Q.Q (flow x t) (flow x' t) :=
  Q.respects_flow x x' t h
```

This is the exact same shape as proving a typing judgment is preserved under a reduction step, or that definitional equality is preserved under substitution: you're showing a relation is stable under an operation the system will actually perform. Framing it this way is not incidental — it is literally what makes $Q_{x_a}$'s satisfaction of Lemma 7.7's hypothesis 1 a *provable, checkable* fact rather than a geometric hope, and it is the same discipline a CEGAR-style abstraction-refinement loop needs when it proves a refined predicate abstraction is still sound: each refinement step must be proved to preserve the invariant that made the previous abstraction valid.

## Synthesis: the first concrete instance of exact quotient-based abstraction, and what generalizes

Chapter 4 promised that quotienting by a bisimulation relation always yields an exactly bisimilar finite model (Theorem 4.18); Chapter 7 opened by asking *for which infinite-state systems can you actually construct such a $Q$*. Timed automata are the chapter's first fully worked answer, and the mechanism is worth stating plainly: **rational thresholds plus unit-slope flow bound how many distinct "clock regions" can ever exist**, because every new boundary the refinement process can introduce is forced to sit at a rational offset from thresholds already present in the automaton's finite syntactic description. That's a finiteness argument grounded in number-theoretic commensurability, not in any deep structural theory.

§7.3 (order-minimal structures, topic 9) generalizes the *reason*, not the recipe: instead of hand-tracing region boundaries, it invokes the **Uniform Finiteness Theorem** (Theorem 7.11) — for any *definable* set $W \subseteq \mathbb{R}^m \times \mathbb{R}^n$ in an order-minimal structure, the number of connected components of each fiber $W_z$ is uniformly bounded across all $z$. Applied to the graph of the flow map $\theta$, this single abstract finiteness fact does automatically, for the much larger class of systems whose flow is *definable* (semi-linear, semi-algebraic, semi-exponential-algebraic...), exactly what the by-hand region construction did here for timed automata's unit-slope flows. Timed automata's flow is trivially definable (it's affine), so Theorem 7.13 in §7.3 actually *subsumes* Theorem 7.8 as a special case — but seeing the concrete region-refinement recipe first is what makes the abstract Uniform Finiteness argument legible later, rather than a black box.

For the `sat-smt-csp` focus area specifically: the region-refinement loop above — alternately tightening a partition against guard/reset/flow constraints until it stabilizes — is structurally the same move as CEGAR's abstraction-refinement loop and as building a DFA-shaped abstract domain for a data structure: you're constructing a finite quotient automaton whose states are exactly the equivalence classes your verification questions can distinguish, and proving termination by bounding how many distinct classes the constraint language (rational thresholds, in this case) can ever generate. That "bound the abstract domain's size via the syntactic shape of the constraint language" argument reappears whenever you're designing a decidable abstraction for an otherwise infinite-state reachability problem.

## Where this leads

Theorem 7.8's timed-automaton construction is the template the rest of the chapter's *exact* techniques (order-minimal quotients in §7.3, sign-based abstractions in §7.4) all vary on; it also foreshadows Chapter 8's [[Exact-Symbolic-Models-for-Control#Discrete-time|discrete-time]] linear control abstractions (adapted partitions), which reuse the same "refine a partition until it's closed under the dynamics" pattern for a control setting where the abstraction additionally has to support controller synthesis, not just verification.
