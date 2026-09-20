---
title: "The AbSolute Solver"
source: "Abstract Domains in Constraint Programming (Marie Pelleau, ISTE/Wiley, 2015)"
chapter: "Chapter 6, §6.2 — 'The AbSolute Solver' (pp. 122–131), building on §6.1.5–6.1.6 (pp. 117–122)"
tags: [abstract-interpretation, constraint-programming, apron, ocaml, splitting-operator, polyhedra, mixed-integer-real, abstract-domains]
---

[[book-guidelines|↩ Back to guidelines]]

## Why build an actual solver at all

Chapter 6's first half (§6.1) does something conceptually daring: it takes Constraint Programming's whole machinery — domains, propagators, exploration — and re-expresses every piece of it as an object from Abstract Interpretation (AI). A CSP's search space becomes a concrete domain $\hat D$; propagators become lower closure operators $\rho^\flat$; the classical Cartesian domain representations (integer tuples, boxes) become instances of a general "abstract domain" record type $(D^\sharp, \gamma, \alpha, \dots)$. That reformulation is elegant, but elegance alone doesn't solve a CSP. Two things are still missing that AI, as a *static analysis* theory, never needed:

1. **A splitting operator.** AI analyzes a fixed program; when it needs disjunction (e.g. at an `if`), it creates exactly two branches, analyzes each, and then *joins* them back into one abstract element before continuing. It never needs to keep refining a single element into arbitrarily many smaller ones in search of a point solution. CSP solving is exactly that: keep cutting a domain until what's left either satisfies every constraint or is small enough to ignore. So §6.1.5 introduces a genuinely new AI-style operator, $\oplus : D^\sharp \to E^\sharp$ (into the *disjunctive completion* $E^\sharp = \mathcal{P}_{\text{finite}}(D^\sharp)$), with three soundness conditions: finite branching, each piece no bigger than the original ($e_i \sqsubseteq^\sharp e$), and no solutions lost ($\gamma(e) = \bigcup \gamma(e_i)$).
2. **A choice operator.** Given a whole disjunction of things-still-to-explore, something has to decide which piece to work on next, and when a piece is "done" (below a precision threshold $r$). This is Definition 6.1.6's $\pi : E^\sharp \to D^\sharp$.

With those two additions bolted onto AI's existing vocabulary, Algorithm 6.1 (the generic abstract solver: pop an element, propagate, then discard / keep-as-solution / split) becomes a drop-in replacement for classical CP solving — and it's proved to terminate (König's lemma, via Definition 6.1.7's compatibility condition between the splitting operator $\oplus$ and the size function $\tau$) and to be sound (each iteration keeps $\bigcup\{\gamma(x)\mid x \in \text{toExplore}\cup\text{sols}\}$ an over-approximation of the true solution set).

**AbSolute** is Pelleau's proof that this isn't just paperwork: a working OCaml prototype that instantiates Algorithm 6.1 concretely on top of Apron, a real numeric-abstract-domain library built for static analysis. If the reformulation is correct, you should be able to hand a CSP solver's job to a program that was never designed to solve CSPs — only to prove things about programs. That's the experiment this section reports on.

```mermaid
flowchart TB
    A["CSP: variables + domains + constraints"] --> B["AbSolute: Environment (int vars, real vars) + linear-constraint table"]
    B --> C["Abstraction: Apron manager builds D# (Box / Oct / Polka)"]
    C --> D["Consistency: local iterations of test-transfer-functions,\ncapped at 3, non-linear terms linearized"]
    D -->|fixpoint or cap reached| E{size τ(e) ≤ r\nor isSol(e)?}
    E -- yes --> F["e added to sols"]
    E -- no --> G["Naive split ⊕: largest dimension of\nbounding box, cut in half"]
    G --> H["push both halves onto toExplore"]
    H --> D
    F --> I["toExplore empty? done"]
```

## Implementation on top of the Apron abstract domain library

AbSolute doesn't implement its own numeric abstract domains — it delegates to **Apron**, a library built for static program analysis that already ships intervals, octagons, and polyhedra (among others) behind one uniform API. The key engineering payoff of building on Apron rather than reimplementing per-domain logic is genericity: AbSolute's consistency routine, splitting routine, and solve loop are written *once*, parametrized over which domain's "manager" gets passed in — they never need to know whether they're manipulating a box, an octagon, or a polyhedron.

This is precisely the shape of an object-oriented (or trait-based) abstraction over multiple implementations of the same interface, and it's worth naming exactly, because it's the same architectural move you'll make when you give your own compiler's abstract-interpretation pass a pluggable domain.

```rust
// The "manager" pattern from Apron/AbSolute, as a Rust trait.
// Any numeric abstract domain (box, octagon, polyhedron, ...) implements this
// once, and the generic consistency/split/solve code never needs to know which.
trait AbstractDomain: Sized {
    type Manager;

    /// Build the top element (or one representing an initial box of constraints).
    fn of_lincons(man: &Self::Manager, vars: &Environment, cons: &[LinCons]) -> Self;

    /// Apron's "test transfer function": tighten `self` w.r.t. one constraint.
    /// This is where HC4-Revise (intervals), or a domain-specific propagator,
    /// or a linearized fallback, actually lives.
    fn test(&self, man: &Self::Manager, c: &Constraint) -> Self;

    /// Size function τ: how "big" is this element still?
    fn size(&self) -> f64;

    /// Naive splitting operator ⊕: cut along the largest dimension of the
    /// smallest enclosing box, regardless of the concrete domain shape.
    fn split(&self, man: &Self::Manager, vars: &Environment) -> Vec<Self>;
}
```

Every later piece of §6.2 — modelization, abstraction, consistency, splitting — is just an instantiation of this one interface, exactly as the book presents it.

## Problem modelization with mixed integer and real environments

Abstract Interpretation has no native notion of "a variable's domain" — a program variable's possible values are whatever the analysis infers, not a declared input. CP, by contrast, *starts* from declared domains. AbSolute bridges this by folding domain declarations into the constraint store itself: a CSP is represented as an **environment** (two tables, one of integer variables, one of real variables) plus a table of linear constraints, where the variable bounds ($v_1 \geq 1$, $v_1 \leq 5$, …) are stored as ordinary constraints alongside the problem's real constraints. Example 6.2.1 in the book:

$$
D_1 = D_2 = [\![1,5]\!] \subset \mathbb{Z}, \quad D_3 = [-10,10] \subset \mathbb{R}
$$
$$
C_1: 6v_1 + 4v_2 - 3v_3 = 0 \qquad C_2: v_1 \times v_2 \geq 3.5
$$

becomes, in AbSolute (OCaml):

```ocaml
let v1 = Var.of_string "v1";;
let v2 = Var.of_string "v2";;
let v3 = Var.of_string "v3";;
let csp =
  let vars = Environment.make [|v1; v2|] [|v3|] in           (* ints, reals *)
  let doms = Parser.lincons1_of_lstring vars
    ["v1 >= 1"; "v1 <= 5"; "v2 >= 1"; "v2 <= 5"; "v3 >= -10"; "v3 <= 10"] in
  let cons = Parser.tcons1_of_lstring vars
    ["6*v1 - 4*v2 - 3*v3 = 0"; "v1*v2 >= 3.5"] in
  (vars, doms, cons);;
```

Notice what this buys: `Environment.make` takes an integer-variable array and a real-variable array *simultaneously*. There's no separate "discrete solver" and "continuous solver" to route the problem to — a single environment can be genuinely mixed, something that is structurally awkward in most CP solvers (which historically bolt integers onto a continuous engine, or vice versa, via ad hoc discretization).

**What breaks without this:** if domains weren't representable as ordinary constraints, AbSolute would need a second, domain-specific data structure sitting *outside* the abstract-domain framework — exactly the kind of CP-specific plumbing that the whole chapter is trying to eliminate by recasting everything in AI's vocabulary.

## Abstraction and consistency via Apron transfer functions

**Abstraction.** Given the environment and the domain constraints, AbSolute picks a manager (`Oct.manager_alloc()` for octagons, a `Polka` manager for polyhedra, a box manager for intervals) and calls `Abstract1.of_lincons_array man vars doms` to build the initial abstract element $D^\sharp$ — this is $\alpha$ applied to the initial box of declared bounds, using whichever domain the manager encodes.

**Consistency.** The propagation step reuses Apron's *test transfer function* for each constraint — Apron already provides this because static analyzers need to narrow an abstract state along a branch condition (`if (x > 0) ...`), which is formally the same operation as narrowing a domain along a CSP constraint. Internally each domain picks its own algorithm: the interval domain uses HC4-Revise (the same tree-walking, two-pass propagator from Chapter 2); domains without a native non-linear-constraint algorithm fall back to **linearization** (below). Since Apron has no built-in notion of "propagate to a fixpoint, but give up after a while" — that's a CP concern, not a static-analysis one — AbSolute wraps repeated calls to the test function in its own local-iteration loop, capped at a fixed maximum (default **3**) rather than run to an actual fixpoint:

```ocaml
let abs = consistency man abs cons max_iter;;   (* max_iter defaults to 3 *)
```

The book gives a sharp example (6.2.4) of *why* this cap matters: for $v_1 = v_2$ and $v_1 = \tfrac{1}{2}v_2$ on $[-4,4]^2$ (unique solution $v_1=v_2=0$), naive alternating propagation halves the domain on every call and *never terminates* — $[-4,4]\to[-2,2]\to[-1,1]\to\cdots$ converges to the fixpoint only in the limit. Ibex handles this with a relative heuristic (stop once an iteration shrinks the domain by less than 10%); AbSolute instead hard-caps the iteration count. Both are pragmatic escapes from the same problem: **consistency computation and termination are in tension**, and neither solver tries to reach the true fixpoint on every node.

This is a genuinely load-bearing implementation decision for anyone building a Horn-clause / invariant-generation engine on abstract interpretation: a propagation loop that's allowed to run to a literal fixpoint can diverge in exactly the geometric-shrink pattern above, so any practical implementation needs *some* early-exit discipline — an iteration cap (AbSolute's choice), a relative-progress threshold (Ibex's), or (the more principled AI answer, not used here) a widening operator.

## Linearization of non-linear constraints

Not every abstract domain has a native way to propagate a non-linear constraint like $v_1 \times v_2 \geq 3.5$. When none of a domain's own methods can handle a non-linear term, AbSolute falls back to an algorithm from [Miné 2004]: pick a subset of the variables occurring non-linearly, and **replace each one by its current interval**, turning the term into a *quasi-linear* constraint — a linear constraint whose coefficients are themselves intervals rather than scalars. Concretely, for $C_2 : v_1 v_2 \geq 3.5$ with $D_1 = D_2 = [\![1,5]\!]$, replacing $v_1$ by its domain and $v_2$ by its domain gives two quasi-linear constraints:

$$
C_{2.1}: [\![1,5]\!]\, v_2 \geq 3.5 \qquad C_{2.2}: [\![1,5]\!]\, v_1 \geq 3.5
$$

An interval coefficient still isn't something a linear solver's Simplex-style machinery wants, so the last step collapses each interval $[a,b]$ to its midpoint $(a+b)/2$ and moves the resulting slack $[(a-b)/2,(b-a)/2]$ into the constant term:

$$
C_{2.1}': 3v_2 + [\![-2,2]\!] \geq 3.5 \qquad C_{2.2}': 3v_1 + [\![-2,2]\!] \geq 3.5
$$

which is now genuinely linear and can be handed to the ordinary linear-constraint transfer functions. (An alternative from [Borradaile & Van Hentenryck 2005] instead rounds each interval to whichever bound — upper or lower — keeps the constraint tightest, rather than always taking the midpoint.) This is exactly the same move a Horn-clause-based invariant generator makes when it needs to feed a non-linear guard into a linear abstract domain (octagons, polyhedra): abstract the non-linear term itself into an interval-valued coefficient, accepting a controlled loss of precision to stay inside a domain with efficient transfer functions.

```python
# Illustrative sketch of the linearization step (not the book's actual algorithm,
# just making the arithmetic concrete): replace v1 in "v1 * v2 >= 3.5" by its
# current domain interval, then collapse that interval to midpoint + slack.
def linearize_product(coeff_domain, other_var_coeff, rhs):
    lo, hi = coeff_domain            # e.g. (1, 5) for v1's current domain
    mid = (lo + hi) / 2
    slack = ((hi - lo) / 2, (lo - hi) / 2)   # added to the constant term
    return f"{mid}*{other_var_coeff} + [{slack[1]}, {slack[0]}] >= {rhs}"
```

## The naive splitting operator

Where the octagonal solver of Chapter 5 defines a *domain-specific* splitting operator $\oplus_o$ that cuts along one of the finitely many octagon-native "unit binary expressions" (Definition 4.3.1), AbSolute deliberately does the opposite: it implements one splitting operator that works identically for **every** domain and **every** variable type. It computes the smallest enclosing box of the current abstract element, finds the dimension with the largest extent, and cuts that dimension in half — this is exactly $\oplus_h$ from Example 6.1.11, applied even when the underlying element is an octagon or a polyhedron:

```ocaml
let list_abs = split man abs vars;;
(* returns a list of abstract domains whose abstract union (⊔) is equivalent
   to the starting element `abs` — condition (3) of Definition 6.1.5 *)
```

The book is candid that this is a real limitation, and Figure 6.2 makes the cost visible: applied to an octagon, the naive box-bisection ignores the octagon's diagonal ($\pm v_i \pm v_j$) structure entirely, producing two much looser pieces than the octagon-aware $\oplus_o$ would. In other words, AbSolute buys domain-genericity (one operator, works everywhere) at the price of precision-per-split (it can't exploit relational structure that a domain-specific splitter would use).

**What breaks without a compatible split.** Definition 6.1.5's three conditions on $\oplus$ (finite, contracting, exact under $\gamma$) aren't decoration — condition 2 ($e_i \sqsubseteq^\sharp e$) together with Definition 6.1.7's compatibility-with-$\tau$ condition is exactly what powers the König's-lemma termination proof of Proposition 6.1.1. A splitting operator that isn't provably contracting for the domain's own size function $\tau$ can produce an infinite search tree even though every individual step "looks like progress." AbSolute's box-bisection split is compatible with each domain's $\tau$ (the book states this for $\tau_a,\tau_b,\tau_h,\tau_o,\tau_p,\tau_m$ collectively) precisely *because* it's defined via a concrete numeric shrink, not a syntactic one — so genericity doesn't cost correctness, only precision.

## Handling the polyhedron abstract domain in practice

The polyhedron domain is the one place where AbSolute's uniform machinery needs a domain-specific patch. Two properties of polyhedra make them behave badly inside the generic loop:

1. **Consistency isn't always reductive.** Propagating a constraint can *add* a new facet to the polyhedron rather than shrink it — and the added facet can be redundant. The book's own example: for the square $\{v_1\geq1, v_1\leq5, v_2\geq1, v_2\leq5\}$, consistency might add $v_2 - 5v_1 \leq 0$, a linear inequality that's already implied by every point in the square (it's always true there) — a wasted, non-tightening addition.
2. Only the *splitting* operator is guaranteed reductive for polyhedra — consistency alone can grow the representation.

Rather than repeatedly checking facet counts after every operation (expensive), AbSolute imposes a cheaper proxy: it caps the **coefficient magnitude** allowed in any newly added linear expression, arbitrarily set to 20. Once a candidate facet's coefficients exceed that bound, it's rejected — no need to re-derive the polyhedron's full facet count from scratch. The author is explicit that this was not tuned exhaustively, and that the chosen bound is "not limiting enough" on some of their own benchmarks — an honest admission that this is a practical stopgap, not a principled solution. (The book's medium-term perspective — better splitting/consistency for polyhedra and other relational domains — names this directly as unfinished work.)

This is a useful cautionary data point for anyone building a Horn-clause-style CHC solver over polyhedra (a very standard invariant domain for that setting): representation blow-up in the polyhedron domain is a real, recurring engineering problem, not a corner case, and needs an explicit containment strategy from day one.

## Experimental results on continuous and mixed benchmarks

AbSolute was benchmarked in two very different regimes, because they stress different parts of the claim.

**Continuous problems (COCONUT benchmark, real variables only).** Here AbSolute is directly comparable to a mature interval CP solver, Ibex, and to Ibex extended with octagons (from Chapter 5). Selected results (CPU seconds):

| problem | vars | type | Ibex (intervals) — all sols | AbSolute (intervals) — all sols | Ibex (intervals) — 1st sol | AbSolute (intervals) — 1st sol |
|---|---|---|---|---|---|---|
| b | 4 | = | 0.02 | 0.10 | 0.009 | 0.018 |
| nbody5.1 | 6 | = | 95.99 | 1538.25 | 32.85 | 708.47 |
| ipp | 8 | = | 38.83 | 39.24 | 0.66 | 9.64 |
| brent-10 | 10 | = | 21.58 | 263.86 | 7.96 | 4.57 |
| KinematicPair | 2 | ≤ | 59.04 | 23.14 | 0.013 | 0.018 |
| biggsc4 | 4 | ≤ | 800.91 | 414.94 | 0.011 | 0.022 |
| o32 | 5 | ≤ | 27.36 | 22.66 | 0.045 | 0.156 |

The pattern the book highlights: AbSolute is **competitive on average**, tends to be **slower on equality-heavy problems** and **faster (sometimes much faster, e.g. `biggsc4`, `KinematicPair`) on inequality-heavy problems**. The proposed explanation isn't the constraint type per se but a structural ratio: how many of a variable's occurrences are actually touched by a given propagation step, versus how many constraints AbSolute re-propagates regardless. Because AbSolute (Remark 6.2.2) propagates *all* constraints at every local iteration — unlike classical CP solvers, which use dependency tracking (e.g. AC-5-style: only re-propagate constraints whose variables actually changed) — problems where a variable appears in only a few of many constraints pay for a lot of wasted propagation work. `brent-10` (10 vars, 10 constraints, each variable in at most 3) is the book's own worked explanation for why that problem times out (≥ 1h) under octagons.

**Mixed problems (MinLPLib, genuinely integer-and-real).** No standard CP benchmark of mixed problems exists, because classical CP solvers largely can't represent them at all — this is the regime where AbSolute's design actually earns its keep rather than merely matching an existing tool:

| problem | int vars | real vars | type | $M^\sharp$ (mixed box) | $O^\sharp$ (octagon) | $P^\sharp$ (polyhedron) |
|---|---|---|---|---|---|---|
| gear4 | 4 | 2 | = | 0.017 | 0.048 | 0.415 |
| st_miqp5 | 2 | 5 | ≤ | 2.636 | 3.636 | ≥ 1h |
| ex1263 | 72 | 20 | =, ≤ | 473.933 | ≥ 1h | ≥ 1h |
| antennes_4_3 | 6 | 2 | ≤ | 520.766 | 1562.335 | ≥ 1h |

The consistent finding: **intervals (the mixed box domain) outperform octagons and polyhedra** on mixed problems — the opposite of what you'd hope, given that relational domains are supposed to be the whole point of this exercise. The book's own diagnosis is that current propagation and splitting strategies simply aren't yet sophisticated enough to *exploit* the relational information octagons/polyhedra carry (echoing Chapter 5's finding that a carefully designed splitting operator, not just a richer domain, is what actually made octagons pay off there). The takeaway is not "relational domains don't help mixed solving" but "AbSolute's current naive splitter leaves that value on the table" — directly motivating the chapter's closing perspective: import Chapter 5's octagon-aware splitting ideas back into AbSolute.

Despite the timeouts, the headline result stands on its own: **AbSolute can represent and solve problems no classical CP solver in this comparison could pose in the first place**, because the mixed integer/real environment is native to the framework rather than bolted on.

## Where this leads

AbSolute closes the loop the whole book opens: Chapters 3–5 import AI's abstract domains *into* CP (illustrated by the octagon domain and its Ibex-based solver); Chapter 6 goes the other way and re-expresses CP's solving process *as* an AI computation, then builds a literal solver out of that reformulation. The chapter's own admission — that AbSolute is competitive but not yet exploiting relational precision, propagates too eagerly, and needs a better splitting operator — is exactly the punch list the book's Chapter 7 perspectives section opens with (better heuristics, reduced products between integer and real domains, eventually linking CP's under-approximations to AI's widening operator).

For the standing project of building a Rust-based dependent/refinement-type checker with an embedded CSP-and-abstract-interpretation kernel, this section is close to a blueprint, not just an analogy:

- The **manager/transfer-function pattern** (one uniform interface — abstraction, test/consistency, split, size — implemented once per concrete domain: box, octagon, polyhedron) is precisely the shape you want for a Rust trait backing your own invariant-generation engine, letting the same Hoare-triple / Horn-clause propagation loop run unmodified over whichever abstract domain best fits a given refinement (intervals for simple bounds, polyhedra for linear relational invariants).
- The **bounded local-iteration consistency loop** (cap at $k$ iterations rather than chase a literal fixpoint) is a concrete answer to a problem your own CHC solver will hit immediately: propagation over a genuinely relational domain does not always converge quickly, and a principled early-exit (iteration cap, relative-progress threshold, or widening) is not optional polish — it is what keeps invariant inference from hanging on adversarial constraint shapes like AbSolute's $v_1 = v_2, v_1 = \tfrac12 v_2$ example.
- **Linearization of non-linear constraints** is the direct precedent for what your own CSP kernel must do when a refinement-type guard is non-linear (a common case for anything beyond simple bound reasoning) but the invariant domain underneath (octagons, polyhedra) is linear-only.
- The **split/choice operator pair** (Definitions 6.1.5–6.1.6) is the general schema for how a CSP-based counterexample search interacts with an abstract-interpretation-based soundness proof inside one solver: splitting refines toward concrete counterexamples (CSP's job — proving *presence* of bugs), while consistency/propagation maintains the over-approximation (AI's job — proving *absence*). AbSolute's Algorithm 6.1 is a working instance of exactly the CEGAR-adjacent loop (refine, propagate, discard/keep/split) that a CEGAR-style refinement-type checker would run internally.
