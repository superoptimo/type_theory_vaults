---
title: "Soft Constraints and Preferences"
source: "Handbook of Constraint Programming (Elsevier, 2006)"
chapter: "Chapter 9 — Soft Constraints (Meseguer, Rossi, Schiex)"
pages: "281–328"
tags: [constraint-programming, soft-constraints, semiring, valued-csp, fuzzy-csp, weighted-csp, csp-optimization, abstract-interpretation]
---

# Soft Constraints and Preferences

[[book-guidelines|↩ Back to guidelines]]

## Why hard constraints aren't enough

A classical CSP is a yes/no machine. You hand it a set of variables, domains, and relations, and it hands back either a complete assignment satisfying every relation, or a flat "unsatisfiable." That binary outcome is exactly the problem in practice. Real timetabling, rostering, and configuration problems are almost always **over-constrained**: if you write down every desideratum as a hard constraint, the conjunction is frequently unsatisfiable, and the classical framework gives you no notion of "close." It also gives you no way to rank two assignments that both happen to satisfy everything — they're just "equally good," even when one is obviously better.

The book's own example is a university timetable. Classroom capacity, opening hours, and "one teacher can't be in two rooms at once" are genuinely hard — violating them produces nonsense. But "the teacher would rather not teach on Fridays" and "prefer smaller rooms when possible" are **preferences**: things you want satisfied as much as possible, not things whose violation invalidates the solution. Model them as hard constraints and you'll frequently get UNSAT for problems that obviously have a good, workable answer. Soft constraints are the fix: replace the boolean "satisfied / violated" verdict with a *graded* one, drawn from some ordered scale, and replace "find an assignment satisfying everything" with "find an assignment that is optimal (or Pareto-optimal) with respect to that scale."

This distinction should feel familiar from a different direction: it's the same move abstract interpretation makes when it replaces "does this program have property $P$" with "what is the most precise fact I can state that's still sound." Soft constraints replace a two-valued satisfaction relation with a *lattice-valued* one — and, as we'll see, the algebraic structure the chapter builds to do this (the c-semiring) is essentially a bounded join-semilattice with a compatible combination operator, i.e. the same shape of object that underlies abstract domains. Keep that parallel in mind; it resurfaces at the end.

## Part 1 — Specific frameworks: three ways to grade an assignment

The chapter's structure is deliberately historical: first a handful of *specific* frameworks were invented independently, each committing to one particular scale and one particular way of combining scores. Later, a common *generic* algebraic skeleton was extracted from all of them. We'll follow that order because it's pedagogically the right one — the abstraction only makes sense once you've seen several instances of the pattern it's abstracting.

### Fuzzy, possibilistic, and lexicographic constraints

**[[Applications-Configuration-Networks-and-Bioinformatics#What breaks without it|What breaks without it]].** Preferences aren't binary, but they also aren't naturally additive — "prefer no Friday classes" isn't a cost you pay in dollars, it's a degree of acceptability. Fuzzy set theory already had a formalism for graded membership; the chapter's first move is to reuse it directly.

A classical relation $R_V$ over a scope $V$ is just a set of allowed tuples. A **fuzzy relation** replaces set membership with a graded **membership function**

$$\mu_{R_V} : \prod_{x_j \in V} D_j \to [0,1]$$

$\mu_{R_V}(t) = 1$ means $t$ fully satisfies the constraint; $\mu_{R_V}(t) = 0$ means it's completely forbidden; anything in between is partial satisfaction, and $\mu_{R_V}(t) < \mu_{R_V}(t')$ means $t'$ is strictly preferred to $t$ for that constraint.

Multiple fuzzy constraints are combined **conjunctively**, and the combination operator is $\min$:

$$\mu_{R_V \cup W}(t) = \min\bigl(\mu_{R_V}(t[V]),\, \mu_{R_W}(t[W])\bigr)$$

so the overall preference of a complete assignment $t$ is the worst score among all constraints:

$$\mu_t = \min_{R_V \in C} \mu_{R_V}(t[V])$$

An **optimal solution** maximizes this min — a max-min optimization. The intuition is risk-averse: you judge a plan by its worst feature, which is exactly right for safety-critical reasoning (you don't average away a critical flaw with several nice-to-haves), but it has a real weakness — two assignments with the same worst score are ranked equal even if one dominates elsewhere. The book's own example: constraints scored $(0.5, 1.0)$ and $(0.5, 0.5)$ both have $\min = 0.5$, yet the first is obviously better. **Fuzzy lexicographic constraints** patch this by comparing the *sorted* vectors of all preference values lexicographically rather than collapsing to a single scalar — a strictly finer-grained order that still degrades gracefully to the plain fuzzy order when the minimum values differ.

**Possibilistic constraints** are the dual formulation: priorities attached to constraints, minimizing the priority of the *most important* violated one (min-max instead of max-min). Same expressive power, inverted scale.

Complexity note worth internalizing early: fuzzy CSP strictly generalizes classical CSP (binary membership degrees recover it exactly), so deciding "is the best satisfaction degree above threshold $\theta$" is NP-complete, and finding an optimal solution is NP-hard. Soft constraints don't buy you tractability for free — they buy you *expressiveness*, and tractability has to be earned separately (Section 9.6.3 covers this).

**Rust grounding.** The natural encoding of "a graded relation" is a closure or trait method from a tuple of assigned values to a score:

```rust
trait SoftConstraint<Val> {
    /// Score in [0.0, 1.0] for a complete assignment restricted to this
    /// constraint's scope. 1.0 = fully satisfied, 0.0 = forbidden.
    fn score(&self, assignment: &[Val]) -> f64;
    fn scope(&self) -> &[usize]; // variable indices
}

fn fuzzy_combine(scores: impl Iterator<Item = f64>) -> f64 {
    scores.fold(1.0, f64::min) // conjunctive combination = min
}
```

This is already the shape of the generic framework to come — `score` returning into an ordered set, and a combinator that's associative, commutative, and (here) idempotent. Idempotency of $\min$ ($\min(a,a) = a$) is not incidental; it's the load-bearing property that makes fuzzy CSP uniquely well-behaved among soft frameworks, as we'll see in Part 3.

### Weighted constraints

**What breaks without it.** Fuzzy's $[0,1]$ satisfaction scale is the wrong shape for problems that are naturally about *cost* — routing (minimize toll + fuel), procurement (minimize total price), scheduling (minimize total tardiness penalty). You don't want "the worst violation dominates," you want violations to *add up*.

A **weighted constraint** $\langle c, w \rangle$ is a classical constraint $c$ plus a weight (penalty) $w$, paid in full when $c$ is violated. The cost of a complete assignment is the **sum** of the weights of every constraint it violates; an optimal solution minimizes total cost. Setting every weight to 1 recovers **MAX-CSP** (minimize the count of violated constraints); restricting further to boolean clauses recovers **MAX-SAT**.

The refined version, **$k$-weighted constraints**, caps costs at a threshold $k$ (beyond which a solution is simply unacceptable) using **bounded sum**:

$$a +_k b = \min(a+b,\, k)$$

A $k$-weighted constraint $f_V : \prod_{x_j \in V} D_j \to [0,k]$; total cost is the bounded sum over all constraints; a solution needs cost $< k$; classical CSP is recovered as the special case where only costs $0$ and $k$ appear. This capping matters practically — without it, a single catastrophic violation could be swamped by many small ones in a sum, which is exactly the failure mode "hard constraints disguised as very heavy soft ones" is meant to prevent.

A closely related variant is the **probabilistic constraint**: each constraint carries a probability $p_R$ that it's actually present in the (uncertain) real-world scenario; independence lets you multiply $(1-p_R)$ over all violated constraints to get the probability the assignment is actually feasible. Since $-\log$ turns products into sums, probabilistic constraints reduce to weighted ones in polynomial time — a first hint of the theme in Part 3: *these frameworks are not independent inventions, they're points in one design space.*

**Why weighted constraints matter most for your compiler project:** this is the shape you want for a **counterexample-search cost function**. If you're using a CSP kernel to search for concrete inputs violating a refinement-type invariant, "how far is this candidate from satisfying all the guard constraints" is naturally a weighted-CSP cost — sum the violated constraints' penalties, treat zero cost as "found a genuine counterexample," and use the cost as a branch-and-bound guide exactly as Section 9.5 describes below. This is also precisely the algebra behind Weighted MAX-SMT, which several SMT-based verification tools use to rank candidate models or to do soft-clause-guided unsat-core minimization.

## Part 2 — Generic frameworks: one algebra to rule them all

Look back at the two frameworks above and the pattern is obvious: each constraint maps assignments to a value on some ordered scale; those values combine via some operator; an optimal solution maximizes (or minimizes) the combined value. Once you see that shape three or four times, the right move is to axiomatize it once and derive both frameworks — and every future one — as instances. That's what Section 9.3 does, via two (essentially equivalent) algebraic structures.

### C-semirings

A **c-semiring** is a 5-tuple $\langle E, +_s, \times_s, 0, 1 \rangle$ where:

- $E$ is the set of preference/satisfaction levels, with $0, 1 \in E$.
- $+_s$ is closed, associative, commutative, and **idempotent**, with $0$ neutral and $1$ absorbing. Idempotency is what makes $+_s$ induce a genuine partial order (a lattice, in fact): define $b <_s a$ to mean $a +_s b = b$ ("$b$ is at least as good as $a$"). $a +_s b$ is the least upper bound of $a$ and $b$ in this order.
- $\times_s$ is closed, associative, and commutative, with $0$ absorbing and $1$ neutral — this is the constraint-combination operator.
- $\times_s$ distributes over $+_s$.

The semantic content behind the axioms: $0$ is "totally forbidden," and it must absorb under $\times_s$ because combining a totally-violated constraint with anything else should still be totally forbidden. $1$ is "fully satisfied," and it must be neutral under $\times_s$ so that combining a trivially-satisfied constraint with a partially-satisfied one changes nothing. The **consistency level** of a complete assignment $t$ is

$$val_s(t) = \bigtimes_{f_V \in C} f_V(t[V])$$

and an optimal solution has a consistency level not strictly dominated by any other's under $<_s$. Because $<_s$ is only a *partial* order in general, there can be several, mutually incomparable optimal solutions — this is deliberate: the book's motivating example is multi-criteria optimization (minimize cost *and* time *and* maximize scenery, all at once), where "one route is better on cost, the other on time" genuinely has no single right answer. A c-semiring is **idempotent** when $\times_s$ is *also* idempotent ($a \times_s a = a$); then $a \times_s b$ is the *greatest lower bound* in the same lattice. `min`, `max`, and `∩` are all idempotent operators; `+` and `×` (real number multiplication) are not.

Solving a semiring CN is NP-hard in general (it strictly generalizes classical CSP), and deciding whether a network's consistency level exceeds a given threshold is NP-complete whenever $\times_s$ and $+_s$ are polynomial to evaluate.

**This is, almost verbatim, a bounded lattice with a compatible monoid action** — precisely the algebraic shape of an abstract domain in abstract interpretation. A Galois-connected abstract domain has a join ($\sqcup$, matching $+_s$), a top/bottom, and typically some transfer/meet operator that composes soundly with the join — matching $\times_s$'s distributivity requirement. When you eventually design the CSP kernel's domain-propagation machinery, parametrizing your propagators over an abstract `CSemiring`-like trait — rather than hardcoding boolean satisfiability — is exactly how you'd support interval domains, weighted cost domains, and probabilistic domains through one propagation engine.

```rust
trait CSemiring: Clone + PartialEq {
    fn zero() -> Self;   // 0: totally forbidden / worst
    fn one() -> Self;    // 1: fully satisfied / best
    fn combine(&self, other: &Self) -> Self;   // ×s
    fn choose_better(&self, other: &Self) -> Self; // +s (join)
    fn dominates(&self, other: &Self) -> bool {
        // b <=s a  iff  a +s b == b
        &self.choose_better(other) == other
    }
}

// Fuzzy: E = [0,1], ×s = min, +s = max
struct Fuzzy(f64);
impl CSemiring for Fuzzy {
    fn zero() -> Self { Fuzzy(0.0) }
    fn one() -> Self { Fuzzy(1.0) }
    fn combine(&self, o: &Self) -> Self { Fuzzy(self.0.min(o.0)) }
    fn choose_better(&self, o: &Self) -> Self { Fuzzy(self.0.max(o.0)) }
}

// k-weighted: E = {0,...,k}, ×s = +k (bounded sum), +s = min (lower cost wins)
struct Weighted { cost: u32, k: u32 }
impl CSemiring for Weighted {
    fn zero() -> Self { Weighted { cost: 0, k: u32::MAX } } // 0 = k = worst
    fn one() -> Self { Weighted { cost: 0, k: 0 } }         // 1 = 0 = best
    fn combine(&self, o: &Self) -> Self {
        Weighted { cost: (self.cost + o.cost).min(self.k), k: self.k }
    }
    fn choose_better(&self, o: &Self) -> Self {
        if self.cost <= o.cost { self.clone() } else { o.clone() }
    }
}
```

(Table 9.2 in the chapter tabulates classical, fuzzy, $k$-weighted, and probabilistic constraints as four instantiations of exactly this signature — $E$, $\times_s$, $+_s$ — which is the strongest evidence that the abstraction is the right one, not an arbitrary generalization.)

**Lean grounding.** The c-semiring axioms map onto a structure Lean/mathlib already has a name for: a **bounded distributive lattice** paired with a commutative monoid whose multiplication distributes over the lattice join — which is precisely the algebraic content of an *ordered semiring with idempotent addition*. Encoding it directly:

```lean
structure CSemiring (E : Type) where
  add    : E → E → E   -- +s
  mul    : E → E → E   -- ×s
  zero   : E           -- 0 : worst
  one    : E           -- 1 : best
  add_comm     : ∀ a b, add a b = add b a
  add_assoc    : ∀ a b c, add (add a b) c = add a (add b c)
  add_idem     : ∀ a, add a a = a        -- induces the lattice order
  add_zero     : ∀ a, add a zero = a
  add_one      : ∀ a, add a one = one
  mul_comm     : ∀ a b, mul a b = mul b a
  mul_assoc    : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_zero     : ∀ a, mul a zero = zero
  mul_one      : ∀ a, mul a one = a
  distrib      : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)

def CSemiring.le {E} (S : CSemiring E) (a b : E) : Prop := S.add a b = b
```

`add_idem` is precisely what forces `le` to be a genuine (reflexive, antisymmetric, transitive) partial order rather than a preorder — the same role idempotency plays for `⊔` in any Lean formalization of a join-semilattice or an abstract domain's ordering.

### Valued constraints

**Valued constraints** are the "violation-scored, totally-ordered" twin of c-semirings: a **valuation structure** $\langle E, \oplus, \preceq_v, \bot, \top \rangle$ where $E$ is *totally* ordered (not just a lattice), $\bot$/$\top$ are min/max violation, and $\oplus$ (playing the role of $\times_s$) is commutative, associative, has $\bot$ as neutral and $\top$ as absorbing, and satisfies **monotonicity**:

$$a \preceq_v b \implies (a \oplus c) \preceq_v (b \oplus c)$$

Monotonicity says "increasing a violation can't decrease the total violation" — a weaker, easier-to-justify version of the distributivity axiom in c-semirings (Table 9.1 gives the exact dictionary: $\oplus \leftrightarrow \times_s$, $\min_v \leftrightarrow +_s$, $\preceq_v \leftrightarrow <_s$, $\top \leftrightarrow 0$, $\bot \leftrightarrow 1$). The chapter proves valuation structures and *totally ordered* c-semirings are formally interconvertible — the same expressive power, different sign convention (satisfaction vs. violation). Because the algorithms in Sections 9.5–9.7 are almost all originally stated in violation/cost terms (branch-and-bound minimizing an upper bound, inference producing lower bounds), the chapter — and this article — mostly works in the valued formalism from here on, with the semiring framework reserved for statements that need partial orders (multi-criteria search).

### Combination and projection — the two operations everything else is built from

Two operations recur throughout the rest of the chapter, and it's worth internalizing them before the search/inference machinery, because both Section 9.5 (search) and Section 9.6 (inference) are just different strategies for applying them.

**Combination** merges two constraints into one over the union of their scopes:

$$(f_V \Join f'_{V'})(t) = f_V(t[V]) \times_s f'_{V'}(t[V'])$$

**Projection** eliminates variables from a constraint by aggregating (via $+_s$) over all the values they could take:

$$f_V[W](t) = \sum_{\substack{t' \\ t'[W]=t}}{}^{\!+_s} f_V(t')$$

— i.e., "the best score achievable by any completion consistent with $t$ on the remaining variables $W$." When $W = V \setminus \{x\}$ this is called *projecting out* $x$, written $f_V[-x]$.

These are exactly relational join and marginalization, generalized from boolean relations to semiring-valued ones — the same operations that underlie relational-algebra query optimization and, not coincidentally, sum-product/max-product message passing in graphical models. Combining *every* constraint in the network and projecting onto the empty scope gives you a single zero-arity constraint whose value **is** the network's overall consistency level — this is the formal definition of "solving the CSP" in this algebra, and bucket elimination (Part 3 below) is nothing more than doing this combine-then-project pipeline cleverly, one variable at a time, instead of all at once.

The **micro-structure** of a soft CN is the natural visualization: one vertex per (variable, value) pair, one labelled hyperedge per non-trivial tuple of a constraint, label = the constraint's score on that tuple. It generalizes the classical micro-structure graph (where edges just mark *compatible* pairs) by additionally carrying the preference/cost.

One more subtlety worth flagging because it will matter for tractability results later: $\times_s$ is always monotonic, but when it's **strictly** monotonic ($a \succ_s c$, $b \neq 0 \Rightarrow a \times_s b \succ_s c \times_s b$), the framework gains a nice rationality property — dominating on one constraint while tying everywhere else guarantees overall domination. But strict monotonicity is *incompatible with idempotency* once $|E| > 2$. You cannot have both "min-style worst-case dominance" (fuzzy) and "every improvement strictly counts" (weighted) in the same operator. This isn't a limitation of the formalism — it's a real fact about preference aggregation, and it's the deep reason fuzzy and weighted CSP behave so differently under inference, which is the next section's central drama.

## Part 3 — Relations among the frameworks

### Semiring ↔ valued: notational duals

Already covered above — Table 9.1's translation dictionary. The two frameworks prove the *same* theorems; the choice of which to use is a presentation convenience (maximize satisfaction vs. minimize violation), except that only totally-ordered c-semirings have a valued-constraint counterpart. Multi-criteria (partially-ordered) reasoning genuinely needs the semiring framework.

### Fuzzy CSP is special: the unique idempotent case

Here's the payoff for having flagged idempotency earlier. **Fuzzy constraints are the only totally-ordered c-semiring instance whose combination operator ($\min$) is idempotent.** This single fact buys fuzzy CSP an entire toolbox that weighted/probabilistic CSP don't get for free:

Given a fuzzy CN and the finite set $F$ of all membership degrees actually used, you can build, for each threshold $\alpha \in F$, the classical CN $P^\alpha$ obtained by an **$\alpha$-cut**: keep exactly the tuples each fuzzy constraint scores $\geq \alpha$. As $\alpha$ increases, $P^\alpha$ gets strictly more restrictive. Let $\alpha^*$ be the largest $\alpha$ for which $P^\alpha$ is still classically satisfiable — then *the solutions of $P^{\alpha^*}$ are exactly the optimal solutions of the fuzzy CN*. Since satisfiability is monotone in $\alpha$, you can find $\alpha^*$ by **binary search** over the (at most $O(d^n)$, but typically far fewer distinct) membership degrees, needing only $O(\log|F|)$ calls to a classical CSP oracle. This is a genuinely powerful reduction: *any* tractable classical constraint language lifts directly to a tractable fuzzy constraint language via this decomposition (Section 9.6.3 makes this precise as "$\Gamma^{cut}$ tractable $\Rightarrow$ $\Gamma$ tractable").

Nothing like this works for weighted CSP, because $+$ isn't idempotent — there is no single threshold slice that captures "the optimal solution," since costs genuinely accumulate rather than saturate. This is also, not coincidentally, why local-consistency enforcement can *loop forever* on weighted networks but always terminates on fuzzy ones (Part 4 below) — idempotency is precisely the property that guarantees "pushing information around doesn't create new information out of nothing."

### Other AI preference formalisms — where soft constraints sit in the wider landscape

The chapter situates soft constraints against several neighboring formalisms, which is useful for knowing when *not* to reach for this machinery:

- **Partial constraint satisfaction** — an earlier, less formalized attempt: relax the original CN via constraint-relaxation operations plus a distance metric, and search for the *nearest* consistent network. Historically important but not cleanly reducible to semiring/valued constraints.
- **Hierarchical [[Constraint-Logic-Programming|Constraint Logic Programming]] (HCLP)** — constraints get a *strength level* in a totally ordered hierarchy (hardest = classical hard constraints); solutions are compared using a lexicographic order over per-level combined "errors." Most concrete combining functions used in practice (weighted sum, weighted max, weighted sum-of-squares) reduce to valued/weighted CNs, but HCLP's *general* definition permits combining functions that violate monotonicity — so it's strictly more permissive (and less well-behaved) than the semiring axioms.
- **MaxSAT** — literally a special case: boolean weighted CSP with clause constraints.
- **Bayesian networks** — also a special case: semiring values in $[0,1]$, $\times_s$ = ordinary multiplication, constraints = conditional probability tables. Finding the Most Probable Explanation is exactly finding an optimal solution of this semiring CN.
- **CP-nets** — this is the most interesting comparison, because the relationship is genuinely **incomparable**, not a subset relation. CP-nets specify, per variable, a *conditional* total preference order over its domain given the values of "parent" variables, interpreted *ceteris paribus* ("all else equal, I prefer $y=w_1$ to $y=w_2$"). If you only care about the *set of optimal solutions*, a CP-net reduces to a classical CN (via one implication per preference statement) — so classical constraints are at least as expressive there. But if you care about the *entire solution ordering* (not just the optimum), the two frameworks diverge in opposite directions: **dominance testing** (deciding which of two assignments is preferred) is NP-complete for CP-nets but polynomial for soft CNs — so no polynomial reduction from CP-nets to soft CNs can exist (unless P=NP) while preserving the ordering. Conversely, CP-nets cannot represent *every* partial order soft CNs can (e.g. two single-flip-different solutions being incomparable is inexpressible in a CP-net), so no reduction exists in the other direction either. Two genuinely different preference languages, neither a special case of the other.
- **Constraint optimization variables** — any totally-ordered soft CN can be re-encoded as a classical CN with one extra variable $x_V$ per constraint (recording that constraint's semiring value) plus one global "aggregator" variable $x_c$ tied together by $\bigtimes_s x_V = x_c$; maximizing $x_c$ solves the soft CN. Useful as an implementation trick (lets you reuse an off-the-shelf classical solver's optimization primitives), at the cost of extra variables, higher-arity constraints, and a structurally modified problem — so it's a translation of convenience, not a free lunch.

## Part 4 — Search

Restricting to totally-ordered (valued) structures for tractable presentation, solving a soft CN is an **optimization** problem — strictly harder in general than classical satisfaction, since even after you've found *a* solution you don't know it's optimal without either exhausting the space or having a matching bound.

### Depth-first branch and bound

The workhorse. Explore the assignment tree depth-first, maintaining a **lower bound** $lb(t)$ (an underestimate of any completion's violation) and an **upper bound** $ub$ (the best violation found — or accepted — so far). Whenever $ub \preceq_v lb(t)$, the subtree under $t$ is provably useless and gets pruned.

```
Algorithm 9.1 — DFBB(t: partial assignment, ub: level) -> level
  if |t| == n: return lb(t)
  pick unassigned xi
  for a in Di:
      if lb(t ∪ {(xi,a)}) ≺v ub:
          ub ← min(ub, DFBB(t ∪ {(xi,a)}, ub))
  return ub
```

Time $O(d^n)$ worst case, space $O(nd)$ — same shape as classical [[Backtracking-Search|backtracking search]], but now the *quality* of the pruning depends entirely on how tight $lb$ and $ub$ are, which is why the chapter spends the rest of Section 9.5.1 on progressively stronger lower bounds:

- $lb_1(t) = \sum_{f_V \in C_P} f_V(t[V])$ — just sum the cost of constraints already fully assigned. Cheapest, weakest.
- $lb_2$ (used in **Partial Forward Checking**, PFC) additionally adds, for each unassigned variable $x_j$, the *minimum* inconsistency count it could contribute — a lookahead exactly analogous to classical forward checking's domain pruning, but summing costs instead of eliminating values.
- $lb_3$ (PFC-MRDAC) further folds in **directed arc-inconsistency counts** — cost contributions from constraints between two *unassigned* variables, using a fixed or reversible variable ordering to avoid double-counting.
- $lb_4$, from **Russian Doll Search** (RDS), is structurally different: instead of one search, run $n$ nested searches on suffix subproblems $\{x_i, \dots, x_n\}$ for $i = n, \dots, 1$, caching each subproblem's optimal cost $rds_i$ and reusing it as an *exact* (not estimated) contribution to the lower bound at earlier levels. Its refinement SRDS computes a per-value version of the same idea at the cost of more subsearches, and typically wins despite the extra work.

A practical note the chapter is careful to make: essentially all of these are subsumed by the **soft-local-consistency-based bounds** of Section 9.7.2 — they're presented mainly because they were historically first and the ideas (lookahead counts, cached subproblem optima) recur throughout the chapter in more sophisticated forms.

```python
# Illustrative sketch of DFBB with a pluggable lower bound — not load-bearing,
# just makes Algorithm 9.1's control flow concrete.
def dfbb(assignment, ub, variables, domains, lower_bound):
    if len(assignment) == len(variables):
        return lower_bound(assignment)  # = actual cost, fully assigned
    xi = next(v for v in variables if v not in assignment)
    for a in domains[xi]:
        candidate = {**assignment, xi: a}
        if lower_bound(candidate) < ub:
            ub = min(ub, dfbb(candidate, ub, variables, domains, lower_bound))
    return ub
```

### Local search and partially ordered semirings

Any classical local-search technique (Chapter 5 of the handbook — hill-climbing, tabu search, min-conflicts, simulated-annealing-style acceptance) directly optimizes the scalar function $\bigoplus_{f_V \in C} f_V(t[V])$; no reformulation needed beyond "the objective is now a semiring aggregate instead of a violation count." It gives up completeness (no optimality guarantee, no certificate of having exhausted the space) in exchange for far better scaling, and the chapter notes the natural symbiosis: run local search first as a cheap preprocessing pass to get a good initial $ub$ for DFBB, tightening its pruning from the very first node.

When the semiring is only **partially** ordered (true multi-criteria optimization), a single scalar optimum stops making sense — you instead have to track the whole Pareto frontier of non-dominated solutions found so far, and prune any partial assignment whose *best possible* level is dominated by an already-found complete solution. This is strictly more bookkeeping (sets of incomparable bounds instead of one scalar), but conceptually the same branch-and-bound skeleton.

## Part 5 — Inference

Search explores; inference **derives**. The classical notion — a constraint $c$ is *implied* by network $P$ if every solution of $P$ satisfies $c$, and can therefore be safely added ("redundant") — doesn't transplant cleanly to the soft case, because adding a new constraint generically *changes the distribution of costs/levels on solutions*, even when it doesn't change which solutions are optimal. The chapter replaces "redundant" with the more careful notion of **implication** via a constraint ordering:

$$f_V \sqsubseteq f'_W \iff \forall t,\ f'_W(t[W]) \preceq_v f_V(t[V])$$

("$f_V$ implies $f'_W$" — $f'_W$'s violation is never worse, so it adds no *new* information beyond what $f_V$ already guarantees.) Three distinct strategies follow from this, differing in how carefully they preserve equivalence:

1. **Saturate directly** — only sound when $\oplus$ is idempotent (fuzzy CSP): just add the implied constraint, the network stays equivalent.
2. **Replace and re-derive** — remove the source constraints, insert the implied one instead. Preserves the *optimum*, not full equivalence, in general.
3. **Add and extract** — add the implied constraint *and* subtract its contribution back out of the sources, using a difference operator $\ominus$. Preserves full equivalence, but requires the valuation structure to support subtraction (**fairness**, defined below).

Bucket/cluster-tree elimination use strategy 2 for *complete* inference; soft local consistency mostly uses strategy 3 for cheaper, *incomplete* inference. Mini-bucket elimination deliberately breaks strategy 2's guarantees to save memory, producing a *lower bound* instead of the exact optimum.

### Complete inference: bucket elimination

**Bucket elimination (BE)** is the direct soft-CSP generalization of classical adaptive consistency (Chapter 3/7's algorithm), and it computes the *entire* optimal solution set, not just one witness.

Fix a variable ordering $o = x_1, \dots, x_n$. The **bucket** $B_i$ of $x_i$ is the set of all constraints whose highest-indexed variable (under $o$) is $x_i$. To *eliminate* $x_i$: combine every constraint in $B_i$ and project $x_i$ out —

$$g_i = \Bigl(\bigjoin_{f \in B_i} f\Bigr)[-x_i]$$

— then delete $x_i$ and replace $B_i$ with the single new constraint $g_i$. Because combination and projection exactly conserve the network's optimal level (that's what "$g_i$ compensates for the absence of $B_i$" means formally), doing this once for every variable, from last to first, collapses the whole network to a single zero-arity constraint whose value **is** the optimal level. A second forward pass (first variable to last, reusing the stored $g_i$'s) reconstructs an actual optimal assignment.

$$\text{Time: } O\bigl(n(2d)^{w^*+1}\bigr) \qquad \text{Space: } O\bigl(n d^{w^*}\bigr)$$

where $w^*$ is the **induced width** of the ordering: process the primal constraint graph's nodes from last to first, connecting each node's earlier-in-$o$ neighbors into a clique as you go (the *induced graph*), and $w^*(o)$ is the max clique size minus one; $w^*$ (the graph's induced width) minimizes over orderings. This is *exactly* the treewidth of the constraint hypergraph, and its exponential cost is a real structural fact, not an artifact of the algorithm — bucket elimination is essentially dynamic programming over a tree decomposition, and $w^*$ measures how far the graph is from being a tree ($w^*=1$).

**Cluster-tree elimination (CTE)** generalizes this to arbitrary tree decompositions $\langle T, \chi, \psi \rangle$ (not just the specific "bucket tree" BE implicitly builds), passing **messages** along tree edges — combine everything local to a node plus all incoming messages except from the target, project onto the separator, send. BE-on-the-bucket-tree is the special two-phase (leaves→root, then root→leaves) case, called **BTE**. Complexity is stated in terms of **tree-width** $tw$ and **separator size** $s$: $O(\deg(r+N)d^{tw})$ time, $O(Nd^s)$ space.

This should look extremely familiar if you've done dataflow analysis: bucket/cluster-tree elimination *is* a fixpoint computation over a tree decomposition, propagating aggregated information along edges until every node holds the marginal answer for its subproblem. It's the direct algorithmic ancestor of tree-decomposition-based abstract interpretation and of message-passing inference in graphical models (sum-product/max-product), just instantiated at the "generic semiring" level rather than a specific probability or interval domain.

### Incomplete inference: trading optimality for memory

BE's Achilles' heel is the arity — hence size — of intermediate constraints $g_i$, which can blow up even when the *final* answer is small. **Mini-bucket elimination MBE($z$)** caps this by partitioning each bucket $B_i$ into mini-buckets $B_i^1, \dots, B_i^m$, each bounded to $\leq z$ variables, and eliminating each mini-bucket separately:

$$g_i^j = \Bigl(\bigjoin_{f \in B_i^j} f\Bigr)[-x_i]$$

Because $\bigoplus_j g_i^j \preceq_v \bigl(\bigjoin_{f \in B_i} f\bigr)[-x_i]$ (splitting the join before projecting can only lose information, never gain it), MBE($z$) computes a valid **lower bound**, not the exact optimum — a controllable exactness/memory trade parametrized by $z$. **MCTE($z$)** is the identical idea applied to cluster-tree elimination's messages.

### Soft local consistency: the idempotency trap

**This is the section where the idempotent/non-idempotent split from Part 3 stops being an abstract observation and becomes an operational hazard.**

The obvious generalization of classical arc consistency — "$x_i$ is arc consistent w.r.t. $f_{ij}$ iff $\forall a \in D_i,\ f_i \sqsubseteq (f_{ij} \Join f_j)[x_i]$," enforced by iteratively tightening $f_i \leftarrow f_i \Join (f_{ij} \Join f_j)[x_i]$ until quiescence — is proven to **terminate and produce a unique equivalent network whenever $\oplus$ is idempotent**. Fuzzy CSP again gets this for free.

But for non-idempotent structures (weighted CSP included), naively applying this rule **can loop forever**, and the chapter's Figure 9.3 shows exactly why: enforcing arc consistency on $x_1$ can push cost onto $x_2$'s unary constraint, which then re-triggers enforcement back on $x_1$, in an infinite ping-pong, because each round genuinely *adds new* cost information rather than merely making existing information explicit (the network is not idempotent, so $\alpha \oplus \alpha \neq \alpha$: repeating the same derivation isn't a no-op). This is not a bug to patch around casually — it's a structural consequence of the algebra, and it's the single most important "what breaks without care" moment in the whole chapter.

Two fixes:

1. **Restrict direction.** Fix a variable ordering and only ever move cost from $j$ to $i$ when $x_i < x_j$ — **Directional Arc Consistency (DAC)**. Combined with plain (undirected) AC you get **Full Directional Arc Consistency (FDAC)**, strictly stronger than either alone, and — crucially — provably terminating.
2. **Track exactly how much you've moved, and be able to move it back.** This needs a **difference operator**: in a valuation structure, if $\alpha \preceq_v \beta$ and $\exists \gamma$ with $\alpha \oplus \gamma = \beta$, $\gamma$ is *a* difference of $\beta$ and $\alpha$. The structure is **fair** if a unique *maximum* difference $\beta \ominus \alpha$ always exists. (Fuzzy's $\oplus = \max$ is trivially fair — the difference is just $\max$ again; $k$-weighted's bounded sum has an explicit fair difference $a -_k b$.) Fairness lets you define **extraction**: build an implied constraint by combining a subnetwork and projecting, add it to the network, then **subtract it back out** ($\ominus$) of the sources — this is strategy 3 from the taxonomy above, and it provably preserves full equivalence, not just the optimum.

This generalizes into the **equivalence-preserving inference rule (EPI rule)**: a pair $(K, Y)$ — a constraint subset $K \subseteq C$ and a variable subset $Y \subseteq X$ — applied by removing $K$, then adding both $(\bigjoin K) \ominus (\bigjoin K)[Y]$ and $(\bigjoin K)[Y]$. Every local consistency in the chapter (node, arc, directional-arc, full-directional-arc) is expressible as a *set* of EPI rules applied to quiescence. The strongest widely implemented one is **Existential Directional Arc Consistency (EDAC)**, and empirically it's currently the best time/pruning tradeoff.

**Why this matters beyond the chapter:** the extraction/difference machinery is doing, in an order-theoretic setting, exactly what a **Galois connection's residuation** does — it's asking "how much of this combined fact can I attribute back to this one source, leaving the rest still sound." If you build a constraint-propagation engine parametrized by an abstract `CSemiring`-like trait for your compiler's invariant-generation kernel, this is the piece that tells you *when* you're allowed to redistribute cost/precision between propagators without breaking soundness — a very close cousin of when it's safe to strengthen one abstract-domain component at the expense of another during a reduced product.

### Soft global constraints and polynomial classes

[[Global-Constraints|Global constraints]] (Chapter 6) get soft versions too, via the same $\langle f_S, x_S \rangle$ encoding used for the "constraint optimization" reformulation in Part 3: soft all-different (two semantics — minimum reassignments, or count of colliding pairs), soft global cardinality, soft regular-language-membership. Their filtering algorithms reuse the flow/matching machinery from Chapter 6, adapted to compute costs instead of pure feasibility.

Tractability splits sharply along the idempotent/non-idempotent line established above (Section 9.6.3):

- **Idempotent $\oplus$** forces $\oplus = \min$ on a totally ordered scale — i.e., you're back in fuzzy CSP — and *every* tractable classical constraint language lifts to a tractable fuzzy one via the $\alpha$-cut decomposition, now needing only $O(n\log d)$ oracle calls (since there are at most $O(d^n)$ distinct levels).
- **Non-idempotent $\oplus$** is much harsher: weighted CSP restricted to boolean domains and $\{0,1\}$ costs *is* MAX-SAT — NP-complete and MAX-SNP-complete (no PTAS). Even binary clauses or plain XOR cost functions are NP-hard. Weighted CSP over larger domains breaks some tractable MAX-2SAT fragments too (soft equality is NP-hard for domains of size $\geq 3$). The one genuinely rich tractable class that survives is **submodular** cost functions ($f(u,v) + f(x,y) \leq f(u,y) + f(x,v)$ for $u \leq x, v \leq y$) — a maximal tractable class solvable in $O(n^3d^3)$, containing convex-shaped costs like $|x-y|^r$ and $\max(x-y,0)^r$.

This is worth remembering precisely because "submodularity buys tractability" recurs everywhere in optimization and is exactly the kind of structural fact CEGAR-style refinement loops can exploit when scoring candidate invariants or ranking counterexamples by cost.

## Part 6 — Combining search and inference

Neither pure search nor pure inference wins outright: elimination is efficient when variables have low degree but memory-catastrophic on dense/cyclic graphs; branch and bound has controlled memory but needs strong bounds to prune effectively. Section 9.7 is about hybridizing them.

- **Direct combination**: eliminate low-degree variables as long as you can (cheap, exact), and branch on high-degree ones when elimination would blow up — each branching decision typically *lowers* the degree of its neighbors and unlocks further eliminations.
- **Mini-bucket-based bounds inside B&B**: run MBE($z$) either once as preprocessing (if search follows a static order matching the bucket ordering) or freshly at every search node restricted to the remaining subproblem (enabling dynamic variable ordering) — either way, the aggregated bucket constraints double as a value-ordering heuristic, not just a pruning bound.
- **Local-consistency-based bounds**: enforce a soft local consistency (AC/DAC/FDAC/EDAC) at each search node; the resulting $f_\emptyset$ *is* a lower bound, directly, and the incremental nature of consistency enforcement (only re-checking what changed) makes this cheap enough to redo at every node — this is, empirically, the best-performing combination the chapter reports.
- **Structure exploitation**: pseudo-tree arrangements identify independent subproblems as soon as a branch splits the remaining graph into disconnected pieces — solve them separately (**PT-BB**), combine with Russian Doll Search leaf-to-root for better local upper bounds (**PT-RDS**), or generalize to full **AND/OR search trees** (**AOBB**). **Bounded backtracking on tree decompositions (BTD)** goes further: it *caches* the optimal cost of every independent subproblem solved (keyed by its separator's assignment) and reuses the cached value whenever the same separator assignment recurs — turning repeated subproblem solves (unavoidable in plain B&B whenever the same partial assignment on a separator recurs along different branches) into $O(1)$ lookups.

## Where this leads

Structurally, this chapter is the handbook's answer to "what do you do once satisfaction alone isn't the question anymore" — it takes almost every mechanism built in the earlier chapters (constraint propagation → soft local consistency; backtracking and branch-and-bound → DFBB with cost bounds; adaptive consistency and tree decompositions from tractability/complexity → bucket/cluster-tree elimination and BTD; global constraints → soft global constraints) and re-derives it under a single unifying algebra (the c-semiring / valued-constraint duality). If you've read the earlier chapters on propagation, backtracking, and tractability, almost nothing here is a genuinely new *algorithm* — it's the same algorithms, generalized along one dimension (the truth value $\{0,1\}$ becomes an arbitrary ordered scale) and specialized back down along another (idempotent vs. non-idempotent $\oplus$, which is the fork in the road for almost every hardness/tractability result in the chapter).

For the compiler/verifier project specifically, three connections are worth carrying forward explicitly:

1. **The c-semiring is a template for your CSP kernel's propagation engine.** If domain/lattice propagation, integer/non-linear reasoning, and DFA/automaton-shaped abstract domains are all meant to sit behind one propagation interface, parametrizing propagators over a semiring-like trait (as sketched above) is exactly how the classical/fuzzy/weighted/probabilistic distinction becomes "which semiring instance you plug in" rather than four separate solvers. Weighted CSP in particular is the natural home for scoring counterexample candidates by "distance from violating an invariant."
2. **Bucket/cluster-tree elimination is dynamic programming over a tree decomposition, generically parametrized** — this is the same algorithmic skeleton you'd want for structured/compositional abstract interpretation over programs with bounded treewidth control-flow (or for eliminating existentially-quantified auxiliary variables from a generated verification condition before handing it to an SMT solver), and the induced-width complexity bound is the same one that governs whether that elimination is tractable.
3. **The idempotent/non-idempotent fork, and the extraction/difference machinery that keeps non-idempotent inference sound, is a Galois-connection-shaped problem.** Any time you're tempted to move precision or cost between two cooperating analyses (a reduced product of abstract domains, or a CEGAR loop redistributing blame for a spurious counterexample across several guard constraints), the EPI-rule discipline here — *only redistribute what you can subtract back out, or you break soundness* — is the right mental model, even outside the constraint-satisfaction setting where it was invented.
