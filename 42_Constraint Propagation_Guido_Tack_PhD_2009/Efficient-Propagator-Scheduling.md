---
title: Efficient Propagator Scheduling
source: "Constraint Propagation: Models, Techniques, Implementation" (Guido Tack, PhD Dissertation, 2009)
chapters: "Chapter 5: Efficient Propagator Scheduling (pp. 47–66)"
tags: [constraint-propagation, csp, scheduling, sat-smt-csp]
---

# Efficient Propagator Scheduling

[[book-guidelines|↩ Back to guidelines]]

## The problem this chapter solves

[[Constraint-Satisfaction-and-Propagation-Based-Solving]] ended with a naive `fixpoint` loop: run every propagator, check if anything changed, repeat until nothing does. It's correct — it's a direct implementation of the fixed-point computation from [[The-Denotational-and-Operational-Model-of-Constraint-Propagation]]'s transition system — but it's also obviously wasteful. If you have a thousand propagators and one variable just got pruned by one unit, why re-run all thousand? Most of them can't possibly do anything: they don't mention the variable that changed, or they mention it but don't care about *that kind* of change.

Chapter 3's transition system ($d \vdash^p\to d'$, picking *some* not-fixed-point propagator $p \in P$ nondeterministically) is deliberately silent on *which* propagator to pick and *how* to know it's not at a fixed point without just running it. That's fine for a correctness proof — nondeterminism is a feature there, since Theorem 3.13 shows termination and stability hold regardless of the order chosen. But an actual solver has to pick, deterministically, and it has to pick *cheaply* — the whole point of propagation is to be the fast half of the solve loop, with search absorbing the exponential cost.

This chapter's answer is built from exactly two ideas, and everything else is refinement:

1. **Propagator-centered propagation.** Keep an explicit worklist — the **agenda** — of propagators that *might* not be at a fixed point. Everything not on the agenda is *known* to be at a fixed point. Only touch propagators on the agenda.
2. **Event-directed scheduling.** Don't put a propagator back on the agenda just because *some* domain changed — put it back only when a domain change of a *kind it actually cares about* happens to a variable it actually depends on.

The chapter builds these up as successive refinements of the same transition-system machinery from Chapter 3, each one proven to preserve the original semantics (same stable domains reachable) while doing less work to get there.

## Propagator-centered propagation and the agenda

### From domains to spaces

Chapter 3's transitions operated on domains alone: $d \vdash^p\to d'$. This chapter promotes the state to a **propagation space** $S = \langle d, Q \rangle$ — a domain paired with an agenda $Q$. The agenda holds propagators that are *possibly* not at a fixed point; propagators are **active** while on the agenda and **idle** otherwise.

**Definition 5.1 (Admissible space).** A space $S = \langle d', Q\rangle$ is *admissible* for a propagation problem $\langle d, P\rangle$ iff $d' \subseteq d$, and every propagator not on the agenda is genuinely at a fixed point:
$$\forall p \in P \setminus Q : p(d') = d'$$

This is the load-bearing invariant of the whole chapter — call it the **agenda invariant**. Every scheduling refinement from here to Section 5.5 is really just "a cheaper way to keep guaranteeing Definition 5.1 without recomputing $p(d')$ to check it."

A transition $S \vdash^p\to S'$ using $p \in Q$ is legal when:

1. $d \neq 0$ (domain not failed),
2. $d' = p(d)$,
3. $S'$ is admissible,
4. $Q' \supseteq Q \setminus \{p\}$, and
5. if $d' = d$ (the propagator didn't prune anything), then $Q' = Q \setminus \{p\}$ — necessary for termination.

Conditions 3–5 together are the **agenda invariant**. A space with $Q = \emptyset$ or $d = 0$ is *stable*; $\langle 0, Q\rangle$ is *failed*. **Theorem 5.2** confirms this machinery is sound: agenda-based propagation terminates, every terminal space is stable, and any stable terminal space is reachable in the *original* Chapter 3 transition system too — so nothing has been lost, only made deterministic-in-shape. The termination argument is a lexicographic ordering on (domain strength, agenda-as-set): every transition either strictly prunes the domain, or (by condition 5) shrinks the agenda — so the pair can't decrease forever.

**What breaks without the agenda invariant:** if you allow a space where some propagator is idle (off the agenda) but *not* actually at a fixed point, the transition system can terminate at a state that looks stable (agenda empty) but isn't a real fixed point of $P$ — a silent correctness bug that shows up as a solver reporting "solved" on an instance that still has prunable slack, or worse, missing solutions during search. Every refinement in this chapter is a proof obligation to keep discharging that invariant more and more cheaply.

The trivial-but-correct starting point Tack gives (before any smarter scheduling): whenever a propagator prunes, put *everything* back on the agenda:
$$Q' = \begin{cases} P & \text{if } p(d) \neq d \\ Q \setminus \{p\} & \text{otherwise}\end{cases}$$
This is literally the naive `fixpoint` loop from the previous article, phrased in agenda terms — reschedule the world on any change. It's admissible, it terminates, and it's exactly what event-directed scheduling exists to avoid.

### Rust: the agenda as a queue of trait objects

```rust
trait Propagator {
    /// Prune the domain in place; report whether anything changed.
    fn propagate(&self, store: &mut DomainStore) -> PropResult;
}

enum PropResult { NoChange, Pruned, Failed, Subsumed }

struct AgendaSolver {
    propagators: Vec<Box<dyn Propagator>>,
    agenda: std::collections::VecDeque<usize>, // indices into propagators
}

impl AgendaSolver {
    /// Naive re-run-the-world rule from the "before events" baseline (Section 5.1).
    fn step(&mut self, store: &mut DomainStore) -> Result<bool, ()> {
        let Some(p_idx) = self.agenda.pop_front() else { return Ok(true) }; // stable
        match self.propagators[p_idx].propagate(store) {
            PropResult::Pruned => {
                // Naive: reschedule *everything* — Section 5.2 replaces this.
                self.agenda.extend(0..self.propagators.len());
                Ok(false)
            }
            PropResult::Failed => Err(()),
            PropResult::NoChange | PropResult::Subsumed => Ok(false),
        }
    }
}
```

This is the naive reschedule-everything rule from Section 5.1, spelled out as code — the placeholder Section 5.2 replaces with real event-directed dependency lookups. Nobody would actually ship this line; it exists here only to make the "before" state concrete.

### Priority queues, FIFO fairness, and starvation

The agenda $Q$ doesn't have to be a plain queue. Tack generalizes it immediately to a **priority queue** with a fixed, small set of levels $\{1, \dots, i_{\max}\}$, exposing three operations:

- `head(Q)` — the oldest propagator at the *highest* priority present.
- `deq(Q, p)` — remove $p$.
- `enq(Q, p, i)` — add $p$ at priority $i$; if $p$ is already queued at priority $j \geq i$, no-op; if queued at $j < i$, *promote* to $i$; otherwise insert fresh at $i$.

The choice of FIFO (within a level) over LIFO matters for a concrete failure mode: **starvation**. A LIFO stack keeps re-running whatever was pushed most recently, which means a propagator that keeps getting pruned by its neighbors can dominate scheduling indefinitely while another propagator — one that might detect failure or do significant pruning — never gets its turn. FIFO guarantees every active propagator eventually reaches the head of its priority level. This isn't a performance nicety; a starved propagator can hide a failure that a smarter order would have found immediately, which matters when failure detection drives the exponential search tree's pruning.

Priorities layer a coarser fairness policy on top: within a level, FIFO fairness holds, but *across* levels, a prioritized system always exhausts all higher-priority propagators before touching a lower-priority one. This lets a solver prefer cheap propagators (which finish fast and might obsolete the need for an expensive one) — the mechanism gets its real payoff in Section 5.4's cost-based priorities.

## Event-directed scheduling

### Why "the domain changed" is too coarse a trigger

Rescheduling *every* propagator on *any* change (the naive rule above) is correct but blind: most propagators only care about a handful of variables, and often only about a specific *kind* of change to those variables.

**Example (the book's own, $x < y$):**
$$p_{x<y}(d)(z) = \begin{cases} d(x) \cap \{-\infty,\dots,\max(d(y))-1\} & z = x \\ d(y) \cap \{\min(d(x))+1,\dots,\infty\} & z = y \\ d(z) & \text{otherwise}\end{cases}$$
This propagator can only prune if $\min(d(x))$ or $\max(d(y))$ moved. If a solver removes some inner value of $d(x)$ that isn't the minimum, $p_{x<y}$ is unaffected — rescheduling it is pure waste.

**Example (the book's all-different, cheap value-propagation version):**
$$p_{\text{all-different}}(d)(z) = \begin{cases} d(x_j)\setminus d(x_i) & i\neq j,\ |d(x_i)|=1,\ x_j=z \\ d(z) & \text{otherwise}\end{cases}$$
This one only cares whether some $x_i$ became *assigned* — arbitrary domain shrinkage that doesn't assign anything is irrelevant to it (though the book notes a stronger, domain-complete all-different, Régin's, would care about any value removal).

Both examples make the same point: the right granularity for "should this propagator run again?" is not "did the domain change" but "did a change of a *specific kind* happen." That kind is called an **event**.

### Events, formally

**Definition 5.10.** An event $e$ is a condition $e(d(x), d'(x))$ on a domain shrinking from $d(x)$ to $d'(x) \subseteq d(x)$, required to be **monotonic**: for $d''(x) \subseteq d'(x) \subseteq d(x)$,
$$e(d(x), d''(x)) \iff e(d(x), d'(x)) \lor e(d'(x), d''(x))$$
and non-trivial: $e(d(x),d(x))$ must be false (an event always signals an actual change).

Monotonicity is the crux: once an event has fired between two domains, it stays "fired" for any further shrinking — $\mathrm{events}(d(x), d'(x)) \cup \mathrm{events}(d'(x), d''(x)) = \mathrm{events}(d(x), d''(x))$. This is exactly what lets a solver accumulate events incrementally instead of recomputing them from the original domain every time.

**What breaks without monotonicity — Example 5.11.** Tack gives a genuine non-monotonic candidate: `itv`, "is the domain currently an interval?" With $d(x) = \{1,2,3,5\}$, $d'(x) = \{1,2,3\}$, $d''(x) = \{1,3\}$: `itv` holds going from $d$ to $d'$ (the result is an interval) but *not* from $d$ to $d''$ (the result isn't). If scheduling used `itv` as a trigger, the *same final domain* $d''(x) = \{1,3\}$ could be reached via two different pruning sequences with different scheduling outcomes — one where the propagator got scheduled (via the $d\to d'\to d''$ path), one where it didn't (a direct $d \to d''$ path that skips the passing-through-an-interval intermediate state). The propagation result stays sound, but it becomes non-monotonic in a new, *avoidable* way — order-dependence introduced purely by a bad choice of event, not inherent to the constraint itself. This is a concrete instance of the general "what breaks without X" pattern: X here is monotonicity of the *scheduling trigger*, and losing it costs you determinism of outcome, not correctness.

Concrete event systems the book walks through: `asn` alone (sufficient for Boolean 0/1 variables, or for forward-checking on arbitrary variables); `dmc` alone (arbitrary domain change — this is exactly **variable-directed scheduling without events**, i.e. the baseline this whole section improves on); the standard integer system $\{$`asn`, `lbc`, `ubc`, `dmc`$\}$; a simplified $\{$`asn`, `bnd`, `dmc`$\}$ (Schulte & Stuckey show collapsing `lbc`/`ubc` into one `bnd` event is empirically *more* efficient, not less, despite being coarser — a reminder that finer-grained events aren't automatically better once you account for bookkeeping cost); and set variables' $\{$`asn`, `lbc`, `ubc`, `card`$\}$ over the set-interval approximation from [[Propagation-Strength-and-Domain-Approximations|Chapter 4]].

### The dependency invariant

For each variable $x$ and event $e$, a mapping $\mathrm{deps}(x)(e) \subseteq P$ names the propagators that must be woken up when $e$ fires on $x$ — we say such a $p$ is *subscribed* to $x$ with $e$. The whole point of `deps` is captured in the **dependency invariant**:
$$p(d) = d \;\land\; d' \subseteq d \;\land\; p(d') \neq d \implies \exists x \in X\, \exists e \in \mathrm{events}(d(x), d'(x)) : p \in \mathrm{deps}(x)(e)$$

In words: whenever a propagator that *was* at a fixed point *stops* being at one, some event it's subscribed to must actually have occurred. Scheduling then becomes: on a transition producing $d'$ from $d$ via propagator $p$,
$$Q' = (Q \setminus \{p\}) \cup \bigcup \{\, \mathrm{deps}(x)(e) \mid e \in \mathrm{events}(d(x), d'(x)) \,\}$$
This maintains the agenda invariant *for free* — if $p(d) = d$, no events fired, so nothing new gets scheduled; if $p$ did prune, the dependency invariant guarantees every propagator that could now be off-fixed-point is subscribed to something that fired, hence gets picked up.

**Propagators must be honest — Example 5.12, and what breaks without it.** The dependency invariant only protects you if propagators subscribe to *at least* the events that can actually cause them to leave a fixed point — and, crucially, don't quietly *use* information from events they didn't subscribe to. Tack's own counterexample: two propagators over $x, y$, one for $c_p = \llbracket y=1 \leftrightarrow x \geq 3\rrbracket$, one for $c_{p'} = \llbracket x=y\rrbracket$, both nominally subscribed to `lbc`/`ubc` on both variables, but $p'$ is domain-complete and *actually* prunes inner values too. Starting from a shared fixed point, pruning $x$'s upper bound to 2 schedules both. If $p'$ runs first and prunes $d(y)$ from $\{0,1,2,3\}$ to $\{0,1,2\}$ (a bound change — legitimately reschedules $p'$ via its own subscription), and $p'$ is immediately re-run and is now at a (bound-level) fixed point, then $p$ runs and prunes $d(y)$ further to $\{0,2\}$ — an *inner* removal, not a bound change. Since $p'$ only declared interest in bound events, it is **not** rescheduled, even though it is no longer at a fixed point (it's domain-complete and $\{0,2\}$ removing $1$ from $y$ interacts with its actual constraint in a way it never gets to check). The terminal "stable" state is not a real fixed point. This is a scheduling-correctness bug, not a performance one — dishonest subscriptions silently break Theorem 5.2's guarantee.

### Mermaid: the event-directed propagation loop

```mermaid
flowchart TD
    A[Agenda Q has propagators?] -->|No| Z[Stable: mutual fixed point reached]
    A -->|Yes| B["p = head(Q); run p(d) -> d'"]
    B --> C{p(d) == d'?}
    C -->|No change| D["remove p from Q"]
    C -->|Pruned| E["compute events(d(x), d'(x)) per modified x"]
    E --> F["Q' = (Q \\ {p}) ∪ deps(x)(e) for fired e"]
    D --> A
    F --> A
```

### Rust: an honest, event-directed agenda

```rust
use std::collections::{HashSet, VecDeque};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Event { Asn, Lbc, Ubc, Dmc }

struct Deps {
    // deps[x][event] -> propagator indices subscribed
    table: Vec<[Vec<usize>; 4]>,
}

impl Deps {
    fn subscribers(&self, var: usize, e: Event) -> &[usize] {
        &self.table[var][e as usize]
    }
}

trait Propagator {
    /// Must only prune according to what its declared events promise —
    /// "honesty" (Example 5.12) is a contract this trait cannot enforce
    /// mechanically, only a discipline the implementer must uphold.
    fn propagate(&self, store: &mut DomainStore) -> PropResult;
}

struct EventDirectedSolver {
    props: Vec<Box<dyn Propagator>>,
    deps: Deps,
    agenda: VecDeque<usize>,
    active: HashSet<usize>, // avoid duplicate agenda entries
}

impl EventDirectedSolver {
    fn schedule(&mut self, p: usize) {
        if self.active.insert(p) {
            self.agenda.push_back(p);
        }
    }

    fn step(&mut self, store: &mut DomainStore) -> Result<bool, ()> {
        let Some(p) = self.agenda.pop_front() else { return Ok(true) };
        self.active.remove(&p);
        let before = store.snapshot();
        match self.props[p].propagate(store) {
            PropResult::Failed => return Err(()),
            PropResult::NoChange | PropResult::Subsumed => {}
            PropResult::Pruned => {
                for (var, ev) in store.events_since(&before) {
                    for &q in self.deps.subscribers(var, ev) {
                        self.schedule(q);
                    }
                }
            }
        }
        Ok(false)
    }
}
```

The important design decision this sketch makes explicit: `deps` is indexed by `(variable, event)`, not just `variable` — that index *is* the dependency mapping from Definition 5.10 onward, and it's the data structure that Chapter 6 (Implementation Architecture) turns into the dependency array.

## Dynamic dependencies, subsumption, and propagator rewriting

So far `deps` and $P$ are fixed for the life of the propagation problem. Section 5.3 makes both dynamic, because a stronger domain often gives *more* information about which subscriptions are still needed than the static analysis could know in advance.

### Losing interest in variables — `cancel`

Book example: a propagator for $y = \max\{x_1,x_2,x_3\}$ with $d(x_1)=\{4,5\}$, $d(x_2)=\{3,5\}$, $d(x_3)=\{2,3\}$. No matter how $x_3$ changes further, it can't be the max — so the propagator can drop its subscription to $x_3$ entirely via a function `cancel(p, d)` returning the dependencies to remove. Spaces become 3-tuples $\langle d, Q, \mathrm{deps}\rangle$, and a transition can now replace `deps` with a `deps'` that still satisfies the dependency invariant:
$$\mathrm{deps}' = \mathrm{deps} \setminus \mathrm{cancel}(p,d)$$
This is explicitly framed as the **kernel/domain-module boundary**: `cancel` (like every domain-dependent helper introduced in this section) is domain-module logic; the kernel just mechanically updates `deps` and re-schedules from the *updated* mapping.

**What breaks without `cancel`:** nothing correctness-wise — it's a pure optimization. But without it, propagators keep accumulating subscriptions to variables that provably can no longer affect them, so the agenda keeps waking them up gratuitously forever, which is exactly the inefficiency this whole chapter exists to eliminate.

### Subsumption

If `cancel` can legitimately remove *all* of $p$'s subscriptions in $d$, the dependency invariant then guarantees $p(d') = d'$ for every stronger $d' \subseteq d$ — $p$ is **subsumed** by $d$ and can be discarded from $P$ entirely (spaces now 4-tuples $\langle d, P, Q, \mathrm{deps}\rangle$, with $P' = P \setminus \mathrm{subsumed}(p,d)$). Subsumption detection is coNP-complete in general, but easy in the common cases the book names: all significant variables assigned; $x<y$ with $\max(d(x)) < \min(d(y))$; all-different with pairwise-disjoint domains. Tack imposes a genuine *requirement*, not just a permission: subsumption must be **eventually** detected — specifically, once all significant variables of $c_p$ are assigned, `subsumed(p,d) = {p}` is mandatory. Chapter 6 explains why: undetected subsumption silently leaks memory and run-time indefinitely in a long-running search, since a subsumed-but-undetected propagator keeps getting scheduled and re-checked for the rest of the search tree below that node.

### Fully dynamic dependencies — watched literals

Cancellation-only dependencies are still monotonically shrinking. `subscribe(p, d)` lets a propagator *gain* new subscriptions too — and this is where **Example 5.13** lands one of the chapter's most consequential connections.

For Boolean disjunction $b_1 \lor \cdots \lor b_n = 1$, a propagator only has real work to do once *all but one* variable is assigned 0 (then it must force the last one to 1). Naively it must subscribe to all $n$ variables with `asn`. With dynamic dependencies, it only ever needs to watch **two** currently-unassigned-to-0 variables $b_i, b_j$: if one of them changes, either it became 1 (propagator subsumed) or it became 0 (cancel that subscription, find a fresh unassigned-to-0 $b_k$ to watch instead — or, if none exists, force the other watched variable to 1, possibly failing). This is precisely SAT's **watched literals** (Moskewicz et al. 2001) — Tack explicitly names the equivalence, and the Related Work section adds the caveat that this model's dynamic dependencies aren't *fully* equivalent to SAT-style watched literals: the latter aren't reset on backtracking and need to know exactly which variable triggered the change for an efficient implementation. This is one of the chapter's clean SAT/CSP bridges — worth keeping explicit for `sat-smt-csp` work, since it's the same mechanism (watch a minimal sufficient subset of literals/variables, re-arm lazily) doing the same job (avoid re-scanning everything) in two different solver families.

**What breaks without dynamic subscriptions here:** you'd have to statically subscribe to all $n$ variables, which means every single assignment among the $n-2$ "boring" variables (the ones neither watched) still wakes the propagator up to do nothing — an $O(n)$ wakeup cost per assignment instead of $O(1)$, exactly the kind of waste watched literals were invented to kill in SAT solvers processing millions of unit propagations.

### Propagator rewriting

The most dynamic move: replace a propagator $p$ by a set $R$ outright, so long as $\mathrm{sol}(\langle d,\{p\}\rangle) = \mathrm{sol}(\langle d, R\rangle)$ — i.e. $R$ induces the same solutions. **Example 5.14 (reified propagators):** for $c = \llbracket c' \leftrightarrow b\rrbracket$, once $d(b) = \{1\}$, rewrite $p_c$ to $p_{c'}$; once $d(b)=\{0\}$, rewrite to $p_{\lnot c'}$; if $c'$ (or $\lnot c'$) is already entailed, assign $b$ directly and report subsumption. Without rewriting, $p_c$ would have to carry *both* $c'$'s and $\lnot c'$'s propagation logic internally and re-check whether $b$ is assigned on every single invocation — rewriting turns a permanent conditional cost into a one-time transition, and gets code reuse (reusing $p_{c'}$ and $p_{\lnot c'}$ as-is) as a bonus.

## Self-rescheduling propagators and fixed-point detection

Section 5.4 (Schulte & Stuckey's contribution, per the book) tackles a subtler inefficiency: even event-directed scheduling will reschedule a propagator that modified *its own* subscribed variables, even when it's easy to tell — without recomputing $p(d')$ — that it's already at a fixed point again (e.g. because it's idempotent).

**Cost/priority levels.** Priorities are repurposed to encode estimated algorithmic cost: `unary=7, binary=6, ternary=5, linear=4, quadratic=3, cubic=2, veryslow=1`. A function `cost(p, d')` reports the *current* estimated cost — dynamically, since e.g. a linear-time propagator over $n$ variables effectively becomes ternary once all but three variables are assigned. Higher priority runs first, so cheap propagators reach their own fixed points before expensive ones are invoked at all — the practical payoff of the priority-queue machinery introduced back in Section 5.1.

**`fix(p, d')`** may return $\{p\}$ if $d'$ is (safely, cheaply determined to be) a fixed point of $p$, else must return $\emptyset$. For idempotent propagators this is unconditionally $\{p\}$; the safe fallback for anything else is $\emptyset$ (i.e., "don't claim fixed-point-ness you can't cheaply prove" — the same discipline as honest subscriptions). The transition rule becomes:
$$Q' = \mathrm{deq}\Big(\mathrm{enq}\big(\mathrm{deq}(Q,p),\ \{\langle p', i\rangle \mid \exists x,e : p' \in \mathrm{deps}'(x)(e) \land i = \mathrm{cost}(p',d')\}\big),\ \mathrm{fix}(p,d')\Big)$$
Read operationally: dequeue $p$, re-enqueue whatever its own modifications now imply (possibly re-adding $p$ itself, at its current cost), then dequeue again anything `fix` certifies as already settled. Section 6.3, per the book, turns this dequeue/enqueue/dequeue dance into one net-effect operation rather than three real ones — a Chapter 6 concern.

**What breaks without `fix`:** every self-modifying propagator gets rescheduled after every single invocation, even the ones that are trivially known (idempotent) to have nothing left to do — a constant per-invocation tax that compounds across a search tree with millions of nodes.

### Staged propagators

Many constraints admit multiple propagation algorithms trading strength for cost — the book's own running numbers: all-different has a domain-complete $O(n^{2.5})$ algorithm (Régin) and a bounds$(\mathbb Z)$-complete $O(n\log n)$ one; linear equations have a linear-time bounds$(\mathbb R)$ algorithm versus NP-hard bounds$(D)$/domain-complete ones (see [[Propagation-Strength-and-Domain-Approximations]]). Running the cheap one at high priority, then the expensive one only once the cheap one stalls, is a direct application of the same priority idea — except now for *one* constraint with *two implementations* instead of two constraints.

Running them as two separate propagators wastes memory/scheduling overhead per propagator, and worse, if one detects subsumption the other still lingers on the agenda uselessly. **Staged propagators** (Schulte & Stuckey) fix both: one propagator object, multiple internal algorithms, and the *triggering event* determines which **stage** — identified with a priority level — runs next.

**Example 5.15 (staged all-different).** Scheduled by `asn` → stage A, priority `linear`, runs $p_{\text{asn}}$ (the cheap value-propagation rule from Example 5.4); if not subsumed, reschedules itself into stage B at priority `quadratic`. Scheduled by `dmc` (and not already in stage A) → stage B directly, runs $p_{\text{dom}}$ (domain-complete), which is idempotent so doesn't reschedule.

Formalizing this promotes each $p \in P$ to a function `Stage -> (Dom -> Dom)`, and threads the stage through every helper: `head(Q)` now returns a `(propagator, priority)` pair; `cost(p, d', e)` also takes the triggering event; a new `nextStage(p, d', i)` decides whether to re-enqueue $p$ at a different stage; `fix(p(i), d')` operates on the stage-specific propagator. The full **prioritized, event-directed, dynamic, staged transition system** combines every mechanism in the chapter into one rule:
$$
\begin{aligned}
d' &= p(i)(d)\\
P' &= (P \setminus \mathrm{subsumed}(p,d)) \cup \mathrm{rewrite}(p,d)\\
\mathrm{deps}' &= (\mathrm{deps}\setminus\mathrm{cancel}(p,d)) \cup \mathrm{subscribe}(p,d)\\
Q' &= \mathrm{deq}\Big(\mathrm{enq}\big(\mathrm{deq}(Q,p),\ \{\langle p',i'\rangle \mid \dots\} \cup \mathrm{nextStage}(p,d',i)\big),\ \mathrm{fix}(p(i),d')\Big)
\end{aligned}
$$
This is genuinely the chapter's capstone equation — every earlier refinement (agenda, events, dynamic deps, subsumption, rewriting, cost-based priority, fixed-point suppression, staging) is a term in it.

### Rust: cost-driven staging as an enum-dispatched propagator

```rust
enum Stage { A, B }

struct StagedAllDifferent { stage: Stage }

impl StagedAllDifferent {
    fn cost(&self, triggering: Event) -> Priority {
        match (&self.stage, triggering) {
            (Stage::A, _) => Priority::Linear,
            (Stage::B, _) => Priority::Quadratic,
        }
    }

    fn run(&mut self, store: &mut DomainStore) -> (PropResult, Option<Stage>) {
        match self.stage {
            Stage::A => {
                let r = value_propagate_assigned(store); // pasn
                (r, Some(Stage::B)) // always advance if not subsumed
            }
            Stage::B => {
                let r = domain_complete_propagate(store); // pdom, idempotent
                (r, None) // never reschedules itself
            }
        }
    }
}
```

The enum-per-stage shape here is the direct Rust analogue of `p : Stage -> (Dom -> Dom)` — a small, closed sum type standing in for the book's function-from-a-finite-index-set.

## Propagation conditions and modification events

Sections 5.1–5.4 leave two efficiency questions unanswered: how do you *cheaply* compute $\mathrm{events}(d(x), d'(x))$, and how do you *cheaply* look up which propagators depend on it? Section 5.5 — the chapter's own original contribution, not a recap of prior work — answers both.

### Propagation conditions: a canonical index for `deps`

The problem: a propagator often needs several events on the same variable (e.g. both `lbc` and `ubc`), and every propagator needs `asn` regardless (since `asn` is the only event guaranteed to eventually fire, and every propagator must eventually see an assignment to enforce its constraint on it). Storing `deps` keyed by raw event *sets* wastes memory (a propagator could appear under several different but equivalent sets) and bookkeeping.

The fix is to quotient event sets by an equivalence: $\{$`lbc`,`dmc`$\}$ and $\{$`dmc`$\}$ are equivalent for scheduling purposes because `lbc` $\to$ `dmc` (`lbc` firing always implies `dmc` fires too). Formally, $e \to e'$ means $e(d(x),d'(x)) \implies e'(d(x),d'(x))$ for all domains.

**Definition 5.16 (Propagation condition).** A set of events $\pi$ such that `asn`$\,\in \pi$, and $\pi$ is closed under the *converse* of implication: if $e \in \pi$ and $e' \to e$, then $e' \in \pi$.

Each propagation condition is a canonical, minimal representative of an equivalence class of event sets — small enough in practice (few events per event system) to encode as a small integer, giving $O(1)$-ish indexing into `deps(x)(\pi)`. Figure 5.1 in the book draws the implication lattice for the standard integer events: `dmc` sits at top (implied by everything), `lbc`/`ubc` in the middle, `asn` at bottom (implies everything) — with the corresponding propagation conditions $\{$`asn`,`lbc`,`ubc`,`dmc`$\}$, $\{$`asn`,`lbc`$\}$, $\{$`asn`,`ubc`$\}$, $\{$`asn`$\}$ layered alongside.

The dependency invariant is restated in these terms with no loss of generality:
$$p(d)=d \land d'\subseteq d \land p(d')\neq d \implies \exists x,\pi : \pi \cap \mathrm{events}(d(x),d'(x)) \neq \emptyset \land p \in \mathrm{deps}(x)(\pi)$$

### Modification events: what actually happened, compactly

The complementary problem: given $d(x)$ and $d'(x)$, computing $\mathrm{events}(d(x),d'(x))$ from scratch every time is wasteful — an implementation should track this *incrementally* as propagation proceeds, and only track the sets that can actually occur.

**Definition 5.17 (Modification event).** A set of events `me` such that either `me = {asn}`, or `asn` $\notin$ `me` and `me` is closed under implication (forward, this time — not converse). Modification events are closed under union, and — like propagation conditions — few enough to enumerate and encode as small integers. For the standard integer event system, the book enumerates exactly five:
$$
\begin{aligned}
\mathit{me}_{\mathrm{asn}} &= \{\text{asn}\}\\
\mathit{me}_{\mathrm{lbc}} &= \{\text{lbc},\text{dmc}\}\\
\mathit{me}_{\mathrm{ubc}} &= \{\text{ubc},\text{dmc}\}\\
\mathit{me}_{\mathrm{bbc}} &= \{\text{lbc},\text{ubc},\text{dmc}\}\\
\mathit{me}_{\mathrm{inner}} &= \{\text{dmc}\}
\end{aligned}
$$
(Note what's *missing*: $\{$`lbc`$\}$ alone can't occur, since `lbc` always implies `dmc`.)

Tying it together, `modifications(p, d)` — again a kernel/domain-module boundary function — returns pairs $\langle x, \mathit{me}\rangle$ of variables modified by running $p$ and their modification events, and scheduling becomes:
$$Q' = (Q\setminus\{p\}) \cup \bigcup\{\, \mathrm{deps}(x)(\pi) \mid \langle x,\mathit{me}\rangle \in \mathrm{modifications}(p,d) \land \pi \cap \mathit{me} \neq \emptyset \,\}$$

**Why the model needs *both* notions, not just one "event set":** propagation conditions answer "what is a propagator subscribed to" (a static, canonical, small-integer *key*); modification events answer "what actually happened between two domains" (a dynamic, incrementally-tracked *value*). Scheduling is then just "does this key intersect that value" — a single integer AND-and-test-nonzero in a real implementation. Collapsing the two into one notion would force either recomputing full event sets from raw domains on every check (defeating the incremental-tracking motivation) or storing subscriptions as arbitrary event sets without a canonical minimal form (defeating the compact-indexing motivation). Keeping them separate is precisely what makes deps a compact table and modification tracking an $O(1)$ per-domain-operation bookkeeping cost — this pairing is exactly what Chapter 6 implements as small integers driving array-indexed dependency lookups.

## Variable-centered versus propagator-centered propagation

The chapter closes (Section 5.6, Related Work) by naming the alternative architecture it did *not* choose: instead of an agenda of propagators, keep an agenda of **modified variables**. The adjusted invariant: for all $v \in X\setminus Q$, all propagators subscribed to $v$ are at a fixed point. ILOG Solver, CHOCO, and Minion use this (CHOCO and ILOG actually hybridize — a dequeued variable's propagators can run immediately or get queued).

The genuine advantage of variable-centered scheduling: when a propagator runs, it's invoked *because a specific variable changed*, so it can propagate **incrementally** from that one change rather than recomputing from scratch. Book example: for $y = \sum_{i=1}^k x_i$, a bounds$(\mathbb R)$ propagator can adjust $y$'s lower bound by exactly the delta in $x_j$'s lower bound, instead of re-summing all $k$ lower bounds. Propagator-centered scheduling, as developed in the rest of this chapter, loses that "which variable, exactly" information at the point of invocation by default — Lagerkvist and Schulte's *advisors* (cited, not detailed here) are the mechanism that recovers incrementality inside a propagator-centered system without abandoning its other advantages (simpler dependency bookkeeping, cleaner subsumption/rewriting semantics as developed above).

This is a genuine architectural fork, not a strict dominance — propagator-centered buys you the clean event/dependency/subsumption machinery this chapter builds; variable-centered buys you incrementality for free at the cost of a different, coarser invariant. Gecode (previewed here, developed in Chapter 6) is propagator-centered.

## Where this leads

Chapter 6 ("[[Implementation-Architecture-of-a-Propagation-Kernel|Implementation Architecture of a Propagation Kernel]]") takes every abstraction introduced here — the agenda, `deps`, propagation conditions, modification events, `cancel`/`subscribe`/`subsumed`/`rewrite`/`fix`/`cost` — and gives each one a concrete, performance-engineered data structure: the dependency array indexed by propagation condition, [[Implementation-Architecture-of-a-Propagation-Kernel#The bucket priority queue|the bucket priority queue]] for the agenda, and the modification-event delta $\Delta\mathit{me}$ threaded through a single `status()` loop. Nothing in Chapter 6 is new *model*; it's this chapter's mathematics turned into arrays and integers.

For the `sat-smt-csp` focus area specifically: this chapter *is* the blueprint for the piece of the target CSP kernel that decides, on every domain change, which constraints need to be re-checked at all. A kernel that re-runs every propagator (or every constraint-check) on every domain narrowing — the naive `fixpoint` baseline — is correct but will not scale to the constraint counts a real counterexample-search kernel needs; propagation conditions plus modification events are precisely the mechanism that turns "did anything change" into "does *this* constraint need to look again," the same discriminating question SAT's watched-literals scheme answers for clause/unit propagation. The dynamic-dependencies material (Section 5.3) is the direct bridge: watched literals in SAT and dynamic `subscribe`/`cancel` in CP are, as the book states outright, the same underlying idea — "watch the minimal sufficient subset, re-arm lazily" — applied to two different constraint representations, and a CSP kernel built to search for counterexamples over automaton/DFA-shaped abstract domains will need exactly this discipline to avoid re-scanning its entire constraint store on every propagation step.
