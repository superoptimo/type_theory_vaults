---
title: The Constraint Solving Procedure
source: Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)
chapters: Section 3.6 "The constraint solving procedure", Section 3.7 "Processing constraints" (pp. 20-23)
tags: [type-theory, elaboration, unification, backtracking-search, lean]
---

[[book-guidelines|↩ Back to guidelines]]

## Why a solver needs more than "solve constraints in order"

By the time we reach this stage, [[The-Preprocessing-Phase|preprocessing]] has already turned a user's partial expression into a term riddled with metavariables, packaged as a bag of [[Constraints-and-Justifications|unification and choice constraints]], and [[The-Constraint-Simplification-Procedure|`simp`]] has sorted each one into a category (pattern, delta, quasi-pattern, flex-rigid, recursor, flex-flex, or a choice-constraint variant). None of that machinery, on its own, tells you *in what order* to attack the constraints, *what to do* when a constraint has several plausible solutions, or *how to recover* when a choice made ten steps ago turns out to have been wrong.

That last problem is the crux of it. Consider solving `?m zero ≈ true` and `?m (succ zero) ≈ false` together with a third constraint that happens to be unsolvable. A naive depth-first solver would guess an assignment for `?m`, then discover the failure buried three constraints later, and — without any memory of *why* it made that particular choice — would have no principled way to know which earlier decision to revisit. It would either re-explore the entire search tree from scratch (correct but wasteful) or backtrack chronologically to the most recent choice point regardless of whether that choice point had anything to do with the failure (fast, but liable to miss the real culprit and thrash).

The constraint solving procedure is the piece of the algorithm that answers these three questions concretely: what order to process constraints in, how to represent a choice point so it can be undone cheaply, and how to backtrack *non*-chronologically — jumping straight to the choice point actually responsible for a failure, rather than the most recent one.

## The four pieces of solver state

The solver is built around four global data structures (the paper treats them as global variables to keep the pseudocode simple; in a real implementation they'd be threaded through explicitly or held in a solver struct):

- **A priority queue $Q$ of constraints** — decides what gets attacked next.
- **A mapping $U$ from metavariables to constraints** — decides what needs re-examining after a metavariable gets assigned.
- **A substitution $S$** — the metavariable assignments accumulated so far, each carrying its [[Constraints-and-Justifications|justification]].
- **A case-split stack $C$** — the backtracking history.

### The priority queue and its ordering

$Q$ is ordered by a fixed total order on constraint categories:

$$
\text{pattern} \prec \text{ready} \prec \text{regular} \prec \text{delta} \prec \text{quasi-pattern} \prec \text{flex-rigid} \prec \text{recursor} \prec \text{postponed} \prec \text{flex-flex}
$$

(`ready`, `regular`, and `postponed` are the three states a *choice* constraint can be in, rather than unification-constraint categories — see [[The-Constraint-Simplification-Procedure]] for how a constraint lands in one of these.) Constraints within the same category are processed first-in-first-out.

This ordering is a deliberate greedy heuristic: solve the things you're *certain* about first. Pattern constraints (Miller patterns) have a unique solution, so solving them can only narrow the search — never introduce new branching. Ready choice constraints are choice constraints whose dependencies are already resolved, so they too are safe to fire immediately. Delta constraints (unfolding definitions) come before the genuinely nondeterministic quasi-pattern/flex-rigid/recursor categories, because unfolding might turn a hard constraint into an easy one. Flex-flex constraints — two metavariables applied to arguments, unified against each other — are last, because they're the most underdetermined: the paper's contract is that the solver is *allowed* to return them unresolved (as long as neither metavariable is otherwise assigned) rather than being forced to guess.

If you've written a SAT solver or a Prolog engine, this should feel familiar: it's the same idea as "propagate everything forced before you branch on anything free."

### $U$: knowing what to wake up

$U[?m]$ is the finite subset of constraints in $Q$ that are *stuck on* $?m$ — either a unification constraint whose reduction got blocked because $?m$ is unassigned, or an `ondemand` choice constraint `⟨?n ℓ : t in f, j⟩` where $?m$ occurs somewhere in $t$. The instant $?m$ gets an assignment, every constraint in $U[?m]$ is a candidate for progress and needs to be revisited.

This is exactly the "watch list" or "wake list" pattern from constraint-propagation solvers (SAT/SMT watched-literals is the closest cousin): rather than re-scanning the entire constraint set after every assignment to see what changed, you maintain an index from "thing that could unblock me" to "constraints waiting on it," and only touch the constraints that could plausibly have become simpler.

```rust
use std::collections::HashMap;

struct SolverState {
    queue: PriorityQueue<Constraint>,      // Q, ordered by category
    waiting_on: HashMap<MetaVarId, Vec<ConstraintId>>, // U
    assignments: Substitution,             // S
    case_splits: Vec<CaseSplit>,           // C
}

fn on_metavar_assigned(state: &mut SolverState, m: MetaVarId) {
    // everything in U[m] might now make progress — revisit it
    if let Some(waiters) = state.waiting_on.remove(&m) {
        for c in waiters {
            visit(state, c);
        }
    }
}
```

### `visit`: the dispatcher

`visit` is the single entry point that routes a constraint to the right handler:

```
visit c:
    if c is a unification constraint:  visiteq c
    else:                              visitchoice c
```

`visiteq ⟨r ≈ s, j⟩` does one of three things:

1. **If $r$ or $s$ is stuck on some already-assigned $?m$** — substitute in $?m$'s assignment and re-run `simp` on the result, folding the assignment's own justification $j_m$ into $j$ via the join operator $\bowtie$. This is the "a stuck term became unstuck" case: an earlier decision unblocked this constraint, so simplify again in light of it.
2. **If the constraint is a pattern `⟨?m ℓ ≈ t, j⟩`** — solve it immediately: assign $?m \mapsto \lambda\text{-abstract}(\ell, t)$ in $S$, then eagerly revisit every constraint in $U[?m]$, since they were all waiting on exactly this. Notice pattern constraints are *never* pushed onto $Q$ — they're always solved on the spot the moment `visit` sees them, which is why they sit first in the priority order but conceptually don't even need to wait in line.
3. **Otherwise** — update $U$ (register this constraint as stuck on whichever metavariable blocks it) and insert it into $Q$ for later processing.

`visitchoice ⟨?n ℓ : t in f, j⟩` is simpler: substitute any already-assigned metavariables occurring in $t$, update $U$, and insert into $Q$.

## Case splits and non-chronological backtracking

Whenever the solver has to solve a genuinely non-pattern constraint — one with more than one plausible way forward — it doesn't just try alternatives and hope; it records a **case split**, a snapshot of everything needed to undo the choice later:

$$
\langle Q_c, U_c, S_c, j_a, j_c, z \rangle
$$

- $Q_c, U_c, S_c$ — copies of the solver state *at the moment the case split was created*, so restoring is just "assign these back to the globals."
- $j_a$ — a fresh **assumption justification**, minted specifically to name this choice point (see [[Constraints-and-Justifications]] for how assumption justifications work).
- $j_c$ — the justification of the constraint that triggered the split.
- $z$ — a *lazy list* of the remaining untried alternatives.

The paper is explicit about the implementation trick that makes cheap snapshotting possible: $Q$, $U$, and $S$ are backed by **pure (persistent) data structures — red-black trees** — that support copy in $O(1)$ via structural sharing. This sidesteps the classic alternative, a *trail* that records and undoes destructive mutations step by step; the authors note they measured that the simpler copy-on-split approach was not a bottleneck in practice. If you've used Clojure's persistent vectors/maps, or Rust's `im` crate, or OCaml's `Map`, this is the same idea: an "update" doesn't mutate the old structure, it returns a new root that shares most of its substructure with the old one, so keeping the old version around for backtracking costs almost nothing.

```rust
// A persistent map gives O(1) "checkpoint" for free — no explicit undo log needed.
use im::HashMap as PersistentMap;

struct CaseSplit {
    queue_snapshot: PersistentQueue,
    waiting_snapshot: PersistentMap<MetaVarId, Vec<ConstraintId>>,
    subst_snapshot: PersistentMap<MetaVarId, (Term, Justification)>,
    assumption: Justification,   // j_a, names this choice point
    constraint_just: Justification, // j_c
    remaining_alternatives: LazyList<Vec<Constraint>>, // z
}
```

### `process`: creating a case split

`process z j` is the procedure that actually creates one of these. Given a lazy list of alternatives $z$ and the triggering justification $j$:

- If $z$ is empty (no alternatives left to try), give up on this branch and call `resolve j`.
- Otherwise, pull the head alternative $a$ off $z$, mint a fresh assumption justification $j_a$, push $\langle Q, U, S, j_a, j_c, z \rangle$ onto $C$, and `visit (a ⊲⊳ j_a ⊲⊳ j)` — try $a$, tagging it with both the new assumption and the accumulated justification chain.

This is where the category-specific case-split logic (delta constraints trying "don't unfold" before "unfold"; flex-rigid constraints trying [[Higher-Order-Unification|Huet's imitation and projection alternatives]] in a particular order; recursor constraints falling back to an approximate treatment) all plug in — each category just needs to hand `process` the right lazy list of alternatives in the right order. See [[Higher-Order-Unification]] for exactly what those alternatives look like for flex-rigid constraints; the point to take away here is that whatever the category, they all funnel through the same `process`/case-split/backtrack machinery.

### `resolve`: why non-chronological beats chronological

This is the payoff. When `simp` (or any downstream step) throws an error justification $j$, `resolve j` doesn't just pop the most recent case split unconditionally — it walks down the stack looking for the *first* case split whose assumption the failure actually **depends on**:

```
resolve j:
    while C is not empty:
        let ⟨Q_c, U_c, S_c, j_a, j_c, z⟩ = top(C)
        if j depends on j_a:
            restore state: Q := Q_c, U := U_c, S := S_c
            if pull(z) = some a:
                pop C
                visit (a ⊲⊳ j_c ⊲⊳ j)
                return
        # else: this case split had nothing to do with the failure — skip past it
    fail: "no solution" (C is empty)
```

"$j$ depends on $j_a$" is answered by walking $j$'s own justification structure (built up via `⊲⊳`, the join operator on justifications — see [[Constraints-and-Justifications]]) and checking whether the assumption $j_a$ appears anywhere in it. If it doesn't, that case split is provably irrelevant to this particular failure — restoring to it and retrying would just reproduce the same error, so `resolve` skips straight past it without wasting a restore/retry cycle. Only when it finds a case split the failure *actually traces back to* does it restore state and try the next alternative from that split's lazy list $z$ — or, if that split is also exhausted, keep unwinding further down the stack.

This is precisely conflict-driven backtracking in the style of modern SAT/SMT solvers (CDCL): instead of "undo the last decision, no matter what," it's "undo the decision that's actually implicated in this conflict." A Prolog implementer would recognize the naive alternative — plain chronological backtracking on failure — and recognize this as the fix for the well-known "thrashing" pathology where a solver keeps re-deriving the same doomed subtree because it never backs up far enough to escape it.

One more detail worth noting: if retrying an alternative from a case split *itself* throws a new error $j'$ (visiting $a$ didn't just succeed — it failed for a different reason), `resolve` doesn't need a separate failure path; it just recursively invokes `resolve j'` on the new error. Backtracking is thus naturally re-entrant: a failed retry is just another error to resolve, possibly digging further down the same stack.

```python
def resolve(state, j):
    while state.case_splits:
        split = state.case_splits[-1]  # top of C
        if depends_on(j, split.assumption):
            restore(state, split.queue, split.waiting, split.subst)
            alt = pull(split.remaining_alternatives)
            if alt is not None:
                state.case_splits.pop()
                try:
                    visit(state, tag(alt, split.constraint_just, j))
                except ElaborationError as j_prime:
                    resolve(state, j_prime)   # naturally recursive
                return
        # this split's assumption is irrelevant to j — keep unwinding
        state.case_splits.pop() if not depends_on(j, split.assumption) else None
    raise ElaborationError("failed to solve constraints")
```

(The Python sketch above simplifies the paper's `while` slightly for clarity — the paper's version only pops $C$ inside the dependency-matching branch, since a split whose assumption $j$ doesn't depend on effectively gets skipped by continuing the loop with it still notionally "current," but the net effect — walk down until you find the responsible split, restore, and retry — is the same.)

## How this connects back

Zooming out: [[The-Constraint-Simplification-Procedure|`simp`]] classifies, [[The-Preprocessing-Phase|preprocessing]] supplies the raw constraints, and this procedure is the engine that actually drives the whole thing to a fixed point — or to failure. Everything downstream of elaboration (type inference, [[Higher-Order-Unification|higher-order unification]] for induction predicates, [[Type-Classes-and-Class-Inference|type class resolution]] as `ondemand` choice constraints, [[Overloading-and-Coercions|coercion and overloading resolution]] as case splits between alternatives) is, from this procedure's point of view, just another category of constraint with its own case-split alternatives — which is precisely the unifying design the paper is making the case for: one constraint-solving core, with all those outward-facing features implemented as instances of the same $Q$/$U$/$S$/$C$ machinery rather than as bespoke passes.

For a Lean user, this is the mechanism that makes elaboration *feel* almost magical when it works, and gives genuinely traceable error messages when it doesn't: a failure isn't "somewhere in this 200-line proof," it's a justification chain that `resolve` can walk to point at the specific case split responsible.
