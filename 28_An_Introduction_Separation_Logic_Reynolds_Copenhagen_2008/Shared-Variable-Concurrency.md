---
title: "Shared-Variable Concurrency"
book: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 1, §1.10"
pages: "28–30"
tags: [separation-logic, concurrency, frame-rule, resource-invariants, ownership]
---

# Shared-Variable Concurrency

[[book-guidelines|↩ Back to guidelines]]

> **A note on scope before we start.** This topic's entire treatment in the book is §1.10 of the overview chapter — about two and a half pages. This is not a compression choice on my part: I checked. The PDF is 204 pages total, the bibliography starts at page 199, and there is no later chapter that returns to concurrency in more depth (Chapters 2–6 cover assertions, specifications, lists, trees/dags, and iterated conjunction — no concurrency chapter exists in this book). Reynolds's own Topic-List framing ("shared-variable concurrency") is delivered here, in miniature, as a *preview* of O'Hearn's extension rather than a full proof-theoretic treatment — the notes are explicit that reasoning fully about conditional critical regions and resource invariants is "far less straightforward" than the material actually developed. So this article treats §1.10 as what it is: a compressed but conceptually complete sketch, and it stays honest about that thinness rather than padding it.

## Why sequential separation logic isn't enough

Everything built so far in the book — the frame rule, the heap-manipulating command rules, the list/tree predicates — is about **one thread of control**. The moment you allow two processes to run concurrently and touch a shared heap, a new failure mode appears that none of the sequential machinery protects against: **interference**. One process's assumptions about the heap can be silently invalidated by another process's mutation, mid-execution, at a point the first process never anticipated.

Classical Hoare logic already has a rule for *non-interfering* parallel composition — Hoare's own rule, predating Owicki-Gries-style reasoning about shared variables:

$$
\frac{\{p_1\}\ c_1\ \{q_1\} \qquad \{p_2\}\ c_2\ \{q_2\}}{\{p_1 \wedge p_2\}\ c_1 \parallel c_2\ \{q_1 \wedge q_2\}}
$$

with the side condition that the free variables of $p_1, c_1, q_1$ are not modified by $c_2$, and vice versa. This rule is sound in ordinary (variable-only) Hoare logic, precisely because the side condition rules out interference at the level of *variables*.

### What breaks: the heap is a shared variable the rule doesn't know about

Bring the heap into the picture, and this rule **fails**, even though the side condition (about program *variables*) is still satisfied. Two processes with no variables in common can still both mutate the same heap cell — the side condition has nothing to say about that, because it was designed for a world where "state" meant "the store," not "the store plus a disjoint-or-shared heap." A process's precondition $p_1$ might assert `x ↦ 3`; if $c_2$ mutates the cell at `x` to `4`, then $q_1$ (which assumed the mutation in $c_1$ landed on an unmolested cell) can be falsified by an event $c_1$ never triggered and has no way to observe was even possible.

This is precisely the sequential story's "unsoundness of the rule of constancy" (from earlier in the chapter) recurring in a concurrent guise: any Hoare-logic rule that reasons about a command's effect while implicitly assuming "everything else stays put" is exactly the rule that heap-sharing breaks. The frame rule fixed this for *sequential* composition by making the "everything else" an explicit, syntactically separate conjunct (`r`) that the command is proved disjoint from. O'Hearn's insight is to apply the identical fix to *parallel* composition.

## O'Hearn's fix: replace $\wedge$ with $*$

$$
\frac{\{p_1\}\ c_1\ \{q_1\} \qquad \{p_2\}\ c_2\ \{q_2\}}{\{p_1 * p_2\}\ c_1 \parallel c_2\ \{q_1 * q_2\}}
$$

(same variable side condition as before). The separating conjunction does exactly the job it always does: it asserts that $p_1$ and $p_2$ hold of **disjoint** portions of the heap. Since the heap is partitioned at the start, and each process's specification is a *local* specification of its own footprint (in the frame-rule sense from earlier in the chapter), no process's precondition can ever be an assertion about a cell the other process owns. Interference is ruled out not by a side condition bolted onto the rule, but *by construction*, the same way `list α i * list γ k` ruled out sharing in the very first example of the book (`LREV`).

This is worth sitting with as a design principle rather than just a rule to memorize: **wherever ordinary conjunction implicitly assumed non-interference that the underlying semantics didn't actually guarantee, separation logic's answer is to make the non-interference an explicit, checkable disjointness condition via `*`.** You saw this move once already (rule of constancy → frame rule); here it is again, one level up, for concurrency. If you're designing a verifier or an effect system, this is the generalizable lesson, not the specific rule.

```rust
// A Rust sketch of what the *-rule licenses: two threads each own a
// disjoint chunk of heap (here, via disjoint indices into a slice split
// with split_at_mut — Rust's own separation-logic-flavored primitive for
// proving two `&mut` regions are non-overlapping at compile time).
fn parallel_update(data: &mut [i32], mid: usize) {
    let (left, right) = data.split_at_mut(mid); // disjointness proved once, statically
    std::thread::scope(|s| {
        s.spawn(|| { for x in left.iter_mut()  { *x += 1; } }); // {p1} c1 {q1}
        s.spawn(|| { for x in right.iter_mut() { *x *= 2; } }); // {p2} c2 {q2}
    });
    // postcondition: q1 * q2 — each half updated independently,
    // and Rust's borrow checker is precisely what makes the "*" here sound.
}
```
`split_at_mut` is a genuinely apt analogy, not a strained one: its entire reason for existing is to let the compiler statically verify a disjointness fact that would otherwise require unsafe code or runtime assertions — exactly the fact O'Hearn's rule needs as its side condition, except separation logic checks it via the *-conjunction's semantics rather than via a borrow checker's region analysis. The proof techniques differ (static aliasing analysis vs. a program logic's inference rules) but the property being established — disjoint ownership of the resource each thread touches — is the same one.

## When synchronization enters: conditional critical regions and resource invariants

Unconstrained parallelism (the rule above) is the easy case — it's essentially "if you can statically [[Case-Studies-in-Program-Verification#Partition|partition]] the heap once and for all, interference is trivially impossible." Real concurrent programs need to **share** access to some region of the heap through synchronized critical sections, and that's where the *interesting* engineering happens: ownership of a piece of the heap needs to move dynamically between "belongs to some process" and "belongs to the shared resource," at exactly the moments processes enter and leave critical regions.

Hoare's original idea (predating separation logic) for conditional critical regions keyed to a **resource** — a named, disjoint collection of variables — was:

- Associate an **invariant** $R$ with each resource.
- On entering a critical region keyed to that resource, you may **assume** $R$ holds.
- On leaving, you must **re-establish** $R$.

O'Hearn's generalization is to let $R$ be a heap assertion (not just a store/variable assertion), so that **the resource can own a portion of the heap**, and entering/leaving a critical region becomes a literal transfer of *heap ownership* between a process and the resource — governed by the same disjointness machinery (`*`) as everything else in the logic.

### Worked example: a one-cell buffer

The book's example is small enough to hold in your head entirely, and it is the cleanest illustration in the whole book of what "ownership transfer" concretely means at the level of assertions. Two processes share a single-cell buffer via two procedures:

```
put(x) = with buf when ¬full do (c := x; full := true)
get(y) = with buf when full do (y := c; full := false)
```

At the level of the two client processes, the buffer's internal state is completely invisible — one process allocates a cell and hands it to `put`; the other calls `get`, uses the resulting cell, and disposes of it:

$$
\begin{array}{ll}
\{\mathrm{emp}\} & \{\mathrm{emp}\} \\
x := \mathrm{cons}(\ldots) ; & \mathrm{get}(y) ; \\
\{x \mapsto -,-\} \quad\parallel\quad & \{y \mapsto -,-\} \\
\mathrm{put}(x) ; & \text{“Use } y\text{”} ; \\
\{\mathrm{emp}\} & \mathrm{dispose}\ y; \{\mathrm{emp}\}
\end{array}
$$

Notice the shape: both processes' pre/postconditions are entirely in terms of `emp` and their own local cell — **the heap cell itself disappears from one process's view exactly when it's handed to `put`, and reappears in the other's view exactly when `get` returns it.** This is what "ownership transfer" means operationally: the *same physical heap cell* is, at different points in time, asserted to be owned by process 1, then by the resource `buf`, then by process 2. Nothing in the client-level view ever needs to assert facts about a cell it doesn't currently own — which is the entire payoff of local reasoning, now extended across a synchronization boundary.

Behind the scenes, the resource carries its own boolean `full` and pointer `c`, with the **resource invariant**:

$$
R \stackrel{\mathrm{def}}{=} (\mathit{full} \wedge c \mapsto -,-) \vee (\neg\mathit{full} \wedge \mathrm{emp})
$$

Read this invariant as a case split on ownership: *either* the resource currently owns a live cell (`full`, and the resource asserts the points-to fact about `c`), *or* it owns nothing (`¬full`, `emp`) — there is no third state, and crucially the invariant is a disjunction of two mutually exclusive heap-ownership claims, not a conjunction of unrelated facts.

The inference rule for critical regions makes $R$ explicit **inside** the critical region's proof and hidden **outside** it — this asymmetry is the whole mechanism:

```
                    {x ↦ −,−}
put(x) = with buf when ¬full do (
             {(R * x ↦ −,−) ∧ ¬full}      -- R made visible on entry
             {emp * x ↦ −,−}              -- case-split on R resolves to emp branch
             {x ↦ −,−}
             c := x; full := true
             {full ∧ c ↦ −,−}             -- now the "live" disjunct of R holds
             {R}                          -- R re-established — ownership handed to resource
             {R * emp})
           {emp}
```

Trace the ownership transfer explicitly: on entry, the process's own precondition `x ↦ -,-` is combined (via `*`) with the freshly-assumed resource invariant `R`; since `R`'s disjunction is resolved by `¬full` to its `emp` branch, the process momentarily "sees" exactly its own cell and nothing else — same footprint discipline as ever. By the end of the body, the process has given up its claim on that cell (it no longer appears in the postcondition) and the resource invariant `R` is re-established, now via its *other* disjunct (`full ∧ c ↦ -,-`) — the resource has, so to speak, absorbed the cell that the process used to own. `get` runs the same argument backward, extracting the cell from the resource's `full` branch back out to the client.

## The synthesis: what separation logic's whole apparatus buys you here

The reason this example is worth dwelling on, thin as the source material is, is that it's a distilled demonstration of the *general* claim the entire book has been building toward: **the separating conjunction, having been introduced purely to make sequential heap-mutation proofs concise, turns out to be exactly the right tool for expressing dynamic transfer of exclusive ownership** — a concept that shows up in concurrency (ownership of heap cells between processes and resources), but that you should recognize as the *same* underlying idea as: a Rust value moving out of one owner's scope into another's (`Box<T>` transferred by move, a `Mutex<T>`'s guard representing temporary, checked-out exclusive access), or a linear/affine type system's treatment of a resource that must be consumed exactly once.

If you're building a Rust-based verifier with Hoare-triple-style contracts, this section is a direct preview of what a **concurrent separation logic** extension to your system would need: resource invariants as first-class specification objects, an entry/exit rule that folds/unfolds the invariant via `*`, and — crucially — the same disjointness-checking machinery your sequential frame rule already needs, just applied at synchronization points instead of at every command. This is precisely the lineage that leads to later, more general treatments (rely/guarantee reasoning, concurrent abstract predicates) that the book's own bibliography gestures at in §1.2 but does not develop.

## Where this leads

This section is deliberately a preview, not a payload — Reynolds is showing you the *shape* of O'Hearn's extension (replace `∧` with `*` in the parallel rule; generalize Hoare's critical-region invariant to a heap assertion; let ownership move between processes and resources) without proving soundness or working a second example. Nothing later in *this* book (which ends at Chapter 6, on iterated separating conjunction, arrays, and the sorting/subset-list case studies) returns to concurrency — the fractional-permissions material in §1.11 is related (it's *also* about controlled, partial sharing of heap cells) but addresses read-sharing between processes under no ownership transfer, a different problem from the exclusive-ownership transfer described here. If your own interests trend toward reasoning about concurrent or effectful programs (rely/guarantee, session types, linear resource tracking in a type checker), this section is the seed of that whole later research program, condensed to its founding example.
