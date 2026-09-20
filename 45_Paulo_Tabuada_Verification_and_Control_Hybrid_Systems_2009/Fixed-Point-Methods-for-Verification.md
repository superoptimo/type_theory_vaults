---
title: Fixed-Point Methods for Verification
source: "Verification and Control of Hybrid Systems: A Symbolic Approach — Paulo Tabuada (2009)"
chapter: "Chapter 5: Verification"
pages: "43–50"
tags:
  - hybrid-systems
  - verification
  - fixed-points
  - simulation
  - bisimulation
  - abstract-interpretation
  - lattice-theory
---

[[book-guidelines|↩ Back to guidelines]]

# Fixed-Point Methods for Verification

## The problem you actually want to solve

Suppose you've built a model $S_a$ of a system — a piece of reactive software, a
protocol, whatever — and you have a specification $S_b$: a model of the
behaviors you're willing to allow. "Verification" here means checking

$$B^\omega(S_a) \subseteq B^\omega(S_b)$$

i.e., every infinite output string $S_a$ can produce is also a string $S_b$
allows. This is *behavioral inclusion*, written $S_a \preceq_B S_b$. It's the
most natural thing to ask for, and it's also the thing you cannot check
directly on any but the smallest systems: $B^\omega(S_a)$ and $B^\omega(S_b)$
are (generally infinite) sets of infinite strings, not data structures you can
enumerate and diff.

What you *can* compute on is the transition structure itself — states and
edges, not strings. Chapter 4 gave you **simulation**: a relation $R
\subseteq X_a \times X_b$ that, informally, lets you "play along" — every
move $S_a$ can make, $S_b$ can match, while staying output-compatible. The
punchline from Chapter 4 (Proposition 4.11, referenced again on p.44) is that
simulation *implies* behavioral inclusion always, and the converse holds too,
*provided* $S_a$ is nonblocking and $S_b$ is output-deterministic. Under those
assumptions, checking $S_a \preceq_S S_b$ (simulation preorder) is exactly as
good as checking $S_a \preceq_B S_b$ — and simulation, unlike behavioral
inclusion, is a *local*, state-and-transition-level condition. That's the move
this chapter is built on: turn a question about infinite strings into a
question about a finite relation you can grow by iteration.

Two things need to fall into place before that reduction is legal, and each
gets its own machinery:

1. **Nonblocking is a syntactic check** — scan for states with no outgoing
   transition. Easy, and Tabuada just asserts you fix $S_a$ if it fails
   (a reactive system that can get stuck is broken regardless of
   verification).
2. **Output-determinism of $S_b$ is not free** — most specifications you'd
   naturally write are *not* output-deterministic (two transitions out of the
   same state producing the same output but leading to different futures).
   This is where the **Myhill–Nerode construction** comes in: it shows you
   can always replace $S_b$ by a behaviorally-equivalent $S_c$ that *is*
   output-deterministic, so the assumption costs you nothing.

Once both hold, you're left with computing a simulation relation. That's
where the **monotone-operator / fixed-point** machinery takes over, and it's
the part of the chapter that matters most for anything you'll ever implement:
it is a two-line abstract-interpretation-style analysis, computed by
iterating a monotone map to its fixed point on a finite lattice — precisely
the pattern that shows up later as "compute reachable states," "compute a
maximal invariant," or "solve a safety game."

## Part 1 — Making the specification output-deterministic (Myhill–Nerode)

**What breaks without this.** If $S_b$ can be in a state $x_b$ with two
transitions on the *same* output symbol going to different successor states,
then "does $S_a$'s next output match some transition of $S_b$" stops being a
well-defined single successor to track — you'd have to track *sets* of
candidate $S_b$-states (a determinization / subset-construction problem, not
a simulation-checking problem). Rather than fold subset construction into the
simulation check, Tabuada does the determinization once, up front, as a
system transformation.

**The construction (Proposition 5.1, p. 44–45).** Given any system $S_b$,
build $S_c$ that is output-deterministic and behaviorally equivalent
($S_b \cong_B S_c$):

- Take $R$, the equivalence relation on finite behaviors $B(S_b)$ (finite
  output strings $S_b$ can produce) defined by: $y = y_0 y_1 \ldots y_k$ is
  $R$-equivalent to $y' = y_0' y_1' \ldots y_l'$ iff $y_k = y_l'$ (same last
  output symbol) **and** for every future output $\bar y \in Y_b$,
  $y\bar y \in B(S_b) \iff y'\bar y \in B(S_b)$ — i.e., $y$ and $y'$ admit
  exactly the same continuations. This is a textbook Myhill–Nerode
  right-congruence: two prefixes are equivalent exactly when they are
  indistinguishable by every possible future.
- $R$ has the key property $(y, y') \in R \implies (y\bar y, y'\bar y) \in R$
  for all $\bar y \in Y_b$ (5.2) — appending the same symbol to two
  equivalent strings keeps them equivalent, which is what lets you define
  transitions *on equivalence classes* rather than on strings.
- Define $S_c$: states $X_c = B(S_b)/R$ (the equivalence classes);
  initial states = classes of the length-1 behaviors $H_b(x_{b0})$;
  inputs $U_c = Y_b$; transition $x_c \xrightarrow{\bar y} x_c'$ when $x_c$
  is the class of some $y$ and $x_c'$ is the class of $y\bar y$; output map
  $H_c(x_c) = $ the last symbol of any representative of $x_c$.
- **Output-determinism falls out immediately**: two transitions out of the
  same class $x_c$ on symbols $u_c = u_c'$ land in classes containing
  $y\bar y$ and $y \bar y$ for the *same* $y$ and *same* $\bar y$ (by
  definition of the transition relation) — hence the same class. There's
  only one place to go.
- $B(S_c) = B(S_b)$ by construction, so $S_c \cong_B S_b$.

If $S_b$ is finite-state, $S_c$ is finite-state too — but the book flags
(footnote, p.45) that $|X_c|$ can be *exponential* in $|X_b|$, since
equivalence classes of strings are exactly the states of a subset-construction-
style determinization. This is the same blow-up you'd see turning an NFA into
a DFA, and for the same reason: Myhill–Nerode classes *are* the minimal DFA
states for a regular language, and this construction is that idea lifted to
systems with structured outputs instead of accept/reject.

**Grounding: this is literally DFA minimization/determinization.** If you've
implemented a lexer or a regex engine, you've built exactly this. A Rust
sketch — building $S_c$'s states as behavior-equivalence classes, represented
concretely by (for a finite-state $S_b$) a Myhill–Nerode table over reachable
"residual behaviors":

```rust
use std::collections::{HashMap, HashSet};

// Sb: explicit finite-state system with output map H_b.
struct Sb {
    // adjacency: (state, output_symbol) -> next_state (may be nondeterministic:
    // multiple next_states with the SAME output_symbol from the same state)
    trans: HashMap<(usize, char), Vec<usize>>,
    initial: Vec<usize>,
    output: HashMap<usize, char>, // H_b(x) — label on entering x
}

// The Myhill-Nerode class of a state is characterized, up to the depth we can
// observe, by the set of continuation-output-strings it admits. For a
// finite-state system this is decidable by iterated refinement (Moore-style
// partition refinement), which is exactly Hopcroft/Moore DFA minimization —
// output-determinizing Sb is subset-construction over Sb's `trans`, keyed by
// (set-of-Sb-states, output symbol) -> canonical class.
fn determinize(sb: &Sb) -> (Vec<HashSet<usize>>, HashMap<(usize, char), usize>) {
    let mut classes: Vec<HashSet<usize>> = Vec::new();
    let mut class_of: HashMap<Vec<usize>, usize> = HashMap::new();
    let mut trans_c: HashMap<(usize, char), usize> = HashMap::new();

    let mut frontier: Vec<HashSet<usize>> = vec![sb.initial.iter().cloned().collect()];
    while let Some(subset) = frontier.pop() {
        let mut key: Vec<usize> = subset.iter().cloned().collect();
        key.sort();
        if class_of.contains_key(&key) { continue; }
        let id = classes.len();
        class_of.insert(key.clone(), id);
        classes.push(subset.clone());

        // group outgoing transitions by output symbol -> union of successors
        let mut by_symbol: HashMap<char, HashSet<usize>> = HashMap::new();
        for &s in &subset {
            for ((from, sym), tos) in &sb.trans {
                if *from == s {
                    by_symbol.entry(*sym).or_default().extend(tos.iter());
                }
            }
        }
        for (sym, succ) in by_symbol {
            let mut succ_key: Vec<usize> = succ.iter().cloned().collect();
            succ_key.sort();
            let succ_id = *class_of.entry(succ_key.clone()).or_insert_with(|| {
                classes.push(succ.clone());
                classes.len() - 1
            });
            trans_c.insert((id, sym), succ_id);
            frontier.push(succ);
        }
    }
    (classes, trans_c)
}
```

Every reachable subset here is (by construction) a distinct output-history
class, and by definition the resulting `trans_c` is a function of `(class,
symbol)` — output-determinism is enforced *by the data structure*, not
checked afterward.

## Part 2 — Simulation as a monotone-operator fixed point

With $S_b$ output-deterministic (swap in $S_c$ if needed, then keep calling it
$S_b$), the reduction from Chapter 4 kicks in: $S_a \preceq_B S_b \iff
S_a \preceq_S S_b$. Now you need to *decide* $S_a \preceq_S S_b$, and,
ideally, *produce* the witnessing simulation relation.

### The operator $F$

Define $F : 2^{X_a \times X_b} \to 2^{X_a \times X_b}$ by: $(x_a, x_b) \in
F(W)$ iff

1. $H_a(x_a) = H_b(x_b)$ (outputs match now),
2. $(x_a, x_b) \in W$ (the pair itself is "currently believed good"),
3. for every transition $x_a \xrightarrow{u_a} x_a'$ in $S_a$ there exists a
   transition $x_b \xrightarrow{u_b} x_b'$ in $S_b$ with $(x_a', x_b') \in W$.

Read condition 3 carefully: it says every successor of $x_a$ has *some*
matching successor of $x_b$ whose pair is in $W$ — it does not require that
successor pair to already satisfy conditions 1–3 itself. $F$ is a
**one-step lookahead** operator: it takes your current *candidate* set $W$ of
"maybe-still-OK" pairs and tightens it by checking local consistency against
$W$.

This is precisely the shape of a monotone dataflow-analysis transfer
function: $F$ inspects a current approximation and *removes* pairs that fail
a local one-step check, never adding anything not implied by the previous
approximation and the fixed transition structure.

**Proposition 5.2 (two facts about $F$).**

1. **$F$ is monotone**: $Z \subseteq Z' \implies F(Z) \subseteq F(Z')$. Proof
   is immediate from the definition — enlarging $W$ only makes condition 3
   easier to satisfy for any fixed pair, and conditions 1–2 don't depend on
   $W$ except by intersection.
2. **$F$'s pre-fixed-points are exactly simulation relations**: $R$ is a
   simulation relation from $S_a$ to $S_b$ iff $R \subseteq F(R)$ **and**
   $X_{a0} \subseteq \pi_a(R \cap (X_{a0} \times X_{b0}))$ (every initial
   state of $S_a$ is matched by some initial state of $S_b$ in $R$). This is
   just unwinding the definition of simulation relation against the
   definition of $F$: the three simulation conditions (output match,
   transition-matching, initial-state coverage) split exactly into "$R
   \subseteq F(R)$" plus the separate initial-state side condition.

### Why the *maximal* fixed-point, and why start from the top

Tarski's fixed-point theorem (reviewed in the Appendix, pp. 191–193, which
this chapter leans on without restating) says: on a complete lattice, a
monotone function's fixed points form a lattice too, with a unique maximum
and minimum, and — this is the constructive part (Theorem A.5) — on a
*finite* lattice you can compute the extremal fixed points by plain
iteration: $\sup Y = \inf\{X, f(X), f^2(X), \ldots\}$ starting from the top
element $X$, or the dual starting from $\bot$.

$2^{X_a \times X_b}$ (ordered by $\subseteq$) is exactly such a finite
complete lattice when $S_a, S_b$ are finite-state. $F$ is monotone
(Proposition 5.2.1). So Tarski applies, and:

$$Z = \lim_{i \to \infty} F^i(X_a \times X_b) \tag{5.3}$$

is the **maximal fixed-point** of $F$, and by Proposition 5.2.2 it is
therefore the **maximal simulation-*candidate* relation** — and
$S_a \preceq_S S_b$ holds iff $X_{a0} \subseteq \pi_a(Z \cap (X_{a0} \times
X_{b0}))$.

**Why start from $X_a \times X_b$ (the top) and not $\emptyset$ (the
bottom).** This is one of the book's own flagged Key Questions, and the
answer is the crux of the whole method: $F$ is a *filtering* operator — it
never adds pairs, only removes ones that fail the local check relative to the
current candidate set. If you start from $\emptyset$, $F(\emptyset)$ checks
condition 3 against the empty set, which every transition trivially fails
(there's no successor pair in $\emptyset$ to match against), so
$F(\emptyset) = \emptyset$ immediately — you converge instantly to the
useless answer "nothing simulates," regardless of the true answer. You have
to start from the *entire* space and carve away pairs that are provably bad,
because "provably bad" is a positive fact you can establish in finitely many
steps (a transition with literally no matching successor), while
"provably good forever" is not something a single step can certify — it's
only certified in the limit, by *surviving* every round of carving. This is
the standard pattern for computing a *greatest* fixed point (as opposed to a
*least* one, discussed below for reachability-style problems): initialize to
$\top$, monotonically shrink.

Concretely: $(x_a, x_b) \notin F(W)$ either because outputs already mismatch,
or because some transition of $x_a$ has *no* candidate match in $W$. Once a
pair is removed for either reason, it can never come back (each iterate is a
subset of the previous one — that's monotonicity plus starting from the top).
So the sequence $X_a \times X_b \supseteq F(X_a\times X_b) \supseteq F^2(X_a
\times X_b) \supseteq \cdots$ is a decreasing chain in a finite lattice, hence
stabilizes in at most $|X_a \times X_b|$ steps, and each step costs at most
$O(|X_a||X_b|)$ work to check — giving the **polynomial-time**, $O(|X_a|^2
|X_b|^2)$-ish, computability claimed in Theorem 5.3. That polynomial bound is
the entire point of the reduction: an intractable-looking question about
infinite string sets becomes a terminating fixed-point iteration on an
explicit finite table.

### The operator $G$ — bisimulation

Strengthen $F$ to $G$ by adding a fourth, symmetric condition: for every
transition $x_b \xrightarrow{u_b} x_b'$ in $S_b$, there must *also* be a
matching $x_a \xrightarrow{u_a} x_a'$ in $S_a$ with $(x_a', x_b') \in W$.
Everything above goes through unchanged with $F \to G$: $G$ is monotone,
its pre-fixed-points are exactly bisimulation relations (given the matching
initial-state side conditions on *both* $X_{a0}$ and $X_{b0}$), and

$$Z = \lim_{i \to \infty} G^i(X_a \times X_b) \tag{5.4}$$

is the **maximal bisimulation relation**, computable in polynomial time for
finite-state systems (Theorem 5.6). The book flags one extra wrinkle:
*for infinite-state systems, (5.4) may not converge in finitely many
steps — it's only a semi-algorithm there.* This matters later: Part III
reuses this exact iteration (with $S_a$ compared against itself) as a
sub-procedure for building finite bisimilar abstractions of infinite-state
systems, where nontermination has to be dealt with by other means (order-
minimality, stability arguments, etc. — that's the subject of other topics in
this vault).

**Grounding: computing $F$'s maximal fixed point by iterated refinement.**
This is a direct analogue of computing a maximal invariant / greatest
post-fixed-point in an abstract interpreter, or Kanellakis–Smolka-style
bisimulation-partition refinement. Here it is over $X_a \times X_b$ directly
(matching the book's presentation, rather than the coarser partition-refinement
formulation used for quotienting):

```rust
use std::collections::HashSet;

#[derive(Clone)]
struct FiniteSystem {
    states: Vec<usize>,
    output: Vec<char>,                    // H(x) for x in states
    trans: Vec<(usize, char, usize)>,     // (from, input_symbol, to)
    initial: Vec<usize>,
}

/// Compute the maximal simulation relation Z from Sa to Sb, per (5.3):
/// Z = lim_i F^i(Xa x Xb), iterating from the TOP (full product), shrinking.
fn maximal_simulation(sa: &FiniteSystem, sb: &FiniteSystem) -> HashSet<(usize, usize)> {
    // Start at the top: every pair with matching current output.
    let mut w: HashSet<(usize, usize)> = sa.states.iter().flat_map(|&xa| {
        sb.states.iter().filter_map(move |&xb| {
            (sa.output[xa] == sb.output[xb]).then_some((xa, xb)))
        })
    }).collect();

    loop {
        let next: HashSet<(usize, usize)> = w.iter().cloned().filter(|&(xa, xb)| {
            // condition 3: every Sa-transition out of xa has a matching
            // Sb-transition into a pair still (currently) in W.
            sa.trans.iter()
                .filter(|&&(from, _, _)| from == xa)
                .all(|&(_, ua, xa_next)| {
                    sb.trans.iter().any(|&(from_b, ub, xb_next)| {
                        from_b == xb && ub == ua && w.contains(&(xa_next, xb_next))
                    })
                })
        }).collect();
        if next == w { return w; }   // fixed point reached
        w = next;                    // monotone shrink — terminates in <= |Xa||Xb| rounds
    }
}
```

Swap the inner `all(...)` check to *also* require the symmetric condition
(every $S_b$-transition out of $x_b$ matched by some $S_a$-transition) and
you have $G$ instead of $F$ — the maximal bisimulation.

A tiny worked instance, in the spirit of the book's bus-fare-machine example
(Example 5.5, p.47): $S_a$ = a machine with states \{idle, swiped, paid\} that
can `swipe` (idle → paid, output `ding`) or `drop-quarter` (idle → paid,
output `dong`); $S_b$ = a stricter spec with only `idle → ding` on `swipe`.
Running the iteration: pairs like `(idle_a, idle_b)` survive (outputs match,
`swipe` has a match); a pair like `(paid-via-quarter_a, ding-state_b)` gets
carved away at the very first output-mismatch check, exactly the way the
book's Figure 5.3/5.5 show the dark "surviving" region shrinking over two or
three rounds before stabilizing.

## Why this belongs in the "fixed point" family, not "search" or "model checking"

It's worth being explicit about what makes this a *fixed-point* algorithm
rather than, say, a graph search: the answer isn't "reachable from a start
state" (that's a least-fixed-point / forward-reachability computation,
starting from $\bot$ and growing — the shape used later in Chapter 6 for
*reachability games*, via a dual operator $G_W$ with a *minimal* fixed-point).
Simulation and bisimulation are **maximal**-fixed-point computations: you're
certifying that a relation survives *every* future step, which is a
universally-quantified, "nothing goes wrong forever" property — the same
logical shape as a *safety invariant*. That's exactly why the iteration has
to start from the top and shrink: it's greatest-fixed-point semantics, dual
to the least-fixed-point semantics of reachability. Chapter 6's safety games
reuse operator $F$ almost verbatim (as $F_W$) for exactly this reason, while
its reachability games need the dual, minimal-fixed-point construction.

## Where this leads

This chapter is the book's computational engine, reused twice more directly:
Chapter 6 lifts $F$ and $G$ to $F_C$ and $G_C$ for *simulation games* and
*bisimulation games* (controller synthesis under adversarial disturbance
inputs), and to $F_W$/$G_W$ for safety/reachability games — same monotone-
operator-on-a-finite-lattice pattern, just with the controllable/uncontrollable
input split baked into the transition-matching condition. Part III's exact
abstraction results (Chapters 7–8) reuse the $G$-iteration as a sub-routine —
run $S$ against itself — to compute the maximal bisimulation used to build a
finite quotient system, with the caveat (flagged above) that termination
there needs extra structure (order-minimality, definability) because the
state space is no longer finite.

More broadly, this is a clean, self-contained instance of the abstract-
interpretation pattern this vault keeps returning to: pose a soundness
property as a fixed point of a monotone operator on a complete lattice
(here, the powerset lattice $(2^{X_a \times X_b}, \subseteq)$), invoke Tarski
to guarantee the extremal fixed point exists and is reachable by iteration,
and get termination/complexity for free from finiteness of the lattice — the
same reasoning that underwrites reachability analysis, dataflow analysis, and
CEGAR-style abstraction-refinement loops in general. The Appendix's Theorem
A.5 (sup-continuity on a finite lattice is automatic) is the fact that quietly
licenses every "iterate a monotone operator until it stabilizes" algorithm in
this book, including the safety-invariant and Horn-clause-style invariant-
generation algorithms this pattern generalizes to: $F$ and $G$ here are a
two-state-system special case of exactly the Galois-connection / abstract-
lattice / domain-propagation machinery (over-approximate by a monotone
transfer function, iterate to a fixed point, get soundness from the lattice
structure alone) that a general abstract interpreter or Horn-clause solver
applies to a single, possibly infinite, program's state space.
