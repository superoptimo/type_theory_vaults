---
title: Empirical Evaluation
source: "ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses (Frohn & Giesl, 2023)"
chapters: "Sect. 5, Experiments subsection (pp. 21–23)"
tags: [chc, sat-smt-csp, benchmarking, refutation-length, acceleration]
---

[[book-guidelines|↩ Back to guidelines]]

## What a calculus paper still has to prove empirically

A calculus can be sound, refutationally complete, and elegant on paper — see [[Metatheoretic-Properties-of-ADCL]] — and still be useless in practice if the theoretical machinery doesn't pay off on real inputs. What breaks without an empirical section: nothing in ADCL's soundness or completeness proofs says *how fast* it finds a refutation, or whether the acceleration machinery's overhead outweighs its benefit on typical verification-condition sets. This section is where the paper has to make good on the claim in its own introduction — that acceleration collapses thousands of resolution steps into a handful — with actual numbers, against actual competing tools, on an actual benchmark suite.

## The benchmark set: CHC Competition '22, category LIA-Lin

LoAT (the implementation of ADCL) is restricted to integer arithmetic, so the evaluation uses the **LIA-Lin** category from the CHC Competition '22 — linear CHCs over linear integer arithmetic drawn from real program-verification tasks. Two practical wrinkles surfaced immediately:

- Many examples use **Bool-typed variables** and the `div`/`mod` operators, despite the category nominally being pure LIA. The paper's response to each differs:
  - `div`/`mod`: **72 examples excluded outright** — LoAT's implementation doesn't support them.
  - `Bool` variables: since these appear in *most* remaining examples, excluding them too would have gutted the benchmark. Instead the authors extended LoAT with a **rudimentary Boolean-acceleration technique** (below), rather than dropping the examples.
- Of the original set, **427 examples remain** after excluding the `div`/`mod` cases — this is the population every subsequent number in this section is drawn from. Of these, **209 use Int only**, and the rest mix Int and Bool.

This is a good illustration of a recurring gap between a calculus's abstract presentation and its implementation's actual coverage: Definition 4's acceleration function is stated for an arbitrary background theory $A$, but *closed-form computation* — the concrete algorithm that realizes `accel` — is only worked out for integers via recurrence solving (see [[Loop-Acceleration]]). Booleans needed a bespoke extension.

## Closed-form acceleration for Boolean variables

The paper adapts the acceleration calculus of prior work ([23], already discussed for integers in [[Loop-Acceleration]]) to handle Booleans, under real restrictions worth naming precisely — this is the concrete mechanism a Rust-based CSP kernel would need to replicate for a Boolean/bitvector abstract domain:

1. **Determinism required.** For a recursive CHC $\varphi := F(\vec X) \wedge \psi \Rightarrow F(\vec Y)$, there must be a substitution $\theta$ such that $\psi \models_A \vec Y = \theta(\vec X)$ and $V(\theta(\vec X)) \subseteq \vec X$ — i.e. each loop iteration's next-state must be a deterministic function of its current state, not a nondeterministic relation. Without determinism, there is no single "$N$-th iterate" to compute a closed form for.
2. **A computable closed form.** LoAT needs a vector $\vec C$ with $\vec C \equiv_A \theta^N(\vec X)$ — a formula for "$\theta$ applied $N$ times," parametric in $N$. For **integer** variables this comes from recurrence solving (e.g. a variable incremented by a constant each iteration has a closed form linear in $N$). For **Boolean** variables $B$, LoAT can only construct a closed form if either:
   - there is some $k \in \mathbb{N}$ such that $\theta^k(B)$ no longer mentions any Boolean variable (the recursion "bottoms out" into a fixed value after finitely many steps), or
   - $\theta^k(B) = \theta^{k+1}(B)$ for some $k$ (the value reaches a fixed point).
3. **Restricted to theory-agnostic techniques in mixed problems.** Once Booleans are in play, only **monotonic increase** and **monotonic decrease** (from [23]) may be used — the richer, theory-specific acceleration techniques available for pure-integer loops don't carry over.

```rust
// Sketch of the determinism + closed-form gate LoAT applies before accelerating
// a recursive CHC with Boolean-typed state variables.
enum ClosedForm {
    IntRecurrence(Polynomial),           // via recurrence solving
    BoolStabilizes { after_k: u32 },     // θ^k(B) has no Bool deps, or θ^k(B) = θ^(k+1)(B)
    NotComputable,                       // acceleration must fall back / fail here
}

fn try_accelerate(theta: &Substitution, vars: &[Var]) -> Option<ClosedForm> {
    if !theta.is_deterministic(vars) { return None; }   // requirement (1)
    // ... probe for (2), restricted to monotonic-increase/decrease under Bools (3)
    todo!()
}
```

**What breaks without this gate:** accelerating a nondeterministic or non-stabilizing Boolean recursion would either be unsound (claiming a closed form that doesn't cover all reachable ground instances) or simply undefined (no finite formula exists). The paper is explicit that this is a genuine limitation, not a simplification of convenience — it explicitly notes it *cannot* reuse an existing over-approximating technique for Boolean acceleration ([46]) because ADCL's soundness depends on `accel` being *exact*, not an over-approximation (recall Definition 4's equality $\mathrm{grnd}(\mathrm{accel}(\varphi)) = \bigcup_{n\ge1}\mathrm{grnd}(\varphi^n)$, not merely $\supseteq$).

## Head-to-head comparison: solved instances

LoAT was run against **Spacer** (via Z3), **Eldarica** (both its default configuration and an `Eld. Acc.` configuration with acceleration-as-preprocessing enabled), **Golem** (using its TPA implementation, since Z3's own Spacer outperformed Golem's built-in Spacer in their tests), and **Z3's BMC**. Timeouts: 300s wallclock, 1200s CPU, 128GB memory, run on StarExec.

The results split the 427 examples into two populations — **Int only** (209 examples) and **Int & Bool** (all 427) — because LoAT's acceleration strength is fundamentally an integer-arithmetic capability:

| Tool | Int only — unsat solved (unique) | Int & Bool — unsat solved (unique) |
|---|---|---|
| **LoAT** | 30, 5 (5) | 78, 11 (5) |
| Z3 BMC | 24, 1 (1) | 84, 5 (5) |
| Spacer | 24, 0 (0) | 79, 2 (2) |
| Eldarica | 23, 0 (–) | 53, 0 (–) |
| Golem TPA | 15, 0 (0) | 56, 0 (0) |
| Eld. Acc. | 21, – (0) | 56, – (4) |

("unique" = examples only that one tool solves; the paper disregards Eld. Acc. in the unique-count comparison since it would be comparing two configurations of the same underlying algorithm against each other, but gives its numbers in parentheses if you substitute it in for plain Eldarica.)

Reading these honestly rather than triumphantly: **on Int-only problems, LoAT dominates** both in raw solved count (30 vs. the next-best 24) and unique contributions (5, tied only by itself). **On the mixed Int & Bool set, LoAT is still the strongest at unsat but the margin narrows** relative to Z3 BMC (78 vs. 84) — and the paper is candid about why: "the core of LoAT's approach are its acceleration techniques, which have been designed for integers," while Spacer's algorithm (related to GPDR, generalizing IC3 to CHCs over arbitrary theories) and BMC (theory-agnostic entirely) don't have that integer-specific bias. This is a good discipline to notice: the paper doesn't claim uniform superiority, it identifies *precisely which structural feature of its own technique* explains where the advantage is largest and where it shrinks.

A runtime-vs-proofs-found curve (Fig. 2, right) adds a temporal dimension: LoAT finds 73 unsat proofs within just 8 seconds — the fastest early lead of any tool — with Z3 BMC catching up by 12–14 seconds and eventually inching ahead (74 vs. 73), and Spacer only catching up to LoAT's count after 260 seconds. So LoAT's advantage is front-loaded: it wins decisively on "how fast can you get most of the easy-to-medium wins," even where its final solved-count tie or slight loss suggests otherwise. **Neither LoAT nor any competing tool in this evaluation proves satisfiability** — the comparison is unsat-only, consistent with LoAT's implementation being restricted to that side (see [[Implementing-ADCL-in-LoAT]]).

## Refutation-length comparison: the paper's central empirical claim

The most direct test of the paper's motivating idea — that acceleration collapses proof length — is **Table 1**, restricted specifically to the instances that *only LoAT* can solve (the reasoning being that any instance other tools can also solve is presumably one where a short, non-accelerated refutation already exists, so it wouldn't showcase the technique).

To measure "how many resolution steps *would* be needed with original clauses alone," the authors instrument every predicate with an extra counter argument $c$: each fact's condition gets $c=1$ appended, each rule's condition gets $c' = c+1$ appended, and the value of $c$ extracted from the SMT model at the query gives exactly the original-clause proof length — a neat trick for measuring proof length via constraint solving rather than by actually materializing the (potentially astronomically long) proof.

| Example | LoAT's refutation (accelerated, steps) | Original refutation (steps) |
|---|---|---|
| chc-LIA-Lin_043.smt2 | 6 | 965,553 |
| chc-LIA-Lin_045.smt2 | 2 | 684,682,683 |
| chc-LIA-Lin_047.smt2 | 3 | 72,536 |
| chc-LIA-Lin_059.smt2 | 3 | 100,000,001 |
| chc-LIA-Lin_154.smt2 | 2 | 134,217,729 |
| chc-LIA-Lin_358.smt2 | 12 | 400,005 |
| chc-LIA-Lin_362.smt2 | 12 | 400,005 |
| chc-LIA-Lin_386.smt2 | 15 | 600,003 |
| chc-LIA-Lin_401.smt2 | 8 | 200,005 |
| chc-LIA-Lin_402.smt2 | 4 | 134,217,723 |
| chc-LIA-Lin_405.smt2 | 9 | 100,012 |

This is the same phenomenon Example 1 illustrated abstractly (10001 steps collapsing to 3) now shown across eleven real, independently-sourced benchmark instances, with reductions ranging from roughly $10^4\times$ up to over $3\times10^8\times$ (`chc-LIA-Lin_045`: 2 vs. 684,682,683). The pattern across the table — single-digit to low-double-digit accelerated proofs against original proofs in the hundreds of thousands to hundreds of millions — is exactly what makes these instances **solvable at all** within the timeout: an SMT-backed proof search that had to explore hundreds of millions of ordinary resolution steps would simply never terminate in 300 seconds, no matter how fast the underlying solver is per-step. Acceleration isn't a constant-factor speedup here; it's the difference between decidable-in-practice and not.

## Where this leads

This section closes the loop the paper opened with in its very first example: [[Constrained-Horn-Clauses-(CHCs)]] introduced the 10001-vs-3-step illustration as motivation, and Table 1 is that same claim validated on real, independently-produced benchmark instances rather than a single hand-picked toy. It also validates two engineering decisions documented in [[The-ADCL-Calculus]] and [[Implementing-ADCL-in-LoAT]]: that redundancy-guided, on-the-fly acceleration (rather than exhaustive resolution) is not just theoretically elegant but the *load-bearing reason* certain instances are solvable within any realistic timeout at all.

For the standing project's CSP-kernel and abstract-interpretation goals (`sat-smt-csp`, `static-analysis`): this evaluation is a concrete existence proof that integrating a loop-acceleration primitive into a resolution/clause-learning search — rather than treating acceleration as a separate preprocessing pass, à la Eldarica's `Eld. Acc.` configuration — yields a qualitatively different reachability-analysis capability, not merely a faster one. The Boolean-acceleration gate above is also a directly transferable design pattern: any accelerated abstract-domain transfer function needs the same determinism-and-closed-form-existence check before it can soundly summarize a loop, whether the domain is integers, Booleans, or the automata-based abstract data structure domains named in the standing project's CSP kernel goals.
