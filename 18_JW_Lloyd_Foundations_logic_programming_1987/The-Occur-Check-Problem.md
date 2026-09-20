---
title: The Occur Check Problem
source: Lloyd, "Foundations of Logic Programming" (1987)
chapters: Chapter 1, §4 (pp. 20–26); Chapter 2, §7 (pp. 44–46)
tags: [occur-check, unification, soundness, infinite-terms, difference-lists]
---

[[book-guidelines|↩ Back to guidelines]]

## A soundness proof with an asterisk

[[SLD-Resolution]] proves Theorem 7.1: every computed answer is a correct answer. This is presented as an unconditional soundness theorem — but Lloyd immediately follows it with a section confessing that the theorem is **false** for [[Unification#The unification algorithm|the unification algorithm]] every real PROLOG system actually ships with. This article is about that gap: a genuine, load-bearing discrepancy between the formal theory (which assumes [[Unification]]'s occur check is always performed) and practical implementations (which, for performance reasons, virtually never perform it). Understanding exactly *where* and *why* this gap opens up is a direct rehearsal for a question your own verifier will face constantly: when is an optimization to a checking algorithm merely "conservative" (loses completeness but stays sound), and when does it silently break soundness itself?

## Why the occur check is expensive enough to skip

Recall from [[Unification]] that step 3 of Robinson's algorithm requires checking, before binding $v \mapsto t$, that $v$ does not occur in $t$. Lloyd proves (via the Corbin–Bidoit family of examples) that this check is not a minor constant-factor cost: unifying $p(x_1,\ldots,x_n)$ against $p(f(x_0,x_0),\ldots,f(x_{n-1},x_{n-1}))$ forces intermediate substitutions whose printed size — and whose occur-check cost at the final step alone — is exponential in $n$. This is *inherent*, not an artifact of a naive implementation: any algorithm that explicitly materializes the final unifier is worst-case exponential. Faced with this, essentially every production PROLOG system made the same engineering trade-off: **drop the occur check**, accept that unification is no longer logically correct in the rare cases where it matters, and rely on programmers to avoid those cases.

This is the same category of trade-off as a compiler's optimizer skipping a provably-safe-but-expensive check (e.g. exhaustive alias analysis) in favor of a cheap heuristic that is *usually* right — except here the stakes are sharper, because the "check" being skipped isn't merely an optimization pass, it's the thing that keeps the fundamental logical soundness theorem true.

## What breaks, precisely: circular bindings

Without the occur check, unifying `p(X,X)` with `p(Y,f(Y))` "succeeds," producing the binding `X = f(X)` — not a finite first-order term at all, but a description of an infinite, self-referential structure ($f(f(f(\cdots)))$). Lloyd's minimal counterexample makes the soundness failure concrete:

```prolog
test :- p(X, X).
p(X, f(X)).
```
`?- test.` **succeeds** under naive (occur-check-free) unification, yet `test` is demonstrably **not** a logical consequence of this program (its least Herbrand model $M_P$ contains no ground instance of `test` — see [[Declarative-Semantics-of-Definite-Programs]]). This is a direct violation of Theorem 7.1. Lloyd distinguishes two failure modes, worth keeping conceptually separate because they have different practical signatures:

1. **A circular binding is constructed but never used again.** The `test` example above: the system silently answers "yes" to a false query. This is the more insidious case — *there is no error message, no crash, just a wrong answer*, exactly the kind of silent-unsoundness bug that is hardest to catch in a verification tool, because nothing looks broken until you audit the actual logical content of the result.
2. **A previously-constructed circular binding is used again** — e.g. `test :- p(X,X). p(X,f(X)) :- p(X,X).` — here the system doesn't answer wrongly, it **loops forever** trying to traverse/print an infinite structure. This fails loudly (non-termination) rather than silently, but is still a correctness failure relative to the specification.

## Difference lists: where this bites in real programs

The pathological examples above look contrived, but Lloyd shows the danger arises naturally in a widely-used, genuinely efficient programming idiom: **difference lists**, terms of the form $x{-}y$ representing "the list obtained by taking $x$ and removing its trailing sublist $y$" (so $x{-}x$ represents the empty list, and $34.56.12.x{-}x$ represents $[34,56,12]$). Two compatible difference lists ($x{-}y$ and $y{-}z$, sharing the middle variable $y$) concatenate in **constant time**:
```prolog
concat(X-Y, Y-Z, X-Z).
```
This is precisely the trick behind O(1) list-append via "hole" pointers, familiar from any zipper- or rope-based data structure implementation. But it is dangerous without the occur check:
```prolog
test :- concat(U-U, V-V, a.W-W).
concat(X-Y, Y-Z, X-Z).
```
`?- test.` succeeds under naive unification — the system believes the empty list concatenated with the empty list is `[a]`. The `qsort` variant using implicit difference-list accumulation (`qsort(nil, X-X).`) has the same latent risk: `?- qsort(nil, a.Y-Y)` "succeeds" with the circular binding `Y = a.Y`, and only fails visibly when you try to *print* the answer. Lloyd's proposed mitigations — a disciplined "protect entry points with a checked top-level predicate" convention, or (better) a preprocessor that statically identifies which clauses are occur-check-risky and inserts the full check only there — are early, hand-rolled versions of exactly the kind of **selective, statically-justified verification** your own compiler will need: run the expensive check *only* where a cheap static analysis can't already rule out the danger, rather than either always paying the cost or never paying it.

## Grounding: this is exactly the unification bug class in HM-style inferencers

```rust
// The naive ("fast but unsound") unifier — exactly what real Prolog does,
// and exactly the bug class that shows up if you forget the occur check
// in your own type-inference engine's unifier.
fn unify_unsafe(a: &Term, b: &Term, subst: &mut HashMap<u32, Term>) -> bool {
    let a = resolve(a, subst);
    let b = resolve(b, subst);
    match (&a, &b) {
        (Term::Var(v1), Term::Var(v2)) if v1 == v2 => true,
        (Term::Var(v), t) | (t, Term::Var(v)) => {
            // BUG: no occurs(*v, t) check here — this is the whole problem.
            subst.insert(*v, t.clone());
            true
        }
        (Term::App(f, xs), Term::App(g, ys)) if f == g && xs.len() == ys.len() => {
            xs.iter().zip(ys).all(|(x, y)| unify_unsafe(x, y, subst))
        }
        _ => false,
    }
}
```
If you have ever debugged a hand-rolled Hindley–Milner implementation that *hangs* (or, worse, silently accepts an ill-typed program) on a recursive-looking type annotation, you have hit this exact bug — `let rec f x = f` without an explicit recursive-type/µ-binder produces exactly the "occurs" case unification is supposed to reject, and a unifier missing the check will either infer a nonsensical infinite type or loop trying to print it.

**In Lean**, the kernel's `isDefEq`/unification machinery ([[Unification]]'s discussion of pattern unification) *must* perform the equivalent of an occur check when assigning a metavariable — assigning `?m := f ?m` would be exactly this pathology lifted to the metavariable level, and a real elaborator's assignment step explicitly rejects (or defers, if under a binder in a way that might later resolve) any solution where the metavariable occurs in its own assigned value. The design question this article poses at the first-order level — "is skipping the occur check ever safe, and under what static conditions?" — recurs verbatim, with higher stakes, at the metavariable level: a **trusted kernel** cannot skip this check the way a PROLOG engine does, because kernel unsoundness is unacceptable, so Lean's kernel pays the (typically much smaller, because well-typed terms are far less pathological than arbitrary first-order terms) occur-check cost unconditionally, while an *elaborator*'s heuristic unifier (outside the trusted kernel) may take shortcuts, provided the kernel re-checks everything at the end.

## Where this leads

- This gap is precisely why [[Semantics-of-Perpetual-Processes]] (chapter 6) exists as a serious piece of theory rather than a footnote: instead of simply forbidding circular bindings, Lloyd builds a rigorous topological semantics (the complete Herbrand universe, a compact metric space of *genuinely infinite* terms) in which some of what naive occur-check-free unification produces turns out to have a legitimate mathematical meaning — "computable at infinity" — while other instances (like `p(f(x)) <- p(f(x))`) remain excluded by a careful definition even in that generalized setting.
- **Directly load-bearing for your trusted-kernel design:** this article is the case study for the general principle "a performance-motivated shortcut in a checking algorithm is only as safe as the domain restriction that justifies skipping the check" — apply the same scrutiny to any shortcut your elaborator's unifier takes (occur checks, indeed, but also things like skipping universe-level checks or short-circuiting definitional-equality unfolding) before assuming the kernel doesn't need to re-verify it.
- Connects back to [[SLD-Resolution]]'s Theorem 7.1 as the theorem whose *hypotheses* (a properly occur-checked mgu) this article shows are silently violated by every practical PROLOG implementation — a clean example of the gap between a "reference semantics" proof and a "what actually ships" system.
