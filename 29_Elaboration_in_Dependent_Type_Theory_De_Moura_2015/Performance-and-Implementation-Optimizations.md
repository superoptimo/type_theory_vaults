---
title: Performance and Implementation Optimizations
source: Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)
chapter: Section 3.2–3.3, pp. 12, 16–17
tags: [type-theory, elaboration, lean, performance, locally-nameless, de-bruijn-indices]
---

[[book-guidelines|↩ Back to guidelines]]

## Why performance is a design constraint, not an afterthought

Every other article in this vault treats elaboration as a *correctness* problem: what does it mean for a partial term to have a unique, well-typed completion? But an elaborator that is correct and unusably slow is not actually useful — and the paper is candid that one specific representational choice, made purely for *implementation simplicity*, threatened to become exactly that kind of trap. This article is about the moment where an elegant design decision collided with real-world performance, and the narrow, surgical fix that resolved it.

The decision in question is the **locally nameless** representation of terms (covered in depth in [[Term-Representation-and-Core-Data-Structures]]): free variables carry a globally unique identifier and a type, while bound variables are represented positionally by a de Bruijn index — a number counting how many binders out from the variable's occurrence you have to walk to reach the binder that introduced it. The appeal is that this eliminates a whole category of bugs around variable capture and context bookkeeping that plague naive named-variable implementations. But the paper is explicit about the cost: "while the locally nameless approach simplifies many aspects of the code, the operations of abstracting and instantiating variables can be costly."

## The concrete bottleneck: `instantiate` and `abstract`

To understand why, you need the two operations the locally nameless representation forces you to perform constantly during elaboration:

- **`instantiate`** — when you need to look inside a $\lambda$- or $\Pi$-binder's body (e.g., to type-check it, or unify it against something), you cannot safely work with a body that still contains a bound variable "pointing out" of any binder scope. So you replace the bound variable (de Bruijn index 0, referring to the binder you just opened) with a fresh free variable. The paper calls a term with such an out-of-scope bound variable one with a *dangling bound variable* — e.g., in $\lambda x{:}\mathrm{Type}, f\,x\,(g\,x)$ there is no dangling variable, but the bare subterm $f\,x\,(g\,x)$ on its own (outside the $\lambda$) does have one. Every major operation — type inference, normalization, unification — maintains the invariant that it never touches a term with dangling bound variables, and `instantiate` is what restores that invariant when you step into a binder.
- **`abstract`** — the inverse operation: given a free variable $\ell$ and a term $t$, replace occurrences of $\ell$ in $t$ with the bound variable at de Bruijn index 0, re-binding it. This is what you do when you're done working under a binder and need to re-close the term.

These two operations are, as the paper puts it, "essentially the only ones that have to deal with de Bruijn indices" — every other piece of machinery is de-Bruijn-agnostic once instantiation and abstraction have done their job. But naively, both operations must walk the *entire* term to find and rewrite every occurrence of the target variable, even in subterms that don't mention it at all. For a term of size $n$ with $m$ binders, that's $O(nm)$ time just to keep the "no dangling bound variables" invariant intact while traversing. The prior work the paper builds on (Avigad et al.'s earlier system, cited as [21]) had already mitigated part of this by generalizing `abstract`/`instantiate` to handle whole *sequences* of binders at once — useful for terms like $\lambda x_1{:}A_1, \lambda x_2{:}A_2, \ldots, \lambda x_n{:}A_n, t$ where you'd otherwise redo the traversal once per binder. But even with that mitigation, the paper reports that these two operations remained "a performance bottleneck for several files in the Lean standard library" — a strong signal that the asymptotic cost, not just a constant factor, needed addressing.

**Why this matters practically:** think of an interpreter that has to re-scan an entire abstract syntax tree every time it enters or exits a function scope, even for the vast majority of subtrees that don't reference the variable being bound. If your programs are large — and Lean's own standard library, with its long chains of nested lemmas and definitions, is exactly this kind of large program being "run" through the elaborator — that redundant traversal compounds badly.

## The fix: two cheap annotations that let the traversal skip subtrees

The optimization the paper introduces is deliberately minimal — not a redesign of the representation, just two small pieces of metadata attached to each term that let `instantiate` and `abstract` *decide not to visit* subtrees that can't possibly need rewriting.

**For `instantiate`:** for every term $t$, store a bound $B$ such that every de Bruijn index occurring anywhere in $t$ is strictly less than $B$ — i.e., $t$'s indices all lie in $[0, B)$. This bound is cheap to maintain incrementally as terms are built:

$$
B(\text{de Bruijn variable } n) = n + 1, \qquad
B(t\,s) = \max(B_t, B_s), \qquad
B(\lambda x{:}t, s) = \max(B_t,\ B_s - 1)
$$

Once every term carries its own $B$, `instantiate`'s job of replacing the bound variable at some target index $k$ becomes a quick check: if $k \geq B$, then no subterm can possibly contain that index (they're all bounded below $B$), so the whole subtree can be skipped without descending into it at all.

**For `abstract`:** a single boolean bit per term, set to true iff the term contains *any* free variable at all. `abstract`'s job is to find occurrences of one specific free variable $\ell$ and rebind them — if a subterm's bit says "no free variables anywhere in here," the traversal can skip it immediately, since it's certain $\ell$ (a free variable) can't occur inside.

Both tricks share the same shape: replace "must traverse to find out" with "cheap precomputed summary lets you skip." This is the same idea behind, e.g., a Rust `HashSet` intersection short-circuiting once one operand is exhausted, or a Python AST optimizer pre-tagging subtrees as "constant, no need to re-visit," or — closer to home for a Lean-adjacent reader — the way an incremental type checker might memoize "this subterm is already in normal form, skip it." None of these are conceptually deep; the paper's own framing is that this is "a very simple complementary optimization," and its power comes entirely from being cheap to compute and applied relentlessly at every recursive step.

## The measured payoff

The paper backs this up with a concrete before/after benchmark on a real workload, not a synthetic microbenchmark: compiling the entire Lean standard library — 172 files, 41,700 lines of Lean code — on an Intel Core i7 3.6GHz machine with 32GB RAM.

| | Compile time |
|---|---|
| With the $B$-bound and free-variable-bit optimizations | 71.06 seconds |
| Without them | 2,189.97 seconds |

That's roughly a **30x** speedup, and it's the paper's own justification for calling these optimizations "crucial to our implementation" rather than a nice-to-have polish pass. Without them, elaborating the standard library would take over half an hour instead of just over a minute — the kind of gap that changes whether an interactive development loop (edit a proof, recompile, see the error) stays usable at all.

## How this connects back into the rest of the algorithm

This topic sits underneath almost everything else in the paper's internals, which is why it's easy to overlook: the constraint-simplification procedure ([[The-Constraint-Simplification-Procedure]]), the preprocessing phase ([[The-Preprocessing-Phase]]), and the constraint-solving loop ([[The-Constraint-Solving-Procedure]]) all constantly create, tear apart, and rebuild terms as they open binders to inspect bodies, unify under $\lambda$/$\Pi$, and instantiate metavariable solutions. Every one of those operations ultimately bottoms out in `instantiate` and `abstract` from [[Term-Representation-and-Core-Data-Structures]]'s core data structures. A representation choice made for *implementation clarity* (locally nameless, no named-variable capture bugs) turned out to need a *performance* patch precisely because it sits on this critical path — a reminder that in a system built from many interacting layers, a decision's cost is often paid several layers away from where the decision itself was made.

**On source material:** this is a narrower topic than most others in the Topic List, and the paper treats it as a single self-contained aside at the end of Section 3.3 (pp. 16–17) rather than a full section of its own — this article covers all of the material the source actually provides (the locally-nameless cost discussion from Section 3.2 that sets up the problem, and the $B$-bound/free-variable-bit fix with its benchmark from Section 3.3), without padding beyond what's there.
