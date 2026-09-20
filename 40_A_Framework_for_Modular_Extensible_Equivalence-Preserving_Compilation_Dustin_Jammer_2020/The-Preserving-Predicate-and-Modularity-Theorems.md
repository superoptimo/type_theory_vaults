---
title: The Preserving Predicate and Modularity Theorems
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "2 Concepts of Pyrosome; 3.3 Framework Proof Structure"
pages: "15–17, 27–29"
tags: [type-theory, automated-reasoning, modularity, proof-engineering]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem a naive proof runs into

Start with a completely standard proof attempt, the kind you'd write without Pyrosome at all: show that the CPS compiler for STLC (from [[The-Problem-of-Extensible-Compiler-Verification]]) preserves equivalence. You'd do this by induction on the derivation of $\Gamma \vdash_{\mathrm{STLC}} e_1 = e_2 : A$, which — because STLC's equational theory is the closure described in [[Language-Specifications-as-Equational-Theories]] — has cases for reflexivity, transitivity, symmetry, congruence, and beta. The first three go through "for free" (trivially, or by the inductive hypothesis); congruence goes through because compilers are substitution-homomorphisms by construction (see [[Compilers-as-Finite-Maps]]). **The only case that actually depends on STLC's specific rules, or the specific CPS compiler, is beta.**

That observation is the whole insight of this chapter, stated as a diagnosis before it's stated as a theorem: **a proof by induction on the full equivalence relation is 90% boilerplate and 10% content, but the boilerplate 90% is exactly what gets re-derived from scratch every time you extend the language**, because the induction's *statement* — "for all STLC terms, compilation preserves equivalence" — says literally nothing about a term that mixes STLC constructs with some new feature's constructs. Add product types, and you don't get to reuse the STLC induction as a lemma inside a new, larger induction; the old theorem's universal quantifier ranges only over the old syntax.

**What breaks without a fix:** every time you add a language feature, you re-derive reflexivity, transitivity, symmetry, and congruence for the *entire enlarged language*, from scratch, even though nothing about those four cases actually changed. This is the concrete mechanism behind the "reverification cost has no predictable upper bound" complaint from [[The-Problem-of-Extensible-Compiler-Verification]] — it isn't vague pessimism about proof engineering, it's this specific structural fact about what an induction-on-equivalence proof commits you to re-proving.

## The fix: factor out one predicate, indexed by rule, not by whole-language induction

The `Preserving` predicate is designed so the *boilerplate* obligations (reflexivity, symmetry, transitivity, congruence — invariants common to *every* Pyrosome language and compiler) are proved **once, generically, by the framework itself**, and the only thing a user of Pyrosome ever has to prove **per feature** is the content case — e.g., beta for STLC, or the two projection equations for products.

$$
\mathrm{Preserving}(L_t,\ cmp,\ L_s)
$$

is an **inductive predicate over the structure of $L_s$** (the source language's rule list from [[Language-Specifications-as-Equational-Theories]]), not over the equivalence relation's derivation tree. It has exactly one case per *kind* of rule that can appear in $L_s$:

- **Sort rule** → the compiler must map it to a well-formed sort in $L_t$.
- **Term rule** → the compiler must map it to a well-formed term in $L_t$.
- **Equation rule** → the compiler must map the left- and right-hand sides to *equivalent* terms in $L_t$.

Each case is defined **recursively in terms of `Preserving` holding for the *tail* of $L_s$** — i.e., proving the obligation for rule $n$ is allowed to assume `Preserving` already holds for rules $1$ through $n-1$. This recursive structure over the *rule list*, rather than over term-equivalence derivations, is the entire trick: it turns "one universally-quantified fact about a whole language" into "one small, independent fact per rule, chained together by the rule list's own order."

**Why this is provable at all — the ordering discipline pays off here directly.** Recall from [[Language-Specifications-as-Equational-Theories]] that a rule may only reference sorts, terms, and metavariables declared *earlier* in the list. This means the obligation for, say, the STLC lambda rule references only the *prefix* of the compiler covering rules before lambda (which doesn't yet include application, since application comes later in the list) — so proving `Preserving` for one rule never has to look ahead at rules that don't exist yet. This is what makes each case genuinely local and independently checkable, rather than secretly depending on the whole eventual language.

## Theorem 1 — Compiler extension: independent proofs compose automatically

$$
\textbf{Theorem 1 (Compiler extension).}\ \text{Let } L_{pre}+L_1 \text{ and } L_{pre}+L_2 \text{ be well-formed languages}
$$
$$
\text{with disjoint rule names in } L_1, L_2.\ \text{If } \mathrm{Preserving}(L_t, cmp_{pre}+cmp_1, L_{pre}+L_1)
$$
$$
\text{and } \mathrm{Preserving}(L_t, cmp_{pre}+cmp_2, L_{pre}+L_2),\ \text{then } \mathrm{Preserving}(L_t, cmp_{pre}+cmp_1+cmp_2, L_{pre}+L_1+L_2).
$$

In words: if you've separately verified two *different* extensions of a shared base language (say, STLC + Recursion verified independently from STLC + Naturals), you can combine both extensions — and both compiler extensions — into a compiler for the combined language $L_{pre}+L_1+L_2$, **without redoing any proof work**, as long as the two extensions don't declare conflicting rule names. This is the formal payoff of the whole design: two teams (or two chapters of one thesis) can independently extend a shared base and get their results *for free* when combined, not just extended-but-still-compatible-in-principle.

A supporting mechanism makes this actually work: **weakening and monotonicity**. Compilers are disallowed from *overwriting* old mappings (only appending new ones, per [[Compilers-as-Finite-Maps]]), so a proof of `Preserving` established using only the prefix compiler $cmp_{pre}$ remains valid — via a weakening lemma — once the compiler is extended to $cmp_{pre}+cmp_1$. All of Pyrosome's judgments are **monotonic under language extension**: a fact that holds in a smaller language continues to hold once the language grows, because nothing about the smaller language's rules changes when new ones are appended after them.

## Theorem 2 — Preserving implies semantic preservation

$$
\textbf{Theorem 2.}\ \text{If } \mathrm{Preserving}(L_t, cmp, L_s), \text{ then } cmp \text{ is a type- and equivalence-preserving compiler from } L_s \text{ to } L_t.
$$

This is the theorem that closes the gap between "I checked one small, local obligation per rule" and "I get the actual, universally-quantified semantic guarantee I wanted." Its proof is by **mutual induction over every judgment form in Pyrosome** — for each judgment (well-formedness of sorts, well-formedness of terms, term equivalence), show it's preserved by compilation. The term-equivalence case is a generalized version of the naive proof sketch at the top of this article: reflexivity/symmetry/transitivity/congruence go through generically, and the beta-style content case is now discharged *once* by appeal to the per-rule `Preserving` obligation, rather than re-derived by hand for the specific compiler at hand.

This is the theorem that makes proving `Preserving` — a mechanical, per-rule checklist — a *strictly easier* thing to do than proving type-and-equivalence preservation directly, while guaranteeing they're equivalent in strength. Practically, the mechanization "automatically breaks down the necessary proof obligations," and the resulting per-rule goals are unquantified (no `∀` at the Coq level) and provable by direct construction of a derivation — the kind of goal automation ([[Proof-Automation-and-Elaboration]]) handles well, unlike the original whole-language induction.

## Theorem 3 — Compiler codomain embedding

$$
\textbf{Theorem 3.}\ \text{If } \mathrm{Preserving}(L_t, cmp, L_s) \text{ and } L_t \subseteq L_t', \text{ then } \mathrm{Preserving}(L_t', cmp, L_s).
$$

Here $L_t \subseteq L_t'$ means literally "every rule in $L_t$ is also in $L_t'$" (a rule-list subset, in the sense established by [[Language-Specifications-as-Equational-Theories]]'s list representation). This theorem says a compiler's *target* language can be embedded into a larger one — for free — without invalidating any existing `Preserving` proof. The motivating case: the core CPS compiler targets a plain CPS calculus; the global-store extension needs to target a CPS calculus *augmented* with stateful operations, which the core compiler was never proved against. Theorem 3 lets you embed the core compiler's target into the larger stateful target language first, so the state extension's proof can build on top of it directly.

## Vertical composition: chaining compiler passes for free

A separate but related benefit of proving *equivalence* preservation (rather than, say, a stronger simulation relation) is that **compiler correctness composes transitively across passes**. If compiler $A$ maps $L_1 \to L_2$ preserving equivalence, and compiler $B$ maps $L_2 \to L_3$ preserving equivalence, then $B \circ A$ maps $L_1 \to L_3$ preserving equivalence — directly, because "preserves equivalence" is exactly the kind of property that survives function composition when both compilers are proved against the *same* notion of equivalence at the shared intermediate language $L_2$.

The book demonstrates this with a genuinely useful refactor: define the base calculus with `fix f(x:A) := e` (general recursion) instead of `λ(x:A).e`, prove a CPS compiler for *that*, and then implement ordinary non-recursive lambda as a **two-stage compiler**: a small desugaring pass ($\lfloor\lambda(x:A).e\rfloor = \mathrm{fix}\ f(x{:}\lfloor A\rfloor) := \lfloor e\rfloor$, for a fresh $f$ not occurring in $e$) followed by the already-proved recursion-CPS compiler. Prove the desugaring pass correct once, and it's reusable against *any* later replacement of the recursion-CPS stage — swap that stage for a different pass, and the desugaring's correctness proof needs no changes, because vertical composition only cares that each stage individually preserves equivalence at its own shared boundary language.

## Grounding: what modular proof obligations look like as code

**Rust (primary) — `Preserving` as a per-rule trait obligation, not a whole-language induction:**

```rust
/// Instead of one big recursive function proving "preserves equivalence"
/// over an entire AST type, Preserving is checked rule-by-rule against
/// a rule LIST, each check only allowed to assume earlier rules are done.
trait PreservingObligation {
    /// Only ever needs the PREFIX of the compiler that came before this rule —
    /// mirrors the "only reference earlier rules" ordering discipline.
    fn discharge(&self, compiled_prefix: &Compiler) -> Result<(), ObligationFailure>;
}

fn check_preserving(rules: &[Rule], cmp: &Compiler) -> Result<(), ObligationFailure> {
    let mut prefix = Compiler::empty();
    for rule in rules {
        rule.obligation().discharge(&prefix)?;   // Theorem-2-style per-rule check
        prefix.extend(cmp.mapping_for(rule));     // weakening: extend, never overwrite
    }
    Ok(())
}
```

This is the direct machine-checkable shape of "one goal per rule, chained left-to-right, never revisiting an earlier goal" — Theorem 1's compiler-extension guarantee is exactly what makes `check_preserving` on `rules_a ++ rules_b` decomposable into independent calls on `rules_a` and `rules_b` when their rule names are disjoint.

**Lean (secondary) — this is the same shape as proving a `simp` set is confluent/terminating incrementally, or proving elaborator soundness lemma-by-lemma rather than as one giant well-founded recursion.** If you've structured a Lean development so that adding a new tactic or a new inductive constructor requires proving one new, self-contained lemma rather than reopening an existing proof, you've already used this pattern. The disciplined ordering ("only reference earlier rules") is analogous to a dependency-respecting order of `have` statements that lets later lemmas cite earlier ones without forward references.

**Python (tertiary sketch)** of the recursive structure of `Preserving` itself:

```python
def preserving(L_s, cmp, L_t):
    if not L_s:
        return True  # base case: empty language trivially satisfies Preserving
    *rest, last_rule = L_s
    return preserving(rest, cmp, L_t) and obligation_for(last_rule, cmp, L_t)
```

## Where this leads

`Preserving` is the mechanism that makes every downstream claim in the thesis "modular" in a checkable, not just aspirational, sense: [[The-STLC-to-CPS-to-Closures-Case-Study]] and [[Extending-the-Case-Study]] both rely on Theorem 1 to add recursion, naturals, unit, and global state without reopening the base compiler's proof; [[Proof-Automation-and-Elaboration]] exploits the fact that `Preserving`'s per-rule goals are quantifier-free and automatable; and Theorem 3's codomain-embedding is what lets the state extension's target language grow past the core compiler's original target.

For the workbench's compiler/elaborator/verification project (`type-theory`, `automated-reasoning`): this is a template for structuring your *own* soundness proofs (e.g. for the refinement-type checker, or the metavariable unifier) so that adding a new refinement-logic connective or a new base type is a bounded, local proof obligation — not a full reopening of the master soundness theorem. It's also a direct precedent for how a trusted kernel's proof-checking obligations should be organized: one obligation per inference rule, checkable independently, exactly the shape a proof-producing architecture needs for its trusted computing base to stay small and stable under extension.
