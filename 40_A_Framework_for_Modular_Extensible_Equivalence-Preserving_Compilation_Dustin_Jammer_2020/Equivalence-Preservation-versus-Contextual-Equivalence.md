---
title: Equivalence Preservation versus Contextual Equivalence
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "2 Concepts of Pyrosome; 3.4 Why Equivalence Preservation"
pages: "17–19, 30–31"
tags: [type-theory, automated-reasoning, semantics, compiler-correctness]
---

[[book-guidelines|↩ Back to guidelines]]

## Two candidate notions of "the compiler didn't change the meaning"

Any theory of compiler correctness needs some formal notion of "semantic equivalence" to state its guarantee against: the compiler is correct if it maps semantically-equivalent source programs to semantically-equivalent target programs (roughly — see the value-mapping caveat below). The question this article is about is: **equivalent according to what relation?** Two candidates dominate the literature, and picking between them is one of the thesis's most consequential design decisions.

**Contextual equivalence** says two terms $e_1$ and $e_2$ are equivalent iff no surrounding program context $C[-]$ can ever observe a difference between $C[e_1]$ and $C[e_2]$ (e.g., no context makes one terminate and the other diverge, or produce different observable output). It's the standard, semantically "obviously right" notion in much of the programming-languages literature — it directly captures "these two programs behave the same no matter how you use them."

**Equivalence via an equational theory** (the notion [[Language-Specifications-as-Equational-Theories]] formalizes) says two terms are equivalent iff they're related by the reflexive-transitive-symmetric-congruence closure of a *specific, finite, listed set of axioms* the language designer chose to include — beta, eta, and whatever else the spec lists, and nothing more.

These sound like they should coincide, or at least that contextual equivalence should be the "more correct" one to aim for, since it's semantically motivated rather than syntactically stipulated. The thesis's central argument in this section is that **for the purposes of compiler correctness under extension, this intuition is backwards.**

## The callTwice example: contextual equivalence changes meaning depending on what else exists

Consider, in plain STLC:

$$
\texttt{callTwice} \triangleq \lambda(f:\mathrm{nat}\to\mathrm{nat}).\,\lambda(x:\mathrm{nat}).\,(\lambda(\_:\mathrm{nat}).\,f\,x)\,(f\,0)
$$

Read operationally: given `f` and `x`, this calls `f` on `0` (discarding the result, bound to the wildcard `_`), and *then* returns `f x`. In pure, sequential STLC with no visible side effects, calling `f 0` and throwing away the result is contextually indistinguishable from not calling it at all — no context built purely from STLC's syntax can tell whether that first call happened. So in plain STLC, `callTwice` is **contextually equivalent** to the much simpler $\lambda(f:\mathrm{nat}\to\mathrm{nat}).\,f$.

Now compile `callTwice` with the CPS transform from [[The-Problem-of-Extensible-Compiler-Verification]], and hand it a continuation built from two auxiliary target-language functions:

$$
\texttt{haltEarly} \triangleq \lambda(x:\mathrm{nat}, k:\neg\mathrm{nat}).\ \mathrm{halt}\ x
\qquad
\texttt{callWithOne} \triangleq \lambda(f:\mathrm{natFun}).\ f\,\langle 1, \mathrm{halt}\rangle
$$

$$
\texttt{cont} \triangleq \lambda(c:\neg(\mathrm{natFun}\times\neg\mathrm{natFun})).\ c\,\langle \texttt{haltEarly}, \texttt{callWithOne}\rangle
$$

Substituting `cont` for the top-level continuation `k` in $\lfloor\texttt{callTwice}\rfloor$ and running the result: the compiled program calls `haltEarly` on `0` **first** (because CPS makes the intermediate `f 0` call's control-flow order explicit and unavoidable, exactly the call that plain STLC's contextual equivalence considered invisible), and `haltEarly` immediately halts with result `0`, **discarding** the continuation `callWithOne` entirely — so the *second* call, `f x`, never happens.

Compile $\lambda(f:\mathrm{nat}\to\mathrm{nat}).\,f$ instead — the term contextual equivalence said was indistinguishable from `callTwice` — and running it against the same `cont` produces a program that halts with result **`1`** (via `callWithOne`), not `0`.

**Two source terms that are contextually equivalent in STLC compile to target programs that behave differently.** If "compiler correctness" meant "preserves contextual equivalence," this compiler — the ordinary CPS transform, the one everybody wants to be able to prove correct — would be *wrong*. That's the blind spot: contextual equivalence in the *source* language is a fact about what STLC-only contexts can observe, but CPS translation itself introduces exactly the kind of observational power (explicit evaluation order, explicit control flow via continuations) that a pure-STLC context never had. The compiled programs live in a strictly more expressive target language, and "equivalent under the weaker source language's contexts" says nothing about what happens once you have access to the target's stronger ones.

**What breaks, generalized:** this isn't a one-off quirk of `callTwice`. Any time a source language is compiled into a strictly more observationally powerful target (which is nearly always true — compilation tends to make implicit things, like evaluation order or resource usage, explicit), contextual equivalence in the source is liable to be too coarse: it may equate terms that a correct compiler is *forced* to distinguish, simply because it must commit to some specific evaluation strategy the source didn't pin down.

## Why the equational-theory notion doesn't have this problem

Pyrosome's source-language semantics for STLC deliberately **restricts beta to call-by-value**:

$$
(\lambda(x:A).\,e)\,v = e[v/x] \qquad \text{(only when the argument is already a value } v\text{, not an arbitrary expression)}
$$

This one restriction is precisely what prevents the theory from equating `callTwice` with $\lambda(f:\mathrm{nat}\to\mathrm{nat}).\,f$: the internal application $(\lambda(\_:\mathrm{nat}).\,f\,x)\,(f\,0)$ inside `callTwice` cannot be beta-reduced until its argument `f 0` has itself been reduced to a value — and reducing `f 0` to a value is exactly the "extra" call whose presence or absence distinguishes the two terms. **The equational theory only ever asserts the equalities the language designer explicitly listed** — it makes no claim about "everything indistinguishable by any context," so it never accidentally licenses an equation the compiler can't actually honor.

This is the deeper reason [[Language-Specifications-as-Equational-Theories]] insists that a language's semantics live in an explicit, finite, listed set of axioms rather than an implicitly-defined closure over "all consistent observations": **the axioms are a contract the compiler-correctness proof has to honor, and the language designer gets to choose that contract to be exactly as strong (or as weak) as the compiler can actually support.** If full, unrestricted beta reduction had been listed instead of the call-by-value-restricted version, the equational theory *would* equate `callTwice` with $\lambda f.f$ — and the CPS compiler's correctness proof would then correctly fail, because no compiler that fixes an evaluation order can honor that equation. The restriction to call-by-value isn't an arbitrary technical patch; it's the language designer being honest, up front, about which equalities the intended target semantics can actually support.

## Equivalence preservation composes with extension; contextual equivalence resists it

Because equational-theory-based equivalence is defined by a *fixed, listed* set of axioms (closed generically under reflexivity/symmetry/transitivity/congruence, per [[Language-Specifications-as-Equational-Theories]]), it is **monotonic under language extension** by construction: adding new rules to a language can only add new axioms, never invalidate or reinterpret old ones, so a fact "$t_1 = t_2$ in $L$" remains true in $L + L'$ for any extension $L'$. This monotonicity is what [[The-Preserving-Predicate-and-Modularity-Theorems]] leans on directly for its weakening/monotonicity lemmas.

Contextual equivalence has no such guarantee: whether $e_1$ and $e_2$ are contextually equivalent can *change* — specifically, can stop holding — when the language is extended with a new feature that introduces a context able to distinguish them, even though neither $e_1$ nor $e_2$ mentions the new feature at all. This is precisely why "prove compiler correctness with respect to contextual equivalence" resists exactly the kind of incremental, per-feature extension [[The-Problem-of-Extensible-Compiler-Verification]] identifies as the whole point of the thesis: a new feature can silently retroactively falsify equivalences your compiler's correctness proof relied on, with no local warning sign in the new feature's own specification.

## The remaining blind spot, and how it's patched

Equivalence preservation, taken alone, is *too permissive* in one specific way: it says nothing about *which* target values source values map to, only that equivalent source terms map to equivalent target terms. This admits degenerate "compilers" that are technically equivalence-preserving but useless or actively wrong as implementations:

- The **trivial compiler** that maps every program to a target term that always returns `0`. Every pair of source terms is (trivially) mapped to the same target term, hence "equivalent" — vacuously satisfying equivalence preservation while doing no actual computation.
- **Value-permuting compilers** that consistently swap `true`↔`false`, or otherwise apply an isomorphism to observable values — these preserve equivalence relations perfectly (an isomorphism preserves all structure) while producing target programs whose observable results don't correspond to the source's intended meaning at all.

The fix is to **separately fix an expected mapping of observable values** from source to target — e.g., stipulate that natural-number and Boolean constants must map to themselves whenever both languages have them — and check the compiler against *that* mapping, on top of (not instead of) equivalence preservation. The book notes this can be checked within the same framework, by reasoning about the compiler's effect on a term that is just a metavariable standing for a constant. Equivalence preservation and a fixed observable-value mapping together close the gap that either one alone leaves open.

## Grounding: seeing the blind spot in code

**Rust (primary) — the trivial-compiler blind spot made concrete:**

```rust
/// Technically "equivalence preserving": maps EVERY source term
/// to the same target constant, so any two equivalent source terms
/// trivially map to equivalent (identical) target terms.
/// This compiles and "passes" a bare equivalence-preservation proof
/// while being a completely useless (or actively wrong) implementation.
fn trivial_compiler(_source: &SourceTerm) -> TargetTerm {
    TargetTerm::Const(0)
}

/// The fix: separately require constants to map to themselves.
fn check_observable_value_mapping(cmp: &Compiler) -> bool {
    cmp.compile(&SourceTerm::Const(0)) == TargetTerm::Const(0)
    // ... and so on for every observable constant, per the fixed mapping
}
```

**Lean (secondary) — this maps onto a distinction Lean's own metatheory has to draw carefully: definitional equality is deliberately a fixed, syntactically-closed relation (like Pyrosome's equational theory) rather than "provable propositional equality" (closer to contextual reasoning, in the sense of ranging over arbitrary proof contexts).** Lean's kernel checks `isDefEq` against a specific, bounded set of reduction rules for exactly the reason this article gives: a notion of equality has to be something a *specific* algorithm (or compiler) can be checked against, not an open-ended "anything a sufficiently clever context could distinguish."

**Python (tertiary sketch)** — the two notions as literal predicates over term pairs:

```python
def contextual_equiv(e1, e2, all_possible_contexts):
    return all(observe(C(e1)) == observe(C(e2)) for C in all_possible_contexts)  # intractable, and shrinks under extension

def theory_equiv(e1, e2, axioms):
    return in_closure(e1, e2, axioms)  # fixed, finite, monotonic under adding axioms
```

## Where this leads

This is the semantic foundation that makes the entire framework's extensibility story *sound*, not just convenient: [[The-Preserving-Predicate-and-Modularity-Theorems]]'s monotonicity lemmas, and the whole "extend without reverifying" promise from [[The-Problem-of-Extensible-Compiler-Verification]], only hold because the notion of equivalence being preserved doesn't shift underfoot when the language grows — which contextual equivalence would. [[Compiler-Correctness-in-the-Broader-Literature]] situates this choice against alternatives like full abstraction (which specifically targets contextual-equivalence preservation) and CompCert-style simulation.

For the workbench's project (`automated-reasoning`, `type-theory`): this is a direct cautionary tale for any Hoare-logic or refinement-type soundness argument — if "program equivalence" in your verification framework is defined via an open-ended semantic relation (contextual-equivalence-flavored) rather than a fixed proof-theoretic one (definitional-equality-flavored), adding a new refinement-logic connective or base type risks silently invalidating equivalences your existing verification-condition-generation relied on. Preferring the fixed, axiom-list notion — and being explicit about which observable-value mappings your VC generator commits to — is the same discipline this section argues for.
