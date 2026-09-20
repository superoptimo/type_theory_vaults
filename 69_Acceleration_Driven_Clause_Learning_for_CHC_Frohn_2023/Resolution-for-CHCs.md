---
title: Resolution for CHCs
source: "ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses (Frohn & Giesl, 2023)"
chapters: "Sect. 2 Preliminaries (pp. 3–6); Appendix A/B (Def. 20–21, Lemma 22–23, pp. 26–28)"
tags: [chc, resolution, unification, automated-reasoning, proof-reconstruction]
---

[[book-guidelines|↩ Back to guidelines]]

## Resolution as the one move ADCL is allowed to make

[[Constrained-Horn-Clauses-(CHCs)]] gave you the vocabulary — facts, rules, queries, conditional empty clauses. Resolution is the single operation that turns a *set* of those clauses into a *chain of reasoning*: pick a fact, chain it through rules that "continue the story it started," and see whether the chain can reach a query and produce a contradiction. Everything ADCL later does — Step, Accelerate, Covered, Refute — is either an application of this one operation or bookkeeping around it. If you don't have resolution nailed down precisely, none of the calculus in [[The-ADCL-Calculus]] will make sense, because every rule there is stated in terms of "extend the trace by resolving."

**What breaks without a single well-defined combination rule:** without resolution, a "proof" of unsatisfiability is just an unstructured claim. Resolution gives you a *syntactic, checkable* certificate — a finite sequence of clauses, each combination step mechanically verifiable — which is exactly what lets a downstream trusted kernel replay the proof without having to re-derive it from scratch. This is the same value proposition as a proof-carrying-code certificate or a Lean proof term: a resolution trace is small to check even when it was expensive to find.

## Definition 2: resolving two CHCs on a shared predicate

Given two CHCs $\varphi = (\eta \wedge \psi \Rightarrow F(\vec x))$ and $\varphi' = (F(\vec y) \wedge \psi' \Rightarrow \eta')$ — first renaming apart so they share no variables — resolution combines them on the predicate $F$ that one produces and the other consumes:

$$\mathrm{res}(\varphi, \varphi') := (\eta \wedge \psi \wedge \psi' \Rightarrow \eta')\theta, \qquad \theta = \mathrm{mgu}(F(\vec x), F(\vec y))$$

and $\mathrm{res}(\varphi,\varphi') := (\bot \Rightarrow \bot)$ if the two $F$-literals don't unify at all (this "always defined, falls back to a fixed sentinel" trick is what lets resolution be a *total* function on pairs of CHCs rather than a partial one — no `Option`/failure case anywhere else in the calculus has to account for "resolution wasn't applicable").

Read it operationally: $\varphi$ says "under $\eta,\psi$, I can produce $F(\vec x)$"; $\varphi'$ says "given $F(\vec y)$ and $\psi'$, I can produce $\eta'$." Chaining them says "under $\eta$, $\psi$, and $\psi'$ (with $\vec x$ and $\vec y$ identified by the mgu), I can produce $\eta'$" — the intermediate predicate $F$ has been eliminated, exactly as in classical propositional resolution where you cancel a literal against its negation.

### The mgu is *always* a variable renaming here — and why that quietly simplifies everything

In general first-order resolution, $\mathrm{mgu}$ can do real work: matching nested terms, discovering that two different-looking terms are actually the same after substitution, failing via an occurs-check on cyclic terms. **None of that happens here.** Because every predicate argument is (per the paper's own normalization, see [[Constrained-Horn-Clauses-(CHCs)]]) a *bare variable*, and $\varphi,\varphi'$ are variable-disjoint by construction, unifying $F(\vec x)$ with $F(\vec y)$ is just "identify $x_i$ with $y_i$ pairwise" — a renaming, never a substitution that could fail for structural reasons (short of arity/name mismatch, which the $\bot\Rightarrow\bot$ fallback absorbs).

This is a genuine simplification worth naming explicitly, because it's easy to over-engineer a Rust implementation for a unification problem that never actually needs full unification:

```rust
// Because predicate arguments are always variables, "unifying" two atoms
// of the same predicate is nothing but building a renaming substitution —
// no occurs-check, no term-structure matching, no failure except arity mismatch.
fn resolve(phi: &Chc, phi_prime: &Chc) -> Chc {
    let (phi, phi_prime) = rename_disjoint(phi, phi_prime); // fresh-variable apart
    match (phi.head_pred(), phi_prime.body_pred()) {
        (Some(f), Some(g)) if f.symbol == g.symbol => {
            let theta = pairwise_rename(&f.args, &g.args); // pure renaming, never fails structurally
            build(phi.body_lits(), phi.cond().and(phi_prime.cond()), phi_prime.head_lits())
                .substitute(&theta)
        }
        _ => Chc::cond_empty(Constraint::False), // ⊥ ⇒ ⊥ sentinel
    }
}
```

If you've implemented Miller's pattern unification for a dependently-typed elaborator, notice the contrast: pattern unification is *interesting* precisely because metavariable arguments are distinct bound variables too, but the surrounding term structure can still be arbitrary, so failure and partial progress are real possibilities. Here, by design, there is no term structure left to fail on — the paper has engineered away exactly the hard part of unification, keeping only the "identify positions" bookkeeping. That's a deliberate simplicity/expressiveness trade-off: CHCs give up arbitrary term arguments so that resolution stays combinatorially cheap and total.

## Lifting resolution to sequences: what a "resolution proof" actually is

A single $\mathrm{res}(\varphi,\varphi')$ step only combines two clauses. A resolution *proof* — the thing Fig. 1's original 10001-step derivation is an instance of — is a whole sequence $\vec\varphi = [\varphi_1,\dots,\varphi_n]$ folded left-to-right:

$$\mathrm{res}([\varphi_1,\varphi_2] :: \vec\varphi) := \mathrm{res}(\mathrm{res}(\varphi_1,\varphi_2) :: \vec\varphi), \qquad \mathrm{res}(\varphi_1) := \varphi_1$$

This is a plain left fold — `fold(chcs, |acc, next| resolve(acc, next))` in Rust terms — and the paper immediately overloads every CHC-level notion ($\mathrm{cond}$, $\mathrm{grnd}$) onto sequences by first collapsing them through $\mathrm{res}$: $\mathrm{cond}(\vec\varphi) := \mathrm{cond}(\mathrm{res}(\vec\varphi))$. Keep this overloading straight — "the condition of a sequence" always means "the condition of what the whole sequence resolves down to," not some per-element aggregate.

A **trace**, later the central data structure of [[The-ADCL-Calculus]], is exactly such a sequence — but built up incrementally, one clause appended at a time, always starting from a fact. **Forward reasoning** is the direction ADCL actually uses: start from a fact (an initial condition) and resolve forward through rules toward a query, mirroring concrete program execution moving forward in time. This is a deliberate choice against the more traditional automated-theorem-proving habit of resolving *backward* from the negated goal — here "forward" coincides with "in the direction the program actually runs," which is what makes a completed trace double as a legible counterexample trace rather than an abstract refutation you'd need to reinterpret. (Contrast this with classical goal-directed/backward resolution — e.g. SLD-resolution in Prolog — which chains backward from a query toward facts; ADCL's Step rule, by construction, only ever extends a trace at the *fact* end going forward, precisely so that the accumulated condition reads as a forward-time program run.)

## Refutations: a satisfiable condition is the whole point

A conditional empty clause $\psi \Rightarrow \bot$ is called a **refutation** exactly when $\psi$ is *satisfiable*. This single word "satisfiable" is doing all the work that separates "we derived a contradiction" from "we derived nothing." If $\psi$ were unsatisfiable, the clause $\psi\Rightarrow\bot$ would be *vacuously* true (an unsatisfiable premise implies anything) and would tell you nothing about the original CHC problem $\Phi$ — you'd have proven a triviality, not found a bug.

Example 3's worked derivation makes this concrete: resolving $[\varphi'_f, \varphi_1^+, \varphi_2^+, \varphi_q]$ eventually collapses to
$$X_1 \le 0 \wedge X_2 \ge 5000 \wedge N' > 0 \wedge 5000+N' = X_2+N' = 10000 \;\Rightarrow\; \bot,$$
and the paper doesn't stop at "we derived $\bot$" — it explicitly exhibits a model ($\sigma(X_1)=0$, $\sigma(X_2)=\sigma(N')=5000$) satisfying the condition, *then* calls the result a refutation. That model is not a formality: substituting it back through the trace turns the abstract resolution proof into a proof on ground instances — a literal, replayable program run ending in the error state. This is the same shape as extracting a concrete counterexample from an SMT-unsat-core-adjacent artifact: the proof and the witness are two views of the same object.

## Soundness and the lifting lemmas: why resolution can be trusted at all

Definition 2 works purely syntactically — mgu, substitution, no reference to models. The paper's soundness argument has to bridge that syntax back to semantics: that resolving two CHCs never invents ground facts that weren't already implied by the originals. This bridge lives in Appendix A/B, built from ground-level resolution and two lemmas.

**Definition 20 (Resolution with Ground Instances)** restates resolution one level down, on *ground* atoms — no variables, no mgu, just matching a produced ground atom against a consumed one:

$$\mathrm{res}(\eta \Rightarrow F(\vec s),\; F(\vec s) \Rightarrow \eta') := (\eta \Rightarrow \eta')$$

This is resolution stripped to its semantic essence: two ground implications chain when the middle atom matches *exactly* (no unification needed — ground terms either are equal or aren't). **Definition 21** then lifts $\mathrm{res}$ pointwise across sets of clauses/sequences (`res(Φ₁, Φ₂) := {res(φ₁, φ₂) | φ₁ ∈ Φ₁, φ₂ ∈ Φ₂}`), which is exactly the machinery needed to state the next lemma without a variable-level detour.

**Lemma 22 (Resolution Distributes over grnd)** is the classical *lifting lemma* of resolution theorem proving, restated for CHCs:

$$\mathrm{grnd}(\mathrm{res}(\varphi_1,\varphi_2)) = \{\varphi \in \mathrm{res}(\mathrm{grnd}(\varphi_1), \mathrm{grnd}(\varphi_2)) \mid \models_A \mathrm{cond}(\varphi)\}$$

In words: grounding *after* resolving the symbolic clauses gives you exactly the (theory-consistent) ground facts you'd get by resolving *all* ground instances of $\varphi_1$ against *all* ground instances of $\varphi_2$ and keeping only the consistent ones. This is precisely the theorem that licenses reasoning at the symbolic (variable) level and trusting the result to correctly summarize every possible ground-level derivation — without it, symbolic resolution would just be a heuristic, not a sound proof procedure. The proof itself is a direct calculation: unfold both sides via the definitions of $\mathrm{grnd}$ and $\mathrm{res}$, and the mgu $\theta$'s renaming property (see above) is exactly what lets you factor a pair of independent ground substitutions $\sigma_1,\sigma_2$ into a single $\sigma$ over the unified variables — the same "no real unification, just identification" simplification from Definition 2 reappears here as the crux of the lifting proof.

**Lemma 23 (Associativity of Resolution)** — $\mathrm{grnd}(\mathrm{res}(\mathrm{res}(\varphi_1,\varphi_2),\varphi_3)) = \mathrm{grnd}(\mathrm{res}(\varphi_1,\mathrm{res}(\varphi_2,\varphi_3)))$ — says the left-fold definition of $\mathrm{res}$ on sequences doesn't secretly depend on association order. At the ground level this is almost definitional (both sides reduce to "chain $\eta_1\Rightarrow\eta_2\Rightarrow\eta_3\Rightarrow\eta_4$ into $\eta_1\Rightarrow\eta_4$"), but it matters enormously for the calculus: it's what justifies treating a **trace** as a flat, order-independent-in-grouping sequence rather than a binary tree whose shape you'd have to track. Later, **Lemma 24 (Composition of Ground Instances)** builds directly on both lemmas to show that resolving *over-approximations* of two sequences still over-approximates the resolvent — the exact property [[Loop-Acceleration]] needs to justify replacing a recursive suffix of a trace with its accelerated closure without losing soundness.

If you've built a resolution-based or tableau-based prover before, Lemma 22 is the CHC-flavored version of the standard first-order lifting lemma ("if ground instances of clauses resolve, the symbolic clauses have a resolvent that ground-instantiates to that resolution"), and Lemma 23 is the usual "resolution order doesn't matter" fact that lets you talk about "the resolvent of a clause set" without committing to a derivation shape. The genuinely CHC-specific twist is the $\models_A \mathrm{cond}(\varphi)$ filter in Lemma 22 — theory-inconsistent ground resolvents are silently discarded, which is exactly the many-sorted-theory analogue of a first-order prover discarding resolvents whose literals can't actually unify.

## Where this leads

This is the machinery [[The-ADCL-Calculus]]'s **Step** rule invokes directly — "extend the trace" is literally "append a clause and take $\mathrm{res}$ of the new sequence," and **Accelerate**'s soundness argument (replacing a recursive suffix with one accelerated clause) leans on Lemma 24, built from the two lemmas here. [[Metatheoretic-Properties-of-ADCL]]'s Soundness theorem is, at bottom, an induction over trace-extension steps where Lemma 22 is the base case doing the real work at every step. And forward reasoning's alignment with real program execution is what [[Empirical-Evaluation]]'s counterexample-witness claims ultimately cash out.

For the standing project (`automated-reasoning`): this is close to the cleanest possible worked example of a **trusted, proof-reconstructible resolution kernel** — a total combination function, a soundness lemma stated purely in terms of ground-instance containment, and a proof *object* (the trace) that doubles as an executable witness. That's the exact shape your theorem prover's clause/resolution engine wants for its trusted core: keep the combination step small and total (as here, thanks to the variables-only-arguments restriction), push all the real semantic risk into a separately-justified lifting lemma, and make the final proof artifact something a downstream kernel can *replay* rather than merely trust.
