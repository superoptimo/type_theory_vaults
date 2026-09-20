---
title: Constrained Horn Clauses (CHCs)
source: "ADCL: Acceleration Driven Clause Learning for Constrained Horn Clauses (Frohn & Giesl, 2023)"
chapters: "Sect. 1 Introduction, Sect. 2 Preliminaries (pp. 1–6)"
tags: [chc, sat-smt-csp, automated-reasoning, verification-conditions, resolution]
---

[[book-guidelines|↩ Back to guidelines]]

## Why verification needs a clause language at all

Suppose you want to verify a program automatically — no human writing a proof, just a tool deciding "safe" or "unsafe." The standard recipe (weakest preconditions, Hoare triples, symbolic execution) eventually produces a pile of *verification conditions*: implications that must all hold if the program is correct. The problem is that a program has loops and recursive functions, and those give you **recursive** verification conditions — "if the invariant holds at iteration $n$, it holds at iteration $n+1$" — not a flat set of first-order formulas you can hand to an SMT solver and be done.

What breaks without a dedicated clause language: if you tried to feed "the invariant is inductive" directly into an SMT solver as one formula, you'd need to already know the invariant (a fixpoint), which is exactly the thing verification is trying to discover. You need a representation that keeps the recursive structure *visible* — as clauses that mutually reference each other via predicate symbols — so that a solver can search over hypotheses for what the predicates should mean, rather than being handed the answer up front.

That representation is a **Constrained Horn Clause (CHC)**: a Horn clause (at most one positive literal) whose body can additionally carry a *constraint* — a first-order formula over some background theory like linear arithmetic. The predicate symbols are uninterpreted (their meaning is exactly what you're trying to find — e.g. "the loop invariant"), while the constraint part is interpreted by a fixed theory $A$ (integers, reals, arrays, …). This is precisely the split a compiler engineer already has intuitions for: uninterpreted symbols are like the type variables you're solving for during type inference, and the constraint is the "side condition" that inference has to satisfy along the way. If you've ever generated Horn-clause-shaped constraints for Hindley-Milner unification or for a refinement-type checker, this is the same shape, just aimed at loop invariants instead of types.

## The four shapes a CHC can take

The paper defines a CHC as a first-order sentence of one of two general forms:

$$\forall \vec X_1,\dots,\vec X_d,\vec Y,\vec Z.\; F_1(\vec X_1) \wedge \dots \wedge F_d(\vec X_d) \wedge \psi \Longrightarrow G(\vec Y)$$
$$\forall \vec X_1,\dots,\vec X_d,\vec Y,\vec Z.\; F_1(\vec X_1) \wedge \dots \wedge F_d(\vec X_d) \wedge \psi \Longrightarrow \bot$$

Read left to right: a conjunction of **uninterpreted predicate literals** ($F_1,\dots,F_d \in \Sigma$, the alphabet of predicates you're solving for) and a **constraint** $\psi$ (a quantifier-free formula over the background theory's own signature $\Sigma_A$) implies either another predicate literal or $\bot$ (falsity — an assertion that this situation must never arise). All variables are implicitly universally quantified, and the paper drops the leading $\forall$ throughout — a convention it's worth internalizing early, since every clause you'll see afterward looks "bare."

The whole vocabulary the paper builds on rests on **restricting to linear CHCs** — at most one predicate literal in the body ($d \le 1$) — which collapses the two general forms above into exactly four named shapes:

| Name | Shape | Reading |
|---|---|---|
| **fact** | $\psi \Rightarrow G(\vec Y)$ | "$G$ holds unconditionally under $\psi$" — e.g. an initial state |
| **rule** | $F(\vec X) \wedge \psi \Rightarrow G(\vec Y)$ | "$G$ holds if $F$ held and $\psi$ transitions us there" — a program step |
| **query** | $F(\vec X) \wedge \psi \Rightarrow \bot$ | "$F$ under $\psi$ must never happen" — an assertion / error condition |
| **conditional empty clause** | $\psi \Rightarrow \bot$ | "$\psi$ alone is already a contradiction" — the terminal artifact of a refutation |

A rule is called **recursive** when its head and body predicate coincide ($F = G$) — this is the syntactic fingerprint of a loop or a recursive call, and it's exactly the case the rest of the paper (loop acceleration) exists to handle specially. A CHC is **conjunctive** when its constraint $\psi$ is a plain conjunction of literals rather than a general Boolean combination — this matters later because acceleration techniques only operate on conjunctive CHCs (see [[Loop-Acceleration]]).

**What breaks without the linearity restriction:** allowing more than one predicate literal in a body ($d > 1$) gives you full Horn-clause-based program synthesis / CLP power, but you lose the clean "one predicate = one program point, resolution chains = one execution path" correspondence this paper exploits. Every structural argument in the calculus — traces as sequences of CHCs, blocking-clause bookkeeping, acceleration of a *single* recursive predicate — depends on there being at most one predicate to resolve against at each step.

Rust-style, you can picture the clause shapes as a small tagged enum, which also makes the "$d\le 1$" invariant visible as a type-level constraint instead of a runtime check:

```rust
enum Chc {
    Fact   { head: PredAtom, cond: Constraint },
    Rule   { body: PredAtom, cond: Constraint, head: PredAtom },
    Query  { body: PredAtom, cond: Constraint },               // implicitly head = False
    CondEmpty { cond: Constraint },                            // implicitly head = False, no body
}

struct PredAtom { pred: PredSymbol, args: Vec<Var> }   // args are always variables (see below)
```

Note the paper's own simplifying assumption baked into this signature: **all predicate arguments are variables.** If you write `Inv(X1 + 1, Y2)` on paper, formally that's sugar for `Inv(Z1, Z2) ∧ Z1 = X1+1 ∧ Z2 = Y2` — a fresh-variable equation folded into the constraint. This is a completely mechanical normalization (the same "flatten complex arguments into fresh temporaries" pass a compiler does for three-address code), and the paper does it silently so that examples stay readable.

## The theory boundary: $\Sigma$ vs. $\Sigma_A$

A CHC lives astride two disjoint signatures:

- $\Sigma$ — the **uninterpreted predicates** ($F, G, \dots$), whose meaning is what a CHC-SAT solver is trying to determine. No functions live here — only predicates.
- $\Sigma_A$ — the signature of a **complete background theory** $A$ (e.g. linear integer arithmetic), which the constraint $\psi$ is built from and whose meaning is fixed in advance.

"Complete" is doing real semantic work here: for every closed $\Sigma_A$-formula $\psi$, either $\models_A \psi$ or $\models_A \neg\psi$. This is what licenses treating an **$A$-interpretation** $\sigma$ — a model of $A$ plus an interpretation of the $\Sigma$-predicates and free variables — as decidable to check against a constraint, and it's why the paper later gets to say $\sigma \models_A \varphi \iff \sigma \models_A \mathrm{grnd}(\varphi)$ (interpretations only ever disagree on $\Sigma$ and $V$, never on the theory itself).

If you've worked with SMT solvers, this two-signature split is exactly the "theory atoms vs. Boolean skeleton" distinction SMT solvers already exploit (DPLL(T)): $\Sigma$-literals here play the role the Boolean skeleton plays there, and $\psi$ plays the role of the theory part a T-solver would discharge. CHC-SAT can be seen as "DPLL(T), but the Boolean skeleton is itself an inductively-defined predicate structure instead of a flat CNF."

## Ground instances: what a CHC actually *means*

A CHC with free variables is really standing in for the (potentially infinite) set of ground facts it licenses once you plug in concrete values satisfying the constraint. This is formalized as:

$$\mathrm{grnd}(\eta \wedge \psi \Rightarrow \eta') := \{\eta\sigma \Rightarrow \eta'\sigma \mid \sigma \models_A \psi\}$$

Read this as: for every model $\sigma$ of the constraint, instantiate all the variables according to $\sigma$ and keep the resulting *ground* (variable-free) implication. This single definition is the semantic anchor for the entire calculus — soundness, redundancy, and acceleration are all ultimately statements about **sets of ground instances being equal or contained in one another**, never about syntactic equality of clauses. Two syntactically different CHCs that produce the same ground-instance set are, for every purpose in this paper, the same clause.

This is worth pausing on if you're used to thinking of a "clause" as a syntactic object (as in classical resolution theorem proving): here, a CHC is more like a *generator* or *stream* of ground facts, and $\mathrm{grnd}$ is the function that materializes that stream. In Rust terms it's the difference between a parameterized query and its (conceptually infinite) result set:

```rust
// A CHC-as-generator: given a model of the constraint, yields one ground fact.
fn grnd_instance(chc: &Rule, sigma: &Model) -> Option<GroundImplication> {
    if sigma.satisfies(&chc.cond) {
        Some(GroundImplication { body: chc.body.substitute(sigma), head: chc.head.substitute(sigma) })
    } else {
        None
    }
}
```

with $\mathrm{grnd}(\varphi)$ being "the image of this function ranging over every model $\sigma$" — a lazy, possibly-infinite iterator rather than a materialized `Vec`.

**What breaks without grounding as the semantic anchor:** without it, "redundancy" (Section 3.1 in the guidelines, see [[Syntactic-Implicants-and-Redundancy]]) and "acceleration" (see [[Loop-Acceleration]]) would have no rigorous meaning — you'd be reduced to comparing clauses syntactically, which is far too brittle (the accelerated clause $\varphi^+_1$ in the paper's running example looks nothing like $N$ copies of $\varphi_r$ chained together, yet has exactly the same ground instances).

## Resolution and CHC problems

A **CHC problem** (denoted $\Phi$ or $\Pi$) is just a set of CHCs — the collected facts, rules, and queries you're trying to determine the satisfiability of. Resolution (Def. 2) combines two clauses on a shared predicate literal via most general unification $\theta$:

$$\mathrm{res}(\eta \wedge \psi \Rightarrow F(\vec x),\; F(\vec y) \wedge \psi' \Rightarrow \eta') := (\eta \wedge \psi \wedge \psi' \Rightarrow \eta')\theta$$

Because the paper restricts to *linear* CHCs and assumes each predicate application uses fresh variables, the mgu $\theta$ here is always a pure variable renaming — a nice simplification that keeps resolution purely structural (no genuine unification failures beyond arity/name mismatches, no need for occurs-checks). This is lifted to sequences of clauses by folding: $\mathrm{res}([\varphi_1,\varphi_2] :: \vec\varphi) := \mathrm{res}(\mathrm{res}(\varphi_1,\varphi_2) :: \vec\varphi)$ — resolve the first two, then keep going. A **refutation** is a conditional empty clause $\psi \Rightarrow \bot$ whose condition $\psi$ is *satisfiable* — because an unsatisfiable $\psi\Rightarrow\bot$ would be vacuous (its constraint can never actually hold), while a satisfiable one witnesses a genuine concrete counterexample once you plug in a model of $\psi$.

This last point is the heart of **CHC-SAT as a verification-condition formalism**: proving a CHC problem $\Phi$ *unsatisfiable* is exactly proving there's some resolution chain from a fact through rules to a query whose accumulated condition is satisfiable — and that satisfying model, substituted back through the chain, is a literal, concrete, executable counterexample trace through the original program. This is the payoff the paper's Example 1 dramatizes: a resolution proof of 10001 steps corresponds to a program run of 10001 loop iterations reaching an error state, and every one of those steps is individually justified by the theory $A$ (here, LIA arithmetic).

Here's the same correspondence sketched in Lean, since "resolution chain length = counterexample trace length" is exactly the kind of structural correspondence Lean's own proof terms make literal — a `Refutation` *is* a certificate, and reconstructing the model is reconstructing a witness:

```lean
-- A CHC problem's unsatisfiability is witnessed by an explicit resolution chain
-- ending in a satisfiable empty clause — this witness *is* the counterexample.
structure Refutation (Φ : Set Chc) where
  trace : List Chc                      -- φ₁ :: φ₂ :: … :: φₙ, each drawn from Φ
  fromΦ : ∀ φ ∈ trace, φ ∈ Φ
  resolves : res trace = (ψ ⟹ False)    -- res of the whole trace is a conditional empty clause
  sat : Satisfiable ψ                    -- and its condition is satisfiable, not vacuous
```

The point of naming it this way: `Refutation` is not just "a proof the set is unsatisfiable" in the classical logical sense — it is *simultaneously* a constructive, replayable program trace. That double duty (proof object = execution witness) is precisely what a Rust-based verifier's counterexample reporting will need to reconstruct: when your compiler says "this program is unsafe," it should hand back exactly this kind of structure, not just a Boolean.

## Where this leads

Everything downstream in the paper is a refinement of the two ideas introduced here. **Ground instances and resolution** are the semantic and proof-theoretic backbone that [[Resolution-for-CHCs]] develops into full soundness/lifting arguments. The **linear/recursive/conjunctive** distinctions set up exactly which clauses [[Loop-Acceleration]] is allowed to touch — acceleration only ever applies to a recursive conjunctive rule. And the **fact/rule/query/conditional-empty-clause** taxonomy becomes the vocabulary of *states* in [[The-ADCL-Calculus]], where a derivation is literally a growing trace of these four clause shapes, periodically collapsed by an accelerated clause instead of extended one ordinary resolution step at a time.

For the standing project: this is the representation your compiler's verification-condition generator would emit before handing anything to a solver backend — the uninterpreted predicates are your program's basic-block/loop-header invariants, the constraint theory is whatever arithmetic/array theory your refinement types range over, and "CHC-SAT" is the precise formal target that a Hoare-triple or dependent-subtyping obligation compiles down to (`sat-smt-csp`, `automated-reasoning`). The resolution machinery here is also a direct, simpler cousin of the clause/resolution engine called for in the standing project's theorem-prover component — same $\mathrm{mgu}$-driven combination step, just over Horn clauses with a decidable background theory instead of full first-order terms.
