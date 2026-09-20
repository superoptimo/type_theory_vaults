---
title: Proof Obligation Rules
book: Modeling in Event-B (J.-R. Abrial, 2010)
chapters: Chapter 5 §5.2 (pp. 188–203)
tags: [event-b, proof-obligations, verification-conditions, refinement, termination]
---

[[book-guidelines|↩ Back to guidelines]]

# Proof Obligation Rules

## What breaks without this

[[The-Event-B-Notation|The Event-B Notation]] gives you a grammar for writing down machines, contexts, and events — but a grammar alone proves nothing. Something has to look at a piece of Event-B text and mechanically produce the list of mathematical statements that, if all proved, jointly guarantee the model is internally consistent and correctly refines its abstraction. That "something" is the **proof obligation generator**, a static tool in the Rodin Platform, and its output is a fixed catalogue of *proof obligation rules* — this topic.

This is worth framing the way a compiler engineer would frame it: think of the proof obligation generator as exactly analogous to a **verification-condition generator** (VCGen) in a Hoare-logic-based verifier, or the constraint-generation pass of a bidirectional type checker. It walks the syntax, and for each syntactic construct that carries a *semantic promise* (an invariant, a guard relationship, a termination claim, a well-definedness side condition), it emits one sequent per promise, per event. Crucially — and this is the discipline that makes proof failures diagnostically useful, as established in [[Formal-Methods-and-the-Modeling-Philosophy|Formal Methods and the Modeling Philosophy]] — every rule here is *named systematically* (`evt/inv/INV`, `evt/act/FIS`, ...), so a failed proof points at exactly which construct, which invariant, which event is implicated. Without this naming discipline, "the proof failed" would tell you nothing actionable.

All the rules below share one running schematic event as their subject:

$$
\texttt{evt} \quad \textbf{any } x \; \textbf{where } G(s,c,v,x) \; \textbf{then } v :| BA(s,c,v,x,v') \; \textbf{end}
$$

with $s,c$ the seen sets/constants, $v$ the machine's variables, $A(s,c)$ the axioms, $I(s,c,v)$ the invariants. Every action is normalized to non-deterministic before-after-predicate form first (recall from the notation topic: deterministic assignment is just the special case where $BA$ pins $v'$ to one value) — that's precisely so *one* rule schema can cover all three surface action syntaxes.

## Invariant preservation — INV

The rule that formalizes exactly the informal argument given in [[Discrete-Transition-Systems|Discrete Transition Systems]] for the bridge controller. Named `evt/inv/INV`, per event and per invariant:

$$
A(s,c),\; I(s,c,v),\; G(s,c,v,x),\; BA(s,c,v,x,v') \;\vdash\; inv(s,c,v')
$$

Read it as: assuming the axioms, assuming *all* current invariants hold, assuming the event's guard holds (so the event is actually enabled), and assuming the before-after predicate describes the transition — prove that *this particular* invariant still holds afterward, with the primed (after) state substituted in.

A refining event needs a strengthened version of the same rule, because now the concrete invariant $J(s,c,v,w)$ may need to be checked, and a witness predicate $W2$ stands in for any abstract variable that disappeared:

$$
A(s,c),\; I(s,c,v),\; J(s,c,v,w),\; H(y,s,c,w),\; W2(v',s,c,w,y,w'),\; BA2(s,c,w,y,w') \;\vdash\; inv(s,c,v',w')
$$

The only structural difference from the non-refining case is the presence of $W2$ — witness predicates appear here precisely *because* a refining event's proof obligations need to talk about abstract variables that no longer literally exist in the concrete state; the witness supplies the missing term so the sequent can still be stated.

```rust
// The shape of what a VCGen would emit for one INV obligation, as a literal
// proof goal a solver/prover would receive — not Event-B syntax, just the isomorphism.
struct ProofObligation {
    name: &'static str,          // e.g. "ML_out/inv0_2/INV"
    hypotheses: Vec<String>,     // axioms + invariants + guard + before-after predicate
    goal: String,                // the invariant, with primed vars substituted per BA
}
```

## Feasibility — FIS

A **non-deterministic** action $v :| BA(\ldots, v')$ is only meaningful if *some* after-state actually satisfies $BA$ — otherwise the event, though its guard may be true, describes a transition to nowhere, which is a modeling error (a promise the model can't keep). `FIS` (per event, per non-deterministic action) proves exactly this existence:

$$
A(s,c),\; I(s,c,v),\; G(s,c,v,x) \;\vdash\; \exists v' \cdot BA(s,c,v,x,v')
$$

This is a **satisfiability** obligation, not an implication about a specific value — it's the Event-B analogue of proving a relation is *total* (every input state the guard admits has at least one valid output), the same shape as proving a non-deterministic transition relation in an operational semantics is never "stuck" once its side conditions are met. If you're building a CSP/constraint kernel, `FIS` is precisely an existential-satisfiability query — the same computational content as asking an SMT solver to find one satisfying assignment, except here it must hold *for every* pre-state consistent with the invariants and guard, so it's really a universally-quantified-over-pre-states, existentially-quantified-over-post-state statement — exactly the shape of a $\forall\exists$ verification condition, one level more complex than a plain SAT query.

## Guard strengthening — GRD

The rule making refinement's guard behavior precise: whenever the concrete (refined) event is enabled, the corresponding abstract event it refines must *also* have been enabled. Otherwise the refinement would let something happen concretely that the abstraction had no license to do at all.

$$
A(s,c),\; I(s,c,v),\; J(s,c,v,w),\; H(y,s,c,w),\; W(x,s,c,w,y) \;\vdash\; g(s,c,v,x)
$$

Here $H$ is the concrete guard, $g$ one specific abstract guard, and $W$ the witness relating abstract parameters $x$ to concrete parameters $y$. Notice the direction: concrete guard (plus witness) implies abstract guard — **concrete guards must be at least as strong** (i.e., at least as restrictive) as abstract ones. This is the same direction of implication as a *subtype*'s method precondition being no stronger than its supertype's — except inverted in the usual behavioral-subtyping phrasing (Liskov wants preconditions no *stronger*, here the concrete guard being logically stronger is fine and expected, because it's an implication target, not a caller-facing contract). The key intuition to hold onto: a concrete model is *allowed to fire less often* than its abstraction (it can add extra conditions narrowing when a transition happens), but it must never fire in a situation the abstraction wouldn't have permitted.

## Guard merging — MRG

A refinement is allowed to **merge** two abstract events with identical parameters and actions into one concrete event — a legitimate way to make a model more concrete by collapsing what used to be two named cases into one. The obligation: the merging event's guard must imply the *disjunction* of the two abstract guards, so that firing the merged event never corresponds to a situation neither original abstract event was licensed to handle:

$$
A(s,c),\; I(s,c,v),\; H(s,c,v,x) \;\vdash\; G1(s,c,v,x) \lor G2(s,c,v,x)
$$

This is `GRD`'s natural generalization to the "many abstract cases, one concrete case" situation — think of it as merging two branches of a case analysis that turn out, at a more concrete level of description, not to need to be told apart.

## Simulation — SIM

Guard strengthening alone only says "the concrete event doesn't fire when it shouldn't." It says *nothing* about whether the concrete event, once it *does* fire, actually does the same thing the abstract event was supposed to do. `SIM` is the rule that closes that gap: the concrete before-after predicate must imply the abstract one (through the appropriate witnesses):

$$
A(s,c),\; I(s,c,v),\; J(s,c,v,w),\; H(y,s,c,w),\; W1(x,\ldots),\; W2(v',\ldots),\; BA2(s,c,w,y,w') \;\vdash\; BA1(s,c,v,x,v')
$$

The book's worked example makes the point vivid: an abstract event $inc$ non-deterministically sets $v' = v+1 \lor v' = v+x$ for $x \in \{2,3,4\}$; a concrete refinement tracks $w = 2v$ and sets $w' = w+2 \lor w' = w+y$ for $y \in \{6,8\}$, with witnesses $x = y/2$ and $w' = 2v'$. `SIM` proves that whatever the concrete transition does is consistent with — a special case of — what the abstraction allowed. A second, simpler shape of `SIM` applies when abstract variables are simply **kept unchanged** in the concrete machine (a *superposition* refinement, as seen with the bridge's traffic lights): then the concrete before-after predicate just needs to directly imply the abstract one, no witnesses required, since there's no vanished variable to reconstruct.

`GRD` + `SIM` together are the complete refinement-correctness story for a single event: `GRD` says "don't fire when you shouldn't," `SIM` says "when you do fire, stay within what the abstraction allowed." This is exactly the pairing a behavioral-subtyping or simulation-relation proof needs — a forward simulation relation is precisely a relation satisfying an enabling condition (`GRD`-like) and a step-preservation condition (`SIM`-like) between concrete and abstract transition systems, which is the same proof structure used to justify compiler-correctness simulation diagrams.

## Convergence: NAT, FIN, and VAR

Three rules jointly discharge the promise a `convergent` or `anticipated` event's variant makes (see [[The-Event-B-Notation|The Event-B Notation]] for the status vocabulary):

- **NAT** — if the variant is numeric, prove it's actually a natural number under the event's guard: $A(s,c), I(s,c,v), G(s,c,v,x) \vdash n(s,c,v) \in \mathbb{N}$.
- **FIN** — if the variant is a set, prove it's finite under the guard: $\vdash \text{finite}(t(s,c,v))$.
- **VAR** — the actual decrease/non-increase obligation, four variants depending on convergent-vs-anticipated and numeric-vs-set:

$$
\begin{array}{ll}
\text{convergent, numeric:} & n(s,c,v') < n(s,c,v) \\
\text{convergent, set:} & t(s,c,v') \subset t(s,c,v) \\
\text{anticipated, numeric:} & n(s,c,v') \le n(s,c,v) \\
\text{anticipated, set:} & t(s,c,v') \subseteq t(s,c,v)
\end{array}
$$

all proved under the same hypotheses: $A(s,c), I(s,c,v), G(s,c,v,x), BA(s,c,v,x,v')$.

`NAT`/`FIN` guarantee the measure lives in a well-founded order to begin with (you can't decrease "forever" in $\mathbb{Z}$, only in $\mathbb{N}$ or a finite-set lattice — this is exactly why the rule insists on naturals or finite sets rather than allowing an arbitrary integer or infinite-set expression). `VAR` then does the actual ranking-function work. If you've implemented a termination checker or written `decreasing_by` proofs in Lean, this triple is structurally identical to what a well-founded-recursion elaborator demands: a type for the measure that admits a well-founded order (`NAT`/`FIN`, playing the role of "this expression really lives in the ordered domain"), plus a per-recursive-call decrease proof (`VAR`). The convergent/anticipated split additionally gives you a *staged* commitment: an anticipated event only has to promise "no regression," deferring "actual progress" to a later refinement once the right variant is known — a two-phase termination argument your CSP/abstract-interpretation kernel could reuse directly for events whose eventual progress measure isn't yet fixed at the point they're first introduced.

## Witness feasibility — WFIS

Just as a non-deterministic *action* needs `FIS` to guarantee it isn't vacuous, a non-deterministic **witness** needs its own existence check. For a witness predicate $W(x,s,c,w,y,w')$ standing in for a vanished abstract parameter or variable:

$$
A(s,c),\; I(s,c,v),\; J(s,c,v,w),\; H(y,s,c,w),\; BA2(s,c,w,y,w') \;\vdash\; \exists x \cdot W(x,s,c,w,y,w')
$$

This is exactly `FIS`'s existential-satisfiability pattern, replayed one level up — but now the thing being shown to exist is the abstract value the refinement is claiming as a legitimate stand-in. Connect this directly to your elaborator project: a witness is a metavariable-resolution claim (see [[The-Event-B-Notation|The Event-B Notation]]'s discussion of witnesses as Skolemization), and `WFIS` is precisely the obligation that the metavariable *has a solution at all* — the proof-obligation-generator-side analogue of an elaborator failing with "cannot synthesize metavariable" when no witness exists.

## Theorem and well-definedness obligations: THM, WD

- **THM** — any stated `theorem` clause (in a context or a machine) must actually be provable from the axioms, invariants, and theorems preceding it. Mechanically this is no different from proving any other goal; the reason theorems get their own named rule is purely organizational — a theorem is a *cached lemma*, proved once and then usable as a free hypothesis in every later proof obligation that can see it, exactly the role a proved auxiliary lemma plays in any interactive proof assistant's library.
- **WD** — the well-definedness side-condition rule, and arguably the most immediately transferable idea here for a verifier implementer. Many mathematical expressions are **partial** — not defined for every input — and Event-B doesn't let a partial expression's use pass silently; it generates an explicit obligation that the usage is within the expression's domain. The book's table:

| Expression | Well-definedness condition |
|---|---|
| $\bigcap S$ | $S \ne \emptyset$ |
| $\{x \cdot P \mid T\}$ | $\exists x \cdot P$ |
| $f(E)$, $f$ partial | $E \in \text{dom}(f)$ |
| $E / F$ | $F \ne 0$ |
| $E \bmod F$ | $0 \le E \land 0 < F$ |
| $\text{card}(S)$ | $\text{finite}(S)$ |
| $\min(S)$ | $S \ne \emptyset \land \exists x \cdot \forall n \cdot n \in S \Rightarrow x \le n$ |
| $\max(S)$ | $S \ne \emptyset \land \exists x \cdot \forall n \cdot n \in S \Rightarrow x \ge n$ |

Every one of these is generated *automatically*, wherever the corresponding construct textually occurs — in an axiom, invariant, guard, action, variant, or witness. This is precisely the discipline a Rust-style verifier needs for partial operations that aren't statically ruled out by the type system (array indexing, division, unwrapping an option) — a division-by-zero or an out-of-bounds index isn't a *type* error, it's a **well-definedness proof obligation**, discharged the same way any other verification condition is, rather than deferred to a runtime panic. `WD` is the cleanest possible illustration that "does this expression even make sense" is not a syntactic question in a language with partial operators — it's a semantic one, answered by proof, exactly like every other property in this chapter.

```lean
-- Lean's own division is total (returns 0 for x/0) precisely to *avoid* needing
-- a WD-style side condition at every use site — a design trade-off worth noting:
-- Event-B keeps division partial and pushes the burden onto proof obligations;
-- Lean keeps it total and pushes the burden onto "know that 0 is a garbage value."
-- A refinement-typed language modeling division faithfully would want the Event-B
-- move: E / F  well-typed only under a proof obligation  F ≠ 0.
def safe_div (e f : Int) (h : f ≠ 0) : Int := e / f
```

## Where this leads

This catalogue is the complete list of *ways a model can fail to be well-formed*, and every one of them will recur, by name, throughout the rest of the book's worked examples — a stuck `INV` proof is how missing guards get discovered (Chapter 2), `GRD`+`SIM` is exactly what gets exercised at every refinement step of every case study, and `VAR`/`NAT`/`FIN` govern every convergence argument from the file-transfer protocol's `receive` event onward. **[[Refinement-Theory|Refinement Theory]]**, the next topic, is where `GRD` and `SIM`'s joint content gets its full theoretical treatment — trace semantics, forward/backward simulation — beyond the single-event mechanics given here. Chapter 14 (outside this batch) later supplies the *mathematical justification* for why these particular rules are sound, grounding them in trace semantics of Event-B developments — worth returning to once the case-study chapters have made the rules feel routine.

**Bearing on the standing project:** this whole section is close to a checklist for your own verifier's VCGen — `INV` is the loop/transition-invariant obligation your Hoare-triple checker generates at every program point; `FIS`/`WFIS` are exactly the existential-satisfiability queries your CSP kernel needs to answer to show a specification is even implementable before attempting refinement; `GRD`+`SIM` is the simulation-relation proof obligation pair underlying data-refinement correctness (relevant directly if your compiler's IR-lowering passes need correctness proofs); the `NAT`/`FIN`+`VAR` triple is a ready template for a termination-obligation generator in your abstract-interpretation pass; and `WD`'s domain-side-condition table is a direct pattern for how a refinement-type system should treat partial operations (array indexing, division, `Option::unwrap`) as proof obligations rather than as either static type errors or deferred runtime panics.
