---
title: Related Work and Positioning
source: Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)
chapters: Section 4, "Related work and conclusions" (pp. 24–26)
tags: [type-theory, elaboration, lean, unification, type-classes, related-work]
---

[[book-guidelines|↩ Back to guidelines]]

## Why a paper about one system's elaborator needs a "related work" section at all

Every design choice described across the rest of this vault — [[Higher-Order-Unification|how Lean resolves flex-rigid constraints]], [[Type-Classes-and-Class-Inference|how it searches for instances]], [[The-Constraint-Solving-Procedure|how it backtracks]] — was a decision made under trade-offs, not a discovery of the One True Algorithm. Elaboration for dependent type theory is, as the paper's introduction puts it, "something of a dark art": several independently developed systems (Coq, Isabelle, Agda, Idris) had each converged on *some* working elaborator, but rarely documented *why* their choices looked the way they did or how they compared to alternatives. Section 4 closes the paper by placing Lean's specific bundle of choices — full backtracking search, no dependency erasure, no free variables inside metavariables, choice constraints for both classes and coercions — against four other lines of work that each made different trades. Reading this section is less "here is a survey" and more "here is what we deliberately chose *not* to do, and why."

The comparison naturally sorts along the same fault line the rest of the paper has been walking since [[Higher-Order-Unification|Section 2.2]]: how aggressively should the elaborator commit to unification decisions eagerly (fast, but sometimes wrong or incomplete) versus defer them and search (complete-ish, but potentially expensive)?

## Abel and Pientka: pruning as an extension of the pattern fragment

The starting point for this whole line of research is Miller's observation, already covered in [[Higher-Order-Unification]], that most higher-order unification problems arising in practice are *patterns* — metavariables applied only to distinct bound variables — and patterns admit a unique, efficiently computable most general unifier, unlike the general higher-order case, which is undecidable.

Abel and Pientka's contribution is to widen that well-behaved fragment. Their technique, called **pruning**, intuitively strips away metavariable arguments that fall outside the pattern shape, in effect throwing away information the solver can't use anyway in exchange for finding *more* solutions than the strict pattern algorithm would. They pair this with a bidirectional type-inference system for a dependently typed calculus, and prove the unification algorithm sound with respect to that type system — a genuine formal guarantee the Lean paper's own algorithm does not attempt to provide (recall from [[The-Constraint-Solving-Procedure]] that Lean's solver is a pragmatic backtracking search, not one accompanied by a completeness or soundness proof).

The paper flags one specific limitation as the hinge for what comes next: Abel and Pientka's system does not treat **defined constants**, with or without recursion. That's precisely the machinery covered in [[Computational-Behavior-and-Reduction]] — the reducibility annotations and delta-unfolding heuristics that let Lean's unifier decide *when* to unfold a `def` while searching for a solution. Handling defined constants turns out to be the crux of making pattern-style unification usable on a real proof library, which is exactly the gap Ziliani and Sozeau's work (and Lean's) tries to close.

## Ziliani and Sozeau's Coq unifier: solving more, keeping less

Ziliani and Sozeau's algorithm for Coq is described as sharing Lean's own motivation closely — describing the *practicalities* of unification for a realistic, full-featured dependently typed language, including defined and recursively defined constants, rather than a clean fragment of the theory. Where it diverges from Lean is in how it buys extra solving power.

On top of Abel and Pientka's pruning, they add two more aggressive techniques:

- **Dependency erasure.** Given a problem like $\{?t\ \mathsf{true} \approx \mathsf{nat},\ ?t\ \mathsf{false} \approx \mathsf{nat}\}$ — a metavariable $?t$ applied to two different concrete arguments, each equated with the same type — their system just drops $?t$'s dependency on its argument, reducing the problem to $?t' \approx \mathsf{nat}$ and solving it as $?t \mapsto \lambda x, \mathsf{nat}$. This *finds a solution* to a case that a strict pattern check would reject outright, at the direct cost of uniqueness: there could be other, dependency-preserving solutions that this rule can never reach.
- **First-order approximation.** A constraint like $?f\ ?y \approx S\ 0$ (the successor of zero, both sides literally applications) gets solved by matching structurally: $?f \mapsto S$, $?y \mapsto 0$, treating an inherently higher-order-shaped equation as if it were first-order.

The Lean paper's response is a direct contrast in solving philosophy, not just technique. Because Lean's own [[The-Constraint-Solving-Procedure|constraint solver]] already embraces multiple solutions and full backtracking search as first-class behavior, both of these example problems are handled *without* a special-purpose rule: the dependency-erasure case falls out as a special case of ordinary **projection**, and the first-order-approximation case falls out as an ordinary **imitation** step — both standard moves in the [[Higher-Order-Unification|Huet-style flex-rigid case split]] already in the toolkit. Where Ziliani and Sozeau add targeted machinery to reach specific solutions up front, Lean gets the same solutions "for free" as instances of a general search procedure it already needed for other reasons.

A second, more structural divergence concerns how the two systems represent free variables trapped inside a metavariable's scope. Lean's answer, stated with characteristic bluntness, is: *there are none*. Recall from [[Term-Representation-and-Core-Data-Structures]] that Lean enforces closed-term-only metavariable assignment — a metavariable can only ever be assigned a term that is already closed with respect to its own local context, sidestepping the free-variable bookkeeping problem entirely at the representation level. Ziliani and Sozeau instead carry a **suspended substitution** alongside every metavariable, which must be actively managed and applied at each resolution step — a more expressive but more operationally expensive representation.

Where the two systems land closer together is delta-unfolding heuristics (see [[Computational-Behavior-and-Reduction]] and [[The-Constraint-Simplification-Procedure]] for Lean's own version): both defer unfolding a constant until after type-class resolution has had a chance to apply, and both treat unfolding to a pattern match or fixpoint as a last resort rather than a default move. The paper is careful to flag this convergence as observational, not as evidence of correctness either way — "more study is needed to examine the trade-offs of these various choices."

The final point of difference is about **postponement**. Lean's solver, as covered in [[The-Constraint-Solving-Procedure]], can push a constraint onto a priority queue and revisit it later once other constraints have resolved enough metavariables to make it tractable — this is central to how Lean handles interleaved unification, type-class, and coercion resolution as one unified problem. Ziliani and Sozeau's system does not allow postponing constraints at all, relying instead on pruning and dependency erasure to dispatch most cases immediately, up front. They report this yields real efficiency gains — but the Lean paper, again, treats the trade-off as open rather than settled.

## Type classes elsewhere: Coq, Matita, and Isabelle

The paper broadens from unification specifically to the type-class and structure-inference machinery covered in [[Type-Classes-and-Class-Inference]] and [[Overloading-and-Coercions]].

Several independent developments inside Coq use **type classes** directly, and others use **canonical structures** — a related mechanism for attaching inferable data to a type — for building algebraic hierarchies; Matita's analogous mechanism is called **unification hints**. These represent close cousins of Lean's own approach: structure-based classes resolved by [[Type-Classes-and-Class-Inference|backward-chaining, Prolog-like instance search]].

Isabelle sits at a genuinely different point in the design space, because it is built on *simple* type theory rather than dependent type theory. It reaches for **axiomatic type classes** together with **locales** (parameterized contexts) to express algebraic structures, and has its own mechanism for inserting [[Overloading-and-Coercions|coercions]]. The paper's key claim about why this matters is concrete and structural, not just stylistic: an algebraic structure that depends on a *parameter* — the running example is the integers modulo $m$, i.e. $\mathbb{Z}/m\mathbb{Z}$ for a variable $m$ — cannot be represented as a type in simple type theory at all, and therefore cannot be made an instance of an axiomatic type class. Lean's structures, being ordinary dependently typed terms, can depend on such a parameter exactly the way any other dependent construction can (a structure genuinely is a $\Sigma$-type in disguise, per [[Type-Classes-and-Class-Inference]]). A second, more architectural contrast: Isabelle uses *separate languages* for constructing expressions, building proofs, and stating relationships between structures, where Lean's propositions-as-types foundation (see [[The-Elaboration-Task]]) lets one term language and one elaborator serve all three jobs at once.

## Idris: elaboration as theorem-proving-by-analogy

Brady's work on Idris takes a philosophically distinct route: it describes elaboration itself *by analogy with theorem proving*, in the setting of pure functional programming. The paper draws the contrast sharply — Lean's design keeps its [[Tactics-and-Proof-Structuring|tactic language]] *completely disjoint* from the mechanisms used to resolve unification constraints, where Idris's elaboration process is itself structured as a form of proof construction.

The paper also points to a difference in the shape of the unification problems each system actually has to solve. In Lean, metavariables can be highly non-local — appearing simultaneously in disparate, unrelated parts of a large in-progress term — and the *set of candidate solutions* the solver has to search over can be an infinite stream rather than a small, enumerable case split. This is a direct echo of why [[The-Constraint-Solving-Procedure|nonchronological backtracking]] matters so much to Lean's design: a naive re-search from scratch after every failure would be untenable against a search space of that shape.

## Evidence of practice, and the paper's own summary

Before any of the comparisons, Section 4 opens by grounding the whole discussion in real usage: the algorithm was developed and tuned *in conjunction with* building out Lean's standard library (roughly 42k lines at time of writing — core datatypes, number systems, the algebraic hierarchy through Sylow's theorem, elementary number theory including unique factorization, and the beginnings of real analysis) and its homotopy type theory library (over 25k lines, covering most of the first seven chapters of the HoTT book plus a substantial development of category theory through the Yoneda lemma, and — via separate work — a nonabelian algebraic topology development). By the closing summary, the paper cites more than 65k lines of formalized library as the algorithm's real-world proving ground. This framing matters for how to read the whole comparison section: every trade-off discussed above (search versus eager commitment, closed metavariables versus suspended substitutions, postponement versus up-front dispatch) is being justified not by a completeness theorem, but by "this scaled to tens of thousands of lines of real formalization."

The paper's own closing self-summary is worth stating plainly, since it is the thesis the entire vault has been unpacking piece by piece: Lean's elaboration procedure borrows techniques from state-of-the-art constraint solvers — nonchronological backtracking, indexing, and justification tracking (see [[Constraints-and-Justifications]] and [[The-Constraint-Solving-Procedure]]) — and uses that same general-purpose machinery, via **choice constraints**, to integrate coercions, type classes, and ad hoc polymorphism smoothly into one unified elaboration problem, rather than bolting each on as a separate special-purpose pass.

## Synthesis: what this section closes

Structurally, this article sits downstream of everything else in the vault: it presupposes the mechanism ([[Higher-Order-Unification]], [[Type-Classes-and-Class-Inference]], [[The-Constraint-Solving-Procedure]]) in order to say what alternative choices existed at each decision point. The throughline across all four comparisons is the same tension that opened [[The-Elaboration-Task]]: how much of the hard work should be pushed into a general, uniform search-and-backtrack engine (Lean's answer, and to a lesser extent Abel & Pientka's), versus how much should be resolved by targeted, up-front heuristics that trade completeness for speed (Ziliani & Sozeau's answer)? Lean's bet — one general constraint-solving core with justification-tracked backtracking, reused for unification, type classes, and coercions alike — is what every earlier article in this vault has been describing the internals of; Section 4 is where the paper steps back and explains why that bet was worth taking.

```
Abel & Pientka  ──extends──►  pattern unification (pruning)
                                        │
                                        ▼ (adds defined constants)
Ziliani & Sozeau ──eager heuristics──►  Coq unifier (dependency erasure,
                                         first-order approx., no postponement)
                                        │
                                        ▼ (contrast: search instead of heuristics)
   Lean  ──unified backtracking search──►  unification + type classes + coercions
                                            (this vault, Sections 2–3)

Isabelle (simple type theory)  ──structural limit──►  no parameterized structures
Idris  ──proof-by-analogy──►  tactics fused with elaboration (vs. Lean's disjoint design)
```
