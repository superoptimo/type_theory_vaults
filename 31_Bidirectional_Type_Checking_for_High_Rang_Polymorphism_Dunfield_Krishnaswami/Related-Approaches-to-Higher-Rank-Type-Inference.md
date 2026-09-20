---
title: Related Approaches to Higher-Rank Type Inference
source: Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism (Dunfield & Krishnaswami, ICFP '13)
chapter: Section 9, Related Work and Discussion (pp. 11–12)
tags: [type-theory, bidirectional-typechecking, higher-rank-polymorphism, unification, type-inference]
---

[[book-guidelines|↩ Back to guidelines]]

# Related Approaches to Higher-Rank Type Inference

## Why a "related work" section earns its own article

It's tempting to skim a related-work section as bookkeeping — citations, priority disputes, acknowledgments. This one isn't that. Section 9 is where Dunfield and Krishnaswami tell you *why the design space looks the way it does* — what you give up if you make a different choice at each of the three or four forks in the road they took. If you're building your own elaborator, this section is a map of the alternatives you're implicitly rejecting every time you follow this paper's rules instead of someone else's.

The organizing fact, stated plainly in the paper itself:

> "language designers can keep any two of: (1) the $\eta$-law for functions, (2) impredicative instantiation, and (3) the standard type language of System F."

This is a genuine trilemma — a "pick two" tradeoff, like CAP in distributed systems. Every system surveyed here is a different choice of which leg to sacrifice.

## What breaks without the trilemma framing

If you don't have this framing going in, MLF, HML, FPH, and this paper's own system look like an arbitrary pile of unrelated formalisms with different rule names. Once you have it, they snap into a $2\times2$-ish table, and you can predict a new system's shape just by asking "which one did they give up?"

| System | $\eta$-laws? | Impredicative? | System F type language? |
|---|---|---|---|
| MLF | yes | yes | no |
| FPH | no | yes | yes |
| HML | no | yes | yes |
| Peyton Jones et al. (2007) | yes | no | yes |
| **This paper** | **yes** | **no** | **yes** |

*(Figure 15 in the source, reproduced verbatim.)*

Read across a row and you can reconstruct the design decision. MLF keeps $\eta$ and impredicativity, so it must pay by *not* using the ordinary System F type language — it needs a richer type language (bounded quantification) to keep principal types under those two constraints. This paper keeps System F types and $\eta$, so it must give up impredicativity — hence the restriction to *predicative* polymorphism you saw motivated back in [[The-Problem-of-Polymorphism-in-Bidirectional-Systems]]. That restriction wasn't an arbitrary simplifying assumption; it's the specific cell in this table the authors chose to occupy.

Why can't you have all three? The paper points to a decidability result: Tiuryn and Urzyczyn (1996) and Chrząszcz (1998) showed subtyping for *impredicative* System F is undecidable — and the source notes that $\eta$-typability specifically requires "instantiat[ing] deeply," i.e. allowing instantiation of quantifiers to the right of an arrow, which is exactly the move that needs impredicative subtyping to be decidable. So: $\eta$ forces deep instantiation; deep instantiation plus impredicativity is undecidable; therefore $\eta$ + impredicativity forces you off the standard System F type language (MLF's route) or forces predicativity (this paper's route).

## 9.1 — Type inference for System F: the paper's own false start

Section 9.1 is unusually candid for a conference paper: the authors admit the present work descends from an earlier paper of Dunfield's (2009) that tried to extend a similar ordered-context approach to *impredicative* polymorphism plus type-level computation — and whose decidability and completeness proofs turned out to be **unsound**. Rather than patch the broken proofs, they restarted, keeping the high-level ideas (ordered contexts, existentials, subtyping-as-instantiation) but rebuilding the technical machinery from scratch under the predicativity restriction.

This is worth pausing on for engineering reasons, not just as a historical footnote. It's direct evidence that "ordered contexts with existential variables" as a *data structure* is more robust than any particular *typing discipline* built on top of it — the same substrate ([[Algorithmic-Contexts]]) supported both a broken impredicative system and this paper's proven-sound predicative one. If you're designing an elaborator's metavariable context, this is a strong argument for keeping the context machinery decoupled from whatever polymorphism discipline you bolt onto it — you may need to swap the discipline later without rebuilding the substrate.

## 9.2 — Two prior bidirectional/local-inference systems

Two systems get direct comparison, both of which handle polymorphism at *application sites* rather than via a general subtyping relation:

- **Pierce and Turner's local type inference** (2000) — bidirectional typechecking for rich subtyping, instantiating polymorphism specifically within function application. Its declarative specification is "more complex than ours" (the paper's words), and its algorithm computes approximations of upper and lower type bounds — a fundamentally different mechanism from this paper's existential-variable instantiation.
- **Colored local type inference** (Odersky et al., 2001) — lets different parts of a type expression propagate information in different directions (hence "colored": pieces of the type are tagged with a direction). The paper notes their own system "gets a similar effect by manipulating type expressions with existential variables" — same *effect*, different *mechanism*. Existentials are a more uniform way to get directional information flow than hand-coding which subexpressions are colored which way.

## 9.3 — Three ideas, three points of comparison

The paper is explicit about which three ideas it considers its real contributions, and pairs each with the closest prior work:

**1. Ordered contexts vs. skolemization.** Traditional type inference treats existential/unification variables as a "bag of constraints" solved by a separate constraint-solving pass, often using skolemization (replacing a universally-quantified variable with a fresh, opaque constant to reason about it) for scoping. This paper embeds existentials *directly into the ordered context itself*, so scoping falls out of context well-formedness rather than needing a separate model-theoretic device. The paper likens this to Rémy's (1992) level-based generalization, also used internally by MLF — interesting, because it means MLF and this paper converge on a *similar* scope-management mechanism despite landing on opposite sides of the impredicativity trilemma.

**2. The instantiation judgment vs. Cardelli's greedy algorithm.** This is the sharpest, most concrete comparison in the section, and worth working through by hand.

Cardelli's (1993) greedy algorithm eagerly solves an existential the moment it sees the first piece of type information touching it, and never revisits that choice. The paper gives a canonical counterexample to greedy's *completeness*:

> Take $f : \forall\alpha.\ \alpha \to \alpha \to \alpha$, applied to a `Cat` and then an `Animal` (where `Cat <: Animal` in whatever subtyping discipline is in play).

Trace it through greedily:

1. See the first argument, `Cat`. Solve $\hat\alpha := \mathrm{Cat}$ immediately (greedy, no backtracking).
2. Check the second argument, `Animal`, against the now-solved $\hat\alpha = \mathrm{Cat}$. This requires $\mathrm{Animal} \mathrel{<:} \mathrm{Cat}$ — but that's backwards; an `Animal` is not a `Cat`. **Typechecking fails.**
3. Yet the term is perfectly well-typed: instantiate $\alpha := \mathrm{Animal}$ instead (the supertype of both arguments), and both `Cat <: Animal` and `Animal <: Animal` hold. Reversing the *order* of the arguments — checking `Animal` first — makes greedy succeed, which is exactly the smell of an algorithm that's order-dependent where the underlying problem isn't.

So greedy is incomplete: it picks a solution too early and has no way to revise it when later evidence contradicts the choice.

This paper's fix isn't to add general backtracking (which would undermine the "no data structure more sophisticated than a list, no search" claim from the paper's own stated goals). Instead it adds two narrowly-scoped escape hatches, both of which you've already met in [[Algorithmic-Subtyping-and-Instantiation]]:

- **Looking under quantifiers** (rules `InstLAllR`/`InstRAllL`) — before committing to a monotype solution, check whether a feasible instantiation exists *under* a quantifier, rather than eagerly grabbing the first monotype seen.
- **Reaching** (rules `InstLReach`/`InstRReach`) — when an existential needs to be equated with another existential to its right in the context, solve the "wrong" (righter) one instead of failing, since ordering in the context otherwise makes that assignment impossible to express directly.

The paper is candid that both mechanisms are *forced moves*, not elegant design choices freely arrived at: looking under quantifiers is forced by the predicativity restriction (you can't just push an existential under a quantifier without first checking feasibility, the way you might under laxer disciplines), and reaching is forced by the choice to use an *ordered* context at all — the same design decision from idea (1) above. This is a nice illustration of how one clean idea (ordered contexts) generates a downstream obligation (reaching) that a less-structured design wouldn't have needed, but which pays for itself by keeping everything list-shaped instead of needing a real constraint graph.

**For your elaborator:** if you ever hand-roll a "just solve the metavariable when you see its first constraint" unification strategy — which is a very natural first cut — this is the exact failure mode to expect, and the exact minimal fix (bounded lookahead under binders + a rescue rule for backwards-ordered constraints) rather than reaching for full backtracking search.

**3. Context extension vs. Gundry, McBride & McKinna, and vs. Miller's mixed-prefix unification.** The context-extension judgment $\Gamma \longrightarrow \Delta$ (fully covered where it's introduced — see the guidelines' Section 4, "Context Extension") is compared to two lines of prior work:

- **Gundry, McBride, and McKinna (2010)** recast the classical Damas–Milner algorithm as *structured constraint solving under ordered contexts* — the same ordered-context idea, but built for ML-style prenex (rank-1) polymorphism rather than higher-rank, and explicitly aimed eventually at *dependent* types. Their core technical device is a *semantic* notion of information increase; this paper's context extension is its *syntactic* analogue. If you're building toward a dependently-typed elaborator, Gundry et al. is arguably the more directly relevant lineage than this paper's own predicative System F setting — worth tracking down as a next read.
- **Miller's (1992) mixed-prefix unification** is named explicitly as the proof-theoretic lens through which *both* this paper's algorithm and Gundry et al.'s can be understood: "we each restrict the unification problem, and then give a proof-search algorithm to solve the type inference problem." Mixed-prefix unification is Miller's framework for unification problems where variables are quantified in a specific left-to-right order (a "prefix") mixing universal and existential quantifiers — exactly the shape of an ordered algorithmic context with universals and existentials interleaved. This is the same neighborhood as Miller's *pattern unification* (the tractable fragment of higher-order unification where existential-variable arguments are distinct bound variables) — the paper isn't using pattern unification directly, since its existentials only ever range over *monotypes*, not arbitrary higher-order terms, but the proof-theoretic ancestry is the same family. **This is the connection to flag hardest for the elaborator project:** this paper's instantiation judgment is a first-order, monotype-restricted special case of the general mixed-prefix unification problem that Miller's pattern-unification fragment also specializes — different specializations of the same underlying proof-theoretic idea, not unrelated techniques.

## Where this leads

This section closes the loop the paper opened in its introduction: having built a full declarative system ([[Declarative-Type-System]]), an algorithm implementing it ([[Algorithmic-Contexts]], [[Algorithmic-Subtyping-and-Instantiation]], [[Algorithmic-Typing]]), and metatheory proving the algorithm correct, Section 9 steps back and locates that whole construction within the wider space of possible designs — the trilemma, the greedy-vs-reaching contrast, and the mixed-prefix-unification framing are the vocabulary you'd use to explain *why this paper's choices*, rather than someone else's, to a colleague already familiar with the area.

For the elaborator project specifically: the Cardelli greedy-instantiation failure is a concrete regression test to keep in mind once you implement metavariable solving — a naive "solve on first sight" unifier will fail exactly this shape of example, and the fix (bounded quantifier lookahead + a reach-style rescue) generalizes past this paper's monotype-only setting. And the mixed-prefix-unification framing is the bridge from this paper's first-order instantiation judgment to the higher-order, pattern-unification-based metavariable solving your Lean-inspired elaborator will eventually need — the two are related by "how much of the term language existentials are allowed to range over," not by being unrelated ideas.
