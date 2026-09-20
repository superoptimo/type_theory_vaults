---
title: Extending the Case Study
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "4.1 Recursive Functions; 4.2 Global State and Evaluation Contexts; 4.3 Substitution"
pages: "35–40"
tags: [type-theory, automated-reasoning, substitution, evaluation-contexts, recursion]
---

[[book-guidelines|↩ Back to guidelines]]

## Stress-testing modularity with three genuinely hard features

[[The-STLC-to-CPS-to-Closures-Case-Study]] built the base two-pass compiler. This article covers the payoff moment of the whole thesis: adding **recursion**, **global mutable state**, and formalizing **substitution** itself — three features chosen specifically because each one interacts nontrivially with the machinery already built, and each interaction is exactly the kind of thing that would force a from-scratch reverification in a non-modular framework. If [[The-Preserving-Predicate-and-Modularity-Theorems]]'s promise ("extend without redoing old proofs") is going to fail anywhere, it's here.

## Recursive functions: a construct that needs its own compiler case, but reuses everything else

STLC gains $\mathrm{fix}\ f(x{:}A) := e$, a recursive function value assigned the *same type* $A \to B$ as an ordinary lambda — meaning it reuses the existing application form and reduction rule shape, differing only in what gets substituted for what upon reduction:

$$
\Gamma \vdash (\mathrm{fix}\ f(x{:}A):=e)\,v = e[(\mathrm{fix}\ f(x{:}A):=e)/f,\ v/x] : B
$$

Notice this substitutes **two** things at once — the function for its own name $f$ (so a recursive call inside $e$ resolves back to the whole `fix` term) and the argument for $x$ — a genuinely new pattern beyond ordinary beta's single substitution.

**CPS translation** adds an analogous recursive-continuation construct to the target calculus and a corresponding translation rule. Because Theorem 4 (the base CPS compiler satisfies `Preserving`, from [[The-STLC-to-CPS-to-Closures-Case-Study]]) is already proved, extending it to recursion needs exactly **three new obligations** — type preservation for recursive functions, preservation of the recursive-reduction rule, and a substitution-related obligation (deferred to this article's own substitution section below) — not a re-proof of everything already established for plain STLC. This is Theorem 1 (compiler extension) from [[The-Preserving-Predicate-and-Modularity-Theorems]], operating exactly as advertised: **Theorem 5** ("the CPS translation for recursion satisfies `Preserving`") is stated and proved as an *addition* on top of Theorem 4, not a replacement of it.

**Closure conversion for recursion is where things get genuinely subtle**, and the thesis's handling of it is a good worked example of "what does it mean to design a language feature so its metatheory stays modular." Naively fusing recursion's self-reference into the existing single `clo⟨...⟩` construct (from [[The-STLC-to-CPS-to-Closures-Case-Study]]) would tangle two independent concerns — "capture the lexical environment" and "make a value refer to itself" — into one construct's equations, forcing every future reasoning step about closures to also reason about recursion. Instead, the thesis introduces a **separate fixpoint combinator**:

$$
\dfrac{\Gamma \vdash v : \neg(\neg A \times A)}{\Gamma \vdash \mathrm{fix}\ v : \neg A}
\qquad\qquad
\Gamma \vdash (\mathrm{fix}\ v)\,v' = v\,\langle \mathrm{fix}\ v,\ v' \rangle
$$

— a construct whose *only* job is "take a continuation expecting (itself, an argument) and tie the self-reference knot," entirely independent of environment capture. The translation of `fix f(x:A) := e` then **splits** into: closure-convert the body as an ordinary (non-recursive) closure over an environment that additionally contains a slot for "myself," then wrap that closure with the standalone `fix` combinator. Some verbose tuple rearrangement is needed to make the environment shapes line up, but the payoff is exactly what modularity requires: **closure laws (beta/eta from [[The-STLC-to-CPS-to-Closures-Case-Study]]) apply to the body unchanged**, because recursion has been "cordoned off" into its own orthogonal piece of syntax rather than smeared across the closure construct's own equations.

**What breaks without this separation:** if recursion were fused directly into `clo⟨...⟩`, every future proof touching closures (including ones about totally unrelated features added later, per the disjoint-extension requirement in Theorem 1) would risk having to additionally reason about the self-reference behavior, even when the feature in question has nothing to do with recursion. Separating orthogonal concerns into orthogonal syntax is a *design discipline* the modularity theorems reward — the theorems don't automatically make your feature design modular, they make a *well-factored* feature design's proof modular.

## Global state: heaps, evaluation contexts, and a genuinely cross-cutting interaction

The global-store extension (previewed informally in [[The-Problem-of-Extensible-Compiler-Verification]] and [[Language-Specifications-as-Equational-Theories]]) depends on two supporting extensions:

1. **Heaps** — given their own sort, governed by the ordinary axioms of finite maps (lookup, update, and the expected interactions between them).
2. **Evaluation contexts** $E$, with judgment form $\Gamma \vdash E : A \rightsquigarrow B$ ("plugging an $A$-typed hole into $E$ yields a $B$-typed term") and a **plug** operation $E[e]$.

Evaluation contexts are the genuinely interesting cross-extension interaction, and the thesis is explicit about *why they're needed at all* given that Pyrosome already provides congruence "for free" (per [[Compilers-as-Finite-Maps]] and [[Language-Specifications-as-Equational-Theories]]): congruence lets you reduce *inside* an arbitrary surrounding term for **pure** features (functions, products) without any extra apparatus, because a pure reduction's correctness doesn't depend on *where* in the program it happens. A **stateful** operation's correctness *does* depend on that — accessing the heap needs the axiom to talk about "the rest of the program, wrapped around this heap access, together with the whole configuration's heap," which is precisely what a configuration $\langle H, E[\mathrm{get}\ n]\rangle$ and its rewrite $\langle H, E[H(n)]\rangle$ express (already worked out equationally in [[The-Preserving-Predicate-and-Modularity-Theorems]]'s discussion of this exact obligation). Evaluation contexts are the formal device that lets an equation "focus on one subterm while still being stated about the whole configuration."

**Then the twist**: since the CPS pass already sequences computations via $\mathrm{bind}\ x := e;\ e'$ (from [[The-STLC-to-CPS-to-Closures-Case-Study]]), evaluation contexts turn out to be **entirely compilable away** during CPS translation — `bind`-sequencing already says, natively, "do this subcomputation, then continue with the rest," which is exactly what an evaluation context was formalizing at the source level. The translation maps evaluation-context judgments to CPS judgments with one extra free variable, conventionally $x_h$ ("hole"), and **plug becomes a `bind`**:

$$
\lfloor [\,]\rfloor \triangleq k\,x_h \qquad\qquad \lfloor E[e]\rfloor \triangleq \mathrm{bind}\ x := \lfloor e\rfloor;\ \lfloor E\rfloor
$$

Because evaluation contexts vanish entirely at the CPS stage, **closure conversion never has to know they existed** — a clean instance of a feature's complexity being fully absorbed by an earlier compiler pass, so later passes stay simple. This is worth flagging explicitly as a design lesson: not every source-language feature needs to survive, as a distinct concept, all the way through the pipeline; sometimes the *right* place to eliminate a feature's complexity is the pass whose own vocabulary (here, `bind`) already subsumes it.

With evaluation contexts compiled away, the heap operations' own CPS translation is almost trivial — `get`/`set` simply take their continuation as an explicit subterm, an inversion of control that means "evaluating an effect inside a context" is no longer even a concern the closure-conversion pass has to reason about; it just reuses the CPS-level translation for heap operations directly, needing only minor adjustment (`get x as v in e ↦ get x as ⌊v⌋ in e[⟨z,x⟩/z]`) to account for the fact that closure conversion changed what the ambient environment binder looks like.

## Substitution: generated, not hand-written, per language

The thesis has, up to this point, used substitution notation ($e[v/x]$, $\gamma(e)$) as if it were free. Section 4.3 makes good on that debt: substitution is implemented as **an explicit substitution calculus**, itself just another Pyrosome language module (derived from Sterling's dependently-typed version, simplified to simply-typed here to stay within reach of the current proof automation — see [[Proof-Automation-and-Elaboration]]).

The key representational idea: **object-language variables are literal repeated applications of a weakening substitution $\uparrow$ to index $0$** — de Bruijn variables aren't a separate primitive, they're *built from* the substitution calculus's own vocabulary. Applying a substitution $\gamma$ to index $0$ retrieves $\gamma$'s first value; composing $\gamma$ with $\uparrow$ first (i.e. $\gamma \circ \uparrow$) discards that first value and shifts everything over. A representative fragment (Figure 4-5):

$$
\dfrac{\vdash \gamma : \Gamma \Rightarrow \Gamma' \qquad \Gamma' \vdash_v v : A}{\Gamma \vdash_v \langle \gamma, v\rangle \circ {\uparrow} = \gamma : \Gamma \Rightarrow \Gamma'}
$$

says precisely: extend $\gamma$ with a new value $v$ (giving $\langle\gamma, v\rangle$), then discard that new slot via $\uparrow$-composition, and you're back to plain $\gamma$ — the substitution-calculus analogue of "push then immediately pop is a no-op."

**Why this matters for extensibility specifically: substitution equations are generated systematically from a language's own syntax rules, not hand-written per feature.** Outside Pyrosome, mechanizing this case study would require writing a bespoke substitution function with one case per syntactic form, *for every language in the pipeline* — three separate hand-written substitution implementations (STLC, CPS calculus, closure calculus), each a fresh source of bugs and each needing its own correctness lemmas. Inside Pyrosome, because term rules already have a fixed, uniform shape (metavariables with declared sorts, explicit vs. inferred subterms — per [[Language-Specifications-as-Equational-Theories]]), the framework can **read off** the substitution-compatibility equation a given syntactic form needs, directly from its term-rule declaration, e.g. for STLC application and lambda:

$$
\gamma(e\,e') = \gamma(e)\,\gamma(e') \qquad\qquad \gamma(\lambda A.\,e) = \lambda A.\ \langle\gamma, 0\rangle(e)
$$

These generated equations do become part of the compiler's **trusted specification** (they're not independently proved sound against some outside notion of "correct substitution" — they're stipulated, by construction, from the syntax) — but the thesis argues this trust is easy to audit precisely *because* the generation is systematic and uniform, rather than ad hoc per-language code that could each hide its own idiosyncratic bug.

The payoff for a multi-pass pipeline specifically: **substitution behavior on values is reused, not reimplemented, across CPS and closure conversion.** The CPS calculus swaps STLC's returning-expression judgment for a nonreturning-computation judgment, but reuses the *same* value-substitution behavior; closure conversion targets the same substitution calculus as CPS, so there's minimal duplicated substitution machinery across the entire three-language pipeline — a concrete instance of "prove it generically once, reuse forever" applied to what would otherwise be the single most repetitive, bug-prone part of a multi-language compiler pipeline.

## Grounding: what "generated substitution" looks like as code

**Rust (primary) — substitution as data-driven codegen from a term-rule declaration, rather than hand-written per constructor:**

```rust
/// A term rule already declares which positions are metavariables and
/// their sorts (per Pyrosome's own representation) — enough information
/// to derive the substitution-compatibility equation MECHANICALLY,
/// instead of a human writing a `subst` match-arm per constructor.
struct TermRule {
    tag: String,
    subterm_sorts: Vec<Sort>,   // what Language-Specifications-as-Equational-Theories calls premises
}

fn generate_subst_equation(rule: &TermRule) -> Equation {
    // γ(#tag t1 .. tn) = #tag γ(t1) .. γ(tn), with binder-shifting where a
    // subterm's sort indicates it's under an extended context.
    Equation::congruence_under_substitution(rule)
}

/// Contrast: the naive approach requires ONE HAND-WRITTEN match arm
/// per constructor, per language, in the pipeline — three languages
/// here means three independent, bug-prone implementations.
fn naive_subst(term: &Term, gamma: &Subst) -> Term {
    match term {
        Term::App(e, ep) => Term::App(Box::new(naive_subst(e, gamma)), Box::new(naive_subst(ep, gamma))),
        Term::Lambda(a, e) => Term::Lambda(a.clone(), Box::new(naive_subst(e, &gamma.extend_with_fresh()))),
        // ... one arm per constructor, PER LANGUAGE, forever
    }
}
```

**Lean (secondary) — de Bruijn variables as `Fin n`, and substitution as a well-studied, previously-formalized pattern.** If you've built or used a de Bruijn-indexed term representation in Lean, "a variable is a repeated weakening of index 0" is exactly the pattern behind `Fin.succ`-style index shifting under a binder, and the $\langle\gamma,v\rangle \circ {\uparrow} = \gamma$ law here is structurally identical to the standard "substitution-composition" lemmas (`comp_ren_subst`, `subst_id`, etc.) that libraries like Lean's own metaprogramming or a hand-rolled STLC formalization prove once and reuse everywhere. This is the *exact* proof-obligation shape your elaborator's metavariable-substitution machinery will need to get right for `isDefEq` to be sound under partial instantiation.

**Python (tertiary sketch)** of evaluation-context elimination via `bind`, the cleanest single idea to show quickly:

```python
def compile_plug(E, e):
    # ⌊E[e]⌋ = bind x := ⌊e⌋; ⌊E⌋   — the hole becomes an explicit sequencing point
    return cps_bind("x", compile(e), compile_context(E))
```

## Where this leads

This chapter is the thesis's strongest evidence that the modularity theorems ([[The-Preserving-Predicate-and-Modularity-Theorems]]) deliver on genuinely hard cases, not just the textbook STLC example: recursion needed real design care (the fixpoint-combinator separation) to *stay* modular, evaluation contexts demonstrated a feature whose complexity is fully absorbed by an earlier pass, and substitution demonstrated the single biggest potential source of per-language duplicated effort being eliminated by generation. [[Proof-Automation-and-Elaboration]] covers how much of the resulting proof obligations were discharged automatically, and the combined-compiler correctness statement (Theorem 6) is summarized in the guidelines' Chapter 4 discussion.

For the workbench's project: the fixpoint-combinator separation is a direct design lesson for how to add recursive types or fixed-point combinators to a Rust-hosted elaborator without entangling them with your environment/closure representation; the generated-substitution technique is close to a checklist for what your elaborator's metavariable-substitution infrastructure should look like if you want it to scale past a handful of hand-written cases (`type-theory`, `automated-reasoning`) — treat "substitution equations should be derivable from the term-rule shape, not written by hand per constructor" as an architectural target, not an optional nicety.
