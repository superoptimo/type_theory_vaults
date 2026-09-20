---
title: Related Frameworks and Future Directions
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "5.1 Alternative Generic Frameworks; 5.3 Optimization; 5.4 Modeling Pyrosome's Equational Theories; 5.5 Advanced Type Systems"
pages: "45–48"
tags: [type-theory, generalized-algebraic-theories, trusted-computing-base, future-work]
---

[[book-guidelines|↩ Back to guidelines]]

## Where Pyrosome sits among frameworks for defining languages generically

[[Compiler-Correctness-in-the-Broader-Literature]] compared Pyrosome's *correctness criterion* against CompCert-style simulation and multilanguage semantics. This article closes the loop one level up: how Pyrosome's *language-definition* mechanism (GATs, per [[Pyrosomes-Design-Philosophy]]) compares to other generic frameworks for formalizing programming languages — then surveys the thesis's own honestly-acknowledged limitations and future directions, which double as a map of exactly where this framework's ideas would need extending to support a project like this workbench's dependent/refinement-type compiler.

### GATs vs. Felleisen's operational-semantics framework

Felleisen (1991) gives programs meaning via an arbitrary termination predicate plus a **contextual-equivalence relation** built from it. This is the same notion whose extensibility problems [[Equivalence-Preservation-versus-Contextual-Equivalence]] developed in depth, now showing up one level higher in the stack: it isn't just that *a particular compiler-correctness proof* using contextual equivalence resists extension — the *ambient framework* for defining "what a language means at all," if built on contextual equivalence from the ground up, inherits the same problem. Generalized algebraic theories sidestep this by presenting language semantics **equationally, from the start** — a fixed, listed set of axioms rather than an implicitly-defined closure over all possible observations.

The thesis adds a design principle here worth internalizing on its own: it deliberately does **not** include every equation that might seem individually reasonable, because "equations that may be reasonable to include, say, in a pure language interact poorly with effectful extensions." This is a direct, practical instance of [[The-Preserving-Predicate-and-Modularity-Theorems]]'s monotonicity requirement — a designer choosing a **minimal** equational theory (only the equations you're sure will remain sound under every extension you intend to support) is buying future extensibility at the cost of not being able to state every intuitively-true fact up front. It's the same tradeoff as choosing call-by-value beta over full beta in [[Equivalence-Preservation-versus-Contextual-Equivalence]], generalized into a design heuristic.

A further, quieter advantage: because GATs don't rely on evaluation to give meaning to terms (unlike operational-semantics-based frameworks, which need a notion of reduction/termination baked in), Pyrosome can treat **fully normalizing** languages and **Turing-complete** languages uniformly, with no special-casing for whether a language happens to always terminate.

### Modular metatheory à la carte, and type/scope-safe syntax with binding

Delaware et al. (2013a,b) mechanized modular metatheory in Coq — covering components like language interpreters with modular soundness properties, in the style of Swierstra's (2008) "data types à la carte." Allais et al. (2018) built a related framework for reasoning about binding, renaming, and translation with real similarities to this thesis's own goals. The thesis's stated distinction from both: **they incorporate object-language binding and substitution directly into the framework's own core metatheory**, rather than treating binding as a first-class, user-definable *feature* the way Pyrosome does (recall from [[Extending-the-Case-Study]] that Pyrosome's substitution calculus is itself just another Pyrosome language module, generated systematically from term-rule shapes). Baking binding into the metatheory is more convenient out of the box — you get substitution reasoning "lifted" into the ambient framework for free — but it costs generality: a framework that has committed to one fixed treatment of binding can't as easily accommodate a language with an unusual binding discipline (dynamic scope, for instance) without reworking the metatheory itself, whereas Pyrosome's tactics were explicitly designed (per [[Proof-Automation-and-Elaboration]]) to be agnostic even to which substitution calculus is in use.

### The K Framework

The K Framework (Roşu and Şerbănută, 2010) has built a mature, extensive ecosystem of generic language-specification tooling, with a logic expressive enough to internalize a variety of binders (Chen and Roşu, 2020) and recent extensions toward certified proofs about individual program behaviors (Chen et al., 2021). The thesis's distinction here is scope, not technique: K doesn't address the **higher-order** concerns this thesis is centrally about — verified *compilation* and *compiler extensibility* specifically, as opposed to specifying and reasoning about a single language's own operational behavior.

## Future direction 1: optimization is fundamentally in tension with the current design

This is arguably the thesis's most important self-critique, and it follows directly from a fact established in [[Compilers-as-Finite-Maps]]: compilers are required to satisfy **syntactic** substitution invariance, $\lfloor\gamma(e)\rfloor = \lfloor\gamma\rfloor(\lfloor e\rfloor)$, literally, as stated — not merely "semantically equivalent to" that equation. This forces a compiler to generate **the exact same target code for every occurrence of a given syntactic form**, regardless of surrounding context — precisely the freedom a real optimizing compiler needs (e.g., specializing a function call's compiled code based on what's statically known about its argument at a particular call site, or eliminating dead code that's locally unreachable even though the same construct is reachable elsewhere).

**What breaks, concretely:** any optimization that makes a compiler's output depend on more than "which constructor is this, and what are its already-compiled subterms" — i.e., anything context-sensitive — violates the finite-map/metavariable-template shape by definition. Constant folding across a whole program, cross-call specialization, and most classical dataflow-driven optimizations are exactly this shape.

The thesis's proposed escape route is narrow but principled: restrict optimization to be **intralanguage** rather than a translation between two different languages. Define an optimization as an arbitrary function $o : \mathrm{term} \to \mathrm{term}$ such that for every well-formed term $e : t$ in some *single* language, $e = o(e) : t$ **in that same language's own equational theory**. Because $o$ relates input and output *within one language* (rather than across a translation boundary), it can, in principle, be inserted into a vertically-composed sequence of translations (per [[The-Preserving-Predicate-and-Modularity-Theorems]]'s vertical-composition discussion) while the composed pipeline still preserves equivalence overall — because "optimize, then translate" and "translate" agree up to the source language's own notion of equality, and equivalence preservation composes through that.

The thesis is candid that this isn't a full solution: an *arbitrary* function $o$ gives up exactly the extensibility guarantees the rest of the framework provides for that language, since nothing about $o$ is required to respect the rule-by-rule, `Preserving`-style modularity — you'd have to re-verify $o$ against the *whole* language it operates on, with no promise that adding a new feature later leaves $o$'s correctness intact. The stated open question — is there a middle ground that expresses standard optimizations while retaining some extensibility — is left explicitly unresolved as future work.

## Future direction 2: shrinking the trusted computing base by modeling target semantics on verified systems

As it stands, every Pyrosome-based correctness theorem trusts **the source- and target-language specifications themselves**, in addition to the framework's own core definitions — if the equational theory you wrote down for your target language doesn't actually characterize what the real hardware or runtime does, your correctness proof says nothing true about the world. The proposed direction: **model** Pyrosome's target-language equational theories **on top of** independently-verified low-level systems — the thesis names CompCert (Leroy et al., 2016) and Bedrock (Erbsen et al., 2021) as concrete targets — so that an end user gets Pyrosome's extensibility benefits at the *upper* levels of a compiler pipeline while inheriting an already-established, independently-trusted foundation underneath, rather than trusting a bespoke target-language axiomatization.

This is a direct, named instance of a general trusted-computing-base discipline this workbench's project should take seriously: a proof-producing architecture's *actual* trust boundary is exactly the set of specifications and axioms it takes as given without independent verification — and reducing that set (by grounding target semantics in an already-verified system rather than a hand-written equational theory) is real progress even when the *upper-level* reasoning (Pyrosome's `Preserving`-style modularity) stays exactly as strong as before.

## Future direction 3: polymorphism, linearity, and dependent types

The thesis states plainly that the **underlying theory** already accommodates a "wide range of features at both the term and type levels," including polymorphism, linearity, and dependent types — the author has even defined a variant of the substitution language (from [[Extending-the-Case-Study]]) that includes **type-level substitutions**, specifically to support polymorphic or dependent types. The choice to restrict the case study to simple types was made for a stated, practical reason: simple types were sufficient to demonstrate the framework's core ideas, and they kept the case study within reach of the current **proof automation** (per [[Proof-Automation-and-Elaboration]]'s documented boundary — the tactics currently struggle specifically with type equations).

The thesis's own framing is important to preserve precisely: this is presented as a **current automation gap**, not a fundamental limitation of the GAT-based representation itself. More complex type systems "should fit naturally within Pyrosome," at the cost of either more manual proof effort today, or better automation techniques in the future — the representation (terms as sorted, tagged trees; languages as rule lists; compilers as finite maps) doesn't inherently privilege simple types, it's specifically the *automated* discharge of `Preserving` obligations that currently does.

## Grounding: reading these future directions as an implementation roadmap

**Rust (primary) — the optimization escape hatch's actual shape, as a type signature that captures exactly what it does and doesn't promise:**

```rust
/// An intralanguage optimization: input and output are terms of the
/// SAME language, related by that language's own equational theory —
/// unlike a `Compiler`, which crosses a language boundary and is
/// restricted to the finite-map/substitution-invariant shape.
trait IntralanguageOptimization<L> {
    /// Caller must independently justify: for all well-formed `e`,
    /// `e` and `optimize(e)` are equal in `L`'s own theory.
    /// Nothing about the trait signature ENFORCES this — it's exactly
    /// the "arbitrary function" freedom (and risk) the thesis flags.
    fn optimize(&self, e: &Term) -> Term;
}

fn insert_into_pipeline<L>(
    opt: &dyn IntralanguageOptimization<L>,
    pipeline: Vec<Box<dyn Compiler>>,
) -> Vec<Box<dyn Compiler>> {
    // insertable because it doesn't cross a language boundary —
    // but re-verifying it against the WHOLE language `L`, not per-rule,
    // is exactly the extensibility cost being given up here.
    todo!()
}
```

**Lean (secondary) — trusted computing base as an explicit design variable.** Lean's own kernel is deliberately kept small precisely so that *it*, and not the elaborator or tactic framework built atop it, is the actual trust boundary — everything the elaborator produces is re-checked by the small kernel. The thesis's future direction of modeling target semantics atop CompCert/Bedrock is the compiler-verification analogue of the same discipline: push as much of the "interesting, extensible, automatable" reasoning as possible into a layer that doesn't need to be trusted directly, because it's checked against (or built on top of) something smaller and already trusted.

**Python (tertiary).** Not a natural target for illustrating trusted-computing-base or type-system-generality tradeoffs — these are architectural, proof-theoretic distinctions rather than implementation patterns, so no code sketch is offered here.

## Where this leads

This closing chapter is less a technical continuation of the thesis's machinery and more an honest accounting of where that machinery's current boundaries are — useful precisely because each boundary names a specific, addressable gap rather than a vague "more work needed." [[Compiler-Correctness-in-the-Broader-Literature]] and this article together form the thesis's full positioning against prior work; [[Proof-Automation-and-Elaboration]]'s automation boundary (type equations, polymorphism, dependent types) is the same boundary named again here as a first-class future-work item.

For the workbench's project directly (`type-theory`, `automated-reasoning`): three of this thesis's stated open problems are close to a checklist for your own compiler/elaborator's hardest design decisions — (1) how to support genuine optimizations without abandoning modular, per-rule extensibility proofs; (2) how to keep your trusted computing base small by grounding target-language semantics in something independently verified rather than a hand-rolled axiomatization, directly relevant to your CSP kernel and abstract-interpretation soundness arguments; and (3) the fact that dependent/refinement types are exactly the frontier where this thesis's own automation techniques stop working — meaning your project is picking up precisely where Pyrosome's stated future work leaves off, not covering already-automated ground.
