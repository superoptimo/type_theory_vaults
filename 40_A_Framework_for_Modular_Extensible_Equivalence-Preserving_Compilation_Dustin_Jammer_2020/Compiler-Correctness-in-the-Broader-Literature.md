---
title: Compiler Correctness in the Broader Literature
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "3.4 Why Equivalence Preservation; 5.2 Multilanguage Semantics"
pages: "30, 43–44"
tags: [automated-reasoning, type-theory, compiler-verification, related-work]
---

[[book-guidelines|↩ Back to guidelines]]

## Placing Pyrosome on the map of compiler-correctness approaches

[[Equivalence-Preservation-versus-Contextual-Equivalence]] argued for a specific correctness criterion (equivalence preservation with respect to an equational theory) largely on its own terms — what problem it solves, what blind spots it has, how it's patched. This article covers the same design choice from the other direction: how it compares against the two dominant alternative traditions in the verified-compiler literature, **whole-program simulation** (CompCert) and **multilanguage semantics** (Perconti and Ahmed and successors) — and why each of those, despite real strengths, resists the specific extensibility goal this thesis is built around.

**What breaks without situating the work this way:** a correctness criterion is only meaningful relative to what it lets you *do* with the resulting proof. "Equivalence preservation" sounds like a weaker, less impressive-sounding guarantee than "full simulation of program behavior" — until you see what each buys and costs with respect to linking and extension, which is the actual axis this thesis cares about.

## CompCert: whole-program simulation, vertically compositional, but closed-world

CompCert (Leroy et al., 2016) proves **whole-program simulation** — the target program's execution trace simulates (matches, step for step, up to the target's own operational granularity) the source program's execution trace — and derives **trace refinement** from it: any observable behavior the target program exhibits is also a behavior the source program could exhibit.

This kind of closed-program simulation has a genuinely valuable structural property: it is **inherently vertically compositional**. If pass $A$ simulates its input, and pass $B$ simulates *its* input (which is $A$'s output), then the composite $B \circ A$ simulates the original source, essentially for free — this is exactly why CompCert's own proof is cleanly divisible pass-by-pass, each pass proved once and chained together. (Pyrosome achieves an analogous vertical-composition benefit for equivalence preservation, per [[The-Preserving-Predicate-and-Modularity-Theorems]]'s discussion of chaining compiler stages — but by a different mechanism, since equivalence preservation isn't automatically compositional in the same structural sense simulation is; it composes because the *same* target notion of equivalence is shared across the composed stages.)

The limitation: **simulation of closed programs says nothing about linking.** CompCert's guarantee is stated for whole, self-contained programs — it doesn't extend to "take this separately-compiled fragment and link it against code the compiler never saw." Modern software is built almost entirely out of linked fragments — libraries, separately compiled modules, hand-written assembly stubs — so a correctness notion that only covers whole programs misses the case that matters most in practice (Ahmed, 2015). This is the same linking gap [[The-Problem-of-Extensible-Compiler-Verification]] opens with.

A separate line of work (Wang et al., 2014) solves linking specifically for programs sharing one fixed low-level target language — but the thesis notes it's unclear how to extend such a framework to support *modular addition of new target-language features*, which is exactly the axis Pyrosome is designed around.

## Multilanguage semantics: expressive linking, but contextual-equivalence-bound

Perconti and Ahmed (2014) — already introduced in [[The-Problem-of-Extensible-Compiler-Verification]] — solve the linking problem far more thoroughly than separate-compilation approaches: their correctness result supports linking compiled code against **genuinely arbitrary target-language code**, not just code from the same compiler or source language. The mechanism is a **multilanguage semantics**: build one combined operational semantics containing constructs from *every* source and target language under consideration, with explicit interoperability rules connecting them, and state compiler correctness as a property of terms in this combined language.

The literature has several instances of this approach (Matthews and Findler, 2009; Perconti and Ahmed, 2014; Ahmed, 2015), and each one is characterized by the same pattern: **the multilanguage is designed ad hoc, per project**, rather than built from a formal, reusable, general framework for combining languages. Bowman (2021) takes a step toward generalizing this — expressing compiler cases as operational rules in a more systematic way — but the thesis notes it remains limited by the same underlying issue as the earlier work.

That underlying issue is exactly the one [[Equivalence-Preservation-versus-Contextual-Equivalence]] developed in depth: **these multilanguage constructions specify compiler correctness in terms of contextual equivalence.** Because contextual equivalence is not robustly monotonic under language extension (the callTwice phenomenon — adding features can retroactively distinguish previously-indistinguishable terms), a multilanguage built and verified against one fixed set of languages **cannot be extended** with new supported source features, new target features, or additional compiler passes without re-examining — and potentially invalidating — the existing contextual-equivalence-based correctness argument. The ad hoc construction compounds this: since the multilanguage itself isn't built from a generic, reusable notion of "language extension," there's no formal apparatus even available to ask "what happens to my correctness proof if I add one more language to the mix."

## The contrast, stated precisely

| | CompCert-style simulation | Multilanguage semantics | Pyrosome |
|---|---|---|---|
| Linking | Not supported (closed programs only) | Fully supported (arbitrary target code) | Fully supported (open terms, per [[Compilers-as-Finite-Maps]]) |
| Vertical composition (chaining passes) | Free, structural | Not the focus | Free, via shared equational theory at each boundary |
| Extending with new features | Requires re-proving simulation for the new whole program | Requires rebuilding/re-verifying the ad hoc multilanguage; blocked by contextual equivalence | Modular — Theorem 1, per [[The-Preserving-Predicate-and-Modularity-Theorems]] |
| Underlying equivalence notion | Trace/behavioral refinement | Contextual equivalence | Equational-theory equivalence, monotonic by construction |

Pyrosome's positioning, in one sentence: it trades away CompCert's stronger closed-program simulation guarantee and Perconti–Ahmed's fully general contextual-equivalence-based linking guarantee, in exchange for a *weaker but more robustly extensible* correctness notion — a trade the thesis argues is worthwhile precisely because extensibility, not raw guarantee strength, is the bottleneck actually blocking verified compilers from being adopted for real, evolving languages.

## Where GATs sit relative to other generic metatheory frameworks (brief, forward-pointer)

Two more comparisons, developed fully in [[Related-Frameworks-and-Future-Directions]], are worth flagging here because they're really the same argument applied to *frameworks for defining languages* rather than *frameworks for stating compiler correctness*: Felleisen's (1991) expressive-power framework gives meaning to programs via an arbitrary termination predicate plus a *contextual*-equivalence relation built from it — the same notion this article and [[Equivalence-Preservation-versus-Contextual-Equivalence]] argue is too strong for extensible reasoning, now showing up one level up, in how the *ambient framework* itself defines "what a language means." GATs sidestep this by presenting semantics equationally from the start.

## Grounding: what "closed-program" vs. "open/linkable" correctness looks like in practice

**Rust (primary).** A CompCert-style correctness statement is naturally a property of a `fn compile(whole_program: Program) -> TargetProgram` — it only typechecks (semantically) to ask about complete programs. An open-terms, linkable correctness statement instead has to be a property that holds for *any* term with free metavariables, which is exactly why [[Compilers-as-Finite-Maps]] requires compilers to be defined via substitution-invariant traversal rather than whole-program transformation:

```rust
// Closed-program correctness: only meaningful for a COMPLETE program.
fn compcert_style_correct(whole: &Program) -> bool { simulates(compile(whole), whole) }

// Open-term correctness: meaningful for ANY fragment, with free metavariables,
// because it's stated in terms of substitution-compatibility, not whole-program behavior.
fn pyrosome_style_correct(fragment: &Term) -> bool {
    // holds for fragment REGARDLESS of what gets substituted in later
    substitution_invariant(compile, fragment)
}
```

**Lean (secondary).** The multilanguage-semantics approach is structurally similar to building one big combined inductive type with constructors from several sub-languages plus explicit "boundary" constructors connecting them — a pattern Lean developments sometimes reach for when gluing together two independently-defined formal systems. The thesis's critique (ad hoc, not extensible, contextual-equivalence-bound) applies just as much there: a hand-built combined inductive type has exactly the same "grows brittle with every added language" problem as an ad hoc multilanguage.

**Python (tertiary).** Not a natural fit for illustrating whole-program-simulation vs. multilanguage tradeoffs — this is a proof-architecture distinction, not an implementation-pattern one, so no code sketch is offered here per the style guide's "a missing example is better than a misleading one."

## Where this leads

This comparison is the thesis's explicit justification for the correctness notion [[Equivalence-Preservation-versus-Contextual-Equivalence]] develops formally and [[The-Preserving-Predicate-and-Modularity-Theorems]] operationalizes — it's presented as a deliberate trade against two well-established, more "impressive-sounding" alternatives, not as an oversight relative to them. [[Related-Frameworks-and-Future-Directions]] continues the comparison one level up the stack, against alternative *language-definition* frameworks (GATs vs. Felleisen, à la carte metatheory, [[Related-Frameworks-and-Future-Directions#The K Framework|the K Framework]]).

For the workbench's project (`automated-reasoning`): if your compiler/elaborator eventually needs a linking or separate-compilation story — plausible for a refinement-type language meant to interoperate with existing Rust code — this table is a direct decision framework for which correctness notion to commit to, and a warning that "prove full simulation" and "support open linking with extensible features" are in real tension, not just different flavors of the same guarantee.
