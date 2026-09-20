---
title: Proof Automation and Elaboration
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "4.4 Summary of Case-Study Implementation; 4.5 Inference and Automation"
pages: "39–43"
tags: [type-theory, automated-reasoning, elaboration, proof-automation]
---

[[book-guidelines|↩ Back to guidelines]]

## Modularity buys structure; automation is what makes the structure cheap to use

[[The-Preserving-Predicate-and-Modularity-Theorems]] guarantees that adding a language feature only requires proving *new*, *local* obligations — but "local and new" doesn't automatically mean "easy" or "fast to write." This chapter reports on the actual engineering payoff: because `Preserving`'s obligations are all quantifier-free, single-goal, per-rule facts with a fixed, predictable shape (per rule kind: well-formedness of a mapped sort/term, or equivalence of two mapped terms), **generic tactics** can be written once, against the *shape* of the obligation rather than against any specific language, and reused across every language and compiler built in Pyrosome.

**What breaks without this:** a framework that achieves modular *proof obligations* but still requires a human to write a bespoke tactic script for each one hasn't actually lowered the cost of verified compilation in practice — it's moved the boilerplate from "re-proving whole-language theorems" to "re-writing per-rule tactic scripts," which is progress, but not the full promise. The thesis's claim that Pyrosome "substantially lowers the burden of proof engineering" rests specifically on showing that the *automation itself* generalizes across languages, not just the theorem statements.

## Elaboration judgments: solving for the parts of a term the user didn't write

Recall from [[Language-Specifications-as-Equational-Theories]] and [[Pyrosomes-Design-Philosophy]] that a term rule marks some subterms **explicit** (a user must supply them) and others **implicit/inferred** (the framework must solve for them — types of subterms, contexts, etc.). Concretely realizing "solve for them" is what an **elaboration judgment** does: for every well-formedness judgment Pyrosome has (term well-formedness, language well-formedness, and `Preserving` itself), there's a **parallel elaboration judgment** that takes one extra input — a **preelaboration syntax** term, i.e., the partial, user-written version with the inferred parts still missing — and produces (as output, not input) the fully elaborated version, while *guaranteeing by the judgment's own definition* that the output actually satisfies well-formedness (or, for the `Preserving`-parallel judgment, actually is a `Preserving`-compatible compiler extension).

This is a **correct-by-construction** design: rather than "guess an elaboration, then separately prove it's well-formed," the elaboration judgment's derivation *is itself* the well-formedness proof — there's no gap in which an elaborated term could turn out to be ill-formed after the fact. Tactics then just need to construct a derivation of the elaboration judgment; the payoff (a well-formed term, or a `Preserving`-satisfying compiler extension) comes along automatically.

**Why this reads as bidirectional typing, even though the thesis doesn't use that vocabulary:** a preelaboration term with some slots filled and others missing, checked against a target well-formedness judgment, and elaborated into a fully explicit term — this is exactly the shape of a bidirectional type checker's *checking* mode discharging implicit-argument resolution as it goes, distinguishing "what the user wrote" (explicit subterms) from "what the elaborator must synthesize" (implicit subterms). If you're building the elaborator described in this workbench's learning goals, this is a direct, load-bearing precedent: Pyrosome's elaboration-judgment-parallel-to-well-formedness-judgment pattern is the same architecture a bidirectional elaborator with metavariable resolution needs — each surface-syntax judgment paired with an elaboration judgment that both fills in metavariables *and* certifies the result is well-typed, in one derivation.

## The tactics: generic over language features, not tied to any specific one

The thesis is explicit and somewhat emphatic about generality here: the tactics developed "bear no ties to any of the languages in my case study, including to the substitution calculus," and the author expects them to generalize to languages with **dynamic scope or linearity** — features not exercised anywhere in this case study. This genericity is only possible *because* of the uniform, systematic representation established in [[Pyrosomes-Design-Philosophy]] and [[Language-Specifications-as-Equational-Theories]]: a tactic written against "a term rule, in the abstract, with its declared explicit/implicit subterm split" applies to *any* term rule of that shape, regardless of what feature it happens to belong to.

Two automation results are reported:

1. **Elaboration/well-formedness automation is total for this case study.** Since every language in the pipeline (STLC + Naturals + Recursion + Unit + State, through closure conversion) is simply typed, the thesis "fully automates all term and language elaboration and well-formedness proofs" — no manual case-by-case elaboration proofs were needed anywhere in the case study.
2. **Equivalence-preservation automation via normalization.** A single tactic normalizes *both sides* of an equivalence-preservation goal, exploiting the convention that every declared equation can be read left-to-right as a **reduction rule** (i.e., the language's equational theory doubles as a rewrite system with a sensible directionality — an orientation choice the language designer makes when writing the equation, not something Pyrosome infers). Normalizing both sides and checking they land on a common normal form solved "almost all" equivalence-preservation goals in the case study — a striking result, given that (per [[The-Preserving-Predicate-and-Modularity-Theorems]]'s worked example) these goals are exactly the kind of equational-reasoning chains that looked laborious when done by hand.

## Where automation stops: type equations and dependent typechecking

The thesis is careful to flag the actual current limitation, and it's precise, not vague: the tactics struggle with languages that have **type equations** — for instance, substitution acting on type variables (the machinery polymorphism needs). Some instances of type equalities can be handled, but **automating polymorphism or dependent typechecking is out of reach for the current tactics.** Such languages *can* still be modeled in Pyrosome — the framework itself doesn't forbid them — but proving `Preserving` for them currently requires substantially more manual proof work, falling back to hand-written tactic scripts rather than the fully generic automation. This limitation is picked up again, as a stated direction for future work, in [[Related-Frameworks-and-Future-Directions]]'s discussion of prospects for polymorphism, linearity, and dependent types.

**Why this particular limitation, and not some other, is the boundary:** type equations (substitution acting on *type-level* metavariables, not just term-level ones) break the normalization-based automation's clean story, because a `Preserving` obligation involving a type equation may require reasoning about definitional equality of types *during* elaboration — exactly the kind of unification-and-normalization interleaving that makes dependent type-checking algorithms significantly harder to automate generically than simply-typed ones. This is directly relevant to the workbench's elaborator project: it's a documented, specific instance of "simply-typed metatheory automation is comparatively easy; type-level equational reasoning during elaboration is where the real difficulty lives" — the exact boundary your own bidirectional/dependent elaborator has to push past, not just observe.

## The line-of-code accounting: what modularity looks like measured, not just argued

Figure 4-6 breaks the entire case study's proof code into three categories:

| Definitions | Theorem Statements | Proofs |
|---|---|---|
| 1054 | 259 | 112 |

The thesis's own reading of these numbers is worth taking at face value rather than skimming past: **proofs are the *smallest* category**, at 112 lines total, for a case study covering STLC extended with naturals, recursion, unit, and global state, compiled through CPS and closure conversion. Definitions dominate the line count, but the thesis notes this code is "quite sparse" — the raw count is inflated by generous vertical formatting for readability, not by genuine density of content. Theorem statements have a **fixed, mechanical format** (a list of dependencies, followed by the language/compiler being verified) — meaning that even though they're a meaningful fraction of the total, writing one imposes essentially no creative or debugging burden; it's closer to filling in a template than composing a proof. Most strikingly, the thesis reports that **the majority of theorems are proved by a single generic tactic invocation** — direct, measured evidence that the automation described above isn't a cherry-picked demo but the dominant mode of actually using the framework.

## A concrete Coq proof, worked through

Figure 4-7 shows the actual Coq statement and proof for the recursive-continuations compiler extension (`fix_cc`), using Coq's `Derive ... SuchThat ... As ...` idiom:

```coq
Derive fix_cc
  SuchThat (elab_preserving_compiler
    (cc ++ prod_cc_compile ++ subst_cc)
    (fix_cc_lang ++ ... ++ value_subst)
    fix_cc_def fix_cc fix_cps_lang)
  As fix_cc_preserving.
Proof.
  auto_elab_compiler.
  cleanup_elab_after
    (reduce;
     term_cong; try term_refl;
     eapply eq_term_trans;
     [eapply eq_term_sym;
      eredex_steps_with cc_lang "clo_eta"|];
     by_reduction).
Qed.
```

`Derive ... SuchThat` is doing exactly the "correct-by-construction elaboration" job described above: it produces the elaborated object `fix_cc` (an extended compiler) *while simultaneously* proving it satisfies `Preserving(L_t, cmp_{pre}+\mathrm{fix\_cc}, L_{pre}+L_s)`, where `cmp_pre`/`L_pre` are built from smaller pieces via Coq's `++` (list append) — the literal embodiment of "compilers and languages compose by concatenation," per [[Compilers-as-Finite-Maps]] and [[Language-Specifications-as-Equational-Theories]].

The proof itself is a good illustration of *exactly where* the generic automation stops and human judgment resumes: `auto_elab_compiler` discharges **2 of the theorem's 3 proof obligations** fully automatically. The remaining one — showing that substitution's behavior on CPS-calculus recursive functions is preserved by the translation — needs "a little finesse" because it can't be solved by beta reduction alone; it genuinely needs **eta expansion for closures** (the eta law from [[The-STLC-to-CPS-to-Closures-Case-Study]]'s closure calculus). The hand-guided proof: reduce both sides as far as possible (leaving two instances of the `fix v` combinator from [[Extending-the-Case-Study]] whose arguments must be equated), go *under* the combinator via congruence, apply the closure eta law on the left-hand side in the needed orientation, then finish by the generic reduction tactic. This is a precise, small, understandable illustration of "automation handles the routine 90%, and the remaining 10% is exactly the genuinely nontrivial equational step a human needed to supply" — not an embarrassing failure of the automation, but the expected and reported shape of where generic tactics run out.

## Grounding: correct-by-construction elaboration as code

**Rust (primary) — the elaboration-judgment pattern as a `Result`-returning function that both fills in gaps and certifies well-formedness in one pass, rather than two:**

```rust
/// Preelaboration syntax: user-written surface syntax with holes
/// for inferred subterms represented explicitly as `None`.
struct PreelabTerm { tag: String, explicit: Vec<Term>, inferred: Vec<Option<Term>> }

/// Correct-by-construction: producing an `ElaboratedTerm` is the SAME operation
/// as proving it well-formed — there's no separate "elaborate, then check" step
/// where an ill-formed result could slip through.
struct ElaboratedTerm(Term);   // constructible only via `elaborate`, which enforces well-formedness

fn elaborate(pre: &PreelabTerm, ctx: &Context) -> Result<ElaboratedTerm, ElabError> {
    let solved_inferred: Vec<Term> = pre.inferred.iter()
        .map(|slot| slot.clone().or_else(|| infer_from_context(ctx)).ok_or(ElabError::Unsolved))
        .collect::<Result<_, _>>()?;
    // constructing the ElaboratedTerm here IS the well-formedness certificate
    Ok(ElaboratedTerm(Term::Node(pre.tag.clone(), merge(&pre.explicit, &solved_inferred))))
}
```

**Lean (secondary) — this is precisely `elab` + `isDefEq` territory.** Lean's own elaborator is structured around exactly this pattern: an elaboration function that takes partially-specified surface syntax (with metavariables for anything not yet resolved) and produces a fully elaborated, type-correct term, with metavariable assignment happening *during* elaboration rather than as a separate post-hoc check. The thesis's normalization-based automation for equivalence-preservation goals — reading equations left-to-right as rewrite rules and normalizing both sides — is structurally the same technique Lean's `whnf`/`isDefEq` machinery uses when it reduces both sides of a definitional-equality check to compare them, and the stated boundary (works for simply-typed, struggles with type equations needed for polymorphism/dependent typechecking) is a direct, named precedent for why a dependent elaborator's `isDefEq` needs strictly more machinery (higher-order/pattern unification, per this workbench's standing focus threads) than a simply-typed one ever requires.

**Python (tertiary sketch)** of "normalize both sides, check for a common normal form" as the core automation idea:

```python
def auto_prove_equivalence(lhs, rhs, rules):
    return normalize(lhs, rules) == normalize(rhs, rules)  # rules read left-to-right as rewrites
```

## Where this leads

This chapter is the thesis's evidence that its modularity theorems translate into an actually-usable proof-engineering workflow, not just a nicer theorem statement: the line-of-code breakdown and the "single tactic proves most theorems" result are the measured version of the promise made in [[The-Problem-of-Extensible-Compiler-Verification]]. The stated automation boundary — simply-typed automation works well, type equations for polymorphism/dependent typechecking don't yet — is picked up directly by [[Related-Frameworks-and-Future-Directions]]'s discussion of prospects for richer type systems in Pyrosome.

For the workbench's elaborator project (`type-theory`, `automated-reasoning`): this chapter is close to a design document for your own elaborator's architecture — pair every typing/well-formedness judgment with an elaboration judgment that both resolves metavariables and certifies correctness in one derivation, automate the routine cases with generic (shape-driven, not language-specific) tactics, and expect — as a documented, not hypothetical, boundary — that type-level equational reasoning (needed for anything approaching dependent types or refinement-type subtyping) is exactly where hand-guided proof engineering has to resume.
