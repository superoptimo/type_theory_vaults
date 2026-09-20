---
title: Related and Prior Work in Type Theory Implementations
source: "Towards a Practical Programming Language Based on Dependent Type Theory (Ulf Norell, 2007)"
chapter: "Chapter 1 §1.2 (pp. 13–14), Chapter 4 §4.1 (pp. 75–76), Chapter 7 (pp. 153–156)"
tags: [type-theory, dependent-types, cayenne, epigram, mcbride, delphin, coq, russell, module-systems, gadt, dependent-ml, norell-thesis]
---

# Related and Prior Work in Type Theory Implementations

[[book-guidelines|↩ Back to guidelines]]

## Why this topic exists as its own thing

Every other topic in this thesis is Norell building *his own* answer to a problem — a pattern-matching algorithm, a metavariable calculus, a module system. This topic is different: it's Norell mapping the space of answers *other people* had already given to closely related problems, so that when he makes a design choice in Chapters 2–4, you can see it as a choice made *against* specific, named alternatives, not in a vacuum. The two places this survey happens are structurally different and worth keeping apart:

- **Chapter 1, §1.2 ("Context")** is the *field-level* survey — where does "programming with dependent types" sit relative to a decade of proof-assistant development, and what are the two directions you can approach it from?
- **Chapter 4, §4.1 ("Introduction")** is a *narrow, mechanism-level* comparison — specifically [[Module-Systems-for-Dependently-Typed-Languages|module systems]], because that's the one place Norell is consciously assembling a design out of pieces borrowed from three named prior systems (Haskell, Cayenne, Coq).

Treating these together as "prior work" is useful precisely because the same tension recurs in both: **how much do you couple a new feature to the core type theory, versus keeping it as an independent layer?** That question is the thread connecting this topic to almost everything else in the thesis, and it's worth tracking explicitly since the learning-goals emphasis on trusted-kernel design and elaborator architecture hinges on exactly this coupling/decoupling axis.

## Two routes into dependently-typed programming

Norell frames the field with a clean dichotomy (p. 13): you can arrive at a dependently-typed *programming language* from either direction of a two-lane road.

1. **Type-theory-to-language**: start from a proof assistant's type theory (which was designed for constructive mathematics, not programming) and adapt it into something a programmer can use — add general recursion, better syntax, [[Metavariables-and-Implicit-Arguments|implicit arguments]], modules.
2. **Language-to-type-theory**: start from a conventional programming language and bolt on dependent-type features incrementally, without committing to a full dependent type theory as the language's foundation.

This dichotomy is worth pausing on because it isn't just historical trivia — it's a **trusted-computing-base decision**. Route 1 inherits a type theory's metatheoretic guarantees (subject reduction, normalization, decidable equality) as a starting point and then has to *fight to keep them* while adding programmer-friendly features. Route 2 starts from a language with no such guarantees and adds dependent types as extensions whose soundness has to be established piecemeal, feature by feature. Norell's own thesis is unambiguously Route 1 — everything in Chapters 2–4 is phrased as "extend $UTT_\Sigma$ while preserving soundness," never as "add types to an existing language." If you are building a Rust-hosted verifying compiler, this is the same fork in the road: do you design your surface language as a dependent type theory from the start (Route 1, what this thesis does, and what Lean/Coq/Agda all do), or do you retrofit refinement predicates onto an existing typed IR (Route 2, closer to how tools like Dafny, F*'s effect layer, or Liquid Haskell approach the problem)? The thesis doesn't argue Route 1 is universally better, but it does implicitly demonstrate the *cost* of Route 1: every one of Chapters 2–4 exists because the base theory $UTT_\Sigma$ alone can't support real programming, and each extension has to be proved not to break what came before.

## Route 1 in practice: three systems Norell is directly answering

### Cayenne — the cautionary tale

Cayenne [Aug98] takes Martin-Löf type theory and combines it with **unrestricted general recursion**. The direct consequence: type checking becomes **undecidable**, because the type checker's conversion-checking step may need to *run* an arbitrary, possibly non-terminating program to decide whether two types are equal.

> **What breaks without termination.** This is the single clearest illustration in the whole "related work" discussion of why type theory usually insists on strongly-normalizing terms. If your language admits `let loop = loop in loop : Nat`, then asking "is `T[loop]` convertible to `T[0]`?" during type checking is asking the type checker to solve the halting problem. Cayenne accepts this cost for the sake of programming flexibility; the rest of the field (including this thesis) doesn't. You'll see the payoff of refusing that cost directly in Chapter 3: the guarded-constant machinery for metavariables exists specifically to avoid ever type-checking against a term that might not normalize, and Norell's soundness theorem for that algorithm would be unprovable in a Cayenne-style setting.

For a verifier-shaped project, Cayenne is the load-bearing negative example: it tells you that "decidable type checking" and "arbitrary recursion" are in direct tension, and any refinement-type or dependent-type system that wants an automatically-checkable kernel has to resolve that tension somehow — either by restricting recursion (structural/well-founded recursion, as Agda and Coq do), by admitting non-termination but separating "the type checker's own reduction" from "the program's actual execution semantics" via an oracle/timeout, or by requiring explicit termination *proofs* as first-class obligations (closer to how a Hoare-style verifier would treat a `decreases` clause). This thesis silently picks the first option throughout; it's worth knowing that's a choice, not a law of nature.

Chapter 4 revisits Cayenne specifically for its **module system** (p. 75): Cayenne modules split into an interface (a *type*, describing what a module provides) and an implementation (a *value* realizing that interface) — mirroring the ML module tradition. Norell explicitly departs from this: Agda modules have **no separate interface**, only implementations. This is a genuine simplification with a real cost/benefit tradeoff, not a value judgment about which is "correct" — dropping the interface layer removes the abstraction (opacity, hiding of representation types) that interfaces normally buy you, in exchange for a much smaller and more implementable system.

### McBride's thesis and Epigram — the direct ancestor of Chapter 2

McBride's thesis [McB99] extended Lego with facilities for **interactive programming and pattern matching**, later refined with McKinna [MM04a] into the **Epigram** language [McB07]. Norell states plainly (p. 13) that "the programming model of Epigram is very similar to what we present in this thesis and has been a great inspiration," with the caveat that Epigram's implementation hadn't scaled to larger programs at the time of writing.

This is the single most direct genealogical link in the whole related-work section: **Chapter 2's entire pattern-matching algorithm is Norell's own answer to the same problem McBride and McKinna were solving.** Their key theoretical move — showing that pattern-match definitions over [[Dependent-Type-Theory-Foundations#Inductive families|inductive families]] can be *reduced* to definitions using only the primitive elimination rules, provided you accept uniqueness of identity proofs (i.e., the K axiom) — is exactly the equivalence Norell cites in Chapter 2 (§2.2) when connecting his coverage-checking algorithm back to the K axiom. Where Norell's own algorithm differs and improves on this lineage is stated explicitly in the Conclusions (Ch. 7, p. 153): "we have given a direct type checking algorithm for pattern match equations supporting the `with` rule... more liberal than previous approaches in that it allows **overlapping pattern equations**." So the relationship isn't "same idea, different notation" — it's "same foundational reduction (pattern matching → elimination via K), but a strictly more permissive surface algorithm on top of it."

### Delphin — a genuine algorithmic fork, not just a design variant

Delphin [PS07], by Poswolsky and Schürmann, is built on the **LF logical framework** [HHP93] and is centered on manipulating **higher-order syntax** via a "newness" operator for quantifying over fresh constants. Norell draws out one precise algorithmic contrast (p. 13): "where we, in our work, get away with **first-order matching**, Delphin uses **unification and higher-order matching at run-time**."

> **Why this distinction is load-bearing for you specifically.** This is the first explicit appearance, anywhere in the thesis's related-work discussion, of the exact fork the learning-goals emphasize: first-order matching/unification versus higher-order matching. Chapter 2's pattern-matching algorithm gets to stay comparatively simple *because* Agda's inductive families only require matching first-order patterns (a constructor applied to variables) against first-order scrutinees — no unification of terms containing bound variables under binders is needed at the object level. Delphin can't take that shortcut, because its domain (representing and pattern-matching over object-language syntax with binders, LF-style) inherently needs to match under binders — which is precisely the higher-order matching problem that Miller's pattern fragment (the tractable subset of higher-order unification you'll be implementing in your own elaborator) was invented to tame. Chapter 3's *metavariable* unification ([[Metavariables-and-Implicit-Arguments#Restricted pattern unification|restricted pattern unification]], §3.3) is where Norell's own thesis actually does confront a version of this problem — so the honest picture is: Norell keeps *object-level pattern matching* first-order (Ch. 2) but still needs *metavariable* unification to handle a Miller-pattern-shaped restricted fragment (Ch. 3). Delphin needs the general higher-order case because its object language itself involves binders being matched against.

### Coq as a programming language, and Russell

Norell notes (pp. 13–14) a body of work using **Coq** directly as a programming language — certified programs by Chlipala [Chl06, Chl07] and Leroy [Ler06] — and **Russell** [Soz07], Sozeau's layer on top of Coq that lets you "write dependently typed programs as if they were simply typed," recording the resulting proof obligations separately for later discharge via Coq's tactic language.

> **The design principle Russell shares with this entire thesis.** Russell's separation — write the program against a simplified view of its types, and record the *real* (dependent, obligation-laden) typing as a side condition to be proved later — is a specific instance of a pattern that recurs across all four of this thesis's own contributions: pattern matching (Ch. 2) separates *what the user writes* (possibly non-linear, overlapping patterns) from *what the kernel checks* (a compiled case tree using only primitive eliminators); metavariables (Ch. 3) separate *the user's possibly-ill-typed intermediate expression* from *the well-typed guarded-constant approximation* the type checker actually manipulates; the module system (Ch. 4) separates *scope checking* from *type checking* entirely. Chapter 7's own retrospective names this explicitly as the thesis's recurring design principle. Russell is evidence this same "separate the friendly surface layer from the trusted core obligation" move was independently arrived at elsewhere — which is directly relevant if your compiler's refinement-type surface syntax is going to desugar into raw Hoare-triple obligations discharged by a separate solver: that's the Russell pattern, generalized from "prove it in Coq's tactic language" to "prove it via CHC/SMT solving."

Coq's own **module system** [Chr03], based on the ML module system [MTH90], is the third input to Chapter 4's design (p. 75–76). Like Cayenne, Coq splits modules into interfaces and implementations, but goes further: Coq supports **higher-order modules (functors)** — modules that map an implementation of one interface to an implementation of a different interface. Norell is explicit about the tradeoff: "the module system of Coq is much more powerful than the module system presented here, [but] it is also significantly more complex." This is a genuine engineering decision documented in real time — functors buy you a form of modular, parametric abstraction (think: a `Set` functor taking an `Ord` module and returning a `Map` module) at the cost of a substantially harder metatheory and implementation. Norell's Agda modules are **parameterised** (a [[Dependent-Type-Theory-Foundations#Telescopes|telescope]] of module parameters, closer to a Coq *section* than a functor) but not first-class values that can themselves be passed around — a deliberate restriction that keeps the module system's own type theory nearly trivial (Chapter 4's own conclusion: modules reduce to name-space bookkeeping plus lambda-lifting, "independent of the underlying type theory").

Two further named influences round out the module-system genealogy (p. 76): **Harper and Pfenning's** module system for LF [HP98], in the same spirit as Coq's, and **Courant's** theoretical treatment of such module systems in the general setting of Pure Type Systems [Bar92a] — establishing that this design space (interfaces + implementations + functors, layered over an arbitrary base type theory) is studied in reasonable generality, not just as one-off engineering. Pollack's work [Pol00, CPT] is cited as the mirror-image design choice to Norell's own: rather than keeping modules and record types cleanly separate (Norell's approach), Pollack **extends record types themselves** with module-like features such as *manifest fields* (fields whose value is fixed/known as part of the type, used to recover a form of sharing/equality between record instances that would otherwise need module-level machinery). This is worth flagging as a genuine alternative architecture, not a strictly worse one — where Norell's module system stays a pure name-space/scoping layer with zero interaction with the type theory, Pollack's approach pushes some of that expressiveness *into* the type theory via richer record types, trading "the module system is free of typing subtleties" for "you get more expressiveness without needing modules at all for some use cases."

## Route 2: adding dependent types to conventional languages

The mirror direction (p. 14) — start from an existing typed language and extend it with a restricted form of dependency — gets a shorter but pointed treatment:

- **Dependent ML** [Xi98] extends ML with types that can depend on **integers** — e.g., array-bounds-indexed types — without going anywhere near a full dependent type theory.
- **Haskell's GADTs** (generalised algebraic datatypes) [PVWW06] are described as "a restricted form of inductive families" — the same underlying idea as Chapter 2's inductive families, but embedded in a language (Haskell) that never committed to dependent types as a foundation, so the restriction is deliberate and structural, not incidental.
- **Applied Type Systems** [Xi04] and **Ωmega** [She05] are named as further points in this same design space.

Norell's summary judgment on the whole Route-2 family is precise and worth quoting almost verbatim: these languages "only support a limited form of type dependencies... there is no way of having a type depending on the value of another dependent type." That's a specific, checkable technical claim, not just "less powerful" — it says these systems support at most *one level* of value-into-type dependency (e.g., a vector length, an integer index) but not the fully general case where a *type itself*, having been computed from a value, can be depended upon by a further type. Full dependent type theory (Chapter 1's $UTT_\Sigma$, with types classified by universes $\mathrm{Set}_i$ that are themselves terms) supports arbitrarily nested dependency because types and terms share one syntactic category; GADT-style extensions to ML/Haskell keep types and terms in separate categories connected by a narrow, fixed interface (index types, kind-level naturals), which is exactly what caps the nesting.

For a Rust-based compiler project, this is the practical fork you'll actually face: full dependent types (Route 1, Norell's own choice, and Lean/Agda/Coq's choice) buy unrestricted expressiveness at real implementation cost (a bidirectional elaborator, a definitional-equality/conversion checker, universe management — everything in Chapters 1 and 3), while a GADT/Dependent-ML-style restricted extension (Route 2) is dramatically simpler to bolt onto an existing Rust-like type system but caps what specifications you can state (typically: index-level naturals/booleans in types, not arbitrary computed types depending on other computed types). Most practical refinement-type systems (Liquid Haskell, F*, Dafny) sit closer to Route 2's restraint even though they borrow Route 1's proof-obligation machinery — refinement predicates are drawn from a decidable logic (linear arithmetic, uninterpreted functions) precisely so an SMT solver can discharge them automatically, rather than letting the refinement predicate be an arbitrary dependent-type-theoretic proposition. Recognizing which side of this line a language sits on is the fastest way to predict whether it needs an interactive elaborator (Route 1) or can get away with automatic, solver-driven checking (Route 2, or a Route-1 language paired with the FOL automation of Chapter 6).

## Where this leads

```
Route 1 (theory → language)          Route 2 (language → theory)
─────────────────────────────       ──────────────────────────────
Cayenne (undecidable checking,        Dependent ML (index types)
  interface/impl modules)             Haskell GADTs (restricted
McBride/Epigram (pattern match          inductive families)
  ancestor of Ch. 2)                  Applied Type Systems, Ωmega
Delphin (higher-order matching,
  LF-based)                          ↳ Norell's verdict: only one
Coq-as-language, Russell               level of value→type dependency;
  (surface/obligation split,           no type-depending-on-a-
  ancestor of the thesis's own          computed-type
  recurring separation principle)
Coq/Harper–Pfenning/Courant module
  systems (functors, full power)
Pollack (manifest fields in records,
  opposite of Norell's separation)
        │
        ▼
Norell's own choices in Ch. 2–4:
strict decidability (no Cayenne-style
general recursion), first-order object-
level matching (unlike Delphin) with
restricted pattern unification for
metavariables only (Ch. 3), a
functor-free parameterised module
system (simpler than Coq, more
featureful than Cayenne/Haskell)
```

This survey's real payoff is that it turns every design decision in Chapters 2–4 from an arbitrary stipulation into a *documented choice against a specific alternative* — which is exactly the posture you want when justifying your own compiler's design decisions later: not "dependent types are good," but "here is the decidability/expressiveness/complexity tradeoff this specific design makes, and here are the named systems that made the opposite call." Chapter 7's closing retrospective reinforces this by naming the one thread the author considers unresolved by *anyone* in this survey: "perhaps the most important challenge we are now facing is that of learning to program with dependent types" — a pedagogical and methodological gap (pioneered by McBride and McKinna) that no system surveyed here, including Agda itself, had yet closed.
