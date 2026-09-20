---
title: "The Dedukti System and Concrete Syntax"
source: "Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory (Assaf, Burel, Cauderlier, Delahaye, Dowek, Dubois, Gilbert, Halmagrand, Hermant, Saillard — arXiv:2311.07185v1)"
chapter: "Section 3 — Dedukti"
pages: "9–11"
tags: [type-theory, dedukti, lambda-pi-calculus, rewrite-rules, logical-framework]
---

# The Dedukti System and Concrete Syntax

[[book-guidelines|↩ Back to guidelines]]

## Why a syntax layer, and why *this* one

Section 2 of the paper gave you a formal object: the $\lambda\Pi$-calculus modulo theory, with its typing judgments, its global context of variable declarations and rewrite rules, and its conversion relation $\equiv_{\beta\Gamma}$. That's a specification. Section 3 is about the thing you actually type into a file and run — Dedukti, the concrete implementation of that specification.

The first design decision the paper is explicit about is a scoping one: **Dedukti is a proof-checker, not a proof-development environment.**

> "This system is not designed to develop proofs, but to check proofs developed in other systems. In particular, it enjoys a minimalistic syntax."

If you're used to Lean, Coq, or Agda, this distinction matters more than it sounds. Those systems give you tactics, an interactive goal-state, elaboration that fills in mountains of detail you didn't write, unification hints, typeclass search — a whole *authoring* experience layered on top of a trusted kernel. Dedukti has none of that layered experience by design. It has a kernel, and a syntax minimal enough to *feed* that kernel terms that were produced somewhere else (by a translator from HOL Light, Coq, a tableaux prover, whatever). [[Embedding-Predicate-Logic-in-a-Logical-Framework#What breaks|What breaks]] if you try to use Dedukti the way you'd use Lean's tactic mode? Nothing breaks technically — but you'd be fighting the tool. There's no elaboration budget spent on inferring implicit structure beyond simple bidirectional type reconstruction (more on that below); everything else is expected to arrive already fully elaborated from an external front-end. This is the same trusted-kernel philosophy that shows up later in Section 9's framing: keep the checker small and auditable, and push all the proof-search intelligence into separate, untrusted translators that target it.

This is directly the "trusted kernel" thread from the Automated Reasoning focus area: Dedukti *is* a minimal trusted kernel in the LCF sense — small enough to audit, everything else (proof search, elaboration, tactic engines) lives outside it and only needs to be *convincing*, not *trusted*, because the kernel re-checks its output.

## The two constructs, and the one built-in constant

Since the $\lambda\Pi$-calculus modulo theory's global context holds exactly two kinds of things — variable declarations and rewrite rules — Dedukti's syntax has exactly two top-level constructs to match. There is exactly one constant available at the root of a file: `Type`, corresponding to the sort $Type$ from Section 2. `Kind` is *not* part of the input syntax at all — it's used only internally by the type-checking algorithm. You can never write `Kind` in a Dedukti source file; it only ever appears as the type synthesized for `Type` itself, one level up.

**Variable declaration.** A bare declaration binds a name to a type:

```
nat : Type .
```

This is the concrete syntax for adding `nat : Type` to the global context $\Gamma$.

**The arrow as $\Pi$.** The dependent product $\Pi x{:}A\, B$ from Section 2.1 is written as a single-line arrow, `x:A -> B`. Read that literally: `->` *is* $\Pi$, just written infix, and it is a genuine binder — `B` may mention `x`. When there's no dependency (the common non-dependent function-type case), you drop the variable name entirely:

```
0 : nat .
S : nat -> nat .
```

`S : nat -> nat` is really `S : Πx{:}\text{nat}.\,\text{nat}` with `x` unused in the codomain — Dedukti just lets you elide dead binders syntactically, exactly the way you'd write `A -> B` in Rust or Haskell instead of a dependent-pair-flavored spelling.

**Rewrite-rule declaration.** Recall from Section 2.2.1 that a rule is a triple $\langle \Delta, l, r\rangle$: a local context $\Delta$ of object-variable declarations, plus a left-hand side and right-hand side, written $l \longrightarrow_\Delta r$. Concretely:

```
def plus : nat -> nat -> nat .
[ n ] plus 0 n --> n .
[ n1 , n2 ] plus ( S n1 ) n2 --> S ( plus n1 n2 ) .
```

The bracketed prefix `[ n ]` and `[ n1 , n2 ]` *is* the local context $\Delta$ — and notice what's absent: no type annotations inside the brackets. The types of $\Delta$'s variables are **inferred automatically** from how they're used against the declared type of the head symbol (`plus`), not written by hand. This is the syntax-level payoff of the well-typedness machinery from Section 2.3.2 (the most-general-typing-substitution story) — the user writes the untyped pattern, the checker reconstructs the typing.

## `def`: which symbols may head a rule

You'll notice `plus` is declared with `def`, but `nat`, `0`, and `S` were not. This is the concrete-syntax face of the **static vs. definable symbol** distinction — worth pulling apart carefully because it's not a stylistic choice, it's load-bearing for soundness.

Trace the motivation back to Section 2.3.2's `tail`/`Cons` example (Topic 3 of this guide): accepting the rule

$$\text{tail}\ n\ (\text{Cons}\ m\ a\ l) \longrightarrow l$$

required computing a *most general typing substitution* for the left-hand side, and that computation's existence depended on the **injectivity** of the symbols `vector` and `S` with respect to $\equiv_{\beta\Gamma}$. Injectivity here means: if $\text{vector}\ n_1 \equiv_{\beta\Gamma} \text{vector}\ n_2$ then $n_1 \equiv_{\beta\Gamma} n_2$ (and similarly for `S`). This is exactly the property you'd expect from an "honest" constructor and would take for granted in Rust's `enum` variants or Lean's inductive constructors — but in a system where *any* symbol can in principle be rewritten arbitrarily, injectivity isn't free. It has to be earned or asserted.

Dedukti's solution is syntactic, not semantic: **forbid the symbol from ever being a rewrite-rule head**, and injectivity follows automatically, because nothing can ever rewrite `vector n` into anything other than a syntactic instance of `vector` applied to something — there's no rule that could collapse two different `vector n` terms into the same normal form except by first equating their arguments.

- A **static symbol** is declared with only a name and a type — no `def` — and can *never* appear at the head of a rewrite rule:

```
A : Type .
vector : nat -> Type .
Nil : vector 0 .
Cons : n : nat -> A -> vector n -> vector ( S n ) .
```

  `vector`, `Nil`, `Cons`, and `S` are all static here. Static-ness is exactly what makes them behave like true constructors — injective and non-overlapping, the properties you'd assume automatically from an inductive datatype declaration in Lean or Rust, but which here have to be purchased by a syntactic restriction rather than assumed.

- A **definable symbol** is declared with the `def` keyword and *may* be a rewrite-rule head:

```
def tail : n : nat -> vector ( S n ) -> vector n .
[ n , m , a , l ] tail n ( Cons m a l ) --> l .
```

Once `vector` and `S` are static (hence injective), the most-general-typing-substitution machinery from Section 2.3.2 goes through, and this rule for `tail` — definable — type-checks and is accepted.

**What breaks without this distinction?** If `S` itself were definable and some later rule rewrote `S`-headed terms in a way that collapsed distinct naturals (even accidentally, as a side effect of an unrelated rule sharing the symbol), the injectivity Dedukti implicitly relied on to type-check `tail` would silently become false, and subject reduction (Lemma 4 of Section 2) could fail without any local symptom at the point where `tail`'s rule was declared. The static/definable split turns an unenforceable global semantic property (injectivity, in general undecidable to verify from a rewrite system) into a locally-checkable syntactic one: scan the rule set, see whether the symbol ever appears at a rule head. This is a recurring shape worth keeping in mind for a Rust verifier: replace an expensive or undecidable *semantic* check with a cheap *syntactic* invariant that implies it by construction.

## Declaring rules "all at once" versus incrementally — and why it matters for typing

A head symbol can have several rewrite rules. Dedukti lets you introduce them two different ways, and — this is one of the Key Questions the guidelines flag — the choice has a real typing consequence, not just a stylistic one.

**Incrementally**, one rule terminated by its own dot:

```
[ n ] plus 0 n --> n .
[ n1 , n2 ] plus ( S n1 ) n2 --> S ( plus n1 n2 ) .
```

**All at once**, the same two rules but with a single trailing dot for the whole group:

```
[ n ] plus 0 n --> n
[ n1 , n2 ] plus ( S n1 ) n2 --> S ( plus n1 n2 ) .
```

The paper is direct about the semantic difference:

> "In the former case, the first rule can be used to type the second, while in the latter, it cannot."

Think of it as a visibility horizon during elaboration. Declaring incrementally is like processing a sequence of top-level `def`s in a file one at a time: by the time the type-checker reaches the second rule, the first rule has already been committed to the global context and is available as a conversion fact — it can participate in checking whether the second rule's left- and right-hand sides are well-typed modulo the rules seen *so far*. Declaring "all at once" instead commits the whole batch to the context *simultaneously* — so when the second rule is checked, it sees the *head symbol's declared type*, but not the first rule as an extra conversion available for that check.

Why would you ever want the more restrictive "all at once" form, given it type-checks against a strictly weaker context? Because mutual dependency can run in **both directions across symbols**: "the well-typing of a rewrite rule on a symbol $g$ may depend on a rewrite rule on a symbol $f$, while further rewrite rules on $f$ may depend on those previously declared on $g$." Sequential, rule-by-rule commitment can't express a genuine mutual dependency where rule 1 on $f$ needs rule 2 on $g$ which needs rule 1 on $f$ back — you'd have a chicken-and-egg ordering problem. Declaring the whole mutually-recursive cluster "all at once" sidesteps the ordering question by not relying on intermediate rules as conversion facts for each other at all; each rule is checked only against what's unconditionally already known (the symbols' *declared types*), not against sibling rules in the same batch. This is precisely the reason mutually recursive function or datatype declarations in most languages (Rust's `mod`, Lean's `mutual` blocks) get processed as one simultaneous unit rather than top-to-bottom — the underlying tension is identical: to let $A$ reference $B$ and $B$ reference $A$, neither can be fully settled before the other starts.

Rules on the same head symbol don't need to be declared contiguously, either — an arbitrary number of unrelated declarations can separate them, which is what makes the incremental/mutual-dependency picture genuinely nontrivial (rather than a purely local, easily-inspected property of one file region).

## Confluence checking is not Dedukti's job

Section 2.3.1 established that confluence has to be verified before termination or typing can be trusted (Key Question 1 of that section). But Dedukti itself does not attempt to *prove* confluence for you — that would require running potentially expensive external algorithms (critical-pair analysis, and beyond that, genuinely hard higher-order confluence checking) inside the trusted kernel, which cuts directly against the minimalism goal.

Instead: "Checking confluence is out of the scope of Dedukti itself, and is a separate concern." Dedukti supports this by *exporting* the rewrite system to the old TPDB format (the Termination Problem Data Base format used in confluence and termination competitions), handing the actual confluence proof obligation to specialized external tools built for exactly that problem. You, the Dedukti user, are trusted to only add rules "as long as confluence is preserved" — and TPDB export is the escape hatch that lets an independent tool audit that claim without folding the audit machinery into the checker.

This is a clean instance of a design principle worth generalizing for your own verifier: **not every soundness-relevant property needs to live inside the trusted kernel.** Some can be discharged by an untrusted, swappable, best-of-breed external tool, provided the kernel's own soundness argument doesn't secretly assume the property holds without a checkable certificate. (Here the "certificate" is informal — TPDB tools report confluent/non-confluent/unknown, and the user is trusted to heed the answer — but the architectural move of exporting to a specialized external format rather than reimplementing the algorithm internally is the transferable idea.)

## `def` beyond rewrite rules: constants and $\lambda$-abstraction

`def` isn't only the marker for "this symbol may head a rule" — it doubles as ordinary constant definition, syntactic sugar for a rewrite rule with an *empty* local context and left-hand side equal to the symbol itself:

```
def two := S ( S 0 ) .
```

Defining a constant this way is, formally, identical to declaring a rewrite rule `two --> S ( S 0 )` with $\Delta = \emptyset$ — `two` unfolds to `S (S 0)` under $\equiv_{\beta\Gamma}$ exactly as any other rewrite would fire. It's presented as special syntax purely for convenience, not because it's a different underlying mechanism.

$\lambda$-abstraction — the term-level binder $\lambda x{:}A.\,t$ from the calculus — is written with the double arrow `=>`:

```
def K2 := x : nat => two .
```

One subtlety flagged explicitly: the type annotation on the bound variable is *optional* when it can be reconstructed by **bidirectional type-checking** — inference mode propagating an expected type down into the abstraction, so the annotation would be redundant. In the `K2` example above, though, the annotation is *mandatory*, because there's nothing above `K2 := x : nat => two` supplying an expected function type to infer `x`'s type from — `def K2 := ...` gives no type ascription for `K2` itself in this snippet, so the elaborator has no top-down information flowing into the abstraction and must be told `x : nat` directly.

This is worth pausing on for the `type-theory` focus area specifically, since it's a place where the paper's own presentation is thinner than the mechanism deserves. "Optional annotation, reconstructed by bidirectional typechecking" is exactly the inference/checking-mode distinction central to Lean's elaborator: a checking-mode position (an expected type is already known, flowing top-down) lets you omit information a synthesis-mode position (no expected type available, information must flow bottom-up from the term itself) cannot. Concretely: if you instead wrote `def K2 : nat -> nat := x => two .`, the ascription `nat -> nat` gives the abstraction its expected type in checking mode, and `x`'s annotation becomes droppable — `x => two` alone would suffice, because the elaborator can read `x`'s type off the `nat -> nat` ascription rather than needing it spelled out locally. That's the general shape of "checking mode subsumes synthesis mode's information need" that a bidirectional elaborator (yours included, per the standing project) leans on constantly to avoid demanding redundant annotations.

A closing remark from this subsection worth internalizing early: "the semantic difference between variables, constants and constructors is purely in the eyes of the user, Dedukti treats them in the same way." There is no `enum`/constructor-tag distinction baked into the kernel the way there is in Lean's or Coq's inductive-type machinery — a "constructor" in Dedukti is just a static symbol the user has chosen never to give rewrite rules to, and the kernel doesn't know or care that you're using it that way. The entire apparatus of "this looks like an inductive datatype" is a user convention riding on top of two primitive kinds of declaration, not a first-class kernel concept.

## Wildcards: patterns you don't need to name

Local-context variables in a rule's left-hand side sometimes appear purely as structural placeholders — matched by unification but never referenced on the right-hand side. Naming them is needless ceremony, so Dedukti provides the wildcard `_`:

```
[ n , a , l ] tail n ( Cons _ a l ) --> l .
```

Here the middle argument of `Cons` (the vector's head element `a`... wait — reread: `Cons` takes `n : nat`, `A`-typed element, `vector n`; the middle wildcard replaces a bound name that would otherwise need declaring in `[ ]` purely to be discarded). Wildcards can be stacked freely:

```
[ l ] tail _ ( Cons _ _ l ) --> l .
```

This is unremarkable as a feature (it's the same idea as Rust's `_` in pattern matches, or Haskell's `_` in equations) but it's worth naming precisely because it clarifies what the local context $\Delta$ is actually *for*: it's the set of names the right-hand side (or the guard mechanism below) might need to refer back to. A wildcard is Dedukti's syntax for "this position participates in matching, but nothing downstream needs its name" — pure unification bookkeeping with zero binding consequence.

## Guards: when injectivity can't be checked, only asserted and re-checked

Wildcards handle *don't-care* positions. Guards handle the opposite problem: positions where the shape genuinely matters for well-typedness, but Dedukti's static/definable machinery can't verify that shape automatically.

Return to the `tail`/`Cons` example once more, now with a twist. Suppose the middle argument of `Cons` were itself something Dedukti couldn't establish injectivity for through the static-symbol mechanism alone — some definable symbol appearing where the most-general-typing-substitution computation needs to know a subterm's exact shape to go through. The paper's own illustrative case reuses the `n` position:

```
[ n , a , l ] tail n ( Cons { n } a l ) --> l .
```

The curly braces around `{ n }` are the **guard**. Operationally, Dedukti does two separate things with a guarded rule:

1. **At declaration time**, it type-checks the rule *as if the guard weren't there* — using the bracketed subterm's asserted shape to make the well-typedness argument go through, the same way the injectivity of a static symbol would.
2. **What's actually stored and used for reduction** is the *linear* rule — the guard replaced by a fresh, ordinary pattern variable, with no special status at match time. So the stored rule for reduction purposes is effectively `[n, a, l] tail n (Cons n' a l) --> l` for some fresh `n'`, not literally requiring `n'` to equal `n` syntactically.
3. **At every use** — every time the rule actually fires during reduction — Dedukti re-derives the typing constraint the guard was asserting and checks it holds *for that specific instance*. If it doesn't, the rule is deemed not well-typed after all, and Dedukti fails with an error at that point.

So a guard is a deferred, run-time-checked promise: "trust me at type-checking time that this subterm has this shape; I accept the obligation to prove it every single time the rule is actually invoked." The reason this has to be deferred rather than settled once and for all up front is stated plainly: validating that the guard follows from typing constraints is **undecidable in general**. Dedukti doesn't attempt the undecidable check; it accepts the user's assertion, keeps its own bookkeeping honest by re-verifying the *specific instance* every time (which is decidable, because it's just checking one concrete substitution rather than universally quantifying over all possible ones), and refuses to reduce if the promise is ever broken.

**What breaks without guards, that wildcards can't fix?** A wildcard says "I don't care what's here." A guard says "I care enormously what's here, need that information to make the typing argument for the *whole rule* work, but the language's automatic injectivity/static-symbol machinery isn't strong enough to derive it for me automatically." Wildcards discard information; guards assert information the checker can't otherwise obtain. They solve genuinely different problems, which is exactly the guidelines' Key Question 2 for this section: wildcards can never substitute for a guard, because a wildcard carries *no* constraint at all, while what a guard needs is precisely a constraint the system will re-check indefinitely into the future.

This is a pattern worth carrying directly into a Rust-based verifier design: not every well-typedness obligation needs to be discharged statically once. Some obligations are cheaper, or only decidable at all, if deferred to the specific instance and re-checked dynamically at each use-site — a controlled, principled escape hatch from a static checker's undecidability, rather than an unsound backdoor, precisely because the *type-safety* of the reduction step is still enforced (checked at every firing) even though the *general validity* of the rule was only ever asserted, never proved.

## Where this leads

Section 3's syntax is the concrete vehicle for everything Sections 4 onward will build: predicate logic, classical logic, simple type theory, full programming languages, and the Calculus of Inductive Constructions with universes are all going to be expressed as nothing more than `def`/rewrite-rule declarations in exactly this syntax — no new kernel features, just bigger and cleverer global contexts. The static/definable distinction you saw here for `vector`/`S`/`tail` reappears, unremarked but load-bearing, every time a later section introduces a "constructor" (`nil`/`cons` for inductive lists in Section 8.2, `lam`/`app` for the embedded $\lambda$-calculus in Section 7.1) — those are static symbols by the same logic, even though the paper stops spelling it out explicitly after this section. And the "check confluence externally, trust the user, verify what you can locally" posture set up here — TPDB export for confluence, guards for undecidable injectivity — is the same trusted-minimal-kernel philosophy that later justifies treating iProverModulo, Zenon Modulo, HOLiDe, and Krajono (Sections 4–8) as untrusted proof producers whose output the small Dedukti kernel alone is responsible for validating.

For the standing project: this section is a close model for the surface syntax and elaboration-boundary decisions a Rust verifier's front-end needs to make explicitly — where annotations can be dropped because checking-mode information is available (the `K2` bidirectional-typing remark), which declarations get to participate in rewriting versus which are frozen as true constructors (the static/definable split, directly reusable as "which of my language's symbols get to be `enum` variants with guaranteed injectivity versus definable functions"), and where an undecidable global property (confluence, or general injectivity) is better handled by exporting to an external tool or deferring to a checked run-time obligation (guards) than by trying to decide it inside the trusted core.
