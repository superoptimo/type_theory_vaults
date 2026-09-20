---
title: The Problem of Extensible Compiler Verification
source: A Framework for Modular, Extensible, Equivalence-Preserving Compilation (Jamner, 2022)
chapter: "1 Introduction"
pages: "9–13"
tags: [type-theory, automated-reasoning, compiler-verification, pyrosome]
---

[[book-guidelines|↩ Back to guidelines]]

## Why is a verified compiler still a rare thing?

Compiler verification is expensive — proportionally far more expensive than writing an unverified compiler of comparable functionality. That expense would be tolerable if it were a one-time cost, paid once and amortized forever. The thesis's central observation is that, for the compilers people actually care about, **it isn't a one-time cost**: real programming languages are *living projects*, with specifications that change routinely (new syntax, new type-system features, bugfixes to corner-case semantics). Every one of those changes threatens to invalidate a monolithic proof of correctness, and the existing state of the art gives you no principled way to bound how much reverification a given change will cost.

**What breaks without a modularity story:** imagine you've verified a compiler for a language with 40 syntactic forms, and your correctness proof is one long induction over "all the ways a term can be formed." Add form 41 — say, a new pattern-matching construct — and in the worst case, *every case of that induction* is now a different proof obligation, because the induction's structure (and possibly its statement) implicitly assumed the fixed set of 40 forms. There's no way to look at the diff to the language spec and predict, in advance, how much proof work the change will cost. That unpredictability, more than the raw effort of any single proof, is what makes verified compilers "bespoke artifacts" that few teams can afford to build and even fewer can afford to maintain.

## Three specific failure modes in prior work

The book is precise about *which* limitations recur, because each one motivates a specific design choice in Pyrosome later on.

### 1. Rigid tie to a fixed source language

Existing verified-compiler projects (CompCert being the canonical example, discussed further in [[Compiler-Correctness-in-the-Broader-Literature]]) build their correctness theorem around one specific, fixed source language definition. The proof machinery — the induction principles, the simulation relations, the invariants — is written *for that language*, not for "languages in general." Extending the source language with a new feature means extending (and often restructuring) the proof machinery itself, not just adding a case to it.

### 2. Separate compilation as a weak form of linking

"Linking" sounds like a solved problem — object files get linked together constantly in unverified toolchains. But verified linking results in the literature typically only support **separate compilation**: you can link two pieces of code *if and only if* both were compiled from the same source language, and often only by the same compiler. This rules out something as ordinary as linking verified-compiler output against hand-written assembly, a hand-optimized library routine, or code compiled by a *different* verified pipeline. Perconti and Ahmed (2014) improved on this by proving a correctness result that supports linking against genuinely arbitrary target-language code — but their technique is a **multilanguage approach**: it works by literally building a combined language containing constructs from *every* source and target language involved, baked directly into the statement of the correctness theorem. That buys expressive linking at the cost of extensibility: adding a new language to the picture means growing the combined multilanguage and restating (and rechecking) the correctness theorem against the new, larger combination.

### 3. Monolithic specifications can't absorb incremental change

Existing verification efforts treat a source language's specification as one indivisible object — you verify against "the language," not against "this specific list of rules, some of which might later be revised." When a real language's spec changes incrementally (which is the normal mode for any actively maintained language), there's no way to isolate the verification cost to just the changed part, because the proof was never structured with "part" as a meaningful unit in the first place.

## The shape of Pyrosome's answer (previewed here, developed later)

The introduction previews — informally, without the generalized-algebraic-theory formalism developed in Chapter 3 — how Pyrosome intends to dissolve all three problems at once, using a worked example: compiling STLC into continuation-passing style (CPS).

The compiler is given as a small table of rewrite-style equations (Figure 1-1 in the source):

$$
\begin{aligned}
\lfloor A \to B \rfloor &\triangleq \neg(\lfloor A \rfloor \times \neg \lfloor B \rfloor) \\
\lfloor x \rfloor &\triangleq k\,x \\
\lfloor \lambda(x:A).\,e \rfloor &\triangleq k\,\lambda(x:\lfloor A \rfloor, k':\neg\lfloor B\rfloor).\,\lfloor e \rfloor[k'/k] \\
\lfloor e\,e' \rfloor &\triangleq \mathrm{bind}\ x := \lfloor e \rfloor;\ \mathrm{bind}\ y := \lfloor e' \rfloor;\ x\,\langle y, k\rangle
\end{aligned}
$$

**Type preservation** for this compiler is unremarkable: a standard induction on the source term, one case per syntactic form, exactly as you'd expect. **Equivalence preservation** is where the interesting design choice appears. The book deliberately does *not* reach for **contextual equivalence** — the standard notion in the literature, which says two terms are equivalent iff no surrounding program context can tell them apart. Contextual equivalence is notoriously hard to reason about directly (it universally quantifies over *all* contexts, an intractable proof obligation in general), and — more importantly for this thesis's purposes — **it behaves badly under language extension**: whether two terms are contextually equivalent can change depending on what other, unrelated features happen to be present in the language, because adding features can add new contexts that suddenly *can* distinguish two previously-indistinguishable terms. (This tension is explored in full via the *callTwice* example in [[Equivalence-Preservation-versus-Contextual-Equivalence]].)

Instead, Pyrosome characterizes source-language semantics via an **equational theory**: a set of equations like beta and eta for STLC,

$$
(\lambda(x:A).\,e)\,v = e[v/x] \qquad\qquad (\lambda(x:A).\,f\,x) = f
$$

closed under reflexivity, transitivity, symmetry, and congruence (see [[Language-Specifications-as-Equational-Theories]] for the full formal treatment). Because this notion of equivalence is defined *syntactically*, by a fixed, finite list of axioms, it doesn't implicitly depend on "every context that might exist in some future extension of the language" — it depends only on the axioms actually listed. This is the structural reason equivalence preservation proofs decompose into one obligation *per axiom*, and why adding a new language feature only adds new axioms (and new proof obligations for them) rather than perturbing the existing ones.

The book walks the beta-equivalence proof obligation for the CPS example concretely: given the beta axiom $(\lambda(x:A).e)\,v = e[v/x]$, the corresponding proof obligation is to show $\lfloor(\lambda(x:A).e)\,v\rfloor = \lfloor e[v/x]\rfloor$ in the *target* language's equational theory — which the book discharges by literally rewriting the left-hand side using target-language equations until it lands on $\lfloor e\rfloor[\lfloor v\rfloor/x] = \lfloor e[v/x]\rfloor$ (the last step relying on substitution invariance, per [[Compilers-as-Finite-Maps]]).

Finally, the introduction previews **extension**: adding a global mutable store to both the source and target languages (Figure 1-2), by adding new compiler cases for `set`/`get`, and reusing — not re-proving — the original beta/eta obligations via a **monotonicity** principle (formalized later in [[The-Preserving-Predicate-and-Modularity-Theorems]]).

## Grounding: what "extensible" verification would look like in practice

**Rust (primary) — the shape of the problem as a type-system designer feels it.** Imagine a compiler pass structured as a big `match` over an AST enum:

```rust
enum SourceExpr {
    Var(String),
    Lambda(String, Type, Box<SourceExpr>),
    App(Box<SourceExpr>, Box<SourceExpr>),
    // adding a new variant here means every exhaustive match
    // over SourceExpr must grow a new arm, INCLUDING the ones
    // buried inside a correctness proof/spec.
}

fn compile(e: &SourceExpr) -> TargetExpr {
    match e {
        SourceExpr::Var(x) => /* ... */,
        SourceExpr::Lambda(x, ty, body) => /* ... */,
        SourceExpr::App(f, arg) => /* ... */,
    }
}
```

A monolithic proof of "compile preserves semantics" that is itself structured as one giant induction over `SourceExpr` has exactly the extensibility problem the book describes: the Rust compiler will *force* you to add a match arm when you add a variant, but nothing forces — or even helps — the *proof* to be similarly incremental unless the proof itself was designed, from the start, to be a composition of independent per-constructor facts (which is exactly what Pyrosome's `Preserving` predicate later provides — see [[The-Preserving-Predicate-and-Modularity-Theorems]]).

**Lean (secondary).** The equational-theory-vs-contextual-equivalence choice maps directly onto a distinction Lean users navigate constantly: definitional equality (`rfl`-provable, syntactically/computationally grounded, closed under a fixed set of reduction rules — analogous to Pyrosome's equational theory) versus propositional equality established via some possibly-elaborate argument about *all possible* uses of a term (closer in spirit to contextual reasoning). Lean's kernel deliberately keeps `isDefEq` checking anchored to a small, fixed reduction relation for exactly the same tractability reason Pyrosome avoids contextual equivalence.

**Python (tertiary).** A tiny illustration of "monolithic vs. per-form" proof obligations, just to see the shape:

```python
# Monolithic: one big function, one undifferentiated correctness claim.
def compile_and_check_whole_language(source_ast): ...

# Per-form: correctness is a dict of independent obligations,
# one per constructor, that can be extended by adding entries.
obligations = {
    "Var": lambda ctx: ...,
    "Lambda": lambda ctx: ...,
    "App": lambda ctx: ...,
}
```

## Where this leads

This chapter is pure motivation — it names the disease (rigidity, weak linking, monolithic specs) without yet giving the cure's formal machinery. Everything that follows is the cure: [[Pyrosomes-Design-Philosophy]] and [[Language-Specifications-as-Equational-Theories]] give the representation that makes "one obligation per rule" possible, [[The-Preserving-Predicate-and-Modularity-Theorems]] gives the actual modular proof technique, and [[The-STLC-to-CPS-to-Closures-Case-Study]] is this same worked example, done for real, with a full formal compiler and proof.

For this workbench's compiler/elaborator project: this is the strongest possible argument for designing your Rust compiler's correctness story (type-checking soundness, refinement-type soundness) around per-construct, per-rule obligations from day one — retrofitting modularity onto a monolithic proof later is, per this chapter, close to as expensive as starting over.
