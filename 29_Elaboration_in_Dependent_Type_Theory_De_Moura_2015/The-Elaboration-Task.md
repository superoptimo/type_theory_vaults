---
title: The Elaboration Task
source: "Elaboration in Dependent Type Theory (de Moura, Avigad, Kong, Roux, 2015)"
chapter: "Section 2, 2.1 (pp. 2-4)"
tags: [type-theory, elaboration, lean, dependent-types, type-inference]
---

# The Elaboration Task

[[book-guidelines|↩ Back to guidelines]]

## The problem: humans write less than the type checker needs

Imagine writing this function in a language with dependent types:

```
definition do_twice (f : N → N) (x : N) : N := f (f x)
```

Every piece of this signature is redundant with information the *body* already determines. Given `f (f x)`, a compiler could work out that `x` must have some type `A`, that `f` must have type `A → A`, and that the whole expression has type `A`. A human writing quick, exploratory mathematics — or a quick, exploratory program — doesn't want to spell out `N → N` and `N` by hand every time; they want to write `f (f x)` and let the machine reconstruct the missing scaffolding.

This is not a new problem. Ordinary typed functional languages solve a version of it already: Hindley-Milner type inference lets you write `let double f x = f (f x)` with no annotations at all, and the compiler reconstructs a principal type. What's new in *dependent* type theory is that the scaffolding being reconstructed is no longer just "which simple type" — it can be an arbitrary *term*, because in dependent type theory, types themselves are terms, and terms can appear inside types. Reconstructing a missing piece of a dependently-typed expression is a strictly harder kind of guessing game than reconstructing a missing simple type.

The paper's name for this reconstruction process is **elaboration**: the passage from a *quasi-formal, partially-specified* expression — something a person would actually be willing to type — to a *completely precise, formal* term that a type checker's trusted kernel can verify outright. Elaboration is not the kernel's job; the kernel only checks terms that are already fully explicit. Elaboration is the layer that produces those fully explicit terms in the first place, and it is where nearly all of the "convenience" a user experiences when writing dependently-typed code or proofs actually comes from.

## Why "dependent" makes this genuinely harder

To see why dependency raises the stakes, it helps to fix what "dependent" means concretely. In Lean's core calculus, there is an infinite hierarchy of type universes $\mathrm{Type}_0, \mathrm{Type}_1, \mathrm{Type}_2, \dots$, and each universe is closed under forming $\Pi$-types:
$$
\Pi x : A,\ B
$$
where $A$ and $B$ are themselves type-valued expressions, and — crucially — $B$ is allowed to *mention* $x$. A $\Pi$-type denotes the type of functions $f$ that send each $a : A$ to an element of $B[a/x]$ (the type $B$ with $a$ substituted for $x$). When $x$ doesn't actually occur in $B$, this degenerates to the familiar non-dependent function type, written $A \to B$.

Think about what this buys you, and what it costs the elaborator. In a non-dependent language, a function's *return type* is fixed no matter what argument you pass it — `length : List a → Int` always returns an `Int`. In a dependently typed language, the return type can be computed *from the argument itself*. A function that takes a natural number `n` and returns a vector of exactly `n` elements has a return type that is only known once you know which `n` was passed. So the elaborator can no longer treat "figure out this missing type" and "figure out this missing term" as separate questions — figuring out a missing *type* frequently means solving for a missing *term* (since the type depends on one), and vice versa. Type inference and term inference collapse into a single unified problem, and this is precisely why the paper describes dependent-type elaboration as a *generalization* of Hindley-Milner, not just an application of it to a richer type language: Hindley-Milner only ever has to reconstruct simple types built from type variables and arrows; here, the thing being reconstructed can be an arbitrary well-typed term.

Terms in this calculus also carry a *computational* interpretation — $(\lambda x, t)\, s$ reduces to $t[s/x]$, recursively defined functions reduce on their recursive arguments, and so on — and the kernel's notion of when two types are "the same" is up to this reduction relation, not just syntactic identity. That means the elaborator, when it's deciding whether two things it's trying to unify actually match, has to be willing to *compute* with them, not just compare their surface syntax. (This computational dimension is its own major topic — see the article on [[Computational-Behavior-and-Reduction|computational behavior and reduction]] — but it's worth flagging here because it's inseparable from why dependent-type elaboration is qualitatively harder than simply-typed inference.)

## The two concrete mechanisms: implicit arguments and placeholders

The paper introduces two complementary ways a user tells the elaborator "you figure this part out," and it's worth being precise about the distinction, because they solve different halves of the same problem.

**Underscores (`_`) mark a specific missing piece at the call site.** If you write an application and leave one argument as `_`, you are saying: "there is a value that belongs here; infer it from context." This is a per-use annotation — you decide, term by term, which arguments to omit.

**Curly braces mark an argument as implicit at the *definition* site**, which then applies to *every* call of that function without the caller doing anything at all. The canonical example is list concatenation:
$$
\texttt{append} : \Pi \{A : \mathrm{Type}\},\ \mathtt{list}\ A \to \mathtt{list}\ A \to \mathtt{list}\ A
$$
Here `{A : Type}` is declared implicit once, in the function's signature. A caller writes `append l1 l2`, not `append A l1 l2` — Lean infers `A` automatically every time, typically by looking at the type of `l1` or `l2`. This is the elaboration analogue of what type inference already does invisibly in Hindley-Milner-style languages: you don't write `double : Int → Int` (or annotate its type variable) at every call site of `double`, the compiler works it out from usage. Implicit arguments extend that same convenience to a setting where the "type variable" being inferred might be an arbitrary dependent-type term, not just a monomorphic type.

Both mechanisms ultimately reduce to the same underlying obligation for the elaborator: introduce a placeholder standing for the missing piece, and find a term to put there that makes the whole expression type-check. The difference between an underscore and an implicit-argument declaration is purely about *where the decision to omit something is made* — at the call site, or once and for all in the definition — not about what kind of inference problem results.

## What kind of inference problem this actually is

For a simple case like `append l1 l2`, resolving the placeholder is easy: if `l1` has type `list T`, and `append`'s second explicit argument must have type `list ?A` (naming the placeholder `?A`), then matching `list ?A` against `list T` immediately forces `?A = T`. This is *first-order unification* — matching two terms structurally, with a hole standing in for an unknown subterm, the same kind of unification that drives ordinary Hindley-Milner inference.

But because the thing being solved for is a full term in a dependent calculus rather than a simple-type variable, the placeholder can end up needing to stand for something far more elaborate than a single type — potentially a whole predicate, or a function of several arguments, appearing applied to other terms rather than sitting in isolation. When the unknown appears in a context where it needs to be solved for *as a function*, applied to arguments, this becomes a **higher-order unification problem**, a substantially harder and, in general, undecidable class of problem than first-order unification. The paper takes this up in full (see the article on higher-order unification), but it's worth registering here as the reason elaboration cannot simply be "Hindley-Milman with dependent types swapped in": some of the placeholders that arise are ordinary structural matches, and some of them are open-ended search problems.

## Where this sits in the paper's structure

This section — "the elaboration task" — is deliberately written from the *outside*: it describes what the elaborator must accomplish, using illustrative examples, before Section 3 commits to *how* it accomplishes it (data structures, the constraint-simplification procedure, the solver). Type inference and implicit arguments are the entry point into that larger picture because they are the most immediately recognizable piece — every one of the other outward-facing tasks the paper surveys (higher-order unification, respecting computational reduction, type class inference, overloading, coercions, tactic integration) is, in one way or another, *also* about resolving a placeholder the user was allowed to omit. Type inference and implicit arguments establish the basic vocabulary — placeholders, unification, "fully specified vs. partially specified" — that the rest of the paper's harder cases build on.

## Grounding the idea outside Lean

The underlying mechanism — introduce a metavariable for what's missing, then solve for it via unification — is not exotic; simpler versions of it appear constantly in ordinary statically-typed programming.

**Rust** infers generic type parameters at call sites via essentially first-order unification, the same mechanism that resolves `append`'s `{A : Type}` above:

```rust
fn identity<T>(x: T) -> T { x }

fn main() {
    let n = identity(5);       // T unified with i32 from the argument
    let s = identity("hi");    // T unified with &str from the argument
}
```
You never write `identity::<i32>(5)` — the compiler introduces a placeholder for `T` and unifies it against the argument's type, exactly the `?A = T` step above, just restricted to Rust's non-dependent type system (no type here can ever depend on a *runtime value*, only on other types).

**Python**, being dynamically typed, doesn't have this problem at the language level — but a similar reconstruction shows up in optional-argument defaults and in tools like `mypy`, which perform the same "infer the missing piece from usage" step statically over annotated code, again bounded to simple/generic types rather than full dependent terms.

**Lean itself** (the target language of the paper) is the clearest illustration, since the paper's examples are literally in it — the `append` signature above is Lean syntax, and writing `append l1 l2` is precisely relying on the elaborator to solve the placeholder for `{A : Type}` by unifying it against `l1`'s type. What distinguishes Lean's case from Rust's is exactly the dependent-type gap described above: a Lean placeholder can stand for an arbitrary term — a proof, a predicate, an index into a family of types — not just a monomorphic type variable, which is why elaboration needs an algorithm far more powerful than Hindley-Milner-style unification to close the gap.

## Synthesis

"The elaboration task" is the paper's on-ramp: it fixes the vocabulary — placeholder, implicit argument, unification — using the *easy* end of the problem (first-order cases like `append`), while flagging, via the higher-order example, that the *hard* end is coming. Everything that follows in Section 2 (higher-order unification proper, computational reduction, type classes, overloading, coercions, tactics) is a variation on the same theme: a user leaves something out, and the elaborator has to reconstruct it, under progressively less constrained and more interesting notions of "reconstruct." Section 3's whole internal machinery — metavariables, constraints, the constraint-solving procedure — exists to make good on the promise this section makes informally: that omitting information is safe, because there is a principled procedure that will fill it back in correctly whenever a filling exists.
