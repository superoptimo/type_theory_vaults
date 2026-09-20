---
title: Algorithmic Subtyping and Instantiation
source: "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism (Dunfield & Krishnaswami, ICFP '13)"
chapters: "Section 3.2–3.3, pp. 5–8"
tags: [type-theory, bidirectional-typechecking, polymorphism, unification, elaboration]
---

# Algorithmic Subtyping and Instantiation

[[book-guidelines|↩ Back to guidelines]]

## Why the declarative rules can't be run as an algorithm

The [[Declarative-Type-System|declarative subtyping rules]] $\le\!\forall L$ and $\le\!\forall R$ are elegant but *oracular*: $\le\!\forall L$ says "replace $\alpha$ with some monotype $\tau$" — but which $\tau$? A specification is allowed to guess; an algorithm has to compute. That's the whole problem this section solves: turn "guess a type" into "defer the guess, and let the rest of the derivation pin it down."

The mechanism is the *existential type variable* $\hat\alpha$, tracked in the [[Algorithmic-Contexts|ordered algorithmic context]] from Section 3.1. Instead of picking $\tau$ up front, $\le\!\forall L$ introduces a fresh $\hat\alpha$ standing for "the answer, to be determined later," and the rest of the derivation *solves* $\hat\alpha$ by comparing it against concrete types as it goes. This is precisely metavariable-driven elaboration: what a Lean-style elaborator calls a metavariable, this paper calls an unsolved existential, and what Lean's `isDefEq`/unifier does when it assigns a metavariable, this paper's `InstLSolve`/`InstRSolve` rules do explicitly, with a full proof that the process terminates and is both sound and complete.

## Algorithmic subtyping (Figure 9)

[[Metatheory-of-the-Algorithm#The judgment|The judgment]] is $\Gamma \vdash A <: B \dashv \Delta$ — under input context $\Gamma$, $A$ is a subtype of $B$, producing an *output* context $\Delta$ that may have learned more about existentials than $\Gamma$ knew. This threading of input/output contexts is the single biggest structural difference from the declarative system, and it's exactly the "context as mutable unification state, passed explicitly" pattern:

```rust
// Every algorithmic judgment has this shape.
fn subtype(gamma: Context, a: &Type, b: &Type) -> Result<Context, TypeError> {
    // returns the *output* context delta, which extends gamma
    todo!()
}
```

**The easy rules — no existentials involved:**

- `<:Var`: $\Gamma[\alpha] \vdash \alpha <: \alpha \dashv \Gamma[\alpha]$ — reflexivity for a bound type variable, output = input.
- `<:Unit`: $\Gamma \vdash 1 <: 1 \dashv \Gamma$ — same idea for the unit type.
- `<:Exvar`: $\Gamma[\hat\alpha] \vdash \hat\alpha <: \hat\alpha \dashv \Gamma[\hat\alpha]$ — an *unsolved* existential is trivially a subtype of itself. Note this doesn't solve $\hat\alpha$ to anything; it just says "no new information here."

**`<:→` — threading the context, sequentially:**

$$\frac{\Gamma \vdash B_1 <: A_1 \dashv \Theta \qquad \Theta \vdash [\Theta]A_2 <: [\Theta]B_2 \dashv \Delta}{\Gamma \vdash A_1 \to A_2 <: B_1 \to B_2 \dashv \Delta}$$

Two things to notice, both of which are exactly what you'd expect from a Rust-style typechecker written with mutable unification state, made explicit here as data:

1. Contravariance: domains are compared $B_1 <: A_1$ (flipped), codomains $A_2 <: B_2$ (same order) — the usual subtyping story for function types.
2. **Sequencing**: the first premise's *output* context $\Theta$ becomes the second premise's *input* context. And critically, the second premise doesn't just check $A_2 <: B_2$ — it checks $[\Theta]A_2 <: [\Theta]B_2$, applying $\Theta$ as a substitution first. This is the algorithm re-normalizing types against everything solved so far before continuing — the same reason a Rust unifier calls `resolve()` on a type before comparing it, rather than trusting a stale copy. The paper states this as an invariant: whenever you're about to derive $\Gamma \vdash A <: B \dashv \Delta$, $A$ and $B$ are already "fully applied" under $\Gamma$ — no unnecessary lingering solved-but-unsubstituted existentials.

**What breaks without re-application:** if `<:→`'s second premise checked $A_2 <: B_2$ directly instead of $[\Theta]A_2 <: [\Theta]B_2$, any existential solved while checking the domain would be invisible when checking the codomain — you'd effectively be unifying against a stale snapshot, exactly the bug you get in a hand-rolled unifier that forgets to path-compress/resolve before comparing.

**`<:∀L` — the key departure from the declarative rule:**

$$\frac{\Gamma, I_{\hat\alpha}, \hat\alpha \vdash [\hat\alpha/\alpha]A <: B \dashv \Delta, I_{\hat\alpha}, \Theta}{\Gamma \vdash \forall\alpha.A <: B \dashv \Delta}$$

Instead of substituting a guessed monotype $\tau$ for $\alpha$ (as $\le\!\forall L$ did), this introduces a **fresh existential $\hat\alpha$** and a **scope marker $I_{\hat\alpha}$**, pushed onto the context, then substitutes $\hat\alpha$ for $\alpha$ and recurses. The marker's job is purely bookkeeping: it delimits which later existentials were "born" during this instantiation (via articulation, see below), so that when the premise concludes, the algorithm can strip $I_{\hat\alpha}$, $\hat\alpha$, and any *unsolved trailing existentials* $\Theta$ out of the output context — they're out of scope once you leave the $\forall L$ derivation, precisely because they were never meaningful outside it (any unconstrained existential can be soundly treated as if it had been instantiated to anything well-formed, e.g. $1$).

**`<:∀R`** is closer to its declarative counterpart $\le\!\forall R$: add a fresh universal $\alpha$ to the context, recurse, then drop $\alpha$ and any trailing $\Theta$ from the output. Since $\alpha$ is a genuine bound variable (not an existential to be solved), it can act as its own "marker" — there's no need for a separate one.

**`<:InstantiateL` / `<:InstantiateR` — the handoff:**

$$\frac{\hat\alpha \notin FV(A) \qquad \Gamma[\hat\alpha] \vdash \hat\alpha :=\!\!< A \dashv \Delta}{\Gamma[\hat\alpha] \vdash \hat\alpha <: A \dashv \Delta} \qquad\qquad \frac{\hat\alpha \notin FV(A) \qquad \Gamma[\hat\alpha] \vdash A =\!\!\!<: \hat\alpha \dashv \Delta}{\Gamma[\hat\alpha] \vdash A <: \hat\alpha \dashv \Delta}$$

These two rules are the seam between subtyping and instantiation. When one side of a subtyping goal is an unsolved existential and the other is some type $A$, subtyping doesn't do the solving itself — it does an *occurs check* $\hat\alpha \notin FV(A)$ (exactly the occurs check every unification algorithm needs, to reject circular solutions like $\hat\alpha := \hat\alpha \to \text{int}$), and then delegates entirely to the instantiation judgment.

## Instantiation (Figure 10): solving an existential

Two judgments, nearly symmetric:

- $\Gamma \vdash \hat\alpha :=\!\!< A \dashv \Delta$ — "instantiate $\hat\alpha$ to a subtype of $A$" (feeds `<:InstantiateL`).
- $\Gamma \vdash A =\!\!\!<: \hat\alpha \dashv \Delta$ — "instantiate $\hat\alpha$ to a supertype of $A$" (feeds `<:InstantiateR`).

The notation $:=\!\!<$ is meant to evoke both "assignment" and "less-than" at once — read it as "solve, with a subtyping obligation attached."

### `InstLSolve` — the base case, an actual metavariable assignment

$$\frac{\Gamma \vdash \tau}{\Gamma, \hat\alpha, \Gamma' \vdash \hat\alpha :=\!\!< \tau \dashv \Gamma, \hat\alpha = \tau, \Gamma'}$$

If the target $A$ is already a *monotype* $\tau$ (no embedded $\forall$), and $\tau$ is well-formed under the part of the context to the left of $\hat\alpha$, just solve it: $\hat\alpha \mapsto \tau$. This is the literal analogue of a Rust `Metavar::assign(tau)` or Lean's metavariable-context update — the point in the algorithm where a piece of unification state actually gets written.

```rust
enum CtxEntry {
    Universal(TyVar),
    TermVar(Var, Ty),
    Unsolved(ExVar),
    Solved(ExVar, Monotype),   // InstLSolve writes exactly this
    Marker(ExVar),
}
```

### `InstLArr` — articulation: the existential learns its own shape

$$\frac{\Gamma[\hat\alpha_2, \hat\alpha_1, \hat\alpha = \hat\alpha_1 \to \hat\alpha_2] \vdash A_1 =\!\!\!<: \hat\alpha_1 \dashv \Theta \qquad \Theta \vdash \hat\alpha_2 :=\!\!< [\Theta]A_2 \dashv \Delta}{\Gamma[\hat\alpha] \vdash \hat\alpha :=\!\!< A_1 \to A_2 \dashv \Delta}$$

If the target is a function type $A_1 \to A_2$, then whatever $\hat\alpha$ eventually resolves to, it has to *be* a function type too — so the algorithm doesn't wait to find out; it commits to the shape immediately. This is **articulation**: replace the single unsolved $\hat\alpha$ with $\hat\alpha = \hat\alpha_1 \to \hat\alpha_2$, where $\hat\alpha_1, \hat\alpha_2$ are two brand-new existentials, inserted **immediately to the left of $\hat\alpha$'s old position**.

**What breaks without that specific insertion point:** the context is *ordered* (see [[Algorithmic-Contexts]]), and $\hat\alpha_1, \hat\alpha_2$ must appear in $\hat\alpha$'s solution — so by well-formedness, they must be declared to its left. But they also need to stay inside whatever scope $\hat\alpha$ itself was created in (e.g. to the right of the marker $I_{\hat\alpha'}$ that `<:∀L` pushed when $\hat\alpha$ was born) — insert them anywhere else and you'd either violate the ordering invariant or leak them out of the scope that's supposed to contain them. It's the same discipline a Rust arena-allocated union-find needs when it splits one placeholder into two: the new nodes have to slot in exactly where the dependency graph requires, not just "somewhere."

Note the domain premise is *flipped* to $A_1 =\!\!\!<: \hat\alpha_1$ (contravariance again, now showing up inside instantiation itself, not just subtyping), and the codomain premise re-applies the intermediate context $\Theta$ to $A_2$ before recursing — the same "always re-substitute before comparing" discipline from `<:→`.

### `InstLReach` — when the "solution" is another existential

$$\frac{}{\Gamma[\hat\alpha][\hat\beta] \vdash \hat\alpha :=\!\!< \hat\beta \dashv \Gamma[\hat\alpha][\hat\beta = \hat\alpha]}$$

Here $\hat\alpha$ appears to the *left* of $\hat\beta$ in the context. You might expect `InstLSolve` to fire (set $\hat\alpha := \hat\beta$), but it can't: $\hat\beta$ isn't even in scope at $\hat\alpha$'s declaration point (it's declared later), so $\hat\beta$ is not well-formed there. The fix "reaches" the other direction: solve $\hat\beta := \hat\alpha$ instead — legal, since $\hat\alpha$ *is* in scope at $\hat\beta$'s position. Same information content, opposite direction of assignment, purely to respect ordering. This is a subtle but important lesson for anyone building a metavariable-context data structure: *which* variable gets assigned to which is not a free choice — it's dictated by declaration order, exactly the way a union-find's "union by rank/which representative wins" has real invariants behind it, not just convention.

### `InstLAllR` — instantiating under a quantifier, predicatively

$$\frac{\Gamma[\hat\alpha], \beta \vdash \hat\alpha :=\!\!< B \dashv \Delta, \beta, \Delta'}{\Gamma[\hat\alpha] \vdash \hat\alpha :=\!\!< \forall\beta.B \dashv \Delta}$$

Because the system is **predicative** (see [[The-Problem-of-Polymorphism-in-Bidirectional-Systems]]), $\hat\alpha$ can never be assigned a polymorphic type outright — $\hat\alpha := \forall\beta.B$ is not a legal monotype solution. So the algorithm decomposes the quantifier the same way subtyping does: push $\beta$ onto the context, recurse into the body, then drop $\beta$ and any trailing existentials on exit.

`InstRSolve`, `InstRReach`, `InstRArr` are the direct mirror images for the $=\!\!\!<: \hat\alpha$ judgment, and `InstRAllL` mirrors `InstLAllR` (decomposing a $\forall$ on the *other* side).

## Worked example: instantiation "changes its mind"

The paper's headline example: instantiate $\hat\beta$ to a *supertype* of $\forall\alpha.\alpha$. The type $\forall\alpha.\alpha$ is so polymorphic it constrains $\hat\beta$ not at all — naively you might think the algorithm is stuck making an arbitrary, incomplete choice. It isn't, because of `InstRAllL` + `InstRReach` working together:

1. `InstRAllL` decomposes $\forall\alpha.\alpha$ by introducing a *fresh* existential $\hat\alpha$ under the quantifier (not reusing $\hat\beta$).
2. Recursing now asks to instantiate $\hat\alpha$ (not $\hat\beta$!) against... $\hat\beta$ itself. This triggers `InstRReach`.
3. `InstRReach` sets $\hat\alpha := \hat\beta$ — **not** the other way around, precisely because $\hat\beta$ was declared first and $\hat\alpha$ is the newcomer.

Net effect: $\hat\beta$ ends the derivation completely unconstrained, exactly as it should be — the algorithm introduced a scratch variable $\hat\alpha$, discovered *it* was the one that needed solving, and solved that instead. This "changing its mind about which variable to instantiate" is the mechanistic core of why the reach rule exists at all: instantiation isn't a single fixed assignment target chosen in advance, it's discovered as the derivation proceeds — precisely the flexibility a real unifier needs when it encounters `?m1 =?= ?m2` and has to decide, based on scope, which metavariable defers to which.

A second worked example (Figure 12 in the paper) chains `InstLReach`, `InstRArr` (articulation on the *right*), and `InstRSolve` to instantiate $\hat\alpha$ against $\forall\beta.\beta\to\beta$, landing on the monomorphic approximation $\hat\beta_1 \to \hat\beta_1$ — a concrete illustration of predicativity in action: the polymorphic type gets approximated by *a* monotype instance, never assigned as-is.

## Termination, briefly

Section 5 (Decidability) later proves this all terminates via a measure that strictly decreases: instantiating to a monotype always shrinks the *count of unsolved existentials* in the context, and `InstLArr`/`InstRArr`'s recursive premises are always applied to strictly smaller types than the conclusion (Θ can't make a type larger, only substitute already-smaller pieces into it). That's beyond this section's scope, but it's the reason none of this loops forever despite the rules calling each other in a cycle (subtyping → instantiation → subtyping via the `Arr` rules' flipped-direction premises).

## Where this leads

This is the mechanical heart of the paper — the piece an implementation actually spends most of its runtime inside. Everything upstream (declarative rules, the notion of contexts) exists to make this precise; everything downstream ([[Algorithmic-Typing|algorithmic typing]], and the metatheory of [[Metatheory-of-the-Algorithm|context extension, decidability, soundness, completeness]]) exists to justify that this precise mechanism is *correct*.

**For the bidirectional elaborator project:** this section *is* the metavariable-solving core you'll build. `InstLSolve`/`InstRSolve` is metavariable assignment; articulation (`InstLArr`/`InstRArr`) is the "decompose a metavariable into a structured shape before you know its full solution" move that any occurs-check-respecting unifier needs for compound types; `InstLReach`/`InstRReach` is exactly the discipline Miller's pattern unification imposes when solving `?m1 =?= ?m2` — which metavariable gets to be the "pattern" solved for depends on scope, not on which side of `=` it's written. The scope-marker discipline ($I_{\hat\alpha}$, dropping trailing existentials on exit) is the same idea as a local-metavariable-scope stack in Lean's elaborator, cleaned up before returning to the caller.
