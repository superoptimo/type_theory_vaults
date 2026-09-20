---
title: Inverting Substitutions
source: "Extensions to Miller's Pattern Unification for Dependent Types and Records (Abel & Pientka)"
chapter: "Chapter 3, Section 3.3 (pp. 12–13)"
tags: [type-theory, unification, higher-order-unification, pattern-unification, automated-reasoning]
---

[[book-guidelines|↩ Back to guidelines]]

## Why unification needs to invert something at all

Zoom out for a second to where the algorithm actually stands by the time it reaches this
section. Decomposition (3.2) has been chewing through a constraint until it's stuck on
something of the shape

$$u[\sigma] = M$$

— a meta-variable applied to some delayed substitution $\sigma$, equated to a term $M$. This is
the moment where the algorithm has to *commit*: propose an actual value for $u$. And the
natural thing to propose is "solve for $u$ by running $\sigma$ backwards" — if $\sigma$ sent $u$'s
local variables into $M$'s ambient context, running it in reverse should recover a term that,
substituted back through $\sigma$, reproduces $M$.

That's the idea. The section exists because that idea is far more fragile than it sounds.
Substitutions in general are not invertible, and even when a *unique* answer does exist, blindly
inverting $\sigma$ can silently produce the wrong one, or produce something when it should have
failed. Get this step wrong and the "most general unifier" the whole algorithm promises stops
being most general — or stops existing at all.

## What breaks without a precise notion of invertibility

Take the simplest possible case, where $\sigma$ isn't even a variable substitution — it substitutes
an actual term for $u$'s argument:

$$u[\mathrm{true}] = \mathrm{true}$$

Already two incompatible closed solutions exist as plain $\lambda$-terms: $u[x] = x$ and $u[x] =
\mathrm{true}$. There is no most general one that captures both — they're just different answers.
(And if the calculus had computation on booleans, as Agda's does, there would be *infinitely*
many solutions, because $u$ could branch on $x$ and leave the $\mathrm{false}$ case completely free.)
This is why the algorithm restricts this solving step to the case where $\sigma$ is a **variable
substitution** $\rho$ — a substitution whose entries are themselves distinct bound variables, not
arbitrary terms. Only then is there hope of a canonical, most-general answer.

But restricting to variable substitutions isn't enough by itself. A variable substitution can
still be *non-linear* — the same variable can appear more than once in its range. And
non-linearity reintroduces exactly the same ambiguity one level up:

$$u[x, x] = x$$

has two equally good solutions, $x, y \vdash u \leftarrow x$ and $x, y \vdash u \leftarrow y$ — the
constraint simply doesn't say which occurrence of $x$ the answer should track. Contrast this with

$$u[x, x, z] = z$$

which *does* have a unique solution, $x, y, z \vdash u \leftarrow z$, despite $\rho$ itself being
non-linear — the non-linear part of $\rho$ (the repeated $x$) just never shows up on the
right-hand side, so it's harmless.

That contrast is the whole section in miniature: linearity of $\rho$ is a clean sufficient
condition for a unique solution to exist, but it's needlessly strong, because a substitution
only has to be linear on the variables that actually occur in $M$.

## Invertibility, defined

The paper makes this precise as a property of a substitution *relative to a specific term*,
not a global property of the substitution alone:

> A variable substitution $\rho$ is **invertible for a term $M$** if there is exactly one $M'$
> such that $[\rho]M' = M$.

And the refined claim that motivates the rest of the section:

- Linearity of $\rho$ (globally) is **sufficient** for invertibility, but not necessary.
- What's actually **necessary** is that $\rho$ be linear *when restricted to $\mathrm{FV}(M)$* —
  and $M$ has to be $\beta$-normal for that restriction to be a stable notion (normalization can
  both create and destroy free-variable occurrences, so "the free variables of $M$" would be a
  moving target otherwise).

This localizes the requirement to exactly the variables that matter for this particular
equation, which is what let the earlier $u[x,x,z]=z$ example succeed despite global
non-linearity.

## The direct algorithm: skip computing free variables entirely

Here's the implementation wrinkle the section actually solves. The definition above suggests an
algorithm: compute $\mathrm{FV}(M)$, check $\rho$ is linear there, invert $\rho$, apply the
inverse to $M$. That's three separate passes plus a decidability check before you've done any
real work.

Abel and Pientka skip all of it. Instead they define a single **partial, structurally recursive
operation** that tries to invert $\rho$'s effect on $\alpha$ (a term, neutral term, or
substitution) directly, term node by term node, and simply gets stuck — is undefined — exactly
where inversion is impossible. No separate free-variables pass, no separate check: success and
failure fall out of the recursion itself.

Written $[\rho/\hat\Phi]^{-1}\alpha$ (inverting the variable substitution $\Psi \vdash \rho
\Leftarrow \Phi$, tracking the target context via $\hat\Phi$, applied to $\alpha ::= M \mid R \mid
\tau$), the defining clauses are:

$$
[\rho/\hat\Phi]^{-1}x =
\begin{cases}
y & \text{if } x/y \in \rho/\hat\Phi \text{ and no other } x/z \in \rho/\hat\Phi \text{ with } z \neq y \\
\text{undefined} & \text{otherwise}
\end{cases}
$$

$$[\rho/\hat\Phi]^{-1}c = c$$

$$[\rho/\hat\Phi]^{-1}(u[\tau]) = u[\tau'] \quad \text{where } \tau' = [\rho/\hat\Phi]^{-1}\tau$$

and homomorphically through every other constructor:

$$[\rho/\hat\Phi]^{-1}(R\,M) = R'\,M' \qquad [\rho/\hat\Phi]^{-1}(\pi\,R) = \pi\,R'$$

$$[\rho/\hat\Phi]^{-1}(\lambda x.\,M) = \lambda x.\,M' \quad \text{if } x \notin \rho, \hat\Phi \text{ and } M' = [\rho, x/\hat\Phi, x]^{-1}M$$

$$[\rho/\hat\Phi]^{-1}(M, N) = (M', N') \qquad [\rho/\hat\Phi]^{-1}(\cdot) = \cdot \qquad [\rho/\hat\Phi]^{-1}(\tau, M) = (\tau', M')$$

The variable case is where all the interesting behavior lives, and it's worth reading it slowly:
to invert $\rho$ at variable $x$, look up which target variable $y$ maps to $x$ under $\rho$ —
**but only if $y$ is the unique such variable**. If two different bound variables both map to
$x$ (the non-linear case), the operation is simply undefined at that occurrence, right when and
where the ambiguity would actually bite — not earlier, via some global linearity check, and not
later, via producing a wrong answer. This is precisely how the $u[x,x,z]=z$ example above gets
solved automatically: inverting at the occurrence of $z$ succeeds cleanly (unique preimage), and
the repeated, ambiguous $x$-occurrences are never even visited because they don't occur in $M$.

The binder case, $[\rho/\hat\Phi]^{-1}(\lambda x. M)$, is the other subtlety: to invert under a
binder you have to *extend* both substitutions with the newly bound variable mapped to itself
($\rho, x$ and $\hat\Phi, x$) before recursing — otherwise the fresh $x$ would have no entry in
$\rho$ at all and every inversion under a lambda would spuriously fail.

## Why this needs three lemmas, not just a definition

A partial operation defined by pattern-matching recursion is only useful for unification if it's
provably doing the job "invertibility" was supposed to do. Three lemmas discharge that:

- **Lemma 3.4 (commutes with meta-substitution).** If $[\rho/\hat\Phi]^{-1}\alpha$ and
  $[\rho/\hat\Phi]^{-1}([\![\theta]\!]\alpha)$ both exist, they agree with applying $\theta$
  after inverting: $[\rho/\hat\Phi]^{-1}([\![\theta]\!]\alpha) = [\![\theta]\!]([\rho/\hat\Phi]^{-1}\alpha)$.
  This is the property that lets the algorithm treat "solve now" and "instantiate metas
  later" as interchangeable — a solution found today stays valid after later meta-variables
  in the same problem get resolved.
- **Lemma 3.5 (soundness).** If $[\rho/\hat\Phi]^{-1}\alpha$ exists, then applying $\rho$ back
  to it reproduces $\alpha$ exactly: $[\rho]_\Phi([\rho/\hat\Phi]^{-1}\alpha) = \alpha$. This is
  the half that says: whenever the algorithm *does* commit to an answer, that answer is
  actually correct — not just plausible.
- **Lemma 3.6 (completeness).** If $[\rho]_\Phi\alpha = \alpha'$ and $\rho$ happens to be
  linear restricted to $\mathrm{FV}(\alpha)$ (in the precise sense above — a unique $y/x \in
  \rho$ for every free $x$), then $[\rho/\hat\Phi]^{-1}\alpha'$ is defined and recovers
  $\alpha$. This is the half that says: whenever a solution *does* exist under the necessary
  condition, the direct recursive procedure is guaranteed to find it — it never gives up
  prematurely.

Soundness plus completeness together mean the recursive, structural definition above is not an
approximation of "invertibility" — it *is* invertibility, computed without ever explicitly
touching $\mathrm{FV}(M)$.

## What this feeds directly: pruning and the occurs check

Section 3.3 sits between the local-simplification rules (3.2) and pruning (3.4) for a reason.
Pruning's opening move — turning $u[\sigma] = M$ into an actual solution — is *exactly*
"invert $\sigma$ on $M$", using this machinery; pruning's job is to first massage away the free
variables of $M$ that fall outside $\sigma$'s range so that this inversion can succeed at all.
Without a precise, partial notion of inversion, "the occurs check fails" and "pruning is
possible" would have no crisp boundary — you'd be relying on informal reasoning about what
"should" be recoverable, which is exactly the kind of gap the paper's introduction calls out in
earlier, non-terminating treatments (Reed 2009b) of this same problem.

## Grounding: this *is* metavariable assignment in an elaborator

This section maps almost line-for-line onto what a dependently typed elaborator's unifier does
when it decides to *assign* a metavariable — this is the mechanism inside Lean's `isDefEq`
(and Agda's, and Coq's) usually called "pattern unification" or "Miller-pattern solving" for
exactly this reason.

**Lean, as the most literal correspondence.** When Lean's elaborator hits `?m x y =?= e` where
`?m` is a metavariable and `x, y` are distinct local free variables (a *pattern*), it doesn't
compute the free variables of `e` as a separate pass either — it walks `e` and tries to rewrite
each free variable it finds back to the argument position that introduced it, failing the whole
attempt the moment it meets a free variable that isn't one of `x, y`, or that would be
ambiguous. That walk **is** `[\rho/\hat\Phi]^{-1}`. The soundness/completeness pair (Lemmas
3.5–3.6) is exactly the property Lean's kernel implicitly relies on when it accepts `?m := fun x
y => e'` as a checked, defeq-preserving assignment — if the elaborator's "abstract $e$ over $x,
y$" step were unsound, `rfl` and `isDefEq` downstream would silently accept ill-formed proofs.

```lean
-- Sketch of what "invert ρ on M" looks like as Lean-elaborator-shaped pseudocode.
-- `fvars` is the pattern's argument list (Ψ's variables in order); `e` is the RHS term.
partial def invertPattern (fvars : Array FVarId) (e : Expr) : Option Expr := do
  -- Walk e; every free variable occurrence must be one of `fvars`, and uniquely so.
  -- This partial function IS [ρ/Φ̂]⁻¹ — undefined (returns none) exactly where
  -- the paper's clauses are undefined: an out-of-scope var, or an ambiguous one.
  let abstracted ← abstractOverPattern e fvars
  return abstracted   -- the candidate solution body for ?m
```

**Rust, as the checker-shaped implementation.** If you're building the elaborator's unifier as a
Rust pass (the shape this paper's whole apparatus is headed toward for a metavariable-solving
kernel), the natural encoding is a `HashMap<VarId, VarId>` for $\rho$ (each domain variable to
its unique range variable) plus a *fallible*, structurally recursive function that returns
`Option<Term>` rather than `Term` — mirroring the paper's partiality directly instead of
throwing or unwrapping:

```rust
fn invert(rho: &HashMap<VarId, VarId>, term: &Term) -> Option<Term> {
    match term {
        // Variable case: succeeds only if exactly one domain var maps to this range var.
        Term::Var(y) => {
            let mut preimages = rho.iter().filter(|(_, ry)| *ry == y);
            match (preimages.next(), preimages.next()) {
                (Some((x, _)), None) => Some(Term::Var(*x)), // unique preimage
                _ => None,                                    // absent or ambiguous
            }
        }
        Term::Const(c) => Some(Term::Const(c.clone())),
        Term::MetaClosure(u, tau) => Some(Term::MetaClosure(*u, invert_subst(rho, tau)?)),
        Term::App(head, arg) => Some(Term::App(
            Box::new(invert(rho, head)?),
            Box::new(invert(rho, arg)?),
        )),
        Term::Lam(x, body) => {
            // Extend rho with x ↦ x before recursing under the binder.
            let mut rho_ext = rho.clone();
            rho_ext.insert(*x, *x);
            Some(Term::Lam(*x, Box::new(invert(&rho_ext, body)?)))
        }
        // ... Pair, Proj, and substitution-cons cases follow the same homomorphic shape.
    }
}
```

The `Option`-returning, no-panic shape here is the point: this is a *checker*, and the paper's
partiality (Lemma 3.4–3.6 all being stated as "if ... exists, then ...") is exactly the contract
that a trusted-kernel-facing Rust implementation has to preserve — a failed inversion is a
legitimate outcome, not an error condition, and swallowing that distinction (e.g. by making the
function total and returning some default term on failure) would be a soundness bug in the
elaborator, not just an ergonomics one.

## Where this leads

Inverting substitutions is the load-bearing primitive underneath both remaining pieces of the
solving story: **Section 3.4 (Pruning)** uses it as the final step once a meta-variable's
offending free variables have been stripped out, and the **occurs check / solving** step later
in the chapter (constraint $u[\rho] = M$) is *defined* as "invert $\rho$ on $M$, provided $u$
itself doesn't occur." Get this section wrong, and both of those inherit the bug silently, since
neither re-derives invertibility from scratch — they both just call $[\rho/\hat\Phi]^{-1}$ and
trust Lemmas 3.4–3.6.

For the standing project, this is the single clearest place in the paper where "the metavariable
unifier (Miller's pattern-unification fragment)" from the **Automated Reasoning** focus area
stops being a slogan and becomes an actual algorithm to port: a partial, structurally recursive
function with a stated soundness and completeness theorem is precisely the shape a trusted
elaborator kernel needs its `assign` step to have, and the Lean correspondence above is meant to
be taken literally rather than as a loose analogy — this *is* the mechanism, under a different
name, that a Lean-style `isDefEq` runs every time it accepts a metavariable assignment during
implicit-argument resolution.
