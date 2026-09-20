---
title: Constraint-Based Unification as an Inference System
source: "Extensions to Miller's Pattern Unification for Dependent Types and Records (Abel & Pientka)"
chapter: "Chapter 3, §§3.1–3.2 (pp. 5–11)"
tags: [type-theory, automated-reasoning, unification, pattern-unification, elaboration, dependent-types]
---

[[book-guidelines|↩ Back to guidelines]]

## Why an algorithm isn't the right shape for this problem

Suppose you sat down to implement higher-order pattern unification as a single recursive function: `unify(M, N) -> Substitution`. You'd hit a wall almost immediately, and it's worth being precise about *which* wall, because the wall is exactly what motivates everything in this chapter.

The wall is this: unifying two dependently-typed terms is not one problem, it's a *pipeline* of many small, independently-justifiable rewriting steps — peel off a $\lambda$, peel off a pair, contract an $\eta$-expansion, split a $\Sigma$-typed variable into two — and at almost every step in that pipeline, you don't yet know whether the term you're holding is well-typed. You've committed to unifying two sides of an equation, but *proving* that equation type-correct might depend on solving other, unrelated pieces of the same overall unification problem that haven't been solved yet. A function that insists on working with fully well-typed intermediate terms will get stuck exactly where a human doing this on paper wouldn't: it'll refuse to decompose a constraint it *knows* is going to become well-typed once a sibling constraint is solved.

The paper's answer is to stop thinking of unification as a function and start thinking of it as an **inference system** — a set of *rewrite rules* over sets of constraints, in the tradition of Shankar's presentation of rewriting-based proof systems. A "run" of the algorithm isn't a single call stack; it's a rewrite sequence $\Delta \gg \mathcal K \to \Delta' \gg \mathcal K' \to \cdots$ that keeps firing whichever rule applies until nothing does. This buys three things simultaneously that a recursive function can't easily give you: (1) constraints can be solved in *any order*, including postponing one to solve another first; (2) each rule is small enough to prove correct in isolation (this pays off directly in Chapter 4's correctness proof); (3) the notion of "stuck" (no rule applies, but you haven't failed) becomes a first-class outcome instead of an exception.

**[[Correctness-of-the-Unification-Algorithm#What breaks without this|What breaks without this]] framing.** Concretely: consider a meta-variable $u : [x{:}\mathrm{bool}]A$ and the constraint
$$
\Psi \vdash (u[x], M) = (u[\mathrm{true}], N) : \Sigma x{:}A.\, P\,x.
$$
The obviously-correct move is to decompose this pair equation into two smaller ones, $\Psi \vdash u[x] = u[\mathrm{true}] : A$ and $\Psi \vdash M = N : P\,u[x]$. But look at the second constraint's type annotation: it's stated as $P\,u[x]$, yet by the pairing typing rule it should really be $P\,u[\mathrm{true}]$ (substituting the first component in for the bound variable). These two are only $\eta$-equal *if* $u[x] =_\eta u[\mathrm{true}]$ — which is exactly the first constraint we just produced, and haven't solved yet! A strictly-well-typed system can't even state this decomposition step, because at the moment it's performed, the two annotations for the second constraint aren't provably equal. Yet every actual solution of the first constraint will make them equal. This single example is the concrete failure mode that forces the paper to give up strict well-typedness at every intermediate step.

## Constraints and constraint sets

The raw material the rewrite system operates on is defined by grammar, not by an ad-hoc data structure bolted on afterward:

$$
\begin{aligned}
\text{Constraint} \quad K &::= \top \mid \bot \\
&\mid \Psi \vdash M = N : C &&\text{unify term } M \text{ with } N \\
&\mid \Psi \mid R{:}A \vdash E = E' &&\text{unify evaluation context } E \text{ with } E' \\
&\mid \Psi \vdash u \leftarrow M : C &&\text{solution for } u \text{ found} \\[4pt]
\text{Constraint sets} \quad \mathcal K &::= K \mid \mathcal K \wedge \mathcal K \quad \text{(modulo laws of conjunction)}
\end{aligned}
$$

Four things are worth pulling apart here, since the book states them tersely:

- **$\top$ and $\bot$** are the two "done" states for a single constraint — trivially true, or provably inconsistent. A whole unification problem fails the moment any conjunct reaches $\bot$.
- **$\Psi \vdash M = N : C$** is the workhorse case: a term equation, annotated with its type. The type annotation is *not* decorative — it's load-bearing for two independent reasons. First, [[The-lambda-Pi-Sigma-Calculus-with-Meta-Variables#Hereditary substitution|hereditary substitution]] (the substitution discipline from Chapter 2 that keeps terms $\beta$-normal as you go) needs to know the type to know how to resolve a newly-created redex. Second, eliminating $\Sigma$-types via the type-isomorphism machinery (the previous topic in this book) needs the type of the *context*, not just the term, to know where a projection can be split into two variables. The paper notes it could get away with dependency-*erased* simple types for both purposes, but keeps full dependent types in the presentation so the same technique scales to systems (like Agda) where types can't be erased.
- **$\Psi \mid R{:}A \vdash E = E'$** is a bookkeeping constraint, not a "real" one from the user's point of view — it's the intermediate form produced when you're partway through decomposing a neutral term $E[R]$ against $E'[R']$ and want to compare the surrounding evaluation contexts (the spine of applications and projections) once the heads have already been checked equal. Its meaning unfolds back to $\Psi \vdash E[R] = E[R'] : C$ where $C$ is $E[R]$'s inferred type.
- **$\Psi \vdash u \leftarrow M : C$** *is* a solution, not a request for one — it records that meta-variable $u$ has been assigned the term $M$.

That last constraint form is what makes the notion of **solved vs. active** meta-variable precise: $u$ is *solved* if some constraint $\Psi \vdash u \leftarrow M : C$ exists in the current set; otherwise it's *active*. Crucially, the paper enforces an invariant that keeps this a clean partition rather than a running tally: **a solved meta-variable never appears anywhere else** — not in any other constraint, not in the type of any other meta-variable in $\Delta$, not even in its own solution $M$. This isn't a passive bookkeeping fact; it's actively *maintained* by how instantiation works (see "Solving a meta-variable, precisely" below) — the moment $u$ gets a solution, that solution is substituted everywhere $u$ occurred, so $u$ vanishes from the live problem rather than lingering as a symbol you have to keep dereferencing.

```mermaid
flowchart LR
    A["Ψ ⊢ M = N : C\n(term equation)"] -->|decomposition| B["smaller term/context\nequations"]
    B -->|η-contraction| C["u[σ] with σ closer\nto a variable list"]
    C -->|lowering /\nflattening Σ| D["u split into\nsimpler meta-variables"]
    D -->|pruning + inversion\n(next topics)| E["Ψ ⊢ u[ρ] = M : C\nρ a variable substitution"]
    E -->|solve| F["Ψ ⊢ u ← M′ : C\n(u now SOLVED,\nsubstituted away everywhere)"]
    style F fill:#2f6f4f,stroke:#7fae95,color:#ffffff
```

**Rust grounding.** This grammar translates almost verbatim into a Rust enum, and the exercise of writing it out is clarifying about what the "solved" invariant actually demands of an implementation:

```rust
enum Constraint {
    Top,
    Bot,
    TermEq   { ctx: Ctx, lhs: Term, rhs: Term, ty: Type },
    SpineEq  { ctx: Ctx, head: Term, head_ty: Type, lhs: Spine, rhs: Spine },
    Solved   { ctx: Ctx, meta: MetaId, term: Term, ty: Type },
}

// A meta-variable's status is NOT a field you toggle in place —
// it's derived from whether a `Solved` constraint mentioning it exists.
// Maintaining "solved metas don't occur elsewhere" means: the moment you
// produce a `Solved` constraint for `u`, you must walk every other live
// constraint and every other meta's type and substitute `u` away —
// exactly what the book calls meta-substitution [[θ]].
struct ConstraintSet(Vec<Constraint>);

fn instantiate(meta_ctx: &mut MetaCtx, set: &mut ConstraintSet, u: MetaId, solution: Term) {
    let theta = MetaSubst::singleton(u, solution);
    meta_ctx.apply(&theta);   // [[θ]]Δ
    set.apply(&theta);        // [[θ]]K
    // the Solved constraint itself is what records u ↦ solution from now on
}
```

The temptation in a naive implementation is to give `MetaId` a mutable `Option<Term>` cell and call `.set()` on it — a union-find-style approach. The book's presentation deliberately avoids that: because meta-substitution is global and eager (every occurrence is rewritten out immediately), there's never a "look up what `u` currently points to" step anywhere in the algorithm. That's a real design choice with a real cost/benefit: it keeps every later correctness lemma about "transitions preserve X" simple to state (X holds of the *whole* new state, not X holds *after dereferencing*), at the cost of doing more rewriting work per step than a mutable-cell union-find would.

## 3.1 Typing modulo: giving up well-typedness on purpose

The fix for the pair-decomposition problem above is to relax *every* typing judgment defined in Chapter 2 so that it checks equality **modulo the current constraint set** instead of modulo strict $\eta$-equality. Formally: for every judgment $\Delta; \Psi \vdash J$, define $\Delta; \Psi \vdash_{\mathcal K} J$ by the identical rules, except every place the original rules invoked $\eta$-equality ($A =_\eta C$), the modulo version invokes $=_{\mathcal K}$ instead, where

$$
\alpha =_{\mathcal K} \beta \iff \llbracket\theta\rrbracket\alpha =_\eta \llbracket\theta\rrbracket\beta \text{ for every ground solution } \theta \text{ of } \mathcal K.
$$

Read this the way the authors intend it to be read: *"if we can solve $\mathcal K$, we can establish that $\alpha$ equals $\beta$."* Typing modulo doesn't claim $\alpha$ and $\beta$ are equal right now — it defers that claim to whatever future point the surrounding constraints get solved, and lets the algorithm proceed on the promissory note. Go back to the pair example: the second constraint $\Psi \vdash M = N : P\,u[x]$ is only well-typed modulo $\mathcal K = \{u[x] = u[\mathrm{true}] : A\}$ — i.e., typing modulo is precisely the mechanism that makes the decomposition step legal.

A well-formed unification problem $\Delta \gg \mathcal K$ is then one where $\Delta \vdash_{\mathcal K} \mathrm{mctx}$ and every term-equation constraint is well-typed *modulo $\mathcal K$ itself* — the constraint set is, in effect, typing-checking its own future.

**Why this doesn't collapse into nonsense.** The obvious worry is that if you're allowed to assume anything you haven't proven yet, the whole system becomes unsound — you could "solve" an unsolvable problem by assuming the very equality you need. Three lemmas close this gap:

- **Lemma 3.1 (Conversion modulo).** If $\Delta' \gg \mathcal K$ and $\Delta =_{\mathcal K} \Delta'$, $\Psi =_{\mathcal K} \Phi$, $A =_{\mathcal K} B$, then typing modulo $\mathcal K$ is preserved when you swap equal-modulo-$\mathcal K$ contexts and types for each other — for checking judgments, inference judgments, and substitution judgments alike. In other words, $=_{\mathcal K}$ behaves like a genuine congruence for the purposes of the modulo typing system, not just a syntactic label.
- **Lemma 3.2 (Substitution principle modulo).** The ordinary substitution lemma (substituting a well-typed term for a variable preserves typing) still holds when everything is relativized to $\mathcal K$ and to equality-modulo-$\mathcal K$ between the substituted type and its target.
- **Lemma 3.3 (Meta-substitution principle modulo).** This is the one that matters operationally: it says that applying a *meta*-substitution $\llbracket\theta\rrbracket$ (i.e., actually solving some meta-variables) to a derivation that was only valid modulo $\mathcal K$ produces a derivation valid modulo $\llbracket\theta\rrbracket\mathcal K$ — the *residual* constraint set after $\theta$ has been applied. This is exactly the guarantee the algorithm needs: every time it instantiates a meta-variable (see the `instantiate` sketch above), the typing-modulo invariant it was relying on doesn't evaporate, it just gets carried forward onto the smaller constraint set.

Put together, these three lemmas are the reason "typing modulo constraints" is a *sound deferral*, not a hole in the type system: nothing is ever accepted as equal without eventually cashing out — via a ground solution $\theta$ — as genuinely $\eta$-equal. The algorithm is allowed to work with IOUs; the lemmas guarantee every IOU is eventually payable.

**Lean grounding — this is exactly Lean's elaboration discipline.** If you've used Lean, you've already lived inside typing modulo constraints without necessarily naming it. Lean's elaborator routinely typechecks a subterm against a type containing *unassigned* metavariables — e.g. elaborating `⟨a, b⟩ : Σ x, P x` before the metavariable standing for `x` in `P x` is pinned down — and `isDefEq` will happily succeed by *assigning* a metavariable rather than by finding the two sides already syntactically equal. That assignment is Lean's analogue of a ground solution $\theta$: Lean is provisionally treating two terms as equal because it can see a metavariable assignment that would make them equal, exactly the "if we can solve $\mathcal K$, we can establish $\alpha =\beta$" reading above. The place this cashes out is `MetavarContext` bookkeeping (`instantiateMVars`) — once metavariables get assigned, every place that held the metavariable is updated, matching the paper's insistence that meta-substitution be applied *globally* rather than looked up lazily. The paper's Lemma 3.3 is, informally, the correctness argument Lean's implementers have to believe is true (even if they don't write it as a lemma) every time `isDefEq` is allowed to succeed by side-effecting the metacontext instead of by direct comparison.

## 3.2 The unification algorithm proper: local simplification

With typing modulo in hand, the algorithm is presented (Fig. 3 / Fig. 4 in the paper) as two families of rewrite rules on a unification problem $\Delta \gg \mathcal K$. This topic covers the first family — **local simplification**, written $\mathcal K \mapsto_m \mathcal K'$ for $m \in \{d, e, p\}$ (decomposition, $\eta$-contraction, projection-elimination) — which acts on one constraint at a time without touching $\Delta$. (The second family — lowering, $\Sigma$-flattening, pruning, same-meta-variable, solving — is meta-variable-directed and gets its own treatment; pruning specifically is deep enough to be its own topic later in this book. Lowering is covered here since it belongs to the same "expose more pattern structure" story as decomposition.)

### Decomposition ($\mapsto_d$)

Decomposition breaks a structural equation into equations between its immediate parts — the syntax-directed half of unification that would be uncontroversial in a simply-typed setting too, except here every step carries dependent-type bookkeeping:

$$
\begin{aligned}
\Psi \vdash \lambda x.M = \lambda x.N : \Pi x{:}A.B &\mapsto_d \Psi, x{:}A \vdash M = N : B \\
\Psi \vdash \lambda x.M = R : \Pi x{:}A.B &\mapsto_d \Psi, x{:}A \vdash M = R\,x : B \\
\Psi \vdash R = \lambda x.M : \Pi x{:}A.B &\mapsto_d \Psi, x{:}A \vdash R\,x = M : B
\end{aligned}
$$

The second and third rules are worth pausing on: they're $\eta$-expansion, applied *asymmetrically*, purely to keep both sides of the equation in the same shape (a $\lambda$) before recursing under the binder. This is a recurring pattern in this whole algorithm — when the two sides disagree in shape but one side's shape is "richer," push the other side into that shape rather than trying to compare across shapes.

The pair rules are the direct $\Sigma$-analogue (three symmetric cases: both pairs, pair-vs-neutral via `fst`/`snd`, neutral-vs-pair):

$$
\begin{aligned}
\Psi \vdash (M_1, M_2) = (N_1, N_2) : \Sigma x{:}A.B &\mapsto_d \Psi \vdash M_1 = N_1 : A \;\wedge\; \Psi \vdash M_2 = N_2 : [M_1/x]B \\
\Psi \vdash (M_1, M_2) = R : \Sigma x{:}A.B &\mapsto_d \Psi \vdash M_1 = \mathrm{fst}\,R : A \;\wedge\; \Psi \vdash M_2 = \mathrm{snd}\,R : [M_1/x]B
\end{aligned}
$$

and neutral terms decompose head-first via evaluation contexts:

$$
\begin{aligned}
\Psi \vdash E[H] = E'[H] : C &\mapsto_d \Psi \mid H{:}A \vdash E = E' &&\text{where } \Psi \vdash H \Rightarrow A \\
\Psi \vdash E[H] = E'[H'] : C &\mapsto_d \bot &&\text{if } H \neq H'
\end{aligned}
$$

— i.e., two neutrals can only possibly unify if they share the same *rigid head* $H$ (a variable or constant, never a meta-variable at this point), and if the heads differ, unification fails immediately: no substitution for any meta-variable can change what a rigid head is. This is where "rigid" occurrences (from the previous topic's vocabulary) start doing real work — a rigid mismatch is a hard failure, not something to postpone.

**What breaks without decomposing pairs the "obvious" way.** The book flags a tempting shortcut: define pair-decomposition uniformly for *any* $\Sigma$-typed equation (not just literal pairs) as $\mathrm{fst}@M = \mathrm{fst}@N \wedge \mathrm{snd}@M = \mathrm{snd}@N$ (where $\pi@M$ means "compute the $\beta$-normal form of $\pi\,M$"). This is more concise, but it would also apply to two *neutral* terms $R = R'$ of $\Sigma$-type, duplicating work that the neutral-decomposition rule above is already going to do once the heads are compared — the projections would get pushed in, then the neutral-decomposition rule would immediately push them right back out through the evaluation-context machinery. The three-case split exists to avoid this redundant round-trip, not out of formal necessity.

**Orientation.** One more local-simplification rule, easy to miss because it looks trivial: if a constraint has a meta-variable application on the right but not the left, flip it:
$$
\Psi \vdash M = u[\sigma] : C \quad \text{with } M \neq v[\ldots] \quad \mapsto_d \quad \Psi \vdash u[\sigma] = M : C.
$$
This is pure bookkeeping, but it's the reason every other rule in the system only needs to be stated with the meta-variable on the left — orientation is what guarantees that canonical form actually holds by the time those rules fire.

### $\eta$-contraction ($\mapsto_e$)

Local simplification can also fire *inside* a meta-variable's suspended substitution $\sigma$, contracting an $\eta$-expanded subterm back to its head:
$$
\Psi \vdash u[\sigma\{\lambda x.\, R\,x\}] = N : C \;\mapsto_e\; \Psi \vdash u[\sigma\{R\}] = N : C, \qquad
\Psi \vdash u[\sigma\{(\mathrm{fst}\,R, \mathrm{snd}\,R)\}] = N : C \;\mapsto_e\; \Psi \vdash u[\sigma\{R\}] = N : C.
$$
The point of this rule is entirely about getting $\sigma$ into **pattern shape** — recall from the previous topic that Miller's decidable fragment requires every meta-variable to be applied to a list of *distinct bound variables*, nothing more elaborate. A substitution entry that's an $\eta$-expanded variable, $\lambda x. y\,x$, is semantically just $y$, but syntactically it's not a bare variable — it's a whole lambda term sitting where the pattern discipline wants a variable. $\eta$-contraction is the rule that notices this and cleans it up, one entry at a time, without needing a separate global normalization pass.

Worked example straight from the text: $u[\lambda x.\, y\,(\mathrm{fst}\,x, \mathrm{snd}\,x)] = M$ contracts (using the pair-contraction rule, since $(\mathrm{fst}\,x,\mathrm{snd}\,x)$ is the $\eta$-expansion of $x$ at $\Sigma$-type) to $u[y] = M$ — suddenly a pattern equation, solvable directly, where the original looked hopelessly non-pattern.

*(The third local-simplification rule, projection elimination via the $\Sigma\!\to\!\Pi$ type isomorphism, is the mechanism this book's previous topic covers in depth — it's listed in Fig. 3 alongside decomposition and $\eta$-contraction because it's syntactically a "local" rewrite, but its justification is the isomorphism itself, not anything new here.)*

### Lowering: manufacturing pattern shape by weakening the meta-variable's type

Sometimes no amount of decomposition or $\eta$-contraction exposes pattern structure, because the meta-variable's *type* is still too rich. **Lowering** attacks this by replacing an active meta-variable of function or pair type with a fresh meta-variable (or pair of meta-variables) at the smaller codomain/component type:

$$
\begin{aligned}
u : (\Pi x{:}A.B)[\Phi] \in \Delta \text{ active} \quad &\mapsto\quad \Delta, v{:}B[\Phi, x{:}A] \gg \mathcal K + \Phi \vdash u \leftarrow \lambda x. v : \Pi x{:}A.B \\
u : (\Sigma x{:}A.B)[\Phi] \in \Delta \text{ active} \quad &\mapsto\quad \Delta, u_1{:}A[\Phi],\, u_2{:}([u_1[\mathrm{wk}_\Phi]/x]B)[\Phi] \gg \mathcal K + \Phi \vdash u \leftarrow (u_1[\mathrm{wk}_\Phi], u_2[\mathrm{wk}_\Phi]) : \Sigma x{:}A.B
\end{aligned}
$$

The worked example makes the necessity concrete: take $\Phi = (y{:}\Sigma x{:}A.B)$, $u : (\Sigma x{:}A.B)[\Phi]$, and the constraint $\Phi \vdash \mathrm{fst}(u[y]) = \mathrm{fst}\,y$. You *cannot* just decompose this into $u[y] = y$ — that would additionally force the second components equal, which the original constraint (which only mentions `fst`) never demanded, and you'd be silently discarding solutions. Instead, lowering first splits $u$ into a pair of smaller meta-variables $u_1 : A[\Phi]$ and $u_2 : ([u_1[y]/x]B)[\Phi]$, turning the original problem into $\Phi \vdash u_1[y] = \mathrm{fst}\,y$ — now a constraint that only pins down the piece the original equation actually constrained. This is the general moral of lowering: **it trades one meta-variable of rich type for several of simpler type**, preserving exactly the degrees of freedom the constraints imply and no more.

### Solving a meta-variable, precisely: the instantiation notation

Fig. 4 defines shorthand for what "instantiate $u$ with $M$" means as an operation on the *entire* problem state, not just a local edit:
$$
\Delta \gg \mathcal K + (\Phi \vdash u \leftarrow M : A) \;=\; \llbracket\theta\rrbracket\Delta \gg \llbracket\theta\rrbracket\mathcal K \wedge \llbracket\theta\rrbracket\Phi \vdash u \leftarrow M : \llbracket\theta\rrbracket A, \qquad \theta = \hat\Phi.M/u.
$$
Read the right-hand side carefully: instantiating $u$ doesn't just add a `Solved` constraint — it meta-substitutes $u \mapsto M$ through the *whole* remaining meta-context $\Delta$ and the *whole* remaining constraint set $\mathcal K$ first, and only then appends the record of the solution. This is precisely the global-rewrite discipline flagged in the Rust sketch above, and it's what makes "a solved meta-variable never occurs elsewhere" true by construction rather than something you have to separately check.

## Worked examples that motivate the whole apparatus (pp. 10–12)

The paper walks through a sequence of small examples specifically chosen to sit *outside* the plain Miller pattern fragment, to show why each rule earns its place:

- **$\eta$-contraction:** $u[\lambda x.\, y\,(\mathrm{fst}\,x,\mathrm{snd}\,x)] = M$ solves by contracting the left-hand side to $u[y]$ (shown above).
- **[[Type-Isomorphisms-for-Dependent-Records#Eliminating projections|Eliminating projections]]:** given $y : \Pi x{:}A. \Sigma z{:}B.C$ and $u[\lambda x.\,\mathrm{fst}(y\,x)] = M$, applying the type-isomorphism substitution $\tau = [\lambda x.(y_1\,x, y_2\,x)/y]$ splits $y$ into two functions $y_1, y_2$, reduces the goal to $u[\lambda x.\, y_1\,x] = [\tau]M$, and then $\eta$-contraction finishes the job to $u[y_1] = [\tau]M$ — solvable provided $y_2$ doesn't occur free in $[\tau]M$.
- **Non-linearity that's still solvable:** $u[x,x,z] = \mathrm{suc}\,z$ has a non-linear occurrence of $x$ on the left, but since $x$ doesn't occur on the right at all, it can simply be ignored: $u[x,y,z] = \mathrm{suc}\,z$ is a valid pattern solution.
- **Non-linearity that breaks well-typedness, not just pattern-hood:** with $u : (P\,z)[\Phi]$, $\Phi = (x{:}A, y{:}P\,x, z{:}A)$, and constraint $x{:}A, y{:}P\,x \vdash u[x,y,x] = y : P\,x$, the naive non-linear-elimination solution $u \leftarrow y$ is *ill-typed* — $y$'s type mentions $x$, which the non-linear substitution $[x,y,x]$ was the only thing keeping in scope for $u$'s domain. The paper's honest conclusion: this constraint is left alone as unsolvable-by-this-algorithm, rather than flagged as definitively unsolvable (a richer type theory with casts could conceivably do better).

*(The remaining worked examples in this stretch of the paper — pruning $v[x,y]$ down to $v'[x]$, the nested-meta-variable case that pruning can't handle, same-meta-variable unification, and the two failing-occurs-check examples — belong to the next topic in this book, which covers [[Pruning-and-the-Occurs-Check|pruning and the occurs check]] in depth.)*

## Where this leads

Structurally, this topic is the hinge of the whole paper: everything in Chapter 2 (the calculus, contextual meta-variables, rigid/flexible occurrences) exists to make these rewrite rules statable, and everything from here to the end of Chapter 3 — pruning, [[Inverting-Substitutions|inverting substitutions]], same-meta-variable unification — is *more* meta-variable-directed machinery bolted onto exactly this same rewrite-relation-on-constraint-sets framework. Chapter 4's correctness proof (termination, solution-preservation, type-preservation) is proved rule-by-rule against precisely the $\mapsto_d$, $\mapsto_e$, lowering, and instantiation definitions given here — none of that proof is possible without first having carved the algorithm into small, individually-checkable steps the way this chapter does.

For the standing project (a Rust elaborator with a Miller-pattern-style metavariable unifier, under `automated-reasoning`): this chapter *is* the blueprint for the unifier's main loop, not just background theory. The concrete architectural commitments worth carrying forward directly are: (1) represent unification state as an explicit, inspectable constraint set rather than hiding it inside a recursive call stack — this is what makes postponement (deferring a constraint you can't yet solve) a normal code path instead of a special case; (2) typing modulo constraints is the same trick Lean's elaborator leans on constantly via its metavariable-assignment discipline in `isDefEq`, so building the Rust unifier around a `ConstraintSet` + eager global meta-substitution (rather than a mutable union-find) is a deliberate, well-precedented design choice, not a naive one; (3) orientation and $\eta$-contraction are cheap, purely-local normalization passes worth running greedily before ever reaching for the heavier machinery (lowering, and — coming next — pruning), which mirrors how a real elaborator budgets its unification effort.
