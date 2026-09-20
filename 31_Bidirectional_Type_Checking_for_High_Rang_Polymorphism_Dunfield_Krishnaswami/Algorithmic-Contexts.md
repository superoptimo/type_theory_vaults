---
title: Algorithmic Contexts
source: "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism (Dunfield & Krishnaswami)"
chapter: "Section 3.1, pp. 5–6"
tags: [type-theory, bidirectional-typechecking, elaboration, unification, rust]
---

[[book-guidelines|↩ Back to guidelines]]

# Algorithmic Contexts

## The problem: guessing isn't an algorithm

The declarative system from Section 2 is a beautiful *specification*, but it's not implementable as written. Three of its rules require an oracle: $\mathrm{Decl}{\forall}\mathrm{App}$ and $\mathrm{Decl}{\to}I{\Rightarrow}$ ask you to "just pick" a type — an instantiation for a quantifier, or a monotype to check a lambda against — and the subtyping rule $\le\!\forall L$ has the identical problem. A specification is allowed to say "there exists a $\tau$ such that…"; a typechecker has to *find* that $\tau$, and it has to do so by inspecting the term and its neighbors, not by magic.

The standard move — familiar from Hindley-Milner — is to defer the choice: instead of guessing a type on the spot, introduce a placeholder, a **unification variable**, and solve it later once enough information has arrived from the surrounding context. The paper calls these placeholders **existential type variables**, written $\hat\alpha, \hat\beta, \ldots$, and the whole point of Section 3.1 is that they are *not* the free-floating global unification variables of classic Hindley-Milner. If they were, you'd immediately have a scoping bug: nothing would stop $\hat\alpha$ from being solved to a type that mentions a universal variable $\alpha$ declared *after* $\hat\alpha$ was created — a variable that, semantically, doesn't exist yet at the point $\hat\alpha$ was introduced.

**What breaks without ordering:** imagine checking `id : ∀α. α → α` against a use site, and along the way you spawn `α̂` to stand in for the unknown argument type. If nothing enforces that `α̂`'s eventual solution can only mention variables declared *before* `α̂`, you could end up "solving" `α̂` to something that refers to a variable local to a sibling branch of the derivation — a variable that will have gone out of scope by the time you actually need `α̂`'s value. The fix the paper adopts is to make the *context itself* ordered, and to make well-formedness police that order on every declaration, existential solutions included.

## The context as a single ordered sequence

An algorithmic context $\Gamma$ (the paper also uses $\Delta$ and $\Theta$ for the same sort of object) is one linear sequence — not three separate maps for term variables, type variables, and metavariables, but one list where position matters. From Figure 6:

$$
\Gamma, \Delta, \Theta ::= \cdot \mid \Gamma, \alpha \mid \Gamma, x{:}A \mid \Gamma, \hat\alpha \mid \Gamma, \hat\alpha = \tau \mid \Gamma, \mathrm{I}_{\hat\alpha}
$$

Five kinds of entries can appear, left to right, in one context:

- $\alpha$ — a universal type variable in scope (a rigid, "real" type variable — the kind you'd get under a $\forall$-binder).
- $x : A$ — a term variable's type, exactly like a declarative context.
- $\hat\alpha$ — an **unsolved** existential variable: "there will be a monotype here, we don't know it yet."
- $\hat\alpha = \tau$ — a **solved** existential variable: $\hat\alpha$'s value has been pinned down to monotype $\tau$.
- $\mathrm{I}_{\hat\alpha}$ — a bare scope **marker**, carrying no information beyond "this is the point where $\hat\alpha$ was introduced." (This becomes essential once you reach [[Algorithmic-Subtyping-and-Instantiation|algorithmic subtyping and instantiation]] — it's how the rules know how much of the context to discard when leaving a scope.)

Crucially, $\hat\alpha$ and $\hat\alpha = \tau$ are the *same slot* at two different moments — unsolved is a variable's "not yet decided" state, solved is its "decided" state — and the entry mutates in place from one to the other as the algorithm runs. This is exactly the lifecycle of a mutable unification cell, except here the cell's *position* in the sequence is itself meaningful data, not an implementation accident.

**Well-formedness as an ordering discipline.** Figure 7's context rules (`UvarCtx`, `VarCtx`, `EvarCtx`, `SolvedEvarCtx`, `MarkerCtx`) all share a shape: each new entry may only be well-formed if everything it depends on already appears to its *left*. Concretely: if $\Gamma = (\Gamma_L, x{:}A, \Gamma_R)$, then $A$ must be well-formed under $\Gamma_L$ alone — it cannot mention any $\alpha$ or $\hat\alpha$ declared in $\Gamma_R$. The same rule applies to a solved existential's payload: if $\Gamma = (\Gamma_L, \hat\alpha = \tau, \Gamma_R)$, then $\tau$ must be well-formed under $\Gamma_L$. This single discipline is what rules out circularity — $(\hat\alpha = \hat\beta, \hat\beta = \hat\alpha)$ is simply not a well-formed context, because whichever one comes second would have to refer to something not yet declared.

## Rust grounding: the context as a `Vec` of entries

This maps almost embarrassingly directly onto a Rust data structure, and it's worth building because it *is* the metavariable-context data structure your own elaborator will need. Model the context as a `Vec<CtxEntry>` — order in the vector *is* the ordering the paper's well-formedness rules are policing:

```rust
#[derive(Clone, Debug)]
enum Monotype {
    Unit,
    Var(String),            // rigid universal, α
    Exist(u32),              // reference to an existential by id
    Arrow(Box<Monotype>, Box<Monotype>),
}

#[derive(Clone, Debug)]
enum Type {
    Unit,
    Var(String),
    Exist(u32),
    Arrow(Box<Type>, Box<Type>),
    Forall(String, Box<Type>),
}

#[derive(Clone, Debug)]
enum CtxEntry {
    Uvar(String),                 // Γ, α
    Var(String, Type),            // Γ, x : A
    Exist(u32),                   // Γ, α̂        (unsolved)
    SolvedExist(u32, Monotype),   // Γ, α̂ = τ    (solved)
    Marker(u32),                  // Γ, I_α̂
}

struct Context {
    entries: Vec<CtxEntry>,
}
```

The unsolved/solved distinction is exactly `CtxEntry::Exist` vs. `CtxEntry::SolvedExist` — two variants of one conceptual slot, just as the paper's notation ($\hat\alpha$ vs. $\hat\alpha = \tau$) treats them as the same declaration at two moments. "Solving" a variable is a targeted, in-place mutation:

```rust
impl Context {
    fn solve(&mut self, id: u32, tau: Monotype) {
        for entry in self.entries.iter_mut() {
            if let CtxEntry::Exist(existing_id) = entry {
                if *existing_id == id {
                    *entry = CtxEntry::SolvedExist(id, tau);
                    return;
                }
            }
        }
        panic!("solve: {id} not found unsolved in context");
    }
}
```

Well-formedness-as-ordering becomes a straightforward invariant: a `Type` is well-formed under a prefix of the `Vec` iff every `Exist`/`Var`/`Uvar` name it mentions already occurs as an entry *before* the current write position. If you enforce this invariant at every insertion point (rather than only checking it lazily), you get the paper's non-circularity guarantee for free — you simply cannot construct a `SolvedExist` whose `Monotype` payload references an id that hasn't appeared yet in the vector.

## Context application: reading out the "current best" substitution

A context isn't just bookkeeping — Figure 8 shows it doubles as a **substitution**. Since some existentials are solved and some aren't, "applying" $\Gamma$ to a type $A$, written $[\Gamma]A$, means: walk $A$, and wherever you hit a solved existential, replace it by its solution (which may *itself* contain other existentials solved earlier — hence the recursive case $[\Gamma][\hat\alpha = \tau]\hat\alpha = [\Gamma, \hat\alpha=\tau]\tau$ chases the chain), while leaving unsolved existentials and universal variables untouched.

$$
[\Gamma]\alpha = \alpha \qquad [\Gamma]1 = 1 \qquad [\Gamma, \hat\alpha][\hat\alpha] = \hat\alpha \qquad [\Gamma, \hat\alpha=\tau][\hat\alpha] = [\Gamma,\hat\alpha=\tau]\tau
$$
$$
[\Gamma](A\to B) = ([\Gamma]A)\to([\Gamma]B) \qquad [\Gamma](\forall\alpha. A) = \forall\alpha.\,[\Gamma]A
$$

Concretely, the worked example from the paper: given $\Gamma = (\hat\alpha = 1,\; \hat\beta = \hat\alpha \to 1)$, applying $\Gamma$ is exactly applying the simultaneous substitution $1/\hat\alpha,\ (1\to 1)/\hat\beta$ — you have to substitute $\hat\alpha$'s solution into $\hat\beta$'s solution too, because $\hat\beta$'s stored payload still literally contains $\hat\alpha$.

```rust
impl Context {
    fn apply_ty(&self, ty: &Type) -> Type {
        match ty {
            Type::Unit | Type::Var(_) => ty.clone(),
            Type::Exist(id) => match self.lookup_solution(*id) {
                Some(mono) => self.apply_ty(&mono.to_type()), // recurse: chase solved chains
                None => ty.clone(),                            // still unsolved — leave as-is
            },
            Type::Arrow(a, b) => Type::Arrow(
                Box::new(self.apply_ty(a)),
                Box::new(self.apply_ty(b)),
            ),
            Type::Forall(name, body) => Type::Forall(name.clone(), Box::new(self.apply_ty(body))),
        }
    }
}
```

This `apply_ty` is precisely what a real elaborator calls "zonking" — walking a term or type and eagerly substituting away every metavariable that currently has a known solution, producing the "fully resolved as of right now" view. It's not idempotent-free-of-cost: because solutions can chain, you may re-walk the same solved existential's payload many times across a derivation, which is one reason real implementations often cache or path-compress.

## Complete contexts: when there's nothing left to chase

A **complete context** $\Omega$ (also in Figure 6, using the same grammar minus the unsolved-existential case) is a context with *no* unsolved variables — every existential it declares is already solved. The paper singles this out because it's exactly the condition under which $[\Omega]A$ (provided $\Omega \vdash A$ is well-formed) produces a type with *zero* existentials left in it — a genuinely finished type, not a snapshot mid-inference. Complete contexts don't show up as a separate case in any of the algorithmic rules themselves; they exist purely as a proof device, the target state that soundness and completeness theorems reason about ("if you complete the algorithm's leftover unsolved variables somehow, you get back a valid declarative derivation"). In Rust terms, a complete context is just a runtime assertion: `entries.iter().all(|e| !matches!(e, CtxEntry::Exist(_)))` — a fact you'd check to justify emitting final, existential-free types out of your elaborator, not a distinct type you'd necessarily encode in the type system (though you certainly could, with a `PhantomData`-tagged wrapper, if you wanted the compiler to enforce it).

## Hole notation: naming the "middle" of a context

Because the algorithm doesn't just append to the end of the context (as the purely additive declarative system does) — it inserts and rewrites declarations *in the middle*, e.g. turning an unsolved $\hat\alpha$ into $\hat\alpha = \tau$ wherever $\hat\alpha$ happens to live — the paper needs a way to talk about "the context with a hole at some interior position." It writes

$$
\Gamma = \Gamma_0[\Theta] \quad\text{meaning}\quad \Gamma = (\Gamma_L, \Theta, \Gamma_R)
$$

i.e., $\Gamma_0[\cdot]$ is a context with a slot, and plugging $\Theta$ into that slot reproduces $\Gamma$. This lets rules state things like "find the entry $\hat\beta$ somewhere in the middle of $\Gamma$, and rewrite that one entry to $\hat\beta = \hat\alpha$, leaving everything to its left and right untouched" — precisely the worked example in the text: if $\Gamma = \Gamma_0[\hat\beta] = (\hat\alpha, \hat\beta, x{:}\hat\beta)$, then $\Gamma_0[\hat\beta = \hat\alpha] = (\hat\alpha, \hat\beta = \hat\alpha, x{:}\hat\beta)$ — same $\Gamma_L$, same $\Gamma_R$, only the plugged-in piece changed. Occasionally two independent interior positions need naming at once, giving two-hole notation $\Gamma = \Gamma_0[\Theta_1][\Theta_2]$, meaning $\Gamma = (\Gamma_L, \Theta_1, \Gamma_M, \Theta_2, \Gamma_R)$.

This is purely a *metatheoretic* notation for writing rules on paper — it's how the rules stay readable despite doing surgery on the interior of a list. In an implementation, it corresponds to nothing more exotic than indexing into your `Vec<CtxEntry>` and splicing at a computed position:

```rust
impl Context {
    /// Splits into (everything left of `pos`, everything right of `pos`),
    /// mirroring Γ = Γ_L, Θ, Γ_R with the hole located at `pos`.
    fn split_at(&self, pos: usize) -> (&[CtxEntry], &[CtxEntry]) {
        (&self.entries[..pos], &self.entries[pos + 1..])
    }
}
```

## Input and output contexts: threading state through the judgments

The declarative system had one context $\Psi$, read at every rule but never *changed* by a rule — checking, synthesis, and application all just consult $\Psi$. The algorithmic system can't get away with that, because the whole reason it exists is to *discover* solutions for existentials as it goes, and those discoveries have to be recorded somewhere for later premises (and later rule applications, elsewhere in the derivation) to see. So every algorithmic judgment takes an **input context** and produces an **output context**, written with a right-facing turnstile-and-dashv pair:

$$
\Gamma \vdash A <: B \dashv \Delta \qquad \Gamma \vdash e \Leftarrow A \dashv \Delta \qquad \Gamma \vdash e \Rightarrow A \dashv \Delta \qquad \Gamma \vdash A \bullet e \Rightarrow\!\!\Rightarrow C \dashv \Delta
$$

Read $\Gamma \vdash \mathcal{J} \dashv \Delta$ as: "starting from context $\Gamma$, judgment $\mathcal{J}$ holds, and along the way some existentials got solved, leaving output context $\Delta$." Concretely, comparing an unsolved existential against a concrete type solves it: $\hat\alpha <: \beta$ (with $\beta$ declared to the left of $\hat\alpha$, so the ordering discipline is respected) produces an output context where $\hat\alpha$'s unsolved declaration has been rewritten to $\hat\alpha = \beta$. Input contexts thus evolve into output contexts that are, in the paper's words, "more solved" — never less. (This "more solved / more information" relationship between an input and its resulting output is given a name and studied formally in Section 4 as **context extension**, $\Gamma \longrightarrow \Delta$ — everything in this section is the data structure that extension is a relation *over*.)

In Rust, this is the natural shape of a typechecking function: it doesn't just return a `Type`, it returns a `Type` *and* a possibly-mutated `Context` — or, more idiomatically, it takes `&mut Context` and mutates it in place as a side effect of walking the derivation, exactly like a Hindley-Milner unifier's `union` calls mutate a union-find structure as inference proceeds:

```rust
fn check(ctx: &mut Context, expr: &Expr, ty: &Type) -> Result<(), TypeError> {
    // ... on the way, may call ctx.solve(id, tau) for some existential id,
    // which mutates ctx in place — the "output context" the paper writes
    // explicitly is here just ctx's state after this call returns.
    todo!()
}
```

The paper's explicit-output-context style (rather than implicit mutation) is what makes the metatheory tractable to state and prove by induction — "the output context extends the input context" is a clean per-rule invariant precisely *because* $\Delta$ is a first-class thing every rule produces, not a hidden side effect. When you implement this in Rust for real, in-place mutation of a shared `&mut Context` is the pragmatic choice, but it's worth recognizing that you're taking on faith (or re-proving yourself, operationally) the invariant the paper states explicitly: every mutation only ever moves a variable from unsolved to solved, never removes a declaration or reorders the sequence.

## Where this leads

This section supplies the load-bearing data structure for everything that follows: Section 3.2's algorithmic subtyping and Section 3.3's instantiation judgment are essentially *procedures that walk types while mutating a `Context` of exactly this shape*, and Section 4's context-extension relation $\Gamma \longrightarrow \Delta$ formalizes the "always more solved, never less" invariant this section only states informally. If you're building the elaborator described in the standing project goals, this *is* your metavariable context: unsolved/solved existentials are metavariables pre- and post-unification, the ordering discipline is exactly what prevents a solved metavariable from escaping its scope (the same failure mode as "metavariable scope escape" in Lean's own elaborator), and context application ($[\Gamma]A$) is your zonking pass. The hole notation and input/output-context threading are the metatheoretic vocabulary for describing what your `&mut Context`-mutating unifier does at each step — worth keeping in mind once you get to proving *your* implementation sound against this specification, not just running it.
