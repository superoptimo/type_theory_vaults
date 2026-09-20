---
title: Elaborating inch into the Evidence Language
source: "Type Inference, Haskell and Dependent Types (Gundry, 2013)"
chapter: "Chapter 7, 'Producing the Evidence: Elaborating inch' (pp. 144–172)"
tags: [type-theory, automated-reasoning, elaboration, bidirectional-typing, metavariables, unification, subsumption, higher-rank-polymorphism, constraint-solving, dependent-case-analysis]
---

[[book-guidelines|↩ Back to guidelines]]

## Why a whole chapter just to compile `inch`

Every earlier chapter of the thesis builds machinery in isolation: Chapter 2's Hindley-Milner elaborator, Chapter 3's units-of-measure unifier, Chapter 4's [[Miller-Pattern-Unification|Miller pattern unification]], Chapter 6's evidence language with its $\Pi$-types and phase distinction. Chapter 7 is where these stop being separate exercises and become one working compiler pass: turning `inch` source (Chapter 5's Haskell-with-$\Pi$-types) into well-typed terms of [[The-Evidence-Language|the evidence language]] (Chapter 6). This is the thesis's proof of concept — if contextual problem-solving *actually* scales to a full-spectrum dependently typed elaborator, this chapter is where that claim gets cashed out.

The problem elaboration solves here is sharper than in Chapter 2. There, Algorithm W just needed to find *a* type; producing the explicit System F term was almost a bookkeeping exercise once the type was known. Here, three things conspire to make elaboration genuinely hard:

1. **Higher-rank types** mean an inferred type and an expected type can be related by more than substitution — sometimes you need to *insert code* (implicit abstractions and applications) to bridge them, not just unify.
2. **Dependent types** mean the elaborator must synthesise not just type arguments but *proof terms* — coercions witnessing type equalities — and those proofs come from a full constraint-solving search, not a simple lookup.
3. **Fine-grained implicit/explicit control** (Chapter 5's departure from "types implicit, terms explicit") means the elaborator can no longer assume a fixed shape for which arguments are inserted automatically; that information has to travel with every function's declared type.

Gundry's answer, mirroring the structure of every earlier chapter: first write down a *non-deterministic specification* of what a correct elaboration looks like (a relation, not an algorithm — Section 7.3), then show how metavariables and contextual problem-solving turn that specification into an actual algorithm (Section 7.5), and finally extend both to handle `case`/`dcase` (Section 7.6) before discussing what got left out (Section 7.7).

## Type schemes: recording who's implicit and who's explicit

**What breaks without this.** Chapter 6's evidence language has ordinary $\Pi$- and $\forall$-quantified types, but a *type* alone doesn't say how to apply a function of that type — which arguments the elaborator should insert on its own, and which must come from the user's source text. Plain Hindley-Milner sidesteps this by fiat: Milner's original design makes type arguments always implicit and term arguments always explicit. `inch` deliberately breaks that coincidence (Chapter 5, §5.2.4) — you might want an implicit *term* argument (a typeclass-style dictionary) or an explicit *type* argument (to disambiguate a call site). So the elaborator needs a structure richer than a type to drive it.

That structure is a **type scheme** $\sigma$: a quantified type where every argument carries an annotation, $\mathtt{:i}$ (implicit) or $\mathtt{:e}$ (explicit):

$$\sigma ::= \tau \;\mid\; (a :^\Phi_e \sigma') \to \sigma \;\mid\; (a :^\Phi_i \tau) \to \sigma$$

For example, the type scheme of the equality type constructor is

$$(\sim) : (a :^\forall_i *,\, b :^\forall_i *,\, x :_e a,\, y :_e b) \to *$$

— the two type parameters are implicit, the two term-level equated values are explicit, which is exactly what justifies writing `x ~ y` as an infix operator without mentioning `a` and `b` at all. The vector-cons constructor scheme is denser still:

$$\mathrm{Cons} : (a :^\forall_i *,\, n :^\forall_i \mathbb{N},\, m :^\forall_i \mathbb{N},\, x :_e a,\, xs :_e \mathrm{Vec}\ a\ m,\, c :^\Pi_i\ n \sim \mathrm{Suc}\ m) \to \mathrm{Vec}\ a\ n$$

— five implicit arguments (three types/numbers, one coercion) surrounding two explicit ones (the head and tail), which is exactly the ergonomics you want from `Cons x xs` in source code.

Crucially, **schemes are not part of the evidence language's type system** — Gundry doesn't re-derive typing rules for annotated types. A scheme erases to an ordinary evidence type via $\lfloor \sigma \rfloor$ (Figure 7.1: the annotations are simply stripped, $(a:^\Phi_e \sigma') \to \sigma \mapsto (a:^\Phi \lfloor\sigma'\rfloor)\to\lfloor\sigma\rfloor$). Schemes exist purely to *drive elaboration* — to tell the algorithm which arguments to insert — and are discarded once the explicit evidence term is produced. This is a clean separation of concerns: the trusted kernel (the evidence language's type checker) never needs to know anything about implicit/explicit annotations; only the untrusted elaborator does.

One design discipline is worth flagging because it's exactly the kind of "what would go wrong without this" question a compiler engineer should ask: **the elaborator never guesses a type scheme**, only propagates schemes that are already known (from a variable's declared type, a constructor's signature, or an explicit ascription). This is why the domain of an implicit quantification in a scheme is always a bare *type*, never another *scheme* — if schemes could nest inside binders, the elaborator would need to *unify schemes*, and there's no principled notion of a most-general scheme the way there is a most-general type. Compare this to Rust's own choice not to infer higher-ranked/nested trait bounds automatically — you write them down once, and the compiler propagates rather than invents them.

**Rust grounding.** A type scheme is structurally a `Vec<(ArgMode, Type)>` paired with a result type, where `ArgMode` is:

```rust
enum ArgMode { Implicit, Explicit }

struct Scheme {
    params: Vec<(String, ArgMode, Type)>, // telescope, annotated
    result: Type,
}

fn erase(s: &Scheme) -> Type {
    // bσc : discard the ArgMode annotations entirely
    s.params.iter().rev().fold(s.result.clone(), |acc, (_, _, ty)| {
        Type::Arrow(Box::new(ty.clone()), Box::new(acc))
    })
}
```

This is precisely the shape of Rust's own const-generics-with-defaults or a hypothetical "which generics get turbofished" table — information that exists purely to guide *call-site elaboration* and never appears in the erased, monomorphized function signature the codegen backend sees.

## Non-determinism as a specification, not an algorithm

Before building an algorithm, Gundry writes down what a *correct* elaboration looks like — deliberately leaving open *how* the elaborator finds it. This is the same "specification first, algorithm second" discipline as Chapter 2's type system versus Algorithm W, except now the specification really does admit multiple, mutually incompatible correct answers. The central judgment (Figure 7.4) is:

$$\Gamma \vdash \rho \rightsquigarrow \rho :_\Psi \sigma$$

read as: "in context $\Gamma$, the `inch` expression $\rho$ (upright rho — source syntax) can be elaborated to the evidence term $\rho$ (italic, i.e. `ρ` in the evidence calculus) with scheme $\sigma$, at phase $\Psi$." Three auxiliary judgments round out the system: $\Gamma \vdash \delta \rightsquigarrow \delta : \Delta$ (elaborating an argument vector against a telescope, inserting implicit arguments), $\Gamma \vdash \sigma \rightsquigarrow \sigma$ (elaborating a source-level scheme annotation), and the subsumption judgment discussed below.

Gundry's own vocabulary for the rules is useful and worth keeping: **structural rules** preserve the shape of the source expression (a variable elaborates to a variable, an application to an application), while **wrapping rules** *add* information the source left implicit. The wrapping rules are where all the non-determinism lives. The canonical one is the "magic rule" for implicit $\lambda$-abstraction:

$$\dfrac{\Gamma, a:^\Phi_i \tau \vdash t \rightsquigarrow e : \sigma}{\Gamma \vdash t \rightsquigarrow \Lambda a:^\Phi \tau.\, e : (a:^\Phi_i \tau) \to \sigma}$$

Read the conclusion carefully: the *source* term $t$ appears unchanged on both sides, but the *target* term gained an entire implicit abstraction $\Lambda a$ that has no counterpart in the source at all. Nothing in the rule says *when* to apply it — a derivation could insert as many or as few implicit abstractions as it likes, wherever it likes, as long as the resulting scheme matches. The same freedom appears in the rule for the "unknown" marker `_` (which conjures *any* elaboration out of thin air, provided the erased types match) and the general conversion rule, which lets a coercion $\gamma$ silently retype a term. **This is genuinely under-determined**: Gundry gives the concrete example that `λx.λy.x y` can non-deterministically elaborate to at least three semantically different, mutually incompatible evidence terms depending on where implicit quantifiers get inserted — there is no principal or canonical choice at the level of the specification alone.

That non-determinism is the whole point of doing it this way: **Theorem 7.1 (Soundness of non-deterministic elaboration)** proves that *any* derivation the specification permits produces a well-typed evidence term (by straightforward structural induction, mirroring bΓc ⊢ ρ :Ψ bσc). So the specification pins down *correctness* completely while leaving *determinism* — i.e., which answer to actually compute — entirely to the algorithm built on top of it. This is the same relationship an operational-semantics-as-a-relation has to an interpreter-as-a-function: the relation tells you what a valid execution looks like; you still need to pick one.

**Lean grounding.** This is structurally identical to how Lean's own elaborator is often *described* even though it's implemented as one big deterministic function: the "elaboration relation" you'd write on paper (`Γ ⊢ e ⤳ e' : σ`) has multiple valid derivations for a term with metavariables in its type, and Lean's actual `elab` monad commits to one particular search order (roughly: try synthesizing instances and unifying metavariables eagerly, defer what can't be solved yet) to make it a function. The paper relation is the spec; `Elab.Term.elabTerm` is the (one possible) implementation.

## Subsumption: what higher-rank polymorphism actually costs the elaborator

**What breaks without this.** If every type were prenex-polymorphic (all quantifiers out front, Hindley-Milner style), "does this term have the expected type" would reduce to unification after instantiating quantifiers. Higher-rank types break that reduction. Gundry's example:

```
x :: ∀ a . Bool → a
y :: (∀ b . (∀ c . c) → b) → Bool
```

`y x` should type-check, but $x$'s scheme $\forall a.\ \mathrm{Bool}\to a$ is not *equal* (up to substitution) to what $y$ expects, $\forall b.\ (\forall c.\,c) \to b$ — it's more general, in a way that requires **contravariance in the domain**: $y$'s argument type demands something that accepts *anything* ($\forall c.\,c$, the type with no inhabitants except via absurdity) where $x$ only promises to accept `Bool`. Checking this is not unification; it's a genuinely asymmetric relation between schemes, and — critically — *verifying* it requires synthesising new code, not just a yes/no answer.

The judgment is subsumption:

$$\Gamma \vdash e : \sigma \prec e' : \sigma'$$

read "$\sigma$ is subsumed by $\sigma'$, and if $e$ has scheme $\sigma$ then $e'$ (built from $e$ by inserting implicit abstractions/applications) has the more general — wait, more accurately here, the *target* — scheme $\sigma'$." In Gundry's example, $\sigma' $ is checked as more general in the up-to-instantiation sense used for the higher-rank check; the mechanism that makes this constructive rather than a mere yes/no is the pair of contravariant rules in Figure 7.6, which peel implicit quantifiers off either side and insert an actual $\Lambda$ or application to compensate:

$$\dfrac{\Gamma, y:_e \sigma_0'' \vdash y : \sigma_0'' \prec e' : \sigma_0' \quad\quad \Gamma, y:_e\sigma_0'' \vdash e\,e' : \sigma_1 \prec e'' : \sigma_1'}{\Gamma \vdash e : (x:_e\sigma_0)\to\sigma_1 \prec \Lambda y:\lfloor\sigma_0''\rfloor.\,e'' : (y:_e\sigma_0'')\to\sigma_1'}$$

Working through Gundry's example concretely: $e = x$ with $\sigma = (a:^\forall_i *, z:_e \mathrm{Bool})\to a$, and the target $\sigma' = (b:^\forall_i *, z:_e((c:^\forall_i *)\to c))\to b$. Substituting $b$ for $a$ reduces both to explicit-quantifications at the same shape, so contravariance kicks in on the domain: it must check that $(c:^\forall_i *)\to c$ is "below" `Bool` — i.e., recursively subsumed in the *other* direction — which the algorithm discharges by instantiating $c := \mathrm{Bool}$ and using reflexivity. The result is a genuinely new term:

$$y\ \bigl(\Lambda b: \forall *.\ \lambda z:((c:^\forall_i *)\to c).\ x\ b\ (z\ \mathrm{Bool})\bigr)$$

— code that did not exist in the source at all. This is the real content of "subsumption for higher-rank polymorphism": it's not a check, it's a code-synthesizing coercion.

One restriction matters for the phase-indexed evidence language: subsumption (with its implicit $\lambda$-insertion) is **only available at the term phase**. At a static phase $\Upsilon$ there's no type-level $\lambda$-abstraction to insert, so the corresponding rule can only appeal to a proof of type *equality* $\gamma : \tau \sim \upsilon$ rather than a genuine subtyping-style coercion. This is a real expressiveness cost: higher-rank definitions at the type level are strictly less flexible than at the term level, purely because the evidence calculus doesn't (and, for its metatheory's sake, shouldn't) have type-level lambdas.

**Rust/Lean grounding.** Rust doesn't have implicit rank-N polymorphism to subsume against (its `dyn`/`impl Trait` boundaries are explicit), so there's no faithful Rust analogue for the code-insertion behavior — flagging that honestly rather than forcing it, per the style guide. Lean is the better fit: this is exactly the shape of Lean's `isDefEq`-adjacent subtyping used when elaborating a term against an expected type that differs by more than definitional equality — e.g. inserting a coercion (`↑`) or an eta-expansion to make a term of one Pi-type fit an expected Pi-type of different implicit-argument binding structure. Lean's elaborator's `synthesizeSyntheticMVars`-and-coercion-insertion machinery is a production version of exactly this "prove subsumption by synthesizing glue code" pattern.

## Metavariables and metacontexts: representing "we don't know yet"

**What breaks without this.** The non-deterministic specification is a relation on *fully elaborated* terms and *fully known* types — it can state that a derivation exists, but it has no vocabulary for "here is a term I've partly elaborated, with some types and proofs still outstanding." An algorithm, run left-to-right over a real program, constantly hits exactly that situation: `λx.λy.x y` needs *some* type for `x` and `y` before it has seen enough of the program to know what they are.

The fix, generalizing Chapter 4's Miller-pattern-unification metavariables to the dependent, phase-indexed evidence language, is the **metacontext** $\Theta$:

$$\Theta ::= \cdot \;\mid\; \Theta, \alpha[\Delta] :^\Phi \kappa \;\mid\; \Theta, \alpha[\Delta] = \rho :^\Phi \kappa \;\mid\; \Theta, a:^\Phi_e \sigma \;\mid\; \Theta, a:^\Phi_i \tau$$

Two kinds of new entries beyond Chapter 4's plain metavariable declarations: metavariables now carry a **telescope of parameters** $\Delta$ (because a metavariable introduced under a binder may depend on the bound variables — exactly the "raising" trick discussed below), and metacontexts also record ordinary variables with their implicit/explicit status, so the algorithm can track which are source-visible. Metavariable *occurrences* in evidence syntax become $\alpha[\delta]$ — the metavariable applied to a vector of arguments instantiating its parameters, typed by

$$\dfrac{\Theta \ni \alpha[\Delta]:^\Phi \kappa \quad \Gamma \vdash \delta : \Delta \quad \Phi \hookrightarrow \Psi}{\Gamma \vdash \alpha[\delta] :_\Psi [\delta/\Delta]\kappa}$$

This is exactly the same discipline as Chapter 2's ordered metacontext, generalized: **information only ever increases**, formalized by a *metasubstitution* $\theta : \Theta_0 \sqsubseteq \Theta_1$ — a map giving values (in terms of $\Theta_1$) to some of the metavariables of $\Theta_0$. The **Metasubstitution Lemma (7.2)** — "if $\theta:\Theta_0\sqsubseteq\Theta_1$ and $\Theta_0 \vdash J$ then $\Theta_1 \vdash \theta J$" — is the load-bearing invariant that makes the whole elaboration algorithm's threading of input/output metacontexts sound: whatever was derivable before a metavariable got solved is still derivable (suitably substituted) afterward.

One operation deserves special attention because it's a genuinely subtle piece of scope management: **parameterisation**, $\Delta \mathbin{\%} \Xi$, which takes a set of metavariables $\Xi$ and re-declares each of them with an extra telescope $\Delta$ prefixed onto its parameters. This is needed whenever elaboration finishes processing a binder ($\lambda x.\,t$, $\forall a.\,\sigma$, …) and the bound variable goes out of scope — any metavariable created *inside* that scope must be "hoisted out" while remembering that it may depend on the now-departed variable. Gundry names this explicitly as **Miller's "raising"** (Miller 1992) — permuting existential quantifiers (metavariables) from right to left past universal quantifiers (bound variables) in the ambient context. This is the same maneuver that makes higher-order pattern unification tractable in Chapter 4: a metavariable that would otherwise be "trapped" under a binder instead gets a parameter for that binder, turning an ill-scoped assignment into a well-scoped, dependently-parameterised one.

**Lean/Rust grounding.** This is the textbook shape of a metavariable context in any elaborator with implicit-argument synthesis: Lean's `MetavarContext` stores each metavariable's local context (its "telescope") and, once solved, its assignment — precisely `Θ, α[Δ] :Φ κ` versus `Θ, α[Δ] = ρ :Φ κ`. "Raising" is the same operation Lean's elaborator performs when a metavariable created inside a `fun x => ...` needs to escape that binder: it gets re-created with `x` added to its local context, and all existing references get an extra argument. In Rust terms, if you were implementing this, a metavariable would be a `struct Meta { id: MetaId, telescope: Vec<(String, Type)>, kind: Type }` living in an arena, with a separate `HashMap<MetaId, Term>` for solved assignments — and "raising" is literally re-keying an occurrence to append new telescope entries, then re-checking every dependent occurrence's argument vector.

## The bidirectional algorithm: three judgments, one discipline

This is the chapter's central engineering move, and it is a direct, explicit instance of **bidirectional typing** (inference vs. checking), generalized to *three* modes rather than the usual two, precisely because scheme lookup and type inference are genuinely different operations here:

| Judgment | Reads as | Role |
|---|---|---|
| $\Theta_0 \vdash^{\mathrm{sch}}_\Psi \rho \rightsquigarrow \rho : \sigma \dashv \Theta_1$ | scheme assignment | *look up* (never guess) an existing scheme for a variable/constructor, or elaborate an explicit ascription |
| $\Theta_0 \vdash_\Psi \rho \rightsquigarrow \rho : \tau \dashv \Theta_1$ | type inference (synthesis) | compute a type bottom-up from the expression's structure |
| $\Theta_0 \vdash_\Psi \rho : \sigma \rightsquigarrow \rho \dashv \Theta_1$ | type checking | verify/elaborate against a scheme supplied top-down |

Everything before the turnstile $\vdash$ (the input metacontext $\Theta_0$, the phase $\Psi$, the source term, and — for checking — the scheme) is an **input**; everything after $\dashv$ (the output metacontext $\Theta_1$, and for the other two, the elaborated term/type) is an **output**. Gundry states the discipline explicitly: "information flows clockwise through each inference rule" — the input metacontext of the conclusion feeds the first premise, whose *output* metacontext feeds the next premise's input, and so on, until the last premise's outputs become the conclusion's outputs. This left-to-right, input-to-output threading is exactly what turns a set of inference rules into pseudocode: each rule reads directly as a sequence of recursive calls.

The three-way split solves a real problem with plain bidirectional typing: **scheme assignment is deliberately not the same as inference**. A scheme is *never derived*, only looked up in the context (a variable or a constructor's declared type) or provided explicitly (a type ascription). Type inference, by contrast, is what happens to *applications*: given a head with an assigned scheme and a spine of argument, inference completes the scheme against the spine to produce an ordinary type. The reason both need to exist is that the head of an application isn't always something with an assigned scheme — it might be a $\lambda$-abstraction (in a $\beta$-redex) or a `let`, which only have inferred types. So inferred-type expressions get *embedded* into assigned-scheme ones via a fallback rule, letting an inferred $\tau$ stand in as a trivial scheme.

Walking Gundry's own worked example is the fastest way to see the machinery cohere. Elaborating `λx.λy.x y`:

1. Entering the outer $\lambda x$, the algorithm doesn't know $x$'s type, so it manufactures a fresh metavariable $\alpha[\cdot]:^\forall *$ and binds $x :_e \alpha$ — same for $y$ with $\beta$.
2. To elaborate the application `x y`, look up $x$'s scheme: it's the bare type $\alpha$ (via the fallback embedding). Since $\alpha$ isn't syntactically an arrow, generate two more fresh metavariables $\alpha_0, \alpha_1$ for domain/codomain and **emit the constraint** $\alpha \sim (\alpha_0 \to \alpha_1)$ to the unifier.
3. Check `y` against the domain $\alpha_0$: `y`'s inferred type is $\beta$, and checking against $\alpha_0$ invokes *subsumption*, which (since both are bare types, no quantifiers to peel) reduces to unification, emitting $\beta \sim \alpha_0$.
4. Before any constraint solving, the raw output is $\lambda x{:}\alpha.\,\lambda y{:}\beta.\,(x.\zeta)\,(y.\zeta')$ in a metacontext carrying $\zeta[\cdot]:\alpha\sim(\alpha_0\to\alpha_1)$ and $\zeta'[\cdot]:\beta\sim\alpha_0$ — every unification obligation reified as a coercion metavariable sitting right there in the term.
5. Once the unifier actually runs, $\alpha := \alpha_0\to\alpha_1$ and $\beta := \alpha_0$ get solved (as *definitions* in the metacontext, per the $\Theta,\alpha[\Delta]=\rho:^\Phi\kappa$ form above), both $\zeta,\zeta'$ become reflexivity proofs and disappear, and the final evidence term collapses to $\lambda x{:}(\alpha_0\to\alpha_1).\,\lambda y{:}\alpha_0.\,(x.\langle\alpha_0\to\alpha_1\rangle)\,(y.\langle\alpha_0\rangle)$.

Notice what happened to the "three incompatible elaborations" non-determinism from Section 7.3: the algorithm didn't magically pick the "right" one — it *deferred the decision* by inventing metavariables for everything unknown, and let unification decide which non-deterministic branch was forced by the actual constraints. This is precisely why Theorem 7.4 (soundness of the algorithm relative to the non-deterministic specification) is provable: every algorithmic derivation, once you erase the "we haven't solved this yet" bookkeeping, *is* one particular derivation the non-deterministic system already permitted.

**Rust grounding.** The three-judgment split maps directly onto a three-function elaborator:

```rust
enum ElabMode<'a> { Synth, Check(&'a Type) }

fn elab_scheme(ctx: &mut Ctx, e: &Expr) -> (Term, Scheme) { /* lookup only */ }
fn elab_infer(ctx: &mut Ctx, e: &Expr) -> (Term, Type) {
    let (head, scheme) = elab_scheme(ctx, e.head());
    apply_spine(ctx, head, scheme, e.args())   // completes scheme against args
}
fn elab_check(ctx: &mut Ctx, e: &Expr, expected: &Type) -> Term {
    let (term, inferred) = elab_infer(ctx, e);
    subsume(ctx, term, inferred, expected)     // may insert code, per subsumption
}
```

— a shape any bidirectional type-checker/elaborator author will recognize immediately, right down to `elab_check` being defined in terms of `elab_infer` plus a subsumption/coercion step.

## Constraint solving as backward-chaining proof search

**What breaks without this.** The algorithm above emits equality obligations ($\alpha \sim (\alpha_0\to\alpha_1)$, or in the dependent setting, arbitrary type-level equalities involving $\Pi$-types and integers) but never says how they get discharged — that's deliberately factored out as a separate concern. Gundry is explicit that designing the constraint solver "is a complex task in itself" and declines to specify it fully; the chapter instead pins down its *interface* and sketches its *shape*.

The interface is one rule, conceptually:

$$\dfrac{\Theta_0,\, \zeta[\cdot]:\tau\sim\upsilon \;\rightsquimap\!\!\rightsquimap\; \Theta_1}{\Theta_0 \vdash \tau \sim \upsilon \rightsquigarrow \zeta \dashv \Theta_1}$$

A fresh coercion metavariable $\zeta$ (a "goal," at phase $\square$) is added for the obligation, and a **backward-chaining proof search** relation ($\rightsquimap\!\!\rightsquimap$, i.e. $\Theta \gg \Theta'$) takes as many solving/simplifying steps as it can. This is where the earlier chapters' unification algorithms get reused as *tactics* inside a bigger search:

- **Congruence decomposition**: a goal $\tau_1\ \upsilon\ \tau_1'\sim \tau_2\ \upsilon\ \tau_2'$ (application congruence) splits into subgoals $\zeta_0:\tau_1\sim\tau_2$, $\zeta_1:\upsilon\sim\upsilon'$, discharged by building the original coercion from the pieces: $\zeta := \mathrm{cong}_a^\Upsilon\ \zeta_0\ \zeta_1$.
- **Computation** ("step $\rho$"): reduce both sides before comparing, reusing the evidence language's own operational semantics.
- **Coherence**: strip coercions from equational goals when they're not needed.
- **Flex-flex / flex-rigid solving**: exactly Chapter 4's higher-order (Miller pattern) unification algorithm, reused verbatim for metavariable-headed goals.
- **Hypothesis use**: a goal can be solved directly from a local assumption in its telescope of parameters — e.g. $\zeta[c: b\sim a] : a \sim b$ solves as $\zeta[c:b\sim a] := \mathrm{sym}\ c$ — and **introducing** a hypothesis for a later goal is literally $\lambda$-abstraction over a coercion variable.
- **Equational-theory-specific solving**: since integers under $+$ form an abelian group, integer constraints reuse Chapter 3's abelian-group unification wholesale.

This is a textbook description of a **backward-chaining, tactic-style theorem prover** embedded inside a type-checker — the same architecture as Coq's tactic engine discharging a goal state, or a Prolog-style resolution search where each "clause" is one of the coercion constructors. Crucially, Gundry's **Soundness of Unification (Lemma 7.3)** conditions everything on one assumption: *if* every step of the search relation ($\gg$) is itself an information-increasing metasubstitution ($\Theta \sqsubseteq \Theta'$), *then* embedding search into elaboration is sound. This cleanly separates two very different engineering concerns: getting the *search strategy* right (heuristics, ordering, termination — left almost entirely unspecified) versus proving that *whatever* the search finds is trustworthy (a small, checkable condition on each step).

**Automated-reasoning / Lean grounding.** This is precisely the "trusted kernel, untrusted search" architecture from the automated-reasoning literature: the search procedure ($\gg$) can be as heuristic, incomplete, or even buggy as it likes — soundness never depends on the search being *any particular* algorithm, only on each step it takes being a genuine information-increasing substitution, checkable independently. This is the same shape as Lean's own tactic framework: tactics are free to search however they like, but every tactic bottoms out in kernel-checkable proof terms, so a buggy tactic produces a rejected proof, never an unsound one. It is *the* answer to "how do I build a proof search engine I can trust without trusting the search": push all cleverness into constructing a certificate, and make certificate-checking trivial and separate.

## Elaborating dependent case expressions

**What breaks without this.** Everything so far handles a first-order fragment without pattern matching. But `case`/`dcase` on GADT-like constructors (recall `Vec`'s indices) is exactly where dependent typing earns its keep in practice — a branch for `Cons` needs to know that the vector's length index is `Suc m` for some `m`, and it needs that fact *as a proof it can use*, not just as a type-level equation floating nearby.

Two case forms extend [[The-Evidence-Language#The grammar|the grammar]]: ordinary `case` (result type may not mention the scrutinee) and `dcase`, **dependent case**, where the branches may refine the *type* using the fact that the scrutinee equals the specific constructor pattern in that branch. The key non-deterministic rule for a branch (Figure 7.14) is

$$\dfrac{\Sigma \ni K:^\Phi (a_i:^\forall_i \kappa_i, \Delta)\to D\ a_i^i \quad \Phi\hookrightarrow\Psi \quad vs : [\upsilon_i/a_i]\Delta \rightsquigarrow \Delta' \quad \Gamma,\Delta' \vdash \rho \rightsquigarrow \rho : \tau}{\Gamma \vdash (K\ vs \to \rho) \rightsquigarrow (K\ \lfloor\Delta'\rfloor \to \rho) :_\Psi D\ \upsilon_i^i \mathbin{\Rightarrow} \tau}$$

The auxiliary judgment $vs : \Delta \rightsquigarrow \Delta'$ does pattern-to-telescope matching: it takes the source-level binding names the programmer actually wrote (`Cons {m = m'} x xs`) and reconciles them against the constructor's full annotated telescope, silently introducing the implicit bindings the programmer didn't bother naming (here, `a` and the coercion `c`) while renaming the explicitly-named ones. This is a clean generalization of ordinary pattern matching to telescopes with mixed implicit/explicit binders — GADT index variables and equality proofs come along for free without the programmer ever writing them.

The `dcase` version additionally augments the branch's local telescope with an equality hypothesis $c :^\square_i \varepsilon \sim K\ \upsilon_i^i\ \Delta'$ — literally "the scrutinee equals this constructor applied to its (possibly fresh) arguments" — which is exactly the propositional-equality-in-context trick that lets, e.g., Agda or Idris's dependent pattern match refine types along each branch. Gundry's worked `replicate` example (recall from Chapter 5) makes this concrete: in the `Zero` branch, the algorithm inserts an implicit proof obligation $\zeta : n \sim \mathrm{Zero}$ (discharged trivially by the branch's own local hypothesis $c$); in the `Suc m` branch, it's $c : n \sim \mathrm{Suc}\ m$, used to type the recursive call correctly at the smaller index.

Two things are explicitly scoped *out* here, and it's worth noting them as honest limitations rather than oversights: only **flat (non-nested) pattern matches** are handled (nested matching is "well-studied" but complicates the presentation), and **coverage checking is assumed, not verified** — proving that an omitted branch is genuinely impossible would require the constraint solver to prove a *negative* (unsatisfiability), which the sketch of Section 7.5.1 never claims to support (Gundry cites Goguen et al. 2006's "refutation" patterns as the standard fix).

**Rust/static-analysis grounding.** This is the formal backbone of what a Rust `match` on an enum with phantom-type-encoded invariants is trying to approximate at the type level (e.g. a `Vec<T, N>`-style length-indexed type using const generics, matched against a `Cons`/`Nil`-shaped representation) — except Rust's type system can't actually *refine* the const-generic parameter inside each match arm the way `dcase` refines $n$ to `Suc m`. This is exactly the gap that motivates refinement-type or dependent extensions to systems languages: without a genuine dependent case rule, you can encode the *shape* of an invariant with phantom types, but you can't get the compiler to *use* the branch-specific refinement automatically — you end up manually threading `PhantomData` proofs or `unsafe` assertions where `dcase`'s hypothesis $c$ would just appear in context for free.

## The decision not to generalise local lets

**What breaks without this** is exactly the interesting question here, because the "obvious" thing to do — following Chapters 2 and 3's Hindley-Milner treatment, where `let`-generalisation is just "skim metavariables off the top of the context after inferring the definiens' type" — turns out to be actively unsound-feeling (not unsound in the metatheoretic sense, but unpredictable) once local constraints and parameterised metavariables enter the picture.

Gundry's own minimal counterexample is worth walking through slowly, because it's the crux of the whole argument. Suppose a local definition has inferred type $\alpha\to\alpha$, in a context ending with $\alpha[\cdot]:^\forall *,\ \zeta[c:\beta\sim\mathrm{Bool}]:\alpha\sim\mathrm{Bool}$ — that is, $\alpha$ has an *outstanding, locally-hypothesis-dependent* constraint saying it's equal to `Bool`, but only under the assumption $c$. Two reasonable-looking strategies disagree about what to do:

- **Generalise now**, discarding the local hypothesis $c$ since $\zeta$'s type doesn't actually depend on it, producing $(a:^\forall_i *,\ z:^\square_i\ a\sim\mathrm{Bool})\to a\to a$ — i.e., "`Bool → Bool` up to isomorphism," a polymorphic function that only actually accepts `Bool`-equal types.
- **Don't generalise, and let constraint solving continue.** If solving later discovers $\alpha\sim\beta$ (from context *outside* the definition, arriving after generalisation would have already committed), the *correct* final type is just $\alpha\to\alpha$ for an unconstrained metavariable $\alpha$ — no polymorphism at all, because $\alpha$ ends up equal to some unrelated, unconstrained type, not `Bool`.

These two answers are not just different presentations of the same type — they are genuinely different, non-isomorphic types, and **which one is right depends on information that arrives after the point where you'd have to decide whether to generalise.** Committing early (as Hindley-Milner generalisation must, by construction) can commit to the wrong answer, and worse, *whether* it goes wrong depends on program-order/constraint-solving-order details that have nothing to do with the program's actual meaning — Gundry's phrase for this is that "elaboration becomes fragile."

The chosen fix, following Vytiniotis et al. (2010, the paper behind GHC's `OutsideIn(X)`): **local `let`-bindings are simply never generalised.** A local definition's type is whatever metavariable(s) it infers to, full stop — those metavariables get solved (or reported as ambiguous errors) exactly like any other metavariable in the enclosing scope, rather than being abstracted into a fresh polymorphic scheme. (Top-level `let`s are still generalised, because at the top level there is no "outside" context left to arrive later with disambiguating information — any leftover parameterised metavariable is unambiguously either solvable or an error.) Gundry is candid that this is a **simplicity-over-power trade-off**, not the only defensible choice: an alternative heuristic — generalise only when the definiens introduced *no* parameterised metavariables at all (no local GADT-case-analysis constraints, no higher-rank subexpressions) — would recover generalisation in the common, unproblematic case, at the cost of making "does my code get polymorphism here" depend on inference-algorithm internals that are hard for a programmer to predict without understanding the implementation.

**Automated-reasoning / type-theory grounding.** This is a direct, load-bearing instance of the "local constraints break principal typing" phenomenon familiar from GADT type inference generally, and it's precisely the reasoning your own elaborator's design will need to reproduce anywhere a metavariable's eventual solution depends on constraints local to one branch of a case analysis or one nested scope: the *safe* default is "don't commit to a shape (a polymorphic scheme) before you're sure external information won't retroactively invalidate that shape." Note the parallel to Hindley-Milner's own soundness argument for *top-level* generalisation (Chapter 2): that argument crucially relies on there being no more information to arrive from "outside" a completed top-level derivation — exactly the assumption that fails for a `let` nested under unresolved local hypotheses.

## Where this leads

```
Ch.2 HM elaboration ──┐
Ch.3 units unification ─┼──► Ch.4 Miller pattern unification ──┐
Ch.6 Evidence language ─┘                                       ├──► Ch.7: THIS
                                                                  │    non-det. spec (7.3)
                                                                  │      → subsumption (higher-rank)
                                                                  │      → metavariables/metacontexts (7.4)
                                                                  │      → bidirectional algorithm (7.5)
                                                                  │      → backward-chaining constraint solving
                                                                  │      → dependent case (7.6)
                                                                  ▼
                                                        Ch.8: worked inch programs
                                                        (Vec/red-black trees/units library)
                                                        exercising exactly this elaborator
```

Everything downstream of this chapter — Chapter 8's worked examples (length-indexed vectors, invariant-preserving red-black trees, a units-of-measure library) — is simply this elaboration algorithm being run on progressively more demanding programs; nothing new is added to the theory. And everything upstream feeds directly in: Chapter 4's Miller pattern unification is reused nearly verbatim as the flex-flex/flex-rigid tactics inside constraint solving; Chapter 3's abelian-group unification is reused for the integer-indexed types; Chapter 2's "generalise a `let` by skimming metavariables" is the strategy this chapter explicitly and deliberately *declines* to extend.

For the standing project (`type-theory` and `automated-reasoning` focus areas both apply directly here): this chapter *is* the closest thing in the whole thesis to a template for the planned Rust elaborator. The three-judgment bidirectional split (scheme-assignment / inference / checking) is close to exactly the API shape a real implementation needs; the metacontext-with-telescoped-metavariables-and-raising is the concrete data structure the Miller-pattern-unification-based implicit-argument resolver will need; and the "trusted-kernel-checks-certificates, untrusted-search-produces-them" separation between the evidence language's type checker and the backward-chaining constraint solver is precisely the soundness architecture a custom theorem prover embedded in a compiler toolchain should copy. The `let`-generalisation discussion is a genuine cautionary tale worth internalizing early: any refinement-type or Hoare-contract inference the planned compiler does under local hypotheses (a branch of a case analysis, a local assumption from a guard) inherits exactly the same "don't commit to a general shape before you know external constraints won't retroactively break it" hazard.
