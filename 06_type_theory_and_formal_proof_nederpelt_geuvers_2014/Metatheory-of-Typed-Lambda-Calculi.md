---
title: Metatheory of Typed Lambda Calculi
source: "Type Theory and Formal Proof: An Introduction (Nederpelt & Geuvers, 2014)"
chapters: "Ch. 2 §§2.10–2.12 (pp. 53–68), Ch. 4 §§4.7–4.8 (pp. 96–99), Ch. 6 §6.3 (pp. 128–132), with grounding from Ch. 1 §1.9 (pp. 19–22)"
tags: [type-theory, lambda-calculus, metatheory, subject-reduction, confluence, normalisation, decidability, formal-proof]
---

[[book-guidelines|↩ Back to guidelines]]

# Metatheory of Typed Lambda Calculi

## Why a type system needs a metatheory, not just a definition

Writing down typing rules is the easy part. Three rules — (var), (appl), (abst)
— and you have a system that looks complete: you can hand it a term and a
context and grind out a derivation. But a set of inference rules is just a
generator of judgements. Nothing *forces* those judgements to hang together
in a way that deserves the name "type system." That coherence has to be
proved, one property at a time, and the properties are not optional
decoration — each one is load-bearing for something you actually want.

Concretely, imagine building a type checker for a language and skipping the
metatheory. What could go wrong?

- **No Subject Reduction.** Your checker approves `f(x)` at type `Bool`. You
  run it — it's just β-reduction under the hood — and the result is a value
  the runtime tags as `Int`. The checker's guarantee ("this term, when it
  produces a result, produces a `Bool`") was a lie. Every downstream
  consumer of "well-typed programs don't get stuck / don't misbehave" is now
  unsound.
- **No Substitution Lemma.** Function calls are substitution. If plugging a
  well-typed argument into a well-typed function body can *change* the
  body's type, then type-checking a function once and reusing it at many
  call sites — the entire premise of having functions at all — stops being
  valid. You'd have to re-check the body from scratch at every call site,
  and even then you couldn't trust the result to compose.
- **No confluence / no unique normal form.** If reduction order affects the
  answer, then a compiler that reduces eagerly and one that reduces lazily
  could produce *different observable results* from the same well-typed
  program. "The" value of a term stops being well-defined.
- **No decidable type checking.** If checking whether `Γ ⊢ M : σ` holds is
  itself undecidable, you cannot build a type checker. Not "a slow one" — no
  algorithm exists, period. Everything downstream (an IDE that reports type
  errors, a compiler that rejects bad programs before running them) is
  impossible in principle, not just impractical.

So the metatheory is not bookkeeping. It's the set of theorems that turns "a
pile of inference rules" into "a type system you can build tools around and
reason about." This article follows how Nederpelt and Geuvers develop that
toolkit for $\lambda \! \to$ (simply typed lambda calculus, Chapter 2), show
how it must be repaired once types themselves can compute in $\lambda\omega$
(Chapter 4), and how it culminates in the Calculus of Constructions $\lambda
C$ (Chapter 6, §6.3, which the book uses as a grand summary of everything
that came before). The properties are cumulative — each richer system either
inherits a lemma unchanged or needs to weaken it slightly to survive a new
feature. That pattern of "what breaks and what has to be repaired" is itself
one of the most instructive threads in the book.

---

## 1. Context bookkeeping: Free Variables, Thinning, Condensing, Permutation

### The intuition

Before you can say anything about *terms*, you need to pin down what a
*context* is allowed to do without disturbing a derivation. A context $\Gamma
\equiv x_1 : \sigma_1, \ldots, x_n : \sigma_n$ is a list of declarations —
think of it as the type environment / symbol table a compiler threads
through type-checking. Four basic facts about how contexts and terms relate
are proved before anything else, because every later proof leans on them.

**Free Variables Lemma.** If $\Gamma \vdash L : \sigma$, then $FV(L) \subseteq
dom(\Gamma)$. Every free variable used by a well-typed term has a
declaration recording its type. This is the formal version of "no
unresolved identifiers" — a compiler's "unbound variable" error is exactly
the contrapositive of this lemma.

**Thinning.** If $\Gamma \vdash M : \sigma$ and $\Gamma \subseteq \Gamma'$
(read: $\Gamma'$ contains all of $\Gamma$'s declarations, in order, plus
maybe more), then $\Gamma' \vdash M : \sigma$ too. Adding irrelevant
declarations to a context can never break a derivation — this is why you can
type-check a function body in isolation and later drop it into a larger
scope with more bindings in play.

**Condensing.** The dual: $\Gamma \vdash M : \sigma$ implies $\Gamma \restriction
FV(M) \vdash M : \sigma$ — you can throw away every declaration for a
variable that doesn't actually occur free in $M$. Together, Thinning and
Condensing say: *"one may either add or remove junk to/from a context,
without affecting derivability"*, where junk means declarations for
variables that don't occur free in the term being checked.

**Permutation.** Reordering the declarations in $\Gamma$ (consistently) never
affects derivability — declarations are independent facts, not a sequential
program.

### What breaks without this

Without Thinning, a type checker couldn't type-check a subexpression in
isolation and then reuse that judgement once more bindings come into scope
— you'd be forced to re-derive everything from an ever-growing context at
every nesting level, and there'd be no local reasoning at all. Without
Condensing, contexts would accumulate garbage forever with no formal
justification for garbage-collecting them.

### Grounding

In Rust, a context is basically a `Vec<(Ident, Type)>` or `HashMap<Ident, Type>`
threaded through a recursive type-checking pass. Thinning corresponds to
the observation that pushing an unrelated binding onto your `Vec` before
recursing into an inner scope can't retroactively invalidate a judgement you
already derived for an outer term — which is exactly why a type checker can
be written as a straightforward recursive function taking `&Context` rather
than needing global reanalysis.

```rust
// Thinning, operationally: extending ctx with irrelevant bindings
// never invalidates a judgement already derived under a subset of it.
fn typecheck(ctx: &Context, term: &Term) -> Result<Type, TypeError> { /* ... */ }

// If `ctx_sub` is a prefix/subset of `ctx_super` (same order, no removed
// entries) and typecheck(ctx_sub, m) succeeds, typecheck(ctx_super, m)
// must succeed with the same type — that's Thinning as a runtime invariant.
```

In Lean, this is close to how the local context (`LocalContext`) works
during elaboration: elaborating a subterm under a context, then extending
that context with more local hypotheses, doesn't invalidate previously
elaborated subterms — it's part of why Lean's elaborator can work
incrementally, goal by goal, hypothesis by hypothesis.

---

## 2. Generation Lemma: derivations are syntax-directed

### The intuition

Suppose you're handed the judgement $\Gamma \vdash M\,N : \tau$. Which rule
produced it? In $\lambda \! \to$, there's exactly one possible answer: it must
have come from (appl), so $M$ has some arrow type $\sigma \to \tau$ and $N$
has type $\sigma$. You never have to guess or search over rules — the
*shape* of the term you're looking at determines which rule could possibly
apply. This property is called **syntax-directedness**, and the Generation
Lemma is its formal statement: each syntactic form of term has exactly one
rule that can conclude a judgement about it.

$$
\begin{aligned}
&\text{(1) } \Gamma \vdash x : \sigma \implies x : \sigma \in \Gamma \\
&\text{(2) } \Gamma \vdash M\,N : \tau \implies \exists \sigma.\ \Gamma \vdash M : \sigma \to \tau \text{ and } \Gamma \vdash N : \sigma \\
&\text{(3) } \Gamma \vdash \lambda x{:}\sigma . M : \rho \implies \exists \tau.\ \Gamma, x{:}\sigma \vdash M : \tau \text{ and } \rho \equiv \sigma \to \tau
\end{aligned}
$$

### What breaks without this

Syntax-directedness is precisely what makes a type checker a straightforward
recursive-descent algorithm instead of a search problem. If a term's shape
didn't determine which rule to try, "type checking" would mean trying every
rule at every step and backtracking — the difference between a linear-time
inference pass and a potentially exponential search.

### Generation Lemma in the Calculus of Constructions: what has to be added

By Chapter 6, once $\lambda C$ has both Π-types (dependent function types) and
the conversion rule (§3 below), the Generation Lemma survives but every
clause picks up an "up to $\beta$-conversion" clause. For instance, case (2)
becomes: if $\Gamma \vdash MN : C$, then $M$ has *some* $\Pi$-type $\Gamma
\vdash M : \Pi x{:}A.B$, $N$ fits it ($\Gamma \vdash N : A$), and $C =_\beta
B[x := N]$ — not $C \equiv B[x:=N]$ syntactically, only convertible to it.
This is the first place you see the pattern that recurs throughout this
article: richer systems keep the *shape* of every $\lambda \! \to$ lemma but
replace syntactic identity ($\equiv$) with convertibility ($=_\beta$)
wherever the conversion rule is in play.

### Grounding

This is exactly bidirectional typing's *checking* mode dispatching on term
constructors — in Rust, a `match` on an AST node where each arm corresponds
to exactly one typing rule:

```rust
fn infer(ctx: &Context, term: &Term) -> Result<Type, TypeError> {
    match term {
        Term::Var(x) => ctx.lookup(x),                 // (var) — only rule for Var
        Term::App(m, n) => {                             // (appl) — only rule for App
            let sigma_to_tau = infer(ctx, m)?;
            let Type::Arrow(sigma, tau) = sigma_to_tau else { return Err(NotAFunction) };
            check(ctx, n, &sigma)?;
            Ok(*tau)
        }
        Term::Abs(x, sigma, body) => { /* (abst) — only rule for Abs */ Ok(/* ... */) }
    }
}
```

Lean's kernel `infer`/`check` functions are structured on this exact
principle: `Expr` is an inductive type, and the type-checker's core loop is
one match arm per constructor, each arm implementing exactly the rule the
Generation Lemma says is the only one available.

---

## 3. Substitution Lemma: function calls preserve types

### The intuition

$\beta$-reduction *is* substitution — $(\lambda x{:}\sigma. M)N \to_\beta
M[x := N]$ — so if substitution could change a term's type, the entire
reduction relation would be untyped chaos. The Substitution Lemma is the
load-bearing fact that makes function application well-behaved:

$$
\text{If } \Gamma', x{:}\sigma, \Gamma \vdash M : \tau \text{ and } \Gamma' \vdash N : \sigma,
\quad \text{then } \Gamma', \Gamma \vdash M[x := N] : \tau .
$$

In words: replacing every free occurrence of $x$ (of type $\sigma$) in $M$
by a term $N$ of the *same* type $\sigma$ leaves the type of $M$ unchanged.
The proof is a clean structural induction, with the interesting case being
abstraction: to substitute into $\lambda u{:}\rho.L$, you push the
substitution under the binder (using that $u \notin FV(N)$, which the Free
Variables Lemma of §1 guarantees) and re-apply (abst) — a textbook example
of induction hypotheses "passing through" a binder.

### What breaks without this

Every call to a function is a substitution waiting to happen at runtime (or
at compile time, for inlining/specialization). Without the Substitution
Lemma, type-checking a generic function body once and reusing that judgement
for every call site would be unsound — you'd have to re-verify from scratch
at every call, defeating the entire point of having reusable, typed
functions in the first place.

### Grounding

This is the theorem that justifies monomorphization and inlining in Rust:
substituting a concrete type/value for a generic parameter is *exactly* the
substitution in this lemma, and the Substitution Lemma is why the compiler
can trust that a generic function, type-checked once against an abstract
`T`, remains well-typed after `T` is instantiated to any concrete type
respecting the same bound.

```rust
fn apply<F, A, B>(f: F, x: A) -> B where F: Fn(A) -> B { f(x) }
// The Substitution Lemma is the metatheoretic fact that lets the compiler
// type-check `apply`'s body once, then instantiate F, A, B at any call
// site without re-checking the body — substitution can't change the type.
```

In Lean, this is precisely what makes `beta` reduction — and more generally
the kernel's `whnf`/`isDefEq` machinery — type-preserving: unfolding a
`let`-bound term or beta-reducing an application is a substitution, and the
Substitution Lemma (transported to $\lambda C$/$\lambda D$-style systems) is
what guarantees the kernel never needs to re-elaborate a term after
reducing it.

---

## 4. Confluence and normal forms: reduction order doesn't matter

### The intuition

$\beta$-reduction is nondeterministic — a term can contain several redexes,
and reducing different ones first can (temporarily) produce syntactically
different terms. The book's example: $(\lambda x.(\lambda y.\,y\,x)z)v$
reduces, via one redex, to $(\lambda y.\,y\,v)z$, and via the other, to
$(\lambda x.\,z\,x)v$. These look different — but both reduce further to the
same term, $zv$. The **Church–Rosser Theorem** (Confluence, CR) says this is
never a coincidence:

$$
\text{If } M \twoheadrightarrow_\beta N_1 \text{ and } M \twoheadrightarrow_\beta N_2, \text{ then } \exists N_3 \text{ with } N_1 \twoheadrightarrow_\beta N_3 \text{ and } N_2 \twoheadrightarrow_\beta N_3.
$$

The immediate corollary is **uniqueness of normal forms**: if a term has a
$\beta$-normal form at all, it has exactly one (up to $\alpha$-equivalence).
"The" value of a term is well-defined independent of which redex you reduce
first. Weak normalisation (some reduction path terminates) is a strictly
weaker property than strong normalisation (every reduction path terminates)
— but confluence guarantees that if you're weakly normalising, it doesn't
matter which terminating path you follow, you land in the same place.

Chapter 2 notes something sharp: types play *no role at all* in the
definition of $\beta$-reduction (the basis rule $(\lambda x{:}\sigma.M)N
\to_\beta M[x:=N]$ doesn't even require $x$ and $N$ to have matching types),
so Confluence for the untyped calculus (Chapter 1, §1.9) transfers to every
typed system essentially for free — it's inherited, not re-proved, all the
way up to $\lambda C$ (Theorem 6.3.11).

### What breaks without this

If reduction order affected the outcome, then an eager evaluator and a lazy
evaluator (or a compiler's constant-folding pass run in a different order)
could disagree about what a program computes — even for a program that
*does* terminate. Confluence is what lets a language spec say "the value of
this expression is X" as opposed to "the value depends on evaluation
strategy."

### Grounding

In Rust, this underwrites the assumption that `const fn` evaluation, or any
compile-time partial evaluation, gives a canonical result regardless of the
order the compiler happens to fold subexpressions in. In Lean, confluence
(for the kernel's definitional-equality reduction — beta/delta/iota/zeta) is
precisely what `isDefEq` relies on: two terms that both reduce to some
common form are judged definitionally equal *regardless* of which reduction
strategy (whnf, unfolding, etc.) the kernel happens to use to discover that
common form. Without confluence, `isDefEq` would be strategy-dependent —
different tactics could get different answers about whether two terms are
"the same."

---

## 5. Subject Reduction, Type Reduction, and the Conversion Rule

### Subject Reduction: computing preserves types

**Subject Reduction** is the workhorse soundness theorem:

$$
\text{If } \Gamma \vdash L : \rho \text{ and } L \twoheadrightarrow_\beta L', \text{ then } \Gamma \vdash L' : \rho.
$$

Reducing the *subject* of a judgement (the term) while holding the type
fixed always yields a derivable judgement. The proof is induction on the
reduction, with the interesting case being the redex itself: if $\Gamma
\vdash (\lambda x{:}\sigma.M)N : \rho$, the Generation Lemma (§2) forces
$\Gamma, x{:}\sigma \vdash M : \rho$ and $\Gamma \vdash N : \sigma$, and then
the Substitution Lemma (§3) directly gives $\Gamma \vdash M[x:=N] : \rho$.
Subject Reduction is thus a direct *consequence* of Generation +
Substitution, not an independent axiom — a nice illustration of how the
metatheory is one connected structure, not a list of unrelated facts.

This is the formal counterpart of "3 + 5 evaluates to 8, and 8 is still a
natural number" — evaluating a well-typed program can never produce
something of the wrong type, and (crucially) can never get *stuck* in a way
that isn't itself a value.

### Type Reduction and the need for a Conversion rule

Subject Reduction reduces the *subject*, keeping the type fixed. What about
reducing the *type*? In $\lambda \! \to$, types are simple objects (built from
base types and $\to$) that don't themselves contain redexes, so the question
doesn't arise. But once you reach $\lambda\omega$ (Chapter 4), *types can be
the result of computation* — a type constructor like $\lambda\alpha{:}{*}.\,
\alpha \to \alpha$ applied to a type $\beta$ reduces: $(\lambda\alpha{:}{*}.\,
\alpha \to \alpha)\,\beta \to_\beta \beta \to \beta$.

Now something breaks. You can derive $\beta{:}{*}, x{:}(\lambda\alpha{:}{*}.\,
\alpha\to\alpha)\beta \vdash x : (\lambda\alpha{:}{*}.\,\alpha\to\alpha)\beta$
by (var). You'd *want* to also conclude $x : \beta \to \beta$, since the two
types are $\beta$-convertible and "intentionally the same type." But the
three original rules (var), (appl), (abst) give you no way to derive this —
the system is, in the book's words, "too weak to draw that conclusion." So a
fourth rule is added:

$$
\text{(conv)} \quad \frac{\Gamma \vdash A : B \qquad \Gamma \vdash B' : s}{\Gamma \vdash A : B'} \quad \text{if } B =_\beta B'.
$$

The second premise ($\Gamma \vdash B' : s$, i.e. $B'$ is itself well-formed
as a type or kind) is not redundant — the book gives a sharp
counterexample: $\beta \to \gamma =_\beta (\lambda\alpha{:}{*}.\,\beta\to
\gamma)\,M$ for *any* term $M$, including ill-formed ones, so
$\beta$-convertibility to a well-formed type does not itself guarantee the
convertible expression is well-formed.

The book is explicit about the three-way distinction this creates:

| | reduces | rule status |
|---|---|---|
| **Subject Reduction** | the subject ($A \to A'$), type fixed | a *theorem*, provable without (conv) |
| **Type Reduction** | the type ($B \to B'$), subject fixed | a *subcase* of (conv), not provable without it |
| **Conversion** | type replaced by any $=_\beta$-equivalent one | the *rule* (conv) itself, strictly more general than reduction in either direction |

### Uniqueness of Types, weakened to "up to conversion"

In $\lambda \! \to$, Uniqueness of Types is exact: $\Gamma \vdash M : \sigma$
and $\Gamma \vdash M : \tau$ force $\sigma \equiv \tau$ syntactically. Once
(conv) is in the system, this can no longer hold literally — $x$ above
provably has *both* $(\lambda\alpha{:}{*}.\alpha\to\alpha)\beta$ and $\beta
\to \beta$ as types, and they are not syntactically identical. The lemma is
repaired, not abandoned:

$$
\textbf{Uniqueness of Types up to Conversion.} \quad \Gamma \vdash A : B_1 \text{ and } \Gamma \vdash A : B_2 \implies B_1 =_\beta B_2.
$$

This exact statement reappears unchanged in $\lambda C$ (Chapter 6, Lemma
6.3.9) — once you've paid the price of weakening "$\equiv$" to "$=_\beta$"
at the $\lambda\omega$ stage, no further systems in the book need to weaken
it any further.

### What breaks without this

Subject Reduction is the difference between "well-typed programs don't get
stuck" and no guarantee at all — it's the single theorem most industrial
type systems point to as their soundness argument. Without the Conversion
rule (once types compute), a perfectly sensible term like the `x` above
would simply be *rejected* by a type checker that insists on syntactic type
equality, even though its two types denote the same thing after evaluation
— you'd be forced to manually reduce types before every comparison, with no
formal license to skip that step when types happen to already coincide.

### Grounding — this is `isDefEq`, named explicitly

This is one of the most direct correspondences in the whole book to modern
proof-assistant engineering. The Conversion rule *is* what Lean's kernel
calls **definitional equality** (`isDefEq`), and the second premise of
(conv) — checking $B'$ is itself well-formed before accepting the
conversion — is exactly why a kernel's defeq check must operate on
*type-correct* expressions, not arbitrary syntax. When Lean accepts a proof
term whose stated type differs syntactically from its expected type but the
two are definitionally equal, that acceptance step is a direct instance of
(conv). "This is exactly what `isDefEq` is doing" is the book's own
Subject-Reduction/Type-Reduction/Conversion diagram, restated in kernel
terms.

```lean
-- Sketch: a kernel accepting `e : A` where the expected type is `A'`
-- and A =β A′ (up to whnf/unfolding) is applying (conv) directly.
-- def check (e : Expr) (expected : Expr) : MetaM Unit := do
--   let inferred ← inferType e
--   unless (← isDefEq inferred expected) do
--     throwError "type mismatch: {inferred} vs {expected}"
```

In Rust, the analogous — much weaker — mechanism is `Deref` coercion or
associated-type normalization: the compiler will accept a value of type `T`
where `U` is expected if `T` normalizes to `U` under a fixed, decidable set
of rules. Rust deliberately keeps this normalization decidable and shallow
precisely because it has no general (conv)-style rule; a full conversion
rule over an unrestricted computation system is one reason dependently
typed kernels need careful termination/decidability arguments that Rust's
type checker avoids entirely by not having genuine type-level computation
with unbounded reduction.

---

## 6. Strong Normalisation

**Theorem (Strong Normalisation / Termination).** Every legal $M$ (in
$\lambda \! \to$, and again — with a much harder proof — in $\lambda C$) is
strongly normalising: there is no infinite $\beta$-reduction sequence
starting from $M$.

The book is candid that this is proved by exhibiting a measure on legal
terms that is always positive and strictly decreases with every
$\beta$-reduction step — details deferred to Barendregt (1992) and Geuvers
& Nederpelt (1994), because the real proof (usually via a reducibility /
saturated-sets argument) is one of the technically hardest results in the
book's development.

**Consequences, spelled out explicitly in §2.12**, are the payoff for all
the preceding machinery:

- **No self-application.** $MM$ can never be legal, because Uniqueness of
  Types plus the Generation Lemma would force $M$'s type to be a proper
  subexpression of itself — impossible for a well-founded type.
- **No untyped fixed-point combinator.** The untyped $Y$ combinator relies
  on self-application; it simply isn't typable in $\lambda \! \to$. This is
  the formal reason "every $\lambda$-term has a fixed point" (Chapter 1's
  striking, slightly alarming fact about the untyped calculus) fails once
  types are added — and it's presented as a trade-off, not a pure win:
  Remark 2.11.7 is explicit that strong normalisation guarantees
  termination but gives *no upper bound* on how long it takes.

### What breaks without this

Strong normalisation is precisely what a general-purpose (Turing-complete)
language *cannot* have — and precisely what a total, dependently typed
proof language (Lean's core calculus, Coq's, etc.) needs in order to use
"type-checking terminates" as a foundation for "proof-checking terminates."
Every simply typed or dependently typed calculus in this book pays for
strong normalisation by giving up general recursion (or requires it to go
through an explicit well-founded recursion / fixed-point *axiom*, checked
separately, rather than baking an unrestricted $Y$ into the calculus).

### Grounding

Rust's type system does not enforce termination of arbitrary Rust programs
(Rust is Turing-complete, deliberately) — but at the *type level*, Rust
carefully restricts trait resolution and const-generics to keep type-level
computation itself decidable and terminating, precisely to avoid the kind
of unbounded type-level reduction that a full (conv)-rule-plus-nontermination
combination would create. Lean's kernel, by contrast, requires *all* terms —
proofs and their types alike — to be strongly normalising by construction
(no unrestricted recursion in the kernel's core term language; recursion
goes through the strictly-positive-inductive-types + well-founded
recursion machinery, itself checked separately), which is exactly why
`#check` and `#eval` on a well-typed term are both guaranteed to terminate.

---

## 7. Decidability of type checking vs. undecidability of inhabitation

[[The-Simply-Typed-Lambda-Calculus#The three canonical problems|The three canonical problems]] (introduced in §2.6, restated as the closing
theorem of Chapter 6's metatheory survey) are:

$$
\begin{aligned}
\textbf{Well-typedness:} \quad & {?} \vdash \text{term} : {?} \\
\textbf{Type Checking:} \quad & \text{context} \vdash \text{term} \overset{?}{:} \text{type} \\
\textbf{Term Finding (Inhabitation):} \quad & \text{context} \vdash {?} : \text{type}
\end{aligned}
$$

In $\lambda \! \to$, **all three are decidable** (Theorem 2.10.10) —
syntax-directedness (the Generation Lemma) is exactly what makes this
possible: because each term-shape has one candidate rule, type inference can
be implemented as a straightforward recursive algorithm with no search.

By Chapter 6 (§6.3, Theorem 6.3.15), the picture for $\lambda C$ and its
subsystems sharpens into a genuine dichotomy: **Well-typedness and Type
Checking remain decidable** everywhere in the cube, but **Term Finding
(Inhabitation) is decidable only in $\lambda \! \to$ and $\lambda\omega$, and
undecidable in every other system in the cube** — including $\lambda 2$ and
$\lambda C$. The reason is not a technical accident; it's the **Curry–Howard
correspondence made unavoidable**: under propositions-as-types, finding a
term that inhabits type $M$ *is* finding a proof of proposition $M$. If
Inhabitation were decidable in $\lambda C$, you would have a general
algorithm for proving or refuting *any* mathematical proposition expressible
in the system — which is precisely what the Church–Turing Undecidability
Theorem rules out. The book states the moral directly: *"logic and
mathematics cannot be fully handed over to a machine that solves all
problems that you pose... humans formulate the types and human intervention
is also required to find inhabitants."*

### What breaks without this — and why the split is not arbitrary

This is the theoretical bedrock under every proof assistant's UX split:
`#check` (type checking — always terminates, always gives a definite
answer) versus tactic search / `exact?` / `apply?` (inhabitation search —
may run forever, may fail to find a proof that exists, is fundamentally a
best-effort semi-decision procedure). If Type Checking were undecidable, IDE
tooling (red squiggles under a type error) would be impossible in principle.
If Inhabitation *were* decidable, tactic-mode theorem proving as a
discipline would be replaced by a button.

### Grounding

This is a direct, load-bearing design constraint for a Rust-based
verifier/checker: whatever "logic-clause specification" checking you build
must live in the *Type Checking* column (decidable, checker-shaped), not the
*Term Finding* column (proof search, `undecidable in general` — you get a
semi-decision procedure at best, with the checker's own type-checking pass
remaining decidable regardless of how hard the search for a witness is).
In Lean, this dichotomy is exactly the boundary between the kernel (`isDefEq`
+ `infer`/`check`, decidable, small, trusted) and elaboration/tactics
(`exact?`, `apply`, unification-based metavariable resolution — a search
procedure that can fail to terminate or fail to find a term even when one
exists, and is *not* part of the trusted kernel). A meta-programming
elaborator resolving implicit arguments via metavariable unification is
squarely a Term-Finding-shaped problem — this is precisely why elaboration
needs heuristics (pattern unification, unification hints, backtracking) that
type checking itself never needs.

---

## Synthesis: where this leads

This chapter's cluster of lemmas is the connective tissue of the entire
book, not a self-contained topic to check off. Concretely:

- **Free Variables / Thinning / Condensing / Permutation** (§1) are used
  silently in essentially every later proof that manipulates contexts —
  including the definition-unfolding machinery of Chapters 8–9, where
  contexts grow to include *definitions*, not just variable declarations.
- **Generation and Substitution** (§§2–3) are the direct ancestors of the
  Generation Lemma and Substitution Lemma restated for $\lambda C$ (Chapter
  6, Lemmas 6.3.6 and 6.3.10) and, later still, for $\lambda D$ (Chapters
  9–10) — same shape, same proof strategy, extended context each time.
- **Confluence** (§4) is inherited essentially unchanged all the way to
  $\lambda D$, because — as the book stresses — types play no role in the
  definition of $\beta$-reduction, so the untyped Church–Rosser proof from
  Chapter 1 is doing double duty for the entire rest of the book.
- **Subject Reduction / Conversion / Uniqueness up to Conversion** (§5) is
  the piece that gets *re-derived*, not just inherited, at every rung of the
  Barendregt cube ($\lambda\omega$ in Ch. 4, $\lambda C$ in Ch. 6, $\lambda D$
  in Ch. 10) because each new system adds a new *kind* of reduction
  (type-level, definition-unfolding/$\delta$-reduction) that the conversion
  rule has to be widened to absorb.
- **Decidability vs. undecidability of the three canonical problems** (§7)
  is the fact that makes the rest of the book possible at all: every
  worked formalisation from Chapter 7 onward (logic, sets, arithmetic,
  Bézout's Lemma) is a *Term Finding* problem solved by a human, whose
  result is then mechanically *Type Checked* — the book's whole
  methodology rests on that asymmetry.

**Load-bearing for the standing project:** the Substitution Lemma and
context-validity machinery in §§1–3 are the direct prerequisite for
Hoare-triple-style soundness (substitution into a specification is only
sound because substitution is type/proposition-preserving — the same lemma,
applied to `Prop`-as-type judgements). The Conversion rule in §5 is the
book's own name for exactly what a Lean-style elaborator's `isDefEq` does,
and Uniqueness of Types up to Conversion is the metatheoretic fact that
makes definitional-equality checking well-defined rather than ambiguous.
The decidability split in §7 is the design boundary a custom automated
theorem prover has to respect: the *checker* must stay in the decidable
column no matter how undecidable the *search* for proofs is allowed to be.
