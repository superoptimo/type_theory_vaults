---
title: "Connecting Type Theory to First-Order Automation"
source: "11_ulf_norell_thesis_2007 — Towards a Practical Programming Language Based on Dependent Type Theory"
chapter: "Chapter 6, First-order Logic (pp. 125–152)"
tags: [type-theory, dependent-types, first-order-logic, resolution, proof-automation, unification, conservativity, agda]
---

# Connecting Type Theory to First-Order Automation

[[book-guidelines|↩ Back to guidelines]]

## Why this chapter exists: the tedium problem

Every interactive proof assistant has the same design tension. Dependent type theory gives you an extraordinarily expressive language for encoding proofs as terms — [[Dependent-Type-Theory-Foundations#Inductive families|inductive families]], propositions-as-types, definitional equality doing real work. But that expressiveness has a cost: even *trivial* reasoning steps (propositional shuffling, "substitute equals for equals," basic first-order consequence) have to be spelled out as explicit terms, one constructor application at a time. Meanwhile, first-order resolution provers are, by the mid-2000s, extremely good at exactly this kind of trivial reasoning — and useless at the high-level structuring (induction schemas, case splits, choosing which lemma to apply) that makes a proof *readable* as an argument rather than a search trace.

The obvious fix is to bolt a first-order prover onto the type checker: whenever a goal is "trivial," hand it to the automatic prover and keep the human-authored skeleton (inductions, case splits, lemma invocations) in the framework. Norell, together with Andreas Abel and Thierry Coquand, actually built this connection (published as [ACN05], reused here as Chapter 6) — but the *engineering* problem turns out to hide a serious *soundness* problem, and most of the chapter is about that soundness problem, not the plumbing.

**What breaks without care here:** naively piping type-theoretic goals through skolemization and clausal normal form to a resolution prover throws away *why* the search succeeded. Take
$$\forall x.\exists y.\forall z.\, R(x,y) \Rightarrow R(x,z)$$
Skolemize the existential ($y \mapsto f(x)$), negate, clausify — you get two unit clauses $\forall y.\, R(a,y)$ and $\forall y.\, \neg R(a, f(y))$ whose mutual contradiction a resolution prover finds instantly. But nothing about that refutation *looks like* the original statement anymore. If you dump a resolution-prover output as your "proof," you've traded an unreadable interactive proof for an unreadable automatic one. The chapter's actual contribution is a way to avoid this: restrict the fragment handed to the prover so that (a) no skolemization is ever needed, and (b) the resulting clausification is intuitionistically transparent, so the automatic proof genuinely *does* correspond to the informal argument a human would write.

This is the connective-tissue chapter of the thesis: it reuses the implicit-argument machinery from Chapter 3 (Metavariables) for notational sanity, and it deliberately sits in a *different* logical framework than the rest of the thesis — Martin-Löf's LF extended with propositions, called $MLF_{Prop}$, rather than $UTT_\Sigma$. Norell is explicit that the results should transfer to $UTT_\Sigma$ without difficulty; the reason for the separate framework is historical (this is joint work from a separate paper) not conceptual.

## 1. The logical framework $MLF_{Prop}$

### 1.1 Why a *separate* sort for propositions?

In $UTT_\Sigma$ (Chapter 1), propositions-as-types means a proposition just *is* a type in `Set`, and a proof just *is* a term of that type — there's no syntactic distinction between "ordinary data" and "proof." $MLF_{Prop}$ deliberately reintroduces that distinction with two new built-in sorts, `Prop` and `Prf`:

- `Set` — the universe of *data* type codes, with `El : Set → Type` decoding a code to the actual type (exactly the codes-and-decoding pattern from `Set`/`El` you'd expect from a Tarski-style universe).
- `Prop` — the universe of *proposition* codes, entirely separate from `Set`.
- `Prf : Prop → Type` — decodes a proposition code to its type of proofs, analogous to `El` but for propositions.

Why bother, if propositions-as-types already gives you proofs as terms? Because the whole automation scheme needs to identify, syntactically and without doing any type inference, *which* subterms of a goal are "logical structure" (to be shipped to the prover) versus "data" (to be left alone, matched up to `refl`/reflexivity rather than logical inference). Splitting `Set`/`El` from `Prop`/`Prf` at the syntax level makes that distinction free to read off, instead of requiring an oracle.

**Grammar** (preserving the book's notation exactly):

$$
\begin{aligned}
x,y,z &&& \text{variables}\\
c,f,p &&& \text{constants}\\
\hat c &::= \mathsf{Fun}\mid \mathsf{El}\mid \mathsf{Set}\mid ()\mid \mathsf{Prf}\mid \mathsf{Prop} && \text{built-in constants}\\
r,s,P,Q &::= \hat c \mid c \mid x \mid \lambda x. r \mid r\,s \mid \mathsf{let}\ x:T=r\ \mathsf{in}\ s && \text{expressions}\\
T,U &::= \mathsf{Set} \mid \mathsf{El}\, s \mid \mathsf{Prop} \mid \mathsf{Prf}\, P \mid \mathsf{Fun}\, T\, (\lambda x. U) && \text{types}\\
\Gamma &::= \cdot \mid \Gamma, x:T && \text{contexts}\\
\Sigma &::= \cdot \mid \Sigma, c:T \mid \Sigma, c:T=r && \text{signatures}
\end{aligned}
$$

`Fun T (λx.U)` is just $\Pi$-type notation spelled out as a constructor of the abstract syntax rather than infix sugar; the thesis writes $(x:T)\to U$ as shorthand for it, matching $UTT_\Sigma$'s notation from Chapter 1. There is no a priori syntactic distinction between terms and types — same unified `expressions` grammar as any PTS-flavored presentation.

Two definitions worth internalizing because the rest of the chapter is built on them:

- A **proof type** is a type of the shape $\Gamma \to \mathsf{Prf}\,P$ — a function returning a proof.
- A **set context** is a context $\Gamma = (x_1:T_1)\ldots(x_n:T_n)$ where every $T_i$ has the shape $\Delta \to \mathsf{El}\,S$ — i.e., every hypothesis is *data-typed*, not proof-typed. If $P:\mathsf{Prop}$ and $\Gamma$ is a set context, then $\Gamma \to \mathsf{Prf}\,P$ corresponds exactly to a first-order formula $\forall x_1 \ldots \forall x_n.\, P$ with a quantifier-free kernel — this is the type shape the translation to FOL targets.

**Rust/Lean grounding.** If you're building a Rust type checker, the `Set`/`Prop` split is the same move as distinguishing an `enum Sort { Type, Prop }` tag on your universe — Lean 4's kernel does exactly this: `Sort 0` (a.k.a. `Prop`) is proof-irrelevant and syntactically distinguishable from `Sort (u+1)` data universes, precisely so that the elaborator and downstream tooling (e.g. Lean's `simp`, or a hypothetical FOL bridge like this one) can cheaply tell "this subterm is logical scaffolding" from "this subterm is data" without doing full type inference. In your own compiler, if you ever want a similar automation hook (e.g. handing goals to an SMT solver), you'll want the same syntactic tag rather than relying on `Set`-vs-`Prop` being an emergent property you'd have to re-derive by inference every time.

### 1.2 Typing rules

Contexts, types, and terms are defined by five mutually-recursive judgments, all implicitly relative to a fixed signature $\Sigma$:

$$
\Gamma \vdash_\Sigma \qquad \Gamma \vdash_\Sigma T \qquad \Gamma \vdash_\Sigma r:T \qquad \Gamma \vdash_\Sigma T = T' \qquad \Gamma \vdash_\Sigma r = r' : T
$$

(well-formed context, well-formed type, typing, type equality, term equality). Term/type equality is generated by unfolding signature definitions plus $\beta$-, $\eta$-, and let-equality — nothing exotic, and decidable on normal terms exactly as in Chapter 1's bidirectional algorithm.

The one rule with real teeth is the side condition on function formation and introduction:

$$
\frac{\Gamma \vdash T \qquad \Gamma, x:T \vdash U}{\Gamma \vdash (x:T)\to U} \ (*) \qquad
\frac{\Gamma, x:T \vdash r:U}{\Gamma \vdash \lambda x. r : (x:T)\to U} \ (*)
$$

$$
(*)\text{: if } T \text{ is a proof type, then also } U.
$$

In words: **you may not build a function whose result type depends computationally on a proof argument.** This looks like an arbitrary restriction, but it's load-bearing for the whole scheme — see §3 below for exactly what breaks without it.

### 1.3 Natural deduction and the `fol` rule

Ordinary propositional/predicate connectives are added as an *extension* signature $\Sigma_{nd}$ (Figure 6.2 in the source) rather than being wired into the core theory — `∧`, `∨`, `⇒`, `¬` (defined as $\lambda P.\, P \Rightarrow \bot$), `⇔`, plus proof rules that are exactly the constructors and eliminators you'd write for these connectives as inductive types (`andI`, `andE₁`/`andE₂`, `orI₁`/`orI₂`, `orE`, `impI`, `impE`) and Leibniz-style typed equality `Id : (D:Set) → El D → El D → Prop` with `refl` and `subst`. Classical reasoning (needed once you bring resolution's law-of-excluded-middle-flavored reasoning back into the framework) lives in a further extension $\Sigma_{class} = \Sigma_{nd} + \mathrm{EM} : (P:\mathsf{Prop}) \to \mathsf{Prf}(P \lor \neg P)$.

One quiet but important addition: a constant $\varepsilon : (D:\mathsf{Set}) \to \mathsf{El}\,D$ is added to $\Sigma_{nd}$, forcing **every set to be non-empty**. This isn't optional bookkeeping — first-order logic's semantics assumes non-empty domains, so if the framework's `Set`s could be empty, the translation to FOL would be unsound. This becomes concretely important in §3 (Theorem 6.3.4's proof).

Now the actual bridge — a single new inference rule:

$$
\frac{\Gamma \vdash T}{\Gamma \vdash () : T} \ \mathsf{fol}, \quad \text{provided } \Gamma \vdash_{FOL} T
$$

`fol` says: if the side condition $\Gamma \vdash_{FOL} T$ holds — meaning $T$ is a proof type and an external first-order prover can derive the corresponding formula from $\Gamma$ — then the *single* proof term $()$ inhabits $T$. Crucially, $\Gamma \vdash_{FOL} T$ is a **side condition**, not part of type checking: it doesn't affect decidability of typing or of equality; the type checker can happily believe `fol` produced a proof of `⊥` and keep functioning (this gets exploited deliberately in the implementation, §4 below).

**Why does the theory need this rule to be conservative, and why is `()` always the same term?** Because the whole point of `fol` is: *the exact shape of the automatic proof doesn't matter to the rest of the program* — only that a proof exists. This is a proof-irrelevance move made concrete: `fol` collapses every automatically-discharged goal to the same placeholder term $()$, so two goals that are propositionally equal but proved by different resolution searches don't accidentally become *definitionally* unequal because their proof terms differ. But this is exactly where the $(*)$ side condition from §1.2 earns its keep — see below.

**What breaks without the $(*)$ restriction.** If you *removed* the constraint that a proof type can't be depended on computationally, you could write a function whose *result type* branches on which specific proof term you plugged in for a `Prf`-typed argument. Then, since `fol` always hands you the *same* term $()$ regardless of which proposition it proved, two calls to that function with two different (but both `fol`-proved) propositions could type-check as producing definitionally-equal results, even though replacing `fol` with the *actual* underlying proofs (which do differ per-goal) would make those two calls produce genuinely different, non-interchangeable terms. That's a soundness leak: conservativity (§3.5) would fail because comparing proof objects during type-checking would give an answer that changes depending on whether `fol` is present. Restricting function spaces so a proof-typed hypothesis can never affect a later *type* closes this leak — at the cost (which the thesis explicitly flags as "rather severe") of being unable to define a function that returns *data* under some propositional precondition without going through the extra ceremony. The thesis notes the real fix would be genuine **proof irrelevance** for `Prop`, left as future work.

## 2. Translating open formulas to first-order logic

### 2.1 What gets translated, and why only *this*

Only types of the exact shape

$$(x_1:T_1)\ldots(x_k:T_k) \to \mathsf{Prf}(P(x_1,\ldots,x_k))$$

are eligible for translation, where the $T_i$ come from a **set context** (data, not proofs) — and they go to an **open formula** $[P(x_1,\ldots,x_k)]$ with all the $x_i$ read as universally quantified. Example:

$$(x:\mathsf{El}\,\mathsf{Nat}) \to \mathsf{Prf}(\mathsf{Id}\,\mathsf{Nat}\,x\,x \land \mathsf{Id}\,\mathsf{Nat}\,x\,(\mathsf{add}\,\mathsf{zero}\,x)) \quad\leadsto\quad x = x \land x = \mathsf{add}\,\mathsf{zero}\,x$$

This is a *purely syntactic* translation over **normal** expressions (all definitions unfolded, all redexes reduced) — it never consults the type checker. Three syntactic classes are carved out:

$$
\begin{aligned}
t,u &::= x \mid f\,\vec t && \text{first-order terms}\\
A,B &::= p\,\vec t \mid \mathsf{Id}\,S\,t_1\,t_2 && \text{atoms}\\
W &::= A \mid W\ \mathrm{op}\ W' && \text{first-order formulæ}\\
\varphi &::= \Delta \to \mathsf{Prf}\,W && \text{translatable formulæ } (\Delta \text{ a set context})
\end{aligned}
$$

A subtlety that matters a lot later: a **proper term** is a first-order term that is *not just a bare variable*. The reason to name this: in a well-typed proper term, the types of its free variables are *uniquely determined by the term itself* (you can read off what type a variable must have just by seeing where it's used inside a proper term). A bare variable's type, by contrast, depends entirely on context — you can't recover it from the term alone. This asymmetry between "proper terms have self-evident typing" and "bare variables don't" is exactly what makes Lemma 6.3.1 (§3) work, and exactly why paramodulation *from* a bare variable has to be forbidden.

Formal term/variable constraints follow directly: a first-order term can contain no binder ($\lambda$ or `let`) and no applied variable (`x u` is disallowed) — anything of that shape simply isn't in the translatable fragment.

### 2.2 The translation itself

For a set context $\Delta = (x_1:T_1)\ldots(x_n:T_n)$, a type $\varphi := \Delta \to \mathsf{Prf}\,W$ translates to $[\varphi] = \forall x_1\ldots\forall x_n. [W]$, with $[W]$ and $\langle t \rangle$ (term translation) defined by mutual recursion, **relative to $\Delta$**:

$$
\begin{aligned}
[W_1 \ \mathrm{op}\ W_2] &:= [W_1]\ \mathrm{op}\ [W_2] \\
[\mathsf{Id}\,S\,t_1\,t_2] &:= \langle t_1\rangle = \langle t_2\rangle && \text{typed equality} \to \text{untyped FOL equality}\\
[p\,t_1\ldots t_n] &:= p(\langle t_1\rangle,\ldots,\langle t_n\rangle) \\
\langle x_i\rangle &:= x_i && x_i \in \Delta\\
\langle x\rangle &:= c_x && x \notin \Delta \ \text{(free var. becomes a FOL \emph{constant})}\\
\langle c\rangle &:= c \\
\langle f\,t_1\ldots t_n\rangle &:= f(\langle t_1\rangle,\ldots,\langle t_n\rangle)
\end{aligned}
$$

with FOL function applications $f(t_1,\ldots,t_n)$ elaborated internally to a fixed binary `app` symbol (curried application encoded first-order-ly, exactly the trick you'd use if you were compiling a curried Rust closure representation down to a fixed-arity target IR).

Two, and *only* two, places where this isn't a naive structural homomorphism:

1. **Typed equality collapses to untyped equality** — `Id S t1 t2` drops the type index `S` entirely on the FOL side. This is safe *only* because well-typed proper terms carry their type information implicitly (per §2.1) — but it's also exactly the mechanism that needs Lemma 6.3.1's care.
2. **Free (outer-bound) variables become constants** — a variable bound *outside* the formula being translated ($x \notin \Delta$) is opaque to the first-order prover; it's just some fixed, unanalyzable individual $c_x$.

This whole scheme is what the thesis calls **implicit typing** (crediting Beeson [Bee07] and Wick & McCune [WM89] as prior art for the idea, in ordinary — non-dependent — type theory): instead of tagging every FOL term with type annotations (which would make proofs unreadable and bloat the search space), you *erase* the types and rely on the fact that, in this restricted fragment, types are recoverable from term shape alone. That recoverability is precisely what Lemma 6.3.1 formalizes and needs.

### 2.3 Geometrical formulas: buying intuitionistic validity

A further-restricted subclass, **geometrical formulas**, is introduced:

$$
G ::= H \mid H \to G \mid G \land G \qquad H ::= A \mid H \land H \mid H \lor H
$$

i.e., implications and conjunctions of "positive" formulas ($H$: conjunctions/disjunctions of atoms only, no negation, no nested implication on the left of an implication). The payoff: **classical, first-order resolution proofs of geometrical formulas can be mapped to *intuitionistic* proofs in the framework.** For general open formulas this isn't automatic — the thesis gives the canonical counterexample: $\neg P \lor Q$ is *not* intuitionistically equivalent to the clause $P \Rightarrow Q$ (classically they coincide; intuitionistically, converting between disjunctive and implicational form for negated disjuncts requires excluded middle). Since clausification silently performs exactly this kind of conversion, an unrestricted open formula's resolution proof might smuggle in a classical step you can't intuitionistically justify — but restricting to the geometrical fragment rules this out by construction (this is the content of Theorem 6.3.4, §3 below).

## 3. The resolution/paramodulation calculus and its restriction

### 3.1 Clauses, in Gentzen sequent notation

A clause is written $X \Rightarrow Y$ (sets of atoms $X$, $Y$) rather than the usual disjunctive-normal-form $\neg A_1 \lor \cdots \lor \neg A_n \lor B_1 \lor \cdots \lor B_m$ — same content, sequent-flavored presentation, chosen because it reads directly as an intuitionistic implication (empty $X$ = truth, empty $Y$ = absurdity). This isn't a cosmetic choice: writing clauses as sequents is *precisely* what lets the calculus's rules be stated so that each one is individually intuitionistically valid (footnote 3 in the source: "in the standard formulation, the `ax` rule would read $\neg A \lor A$" — literal excluded middle — "our" formulation instead reads $A \Rightarrow A$, which needs no classical principle at all).

The four rules (Figure 6.3):

$$
\frac{}{A \Rightarrow A}\ \mathsf{ax} \qquad
\frac{X \supseteq X' \quad X' \Rightarrow Y' \quad Y' \subseteq Y}{X \Rightarrow Y}\ \mathsf{sub}
$$

$$
\frac{X_1 \Rightarrow Z_1, Y_1 \qquad X_2, Z_2 \Rightarrow Y_2}{(X_1,X_2 \Rightarrow Y_1,Y_2)\sigma}\ \mathsf{res}, \quad \sigma = \mathrm{mgu}(Z_1,Z_2)
$$

$$
\frac{}{\cdot \Rightarrow x = x}\ \mathsf{refl} \qquad
\frac{X_1 \Rightarrow t=u, Y_1 \qquad X_2[t'] \Rightarrow Y_2[t']}{(X_1,X_2[u] \Rightarrow Y_1,Y_2[u])\sigma}\ \mathsf{para}, \quad \sigma = \mathrm{mgu}(t,t')
$$

`sub` (weakening/subsumption) is only ever needed as the *very last* step of any derivation — every resolution proof can be normalized so `sub` appears at most once, at the end. `res` is standard binary resolution: unify the two clashing atoms $Z_1$/$Z_2$ across two clauses, combine what's left. `para` is paramodulation (equality-substitution): if you've derived an equation $t=u$ and separately have a clause mentioning $t'$ somewhere, and $t$ unifies with $t'$, you can rewrite that occurrence to $u$.

**The one restriction that makes everything sound:** the thesis defines **restricted paramodulation** as the version of `para` where **both $t$ and $t'$ must be proper terms** (never bare variables). This single side condition is doing all of the soundness work in the rest of the chapter.

**What breaks without the restriction — concretely.** Consider a signature

$$\mathsf{Nat}:\mathsf{Set} \qquad \mathsf{zero}:\mathsf{El}\,\mathsf{Nat} \qquad h : (x:\mathsf{El}\,\mathsf{Nat}) \to \mathsf{Prf}(\mathsf{Id}\,\mathsf{Nat}\,x\,\mathsf{zero}) \qquad A:\mathsf{Set} \qquad a:\mathsf{El}\,A$$

`h`'s type translates to $x = \mathsf{zero}$ in FOL — a formula whose only free variable is the *universally quantified* $x$. If unrestricted paramodulation from that bare variable $x$ were allowed, you could rewrite an occurrence of some other variable that happens to unify with $x$ under an *unsound* substitution — concretely, paramodulating from the variable $x$ in $x=\mathsf{zero}$ lets you derive $a = \mathsf{zero}$, even though $a : \mathsf{El}\,A$ and $\mathsf{zero}:\mathsf{El}\,\mathsf{Nat}$ live in *entirely different sets* — a statement that is not just false but doesn't even *type-check* back in the framework. Forbidding paramodulation from a variable rules this out. (Implementation footnote: Otter permits it, Gandalf's earlier versions didn't and later versions added it back for completeness — in the thesis's own experiments this restriction never bit.)

### 3.2 Lemma 6.3.1 — the technical crux

> **Lemma 6.3.1.** If two proper first-order terms $t_1, t_2$ over disjoint variables are well-typed and unifiable, then their most general unifier $\mathrm{mgu}(t_1,t_2)$ is well-typed.

This is *the* load-bearing lemma of the whole chapter. Recall §2.1: a proper term's variables have their types uniquely determined by the term's shape. The proof runs a standard structural unification algorithm and shows well-typedness is preserved at every step:

- If both sides are proper ($f(a_1,\ldots,a_k)$ vs. $f(b_1,\ldots,b_k)$ — note they must share head symbol $f$, since $f$'s type pins down the arity/shape), decompose to $a_i = b_i$ subproblems — well-typedness is inherited componentwise.
- If one side is a bare variable $x$ not occurring in the other side $u_1$: since $u_1$'s variables' types are self-determined by $u_1$ alone (proper-term property again), you can always reorder the context so those variables come *before* $x$, substitute $x := u_1$ into everything after, and recurse on a strictly smaller problem.

Worked example straight from the source: $\mathsf{add}\,x\,\mathsf{zero}$ and $\mathsf{add}\,(\mathsf{suc}\,y)\,z$ are well-typed, proper, unifiable, and their mgu $\{x \mapsto \mathsf{suc}\,y,\, z \mapsto \mathsf{zero}\}$ is well-typed.

**Rust/Lean grounding — this is literally your elaborator's unification, minus the pattern-fragment restriction.** If you've internalized Miller pattern unification (metavariable applied to distinct bound variables ⇒ unique, computable solution), Lemma 6.3.1 is solving a *different* but structurally adjacent problem: here there are no metavariables at all — every symbol is a rigid constant or a genuinely universally-quantified variable — and the thing being proved is that *ordinary* first-order (Robinson) unification, restricted to *proper* terms, never produces an ill-typed substitution. The reason this is even a question worth proving is that the *types have been erased* (§2.2) before unification runs; Lemma 6.3.1 is exactly the statement "erasure was safe because it's invertible on this fragment." If you build a Rust checker that ever erases types before shipping a subproblem to an untyped solver (a common move — e.g. feeding a monomorphic core to an SMT solver), you need an analogous invertibility argument, and this lemma is a clean template for how to structure that proof: reduce to "the substitution I recover from the untyped solver, replayed through the erasure-inverse, is well-typed by structural induction on the unification trace."

### 3.3 Lifting resolution steps, and the conservativity theorem

**Lemma 6.3.2** lifts Lemma 6.3.1 from single unification steps to whole resolution/paramodulation inferences: if two derivable clausal types (types that translate to a clause) resolve or restricted-paramodulate to clause $C$, then there's a context $\Gamma$ and a derivable framework type $\Gamma \to \mathsf{Prf}\,W$ with $C = [W]$ — and $\Gamma$ stays a set context if the inputs were set contexts. In other words: **every legal step of the resolution calculus corresponds to an actual, well-typed derivation step back in $MLF_{Prop}$.**

From there, two theorems, each strictly stronger given a stronger hypothesis on the input formulas:

> **Theorem 6.3.3.** If $[\varphi]$ is derivable from $[\varphi_1],\ldots,[\varphi_k]$ by resolution + restricted paramodulation, then $\varphi$ is derivable from $\varphi_1,\ldots,\varphi_k$ in *any* extension of $\Sigma_{class}$.

(Classical, because clausifying a general open formula into conjunctive-clause form can itself require excluded middle, per §2.3.)

> **Theorem 6.3.4.** Same hypothesis, but restricted to *geometrical* formulas $\varphi,\varphi_1,\ldots,\varphi_k$ ⟹ the derivation lives in any extension of $\Sigma_{nd}$ — **intuitionistically**, no excluded middle needed.

Theorem 6.3.4's proof leans on set-context inhabitedness (the $\varepsilon$ constant from §1.3) in a genuinely subtle way: with $D:\mathsf{Set}$, $P:\mathsf{Prop}$ ($x$ not free in $P$), both $\varphi_1 = (x:\mathsf{El}\,D)\to\mathsf{Prf}\,P$ and $\varphi_2 = \mathsf{Prf}\,P$ translate to the *same* FOL formula $[\varphi_1]=[\varphi_2]=P$ — but deriving $\varphi_2$ from $\varphi_1$ inside the framework is only valid *because* $\mathsf{El}\,D$ is guaranteed inhabited (otherwise a vacuously-true universal over an empty domain wouldn't license instantiating away the quantifier).

Both theorems assemble into the chapter's headline result:

> **Theorem 6.3.5 (Conservativity).** If a type is inhabited in $MLF_{Prop} + \mathsf{fol} + \Sigma_{class}$, then it is inhabited in $MLF_{Prop} + \Sigma_{class}$.

Proved by induction on the typing derivation, invoking Theorem 6.3.3 at every use of `fol`. This is the metatheorem promised in the introduction: **it's not merely that we *believe* the automatic prover — every time it succeeds, there provably exists an actual framework-native proof term**, and the proof of the theorem is *constructive*: it doesn't just assert existence, it hands you an algorithm for producing that term by replaying the resolution trace as framework inference steps. So `fol` is never a trust-me black box; it's a checked shortcut that's always, in principle, redeemable for a real proof.

**Load-bearing for the reader's own project.** This is the piece of the chapter that generalizes furthest beyond FOL specifically. Any time you build a "trusted external oracle" bridge into a verifier — an SMT call discharging a Hoare-triple side condition, a Horn-clause solver returning an invariant, a CHC engine proving unreachability — the *shape* of the soundness argument you need is exactly Theorem 6.3.5's shape: (1) restrict the fragment you hand the oracle to one where the erasure/encoding step is provably invertible (this chapter's Lemma 6.3.1 analog), (2) show each oracle-internal inference step lifts to a step in your trusted kernel's proof language (Lemma 6.3.2 analog), (3) conclude by induction that oracle-assisted derivability implies kernel derivability (Theorem 6.3.5 analog). This is precisely the "proof-producing architecture" pattern: the oracle can be as untrusted and as fast as you like, because the *kernel* never actually trusts it — it trusts the metatheorem that says the oracle's answers are always replayable.

### 3.4 Worked examples: induction stays in the framework, algebra leaves it

Two small examples cement the intended division of labor. First, natural-number induction (signature in Figure 6.4: `Nat`, `zero`, `suc`, `indNat`, plus recursive `add` axioms `addZero`/`addSuc`). Proving $(x:\mathsf{El}\,\mathsf{Nat}) \to \mathsf{Id}\,\mathsf{Nat}\,(\mathsf{add}\,\mathsf{zero}\,x)\,x$ uses `indNat` explicitly at the framework level:

$$\mathsf{indNat}\ (\lambda x.\, \mathsf{Id}\,\mathsf{Nat}\,(\mathsf{add}\,\mathsf{zero}\,x)\,x)\ ()\ (\lambda a.\, \mathsf{impI}\,(\lambda\mathit{ih}.\ ()))$$

— note the two `()`s are literally `fol` placeholders standing in for the base case $\mathsf{add}\,\mathsf{zero}\,\mathsf{zero} = \mathsf{zero}$ (a one-step rewrite via `addZero`) and the step case $\mathsf{add}\,\mathsf{zero}\,(\mathsf{suc}\,a) = \mathsf{suc}\,a$ (a one-step rewrite via `addSuc` and the induction hypothesis) — both dischargeable by the FOL prover with zero framework-level ceremony. This is the whole thesis of the chapter in miniature: *induction is a framework-level structural decision (which schema, on which variable), the resulting subgoals are framework-level-free first-order consequences.*

Second, a small but pointed example (Warshall's-algorithm correctness fragment): a *higher-order* operation `F : El D → (El D → El D → Prop) → El D → El D → Prop` can still have some of its *instantiated, unfolded, first-order-shaped* consequences discharged by the FOL prover — the translation only inspects the *normal form* of the goal, so as long as unfolding `F` produces something in the translatable fragment, the higher-order machinery used to *define* the goal is irrelevant to whether it's automatable.

## 4. Implementation: implicit arguments, plug-ins, and the FOL plug-in

### 4.1 Implicit arguments make the notation survivable

Fully explicit $MLF_{Prop}$ notation is nearly unreadable — associativity of composition (Figure 6.5) requires spelling out four `Set` arguments by hand at every use site. The chapter reuses Chapter 3's implicit-argument mechanism, writing `x (Δ) : T` for "`x` has type `Δ → T` with `Δ` implicit," resolved at each use site via **pattern unification** [Mil92] — explicitly *more restricted* than the general [[Metavariables-and-Implicit-Arguments|implicit arguments]] of §3.6 of the thesis, because here every implicit instantiation must be recoverable by pattern unification specifically, not general higher-order constraint solving. With implicits, associativity shrinks to something you'd actually want to read:

```
assoc (A B C D : Set) :
     (f : El C → El D, g : El B → El C, h : El A → El B) →
     Prf (f ◦ (g ◦ h) == (f ◦ g) ◦ h)
```

The conjecture (left open) is that conservativity extends to *omit* implicit arguments from the FOL translation too, when they're inferable from the resulting first-order term — preserving the crucial "well-typed proper term ⟹ unique typing" property that Lemma 6.3.1 needs. This is flagged as working for the thesis's specific style of implicits but doubtful for others (e.g. implicit dictionaries for overloading) — a useful cautionary note if you're designing your own implicit-argument-erasure story: erasure being *sound* depends on the specific inference discipline, not just on "the information happens to be redundant."

### 4.2 The plug-in mechanism: a general escape hatch

Rather than hard-wiring the FOL connection into the type checker, the implementation factors it through a **general plug-in interface** — a genuinely reusable architectural pattern:

- a plug-in supplies a **type-checking function**, invoked on particular goals during elaboration (via a new expression form `name-plugin(s₁,…,sₙ)`, arguments passed through *unchecked* — a plug-in may receive ill-typed terms and is responsible for checking them itself if it needs to);
- and a **finalization function**, run once, *after* type checking completes, that actually solves whatever constraints the plug-in accumulated during the type-checking pass.

This two-phase split (collect-then-solve) is the same architectural move you'd make separating **constraint generation** from **constraint solving** in a bidirectional elaborator with metavariables (Chapter 3's guarded constants do exactly this for unification constraints) — here it's reused for an entirely different external system, which is the point: *the plug-in interface doesn't care what's on the other side.* A model checker, a Presburger-arithmetic decision procedure (both mentioned explicitly as future plug-ins), or — for the reader's own compiler project — a CHC solver or an abstract-interpretation-based invariant generator could all be wired in through the identical two-phase protocol, provided each is accompanied by its own conservativity metatheorem in this chapter's style.

### 4.3 The FOL plug-in specifically

The built-in `fol`-rule's placeholder `()` is *replaced by a call to the plug-in* in the implementation — same idea, wired through the general mechanism rather than being a special case. Its typing rule:

$$
\frac{\Gamma \vdash \varphi \qquad \Gamma \vdash s_1:\varphi_1\ \ldots\ \Gamma \vdash s_n:\varphi_n}{\Gamma \vdash \mathsf{fol\text{-}plugin}(s_1,\ldots,s_n):\varphi}\ \varphi_1,\ldots,\varphi_n \vdash_{FOL} \varphi
$$

Two design decisions here are worth flagging as *deliberate engineering choices*, not incidental details:

1. **Decidability of type checking never depends on validity of the FOL side condition.** "Nothing will break if the type checker is led to believe that there is an $s : \mathsf{Prf}\,\bot$" — i.e., type checking is decoupled entirely from proof search correctness, and is cheap; proof search is expensive and can be deferred. Concretely: the plug-in's type-checking function only checks that the goal is *translatable* and the arguments are well-typed proofs of translatable formulas — it stashes the actual obligation $\varphi_1,\ldots,\varphi_n \vdash_{FOL} \varphi$ and only *discharges* it in finalization, by clausifying and invoking Gandalf with a time limit. This separation — "can I even ask this question" (cheap, always decidable) vs. "is the answer yes" (expensive, possibly slow or failing) — is a pattern worth keeping in mind for any checker embedding an external decision procedure: never let the *existence* of an obligation block or complicate the core typing algorithm's decidability.
2. **Explicit lemma-passing instead of dumping the whole context.** The plug-in is deliberately *not* handed the ambient context automatically — the user must name exactly which axioms/lemmas ($s_1,\ldots,s_n$) are relevant to a given goal. This is a usability call as much as a technical one: an unfiltered context would "overwhelm the prover" with irrelevant hypotheses, and the thesis is candid that the plug-in is meant "for simple goals where you already have an idea of the proof" — automation as a local tactic, not as a search over the entire proof state.

## 5. Examples: what actually gets automated

Three worked case studies (§6.5) show the intended usage pattern, and are worth reading as templates:

- **Relational algebra** — symmetry of transitive closure, defined via a monotone chain $R^{(n)}$ of approximations. Induction over $n$ (framework-level, via `indNat`) with both base and step case dispatched to `fol-plugin`. The chapter reproduces Gandalf's actual pretty-printed proof trace for the step case — a twelve-line linear resolution derivation that, read informally, is essentially the pen-and-paper argument a human would give (chase through the recursive characterization of $R^{(n)}$, apply symmetry, contradiction). This is the chapter's concrete evidence for its central design claim: *automated proof traces that stay readable because the fragment was restricted up front.*
- **Category theory** — proving that if $g \circ f = h \circ f$-implies-$g=h$ is epi-composed-with-$k$, then $f$ alone is epi. Pure equational/associativity shuffling — exactly the kind of "tedious but trivial" reasoning motivating the whole chapter — resolved by Gandalf in six lines that again read essentially as the natural hand-proof.
- **Computer algebra** (after M. Beeson) — nilpotency implies zero in an integral ring. This example is the richest: it interleaves `fol-plugin` calls for local algebraic facts (`lemCancel`, `lemZero`, `lemOneZero`) with explicit framework-level induction (`lemMain`, built via `indNat` with `fol-plugin`-proved base and step), and a final `existsE`-based unwrapping of the existential witness for "some power of $x$ is zero." This is the clearest illustration of the intended workflow: **the human writes the proof skeleton — which lemmas, which induction, which existential witness to extract — and the prover fills in the algebra between the joints.**

## Where this leads

Chapter 6 is architecturally a side branch of the thesis — it doesn't feed the pattern-matching (Ch. 2), metavariable (Ch. 3), or module (Ch. 4) machinery, and Agda-the-language (Ch. 5) doesn't actually include this FOL connection ("this implementation is not the same as [[The-Agda-Language|the Agda language]] from Chapter 5," the chapter says explicitly). But it reuses Chapter 3's implicit-argument/pattern-unification machinery for notation, and its central methodological move — *restrict a fragment until an erasure step becomes provably invertible, then get a metatheorem for free* — is the same move that makes Chapter 3's guarded-constants soundness argument work, just applied to an external prover instead of an internal unifier.

For the standing project (a Rust dependent/refinement-type compiler with an embedded automated prover): this chapter is close to a direct blueprint for the "trusted kernel talks to an untrusted external solver" boundary that any CHC-, SMT-, or abstract-interpretation-backed verification condition discharger will need. Concretely:

- The `Set`/`Prop` separation with the $(*)$ no-type-depends-on-a-proof restriction is the cheapest available discipline for keeping proof-irrelevant automation from leaking into type-level computation — worth considering even outside a first-order-logic-specific bridge, e.g. for a refinement-type system where a Hoare-triple side condition is discharged by SMT and must not be allowed to influence what a later type *is*.
- Lemma 6.3.1 (well-typedness preserved under unification of erased/untyped terms) is the exact proof obligation you'll face wiring an untyped SMT term representation back to a typed refinement-type checker — the "proper term ⟹ unique typing" argument generalizes directly.
- The two-phase plug-in protocol (cheap, always-decidable type checking; deferred, possibly-failing constraint discharge at finalization) is the right shape for embedding a CHC/SMT solver into a bidirectional elaborator without compromising the elaborator's own decidability guarantees.
- The conservativity-theorem pattern (§3.3) is the template for the soundness argument your compiler will eventually need to state and prove for *its own* embedded prover, however it ends up implemented.
