---
title: "The Formal System of Type Theory (TT0)"
source: "Type Theory and Functional Programming — Simon Thompson (1999)"
chapter: "Chapter 4, Introduction to Type Theory — §4.2, §4.3, §4.4 (pattern), §4.10, §4.11 (pp. 67, 70–83, 108–124)"
tags: [type-theory, judgements, curry-howard, identity-type, convertibility, substitution, martin-lof]
---

[[book-guidelines|↩ Back to guidelines]]

# The Formal System of Type Theory ($TT_0$)

## Why a proof system needs its own grammar of rules

Chapter 1 of Thompson's book gave you natural deduction the ordinary way: rules that derive judgements of the form "$A$ is valid." That system tells you *whether* a proposition holds, but it throws away the *evidence*. [[Constructive-Mathematics|Constructive mathematics]] (Chapter 3) refuses to do that — a proof of $A \lor B$ has to tell you which disjunct holds and hand you a witness, not just certify validity in the abstract.

So the very first move in Chapter 4 is a change of judgement form. Instead of "$A$ is valid," Thompson derives statements of the form

$$p : P$$

read as "$p$ is a proof of the proposition $P$." This single notational shift is what makes the rest of the chapter possible: once proofs are named, syntactic objects, you can compute with them, simplify them, and — crucially — read the very same rules a second time as a specification of a typed functional programming language, with $p:P$ now read "$p$ is a member of the type $P$." That is the Curry–Howard correspondence, and this article is about the scaffolding that carries it: what a *judgement* is, what the four kinds of rule attached to each type former do, how equality gets internalized as a type of its own, and how the whole system's notion of "these two expressions are the same" (convertibility) is wired into the rules via substitution. This is the load-bearing formal apparatus of $TT_0$ — the specific type formers (booleans, naturals, quantifiers) are separate topics; here we're after the shape of the machine that generates and glues them together.

If your target is a Rust verifier or a Lean-style elaborator, this is close to the most important article in the whole book: judgement forms are what a type checker checks, and convertibility-via-substitution is exactly the machinery behind `isDefEq`.

## Judgements, proofs, and derivations (§4.2)

**What breaks without this distinction:** if you don't separate "the object language" (propositions and proofs, or types and programs) from "the meta-language that reasons about it" (rules that produce judgements), you can't talk cleanly about *how* a proof was built, only *that* it exists. Thompson makes the separation explicit:

> "proofs and propositions form the object language; derivations are the means by which we infer judgements concerning the object language."

A rule like conjunction-introduction is now written with proof objects attached to each premise and conclusion:

$$\dfrac{p:A \quad q:B}{(p,q):(A\land B)}\ (\land I)$$

Read it as: given a derivation of $p:A$ and a derivation of $q:B$, you may derive $(p,q):(A\land B)$ — and the pairing operation $(p,q)$ is not incidental bookkeeping, it *is* the proof. Elimination undoes this:

$$\dfrac{r:(A\land B)}{fst\ r:A}\ (\land E_1) \qquad \dfrac{r:(A\land B)}{snd\ r:B}\ (\land E_2)$$

and Thompson works a small derivation to show how these combine — deriving $(snd\ r, fst\ r):(B\land A)$ from $r:(A\land B)$ by chaining $(\land E_2)$, $(\land E_1)$, and $(\land I)$. A **derivation** is exactly this: a tree built by repeated rule application, whose root is the judgement being established and whose leaves are assumptions or axioms.

Some rules also involve a second judgement form, "$A$ is a formula" (later "$A$ is a type"), needed because you can only sensibly assume $x:A$ once you know $A$ is well-formed. This gives the **[[The-Curry-Howard-Isomorphism-(Propositions-as-Types)#Rule of Assumption|Rule of Assumption]]**:

$$\dfrac{A\ is\ a\ formula}{x:A}\ (AS)$$

— assumptions don't sit at the leaves for free; they're licensed by a prior derivation that the type itself makes sense.

**Grounding (Rust).** A judgement $p:P$ is precisely what a type checker's core relation `check(ctx, term, ty) -> bool` or `infer(ctx, term) -> Ty` computes — except here the "term" being checked is simultaneously a candidate proof. A derivation tree is the call tree of your recursive `check`/`infer` functions; each rule is one match arm. Rust's own trait-resolution engine derives judgements of the shape "type $T$ implements trait $Tr$" using an analogous inductive rule system (blanket impls play the role of a formation/introduction pair).

**Grounding (Lean).** This is the literal ancestor of Lean's `Expr` typing judgement, `Γ ⊢ e : T`. Lean's kernel `infer`/`check` functions are, structurally, an implementation of exactly this rule system, generalized to dependent types.

## The four-rule pattern (§4.3, illustrated via $\land$, $\Rightarrow$, $\lor$, $\bot$)

Thompson's key organizing decision — the one that recurs for *every* type former in the book — is that each connective/type comes with exactly four kinds of rule:

1. **Formation** — the syntax rule: under what conditions is this a well-formed type at all?
2. **Introduction** — how do you construct (prove) a member of the type?
3. **Elimination** — what can you do with (extract from) a member of the type, and — read as a "closure" rule — what does *every* member of the type look like?
4. **Computation** — how do introduction and elimination cancel: what happens when you eliminate something you just introduced?

Worked in full for conjunction:

$$\dfrac{A\ is\ a\ type \quad B\ is\ a\ type}{(A\land B)\ is\ a\ type}\ (\land F)$$
$$\dfrac{p:A \quad q:B}{(p,q):(A\land B)}\ (\land I) \qquad \dfrac{r:(A\land B)}{fst\ r:A}\ (\land E_1)\quad \dfrac{r:(A\land B)}{snd\ r:B}\ (\land E_2)$$
$$fst\ (p,q)\to p \qquad snd\ (p,q)\to q \quad (\land\,\text{computation})$$

The pattern repeats for $\Rightarrow$ — introduction is $\lambda$-abstraction (discharging an assumption $[x:A]$), elimination is application, and computation is exactly $\beta$-reduction:

$$\dfrac{[x:A]\atop{\vdots\atop e:B}}{(\lambda x:A).e:(A\Rightarrow B)}\ (\Rightarrow I) \qquad \dfrac{q:(A\Rightarrow B)\quad a:A}{(q\ a):B}\ (\Rightarrow E) \qquad ((\lambda x:A).e)\,a \to e[a/x]$$

— and for $\lor$ (introduction tags a proof with `inl`/`inr`; elimination is `cases`, taking a proof of $A\lor B$ plus a handler for each side) and for $\bot$, which gets a formation rule and an elimination rule (`abort`, *ex falso quodlibet*) but **no introduction rule at all** — there is deliberately no way to construct a proof of falsity, and no computation rule either, since there's nothing to simplify from an object you can never build.

Introduction and elimination are formal duals: introduction says "here is *one way* to build a member"; elimination says "*every* member looks like this" — i.e., elimination is the exhaustiveness/closure guarantee. Thompson flags this duality explicitly and returns to it formally in §8.4 ([[The-Inversion-Principle|the Inversion Principle]], where elimination and computation rules are mechanically *derived* from introduction rules).

**What breaks without computation rules specifically:** formation + introduction + elimination alone gives you a *static* type system — it tells you which expressions are well-typed, but nothing about running them. It's the computation rules that turn the system into a programming language with an evaluation semantics, and — read on the logic side — a notion of proof simplification. This is also, not coincidentally, why the identity type (below) is disruptive: it's the point where the "static" (formation/typing) and "dynamic" (computation/reduction) readings stop being cleanly separable.

**Grounding (Rust).** Formation is your type declaration (`enum Either<A,B>`); introduction is the constructors (`Either::Left`, `Either::Right`); elimination is `match`; computation is what the compiler actually reduces `match Either::Left(x) { Left(y) => f(y), Right(z) => g(z) }` to (`f(x)`) at evaluation. The four-rule pattern is literally "define an ADT, define its constructors, define pattern matching over it, define what matching a freshly-constructed value reduces to" — this is worth internalizing early since it's the shape you'll reuse for every dependent type former the book introduces later (§4.6 quantifiers, §4.7–4.9 base types).

**Grounding (Lean).** Lean's `inductive` command auto-generates exactly formation (the type), introduction (constructors), and a computation principle (`Eq.mpr`/definitional unfolding of pattern matches via the recursor); the *elimination* rule is the generated recursor/eliminator (`Either.rec`), and `match` is sugar compiling down to it. When you write a Lean inductive type, you are writing all four Thompson rules at once, just under different names.

## The identity (equality) type — the first genuinely dependent formula (§4.10)

**What problem this solves.** Up to this point, every rule in the system has zero free-standing atomic predicates — there are no primitive formulas containing free variables to build on. To get anything resembling ordinary mathematics (or a program invariant like "the array stays sorted"), you need some primitive notion of equality between two elements *of a type*, expressed *inside* the system as a proposition with its own proof objects. That's what the identity type $I(A,a,b)$ (written $a=_A b$) supplies.

**Formation — and why it breaks the pattern.** Every formation rule so far had the shape "…is a type, …is a type $\Rightarrow$ …is a type," decoupled from which particular elements inhabit those types. Identity types can't do that:

$$\dfrac{A\ is\ a\ type \quad a:A \quad b:A}{I(A,a,b)\ is\ a\ type}\ (IF)$$

Formation now depends on *typed premises* — on there already being derivations $a:A$, $b:A$. This is exactly the point Thompson flags as breaking the earlier clean separation of "syntax" (formation) from "derivation" (typing): from §4.10 on, you cannot decide what counts as a well-formed formula without already having derivability judgements about specific terms. This single rule is why the book abandoned the idea of specifying the grammar of types by a separate BNF up front (foreshadowed as early as §4.3).

**Introduction — reflexivity, and nothing else.** The only primitive way to inhabit $I(A,a,b)$ is to already have $a$ and the *same* $a$:

$$\dfrac{a:A}{r(a):I(A,a,a)}\ (II)$$

$r(a)$ has no internal structure — it just witnesses "$a$ is equal to itself." That triviality is deceptive: everything else (symmetry, transitivity, substitution of equals) has to be *derived* from this one rule plus elimination.

**Elimination — Leibniz's law as a formal rule.** The intuitive content of equality is "equals can be substituted for equals" (Leibniz's law). Thompson encodes this as an elimination rule that lets a family of formulas $C$ (which may itself mention the equality proof) transport a proof from one side of an equation to the other:

$$\dfrac{c:I(A,a,b) \quad d:C(a,a,r(a))}{J(c,d):C(a,b,c)}\ (IE)$$

and proves Leibniz's law as **Theorem 4.4**: instantiate $C(a,b,c) \equiv_{df} P(b)$; given $d:P(a)$ (i.e. $d:C(a,a,r(a))$) and $c:I(A,a,b)$, conclude $J(c,d):P(b)$. Symmetry (**Theorem 4.5**) and transitivity (**Theorem 4.6**) are then both one-line applications of $(IE)$ — e.g. transitivity takes $z:I(A,b,c)$ and $w:I(A,a,b)$ to $J(z,w):I(A,a,c)$, by choosing $C(b,c,r)\equiv_{df} I(A,a,c)$.

**Computation.** Eliminating a *reflexivity* proof just returns the payload:

$$J(r(a),d) \to d$$

which is the formal reason Leibniz transport is "free" when the equality being used is literally reflexivity — no runtime work happens, it's a no-op that only matters to the type checker.

**Two consequences worth sitting with, both flagged directly by Thompson:**

- *Equality over base types is provable, not assumed.* §4.10.1 proves $(\forall x:bool).(x=_{bool}True \lor x=_{bool}False)$ is inhabited, purely by combining boolean-elimination with $(II)$ and $(\lor I)$ — this is the formal cash-value of "the elimination rule says every element has the introduced shape," now stated as an equation rather than a vague claim.
- *All proofs of the same identity type are themselves provably equal* (§4.10.4): given $a:A$, any $p:I(A,a,a)$ can be shown equal to $r(a)$ via $J(p, r(r(a))):I(I(A,a,a), r(a), p)$. This is Thompson's first hint of the intensional-vs-extensional equality tension that becomes a whole later topic (§5.7–5.8, and the workbench's own "definitional vs. propositional equality" thread) — proof-irrelevance of equality proofs is *not* free in this system; it has to be argued for, and doesn't extend to full extensionality without cost.

**Grounding (Rust — checker-shaped, primary here).** $I(A,a,b)$ is not `PartialEq`/`==` (a *runtime, decidable* Boolean test) — it's much closer to a `PhantomData`-carrying proof witness type in a dependently-typed-in-spirit Rust encoding, e.g. `struct Refl<A>(PhantomData<A>)` constructible only when the compiler can already see the two types/values coincide, the way `std::mem::transmute` soundness proofs or GATs-based type-equality witnesses (`Eq<A,B>` with only a reflexive constructor) work in advanced Rust type-level programming. A verifier built to check Hoare-style contracts will need exactly this shape: a proposition "these two program states/values are equal," with reflexivity as the sole primitive constructor and everything else — symmetry, transitivity, substitution into a predicate — derived as *lemmas about proof terms*, not built-in compiler magic.

**Grounding (Lean — elaboration-shaped, primary here).** This is verbatim Lean's `Eq` type: `inductive Eq (a : α) : α → Prop | refl : Eq a a`, with `Eq.mpr`/`▸` playing the role of $J$, and `rfl` playing the role of $r(a)$. Lean's kernel reduction rule for `Eq.rec` applied to `Eq.refl` is exactly $J(r(a),d)\to d$ above. When Thompson proves Theorem 4.4 is derivable, he is proving, by hand, exactly what Lean's `Eq.subst`/`▸` gives you for free from the `Eq` recursor — worth recognizing as the same mechanism, because it means the book's derivations for symmetry/transitivity of $I$ are literally the derivations of `Eq.symm`/`Eq.trans` in Lean's own core library.

## Convertibility and the rules of substitution (§4.11)

**What problem this solves.** The formation/introduction/elimination rules tell you which propositions are inhabited — full stop, from a purely logical point of view you could stop there. But the moment you also want *equality reasoning inside the system* (which is exactly what $I(A,a,b)$ demands), you need to connect "the proof-simplification process" (computation, i.e. reduction $\to$) to "the equality relation the type theory reasons about." §4.11 is the plumbing that does this.

**Redexes and reduction, generalized.** Thompson tightens the definitions from the untyped/simply-typed $\lambda$-calculus (Chapter 2) to the typed setting:

- A **free subexpression** of $e$ is a subexpression none of whose free variables are bound within $e$ — i.e. exactly the kind of thing that could have arisen by substitution into $e$.
- A **redex** is a free subexpression matching the left-hand side of some computation rule (e.g. $fst\,(p,q)$, or $((\lambda x:A).e)\,a$).
- $e_1 \to e_2$ means some free-subexpression redex $f_1$ of $e_1$ is replaced by its reduct to give $e_2$. This is *more restrictive* than the untyped calculus's reduction: reduction under a binder is only allowed when the reduced part doesn't mention the bound variable free.
- $\twoheadrightarrow$ is the reflexive-transitive closure of $\to$ (a sequence of one-step reductions in either the same or successive terms).
- **Convertibility**, $\leftrightarrow$, is the smallest *equivalence relation* extending $\to$ — i.e. it also permits going "backwards," so two terms are convertible if connected by a zig-zag of forward/backward reduction steps.

**The substitution rules — where convertibility gets teeth.** Convertible expressions are declared interchangeable *inside derivations* via six substitution rules. The four primary ones:

$$\dfrac{a\leftrightarrow b \quad B(a)\ is\ a\ type}{B(b)\ is\ a\ type}\ (S_1) \qquad \dfrac{a\leftrightarrow b \quad p(a):B(a)}{p(b):B(b)}\ (S_2)$$
$$\dfrac{A\leftrightarrow B \quad A\ is\ a\ type}{B\ is\ a\ type}\ (S_3) \qquad \dfrac{A\leftrightarrow B \quad p:A}{p:B}\ (S_4)$$

plus two derived rules ($S_5$, $S_6$) for substituting a convertible term for a free variable under an open assumption $[x:A]$. These four rules are precisely what makes the type system's "static" and "dynamic" halves inseparable, as flagged back in §4.4: whether an expression type-checks can depend on whether two subexpressions reduce to the same normal form, not just on their surface syntax.

**The strengthened I-introduction rule.** With substitution in hand, Thompson upgrades reflexivity to work across *any* convertible pair, not just syntactically identical terms:

$$\dfrac{a\leftrightarrow b \quad a:A \quad b:A}{r(a):I(A,a,b)}\ (II')$$

This is the rule that actually lets you *use* computation to prove propositional equalities — and it is, functionally, exactly what a dependently-typed checker's `isDefEq`/definitional-equality check does: two terms that reduce to a common form are treated as the same term for typing purposes, without needing an explicit equality proof term at all.

**Worked example — `addone` vs. `succ` (§4.11.2).** Thompson proves $addone\ x =_N succ\ x$ is inhabited for every $x:N$, by induction, grounding the base case in raw computation:
$$addone\ 0 \equiv (\lambda x.\,prim\ x\ 1\ succ') \, 0 \to prim\ 0\ 1\ succ' \to 1 \equiv succ\ 0$$
so $addone\ 0$ and $succ\ 0$ are convertible, hence by $(II')$ the type $(addone\ 0 =_N succ\ 0)$ is inhabited. The inductive step chains this with the *derived* transitivity rule from §4.10 to close the loop. Crucially — and this is one of the book's sharper points — Thompson stops to note that proving $\forall x.\ succ\ x =_N addone\ x$ this way does **not** license concluding $\lambda x.succ\ x =_{N\Rightarrow N} \lambda x.addone\ x$ (the functions-as-equal statement), because the two lambda terms are not themselves convertible — pointwise propositional equality does not collapse into definitional/convertibility equality. This gap between "provably equal pointwise" and "identical as terms" is exactly the extensionality problem picked up again in §5.8, and it is the precise reason a checker needs *both* a decidable convertibility check *and* a separate mechanism (propositional equality proofs, explicitly carried and applied) for the facts convertibility alone can't see.

**Worked example — natural-number equality is well-behaved (§4.11.3).** A `discrim` function (by primitive recursion, `True` on `0`, `False` on any successor) combined with the boolean-distinctness axiom `ax : ¬(True =_bool False)` proves zero is never a successor; the predecessor function from §4.10.3 combined with substitution proves the successor function is injective. Both results are earned entirely from reduction + substitution + the one non-derivable axiom that the two booleans are distinct — nothing about $N$'s "infinitude" is smuggled in beyond what primitive recursion already gives.

**Grounding (Rust — primary, checker-shaped).** Convertibility is what a Rust-based verifier's core `defeq(t1, t2, ctx) -> bool` routine implements: normalize (or reduce stepwise with fuel/sharing) both sides and compare, or reduce in lockstep. The redex/reduct machinery — "match a subterm against a left-hand-side pattern, rewrite to the right-hand side" — is literally the shape of a small-step interpreter's `step()` function over an AST enum, which is exactly the artifact you'd build first in a Rust verifier before adding proof terms on top.

**Grounding (Lean — primary, elaboration-shaped).** This section is the source-level ancestor of Lean's `isDefEq`: Lean's kernel reduces both sides using weak-head normalization and compares (with special-cased $\eta$/$\iota$ rules), exactly mirroring $\leftrightarrow$ as "smallest equivalence relation extending $\to$." The `addone`/`succ` example is a compact illustration of *why* Lean needs both `rfl` (definitional equality, decided by the kernel via reduction) and `Eq` proofs built via tactics like `induction`/`simp` (propositional equality, requiring explicit proof terms) — precisely the gap Thompson calls out between "convertible" and "merely propositionally, inductively equal."

## Synthesis: where this sits in the book, and what it feeds

```
Judgements (p : P)  ──────────────────────────┐
        │                                      │
        ▼                                      ▼
Formation / Introduction /      Identity type I(A,a,b)
Elimination / Computation        (formation depends on
   (the 4-rule pattern,          typed premises — breaks
   §4.3, reused for every        the earlier syntax/typing
   type former in §4.6–4.9)      separation, §4.10)
        │                                      │
        │                                      ▼
        │                        Convertibility ↔, redexes,
        │                        substitution rules S1–S6
        │                        (§4.11) ──► strengthened (II')
        │                                      │
        └──────────────► TT0 (defined in full, §5.3) ◄──┘
                                   │
                    ┌──────────────┼───────────────────┐
                    ▼              ▼                    ▼
        Chapter 5: metatheory  Chapter 6: programs  Chapter 5 §5.7–5.8:
        (normalisation,        verified via the      intensional vs.
        decidability of        very same rules       extensional equality
        convertibility)        used to write them    (cost of full
                                                       extensionality)
```

Everything downstream in the book presupposes this machinery. The four-rule pattern here is the template Thompson reuses verbatim for quantifiers (§4.6, universal/existential as dependent function/sum types), base types (§4.7–4.9), and later the subset, quotient, and well-founded types of Chapter 7 — so understanding *why* the pattern has exactly these four parts, rather than memorizing conjunction's instance of it, is what makes those later chapters fast reading instead of each one relearning the idea from scratch. The identity type and convertibility together are also what make Chapter 6's promise possible — "prove a program correct in the same system in which it's written" — since program equality claims (`addone x = succ x`) and program execution (`addone x → succ x`) are, after this section, facets of the *same* relation, differing only in whether you're allowed to go backwards.

For the standing project: this is the direct formal source of two mechanisms you'll build by hand. The four-rule pattern *is* the algorithm for turning a type-former specification into a type checker's match arms — every dependent type former Chapter 6 and 7 introduce later is an instance of it. And the split between convertibility (decidable, syntactic, no proof term needed — §4.11's $\leftrightarrow$) versus the identity type (a first-class proposition requiring an explicit proof term, §4.10's $I(A,a,b)$) is exactly the split a Rust verifier needs between its fast definitional-equality check and its explicit-proof-obligation mechanism, and exactly the split Lean's kernel draws between `isDefEq` and `Eq`. The `addone`/`succ` example is worth remembering by name — it's the smallest complete illustration in the book of why both mechanisms have to coexist.
