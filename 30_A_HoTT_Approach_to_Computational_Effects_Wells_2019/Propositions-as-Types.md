---
title: Propositions as Types
source: A HoTT Approach to Computational Effects (Wells, 2019)
chapter: "2.2: Proof and Logic"
pages: "18–22"
tags: [hott, curry-howard, identity-type, propositions, truncation, predicate-logic]
---

[[book-guidelines|↩ Back to guidelines]]

## The correspondence, stated plainly

**The Curry-Howard correspondence** (also "propositions as types," also "proofs as programs") says: computer programs, proofs of propositions, and objects of types are all *the same kind of thing*, viewed from three angles. HoTT pushes this one step further than ordinary type theory: a proposition isn't just "a type" — it's **a space whose points are the proofs (witnesses) of that proposition**. Proving a theorem, concretely, means: introduce a type corresponding to the proposition, then specify an algorithm that constructs an object of that type. Because that algorithm is literally a program, it can be checked computationally — which is why HoTT proofs can live simultaneously as ordinary mathematical prose *and* as machine-checked code, with no translation gap in principle between the two.

If you've ever written a Lean or Coq proof, you've already lived this correspondence without necessarily naming it: `theorem foo : P := proof_term` is exactly "introduce a type `P`, construct an object of it." The rest of this article is about making that idea precise enough to actually build a logic on top of it — which turns out to require real care, because the naive version breaks classical reasoning.

## Identity types: propositional equality as a path

[[Foundations-of-Homotopy-Type-Theory|Judgmental equality]] ($A \equiv B$) is a fixed, static, decidable-by-reduction relation — great for definitions, useless for the theorems you actually want to prove ("these two possibly-different-looking things are equal"). For that you need the **identity type**: given $a, b : A$, a *propositional* equality $a = b$, with the full collection of identities between $A$'s objects captured by the dependent type $\mathrm{Id} : A \to A \to \mathcal{U}$. Note the shape — this is precisely the dependent-type machinery from [[Type-Formers|the previous article]]: $\mathrm{Id}$ takes two values and returns a *type*, the type of proofs that those two values are equal.

An object $p : a = b$ is a **witness** of the equality — a proof, but also, topologically, **a path** from point $a$ to point $b$. This is where "homotopy" in "homotopy type theory" earns its name: identity isn't a flat yes/no relation, it's a *type of paths*, and different paths between the same two points can genuinely be different objects (this becomes the crux of the Univalence discussion — equal things can be equal in more than one way).

**Reflexivity** is the base case: the identity $a = a$, witnessed by $\mathrm{refl} : \prod_{a:A} (a = a)$ — every object is equal to itself, trivially, by the constant "stay put" path. Reflexivity comes with a computation rule called **path induction** (or the induction principle for equality): to prove *any* property of an arbitrary equality $a = b$, it suffices to prove it for the single case $\mathrm{refl}_a$ (i.e. $a = a$). This is a genuinely strong principle — it says the only way to *build* a proof about equalities in general is to handle the reflexivity case and let the machinery propagate that proof to every other path.

```lean
-- Path induction is exactly `Eq.rec` / the eliminator Lean generates
-- automatically for the inductive `Eq` type — this is not an analogy,
-- it's the same principle by another name.
example (a b : Nat) (p : a = b) (motive : Nat → Prop) (h : motive a) : motive b :=
  p ▸ h   -- rewriting along p is path induction in action
```

This is the mechanism underneath `rewrite`/`subst` tactics in any proof assistant, and underneath any elaborator's `isDefEq`-adjacent handling of propositional (not just definitional) equality — worth remembering, since it resurfaces directly in the closing synthesis below.

## Propositions: why not every type gets to be one

Here's the trap the naive Curry-Howard correspondence falls into: if *any* type is allowed to represent a proposition, conventional classical logic breaks. The book's example: the law of double negation becomes incompatible with an unrestricted propositions-as-types reading. Why? Because a type can have many *different* inhabitants (many different proofs/programs of that type), and classical logic wants a proposition's truth value to carry no more information than "true or false" — not "true, and here specifically is *which* proof."

**The fix:** define a type to count as a genuine **proposition** only if it is **contractible when inhabited** — meaning any two witnesses of it must be *equal to each other*. Concretely: an inhabited proposition is equivalent to the unit type $1$ (exactly one "shape" of proof, up to equality); an uninhabited one is equivalent to the empty type $0$. The visual: an inhabited proposition is a disc you can contract down to a single point — however many proofs it seems to have, they're all secretly the same point once you account for identity.

This is formalized as a type called $\mathrm{Prop}$:

$$\mathrm{Prop} :\equiv \prod_{a:A}\prod_{b:A} (a = b)$$

— read as "for all $a, b$ in $A$, $a$ equals $b$." A worked example the book gives: proving $x = y$ given $x \equiv y : X$ (judgmental equality already holding) is immediate — $\mathrm{refl}_x : x = x$, and since $x \equiv y$ by definition, that same witness serves as $\mathrm{refl}_x : x = y$. This is the bridge between judgmental and propositional equality: judgmental equality is always *free* propositional equality, via reflexivity.

**Truncation** handles the types that *aren't* naturally contractible but need to behave like propositions anyway. The truncation $\|A\|$ of any type $A$ strips away everything except "is it inhabited or not" — to construct $|a| : \|A\|$, it suffices to exhibit *some* $a : A$; the specific $a$ you used gets forgotten. This is the formal tool for "I know a proof exists, and I've deliberately decided not to care which one" — useful whenever a type carries more structure than you want a downstream proof to be able to inspect.

## Predicate logic: connectives as type formers, verbatim

With $\mathrm{Prop}$ pinned down, the book assembles ordinary predicate logic entirely out of the type formers already introduced — no new primitives needed:

| Logical notion | Type-theoretic encoding |
|---|---|
| True | the unit type $1$ |
| False | the empty type $0$ (a witness of $0$ is called a **contradiction**) |
| $A \Rightarrow B$ (implication) | a function $f : A \to B$ |
| $\lnot A$ (negation) | a function $g : A \to 0$ |
| $A \land B$ (conjunction) | the product type $A \times B$ |
| $A \lor B$ (disjunction) | the sum type $A + B$ |
| $A \Leftrightarrow B$ (bi-implication) | $(A \to B) \times (B \to A)$ |
| $\forall n{:}\mathbb{N}.\, P\ n$ (universal) | $\prod_{n:\mathbb{N}} (P\ n)$ |
| $\exists n{:}\mathbb{N}.\, P\ n$ (existential) | $\sum_{n:\mathbb{N}} (P\ n)$ |

A couple of these deserve a second look because the *mechanism*, not just the table entry, is the interesting part:

**Negation as "maps to the empty type."** To prove $\lnot A$, you construct $g : A \to 0$. Why does this work as negation? Because a function that lands in $0$ can only exist at all if its *domain is also empty* (you can't map a real point into a space with no points). So "$A \to 0$ is inhabited" really does mean "$A$ has no inhabitants" — negation falls straight out of the empty type's own defining property, not out of any new logical primitive. And the reverse direction — $0 \to A$ for arbitrary $A$ — is always inhabited (the empty function, vacuously total), which is exactly "false implies anything," now visible as a consequence of $0$ having zero constructors to case-split on.

**Quantifiers are the dependent types from the previous article, not new machinery.** This is the payoff for having taken $\Pi$- and $\Sigma$-types seriously already: "for all $n$, $P\ n$ holds" is *literally* $\prod_{n:\mathbb{N}}(P\ n)$ — a dependent function that, given any $n$, produces a proof of $P\ n$. "There exists $n$ such that $P\ n$" is *literally* $\sum_{n:\mathbb{N}}(P\ n)$ — a pair of a witness $n$ and a proof that $P$ holds of it. Nothing new was defined; the quantifiers were already sitting inside the type formers.

The book compiles some worked translations directly:

$$(P \Rightarrow Q) \lor (Q \Rightarrow P) :\equiv (P \to Q) + (Q \to P)$$
$$(P \land Q) \Rightarrow (P \lor Q) :\equiv (P \times Q) \to (P + Q)$$
$$\lnot P \Rightarrow (\lnot P \land P) :\equiv (P \to 0) \to ((P \to 0) \times P)$$

**A subtlety worth flagging explicitly, since it's easy to skate past:** if $P$ and $Q$ are genuine propositions (contractible-when-inhabited), then $P \times Q$ is guaranteed to still be a proposition, and so are functions over propositions — but **sum types and $\Sigma$-types are not automatically propositions**, even when built from propositions. A sum $P + Q$ can carry the extra information of *which side* was taken, and a $\Sigma$-type can carry *which witness* was chosen — exactly the kind of extra information $\mathrm{Prop}$ is designed to forbid. When this happens, truncation is the tool that flattens the result back down to something classically well-behaved.

Closing out the section, the book proves $\top \neq \bot$ for a two-element type $B$ with $\top, \bot : B$, by constructing an element of $(\top = \bot) \to 0$: define $B : B \to \mathcal{U}$ with $B\ \top :\equiv 1$ and $B\ \bot :\equiv 0$, assume $p : \top = \bot$, substitute along $p$ to turn a witness $\bullet : B\ \top$ into an element of $B\ \bot \equiv 0$ — a contradiction. This is worth internalizing as a *pattern*, not just a one-off proof: "define a type family that distinguishes cases, then substitute along a hypothesized equality to derive an inhabitant of $0$" is the generic recipe for proving two constructors of an inductive type are unequal — precisely what Coq's/Lean's automatically-derived `discriminate`-style tactics are doing mechanically.

## Where this leads

Propositions-as-types is the piece that makes the whole thesis's project *possible* in the first place: Chapter 5's central law — $\prod_{a:A} \mathrm{eval}(\mathrm{bind}\ a) = a$ — is a $\Pi$-type over an identity type, i.e. exactly the machinery built here, applied to the action-type definition. The distinction between judgmental and propositional equality set up in this article is also the seed of the next major topic in the book: [[Equivalence-and-Univalence|Equivalence and Univalence]] exists precisely because propositional equality ($a = b$) turns out to need its *own* richer theory once you start asking when two entire *types* (not just objects) should count as equal — reflexivity alone isn't enough once function extensionality and isomorphism-invariance enter the picture.

**Connection to the standing project:** this is the most directly load-bearing article for a refinement-type checker so far. The **judgmental vs. propositional equality split** *is* the split between `isDefEq` (fast, syntactic, decidable, used pervasively during elaboration) and general propositional-equality proof obligations (potentially requiring a real proof term, exactly what a proof-obligation/VC-generation pass emits for a Hoare-style refinement). And the $\mathrm{Prop}$-via-contractibility definition is the direct ancestor of **proof irrelevance** — a checker built on this discipline can safely erase proof terms at runtime (any two proofs of the same proposition are, by construction, equal), which is exactly what you want if refinement-type proof obligations shouldn't survive into compiled code. Path induction, meanwhile, is your `isDefEq`/substitution engine's actual algorithmic core — every "rewrite along an equality proof" step in a verifier is path induction wearing a different name.
