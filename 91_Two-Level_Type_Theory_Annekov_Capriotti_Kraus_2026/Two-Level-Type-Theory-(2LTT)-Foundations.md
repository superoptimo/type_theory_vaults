---
title: "Two-Level Type Theory (2LTT) Foundations"
source: "Two-Level Type Theory and Applications (Annenkov, Capriotti, Kraus, Sattler)"
chapters: "Chapter 1 (pp. 2–6), Chapter 2 (pp. 6–24)"
tags:
  - type-theory
  - two-level-type-theory
  - homotopy-type-theory
  - cwf
  - univalence
  - uip
---

[[book-guidelines|↩ Back to guidelines]]

# Two-Level Type Theory (2LTT) Foundations

## The problem that forces a second level

Homotopy type theory (HoTT) gives you a universe $\mathcal{U}$ with a genuinely useful equality type: paths, univalence, the whole machinery that lets "isomorphic implies equal" be a *theorem* instead of an axiom you bolt on. But there is a class of constructions that HoTT, taken alone, simply cannot express — not because they're false, but because the type theory has no internal way to talk about *itself* while quantifying over an unbounded external parameter.

The paper's motivating example is worth sitting with, because it's not a toy: **semisimplicial types**. A semisimplicial type of level 1 is just a type $A_0 : \mathcal{U}$. Level 2 adds a family of "edges" $A_1 : A_0 \to A_0 \to \mathcal{U}$. Level 3 adds "triangle fillers":

$$A_2 : \Pi_{(x,y,z:A_0)}.\, A_1\,x\,y \to A_1\,y\,z \to A_1\,x\,z \to \mathcal{U}$$

You can keep going — level 4, level 100 — and at every *fixed, externally chosen* level $k$, you can write down the type $S_k$ that classifies semisimplicial types of that level. This is tedious but mechanical. The open problem is different: can you construct a single internal function

$$S : \mathbb{N} \to \mathcal{U}_1$$

such that $S(n)$ *is* the type of semisimplicial types of level $n$, for every $n$ at once — including internal, non-standard, "meta" naturals your program never enumerates by hand? Nobody knows how to build $S$ inside plain HoTT. The gap between "I can build $S_k$ for any $k$ you name" and "I can build $S$, quantified over all $k$" is exactly the gap between an external, meta-theoretic construction and an internal, type-theoretic one.

**What breaks without a second level:** if you try to formalize $S$ directly in HoTT, you need to talk about *all* type formers, *all* fibrancy conditions, and an unbounded recursion scheme over an externally-indexed family — but HoTT's own syntax has no notion of "the type theory reasoning about itself." You'd be trying to write a program that inspects its own elaborator's universe hierarchy from inside the source language. Something has to give: either you accept $S$ is unconstructible, or you extend the theory with a genuine meta-level that can see and manipulate the object theory as data.

This is precisely the move Voevodsky made with his **Homotopy Type System (HTS)**, and it's the move this paper generalizes and makes minimal: **two-level type theory (2LTT)**.

## Two type theories, one category of contexts

The core idea: instead of one universe of types, keep *two parallel copies* of the whole type-theoretic apparatus, living in the same contexts, related by a one-way conversion operation.

- The **outer level** is a traditional Martin-Löf type theory (MLTT) with intensional equality, but crucially assuming **uniqueness of identity proofs (UIP)** — any two proofs of $a = b$ are themselves equal. This kills all interesting higher-dimensional structure; outer equality behaves like classical, "flat" equality. This is deliberate: the outer level is meant to play the role of an *ambient meta-theory* you can compute in freely, the way you'd reason about a proof assistant's kernel from outside it.
- The **inner level** is essentially HoTT itself: univalent universes, and potentially higher inductive types. This is the "object language" — the theory whose meta-theory you're trying to internalize.

Both levels share **one notion of context** ($\Gamma\,\mathsf{ctx}$) and one notion of term/type-in-context judgment, just doubled for types:

$$\Gamma \vdash A\ \mathsf{type}_j \qquad \Gamma \vdash A\ \mathsf{type}^i_j$$

(the superscript $i$ marks "inner"; $j$ is the universe level). Every basic type former gets two copies — $\Pi/\Pi^i$, $\Sigma/\Sigma^i$, $+/{+^i}$, $\mathbf{1}/\mathbf{1}^i$, $\mathbf{0}/\mathbf{0}^i$, $\mathbb{N}/\mathbb{N}^i$, and the equality types $=/{=^i}$ — with completely standard formation/introduction/elimination/computation rules on each side, mirroring Appendix A.2 of the HoTT book. For instance, outer coproducts and inner coproducts are formed by genuinely separate rules:

$$\dfrac{\Gamma \vdash A\ \mathsf{type}_j \qquad \Gamma \vdash B\ \mathsf{type}_j}{\Gamma \vdash A + B\ \mathsf{type}_j}\ \texttt{form-+} \qquad\qquad \dfrac{\Gamma \vdash A\ \mathsf{type}^i_j \qquad \Gamma \vdash B\ \mathsf{type}^i_j}{\Gamma \vdash A +^i B\ \mathsf{type}^i_j}\ \texttt{form-+}^i$$

and crucially **you cannot mix them** — there is no rule for forming a coproduct of one inner and one outer type. The two universes of discourse are genuinely separate; they only ever touch through one designated bridge.

Context extension works uniformly across both:

$$\dfrac{\Gamma\,\mathsf{ctx} \quad \Gamma \vdash A\ \mathsf{type}_j}{\Gamma.A\,\mathsf{ctx}}\ \texttt{ctx-ext} \qquad\qquad \dfrac{\Gamma\,\mathsf{ctx} \quad \Gamma \vdash A\ \mathsf{type}^i_j}{\Gamma.A\,\mathsf{ctx}}\ \texttt{ctx}^i\texttt{-ext}$$

which is the formal expression of "contexts are shared" — there's only one $\Gamma\,\mathsf{ctx}$ judgment, and you can extend it by either an inner or an outer type, landing in the same category of contexts either way.

**Rust grounding.** The cleanest first-pass analogy for this split is a **typestate / marker-trait** pattern where you have two disjoint families of types tagged by a phantom parameter, sharing one "environment":

```rust
// Two disjoint universes of "types" living over the same context representation.
struct Outer;
struct Inner;

// A tagged type-in-context, phantom-typed by which universe it lives in.
struct TypeInCtx<Level> {
    repr: TypeRepr,
    _level: std::marker::PhantomData<Level>,
}

// Sum ("+") formers exist separately for each level — there is NO impl
// that lets you build TypeInCtx<Outer> out of a TypeInCtx<Inner> and a
// TypeInCtx<Outer> mixed together. That asymmetry is the point: the
// type system enforces "no mixing" the same way form-+ / form-+^i do.
impl TypeInCtx<Outer> {
    fn sum(a: TypeInCtx<Outer>, b: TypeInCtx<Outer>) -> TypeInCtx<Outer> { /* ... */ }
}
impl TypeInCtx<Inner> {
    fn sum(a: TypeInCtx<Inner>, b: TypeInCtx<Inner>) -> TypeInCtx<Inner> { /* ... */ }
}
```

This is illustrative, not load-bearing — Rust's trait system has no analogue of dependent contexts or of a *conversion* function between the two universes, which is the actual heart of 2LTT and which we cover next.

**Lean grounding (the sharper analogy).** Lean already has something structurally close to the outer/inner split, and it's worth naming explicitly because it's exact rather than metaphorical: **`Prop`**. In Lean 4, `Prop` has *definitional proof irrelevance* — any two terms `p q : P` for `P : Prop` are judgmentally equal, `p ≡ q`. That is UIP-like behavior baked into the kernel for one universe, coexisting with `Type`, where two proofs of an equality `a = b` are *not* forced to be equal (Lean's `Type` doesn't validate univalence either, but it doesn't impose UIP the way `Prop` effectively does for its inhabitants). The 2LTT paper's outer level plays the role Lean's `Prop`-style irrelevance plays for equality proofs, generalized to *all* types, not just propositions — and its inner level is what a cubical/univalent extension of `Type` would be. If you've ever wondered why Lean's kernel can get away with proof irrelevance in `Prop` while `Type` stays intensional, you've already seen a shadow of the outer/inner distinction this paper formalizes generally.

## The conversion function $c$: the one bridge

The two levels would be useless side by side if there were no way to move between them. 2LTT provides exactly one primitive operation for this, the **conversion function** $c$:

> Whenever $\Gamma \vdash A\ \mathsf{type}^i_j$ (an inner type), there is an outer type $c(A)$ with $\Gamma \vdash c(A)\ \mathsf{type}_j$, and this operation preserves context extension: $\Gamma.A$ and $\Gamma.c(A)$ are *the same context*.

That last clause is doing a lot of work. It means the set of terms of $A$ (inner) and the set of terms of $c(A)$ (outer) are automatically in bijection — you get a term-level conversion $c(a) : c(A)$ for free, and it's an isomorphism on terms (Lemma 2.10), essentially "for free" from the universal property of context extension (via the Yoneda-style argument that representable functors preserve isomorphisms).

Notice the direction: $c$ only goes **inner → outer**. There is no general operation going the other way. This one-directionality is the entire technical content of the "meta-theory vs. object theory" intuition from the introduction: *from a type in HoTT, you can always extract a statement in the meta-theory (its outer shadow $c(A)$); from an arbitrary meta-theoretic statement, you cannot always reconstruct a HoTT type.* This is the formal echo of the informal claim "we can convert inner types into outer ones, but not always vice versa."

**What $c$ does and doesn't preserve — Lemma 2.11.** This is the load-bearing technical result of the whole syntactic setup, and it splits type formers into two very different behavioral classes:

| Type former | Preserved by $c$ up to (natural) isomorphism? |
|---|---|
| $\mathbf{1}$ | **Yes** — isomorphism (2.1) |
| $\Sigma$ | **Yes** — isomorphism (2.2) |
| $\Pi$ | **Yes** — isomorphism (2.3) |
| $+$ | Only a one-directional comparison map (2.4) |
| $\mathbf{0}$ | Only a one-directional comparison map (2.5) |
| $\mathbb{N}$ | Only a one-directional comparison map (2.6) |
| $=$ (equality) | Only a one-directional comparison map (2.7) |
| Universes $\mathcal{U}^i_j$ | Only a one-directional comparison map (2.8) |

Why the split? The three "good" type formers — $\mathbf{1}$, $\Sigma$, $\Pi$ — are characterized by *universal properties about maps **into** a slice from an arbitrary object* (their eliminators talk about the whole context of possible destinations), and crucially, in this theory, both $\Sigma$ and $\Pi$ are assumed to satisfy their $\eta$-laws. Because $c$ preserves context extension **on the nose**, and $\Sigma/\Pi$-terms are uniquely determined (up to $\eta$) by their universal property, the isomorphism just falls out of a chain of context-extension identities:

$$\Gamma.c(\Sigma^i_A B) = \Gamma.\Sigma^i_A B \;\simeq\; \Gamma.A.B \;=\; \Gamma.c(A).c(B) \;\simeq\; \Gamma.\Sigma_{c(A)}c(B)$$

The "bad" (or as the paper calls them, **positive**) type formers — $+$, $\mathbf{0}$, $\mathbb{N}$, equality — are characterized by universal properties about maps **out of** them (their eliminators describe how to consume a value, via case-splitting or induction), and that shape of universal property does *not* transport across $c$ for a structural reason: to conclude $\Gamma.\mathbf{0}^i \simeq \Gamma.\mathbf{0}$ over $\Gamma$, you'd need to apply the universal property of $\mathbf{0}^i$ (an *inner* fact) to an *outer* type $C$ — but nothing licenses using an inner elimination principle to eliminate into the outer level. Concretely:

- **Coproducts:** a term of $A$ or $B$ in the meta-theory gives you an element of $A+^i B$, but not conversely — a context might not let you *normalize* an inner-coproduct element back down to a coprojection.
- **Empty type:** a meta-theoretic contradiction gives an object-theoretic one, never the reverse.
- **Naturals:** an external numeral (a literal $0, 1, 2, \dots$ built by iterating successor) always gives an internal natural, but an *arbitrary* element of $\mathbb{N}^i$ need not reduce to a numeral — think of a natural number produced by an unresolved recursive definition, still "stuck," with no external numeral to point to yet.
- **Equality:** two syntactically-equal (meta-theoretically identical) expressions are trivially provably equal via `refl`, but two *provably* equal expressions need not be syntactically identical.

This is not a technical inconvenience to be patched — the paper is emphatic that for **equality specifically**, forcing this map to be invertible would collapse the entire motivation for having two levels at all (it would essentially force inner and outer equality to coincide, erasing the homotopical content you built the inner level to protect in the first place).

**What breaks without this asymmetry:** if $c$ preserved *everything* on the nose, you'd effectively be back to a single-level theory where "outer" is just a synonym for "inner" — there'd be no meaningful sense in which the outer level is doing meta-theoretic bookkeeping the inner level can't do itself, and the entire point of 2LTT (a place to build $S : \mathbb{N} \to \mathcal{U}$ using outer-level natural-number induction over an internal notion of "inner diagram") would evaporate.

## Making it precise: models via categories with families

The paper deliberately does *not* try to nail down a complete syntactic specification (a full generalized algebraic theory presentation) as the primary definition. Instead, 2LTT is defined **semantically**, via its category of models, with the syntax understood as mere notation for constructions valid in every model (Remark 2.1 — an initiality/term-model argument in the style of Streicher's work on the calculus of constructions, acknowledged as technically demanding and left as future work, but orthogonal to the two-level idea itself). This is a clean, standard move in categorical type theory: define semantics first, treat syntax as a convenient DSL for talking about the initial model.

The semantic vocabulary is **categories with families (cwfs)**, the standard categorical packaging of "a category of contexts with dependent types and terms attached":

> **Definition (cwf).** A category $E$ with a presheaf $\mathsf{Ty}$ of types over $E$, a presheaf $\mathsf{Tm}$ of terms over the category of elements $E/\mathsf{Ty}$, a terminal object $\mathbf{1} \in E$ (empty context), and for every $\Gamma \in E$, $A \in \mathsf{Ty}(\Gamma)$, a terminal object $(\Gamma.A, p_A, q_A)$ among triples $(\Delta, \sigma, t)$ with $\sigma : \Delta \to \Gamma$ and $t \in \mathsf{Tm}(\Delta, A[\sigma])$ — this is context extension, defined by its universal property rather than by fiat.

Layer on top of this:

- A **cwf hierarchy** is a chain $\mathsf{Ty}_0 \to \mathsf{Ty}_1 \to \cdots$ of cwf structures (a cumulative universe tower).
- A **model of Martin-Löf type theory** is a cwf hierarchy plus, at each level $j$, a global "universe" element $U_j$ with $\mathsf{El}_j : \mathsf{Tm}_{j+1}(\Gamma, U_j) \simeq \mathsf{Ty}_j(\Gamma)$ naturally in $\Gamma$ — the categorical version of Tarski-style universes.
- A **model of set type theory** = model of MLTT with $\mathbf{1}/\Sigma/\Pi$ (with $\eta$), plus identity/empty/coproduct/naturals, plus **UIP and function extensionality**.
- A **model of homotopy type theory** = same basic type formers, but with **univalent** universes instead of UIP/funext.
- A **two-level model** bundles: one shared category of contexts $E$; an inner model $\mathsf{Ty}^i$ on $E$; an outer model $\mathsf{Ty}$ on $E$; and a **conversion morphism of cwf hierarchies** $c : \mathsf{Ty}^i \to \mathsf{Ty}$ that is the identity on $E$ itself (so context extension is *automatically* shared — this is where "$\Gamma.A$ and $\Gamma.c(A)$ are the same object" comes from categorically, not as an extra axiom).
- A **model of two-level type theory**, finally: a two-level model where the inner level is a model of HoTT and the outer level is a model of set type theory.

This definitional cascade is worth internalizing because it tells you exactly what's *assumed* versus *derived*. Nothing about how $c$ interacts with $+$, $\mathbf{0}$, $\mathbb{N}$, or $=$ is assumed — Lemma 2.11's asymmetric preservation results are *theorems*, forced purely by $c$ being a cwf-hierarchy morphism (hence preserving context extension, hence preserving universal-property-style type formers) and nothing more. That minimalism is a design choice, not an oversight: every extra property (discussed next) has to be justified by pointing at an actual class of models that satisfies it.

## Strengthenings: three families of optional axioms

Because the base definition is deliberately weak, the paper catalogues a menu of strengthenings a user of 2LTT is free to add — each one is a genuine axiom, only sound to add when some model of interest validates it.

**Group 1 — properties of a single-level model (apply separately to inner and outer):**

- **(M1)** The cumulative step maps $\mathsf{Ty}_j \to \mathsf{Ty}_{j+1}$ are *mono* (in a set-theoretic metatheory: subpresheaf inclusions).
- **(M2)** $\mathsf{El}$ is an equality on the nose, not just an isomorphism — i.e. **Russell-style** universes instead of Tarski-style. (M1)+(M2)+univalence together reproduce exactly the style of the HoTT book's appendix.

**Group 2 — strictness of the conversion morphism $c$:**

- **(T1)** $c$ is *mono on types* (injective on types in every context) — optionally strict, i.e. an actual subpresheaf inclusion.
- **(T2)** The Lemma 2.11 isomorphisms for $\mathbf{1}/\Sigma/\Pi$ hold **on the nose** (equalities, not just isomorphisms) — e.g. $c(\Pi^i_A B) = \Pi_{c(A)}c(B)$ *and* application commutes strictly: $\mathrm{app}^i(f,a) = \mathrm{app}(f,a)$.
- **(T3)** Inner types are **replete** in outer types: any outer type whose extension is isomorphic to an inner type's extension is itself (up to $c$) the image of some inner type.

(T1)+(T2) together is precisely what turns "outer type theory with a predicate of being inner" into the picture HTS uses, where inner types are literally a distinguished, closed-under-type-formers subset ("fibrant") of the outer ones.

**Group 3 — semantic axioms about specific models:**

- **(A1)** The one-directional comparison maps for the *positive* type formers ($+$, $\mathbf{0}$, $\mathbb{N}$ — not equality) are actually invertible.
- **(A2)** A strictly weaker substitute for (A1) on naturals: countably infinite towers of (trivial) fibrations have (trivially) fibrant limits — an internalized version of a standard (co)fibration-category axiom, sufficient (unlike (A1) itself) to build Reedy-fibrant semisimplicial types later in the paper.
- **(A3)** Weaker still: the outer natural-number type is *cofibrant* (a notion defined via the Leibniz/pullback-exponential construction in Chapter 3) — suggested by Shulman.
- **(A4)** Outer universes are "fibrant" — there is an inner type equivalent (or literally equal, via $c$) to the outer universe.
- **(A5)** The outer level validates **equality reflection** (full extensional type theory) — true of every presheaf-style example model in this paper, but stated as an optional extension rather than baked in, because it destroys decidable type-checking and is thus a poor default for proof-assistant implementations.
- **(A6)** Add more type formers as desired (inner higher/higher-inductive-inductive types; outer quotient or quotient-inductive-inductive types).

**Voevodsky's HTS, precisely located:** the paper can now state exactly what HTS is, in this vocabulary — **2LTT plus (T1), (T2), (A1), (A4), (A5), each in their strongest form.** This is a genuinely useful thing to know: it means every result proved for "basic" 2LTT (no strengthenings) automatically applies to HTS, but not vice versa, and it tells you exactly which extra commitments HTS makes (an injective, strictly-$\Pi/\Sigma/\mathbf{1}$-preserving conversion function; invertible positive-type-former comparisons; fibrant universes; full equality reflection) that basic 2LTT refuses to assume by default.

## Three families of models

The paper grounds all of this in concrete constructions:

1. **Presheaf models over an arbitrary model of HoTT $C$** (Proposition 2.13/Corollary 2.14). Take the presheaf category $\hat{C}$; its *outer* level is the standard Hofmann–Streicher extensional presheaf model, and its *inner* level is built by taking $\mathsf{Ty}_C$ itself (the classifying object of $C$'s own type structure) as a "universe" internal to $\hat{C}$, with the conversion function sending an inner type to its own term-presheaf, restricted appropriately. The Yoneda embedding $y_C : C \to \hat{C}$ becomes a *weak morphism of cwfs* that acts bijectively on types and terms — this bijectivity is the engine behind conservativity (next section). This model satisfies (T1) only if $C$'s term-presheaf action is injective (always fixable via the Grothendieck construction) but none of (T2)/(T3)/(A1)-(A4) in general.
2. **Modified presheaf model (Proposition 2.16).** A cleverer variant, factoring the outer level through a coproduct-decorated universe $\mathsf{Ty}' = y(\mathsf{Ty}_C + U)$, achieving (T1) *and* (T2) strictly, at the cost of only working for *finitary* type formers (adding infinite-arity $\Sigma$/$\Pi$ would force an infinite case split requiring classical logic).
3. **Simplicial sets** (the original Kan–Lurie model of HoTT, doubled as a 2LTT model). Inner types = outer types whose display map is a Kan fibration. This gets you (T1) (fibrations are closed under isomorphism, giving (T3) too), (T2) (since $\mathbf{1}/\Sigma/\Pi$ preserve fibrancy, so do their empty/coproduct/$\mathbb{N}$-analogues, giving (A1)-(A3)), and (A4) (pullback/pushforward along a mono is a coreflection).
4. **Cubical sets.** Structurally similar, but here **Kan composition is extra data**, not merely a property an outer type might or might not have — this is exactly what **invalidates (T1)**: an inner type is not simply an outer type satisfying a predicate, it's an outer type *plus* a chosen filling structure. Everything else ((T2), (T3), (A1)-(A6)) transfers from the simplicial case by the same argument (fibrant objects closed under small coproducts).

The simplicial-vs-cubical contrast is a genuinely illuminating case study: it shows that "(T1) holds" is not a universal feature of homotopical models — it depends on whether fibrancy is a *property* (simplicial: a Kan-fibration display map either exists or it doesn't) or *structure* (cubical: you must supply the Kan-composition operation as data). This is one of the cleanest illustrations in the paper of why the strengthenings are optional axioms and not theorems.

## Conservativity: 2LTT proves nothing new about HoTT

The paper's central positive result addresses exactly the "question 1" from the introduction: is 2LTT a *safe* extension of HoTT, in the sense that nothing you prove using the outer-level scaffolding leaks back as a false theorem of plain HoTT?

The precise notion (Definition 2.17): a cwf morphism $F : C \to D$ is **conservative** if whenever $F\Gamma \vdash \mathsf{Tm}_D(FA)$ is inhabited, then $\mathsf{Tm}_C(\Gamma, A)$ was already inhabited. This is the *weakest* reasonable notion — it says nothing about $F$ being surjective, injective, or an equivalence; it only says $D$ can't manufacture proofs $C$ didn't already have.

> **Proposition 2.18.** Basic 2LTT is conservative over HoTT — the canonical map $! : 0_{\mathrm{HoTT}} \to (0_{\mathrm{2LTT}})^i$ (from the initial HoTT model into the inner level of the initial 2LTT model) is conservative. This survives adding any type former validated by the standard presheaf model (e.g. (A5)).

The proof is a one-line consequence of the machinery already built: apply the presheaf-model construction (Corollary 2.14) to $0_{\mathrm{HoTT}}$ and $0_{\mathrm{2LTT}}^i$; the resulting triangle commutes up to isomorphism, and conservativity of the vertical leg follows immediately because the Yoneda embedding is bijective on terms. No new argument — the presheaf model *is* the conservativity proof.

> **Proposition 2.19.** 2LTT with (T1) and (T2) is *also* conservative over HoTT — same proof, swapping in the modified presheaf model of Proposition 2.16.

The practical upshot, stated in the Conclusions and worth internalizing now: if you stick to *basic* 2LTT (no strengthenings beyond what's proved here), **any theorem you prove about an externally-fixed bound transfers back to plain HoTT automatically** — you get to use the outer level's extra expressiveness (e.g. genuine limits of arbitrary diagrams of types, which the outer level has and the inner level generally lacks) as a scratchpad, with a guarantee that nothing escapes as an unsound addition to HoTT itself. Reach for the stronger axioms (A2, A3, and beyond) and you lose this automatic guarantee — you're now making a genuine strengthening, not just borrowing convenient bookkeeping.

## Why you can't internalize fibrant replacement (Theorem 2.20)

Given that inner types correspond to *fibrations* over a context and outer types to *arbitrary maps*, it's natural to want a **fibrant replacement** type former $R$: given any outer type $A$, produce the "closest" inner approximation $RA$, universal in the sense that maps $RA \to X$ (for $X$ inner) correspond to maps $A \to c(X)$ (outer). The candidate rules look exactly like propositional truncation, but targeting fibrancy instead of propositionhood:

$$\dfrac{\Gamma \vdash A\ \mathsf{type}_j}{\Gamma \vdash RA\ \mathsf{type}^i_j}\ \texttt{form-R} \qquad \dfrac{\Gamma \vdash a : A}{\Gamma \vdash r(a) : RA}\ \texttt{intro-R}$$

with an eliminator into any inner type $P$ and the expected computation rule. This is exactly the kind of thing you'd want for the fully general $S : \mathbb{N} \to \mathcal{U}$ construction motivating the whole paper — freely making things fibrant on demand.

**It cannot be added.** This is the paper's key negative result:

> **Theorem 2.20.** If a fibrant-replacement type former $R$ (as specified by `form-R`–`comp-R`) exists, then the **inner level satisfies UIP**.

The proof is a genuinely elegant diagonal argument. Start from the canonical (one-directional, per Lemma 2.11) comparison map $i : (c(u) =_{c(A)} c(v)) \to c(u =^i_A v)$ for an inner type $A$ with $u, v : A$. Using $R$'s universal property, construct the term

$$\Pi_{u,v:A,\,p:u=^i_A v}\, R\big(\Pi_{h:c(u)=c(A)c(v)}\, c(c^{-1}(i(h)) =^i p)\big)$$

By inner path induction, reduce to the case $p \equiv \mathrm{refl}^i_u$; then, using `intro-R`, it suffices to show $c(c^{-1}(i(h)) =^i \mathrm{refl}^i_u)$ for $h : c(u) = c(u)$. But now **outer UIP** lets you replace $h$ by $\mathrm{refl}_{c(u)}$, and $i$ sends the trivial outer equality to the trivial inner one, closing the case. Unwinding: for any $u : A$ and $p : u =^i u$, this produces a proof $p =^i \mathrm{refl}^i_u$ — which is exactly inner UIP.

**Why this doesn't contradict the existence of homotopical models.** Simplicial and cubical sets certainly *have* fibrant replacement, coming from the ambient weak factorisation system — but that operation is famously **not stable under base change** (not natural in the context $\Gamma$). The type-theoretic rules above implicitly demand naturality in $\Gamma$ (that's what a type former in context *is*), so the theorem is really saying: the external, non-natural fibrant replacement every homotopical model already has cannot be upgraded to an internal, natural type former without destroying the inner level's homotopical content entirely. This is a sharp, useful boundary — the paper notes that one escape hatch is to weaken the ambition and expose the operation only in a *modal* type theory with a notion of "crisp" types, where a restricted, non-fully-natural version of replacement can still be stated.

## Notational housekeeping (Section 2.8)

For the rest of the paper (Chapters 3 onward), several conventions kick in that are worth flagging so later material doesn't look inconsistent with what you just read:

- $\mathsf{El}$ and universe indices are omitted — the paper pretends to work with Russell-style universes even though the official semantics is Tarski-style, purely for notational convenience.
- The conversion operation $c$ is left **implicit** — when you see an inner type used where an outer one is expected, $c$ is silently inserted.
- **Propositions** are *defined*, not primitive, at both levels: $\mathrm{Prop}^i :\equiv \Sigma_{X:\mathcal{U}^i}\, \Pi_{x,y:X}(x =^i y)$ and $\mathrm{Prop} :\equiv \Sigma_{X:\mathcal{U}}\,\Pi_{x,y:X}(x=y)$ — a type paired with a proof it's a subsingleton, not a distinguished universe.
- The outer level is the *default*: bare "equality," "the equality type," and unannotated type formers always mean the outer ones; inner constructions carry the $i$ superscript. "Commutes" (for diagrams) means commutes up to *outer* equality.
- Because of outer UIP, **outer isomorphism** $A \simeq B$ (two maps composing to identity on the nose up to outer equality) is well-behaved as *the* notion of sameness for outer types — there's no need for anything fancier, unlike inner equivalence $A \simeq^i B$, which is the genuine HoTT notion carrying real homotopical content.

## Where this leads

This chapter is the foundation everything else in the paper stands on. The fibrancy/cofibrancy toolkit of Chapter 3 (topic 2 in this book's list) is built directly on the outer-vs-inner distinction established here: a type is "fibrant" exactly when it's isomorphic (in the outer, UIP-flavored sense) to an inner type, and a map is a "fibration" exactly when its fibres are fibrant — definitions that only typecheck because Chapter 2 gave you two separate universes and a directional bridge between them. The internal category theory (topic 3) and the [[Reedy-Fibrant-Diagrams|Reedy fibrant diagrams]] machinery (topic 4) that culminates in semi-Segal types and univalent $(\infty,1)$-categories (topic 5) is the payoff: it's the construction of $S_k$-for-variable-$k$ that Chapter 1 posed as the open problem, made possible precisely because the outer level supplies genuine natural-number induction and arbitrary limits that the inner level alone cannot.

**For the standing `type-theory` project goals:** the outer/inner split, and specifically the asymmetric preservation result of Lemma 2.11, is a genuinely reusable pattern beyond homotopy theory. Any system that needs to reason *about* a type theory from *within* an extension of it — an elaborator inspecting its own metavariable contexts, a kernel validating definitional equality while working in a richer meta-language, a verifier's trusted core distinguishing "terms the surface language can construct" from "terms only the checker itself can construct" — is implicitly drawing the same outer/inner line this paper draws formally. The precise moral to carry forward: a conversion function between two levels of a system is *never* going to be an isomorphism on "positive" (introduction-rule-defined) type formers unless you're willing to pay for it with an explicit axiom (like (A1)) backed by a genuine model — which is exactly the discipline a trusted kernel needs when deciding what definitional-equality shortcuts it's allowed to bake in.
