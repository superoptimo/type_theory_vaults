---
title: Universal Properties
source: "Notes on Category Theory (Paolo Perrone, arXiv:1912.10642v7)"
chapter: "Chapter 2, Section 2.3 — Universal properties (pp. 77–82)"
tags: [category-theory, universal-property, yoneda, cartesian-product, tensor-product, representable-functors]
---

# Universal Properties

[[book-guidelines|↩ Back to guidelines]]

## Why you need this at all

By the end of [[The-Yoneda-Lemma|the Yoneda lemma]], you've absorbed a strange but load-bearing fact: an object $X$ in a category is completely determined, up to isomorphism, by the functor or presheaf it represents — that is, by the *pattern of arrows* into or out of it, $\mathrm{Hom}_\mathcal{C}(-, X)$ or $\mathrm{Hom}_\mathcal{C}(X, -)$. Perrone's running metaphor is a good one: $X$ is a "probe," and knowing how every other object $S$ interacts with $X$ (every map $S \to X$) tells you everything there is to know about $X$ itself.

Section 2.3 turns that fact around and makes it *constructive*. Instead of starting with an object and asking what it represents, you start with a functor or presheaf you actually care about — "pairs of maps into $X$ and $Y$," say, or "bilinear maps out of $V \times W$" — and ask: is there an object that represents *this*? If so, that object is said to satisfy a **universal property**. This is how category theory manufactures new objects (products, tensor products, and eventually all [[Limits-and-Colimits|limits and colimits]]) without ever describing their internals — only the arrows in and out.

**[[Comonads#What breaks without this|What breaks without this]].** Without a universal-property specification, "the cartesian product" is just whatever your favorite category happens to build — ordered pairs in $\mathbf{Set}$, pairs of continuous functions glued with the product topology in $\mathbf{Top}$, direct sums of matrices in $\mathbf{Vect}$. These constructions look completely different at the level of implementation. A universal property gives you a *specification* that all of them satisfy simultaneously, and — crucially — a proof that anything satisfying the specification is unique up to a canonical isomorphism. You stop caring how the object is built and start caring only about how it behaves under composition with everything else. This is precisely the shift from "here is a concrete data structure" to "here is an interface," and it's why the same universal-property template reappears, unmodified, for limits, colimits, [[Adjunctions|adjunctions]], and free constructions throughout the rest of the book.

## The definition, unpacked

Here is the book's Definition 2.3.1, verbatim in spirit:

> Let $\mathcal{C}$ be a category and $X$ an object of $\mathcal{C}$. A **universal property** of $X$ consists of either a functor $F : \mathcal{C} \to \mathbf{Set}$ or a presheaf $P : \mathcal{C}^{op} \to \mathbf{Set}$, together with a chosen **natural isomorphism**
> $$\mathrm{Hom}_\mathcal{C}(X, -) \Rightarrow F \qquad \text{or} \qquad \mathrm{Hom}_\mathcal{C}(-, X) \Rightarrow P.$$

Read that slowly, because every word matters:

- $X$ **satisfies** a universal property with respect to $F$ (or $P$) — the property doesn't belong to $F$ alone, it's a relationship between $X$ and $F$.
- The isomorphism has to be **natural**: it has to commute with the naturality squares from Chapter 1, not just be a bijection at each object.
- It has to be **chosen**. Remark 2.3.6 stresses this explicitly: it is not enough to say "there exists some natural isomorphism" — you have to name it, because the isomorphism itself carries data (the specific maps, like the projections $p_1, p_2$ of a product) that you need later. Two objects can both be abstractly isomorphic to $F$ without either one being *the* canonical representing object unless you've pinned down which isomorphism you mean.
- By Remark 2.3.2, $F$ (or $P$) is automatically **representable** in the sense of Section 2.1 — a universal property is just representability packaged with the specific witnessing isomorphism spelled out.

## Reading it as existence-and-uniqueness

The abstract phrasing "$X$ represents $F$" doesn't yet look like something useful to *compute with*. Perrone's real contribution in this section is unpacking what a natural isomorphism to a Hom-functor *means concretely*, and the unpacking is worth doing by hand because you'll do it again for every limit, colimit, and adjunction later in the book.

Take the presheaf case: $\alpha : \mathrm{Hom}_\mathcal{C}(-, X) \Rightarrow P$ a natural isomorphism. Chase the naturality square starting from $\mathrm{id}_X \in \mathrm{Hom}_\mathcal{C}(X,X)$ along a morphism $f : Y \to X$:

$$
\begin{array}{ccc}
\mathrm{Hom}_\mathcal{C}(X,X) & \xrightarrow{-\circ f} & \mathrm{Hom}_\mathcal{C}(Y,X) \\
\alpha_X \downarrow & & \downarrow \alpha_Y \\
PX & \xrightarrow{Pf} & PY
\end{array}
$$

Set $p := \alpha_X(\mathrm{id}_X) \in PX$ — this single element is the "generic instance" of the universal property, exactly analogous to how $\mathrm{id}_X$ was the seed of the Yoneda lemma itself. Commutativity forces $Pf(p) = \alpha_Y(f)$ for every $f : Y \to X$. Since $\alpha_Y$ is a *bijection* (it's a natural iso, not just a transformation), this says:

> For every object $Y$ and every element $x \in PY$, there is a **unique** morphism $f : Y \to X$ such that $Pf(p) = x$.

That's the whole content of a universal property, stripped of its Yoneda dressing: fix one canonical element $p \in PX$; then every "instance" $x$ living over any other object $Y$ factors through $X$ via a unique mediating morphism. Dually, a universal property given by a *functor* $F : \mathcal{C} \to \mathbf{Set}$ (rather than a presheaf) gives existence-and-uniqueness of mediating arrows going *out of* $X$, not into it.

This is exactly what the book's **dashed-arrow notation** is for. Whenever you see

$$X \dashrightarrow Y$$

in a diagram, it signals "this is not just any morphism — it is *the* morphism whose existence and uniqueness is guaranteed by a universal property." The dashed arrow is doing double duty as both an existence claim and a uniqueness claim, and you should read every occurrence of it that way for the rest of the book.

## Example 1: the cartesian product in $\mathbf{Top}$

Fix two topological spaces $X$ and $Y$. Consider the presheaf

$$P = \mathrm{Hom}_{\mathbf{Top}}(-, X) \times \mathrm{Hom}_{\mathbf{Top}}(-, Y) : \mathbf{Top}^{op} \to \mathbf{Set},$$

sending a space $S$ to the set of *pairs* of continuous maps $(f_1 : S \to X,\ f_2 : S \to Y)$. Perrone's intuition: this is a "combined observation" of $S$ made with two instruments at once, or two eyes looking at $S$ from two different angles.

The question the universal property answers is: **is $P$ representable?** Is there a single space $Z$ such that mapping into $Z$ is *the same thing*, naturally, as mapping into $X$ and into $Y$ simultaneously? Unpacking the natural isomorphism $\mathrm{Hom}_{\mathbf{Top}}(-, Z) \Rightarrow P$ exactly as above gives: fix $p = (p_1 : Z \to X,\ p_2 : Z \to Y) \in PZ$. Then for every $S$ and every pair $(f_1 : S \to X, f_2 : S \to Y)$, there must exist a **unique** $f : S \to Z$ making this diagram commute:

<svg viewBox="0 0 420 240" xmlns="http://www.w3.org/2000/svg" font-family="ui-monospace, SFMono-Regular, Menlo, monospace" font-size="16">
  <text x="210" y="30" text-anchor="middle" fill="#8a8a8a">S</text>
  <text x="60" y="140" text-anchor="middle" fill="#4a90d9">X</text>
  <text x="210" y="210" text-anchor="middle" fill="#c96442">Z</text>
  <text x="360" y="140" text-anchor="middle" fill="#4a90d9">Y</text>

  <line x1="200" y1="45" x2="80" y2="125" stroke="#8a8a8a" stroke-width="1.5" />
  <text x="120" y="80" fill="#8a8a8a">f1</text>

  <line x1="220" y1="45" x2="340" y2="125" stroke="#8a8a8a" stroke-width="1.5" />
  <text x="300" y="80" fill="#8a8a8a">f2</text>

  <line x1="210" y1="45" x2="210" y2="190" stroke="#c96442" stroke-width="1.5" stroke-dasharray="6,5" />
  <text x="228" y="120" fill="#c96442">f (unique)</text>

  <line x1="200" y1="200" x2="85" y2="150" stroke="#4a90d9" stroke-width="1.5" />
  <text x="130" y="185" fill="#4a90d9">p1</text>

  <line x1="220" y1="200" x2="335" y2="150" stroke="#4a90d9" stroke-width="1.5" />
  <text x="290" y="185" fill="#4a90d9">p2</text>
</svg>

The solution is the one you already know: $Z = X \times Y$ with the product topology, and $p_1, p_2$ the two projections. Given $f_1, f_2$, the mediating map is forced to be $f(s) = (f_1(s), f_2(s))$ — there is no other choice, because an element of $X \times Y$ *is* a pair, so any map into it is determined by its two components. (Continuity of this induced $f$, given continuity of $f_1$ and $f_2$, is Exercise 2.3.5 — a short argument about preimages of the generating open sets of the product topology.)

**The important subtlety (Remark 2.3.6): the projections are part of the data.** It's tempting to say "the universal property of the product is that there's a natural isomorphism to $\mathrm{Hom}(-,X) \times \mathrm{Hom}(-,Y)$" and stop there — but that's not enough. Two spaces can be abstractly homeomorphic without either one being *the* product in the canonical sense unless the specific maps $p_1, p_2$ are also fixed. This matters especially "in presence of symmetries" — e.g. $X \times X$ has a nontrivial automorphism (swap the factors) that fixes the underlying space but not the pair of projections. The universal property is a structure, not merely a property of the underlying object.

The book notes in passing that the same construction works for vector spaces (Exercise 2.3.7) and groups (Exercise 2.3.8) with essentially the same proof — a first hint that this is an instance of something category-independent. That "something" is the **limit**, developed fully in Chapter 3; the cartesian product is the limit of the two-object discrete diagram $\{X, Y\}$.

## Example 2: the tensor product in $\mathbf{Vect}$

The tensor product is the dual-flavored case: instead of representing a *presheaf* (giving arrows *into* the universal object), it represents a *functor* (giving arrows *out of* it) — and the functor itself is built not from plain Hom-sets but from bilinear maps.

A map $f : V \times W \to U$ between vector spaces is **bilinear** if it's linear in each argument separately, holding the other fixed. Bilinear is a strictly weaker condition than linear-as-a-map-$V\times W \to U$: the multiplication map $\mathbb{R} \times \mathbb{R} \to \mathbb{R}$, $(x,y) \mapsto xy$, is bilinear but not linear (scaling both inputs by 2 scales the output by 4, not 2). Signed parallelogram area and inner products are further examples.

Fix $V, W$. Then $\mathrm{Bilin}(V, W; -) : \mathbf{Vect} \to \mathbf{Set}$, sending $U \mapsto$ {bilinear maps $V \times W \to U$}, is a genuine functor (post-composing a bilinear map with a linear map keeps it bilinear — Exercise 2.3.11). The universal-property question: is this functor representable? Is there a space $Z$ and a natural isomorphism

$$\mathrm{Hom}_{\mathbf{Vect}}(Z, -) \Rightarrow \mathrm{Bilin}(V, W; -)?$$

Unpacking exactly as before: fix $q \in \mathrm{Bilin}(V,W;Z)$, i.e. a *bilinear* map $q : V \times W \to Z$. Then for every vector space $S$ and every bilinear $b : V \times W \to S$, there must be a **unique linear** map $f : Z \to S$ with $f \circ q = b$:

<svg viewBox="0 0 420 240" xmlns="http://www.w3.org/2000/svg" font-family="ui-monospace, SFMono-Regular, Menlo, monospace" font-size="16">
  <text x="210" y="30" text-anchor="middle" fill="#8a8a8a">V × W</text>
  <text x="90" y="210" text-anchor="middle" fill="#c96442">Z = V ⊗ W</text>
  <text x="360" y="140" text-anchor="middle" fill="#4a90d9">S</text>

  <line x1="200" y1="45" x2="110" y2="185" stroke="#4a90d9" stroke-width="1.5" />
  <text x="130" y="120" fill="#4a90d9">q (bilinear)</text>

  <line x1="230" y1="45" x2="345" y2="125" stroke="#8a8a8a" stroke-width="1.5" />
  <text x="290" y="80" fill="#8a8a8a">b (bilinear)</text>

  <line x1="150" y1="195" x2="330" y2="150" stroke="#c96442" stroke-width="1.5" stroke-dasharray="6,5" />
  <text x="200" y="195" fill="#c96442">f (unique, linear)</text>
</svg>

*(As the book flags, the two solid arrows here are bilinear, not linear — this diagram is a convenient picture, not literally a diagram internal to $\mathbf{Vect}$.)*

The solution is $Z = V \otimes W$, the tensor product, with $q(v,w) = v \otimes w$. Why does this work, concretely? Every element of $V \otimes W$ is a linear combination of "pure tensors" $v \otimes w$ — so a *linear* map out of $V \otimes W$ is completely pinned down by its values on pure tensors. Given any bilinear $b : V \times W \to S$, define $f(v \otimes w) := b(v,w)$ and extend linearly; this is well-defined and linear precisely because $b$ is bilinear (bilinearity is exactly the compatibility condition that makes this extension consistent). Uniqueness follows because the pure tensors span $V \otimes W$, so no two distinct linear maps can agree on all of them.

Again, Remark-2.3.6-style: the map $q$ is not incidental — it *is* part of the tensor product's structure, exactly as $p_1, p_2$ were part of the product's structure. "The tensor product" without its canonical bilinear map $q$ isn't fully specified. The intuitive gloss the book gives: the tensor product is "the unique way to combine $V$ and $W$ in terms of bilinear maps on them," mirroring "the cartesian product is the unique way to combine $X$ and $Y$ in terms of maps into them." Same template, dual direction, different structure on the arrows (bilinear vs. plain).

## The common shape

Both examples instantiate Definition 2.3.1 identically once you strip away the surface content:

| | Cartesian product ($\mathbf{Top}$) | Tensor product ($\mathbf{Vect}$) |
|---|---|---|
| Representing... | a presheaf ($\mathrm{Hom}(-,X)\times\mathrm{Hom}(-,Y)$) | a functor ($\mathrm{Bilin}(V,W;-)$) |
| Direction of mediating arrow | into $Z$ | out of $Z$ |
| Canonical structure map(s) | $p_1, p_2$ (projections) | $q$ (the tensor map) |
| Universal object | $X \times Y$ | $V \otimes W$ |
| "Instance" being represented | pairs of maps $S \to X, S \to Y$ | bilinear maps $V \times W \to S$ |

This table is exactly why Perrone's Key Question 3 for this chapter — how can a product-type construction and a bilinear-map construction be "the same kind of thing" — has a clean answer: both are the *representing object of a functor built from $X$ and $Y$*, full stop. The functor's shape (plain-map pairs vs. bilinear maps) determines what the universal object looks like, but the *pattern* — pick the generic element, chase naturality, get existence-and-uniqueness of a mediating map — is category-independent machinery. That machinery is the actual subject of Section 2.3; the product and tensor product are just its first two demonstrations.

## Grounding: universal properties as "there's exactly one sane implementation"

**Rust.** The product case is close to something you already write constantly. Given `f1: S -> X` and `f2: S -> Y`, there is exactly one sane way to build a map `S -> (X, Y)`:

```rust
fn pair<S, X, Y>(f1: impl Fn(&S) -> X, f2: impl Fn(&S) -> Y) -> impl Fn(&S) -> (X, Y) {
    move |s| (f1(s), f2(s))
}

// The projections are the "universal maps" p1, p2 from Definition 2.3.1's example:
fn p1<X, Y>(pair: &(X, Y)) -> &X { &pair.0 }
fn p2<X, Y>(pair: &(X, Y)) -> &Y { &pair.1 }
```

The universal property says something stronger than "this function exists": it says this is the *only* function `S -> (X, Y)` that recovers `f1` and `f2` when composed with `.0` and `.1`. That "only" is not a style preference — it's forced by the fact that a tuple's identity *is* its two components; there is no hidden state a different implementation could vary. This is precisely why `(X, Y)` is *the* product type in Rust's type system and not merely *a* type that happens to hold both — the mediating-map uniqueness argument from the book is the formal version of "a struct with exactly these two public fields and no others has exactly one reasonable constructor from `(f1, f2)`."

The tensor product doesn't have as natural a `std`-level Rust analogue (Rust's type system has no bilinear-map primitive), so per the style guidance here's the honest statement instead of a strained one: the closest engineering intuition is a **normal form / canonicalization pass** — $V \otimes W$ is the "flattened, canonical buffer" such that any bilinear operation on $(V, W)$ factors through first canonicalizing into that buffer, then applying an ordinary (linear) pass. This is the same shape as compiling a two-argument operation down to a single-argument one over a combined representation, but it's an analogy, not a translation — flag it as such rather than pretending Rust has this concept natively.

**Lean.** This is where the correspondence stops being an analogy and becomes closer to a citation. Mathlib's category theory library defines categorical products and the tensor product using *exactly* this universal-property template, not an ad hoc concrete construction:

- `CategoryTheory.Limits.prod X Y` is defined via `IsLimit`, and `CategoryTheory.Limits.prod.lift (f1 : S ⟶ X) (f2 : S ⟶ Y) : S ⟶ prod X Y` is the mediating map $f$ from the diagram above — its defining property, `prod.lift_fst`/`prod.lift_snd`, is literally $p_1 \circ f = f_1$, $p_2 \circ f = f_2$, and uniqueness is proved separately as `prod.hom_ext`.
- `TensorProduct.lift : (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P)` is, almost verbatim, the natural bijection $\mathrm{Bilin}(V,W;S) \cong \mathrm{Hom}(V\otimes W, S)$ from Example 2.3.12 — a curried bilinear map goes in, the unique linear map out of the tensor product comes out.

The reason this matters for your elaborator project specifically: a **universal property is, structurally, exactly what "the most general solution to a set of constraints" means** — and that's the same shape you need for metavariable resolution. When an elaborator resolves an implicit argument, it isn't just finding *some* term satisfying the surrounding typing constraints; when Miller pattern unification applies, it finds *the* term — the unique most-general solution the constraint set determines, with anything else forced to factor through it. Existence-and-uniqueness-of-a-mediating-map is the categorical vocabulary for the same property that makes a most-general unifier well-defined: any other unifier is a specialization (factors through) the most general one. Definition 2.3.1's insistence that the witnessing map be *chosen*, not merely asserted to exist, mirrors why a unification algorithm has to actually *produce* a substitution, not just prove one exists.

## Where this leads

Section 2.3 is deliberately minimal — two examples, no general theory yet — because the general theory is the entire content of Chapter 3. There, "cone/cocone over a diagram" replaces "pair of maps into $X,Y$" as the shape being represented, and **limit**/**colimit** are defined as exactly this same existence-and-uniqueness pattern applied to an arbitrary diagram — the cartesian product becomes the special case of a limit over a two-object discrete diagram, and the disjoint union/coproduct is the dual colimit. The tensor product's "represent a functor of bilinear maps" pattern reappears almost unchanged when the book later builds free constructions and adjunctions (Chapter 4): a left adjoint is defined by a universal property that is, again, existence-and-uniqueness of a mediating morphism out of a "most efficient" object. If you keep this section's diagram-chase in your fingers, you can read the rest of the book's constructions — limits, colimits, adjunctions, free algebras — as re-skins of the same argument.

[[book-guidelines|↩ Back to guidelines]]
