---
title: Fibrancy and Cofibrancy
source: "Two-Level Type Theory and Applications (Annenkov, Capriotti, Kraus, Sattler)"
chapter: "Chapter 3, §3.2–3.4 (pp. 24–34)"
tags:
  - type-theory
  - two-level-type-theory
  - homotopy-type-theory
  - fibrations
  - cofibrations
  - category-theory
---

[[book-guidelines|↩ Back to guidelines]]

## Why the outer level needs a vocabulary for "behaves like an inner type"

2LTT gives you two universes glued together by a conversion function $c \colon \mathcal{U}^i \to \mathcal{U}$: an *inner* universe of homotopical (HoTT) types, and an *outer* universe of ordinary, UIP-satisfying types. The whole point of the two-level setup is to let you *reason about* inner, homotopical structure using outer, set-truncated tools — matching objects, limits over categories, induction on natural numbers — none of which the inner level supports well on its own (recall from Chapter 2: an internal fibrant-replacement type former is provably impossible without collapsing the inner level to UIP). But the moment you start building outer-level scaffolding *around* inner types, you constantly need to ask two questions:

1. Is this outer type actually (isomorphic to) an inner type — can I trust it to carry inner homotopical structure like an identity type with the right behavior?
2. Given a map between outer types, does it "act like" a nice map of inner types — a Kan fibration, in the topologist's or simplicial-set language — even though it's phrased using only outer machinery (pullbacks, fibres, dependent sums)?

Fibrancy answers (1); fibrations answer (2). Chapter 3 needs both before it can do anything homotopically meaningful in the outer level — this is the "basic tools" chapter, deliberately dry, because everything from Reedy diagrams (Chapter 4) to semi-Segal types (Chapter 4.7) is built on top of these definitions.

Cofibrancy is the dual notion, and it earns its place for a more specific reason: some very ordinary outer-level constructions — most importantly, exponentiating by a finite type — do *not* automatically preserve fibrancy in 2LTT the way they would if you were working purely in HoTT. Cofibrant types are exactly the ones for which exponentiation *does* preserve fibrancy, and it turns out you need a proof of that, not just faith.

## Fibrant types: "this outer type is secretly an inner type"

**Definition 3.4.** A type $A : \mathcal{U}$ is **fibrant** if it is isomorphic to some inner type $A' : \mathcal{U}^i$ (i.e. $A \cong c(A')$). It is **trivially fibrant** if in addition $A'$ is (inner-)contractible.

Two things to notice immediately, because they trip people up:

- **Fibrancy is data, not a proposition.** Being fibrant is not "at most one witness" — a fibrant type $A$ *carries* a specific inner type $A'$ and a specific isomorphism $f : A \cong A'$ as part of its structure. If you say "$A$ is fibrant exactly when $B$ is," what you formally mean is a pair of maps back and forth relating their fibrancy witnesses — this is the paper's "propositions-as-types" convention applied to structure rather than truth. This convention carries straight through to fibrations, cofibrations, and their Reedy variants later in the book — get used to reading "$X$ is a $P$" as "$X$ comes with a witness of $P$," not "the proposition $P(X)$ holds."
- **$\mathcal{U}_{\mathrm{fib}}$, the type of fibrant types, is not itself generally fibrant** (though it is in some intended models, e.g. simplicial sets). The map $\mathcal{U}_{\mathrm{fib}} \to \mathcal{U}$ is best understood as an *isofibration replacement* of the coercion functor $\mathcal{U}^i \to \mathcal{U}$: instead of the raw coercion, you get a version that behaves well with respect to isomorphism (fibrant types are closed under isomorphism by construction).

**What breaks without this.** Without a name for "fibrant," you'd be forced to write every construction directly in terms of literal inner types and the coercion $c$, tracking naturality of $c$ by hand every time you wanted to combine two pieces of homotopical data built at different points in a proof. Fibrancy lets you talk about "the type of paths," "the type of equivalences," etc. as *outer* citizens that happen to carry inner content, so ordinary outer-level tools (dependent sums, universes, category theory) apply to them directly.

**Closure properties (Lemma 3.5).** Fibrant types are closed under the type formers that $c$ preserves up to isomorphism (recall Lemma 2.11: $c$ preserves $1$, $\Sigma$, $\Pi$ but not $+, 0, \mathbb{N}$, or equality on the nose):

- The unit type $1$ is trivially fibrant.
- If $A : \mathcal{U}_{\mathrm{fib}}$ and $B : A \to \mathcal{U}_{\mathrm{fib}}$, then $\Sigma_A B$ is fibrant (trivially fibrant if $A$ and $B$ are).
- If $A : \mathcal{U}_{\mathrm{fib}}$ and $B : A \to \mathcal{U}_{\mathrm{fib}}$, then $\Pi_A B$ is fibrant (trivially fibrant if $B$ is).

The proof pattern is worth internalizing because it recurs everywhere in this chapter: internalize the inner operation ($\Pi^i$, say) as an outer function $\mathcal{U}^i$-indexed, produce a comparison isomorphism with the outer $\Pi$ built from coerced components, then bootstrap from literal inner families to arbitrary *fibrant* families by reindexing along the fibrancy witness isomorphisms. The "hard part" (closure under $\Pi$/$\Sigma$/$1$) is a one-time semantic fact about $c$; everything else is isomorphism transport.

**Definition 3.6 (equivalence between fibrant types).** A function $f : A \to B$ between fibrant types (with underlying inner types $A'$, $B'$) is an **equivalence** if the corresponding inner function $A' \to^i B'$ is an inner equivalence (HoTT sense). This notion technically depends on the fibrancy witnesses, but different witnesses give logically equivalent, propositionally fibrant results (their underlying inner type is an inner HoTT-proposition), so by the paper's convention we still say "equivalence" is isomorphism-invariant. Properties like 2-out-of-6 lift directly from the inner level for free.

### Grounding: fibrancy as a refinement type / typestate

The closest engineering analogue is a **refinement type carrying a proof obligation as a field**, not just a boolean tag:

```rust
// A "fibrant" outer type: carries the inner witness, not just a flag.
struct Fibrant<A> {
    outer: PhantomData<A>,       // the outer type A
    inner: InnerTypeHandle,      // the specific A' : U^i
    iso: Isomorphism<A, InnerCoerced>, // A ≅ c(A'), the actual data
}
```

Crucially, `Fibrant<A>` is not `impl Fibrant for A {}` (a trait with no associated data) — it's a *struct*, because two different `Fibrant<A>` values (two different choices of `A'` and the isomorphism) are not required to be equal, only interconvertible. This is precisely the "fibrancy is proof-relevant data" warning above, and it's the same shape of design decision as choosing `enum` variants that carry evidence (a `Checked<T>` wrapper holding both the value and the certificate) over a marker trait. If your Rust verifier ever needs a "this type is really an SMT-decidable base type" tag, model it this way: the coercion witness is inspectable data your solver backend can consult, not an erased compile-time fact.

In Lean, this is exactly the shape of a **type class carrying data**, e.g. `class Fibrant (A : Type) where inner : Type; iso : A ≃ inner`. This is worth flagging explicitly because it is *literally* how the paper's own formalisation strategy in Lean (covered under "[[Formalisation-of-2LTT-in-Proof-Assistants|Formalisation of 2LTT in Proof Assistants]]," Chapter 6) tracks fibrancy — a type class attached to outer types, with instance resolution standing in for "finding the fibrancy witness." Type-class *resolution* here is doing the job of *elaboration-time proof search for a specific kind of metadata* — the same mechanism your project's elaborator will use for implicit-argument and instance resolution, just applied to a homotopical property instead of, say, a `Monad` instance.

## Fibrations: maps whose fibres are fibrant

Recall the ordinary (non-homotopical) fibre of $p : Y \to X$ over $x : X$: $p^{-1}(x) :\equiv \Sigma(y:Y).\, p(y) = x$, built from the *outer* identity type — not to be confused with the *homotopy* fibre, which only makes sense for inner types using the inner identity type. More generally, $A$ "is the fibre of $p$ over $x$" if $A$ arises as the pullback of $p$ along $1 \to X$ (so $A \cong p^{-1}(x)$).

**Definition 3.7.** $p : Y \to X$ is a **(trivial) fibration** if all its fibres are (trivially) fibrant. Notation: $Y \twoheadrightarrow X$.

Immediate consequences (Remark 3.8):

- $A \to 1$ is a (trivial) fibration exactly when $A$ is (trivially) fibrant — fibrancy of types is the special case of fibrancy of maps into the terminal object, matching the standard move in abstract homotopy theory of treating "fibration" as primitive and "fibrant object" as a derived notion.
- Every trivial fibration is a fibration (contractible $\Rightarrow$ inhabited-and-inner, trivially, but the converse direction is the substantive one).
- **This internal definition is genuinely weaker than the external one in the simplicial-set model.** A map $Y \to X$ of simplicial sets with every fibre $Y_x$ a Kan complex (for $x \in X_0$) is *not* necessarily a Kan fibration — the internal "quantify over all elements of $X$" secretly externalizes to "quantify over all $[n] \in \Delta$ and all $x \in X_n$," and the fibrancy witness becomes a naturality-coherent family $\sigma([n], x) \in \mathcal{U}_n$ (the universe of Kan fibrations), not a pointwise condition on vertices alone. This is exactly the gap that motivates the *Reedy* fibration machinery of Chapter 4 — plain internal fibrancy of fibres, checked only at points, isn't enough once you have higher-dimensional shapes; you need the fibrancy condition to interact correctly with the *matching object* at every level.

**Lemma 3.9** gives four equivalent reformulations of "$p$ is a fibration," the most useful being: $p$ is isomorphic (over $X$) to a dependent-sum projection $\Sigma_X Y' \to X$ for some family $Y' : X \to \mathcal{U}_{\mathrm{fib}}$ (or, sharpening further, $Y' : X \to \mathcal{U}^i$). If $X$ itself is fibrant with underlying inner type $X'$, this upgrades to: $p$ is isomorphic to the outer image of a literal *inner* dependent projection $\Sigma^i_{X'} Y' \to^i X'$. In other words: every fibration is, up to isomorphism, "secretly" a family of inner types varying over the base — the definition via fibres is just the fibre-wise unpacking of that fact. This normal form is what every subsequent proof in the section actually manipulates.

**Closure (Lemma 3.10).** (Trivial) fibrations are closed under pullback, finite composition, and finite products — all essentially free once you have the normal form above and Lemma 3.5's closure results.

**Lemma 3.11 (sections).** Every trivial fibration has a section: write it as $\Sigma(b:B).\,X(b) \to B$ with $X(b)$ inner-contractible for all $b$, then extract the *centre of contraction* pointwise to get $\Pi_{b:B} X(b)$. This is the internal-type-theory analogue of "an acyclic fibration always has a section" from classical homotopy theory, and the proof is completely constructive — contractibility literally hands you the section value.

**Lemma 3.12 (Whitehead-style characterisation).** For $p : E \to B$ between *fibrant* types: $p$ is a trivial fibration $\iff$ $p$ is a fibration *and* an equivalence. The proof reduces $p$ to the inner dependent projection $\Sigma^i(b:B).X(b) \to^i B$ and invokes the standard HoTT fact that this projection is an equivalence exactly when all its fibres $X(b)$ are contractible. This is the internal-2LTT incarnation of "fibration + weak equivalence = trivial (acyclic) fibration," one of the defining interactions in any model category — and it's the lemma that lets later sections freely convert between "is a trivial fibration" and "is a fibration that happens to be invertible up to homotopy."

### Grounding: fibrations as typestate-checked accessors

Think of a fibration $p : Y \twoheadrightarrow X$ as a function that is *guaranteed*, for every possible input, to land you in a "nice" (fibrant) fibre — a typestate machine where every state transition provably preserves an invariant:

```rust
// p : Y -> X is a fibration: every fibre carries a fibrancy witness.
trait Fibration<X, Y> {
    fn fibre_at(&self, x: &X) -> Fibrant<Y>; // never just "Y" — always with the witness
}
```

Compare this to the **soundness contract of a type checker's `typeOf` function**: a well-typed term always yields a well-formed type, never garbage. Fibrations are the homotopical version of that same "the output always satisfies invariant $P$" discipline, just with $P$ = "is fibrant" instead of $P$ = "is well-formed." In Lean, Lemma 3.9's normal form ($p \cong \Sigma_X Y' \to X$) is precisely the shape of a **dependent record / sigma-type-indexed family** — `Σ (Y' : X → Type), (b : X) × Y' b`, i.e. the same representation Lean uses internally for a family of types indexed by a base, which is what a well-formed *inductive family*'s constructors amount to.

## The Leibniz construction and pullback exponentials

Before defining cofibrations, the paper needs a general categorical gadget: the **Leibniz construction**, following Riehl–Verity [RV14].

Given a bifunctor $F : \mathcal{C} \times \mathcal{D} \to \mathcal{E}$ and maps $f : A \to B$ in $\mathcal{C}$, $g : C \to D$ in $\mathcal{D}$, the **Leibniz action** $\widehat{F}(f,g)$ is the induced map out of the pushout corner:

$$
F(A,D) +_{F(A,C)} F(B,C) \xrightarrow{\ \widehat{F}(f,g)\ } F(B,D)
$$

(assuming this pushout exists), giving a bifunctor $\widehat{F} : \mathcal{C}^{\to} \times \mathcal{D}^{\to} \to \mathcal{E}^{\to}$ on arrow categories when $\mathcal{E}$ has all pushouts.

Two named specializations matter here:

- The Leibniz action of the **product functor** $(-)\times(-)$ in a category with finite products is called the **pushout product**.
- The Leibniz action of the (dualized) **exponential functor** $\exp^{\mathrm{op}} : \mathcal{C} \times \mathcal{C}^{\mathrm{op}} \to \mathcal{C}^{\mathrm{op}}$ in a Cartesian closed category is called the **pullback exponential**. (The dualized signature is what turns the pushout-in-$\mathcal{C}^{\mathrm{op}}$ into a pullback-in-$\mathcal{C}$ — hence the name.)

Since $\mathcal{U}$ (the category of types) is Cartesian closed *and* has pullbacks, it carries a pullback exponential bifunctor $\widehat{\exp} : (\mathcal{U}^{\mathrm{op}})^{\to} \times \mathcal{U}^{\to} \to \mathcal{U}^{\to}$: given $f : A \to B$ and $p : Y \to X$, it produces

$$
(B \to Y) \xrightarrow{\ \widehat{\exp}(f,p)\ } (B \to X) \times_{(A \to X)} (A \to Y).
$$

**Why bother with this abstraction?** Because "cofibration" is going to be defined as "this specific map, built by pullback-exponentiating $f$ against arbitrary fibrations, always lands you back in fibrations" — and stating *that* cleanly, plus proving its closure properties (pushouts, composites, coproducts, products), is dramatically easier once you have the general Leibniz calculus to lean on (literally: Lemma 3.21's proof just cites general categorical facts about $\widehat{F}$ from [RV14] rather than re-deriving them for $\mathcal{U}$ each time).

### Grounding: Leibniz construction as a generic "lift the diff" combinator

If you've ever written a diffing/patching library, the pushout-product shape should feel familiar: given "what changed on the left" ($f$) and "what changed on the right" ($g$), the Leibniz action computes the *minimal combined object* that's consistent with both changes, then maps it into the fully-changed target. In Rust terms, this is close to a generic `zip`-like combinator over two "edit scripts," except instantiated categorically. This construction rarely shows up by that name in mainstream software engineering — it's genuinely homotopy-theoretic plumbing — so resist the urge to force a strained analogy here; the honest grounding is "this is the general machine that makes the pushout-product/pullback-exponential axiom of Cartesian-closed model categories statable," full stop, and it's worth knowing the name because [RV14] and the wider Riehl–Shulman synthetic-$(\infty,1)$-category literature use it constantly.

## Cofibrations and cofibrant types

**Motivation, stated directly by the authors:** if $B$ is fibrant, so are $B \times B$ and $B \times B \times B$, and more generally, for any *externally fixed* natural number $n$ in HoTT's meta-theory, the $n$-fold product of $B$ is fibrant. Inside 2LTT this corresponds to the function type $\mathrm{Fin}_n \to B$ where $\mathrm{Fin}_n$ is the *outer* finite type. But here's the catch: $(\mathrm{Fin}_2 \to B) \cong B \times B$ holds for the *outer* $\mathrm{Fin}_2$, yet the analogous statement for the *inner* $\mathrm{Fin}_2^i$ only gives you a weaker inner *equivalence*, not an isomorphism. And crucially, $\mathrm{Fin}_n \to B$ being fibrant is **not** handed to you for free by the rules of 2LTT — it requires an actual proof (Lemma 3.25). Cofibrant types are exactly the types $B$ for which exponentiating-by-$B$ is *guaranteed* to preserve fibrancy, and cofibrations are the map-level generalization of that guarantee.

**Definition 3.13.** A function $f : A \to B$ is:

- a **cofibration** if $\widehat{\exp}(f, -)$ preserves fibrations and trivial fibrations;
- a **trivial cofibration** if $\widehat{\exp}(f,-)$ sends fibrations to *trivial* fibrations.

A type $B$ is (**trivially**) **cofibrant** if $0 \to B$ (the map out of the empty type) is a (trivial) cofibration.

**Unfolded (Remark 3.14(i)):** $f : A \to B$ is a cofibration exactly when, for every fibration $p : Y \twoheadrightarrow X$ and every commuting square

$$
\begin{array}{ccc}
A & \to & Y \\
{\scriptstyle f}\downarrow & \nearrow & \downarrow{\scriptstyle p} \\
B & \to & X
\end{array}
$$

the *type of diagonal fillers* is fibrant (and trivially fibrant if $p$ was a trivial fibration). This is the "pushout-product axiom, dualized" reading Remark 3.15 flags explicitly — it is the internal-type-theoretic mirror of the pushout-product axiom for Cartesian-closed model categories, phrased via pullback exponentials instead of pushout products. Concretely: for cofibrations $f$ against fibrations $p$, you don't just get *some* filler — you get a whole *fibrant space* of fillers, coherently.

**Why this matches (and diverges from) the topological picture (Remark 3.15).** In the simplicial-set model, restricted to the empty context, this notion of (trivial) cofibration coincides with the Kan model structure's own (trivial) cofibrations — the Kan model structure is Cartesian closed, so the general fact transfers both ways (via Lemma 3.11 giving sections, hence lifts, in one direction). But the correspondence is **not local**: in a nonempty context $\Gamma$, the slice category over $\Gamma$ is *not* Cartesian closed in general, so cofibrations "in context $\Gamma$" (2LTT's internal notion) can be strictly fewer than the model-structure cofibrations over $\Gamma$. The paper gives a concrete counterexample with $\Gamma = \Delta^1$ and the map $\{0\} \to \Delta^1$: it's a trivial cofibration of the ambient model structure but fails to be even a cofibration in 2LTT's internal sense over that context. This is a genuinely important caveat — it tells you the internal notion is *doing real, non-trivial work*, not just repackaging an external one.

**Anodyne maps, introduced by contrast (Remark 3.16).** You might expect "cofibration" to just mean "has the left lifting property against (trivial) fibrations" — but the authors explicitly warn that this *doesn't* capture the cofibrancy intuition sketched above, and reserve the name **anodyne** for maps with that left-lifting-property (formalized later as Definition 4.11: $i : A \to B$ is anodyne if for every fibration $p : Y \to X$, the pullback exponential $(B\to Y) \to (B\to X)\times_{A\to X}(A\to Y)$ has a *section* — equivalently, by Lemma 4.12, if every term defined on $A$ extends along $i$ to a term defined on all of $B$, for any fibrant family over $B$). So: (trivial) cofibrations and anodyne maps are two genuinely different generalizations of "nice inclusion," and the paper is careful to keep them apart — (trivial) cofibrations and (trivial) fibrations here do **not** form a weak factorisation system, which is exactly why anodyne maps have to be defined and studied separately (they reappear as the backbone of Reedy fibrant factorisation in Chapter 4.4).

**Lemma 3.17 (the promised dual of 3.12).** For $f : A \to B$ between *fibrant* types: $f$ is a trivial cofibration $\iff$ $f$ is a cofibration and an equivalence. The proof is a genuinely elegant Yoneda-style argument: build the unique retraction $g : B \to A$ with $g \circ f = \mathrm{id}_A$ from the (trivially fibrant, hence contractible) type of fillers of one square, then use fillers of a *second* square to force $f \circ g = \mathrm{id}_B$ by uniqueness. This is the cofibration-side mirror image of Lemma 3.12.

**Lemma 3.18 (the working characterisation) and Corollary 3.20 (its $A=0$ special case).** $f : A \to B$ is a cofibration exactly when, for every family $Y' : B \to \mathcal{U}_{\mathrm{fib}}$, the induced map $\Pi_B Y' \to \Pi_A(Y' \circ f)$ is a (trivial) fibration. Specializing to $f = (0 \to B)$: **$B$ is cofibrant exactly when $\Pi_B Y'$ is (trivially) fibrant for every (trivially) fibrant family $Y'$ over $B$** — i.e., dependent products over a cofibrant base preserve fibrancy. This is the operative definition used in every subsequent closure proof.

**Closure properties, largely inherited "for free" from the dual fibration results via general Leibniz-calculus facts (Lemma 3.21, Lemma 3.23, Lemma 3.25):**

- (Trivial) cofibrations are closed under pushouts (when they exist — recall $\mathcal{U}$ doesn't have all pushouts), finite composition, and finite coproducts.
- The pushout product of two cofibrations is again a cofibration (a trivial cofibration if either factor is), by the two-variable-adjunction argument transported through the Leibniz calculus (Lemma 3.23).
- **Fibrant types are cofibrant** (Lemma 3.25(i)) — immediate from Corollary 3.20 plus Lemma 3.5(iii): exponentiating a fibrant family by a *fibrant* base preserves fibrancy, because $\Pi$ of fibrant families over a fibrant base is fibrant.
- Cofibrant types are closed under finite coproducts and finite products, and $\Sigma_A B$ is cofibrant whenever $A$ and (every fibre of) $B$ are.
- **Finite types are cofibrant** — a direct corollary of $1$ being cofibrant (nullary pushout-product unit) plus closure under coproducts.

The single most load-bearing fact for everything downstream is **"fibrant $\Rightarrow$ cofibrant."** It is what lets the paper bootstrap a supply of cofibrant examples (unit type, finite types, $\Sigma$-types of cofibrant families) essentially without extra work, which Chapter 4 then needs constantly when it has to check that diagrams and boundary inclusions over inverse categories are (Reedy) cofibrant.

### Grounding: cofibrations as "safe substitution contexts"

The cleanest software analogy for a cofibration is a **context into which you can always safely substitute without breaking a well-formedness invariant** — the same shape of guarantee that makes substitution lemmas in a type checker's metatheory work. If $f : A \to B$ is a cofibration and you have a "good" (fibrant) family $Y'$ indexed over $B$, restricting along $f$ (going from $\Pi_B Y'$ to $\Pi_A(Y' \circ f)$) is guaranteed to stay "good" (fibration/trivial-fibration) — nothing pathological happens when you narrow your domain of quantification. Concretely, in a Rust verifier, this is the same discipline as ensuring that **narrowing a refinement-typed context along an inclusion of variables never invalidates the verification conditions already discharged** — a soundness property you'd want to state and prove exactly once, generically, rather than per-construct.

```python
# Toy sketch: "cofibrant base" as "quantifying over it never breaks niceness"
def is_cofibrant(B, is_fibrant_family):
    # B is cofibrant iff, for every fibrant family Y' over B,
    # the dependent product Pi_B Y' is again fibrant.
    return all(is_fibrant(pi_type(B, Yp)) for Yp in fibrant_families_over(B))
```

This is intentionally a *sketch*, not load-bearing code — the actual content is the universal quantification over all fibrant families, which no five-line snippet can check; the value here is purely in making Corollary 3.20's shape legible before you re-read the LaTeX.

## Synthesis: what this section buys the rest of the book

```
Fibrant types (Def 3.4)  ---closed under 1, Σ, Π (Lem 3.5)---> Ufib
        │
        │ (special case: maps into 1)
        ▼
Fibrations (Def 3.7) --closed under pullback/comp/product (Lem 3.10)--> normal form Σ_X Y' → X (Lem 3.9)
        │                                                                          │
        │ dualize via Leibniz/pullback-exponential                                │ trivial fib. + fibrant ⟺ equivalence (Lem 3.12)
        ▼                                                                          │
Cofibrations (Def 3.13) --closed under pushout/comp/coproduct (Lem 3.21)--> fibrant ⟹ cofibrant (Lem 3.25)
        │
        │ contrasted with (Remark 3.16)
        ▼
Anodyne maps (Def 4.11, forward reference) — left lifting property against fibrations
```

Fibrancy and cofibrancy are the load-bearing vocabulary for *everything* that follows:

- **Chapter 4 ([[Reedy-Fibrant-Diagrams|Reedy fibrant diagrams]])** cannot even state what a "Reedy fibration" is without this chapter's notion of fibration (a Reedy fibration is defined by requiring a certain map into a *matching object* to be a fibration in exactly this sense), and its factorisation results (anodyne-then-Reedy-fibration) depend on knowing which types are cofibrant (so that boundary inclusions of diagrams behave well).
- **Chapter 4.7 (semi-Segal types, univalent $(\infty,1)$-categories)** is defined as "Reedy fibrant and local with respect to inner horn inclusions" — a direct descendant of the fibration/anodyne vocabulary developed here.
- The recurring warning that the *internal* notion of fibration doesn't coincide with the *external* Kan-fibration notion pointwise (Remark 3.8(ii)) is precisely the gap Reedy fibrancy is built to close.

**Connection to the standing project (`type-theory` focus area).** The fibrant/cofibrant distinction is a clean, non-trivial instance of a pattern your compiler project will need repeatedly: *defining a semantic property (here, "carries homotopical structure") purely in terms of syntactic/categorical closure conditions, then proving a hierarchy of derived characterizations (Lemma 3.9's normal form, Lemma 3.12's "fibration + equivalence = trivial fibration") that make the property tractable to check compositionally instead of by brute-force unfolding.* That's exactly the discipline behind a soundness-preserving type checker: define well-formedness, then prove closure lemmas (substitution, weakening, narrowing) so you never have to re-derive well-formedness from scratch at every node of a derivation. The Lean-side fibrancy-as-type-class encoding mentioned above (and treated properly in the "Formalisation of 2LTT in Proof Assistants" topic) is the most direct bridge: it is literally an elaboration/instance-resolution mechanism carrying a homotopical proof obligation, the same machinery your elaborator's metavariable resolution will lean on for very different (but structurally analogous) obligations.
