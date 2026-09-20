---
title: Functors and Natural Transformations
source: "Topoi: The Categorial Analysis of Logic — Goldblatt"
chapter: "Chapter 9: Functors"
pages: "194–210"
tags:
  - category-theory
  - functors
  - natural-transformations
  - presheaves
  - topos-theory
  - type-theory-connections
---

[[book-guidelines|↩ Back to guidelines]]

## Why this chapter exists here

Chapter 8 finished the story of a *single* topos — its internal Heyting algebra, its Kripke-style semantics. But Goldblatt is heading somewhere specific: he wants to show that $\mathbf{Set}^P$, the category of "$P$-indexed families of sets varying compatibly over a poset $P$," is *itself* a topos, and that its internal logic reproduces Kripke semantics exactly. To even state what $\mathbf{Set}^P$ *is*, you need a notion of "structure-preserving map between categories" (a functor) and a notion of "map between two such maps" (a natural transformation) — because $\mathbf{Set}^P$'s objects turn out to be functors $P \to \mathbf{Set}$, and its arrows turn out to be natural transformations between them. This chapter is the machine shop for Chapter 10, not a detour.

There is a second reason this chapter matters more than a typical prerequisite chapter: functor categories $\mathscr{D}^{\mathscr{C}}$ (Goldblatt writes them $\mathrm{Funct}(\mathscr{C}, \mathscr{D})$ or $\mathscr{D}^{\mathscr{C}}$) are the categorical model of **presheaves**, and presheaf categories are the standard semantic universe for dependent type theory (categories-with-families, natural models, the whole "contexts as objects, substitutions as arrows" picture). Every naturality square you learn to read here is, later, the exact shape of the coherence condition that makes substitution well-behaved in a type theory. Keep that in the back of your mind — it surfaces explicitly at the end.

## 9.1 The concept of a functor

**What breaks without it.** Chapter 3 gave you categories: objects and arrows, composition, identities. But a category is a single "world." As soon as you want to compare two worlds — say, relate the category of posets to the category of sets, or relate a monoid's arrow structure to the topos $\mathbf{Set}$'s — you need a *map between categories*. An arbitrary function from objects-of-$\mathscr{C}$ to objects-of-$\mathscr{D}$ isn't enough, because it throws away all the arrow structure that made $\mathscr{C}$ a category in the first place. You need something that carries objects to objects **and** arrows to arrows, in a way that respects domains, codomains, composition, and identities. That something is a functor.

Goldblatt's definition (p. 194): a functor $F$ from category $\mathscr{C}$ to category $\mathscr{D}$ is a function that assigns

- to each $\mathscr{C}$-object $a$, a $\mathscr{D}$-object $F(a)$;
- to each $\mathscr{C}$-arrow $f : a \to b$, a $\mathscr{D}$-arrow $F(f) : F(a) \to F(b)$;

such that

$$F(1_a) = 1_{F(a)} \quad \text{for all } \mathscr{C}\text{-objects } a,$$
$$F(g \circ f) = F(g) \circ F(f) \quad \text{whenever } g \circ f \text{ is defined.}$$

In words: $F$ preserves identities and preserves composition. This is the whole definition — no more, no less. Notice what it does *not* require: $F$ need not be injective or surjective on objects or arrows, and it can collapse a lot of structure (the "forgetful functor" below collapses almost everything).

**[[Logical-Geometry#Grounding|Grounding]] (Rust).** The closest everyday analogue a Rust programmer already has is a generic type constructor together with a `map`-like operation — precisely the shape of the `Functor` pattern (Rust doesn't have a `Functor` trait in std, but the pattern is everywhere: `Option<T>`, `Vec<T>`, `Result<T, E>`).

```rust
// F : Category(Rust-types-and-fns) -> Category(Rust-types-and-fns)
// Object part:  T |-> Option<T>
// Arrow part:   f: A -> B |-> Option::map(f): Option<A> -> Option<B>

fn map_option<A, B>(f: impl Fn(A) -> B, oa: Option<A>) -> Option<B> {
    oa.map(f)
}

// Functor law 1 (preserve identity):
//   map_option(|x| x, oa) == oa
// Functor law 2 (preserve composition):
//   map_option(g compose f, oa) == map_option(g, map_option(f, oa))
```

`Option<_>` is the object part ($F(a) = \texttt{Option<a>}$); `Option::map` is the arrow part ($F(f)$). The two functor laws are exactly the laws Rust programmers informally check when they write a `Functor`-shaped type — they're just not usually forced to *state* them, because Rust's type system doesn't check them for you the way, e.g., a Lean `Functor` instance with law-obligations would.

**Grounding (Lean).** Lean's `Functor` type class makes both the arrow-mapping operation *and* (optionally, via `LawfulFunctor`) the two laws explicit as proof obligations:

```lean
class Functor (f : Type u → Type v) where
  map : {α β : Type u} → (α → β) → f α → f β

class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const : ...
  id_map : ∀ {α} (x : f α), id <$> x = x            -- F(1_a) = 1_{F(a)}
  comp_map : ∀ {α β γ} (g : α → β) (h : β → γ) (x : f α),
      (h ∘ g) <$> x = h <$> (g <$> x)                 -- F(g∘f) = F(g)∘F(f)
```

This is Goldblatt's definition, verbatim, just typed. `LawfulFunctor` is not decoration — it is precisely what licenses the compiler (or you) to treat `map` as *structure-preserving* rather than as an arbitrary transformation that happens to have the right type signature.

**The book's example gallery, and what each one teaches.** Goldblatt runs through eleven examples (pp. 194–197); they're worth walking through because together they show the *range* of what "structure-preserving map" can mean:

1. **Identity functor** $1_{\mathscr{C}} : \mathscr{C} \to \mathscr{C}$. Trivial, but it's the identity arrow in the category of categories $\mathbf{Cat}$ — you need it before you can even say "$\mathbf{Cat}$ is a category."
2. **Forgetful functors** $U : \mathscr{C} \to \mathbf{Set}$, e.g. $\mathscr{C} = \mathbf{Top}$ (topological spaces): send a space to its underlying set, a continuous map to itself as a plain function. This is the paradigm case of a functor that *discards* structure while preserving the "shape" of arrows — exactly what `impl Deref for MyWrapper` or an "unwrap the newtype" function does in Rust.
3. **Powerset functor** $\mathscr{P} : \mathbf{Set} \to \mathbf{Set}$, $A \mapsto \mathscr{P}(A)$, $f \mapsto \mathscr{P}(f)$ where $\mathscr{P}(f)$ takes the direct image $f(X)$. This is covariant.
4. **Monotone maps between posets** are exactly functors between posets-as-categories (recall a poset is a category with at most one arrow $p \to q$, present iff $p \sqsubseteq q$). Functoriality collapses to: $p \sqsubseteq q \implies F(p) \sqsubseteq F(q)$.
5. **Monoid homomorphisms** are exactly functors between one-object categories. This is a genuinely illuminating collapse: "structure-preserving map of algebraic gadgets" and "functor" turn out to be the *same concept* once you see monoids as categories.
6. **The functor $- \times a : \mathscr{C} \to \mathscr{C}$** (when $\mathscr{C}$ has products): fixes one factor, lets the other vary. This will reappear as the key player in Example 3 of §9.2.
7. **Hom-functors** $\mathscr{C}(a, -) : \mathscr{C} \to \mathbf{Set}$: fix the source object $a$, send $b \mapsto \mathscr{C}(a,b)$ (the *set* of arrows $a \to b$ — Goldblatt flags explicitly that this requires hom-collections to be small sets, not proper classes, for the functor to even land in $\mathbf{Set}$). On arrows $f : b \to c$, post-compose: $\mathscr{C}(a,f)(g) = f \circ g$.

Examples 8–11 are the **contravariant** cousins (below), and Example 11, $\mathrm{Sub} : \mathscr{C} \to \mathbf{Set}$ sending $a$ to its subobjects and an arrow to *pullback along it*, is worth flagging now: it reappears verbatim as Exercise 2 of §9.2 as "a functorial statement of the $\Omega$-axiom" — i.e., the subobject classifier's defining property is literally a naturality statement about the functor $\mathrm{Sub}$.

**Contravariant functors.** A contravariant functor $F : \mathscr{C} \to \mathscr{D}$ reverses arrows: it assigns to $f : a \to b$ an arrow $F(f) : F(b) \to F(a)$ (note the swap), while still preserving identities, and now composition reverses too: $F(g \circ f) = F(f) \circ F(g)$. Goldblatt's convention — and one you should hold onto, because it recurs constantly in the type-theory literature — is that a contravariant functor $F : \mathscr{C} \to \mathscr{D}$ is *definitionally* the same thing as a covariant functor $F : \mathscr{C}^{\mathrm{op}} \to \mathscr{D}$ out of the **opposite category** $\mathscr{C}^{\mathrm{op}}$ (same objects, arrows reversed). This is not a mere notational trick — it's what lets you say "there is only one kind of functor" and push all the direction-bookkeeping into the choice of source category. The book will stop mentioning contravariant functors by name after this chapter and just write $F : \mathscr{C}^{\mathrm{op}} \to \mathscr{D}$ from Chapter 14 on.

Two contravariant examples worth remembering by name because they return in Chapter 10:

- **Example 9, contravariant powerset** $\mathscr{P} : \mathbf{Set} \to \mathbf{Set}$, sending $f : A \to B$ to *preimage* $f^{-1} : \mathscr{P}(B) \to \mathscr{P}(A)$.
- **Example 10, contravariant hom-functor** $\mathscr{C}(-, a) : \mathscr{C}^{\mathrm{op}} \to \mathbf{Set}$: fix the *target*, vary the source, and arrows act by pre-composition. This is the functor that gets exponentiated into a presheaf category at the very end of the chapter (§9.3, [[Adjointness-and-Quantifiers#Exponentiation|exponentiation]] in $\mathbf{Set}^{\mathscr{C}}$), and it is *the* motivating example for the Yoneda embedding that Goldblatt develops in Chapter 14.

**$\mathbf{Cat}$.** Because functors compose associatively ($H \circ (G \circ F) = (H \circ G) \circ F$) and the identity functor is a unit for composition, you get a category $\mathbf{Cat}$ whose objects are categories and whose arrows are functors. Goldblatt flags the size problem immediately: $\mathbf{Set}$ can't be an object of $\mathbf{Cat}$-as-usually-conceived without running into Russell's-paradox-adjacent trouble, so $\mathbf{Cat}$ is by convention the category of *small* categories (those whose arrow-collection is a genuine set). This is the same size discipline that will matter later when you ask whether a category of types-and-terms is itself "small enough" to sit inside a semantic universe — a live issue for any elaborator that reasons about universes of types.

## 9.2 Natural transformations

**What breaks without it.** Once functors are "arrows between categories," the next question is unavoidable: what's an arrow between two functors $F, G : \mathscr{C} \to \mathscr{D}$? You might reach for "any family of $\mathscr{D}$-arrows $\eta_a : F(a) \to G(a)$, one per $\mathscr{C}$-object $a$." But that's too weak — it says nothing about how the family interacts with $\mathscr{C}$'s arrows, so it can't be called "structure-preserving" in any meaningful sense; it would just be an unrelated bag of arrows indexed by objects. Goldblatt's motivating image (p. 198) is worth keeping verbatim: think of $F$ and $G$ as two different "pictures" of $\mathscr{C}$ sitting inside $\mathscr{D}$, and a natural transformation as the operation of *sliding* the $F$-picture onto the $G$-picture, using $\mathscr{D}$'s own structure to do the translating.

The requirement that makes this "structure-preserving" is: for every $\mathscr{C}$-arrow $f : a \to b$, the square

$$
\begin{array}{ccc}
F(a) & \xrightarrow{\ \eta_a\ } & G(a) \\
{\scriptstyle F(f)}\big\downarrow & & \big\downarrow{\scriptstyle G(f)} \\
F(b) & \xrightarrow{\ \eta_b\ } & G(b)
\end{array}
$$

commutes, i.e. $\eta_b \circ F(f) = G(f) \circ \eta_a$. This is **the naturality square** — arguably the single most important commuting diagram in category theory, because it is the formal expression of "this family of arrows doesn't care how you got from $a$ to $b$; both routes around the square agree."

A natural transformation $\eta : F \Rightarrow G$ (Goldblatt writes $\tau : F \dot\to G$) is exactly: a family $(\eta_a)_{a \in \mathscr{C}}$ of $\mathscr{D}$-arrows $\eta_a : F(a) \to G(a)$, one per object, such that every such square commutes. The $\eta_a$ are its **components**. If every component is an iso, $\eta$ is a **natural isomorphism**, written $F \cong G$; the inverses $\eta_a^{-1}$ then assemble into a natural isomorphism $\eta^{-1} : G \cong F$.

**Answering the book's own Key Question 1** ("why must the square commute, and what does this buy over an arbitrary family?"): an arbitrary family gives you *no* guarantee of compatibility with $\mathscr{C}$'s morphisms — you could have $\eta_a$ and $\eta_b$ be completely unrelated arrows that happen to have the right types. Naturality is what upgrades "a bunch of arrows indexed by objects" into "a genuinely uniform, parametrically-defined translation from the $F$-picture to the $G$-picture" — one formula that works the same way at every object, provably, not just coincidentally.

**Grounding (Rust/Lean) — this is where the payoff for your project is largest.** A natural transformation between two functors $F, G : \mathbf{Type} \to \mathbf{Type}$ (thinking of the category of types-and-functions) is *exactly* a **polymorphic function generic in the type parameter**, subject to the naturality square. Take $F = \mathrm{Option}$, $G = \mathrm{Vec}$ (or `List`), and

```rust
fn opt_to_vec<T>(o: Option<T>) -> Vec<T> {
    match o { Some(x) => vec![x], None => vec![] }
}
```

Naturality here says: for any $f : A \to B$, mapping-then-converting equals converting-then-mapping —
`opt_to_vec(o.map(f)) == opt_to_vec(o).into_iter().map(f).collect()`.
This is *not* a theorem you have to separately prove about `opt_to_vec` by induction on its cases — it is a **free theorem** (Wadler), guaranteed by parametricity purely because `opt_to_vec`'s type is `∀T. Option<T> -> Vec<T>` and it can't inspect `T`. This is the precise sense in which "naturality" and "parametricity" are the same phenomenon viewed from two fields: category theory calls the commuting-square property naturality; programming-language theory calls the same fact (derived from a term's polymorphic type alone) a free theorem. Lean's own reasoning about generic functions over `Type u` rests on the identical fact, and it is exactly what licenses treating `id <$> x = x`-style laws as *provable from typing alone* in a parametric setting rather than needing to be checked case by case.

**The book's worked examples**, briefly, because each demonstrates a different flavor of naturality:

- **Example 1**: the identity natural transformation $1_F : F \Rightarrow F$, components $1_{F(a)}$ — trivially natural, and it's the identity arrow of the functor category (see §9.3).
- **Example 2**: in $\mathbf{Set}$, $A \cong A \times 1$ for every set $A$, and this isomorphism is *natural* in $A$ — i.e., it assembles into a natural isomorphism $1_{\mathbf{Set}} \cong (- \times 1)$ between the identity functor and the "$- \times 1$" functor from Example 6 of §9.1. This is the prototypical case of "the same construction works uniformly at every object, and the naturality square is what certifies 'uniformly.'"
- **Example 3**: the twist map $\mathrm{tw}_B : A \times B \to B \times A$ is natural in $B$, giving a natural isomorphism between the functors $A \times -$ and $- \times A$.
- **Equivalence of categories**: two categories can fail to be *isomorphic* (no functor $F$ with a strict two-sided inverse) while still being "the same up to isomorphism" — this is captured by asking for functors $F : \mathscr{C} \to \mathscr{D}$, $G : \mathscr{D} \to \mathscr{C}$ with $G \circ F \cong 1_{\mathscr{C}}$ and $F \circ G \cong 1_{\mathscr{D}}$ via *natural* isomorphisms (not mere equalities). The worked example, $\mathbf{Finord} \simeq \mathbf{Finset}$ (finite ordinals vs. all finite sets), shows why this weaker notion is the right one: $\mathbf{Finord}$'s objects form a genuine set, while $\mathbf{Finset}$'s form a proper class, so they can't possibly be isomorphic as categories, yet every finite set is naturally in bijection with *some* ordinal, which is exactly what equivalence captures. This "isomorphic up to coherent natural isomorphism, not on the nose" pattern is precisely the discipline you'll need when reasoning about whether two presentations of a type-theoretic model (e.g. two different context-representations in an elaborator) are "the same" without demanding literal syntactic equality — the categorical analogue of definitional vs. propositional equality.

## 9.3 Functor categories

**What breaks without it.** Having a notion of arrow between two functors invites the obvious next move (§9.3 opens by naming this explicitly, p. 202): treat *functors themselves* as objects, and natural transformations as the arrows between them, forming a new category $\mathscr{D}^{\mathscr{C}}$ (or $\mathrm{Funct}(\mathscr{C}, \mathscr{D})$). This requires a composition operation for natural transformations — and it must itself be shown to produce a natural transformation, not just an arbitrary family.

Given $\tau : F \Rightarrow G$ and $\sigma : G \Rightarrow H$, define the (vertical) composite $(\sigma \circ \tau)_a := \sigma_a \circ \tau_a$ at each object $a$. Because both the $\tau$-square and the $\sigma$-square commute individually, the outer rectangle they stack into commutes too — so $\sigma \circ \tau : F \Rightarrow H$ is natural. The identity arrow on object $F$ of $\mathscr{D}^{\mathscr{C}}$ is $1_F$ from Example 1 above. This is enough to make $\mathscr{D}^{\mathscr{C}}$ a bona fide category (Goldblatt leaves associativity and the identity laws as immediate from the pointwise definition).

**Four instructive special cases** (p. 203, examples A–D), each identifying a familiar category as a functor category:

| Source category $\mathscr{C}$ | $\mathbf{Set}^{\mathscr{C}}$ turns out to be |
|---|---|
| $\mathbf{2} = \{0,1\}$ discrete | $\mathbf{Set}^2$, pairs of sets and pairs of functions |
| $\mathbf{2} = \{0 \to 1\}$ (arrow category) | $\mathbf{Set}^{\to}$, the category of *functions* $f : F_0 \to F_1$ as objects, commuting squares as arrows |
| $M$, a monoid as one-object category | $M\text{-}\mathbf{Set}$, sets with an $M$-action, arrows = equivariant maps |
| $I$, a discrete category (index set) | $\mathbf{Bn}(I)$, bundles (indexed families of sets) over $I$ |

The pattern across all four: **a functor out of $\mathscr{C}$ into $\mathbf{Set}$ is exactly "a $\mathscr{C}$-shaped diagram of sets,"** and what counts as "$\mathscr{C}$-shaped" is entirely dictated by $\mathscr{C}$'s own arrow structure — a discrete category gives you unrelated sets, the walking-arrow category gives you a single function, a monoid gives you an action, an arbitrary small category gives you the fully general notion, which is precisely a **presheaf** when $\mathscr{C}$ is replaced by $\mathscr{C}^{\mathrm{op}}$.

**The chapter's punchline**, stated as its own displayed claim (p. 203):

> for any "small" category $\mathscr{C}$, the functor category $\mathbf{Set}^{\mathscr{C}}$ is a **topos**.

Goldblatt spends the rest of the chapter proving this by constructing each piece of topos structure *componentwise* — i.e., pointwise at each object of $\mathscr{C}$, then checking the resulting assignment is itself functorial:

- **Terminal object**: the constant functor $1 : \mathscr{C} \to \mathbf{Set}$ sending everything to a fixed singleton $\{0\}$.
- **Pullback**: built object-by-object as an ordinary $\mathbf{Set}$-pullback $K(a)$, with the arrow-action $K(f)$ forced by the universal property applied to the resulting "cube" diagram.
- **Subobject classifier $\Omega$**: this is the genuinely new machinery, and it's where **sieves** are introduced (p. 205) — for an object $a$, the collection $S_a$ of all arrows with domain $a$, and an *$a$-sieve* is a subset $S \subseteq S_a$ closed under left-composition (post-composing anything in $S$ with a further arrow keeps you in $S$). Then $\Omega(a) := \{S : S \text{ is an } a\text{-sieve}\}$, with $\Omega(f)$ defined by "pulling a sieve back along $f$." The classifying arrow $\mathrm{true} : 1 \Rightarrow \Omega$ picks out, at each $a$, the *largest* sieve $S_a$ itself (the sieve containing every arrow out of $a$ — the categorical analogue of "true everywhere downstream"). A monic $\tau : F \Rightarrowtail G$ is classified by sending $x \in G(a)$ to the sieve of arrows $f : a \to b$ along which $x$'s $G$-image eventually lands back in $F$'s image — concretely, $\{f : a \to b \mid G(f)(x) \in F(b)\}$ when $\tau$ is an inclusion. This is a genuinely new idea, not a routine componentwise construction, and Goldblatt flags it will be *the* structure explained in depth in Chapter 10 (upward-closed sets / sieves as "stage-relative truth values").
- **Exponentiation**: for $F, G : \mathscr{C} \to \mathbf{Set}$, define an auxiliary "restriction" functor $F_a : (a {\downarrow} \mathscr{C}) \to \mathbf{Set}$ on the slice/comma category of objects-under-$a$, then set $G^F(a) := \mathrm{Nat}[F_a, G_a]$ — the *set of natural transformations* between the restricted functors. This is dense (Goldblatt himself calls it "this very complex construction," p. 209), and its payoff is concrete: worked out for $\mathscr{C} = \mathbf{2}$, it correctly reproduces $D^B$ (ordinary function-space) as the exponential in $\mathbf{Set}^{\mathbf{2}}$.

**Answering the book's Key Question 2** ("how does $\mathbf{Set}^P$ as a functor category prepare for treating presheaves as topoi?"): this chapter proves the *general* theorem — any small $\mathscr{C}$ gives a topos $\mathbf{Set}^{\mathscr{C}}$ — as pure category theory, with no reference to logic yet. Chapter 10 specializes $\mathscr{C}$ to (the opposite of) a poset $P$ and reads off what the abstract pieces built here — $\Omega$ as sieves, "true" as the top sieve — *mean* logically: sieves over a poset become upward-closed sets of later "stages," and the classifier's stage-relative truth values become exactly Kripke's forcing relation. Nothing in Chapter 10 is new construction; it's this chapter's machinery, instantiated and reinterpreted.

## Structural summary

<svg viewBox="0 0 760 300" xmlns="http://www.w3.org/2000/svg" font-family="sans-serif" font-size="13">
  <rect x="0" y="0" width="760" height="300" fill="none"/>
  <!-- Category level -->
  <rect x="20" y="20" width="200" height="60" rx="6" fill="none" stroke="#888" stroke-width="1.5"/>
  <text x="120" y="45" text-anchor="middle" fill="#666">Objects &amp; arrows</text>
  <text x="120" y="65" text-anchor="middle" font-weight="bold">a category $\mathscr{C}$</text>

  <rect x="290" y="20" width="200" height="60" rx="6" fill="none" stroke="#888" stroke-width="1.5"/>
  <text x="390" y="45" text-anchor="middle" fill="#666">preserves dom/cod, ∘, id</text>
  <text x="390" y="65" text-anchor="middle" font-weight="bold">a functor $F:\mathscr{C}\to\mathscr{D}$</text>

  <rect x="560" y="20" width="180" height="60" rx="6" fill="none" stroke="#888" stroke-width="1.5"/>
  <text x="650" y="45" text-anchor="middle" fill="#666">objects = categories</text>
  <text x="650" y="65" text-anchor="middle" font-weight="bold">$\mathbf{Cat}$</text>

  <line x1="220" y1="50" x2="285" y2="50" stroke="#888" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="490" y1="50" x2="555" y2="50" stroke="#888" stroke-width="1.5" marker-end="url(#arrow)"/>

  <!-- step up -->
  <rect x="20" y="120" width="200" height="60" rx="6" fill="none" stroke="#888" stroke-width="1.5"/>
  <text x="120" y="145" text-anchor="middle" fill="#666">objects = functors $F,G$</text>
  <text x="120" y="165" text-anchor="middle" font-weight="bold">arrow = natural $\eta:F\Rightarrow G$</text>

  <rect x="290" y="120" width="200" height="60" rx="6" fill="none" stroke="#888" stroke-width="1.5"/>
  <text x="390" y="145" text-anchor="middle" fill="#666">naturality square commutes</text>
  <text x="390" y="165" text-anchor="middle" font-weight="bold">$\eta_a$ per object, coherent</text>

  <rect x="560" y="120" width="180" height="60" rx="6" fill="none" stroke="#888" stroke-width="1.5"/>
  <text x="650" y="145" text-anchor="middle" fill="#666">§9.3</text>
  <text x="650" y="165" text-anchor="middle" font-weight="bold">functor category $\mathscr{D}^{\mathscr{C}}$</text>

  <line x1="220" y1="150" x2="285" y2="150" stroke="#888" stroke-width="1.5" marker-end="url(#arrow)"/>
  <line x1="490" y1="150" x2="555" y2="150" stroke="#888" stroke-width="1.5" marker-end="url(#arrow)"/>

  <!-- payoff -->
  <rect x="150" y="220" width="460" height="60" rx="6" fill="none" stroke="#4a7" stroke-width="2"/>
  <text x="380" y="245" text-anchor="middle" fill="#2a6">Chapter 9's theorem</text>
  <text x="380" y="265" text-anchor="middle" font-weight="bold">$\mathbf{Set}^{\mathscr{C}}$ is a topos, for any small $\mathscr{C}$</text>

  <line x1="650" y1="180" x2="480" y2="220" stroke="#4a7" stroke-width="1.5" marker-end="url(#arrow2)"/>

  <defs>
    <marker id="arrow" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#888"/>
    </marker>
    <marker id="arrow2" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#4a7"/>
    </marker>
  </defs>
</svg>

## Where this leads

$\mathbf{Set}^{\mathscr{C}}$-as-topos is the direct setup for **Chapter 10**, which specializes $\mathscr{C}$ to a poset $P$ (so $\mathbf{Set}^{P^{\mathrm{op}}}$, or Goldblatt's $\mathbf{Set}^P$), reads its sieve-based $\Omega$ as "stage-relative truth values," and shows that internal validity in this topos *is* Kripke forcing. It also quietly sets up **Chapter 14**, where the contravariant/opposite-category convention from §9.1 and the hom-functor examples get reused for the Yoneda embedding, and where "cribles" (the dual of sieves, deferred here on p. 208) finally get their turn.

For your project specifically: functor categories are the categorical semantics of **presheaf models of type theory** — a context category $\mathscr{C}$ with contexts as objects and substitutions as arrows, and a type/term presheaf over it. The naturality square you now recognize on sight is exactly the "substitution stability" law that a well-behaved type-theoretic model must satisfy: applying a substitution and then reading off a type must agree with reading off the type and then substituting. Any time you formalize what it means for your elaborator's typing judgments to be *stable under weakening and substitution*, you are asking for a diagram to commute in a functor category, whether or not you spell it out categorically. And the free-theorem/parametricity connection above is not a decoration: it is the same fact your unifier will lean on whenever it treats a polymorphic function as opaque in its type parameter rather than pattern-matching on it.
