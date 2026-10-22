---
title: Category Theory in Univalent Foundations
book: Homotopy Type Theory — Univalent Foundations of Mathematics
chapters: "Chapter 9 (printed pp. 307–340)"
tags: [homotopy-type-theory, category-theory, univalence, precategory, yoneda, rezk-completion, type-theory]
---

[[book-guidelines|↩ Back to guidelines]]

# Category Theory in Univalent Foundations

## 1. Why a "category" needs redefining

Ordinary category theory has a built-in tension. Almost every statement a category theorist cares about is invariant under *isomorphism* of objects and *equivalence* of categories. Yet set-based foundations only offer *equality* of objects, which is a much finer relation. The usual workarounds are to say "up to isomorphism" informally, or to invoke the axiom of choice. The classic case is "every fully faithful, essentially surjective functor is an equivalence", which in set-based mathematics is equivalent to the axiom of choice.

The univalence axiom solved the same mismatch for types: it identifies equality with equivalence. Chapter 9 asks for the same move for categories: define a "category" so that equality of objects *is* isomorphism of objects.

Since the type-theoretic version distinguishes three notions, the chapter opens by comparing them on that one statement:

| Notion | Objects | "Fully faithful + essentially surjective ⇒ equivalence" |
|---|---|---|
| strict category | a set | still equivalent to the axiom of choice |
| precategory | a type | no consistent choice axiom can make it true |
| **category** | a type, with $\mathsf{idtoiso}$ an equivalence | provable with no choice |

## 2. Precategories, isomorphisms, and the univalence condition (§9.1)

Because we have dependent types, the arrows are a type *family* indexed by the objects. This matches how hom-types are used: arrows are only compared once their domains and codomains agree. Since the chapter develops 1-categories only, every hom-type is required to be a *set*.

**Definition 9.1.1 (precategory).** A precategory $A$ has:
- a type $A_0$ of objects,
- for $a, b : A$, a set $\hom_A(a,b)$,
- identities $1_a : \hom_A(a,a)$,
- composition $\hom_A(b,c) \to \hom_A(a,b) \to \hom_A(a,c)$,
- unit laws $f = 1_b \circ f$ and $f = f \circ 1_a$,
- associativity $h \circ (g \circ f) = (h \circ g) \circ f$.

Two notions of "sameness" now exist for $a, b : A$: the identity type $(a =_{A_0} b)$ and the type of isomorphisms $a \cong b$.

**Lemma 9.1.3.** "$f$ is an isomorphism" is a mere proposition, so $a \cong b$ is a set. The proof shows that the inverse is unique: $g' = 1_a \circ g' = (g\circ f)\circ g' = g \circ (f \circ g') = g \circ 1_b = g$.

**Lemma 9.1.4 ($\mathsf{idtoiso}$).** There is a canonical map $(a = b) \to (a \cong b)$, defined by path induction (the case $\mathsf{refl}_a$ goes to $1_a$). It is the only link between the two notions in a precategory.

**Definition 9.1.6 (category).** A precategory is a *category* when $\mathsf{idtoiso}_{a,b}$ is an equivalence for all $a, b$. Its inverse is written $\mathsf{isotoid}$.

Consequences and examples from the text:
- In the precategory $\mathcal{S}et$ (objects: sets; morphisms: functions), $\mathsf{idtoiso}$ is exactly $\mathsf{idtoeqv}$ restricted to sets (Example 9.1.5). So univalence makes $\mathcal{S}et$ a category (Example 9.1.7).
- In a category, the type of objects is a **1-type**. The reason is that $a = b \simeq a \cong b$, and the latter is a set (Lemma 9.1.8).
- Lemma 9.1.9 says that transport along $(p,q)$ acts on a morphism $f$ as $\mathsf{idtoiso}(q) \circ f \circ \mathsf{idtoiso}(p)^{-1}$. This is the workhorse lemma, used repeatedly below.
- A preorder (a precategory with propositional homs) is a category exactly when it is a **poset**. That means $A_0$ is a set and $\le$ is antisymmetric (Example 9.1.14).
- A category has a set of objects exactly when it is *gaunt* (Example 9.1.15). This means every automorphism is an identity.
- Further examples are Rel (Example 9.1.19, shown to be a category), the discrete category and groupoids on a 1-type, the fundamental pregroupoid with $\hom(x,y) :\equiv \|x = y\|_0$, and the homotopy precategory of types.

## 3. Functors, transformations, and the functor category (§9.2)

Functors and natural transformations need no modification. The one new point is that, since hom-types are sets, **the axioms are mere propositions**. So equality of natural transformations is componentwise, and the type of natural transformations is a set.

**Theorem 9.2.5.** If $A$ is a precategory and $B$ is a **category**, then $B^A$ is a category. The proof builds $\mathsf{isotoid}$ for natural isomorphisms. It takes a natural isomorphism $\gamma$, forms $\mathsf{isotoid}(\gamma_a) : Fa = Ga$ at each component, and combines these with function extensionality. It then checks that transport (via Lemma 9.1.9) lands on $Gf$ by naturality. Corollary: naturally isomorphic functors into a category are equal.

The chapter also notes that associativity of functor composition holds only as a propositional equality, not a definitional one. It therefore proves coherence lemmas (pentagon and triangle). It also declines to define a separate "horizontal composite" and uses a single $\circ$ for all compositions.

## 4. Adjunctions and equivalences (§§9.3–9.4)

**Adjunction (Def. 9.3.1).** $F$ is a left adjoint when there are $G$, a unit $\eta : 1_A \to GF$, a counit $\epsilon : FG \to 1_B$, and the two triangle identities $(\epsilon F)(F\eta) = 1_F$ and $(G\epsilon)(\eta G) = 1_G$.

**Lemma 9.3.2.** If $A$ is a category, "$F$ is a left adjoint" is a mere proposition. The proof builds a natural isomorphism $G \cong G'$ from the units and counits, turns it into an equality by Theorem 9.2.5, and checks that $\eta, \epsilon$ transport correctly.

**Equivalence of (pre)categories (Def. 9.4.1).** This is a left adjoint whose unit and counit are isomorphisms. The authors choose the adjoint-equivalence form for the same reason as in §4.2. The naive "inverse functor plus natural isomorphisms" would not be a mere proposition.

Key results (Lemmas 9.4.5–9.4.16):
- $F$ is an equivalence of precategories $\simeq$ $F$ is fully faithful and **split** essentially surjective. "Split" means a chosen $a$ with $Fa \cong b$ for each $b$.
- A **weak equivalence** is fully faithful and essentially surjective. Here "essentially surjective" uses a *mere* existence, which is the truncated version.
- **Lemma 9.4.7.** If $F$ is fully faithful and the domain is a category, then $\sum_{a:A} (Fa \cong b)$ is a mere proposition. Hence for categories, equivalence $\Leftrightarrow$ weak equivalence, which is the choice-free version of the classical statement. The authors describe it as a category-theoretic version of unique choice.
- For a precategory, an *isomorphism of precategories* is fully faithful with $F_0$ an equivalence of types. Isomorphism implies equivalence. The converse can fail, for example the indiscrete precategory $X_{ch} \to 1$ (Example 9.4.13). For categories, the two notions coincide (Lemma 9.4.14).
- For precategories $A, B$, the canonical map $(A = B) \to (A \cong B)$ is an equivalence (Lemma 9.4.15). By Lemma 9.4.14, for categories $(A = B) \simeq (A \simeq B)$ (Theorem 9.4.16). So **equivalent categories are equal**, and the type of categories is a 2-type.

## 5. The Yoneda lemma (§9.5)

The chapter defines the opposite category $A^{op}$, the product $A \times B$, and the currying equivalence between functors $A \times B \to C$ and functors $A \to C^B$ (Lemma 9.5.3). The hom-functor $\hom_A : A^{op} \times A \to \mathcal{S}et$ then induces the Yoneda embedding $y : A \to \mathcal{S}et^{A^{op}}$.

**Theorem 9.5.4 (Yoneda).** For $a : A$ and a functor $F : \mathcal{S}et^{A^{op}}$,
$$\hom_{\mathcal{S}et^{A^{op}}}(ya, F) \cong Fa,$$
natural in $a$ and $F$. The forward map sends $\alpha$ to $\alpha_a(1_a)$. The inverse sends $x : Fa$ to $\alpha_{a'}(f) :\equiv F_{a,a'}(f)(x)$.

Consequences:
- The Yoneda embedding is **fully faithful** (Corollary 9.5.6).
- If $A$ is a category, $y_0$ is an **embedding** of types (Corollary 9.5.7). So "$F$ is representable" is a mere proposition (Theorem 9.5.9).
- This gives a second proof that left adjointness is a mere proposition. By Lemma 9.5.10, $F$ is a left adjoint iff each $b \mapsto \hom_B(F-, b)$ is representable, which is a mere proposition when $A$ is a category (Corollary 9.5.11).

## 6. Strict categories and $\dagger$-categories (§§9.6–9.7)

These sections explain that precategories other than categories are still useful. They are the raw material from which several categorical structures are built.

- **Strict category (Def. 9.6.1):** a precategory whose type of objects is a *set*. A category is strict exactly when it is gaunt. Strict categories matter when isomorphism is the wrong notion of sameness. Example 9.6.3 is the Galois correspondence, where the book argues a strict category fits better.
- **$\dagger$-category (Defs. 9.7.1–9.7.4):** a precategory with a contravariant, involutive, identity-on-objects operation $f \mapsto f^\dagger$. A morphism is *unitary* when $f^\dagger \circ f = 1$ and $f \circ f^\dagger = 1$. $\mathsf{idtoiso}$ always lands in unitary isomorphisms. A $\dagger$-category is one where the resulting map $(x = y) \to (x \cong_\dagger y)$ is an equivalence. Examples include Rel and finite-dimensional Hilbert spaces (Hilb), where unitary isomorphism is the right "sameness".

## 7. The structure identity principle (§9.8)

The structure identity principle informally says that isomorphic structures have the same properties. Univalence gives it for plain types, and this section extends it to structured sets.

A **notion of structure** $(P,H)$ over a category $X$ consists of:
- a set-valued family $P : X_0 \to \mathcal{S}et$,
- for $x,y : X$, $\alpha : Px$, $\beta : Py$ and $f : x \cong y$, a mere proposition $H_{\alpha\beta}(f)$ ("$f$ is a homomorphism"),
- the evident identity, composition and inverse conditions,
- the condition that $f$ is a homomorphism both ways forces $\alpha = \beta$ when $f = 1_x$ (this makes it *standard*).

**Theorem 9.8.2.** If $X$ is a category and $(P,H)$ a standard notion of structure, then $(x,\alpha) = (y,\beta)$ iff there is an isomorphism $f : x \cong y$ that is a homomorphism from $\alpha$ to $\beta$. Hence the resulting precategory of structured objects is itself a category.

Instances: functor categories (Example 9.8.3) and the category of $\Omega$-structures over $\mathcal{S}et$ (Def. 9.8.4), which covers groups, rings and similar algebraic structures.

## 8. The Rezk completion (§9.9)

The goal is a universal way to replace a precategory by a category.

**Theorem 9.9.4.** If $C$ is a category and $H : A \to B$ a weak equivalence of precategories, then precomposition $(- \circ H) : C^B \to C^A$ is an *isomorphism of categories*. The proof goes through fullness and faithfulness lemmas (9.9.1–9.9.2) for essentially surjective functors. It shows the relevant fibers are contractible, using the unique-choice-style argument available because isomorphism is equality in $C$.

**Theorem 9.9.5.** Every precategory $A$ has a category $\hat A$ and a weak equivalence $A \to \hat A$.
- *First proof:* take the full subcategory of $\mathcal{S}et^{A^{op}}$ on functors that are *merely* representable. The Yoneda embedding corestricts to it. It is fully faithful and essentially surjective, and $\hat{A}$ is a category because $\mathcal{S}et^{A^{op}}$ is.
- *Second proof:* a higher inductive type construction of $\hat A$, which avoids the universe jump in the first.

Examples: the Rezk completion of the fundamental pregroupoid of $X$ gives the fundamental groupoid (Example 9.9.6), and that of the homotopy precategory of types gives the homotopy category (Example 9.9.7).

**Theorem 9.9.8 (characterization).** A precategory $C$ is a category iff for every weak equivalence $H : A \to B$, $(- \circ H) : C^B \to C^A$ is an isomorphism of precategories. So the notion of "category" is already implicit in the notion of "weak equivalence".

## 9. Grounding in code

The mechanism worth carrying away is the *shape of the data*: the hom-sets are a family indexed by objects, the laws are propositions (hence invisible to equality), and the univalence condition is an extra proof about $\mathsf{idtoiso}$.

**Lean.** Mathlib's `CategoryTheory.Category` has `Hom : C → C → Type` plus `id`, `comp` and the laws, matching Definition 9.1.1 (hom-sets are sets, because `Eq` is proof-irrelevant in Lean). It does *not* require the univalence condition: `Iso a b` and `a = b` are unrelated in general, so Mathlib categories are precategories in the book's sense. Mathlib's `Functor.IsEquivalence` is built from fully faithful and essentially surjective using `Classical.choice`, which is exactly the choice-dependence the chapter eliminates. This is an observation from my own knowledge of Mathlib, not from the book.

```lean
-- Precategory data in Lean 4 (sketch; Mathlib's real class is richer)
structure PreCat where
  Obj  : Type
  Hom  : Obj → Obj → Type
  id   : (a : Obj) → Hom a a
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c
  idl  : ∀ {a b} (f : Hom a b), comp (id b) f = f
  idr  : ∀ {a b} (f : Hom a b), comp f (id a) = f
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
          comp h (comp g f) = comp (comp h g) f
```

**Rust.** The same data as a trait. The univalence condition is not expressible in Rust's type system; it would be a proof obligation, so in a checker it becomes a runtime or meta-level property.

```rust
trait PreCategory {
    type Obj;
    type Hom<A, B>; // hom-set family indexed by objects (not literal Rust; GAT sketch)
    fn id<A>() -> Self::Hom<A, A>;
    fn comp<A, B, C>(g: Self::Hom<B, C>, f: Self::Hom<A, B>) -> Self::Hom<A, C>;
}
```

**Python.** In a dynamically typed setting the nearest analogue of $\mathsf{idtoiso}$ is a canonicalization pass. For example, hash-consing isomorphic structures to a normal form makes "isomorphic implies identical" true by construction, which resembles the effect of the Rezk completion, but nothing checks it.

(I wrote these snippets as illustrations and did not compile or run them.)

## 10. Synthesis: where this sits in the book

```
Ch. 2: univalence, funext, transport
Ch. 3: mere propositions, truncation, unique choice
Ch. 4: half adjoint equivalences
   │
   ▼
Ch. 9: precategory ──(idtoiso an equivalence)──► category
          │                                         │
          ├─ functor category B^A is a category     ├─ equivalence = weak equivalence (no AC)
          ├─ Yoneda, representability is a prop     ├─ A = B  ≃  A ≃ B
          └─ Rezk completion A → Â  ◄───────────────┘
Ch. 10: category of sets;  Ch. 11: uses Set-level structure
```

- **What it depends on:** univalence and function extensionality (Chapter 2), mere propositions and truncation (Chapter 3), the half-adjoint technique of Chapter 4, and, for the second Rezk construction, [[Higher-Inductive-Types|higher inductive types]] (Chapter 6).
- **What depends on it:** the category of sets in Chapter 10 reuses these notions.

**Relevance to the stated project (`type-theory` tag; no other Focus Area).** This chapter is mathematical application rather than mechanism, so it does not feed the elaborator or kernel directly. Two threads are worth noting without forcing them:
- The *data-versus-property* discipline is the same as the refinement-type split between computational content and proof-irrelevant predicates. The laws are mere propositions that never need to be compared.
- The $\mathsf{idtoiso}$ condition is a concrete example of a *quotient by definitional-style sameness* made explicit in the types. That is one answer to the question of which equalities a kernel's $\mathsf{isDefEq}$ should and should not identify.

Note that the book does not describe any algorithms in this chapter; the connection to the compiler goals is conceptual only.

## Notes on source fidelity

- This article was written from the chapter text (printed pp. 307–340). I read §§9.1–9.5 in full, and for §§9.5 (end) through 9.9 I read the statements of definitions, lemmas and theorems but not every proof. Those later proof outlines are summarized from the statements and visible proof openings.
- One correction to `book-guidelines.md`: it describes §9.6 as "categories whose objects form a set". The source defines a *strict category* as a **precategory** whose type of objects is a set (Definition 9.6.1). A category that is strict is a *gaunt* one.
