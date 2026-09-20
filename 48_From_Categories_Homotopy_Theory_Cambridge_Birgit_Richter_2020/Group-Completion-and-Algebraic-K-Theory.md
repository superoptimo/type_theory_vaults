---
title: Group Completion and Algebraic K-Theory
source: "From Categories to Homotopy Theory (Birgit Richter, 2020)"
chapter: "Chapter 13: Classifying Spaces of Symmetric Monoidal Categories (pp. 304–315)"
tags: [category-theory, homotopy-theory, symmetric-monoidal-categories, group-completion, algebraic-k-theory, classifying-spaces, type-theory]
---

[[book-guidelines|↩ Back to guidelines]]

# Group Completion and Algebraic K-Theory

## The problem: you have a monoid, but you want a group

Take the natural numbers under addition, $(\mathbb{N}_0, +, 0)$. There's no subtraction — $3 - 5$ isn't a natural number. But you can *formally invent* subtraction by working with pairs $(m, n)$, meaning "think of this as $m - n$," and quotienting by the relation that makes $(m,n) \sim (m', n')$ exactly when $m + n' = m' + n$. Do this to $\mathbb{N}_0$ and you get $\mathbb{Z}$. This trick — freely adjoining inverses to an abelian monoid to produce the smallest abelian group that contains it — is the **Grothendieck group construction**, and it is the algebraic seed of an entire subject: algebraic K-theory.

**What breaks without it.** Plenty of the monoids that show up in nature — isomorphism classes of vector bundles under direct sum, isomorphism classes of finitely generated projective modules under $\oplus$, path components of a symmetric monoidal category under $\otimes$ — are not groups, and the interesting invariants of a space or a ring (topological K-theory, algebraic K-theory) are literally *defined* as the group completions of these monoids. If you only ever work with the monoid, you can't say "the inverse of this vector bundle," which is exactly the kind of statement K-theory needs to make (e.g., to define the index of a Fredholm operator, or the Euler characteristic of a projective module, as an actual *element* of a group rather than an equivalence class you can't subtract from).

Chapter 13 does this construction three times, at three levels of sophistication, each one categorifying the previous:

1. **Discrete monoids → groups.** The classical Grothendieck group $G(M)$.
2. **Symmetric [[Monoidal-Categories|monoidal categories]] → symmetric monoidal categories with invertible objects (up to $\pi_0$).** The **Grayson–Quillen construction** $C^{-1}C$, whose classifying space is literally $K$-theory.
3. **H-spaces → H-spaces.** A homotopical group completion, general enough to say "the classifying space of the Grayson–Quillen construction really *is* the correct group completion of $BC$," and to unify the group-theoretic and homotopical stories.

If you've built a compiler pass that computes "the net effect of a sequence of operations" and had to invent a signed delta to represent operations that partially cancel, you've already felt the shape of a Grothendieck group without naming it — this chapter makes that construction functorial and universal.

## 13.1 — Classifying spaces of symmetric monoidal categories are H-spaces

Before completing anything, Richter first has to show there's something worth completing: that $BC$, the classifying space of a symmetric monoidal category, carries multiplicative structure at all.

**Definition 13.1.1 (H-space).** An **H-space** is a topological space $X$ with a basepoint $x_0$ and a continuous multiplication $\mu: X \times X \to X$ such that $\mu(x_0, -)$ and $\mu(-, x_0)$ are each homotopic to the identity (an up-to-homotopy unit). It's **associative**/**commutative** if $\mu$ is associative/commutative up to homotopy, and **group-like** if there's a map $\chi: X \to X$ (an up-to-homotopy inverse) with $\mu \circ (1_X \times \chi) \circ \Delta \simeq \mathrm{id}$.

This is exactly a monoid object, but weakened: instead of demanding the monoid axioms as literal equations, you only demand them up to a witnessing homotopy. (A based loop space $\Omega Y$ is [[Natural-Transformations-and-the-Yoneda-Lemma#The motivating example|the motivating example]] — concatenation of loops is associative only up to a reparametrization homotopy, and running a loop backwards is an inverse only up to homotopy.)

**Theorem 13.1.4.** If $C$ is a small symmetric monoidal category, $BC$ is an associative, commutative H-space.

The proof is a direct transport of structure. Since $B$ is (lax) symmetric monoidal, $B(\otimes): B(C \times C) \to BC$, composed with the natural iso $BC \times BC \cong B(C\times C)$, gives the multiplication $\mu$. Every coherence isomorphism in $C$ becomes a coherence *homotopy* in $BC$:

- The unit isomorphisms $\lambda, \rho: e \otimes C \cong C \cong C \otimes e$ become natural transformations, hence homotopies witnessing $x_0 = [e]$ as a homotopy unit.
- The associator $\alpha$ becomes a homotopy witnessing associativity of $\mu$.
- The symmetry $\tau$ becomes a homotopy between $\otimes$ and $\otimes \circ (1,2)$ (swap factors), witnessing commutativity.

This is the general engine of the chapter and, frankly, of the whole book: **strict algebraic coherence data upstairs becomes homotopy-coherence data downstairs**, because $B$ turns natural isomorphisms into homotopies (Chapter 11's homotopy-invariance of $B$) and turns products into products up to weak equivalence (via $k$-ification, hence the chapter's standing assumption that all spaces live in $\mathsf{cg}$, the category of compactly generated spaces from §8.5).

**Theorem 13.1.5 upgrades this further.** If $C$ is *permutative* (a strict monoidal category with a symmetry, so the associator and unit isomorphisms are literal identities), then $BC$ isn't just an H-space — it's a genuine algebra over the **Barratt–Eccles operad** (an $E_\infty$-operad from Chapter 12). Every symmetric monoidal category can be *rigidified* to a permutative one with a homeomorphic classifying space (Remark 13.1.6, citing Prop. 8.3.4's strictification theorem), so:

> **Every classifying space of a symmetric monoidal category carries a full $E_\infty$-structure, not just an up-to-homotopy commutative one.**

This is the "why must $BC$ be rigidified first" answer from the guidelines' key question: you need strictness of the algebraic input (permutativity) to get the *stronger, coherent* $E_\infty$ output — an H-space structure alone only gives you homotopy commutativity for a single binary operation, not compatible operations for every arity $n$ simultaneously.

**Remark 13.1.9** records the shadow this leaves on $\pi_0$: for any symmetric monoidal $C$, $\pi_0(C)$ is an abelian monoid under $[C] + [D] := [C \otimes D]$. This is the discrete residue of the H-space structure, and it's exactly the input to §13.2.

**Worked examples (13.1.10).** Two examples recur throughout the chapter as running test cases:
- $\Sigma$, the category of finite sets and bijections, symmetric monoidal under disjoint union ($n \otimes m := n + m$, with the shuffle permutation as the symmetry). $B\Sigma \simeq \coprod_{n \geq 0} B\Sigma_n$ and $\pi_0(\Sigma) = \mathbb{N}_0$.
- $F(R)$, objects $\mathbb{N}_0$, morphisms $F(R)(n,n) = GL_n(R)$, symmetric monoidal via block sum of matrices. $BF(R) \simeq \coprod_{n\geq0} BGL_n(R)$, $\pi_0(F(R)) = \mathbb{N}_0$.

These two examples are the ones that get group-completed at the end of the chapter to produce, respectively, the sphere spectrum's zeroth space and Quillen's algebraic K-theory space of a ring.

```rust
// A symmetric monoidal category, sketched as a trait. This is the
// *algebraic* input; B and group completion are what a homotopy
// theorist does to its classifying space afterward.
trait SymmetricMonoidalCategory {
    type Obj: Clone + PartialEq;
    type Morphism;

    fn unit(&self) -> Self::Obj;
    fn tensor(&self, a: &Self::Obj, b: &Self::Obj) -> Self::Obj;
    // associator, unitors, and the symmetry braiding are witnessed by
    // isomorphisms in the real definition (Ch. 8) -- omitted here since
    // we only need tensor and pi0 to build the Grothendieck monoid below.
    fn iso_class(&self, a: &Self::Obj) -> IsoClass; // the map into pi0(C)
}
```

## 13.2 — Group completion of discrete abelian monoids

This section is purely algebraic — no spaces yet — but it's the model every later construction imitates.

**Definition 13.2.1 (Grothendieck group).** For an abelian monoid $M$, the **Grothendieck group** $G(M)$ is an abelian group with a monoid map $j: M \to G(M)$ satisfying the universal property: for every abelian group $G$ and monoid map $f: M \to G$, there is a *unique* group homomorphism $\bar f: G(M) \to G$ with $\bar f \circ j = f$.

$$
\begin{array}{ccc}
M & \xrightarrow{\ f\ } & G \\
\downarrow{\scriptstyle j} & \nearrow_{\scriptstyle \bar f} & \\
G(M) & &
\end{array}
$$

This universal property is exactly what makes $M \mapsto G(M)$ into a functor that is **left adjoint to the forgetful functor** from abelian groups to abelian monoids — the same adjoint-functor pattern that appears throughout the book (free–forgetful adjunctions in Chapter 2) applied here to (Ab-monoid, Ab-group).

**Explicit construction ($M \times M$ model).** Put the product monoid structure on $M \times M$, $(m_1,n_1)+(m_2,n_2) := (m_1+m_2, n_1+n_2)$, and quotient by $(m_1,n_1)\sim(m_2,n_2)$ iff $\exists \ell \in M$ with $m_1+n_2+\ell = m_2+n_1+\ell$. Read $(m,n)$ as "$m - n$"; the class $[(m,m)]$ is the zero element, and $-[(m,n)] = [(n,m)]$. The stabilizing element $\ell$ is needed precisely because $M$ may lack cancellation — without it the naive relation "$(m_1,n_1)\sim(m_2,n_2)$ iff $m_1+n_2=m_2+n_1$" need not be transitive.

**Alternative construction (free abelian group model).** $G(M) = \mathbb{Z}\{M\} / \langle (m+n) - (m) - (n)\rangle$. Every element is a $\mathbb{Z}$-linear combination of basis elements $[m]$, and sorting by sign of the coefficients shows every element is of the form $[m]-[n]$.

**Example 13.2.3.** $G(\mathbb{N}_0, +, 0) \cong \mathbb{Z}$, and $j$ is injective here because $\mathbb{N}_0$ has the **cancellation property** ($m+p=n+p \Rightarrow m=n$). Injectivity of $j$ is not automatic in general — a monoid without cancellation can have elements that die inside $G(M)$ (Exercise 13.2.4 asks you to find a nontrivial $M$ with trivial $G(M)$: e.g. take $M$ with an absorbing element $\infty$ where $m + \infty = \infty$ for all $m$ — then $[\infty]=[\infty+\infty]$ forces $[\infty]=0$, and if every element maps to $[\infty]$-type behavior the whole group can collapse).

**Example 13.2.5 — topological K-theory.** This is the section's payoff, and the reason "K-theory" is even in the chapter title. Real vector bundles $\mathrm{Vect}_{\mathbb R}(X)$ over a compact Hausdorff space $X$, under Whitney sum $\oplus$, form an abelian monoid. Its Grothendieck group is *defined* to be $KO^0(X)$. Swap real for complex bundles and you get $KU^0(X)$. The nontrivial K-theory class of the Möbius bundle over $S^1$ is a canonical nonzero element that only exists because you *completed* the monoid.

**Definition 13.2.6 (nonabelian case).** For a general (possibly nonabelian) monoid $M$, the **universal group** $U(M) = F(M)/N$, where $F(M)$ is the free group on the underlying set of $M$ and $N$ is the normal subgroup generated by relations $xyz^{-1}$ whenever $xy=z$ holds in $M$. When $M$ is abelian, $U(M) \cong G(M)$ — two different-looking universal constructions collapsing to the same answer, which is itself a small lesson in how universal properties pin down an object up to unique isomorphism regardless of the model you build it from.

```python
# A minimal illustration of the Grothendieck group construction --
# not load-bearing, just makes the (m, n) <-> "m - n" idea concrete.
from fractions import Fraction

def grothendieck_class(m, n, cancel_check=None):
    """Represents the formal difference m - n in G(M)."""
    return (m, n)

def add(p, q):
    (m1, n1), (m2, n2) = p, q
    return (m1 + m2, n1 + n2)

def equiv(p, q, M_has_cancellation=True):
    (m1, n1), (m2, n2) = p, q
    if M_has_cancellation:
        return m1 + n2 == m2 + n1
    # general case needs an existential search for a stabilizer l
    raise NotImplementedError("search over l in M with m1+n2+l == m2+n1+l")
```

## 13.3 — The Grayson–Quillen construction: categorifying the Grothendieck group

Now categorify everything in §13.2. Instead of an abelian monoid $M$, start with a small **symmetric monoidal category** $C$, and instead of formally subtracting elements, formally invert objects.

**Definition 13.3.1 (Grayson–Quillen construction $C^{-1}C$).** Objects are pairs $(C, D)$ of objects of $C$ — think "$C - D$," or "formal quotient $C/D$" if you prefer multiplicative notation. A morphism $(C_1,D_1) \to (C_2,D_2)$ is an equivalence class of pairs $(f: C_1\otimes E \to C_2,\ g: D_1 \otimes E \to D_2)$ for some auxiliary object $E$ — you're allowed to "tensor up" both sides by a common $E$ before comparing them, exactly mirroring the stabilizing element $\ell$ from Definition 13.2.1's discrete construction. Two such pairs are equivalent if an isomorphism $h: E \to E'$ makes the evident square commute.

Setting $E = e$ (the unit) shows every morphism $(f,g)$ in $C\times C$ gives a morphism in $C^{-1}C$ directly, so $C^{-1}C$ genuinely contains a copy of $C \times C$'s morphisms — it's a *generalization*, not a wholly different category.

**Lemma 13.3.2.** $C^{-1}C$ is symmetric monoidal (componentwise: $(C_1,D_1)\otimes(C_2,D_2) := (C_1\otimes C_2, D_1\otimes D_2)$), there's a lax symmetric monoidal functor $j: C \to C^{-1}C$, $j(C) = (C,e)$ — the categorified analogue of $j: M \to G(M)$ — and $\pi_0(C^{-1}C)$ is an honest **abelian group**. The inverse of $[(C,D)]$ is $[(D,C)]$, witnessed by the explicit zigzag
$$(C,D)\otimes(D,C) = (C\otimes D, D \otimes C) \xrightarrow{(1,\tau_{D,C})} (C\otimes D, C\otimes D) \cong (e,e).$$

**Definition 13.3.3 (K-theory space and K-groups).**
$$KC := B(C^{-1}C), \qquad K_n C := \pi_n B(C^{-1}C).$$

This is the moment the chapter title's "algebraic K-theory" cashes out: it is *literally* the classifying space of a categorified Grothendieck-group construction.

**Lemma 13.3.4 — the key compatibility check.** $K_0(C) = \pi_0(KC) \cong G(\pi_0(C))$. In words: taking $\pi_0$ of the K-theory space recovers *exactly* the discrete Grothendieck group of the discrete monoid $\pi_0(C)$ from §13.2 — the categorified construction is faithful to the one-level-down algebraic construction on path components. The proof builds the comparison map $\varphi: (C,D) \mapsto [C]-[D]$ directly by hand and shows it's well-defined, surjective, and injective by chasing zigzags — a nice worked example of "define a map out of a quotient-like construction by checking it respects every identification in [[Simplicial-Objects-and-Simplicial-Sets#The definition|the definition]]."

**Examples 13.3.6–13.3.8 (this is where "algebraic K-theory" gets its name):**
- $P(R)^{-1}P(R)$ for the category $P(R)$ of finitely generated projective $R$-modules (realized concretely via idempotent matrices, $P^2=P$) gives $\pi_0 \cong K_0(R)$, the *classical* $K_0$ of a ring.
- $F(R)^{-1}F(R)$ for finitely generated *free* modules gives the group completion of $\mathbb{N}_0$, i.e. just $\mathbb{Z}$ — a strictly weaker invariant than $K_0(R)$ unless every projective module over $R$ is free (e.g. local or PID-like rings).
- $\Sigma^{-1}\Sigma$ is identified (via Sagave–Schlichtkrull) with the category $J$ built from $I$ (finite sets and injections, Example 1.2.3) — showing the abstract Grayson–Quillen machine reduces to a concrete, previously-known combinatorial category in this case.

```rust
// The Grayson-Quillen construction as a type: pairs of objects, with
// morphisms carrying an existential witness object E. In Rust terms
// this is almost a "difference type" or a signed delta over a
// commutative-monoid-shaped resource.
struct GraysonQuillenObj<C> {
    plus: C,  // the "C" in (C, D)
    minus: C, // the "D" in (C, D)
}

// A morphism (C1, D1) -> (C2, D2) existentially quantifies over E:
// exists E, f: C1 (x) E -> C2, g: D1 (x) E -> D2, up to the equivalence
// that lets you change E via an isomorphism. This existential-witness
// shape is exactly what a Coq/Lean sigma type would encode:
//   Sigma (E : C.Obj), (Hom (tensor C1 E) C2) * (Hom (tensor D1 E) D2)
```

**Lean framing.** The existential-with-equivalence-relation pattern in Definition 13.3.1 is precisely a **quotient of a sigma type**: morphisms are elements of $\Sigma(E : \mathrm{Obj}(C)).\ \mathrm{Hom}(C_1\otimes E, C_2) \times \mathrm{Hom}(D_1\otimes E, D_2)$, modulo an equivalence relation generated by isomorphisms of the witness $E$. This is the same shape you'd reach for whenever a construction needs to say "up to a choice of auxiliary data" — a `Quotient` of a `Setoid` built over a dependent pair, and it's worth flagging because it's structurally identical to how localization of a category at a class of morphisms (§11.5) packages "invert these morphisms formally."

## 13.4 — Group completion of H-spaces: closing the triangle

The final section makes precise, at the level of spaces, what it means for $KC = B(C^{-1}C)$ to actually **be** "the" group completion of $BC$ — not just something that happens to have the right $\pi_0$.

**Definition 13.4.1 (group completion of an H-space).** Let $X$ be an associative H-space (CW homotopy type, with left translation homotopic to right translation by every element — a "homotopy-commutative-enough" condition). A **group completion** of $X$ is an H-space $Y$ (same hypotheses) with a map $f: X \to Y$ such that:
1. $\pi_0(f): \pi_0(X) \to \pi_0(Y)$ exhibits $\pi_0(Y)$ as the (discrete, §13.2) Grothendieck group $G(\pi_0(X))$, **and**
2. $f$ induces, for every commutative ring $k$, an isomorphism after localizing homology at $\pi_0(X)$:
$$H_*(X;k)[\pi_0(X)^{-1}] \xrightarrow{\ \cong\ } H_*(Y;k). \tag{13.4.1}$$

Why localize homology rather than just asking $H_*(X;k)\cong H_*(Y;k)$ directly? Because $H_0(X;k) = k[\pi_0(X)]$ is a *monoid ring*, and $H_*(X;k)$ is a graded module over it (via the Künneth map composed with $\mu_*$) — group completion should turn that monoid-ring action into an honest group-ring action, and the only way to force $\pi_0(X)$'s elements to become invertible on the nose is to literally invert them in the coefficient ring, i.e. localize. This is the precise answer to the guidelines' key question: checking (13.4.1) is what "being the group completion" *means*, not merely having the right $\pi_0$.

**Remark 13.4.2** (Quillen): it suffices to check (13.4.1) for $k = \mathbb{Q}$ and $k = \mathbb{F}_p$ for every prime $p$ — you don't need to verify it over every commutative ring. This is a standard arithmetic-fracture-square argument: rational and mod-$p$ homology jointly detect all the information visible to ordinary integral homology (via the universal coefficient theorem and the fact that a map of finitely-generated abelian groups that's an iso rationally and mod every prime is an iso), so checking the two extremes is exhaustive.

**Theorem 13.4.3 (a Whitehead theorem with local coefficients)** and the discussion around it explain *why* group-like H-spaces are the easy case: if $X$ is group-like, $X \simeq \pi_0(X) \times X_0$ (all path components are homeomorphic, correctable by the group structure), every local coefficient system on $X$ is simple, and Theorem 13.4.3 reduces "is $f: X\to Y$ a homotopy equivalence" down to a check on the identity components $X_0 \to Y_0$ alone.

**Proposition 13.4.4 [May74].** For a topological monoid $M$ with left/right translation homotopic, the canonical map $\alpha: M \to \Omega BM$ is a group completion. This single statement instantiates the whole chapter's running examples: applying it to $M = \coprod_n B\Sigma_n$ or $M = \coprod_n BGL_n(R)$ gives $\pi_1(B(\coprod_n B\Sigma_n)) \cong G(\pi_0) = \mathbb{Z}$, and similarly identifies $\pi_1$ of the bar construction on $\coprod_n BGL_n(R)$ with the classical $K$-group.

**Theorem 13.4.5** extends the same idea to $E_\infty$- and $E_n$-operad actions ($\Omega^n\Sigma^n X \to \Omega^n\Sigma^n X$-style group completions for $n>1$, via [Segal, Cohen–Lada–May]) — the homotopical group completion machinery isn't special to symmetric monoidal categories, it works for any sufficiently coherent H-space-like structure.

**Theorem 13.4.6 [Grayson]** — the theorem that finally *ties the categorical and homotopical constructions together*: if $C$ is a small symmetric monoidal **groupoid** in which $(-)\otimes C: C \to C$ is faithful for every object $C$, then $B(C^{-1}C)$ is a group completion of $BC$ **in the sense of Definition 13.4.1** — not merely a space with the right $\pi_0$, but one satisfying the homology-localization condition. This is what licenses calling $KC$ "the" K-theory space rather than merely "a" space with the correct $\pi_0$-group. Applied to the running examples:
$$B(\Sigma^{-1}\Sigma) \simeq B\left(\coprod_{n\geq0} B\Sigma_n\right), \qquad B(F(R)^{-1}F(R)) \simeq B\left(\coprod_{n\geq0} BGL_n(R)\right),$$
the second of which is (one model of) Quillen's classical definition of the algebraic K-theory space of a ring.

**Remark 13.4.7 (Kan–Thurston, McDuff)** closes the chapter with a striking capstone fact, only loosely tied to group completion but showing how far "space $\leftrightarrow$ (something built from a category or monoid)" reaches: *every* connected space $X$ is homology-equivalent to $BG_X$ for some discrete group $G_X$ (Kan–Thurston), and — since $BG_X$ has only one nonzero homotopy group, so this can't be a homotopy equivalence in general — McDuff strengthened this to: every connected $X$ has the same *weak homotopy type* as $BM$ for some discrete monoid $M$. Every space, up to weak equivalence, is a classifying space of *something* discrete.

## Synthesis: where this sits in the book, and what it buys you

```mermaid
flowchart TD
    A["Symmetric monoidal category C<br/>(Ch. 8)"] -->|classifying space B| B["BC: associative,<br/>commutative H-space (13.1)"]
    A -->|rigidify (8.3.4)| A2["permutative category"]
    A2 -->|B| B2["BC: E-infinity algebra<br/>over Barratt-Eccles operad (13.1.5)"]
    A -->|pi0, discrete shadow| M["pi0(C): abelian monoid (13.1.9)"]
    M -->|Grothendieck group G(-) (13.2)| G["G(pi0(C)): abelian group"]
    A -->|Grayson-Quillen C^-1 C (13.3)| C2["C^-1 C: symmetric monoidal,<br/>pi0 is a group"]
    C2 -->|B| KC["K(C) = B(C^-1 C):<br/>K-theory space (13.3.3)"]
    KC -->|pi0| G
    B -->|"group completion (13.4),<br/>homology-localization iso"| KC
    KC --> LOOP["Ch. 14: iterated/infinite<br/>loop space models"]
```

This chapter is the hinge between the "purely categorical" first half of the book and the deep homotopy-theoretic machinery of Chapters 14–16. It depends on:
- **Chapter 8** (monoidal categories, coherence, strictification, the symmetry $\tau$) for the algebraic input,
- **Chapter 11** (the classifying-space functor $B$, its lax symmetric monoidality, and homotopy invariance) for turning that algebra into topology,
- **Chapter 12** (the Barratt–Eccles operad) for the $E_\infty$ upgrade in §13.1.

And it feeds directly into:
- **Chapter 14**, where the same group-completion idea (applied to $\Gamma$-spaces, $I$-spaces, braided injections) produces models of $n$-fold and infinite loop spaces — $KC$ here is the $n=1$ case of a much larger machine,
- the entire subject of algebraic K-theory as practiced today, where $K$-theory spaces/spectra of rings, schemes, and categories are *defined* via exactly this group-completion process (or its modern refinement, Waldhausen's S-dot construction, which this chapter is a direct ancestor of).

**On the learning-goals connection (`type-theory`).** The load-bearing transferable idea here isn't K-theory itself — it's the **discipline of universal constructions defined by a lifting/uniqueness property**, which is the same discipline underlying definitional equality and elaboration in a dependent type checker. Definition 13.2.1's diagram ("for every $f$ there is a *unique* $\bar f$ making the triangle commute") is the *identical logical shape* as a `PROP`-style typing judgment's uniqueness clause, or as the specification of `isDefEq`: you don't compute the Grothendieck group by inspecting its internals, you characterize it by what maps *out* of it must look like, exactly as you'd characterize a metavariable's solution by what any valid instantiation must satisfy. The Grayson–Quillen construction's morphisms — equivalence classes of pairs $(f,g)$ up to a choice of witness object $E$ — are also a concrete, worked example of **quotienting a sigma-type by a setoid relation**, the same pattern an elaborator uses when normalizing terms that are equal only after choosing compatible metavariable instantiations. Neither of these is a strained analogy the book itself makes; they're the same categorical/logical skeleton (universal property, quotient-of-existential) appearing in two different technical costumes.
