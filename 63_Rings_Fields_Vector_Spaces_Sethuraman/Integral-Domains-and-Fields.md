---
title: Integral Domains and Fields
source: Rings, Fields, and Vector Spaces (B. A. Sethuraman)
chapter: "2. Rings and Fields (pp. 49–54)"
tags: [abstract-algebra, ring-theory, field-theory, zero-divisors, integral-domain]
---

[[book-guidelines|↩ Back to guidelines]]

# Integral Domains and Fields

## What breaks without this: zero-divisors

A ring, as defined earlier in Chapter 2, is a very permissive structure — associative, distributive, with additive inverses — but it says nothing about what multiplication is allowed to *do* to nonzero elements. In particular, nothing stops two nonzero elements from multiplying to zero. Concretely, in $M_2(\mathbb{R})$, the ring of $2\times 2$ real matrices:

$$
\begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}
\begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}
=
\begin{pmatrix} 0 & 0 \\ 0 & 0 \end{pmatrix}
$$

Neither factor is the zero matrix, yet the product is. If your entire intuition for "multiplication" comes from $\mathbb{Z}, \mathbb{Q}, \mathbb{R}, \mathbb{C}$ — subrings of $\mathbb{C}$, all of them — this looks pathological. It isn't; it's just a fact about *some* [[Rings|rings]] and not others, and it turns out to be exactly the fact that determines whether cancellation, division, and (later) polynomial factorization behave the way you'd want.

**Definition 2.17 (zero-divisor).** A zero-divisor in a ring $R$ is a nonzero element $a$ for which there exists a nonzero element $b$ with $ab = 0$ or $ba = 0$.

Zero-divisors aren't a matrix-only curiosity. $\mathbb{Z}/4\mathbb{Z}$ has one: $[2]_4 \cdot [2]_4 = [0]_4$, and in general $\mathbb{Z}/n\mathbb{Z}$ has zero-divisors exactly when $n$ is composite (the book leaves the "$n$ prime $\Rightarrow$ no zero-divisors" direction as a fact to prove, and it falls straight out of Lemma 1.13 from Chapter 1: if $p \mid ab$ then $p \mid a$ or $p \mid b$). The direct product of two nonzero rings always has zero-divisors too — $(1,0)\cdot(0,1) = (0,0)$ — which is the general shape of the phenomenon: whenever a ring "factors" into independent pieces, elements that are nonzero in one piece and zero in the other will multiply to give zero overall.

## Naming the well-behaved rings

Rings without zero-divisors are simply easier to reason about — this is the entire motivation for singling them out:

**Definition 2.18 (integral domain).** An integral domain is a commutative ring with no zero-divisors.

Equivalently — and this is the form you'll actually use in proofs — $R$ is an integral domain iff whenever $ab = 0$ for $a, b \in R$, either $a = 0$ or $b = 0$. $\mathbb{Z}, \mathbb{Q}, \mathbb{R}, \mathbb{C}$ are all integral domains (by direct appeal to familiarity — the book doesn't reprove this from [[Rings#The ring axioms|the ring axioms]]). A useful inheritance fact: *any subring of an integral domain is itself an integral domain* — if $ab = 0$ held inside a subring $S \subseteq R$, it would witness $ab = 0$ in $R$ too, contradicting $R$'s domain property. In particular, every subring of $\mathbb{C}$ is automatically an integral domain, which is why $\mathbb{Z}[\sqrt2]$, $\mathbb{Q}[i]$, etc. never need to be checked for zero-divisors individually. (The converse direction — if a *subring* $S$ is a domain, must $R$ be? — is explicitly left as an open question in the text; it's false in general, and thinking about why is a good exercise: nothing about $S$'s good behavior constrains elements of $R \setminus S$.)

The payoff for excluding zero-divisors is cancellation, which otherwise silently fails:

**Lemma 2.19.** Let $R$ be an integral domain, $a \ne 0$. If $ab = ac$, then $b = c$.

*Proof.* $ab = ac \Rightarrow a(b-c) = 0$. Since $a \ne 0$ and $R$ has no zero-divisors, $b - c = 0$. $\blacksquare$

Notice exactly where the domain hypothesis is load-bearing: the proof reduces "$ab=ac \Rightarrow b=c$" to "$a \cdot x = 0 \Rightarrow x = 0$ (given $a\neq0$)" — which *is* the no-zero-divisors condition, just restated. Take this lemma into $M_2(\mathbb{R})$ and it fails immediately: $\begin{pmatrix}1&0\\0&0\end{pmatrix}\begin{pmatrix}1&0\\0&0\end{pmatrix} = \begin{pmatrix}1&0\\0&0\end{pmatrix}\begin{pmatrix}1&0\\0&1\end{pmatrix}$ but the two right-hand factors are different matrices.

## From "no zero-divisors" to "you can divide"

Integral domains are strictly nicer than general commutative rings, but $\mathbb{Z}$ itself is a integral domain that still can't do something you'd expect a number system to do: divide. There's no integer solving $5x = 3$. Sethuraman's framing of *why* is worth internalizing, because it's the definitional move that produces fields: dividing 3 by 5 is really *multiplying* 3 by $1/5$, where $1/5$ is characterized purely algebraically as the element satisfying $5 \cdot (1/5) = 1$ — a **multiplicative inverse**. The reason $\mathbb{Z}$ can't divide is that most nonzero integers simply don't have one.

**Definition 2.20 (field).** A field is an integral domain in which every nonzero element $a$ has an element $b$ (written $1/a$ or $a^{-1}$) with $ab = 1$.

Two remarks the book flags as easy but important:
- $F^* := F \setminus \{0\}$ is a group under multiplication (Remark 2.21) — associativity and the identity $1$ are inherited from the ring, and now every element has an inverse *by definition*.
- $0$ can never have an inverse, since $a \cdot 0 = 0 \ne 1$ for any $a$ — "division by zero is undefined" isn't a programming convention, it's a theorem about what $0$ does to multiplication (Remark 2.22).

**Examples 2.23.** $\mathbb{R}$ and $\mathbb{C}$ are fields (for $\mathbb{C}$: $\overline{(a+ib)}/(a^2+b^2)$ is the inverse of $a + ib$). $\mathbb{Q}[\sqrt2]$ is a field — rationalizing the denominator gives $\dfrac{1}{a+b\sqrt2} = \dfrac{a - b\sqrt2}{a^2 - 2b^2}$, and $a^2-2b^2 \ne 0$ unless $a=b=0$ because $\sqrt2 \notin \mathbb{Q}$. By contrast $\mathbb{Z}[\sqrt2]$ (integer $a,b$) is *not* a field: it's an integral domain (a subring of $\mathbb{R}$) but $1/2$ isn't of the form $a+b\sqrt2$ with $a,b\in\mathbb{Z}$ — same failure mode as $\mathbb{Z}$ itself, for the same underlying reason. $\mathbb{R}(x)$, the field of rational functions $f(x)/g(x)$, is the field-of-fractions construction applied to the domain $\mathbb{R}[x]$ — every nonzero domain sits inside a smallest field the same way, though the book doesn't name the general construction here.

Finally, the notion of a subring specializes:

**Definition 2.24 (subfield, field extension).** $F \subseteq K$ is a subfield if $F$ is a subring of $K$ and is itself a field. We then call $K$ an extension field of $F$, and write the pair as the field extension $K/F$.

The gap between "subring" and "subfield" is exactly the gap this whole section has been building toward: a subring $R \subseteq K$ has, for each nonzero $a\in R$, an inverse $1/a$ *somewhere in $K$* (since $K$ is a field) — but that inverse might not land back inside $R$. $\mathbb{Z} \subset \mathbb{R}$ is the paradigm case: $1/2$ exists in $\mathbb{R}$ but not in $\mathbb{Z}$, so $\mathbb{Z}$ is a subring of $\mathbb{R}$ but not a subfield. $\mathbb{Q} \subset \mathbb{Q}[\sqrt2] \subset \mathbb{R} \subset \mathbb{C}$, however, is a chain of *subfields* — every inverse taken inside a smaller field is still found inside that same smaller field. This chain is exactly the kind of structure Chapters 4–7 will measure (via extension *degree*) to answer the constructibility question.

## Grounding: this is a trait hierarchy

The domain/field distinction is a textbook example of a *refinement* relationship between typeclasses, and it's worth being precise about which method's totality is actually being asserted at each level.

```rust
trait CommutativeRing:
    Sized + Add<Output = Self> + Mul<Output = Self> + Neg<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
}

/// Adds nothing new *structurally* — it's a refinement, asserting a
/// PROPERTY of the existing operations (no zero-divisors), not a new
/// operation. In Rust there's no way to encode "no zero-divisors" as
/// a trait bound checked by the compiler — it's a proof obligation on
/// the impl, not something the type system enforces. This is exactly
/// where Lean's typeclasses diverge from Rust's: see below.
trait IntegralDomain: CommutativeRing {}

trait Field: IntegralDomain {
    /// Partial by construction: None exactly at Self::ZERO.
    /// This signature *is* Remark 2.22, encoded: the type system
    /// forces every call site to handle the zero case, rather than
    /// letting "divide by zero" be an unchecked runtime possibility.
    fn inverse(&self) -> Option<Self>;
}
```

The reason `IntegralDomain` looks structurally empty in Rust is precisely the reason it's interesting mathematically: "no zero-divisors" is a *universally quantified proof obligation* over all pairs of elements ($\forall a, b \ne 0,\ ab \ne 0$), not an operation you can implement and typecheck. Rust's trait system can't express it; it can only be documented and relied upon (or, in an `unsafe`-adjacent sense, assumed by algorithms like polynomial-root counting in Chapter 5 that silently require it). This is exactly the gap that a proof assistant closes.

**Lean / Mathlib** names this hierarchy almost verbatim: `Mathlib`'s `IsDomain` extends `CommRing` and asserts `mul_eq_zero : a * b = 0 → a = 0 ∨ b = 0` as an actual field of the structure — a *proof term*, not just a signature, so the "no zero-divisors" property is checked once at the instance and then available everywhere, not re-asserted per call site. `Field extends DivisionRing, CommRing` similarly bundles a genuine `inv` function together with the axiom `mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1`. Lean's `a⁻¹` for `a = 0` is total (it's defined to *equal* `0` in `Field`, following the junk-value convention rather than `Option`), which is a deliberate departure from Rust's `Option<Self>` above — Lean prefers a total function with a degenerate case over a partial one, precisely so that later proofs don't have to case-split on `Option` at every use of `inv`. Both encodings are faithful to the mathematics; they differ only in how they push the $a=0$ case out of the type signature versus into the axioms.

## Why this matters for a refinement-type checker

The zero-divisor/cancellation story is a clean small-scale rehearsal for a pattern that recurs constantly in verified compiler work: *an algebraic simplification rule (cancel $a$ from both sides) is only sound under a side-condition ($a \ne 0$, ring is a domain)*. That's structurally identical to what a refinement-type system has to track when it simplifies `x * y == x * z` to `y == z` — the rewrite needs a **precondition** ($x \ne 0$) attached, exactly the way $a \ne 0$ is attached to Lemma 2.19. And Definition 2.20's totality gap ($1/a$ defined only for $a \ne 0$) is the algebraic ancestor of the canonical refinement-type example: `fn div(x: i32, y: NonZero<i32>) -> i32` — a *type-level* enforcement of exactly the side-condition this section proves is unavoidable, not a convention.

## Where this leads

Chapter 3 needs a field of scalars for the vector-space axioms to typecheck (`(rs)\cdot v = r\cdot(s\cdot v)$ implicitly needs $r,s$ drawn from a structure where multiplication behaves), and Chapter 4's field extensions $K/F$ are literally built on Definition 2.24's subfield relation — $[K:F]$, the "degree" that eventually decides constructibility, is measured by treating $K$ as a vector space over the subfield $F$.
