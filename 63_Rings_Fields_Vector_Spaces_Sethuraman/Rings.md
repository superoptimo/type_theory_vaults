---
title: Rings
source: Rings, Fields, and Vector Spaces (B.A. Sethuraman)
chapter: "Chapter 2: Rings and Fields (pp. 29–48)"
tags: [abstract-algebra, rings, algebraic-structures]
---

[[book-guidelines|↩ Back to guidelines]]

# Rings

## What problem does "ring" solve?

Chapter 1 studied $\mathbb{Z}$ through one lens: divisibility, which is defined purely in terms of multiplication ($d \mid a$ iff $a = db$). But that left something on the table — the chapter never asked *why* $\mathbb{Z}$'s addition and multiplication behave the way they do, only what falls out once you assume they do.

Sethuraman's move at the start of Chapter 2 is the classic abstraction step: notice that $\mathbb{Z}$, $\mathbb{Q}$, $2\times 2$ real matrices, and $\mathbb{R}[x]$ (polynomials) are all *different sets* that nonetheless carry two operations — commonly called "addition" and "multiplication" — with a shared list of behavioral guarantees. Rather than re-derive the same facts (cancellation, distributivity-driven expansion, etc.) separately for each set, you isolate the shared axioms once and call anything satisfying them a **ring**. Every theorem you prove about "a ring" is then a theorem about $\mathbb{Z}$, $\mathbb{Q}$, $M_2(\mathbb{R})$, and $\mathbb{R}[x]$ simultaneously, for free.

If you've written generic code against a trait/typeclass instead of a concrete type, this is exactly that move, just aimed at $+$ and $\times$ instead of at, say, `Iterator`.

## Binary operations, then groups

Before defining a ring, the book defines the more primitive notion of a **binary operation**: given a set $S$, a binary operation is a function $f : S \times S \to S$ — literally "you feed it two elements of $S$, it hands back a third element of $S$." Addition and multiplication on $\mathbb{Z}$ are binary operations in this sense; nothing about them being "arithmetic" is doing any work yet, only the fact that they are total functions $S \times S \to S$.

**What breaks without closure.** If $f$ could sometimes hand back something outside $S$, you couldn't chain operations — $f(f(a,b), c)$ wouldn't type-check. Closure is the precondition for *any* further algebraic structure to make sense at all; it's the reason, later, that checking "is this subset a subring?" always starts by checking closure first (Lemma 2.11 below).

$(\mathbb{Z}, +)$ turns out to satisfy three properties that recur across mathematics often enough to deserve their own name:

> **Definition 2.1 (Group).** A group is a set $S$ with a binary operation $f : S \times S \to S$ such that
> 1. $f$ is associative,
> 2. $S$ has an identity element with respect to $f$, and
> 3. every element of $S$ has an inverse with respect to $f$.

$(\mathbb{Z}, +)$ is a group: associativity holds, $0$ is the identity, and $-a$ is the inverse of $a$. Add commutativity and you get:

> **Definition 2.2 (Abelian group).** A group in which $f(a,b) = f(b,a)$ for all $a, b \in S$.

$(\mathbb{Z}, +)$ is abelian. $(\mathbb{Z}, \cdot)$, by contrast, is *not* a group — $2$ has no multiplicative inverse in $\mathbb{Z}$ — even though it is associative and has an identity ($1$). This asymmetry between $+$ and $\cdot$ is exactly what the ring axioms below are built to capture: full group structure for addition, but only a weaker set of guarantees for multiplication.

## The ring axioms

> **Definition 2.3 (Ring).** A ring is a set $R$ with two binary operations $+$ and $\cdot$ such that
> 1. $a + b = b + a$ for all $a, b \in R$ (commutativity of $+$),
> 2. $a + (b+c) = (a+b) + c$ for all $a,b,c \in R$ (associativity of $+$),
> 3. there exists $0 \in R$ with $a + 0 = a$ for all $a$ (additive identity),
> 4. for each $a \in R$ there exists $-a \in R$ with $a + (-a) = 0$ (additive inverses),
> 5. $a \cdot (b \cdot c) = (a \cdot b) \cdot c$ for all $a,b,c \in R$ (associativity of $\cdot$),
> 6. there exists $1 \in R$ with $a \cdot 1 = 1 \cdot a = a$ for all $a$ (multiplicative identity),
> 7. $a \cdot (b+c) = a \cdot b + a \cdot c$ and $(a+b)\cdot c = a \cdot c + b \cdot c$ for all $a,b,c \in R$ (distributivity, both sides).

Compactly: $(R, +)$ is an abelian group, $\cdot$ is associative with an identity, and $\cdot$ distributes over $+$ from both sides. Notice what's conspicuously *absent*: commutativity of $\cdot$, and multiplicative inverses. Both are true of $\mathbb{Z}$, but the book deliberately keeps them out of the base definition, because there are important rings — $2\times 2$ real matrices, most centrally — where multiplication genuinely isn't commutative:
$$
\begin{pmatrix}0&1\\0&0\end{pmatrix}\begin{pmatrix}1&0\\0&0\end{pmatrix} \ne \begin{pmatrix}1&0\\0&0\end{pmatrix}\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$
Requiring commutativity in the definition of "ring" would exile matrices from the theory, which is too high a price for a property most — but not all — rings happen to have. So the book carves it out as a separate refinement:

> **Definition 2.6 (Commutative ring).** A ring $R$ in which $a \cdot b = b \cdot a$ for all $a, b \in R$.

**What breaks without distributivity.** Distributivity is the one axiom that *entangles* $+$ and $\cdot$ — without it, you'd have two independent group-like structures sharing a carrier set but no way to expand $a(b+c)$, which means no polynomial expansion, no FOIL, no factoring. Every algebraic manipulation you take for granted (expanding $(x+1)(x-1) = x^2 - 1$) is an appeal to axiom 7. This is also *why* the book requires distributivity on both sides separately — in a noncommutative ring, left-distributivity doesn't hand you right-distributivity for free.

Remark 2.5 makes an important terminological point: the informal phrase "number system," used loosely in Chapter 1, is now given a precise meaning — a *number system just is a ring*. But the book flags this as nonstandard usage outside its own pages; "ring" is the term you'll see in the literature.

### Worked examples (Examples 2.7)

The book runs through a deliberately varied gallery to show the axioms are doing real generalizing work, not just relabeling $\mathbb{Z}$:

- $\mathbb{Q}, \mathbb{R}, \mathbb{C}$ — commutative rings, familiar.
- $\mathbb{Q}[\sqrt2] = \{a + b\sqrt2 : a,b \in \mathbb{Q}\}$ — closed under the usual $+,\cdot$ because $(\sqrt2)^2 = 2$ folds back into the rational part; a nontrivial subring of $\mathbb{R}$.
- $\mathbb{Q}[i] = \{a+bi : a,b\in\mathbb{Q}\}$ — same idea, using $i^2=-1$.
- $\mathbb{Z}_{(2)}$ — rationals reducible to a fraction with *odd* denominator; oddness is exactly the property that keeps this set closed under $+$ and $\cdot$ (adding/multiplying two odd-denominator fractions never reintroduces a factor of $2$ in the denominator).
- $M_n(\mathbb{R})$ — $n \times n$ real matrices; noncommutative for $n \ge 2$, the book's running counterexample to commutativity.
- $\mathbb{R}[x]$ — polynomials in one variable; degree of a nonzero polynomial and its highest coefficient are defined, but the zero polynomial's degree is left *undefined on purpose* (this pays off later when theorems need to talk uniformly about "the degree of a product" without special-casing zero).
- $\mathbb{Z}/2\mathbb{Z}$ — the two-element ring $\{[0]_2, [1]_2\}$ (even/odd classes), with addition and multiplication tables built from "even+even=even" style reasoning. This is the book's first genuinely *finite* ring, planting the seed that "ring" doesn't mean "infinite number system."

### Rust grounding: a ring as a trait

The axioms translate almost mechanically into a trait, with the caveat that Rust's type system can state the *signatures* (closure, identity elements, inverse) but can't check the *laws* (associativity, distributivity) — those live only as doc-comments or, if you want machine-checked laws, as a property-testing suite (`proptest`) run against every implementor.

```rust
trait Ring: Sized + Clone + PartialEq {
    fn zero() -> Self;              // additive identity
    fn one() -> Self;               // multiplicative identity
    fn add(&self, other: &Self) -> Self;
    fn neg(&self) -> Self;          // additive inverse
    fn mul(&self, other: &Self) -> Self;

    // Laws (unchecked by the type system — verify via property tests):
    // add is associative & commutative; zero is additive identity;
    // neg gives additive inverses; mul is associative;
    // one is multiplicative identity; mul distributes over add (both sides).
}

trait CommutativeRing: Ring {
    // mul is additionally commutative — no new methods, just a stronger
    // law obligation on the same operations.
}
```

`M_n(\mathbb{R})` implements `Ring` but not `CommutativeRing`; `Q[\sqrt2]`, `\mathbb{Z}/2\mathbb{Z}`, and `\mathbb{R}[x]` (as a `Vec<f64>` of coefficients, say) implement both. The trait boundary *is* the axiom boundary — this is precisely why the book bothers separating Definition 2.3 from Definition 2.6.

### Lean grounding: this is Mathlib's own hierarchy, almost verbatim

Lean's Mathlib doesn't just have an analogous structure — it has *this exact* structure, under *this exact* name, built the same way for the same reason (share proofs across $\mathbb{Z}$, $\mathbb{Q}$, matrix rings, polynomial rings):

```lean
class Ring (α : Type) extends AddCommGroup α, Monoid α where
  left_distrib  : ∀ a b c : α, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c

class CommRing (α : Type) extends Ring α where
  mul_comm : ∀ a b : α, a * b = b * a
```

`extends AddCommGroup α` is literally Definition 2.1 + Definition 2.2 applied to `+` — Lean's kernel is checking, by construction, that `(R, +)` is an abelian group before `Ring` is even allowed to add multiplication on top. `Monoid α` supplies associativity and the identity `1` for `*` (axioms 5–6). The two distributivity fields are axiom 7, split exactly the way Sethuraman splits it. Unlike the Rust sketch, Mathlib's laws genuinely are checked — `left_distrib` etc. are *proof obligations* every instance must discharge, not documentation. If you're building a trusted kernel later, this is the fidelity level you're aiming for: Rust's trait gives you the *shape*, Lean's typeclass gives you the shape *plus a machine-checked witness that the laws actually hold*.

## Subrings: when does a subset inherit the ring structure?

Once you have a ring $R$, a natural question is whether some subset $S \subseteq R$, using the *same* $+$ and $\cdot$ (just restricted to $S$), is itself a ring. The three motivating examples above ($\mathbb{Q}[\sqrt2] \subseteq \mathbb{R}$, $\mathbb{Q}[i] \subseteq \mathbb{C}$, $\mathbb{Z}_{(2)} \subseteq \mathbb{Q}$) are exactly this phenomenon, and the book now names it precisely.

> **Definition 2.9.** $S$ is *closed under addition* if $s_1, s_2 \in S \implies s_1+s_2 \in S$; similarly for multiplication.
>
> **Definition 2.10 (Subring).** Let $S \subseteq R$ be closed under $+$ and $\cdot$, with $1 \in S$. If $S$, under the operations induced from $R$, is itself a ring, then $S$ is a *subring* of $R$.

Checking "is this a ring?" from scratch every time would mean re-verifying all seven axioms. But most of those axioms (associativity, distributivity, commutativity of addition) are *inherited for free* from $R$ — if they hold for all elements of $R$, they certainly hold for the subset $S$. What actually needs checking is much shorter:

> **Lemma 2.11.** If $S \subseteq R$ is closed under addition, closed under multiplication, contains $1$, and contains $-a$ for every $a \in S$, then $S$ is a subring of $R$.

This is the general pattern for verifying any algebraic substructure: don't reprove the axioms, prove *closure* under the operations and the presence of the distinguished elements ($0$ falls out from $1 + (-1) \in S$), and let the ambient structure's axioms do the rest. It's the same proof-reuse instinct as inheriting a trait's default-method behavior instead of reimplementing it.

## Generating a subring: $S[a]$

Here's a sharper question, and the one that matters most for everything downstream in the book (field extensions in Chapter 4, minimal polynomials in Chapter 6): given a subring $S \subseteq R$ and *one extra element* $a \in R$, what is the **smallest** subring of $R$ that contains both $S$ and $a$?

Take $R = \mathbb{R}$, $S = \mathbb{Q}$, $a = 1+\sqrt2$. The set $\mathbb{Q} \cup \{1+\sqrt2\}$ is *not* closed — $(1+\sqrt2)^2 = 3+2\sqrt2$ isn't in it, nor is $2 + (1+\sqrt2)$. To fix closure under multiplication you need every power $a, a^2, a^3, \dots$; to fix closure under addition combined with scaling by $S$, you need every $\mathbb{Q}$-linear combination of those powers. That's exactly:

> **Definition 2.13.** An expression $s_0 + s_1 a + s_2 a^2 + \cdots + s_n a^n$ (with $s_i \in S$) is a *polynomial expression in $a$ with coefficients in $S$*. $S[a]$ denotes the set of all such expressions — the subring of $R$ **generated** by $S$ and $a$.

> **Lemma 2.14.** $S[a]$, as defined, actually is a subring of $R$.

This is a *closure construction* — you start with a generating set and close it under the operations you need, and the result is provably the least fixed point containing your generators. If you've built a symbol table's scope-closure, a dependency graph's transitive closure, or (relevantly for your elaborator work) the smallest context/term satisfying a set of constraints, this is the same shape: closure-under-operations as the definition of "smallest structure containing X."

Working through $\mathbb{Q}[\sqrt2]$: every polynomial expression $q_0 + q_1\sqrt2 + q_2(\sqrt2)^2 + \cdots$ collapses, because $(\sqrt2)^2 = 2$ is rational, so every even power contributes to the rational part and every odd power contributes to the $\sqrt2$-coefficient. The infinite-looking generating process collapses to the two-dimensional set $\{a + b\sqrt2\}$ you'd guess — which is *why* the notation $\mathbb{Q}[\sqrt2]$ from Examples 2.7 makes sense in hindsight: it's literally $\mathbb{Q}[a]$ for $a = \sqrt2$.

### The subtlety in Remark 2.16 — and why it matters later

This is the sharpest idea in the chapter, and it's easy to read past. A *polynomial expression in $a$* is not the same kind of object as a *polynomial in the formal variable $x$*, even though they look identical on the page.

- **Polynomials in $x$:** $\sum f_i x^i = \sum g_i x^i$ iff $f_i = g_i$ for every $i$ (same degree, same coefficients, no exceptions). Equality is *syntactic*.
- **Polynomial expressions in $a$:** two expressions of *different* apparent degree can be genuinely equal as elements of $S[a]$, because $a$ itself might satisfy some algebraic relation.

The book's example: with $a = \sqrt2$,
$$
1 + \sqrt2 + (\sqrt2)^2 + (\sqrt2)^3 = 3 + 3\sqrt2,
$$
a "degree 3" expression equal to a "degree 1" expression — because $(\sqrt2)^2 - 2 = 0$ lets you rewrite $(\sqrt2)^2 \mapsto 2$ and $(\sqrt2)^3 \mapsto 2\sqrt2$ at will. Formal polynomials in $x$ have *no* such collapsing relation available (a nonzero polynomial in $x$ is never the zero function unless every coefficient is $0$); polynomial expressions in an algebraic element do, whenever that element satisfies some nonzero polynomial equation.

**Why this is load-bearing, not a curiosity.** This is the exact phenomenon Chapter 6 turns into the *minimal polynomial* $m_{F,a}$: the (unique, monic, lowest-degree) polynomial capturing the relation $a$ satisfies. Once you have it, $F[a] \cong F[x]/(m_{F,a})$ — the ring of polynomial expressions in $a$ *is* the formal polynomial ring modulo exactly the "collapsing" relation Remark 2.16 is warning you about. If you've implemented a computer-algebra normal form or a term-rewriting system with confluence, this is the same idea: a set of expressions modulo a rewrite rule, collapsed to canonical representatives. If $a$ is *transcendental* (satisfies no polynomial relation at all — Chapter 4's vocabulary), no such collapsing ever happens, and $S[a]$ really does behave like the formal polynomial ring, degree-for-degree.

## Where this leads

The ring axioms are the base of every structure the rest of the book builds: **integral domains** (rings with no zero-divisors, the next Topic List article) and **fields** (integral domains where every nonzero element is invertible) are both refinements of *this* definition, not separate ones. The $S[a]$ generation construction reappears immediately in Chapter 4 as the machinery for field extensions ($F[a]$ vs. $F(a)$), and Remark 2.16's degree-collapsing phenomenon is precisely what Chapter 6 formalizes as the minimal polynomial — the single most load-bearing concept connecting field extensions, polynomial factorization, and (in Chapter 7) the algebraic criterion for straightedge-and-compass constructibility.
