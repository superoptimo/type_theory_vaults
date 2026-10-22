---
title: Constructive Real Analysis
book: Homotopy Type Theory — Univalent Foundations of Mathematics
chapters: "Chapter 11 (printed pp. 373–422)"
tags: [homotopy-type-theory, real-numbers, dedekind-reals, cauchy-reals, higher-inductive-inductive-types, constructive-analysis, compactness, surreal-numbers, automated-reasoning]
---

[[book-guidelines|↩ Back to guidelines]]

# Constructive Real Analysis

## 1. Why this chapter exists

The chapter opens by saying that a foundation "worthy of its name must eventually address the construction of real numbers", meaning a complete archimedean ordered field. Constructively, "complete" splits into two inequivalent notions:

- **Cauchy completeness:** every Cauchy sequence has a limit.
- **Dedekind completeness:** every Dedekind cut is a real.

Classically the two coincide, so nobody notices. Without excluded middle or choice, each construction has a known defect:

| Construction | Defect in traditional constructive math |
|---|---|
| Dedekind reals | They need power sets or impredicativity, because a cut is a *subset* of $\mathbb{Q}$. |
| Cauchy reals as a quotient of sequences | Showing the quotient is Cauchy complete requires lifting a sequence of equivalence classes to a sequence of representatives. That uses countable choice. |

The chapter's new contribution is a third route: the Cauchy reals as a **higher inductive-inductive type** (HIIT). It needs neither power sets nor countable choice. It also serves as a showcase for the machinery of Chapters 5–7, which is the main reason the chapter belongs in this book.

The two completions are compared in §11.4. §11.5 shows how compactness splits into three inequivalent notions. §11.6 builds Conway's surreal numbers with the same HIIT technique. The book states that assuming excluded middle and choice recovers standard classical analysis, so nothing here forces constructivism. The constructions work in both settings.

## 2. The rationals $\mathbb{Q}$ (§11.1)

First principles: we need a countable set with decidable equality and order, on which both completions can be built. The book builds it as a set-quotient:

$$\mathbb{Q} :\equiv (\mathbb{Z} \times \mathbb{N}) / \approx, \qquad (u,a) \approx (v,b) :\equiv u(b+1) = v(a+1).$$

The pair $(u,a)$ represents $u/(1+a)$, so the denominator can never be zero. Lowest-terms fractions give canonical representatives. Lemma 6.10.8 then yields a *set* $\mathbb{Q}$ with decidable equality, and the book records that it is also the initial ordered field. $\mathbb{Q}^+ :\equiv \{q : \mathbb{Q} \mid q > 0\}$ denotes positive rationals and appears in every definition below.

## 3. Dedekind reals (§11.2)

### 3.1 The problem it solves and the definition

Idea: identify a real number with the set of rationals below it and the set above it. The book uses **two-sided** cuts because the symmetry is more elegant and works constructively.

A Dedekind cut is a pair of mere predicates $L, U : \mathbb{Q} \to \Omega$ that is:

1. **inhabited:** $\exists q.\, L(q)$ and $\exists r.\, U(r)$
2. **rounded:** $L(q) \Leftrightarrow \exists r.\,(q<r) \wedge L(r)$, and symmetrically for $U$
3. **disjoint:** $\neg(L(q) \wedge U(q))$
4. **located:** $(q<r) \Rightarrow L(q) \vee U(r)$

$$\mathbb{R}_d :\equiv \{(L,U) : (\mathbb{Q}\to\Omega)\times(\mathbb{Q}\to\Omega) \mid \mathsf{isCut}(L,U)\}.$$

Locatedness is the constructive condition. It says there is "no large gap" between $L$ and $U$, and it is what makes the cut behave like a point rather than a fuzzy region. Roundedness makes cuts open, so a cut never contains the point in between.

### 3.2 The universe-size problem and the choice of $\Omega$

A naive translation would use $\mathsf{Prop}_{\mathcal{U}_i}$ for $\Omega$. Then $\mathbb{R}_d$ lives in $\mathcal{U}_{i+1}$, a property of reals in $\mathcal{U}_{i+2}$, and so on. The book avoids this bookkeeping by assuming a single type of propositions $\Omega$, and lists four readings:

1. $\Omega$ is the ambiguous $\mathsf{Prop}$, with universe levels tracked by hand or by a proof assistant.
2. Assume propositional resizing (§3.5).
3. Assume excluded middle for mere propositions, so $\Omega \equiv \mathbf{2}$. This yields the standard classical construction.
4. Take the *minimal* requirement. The cut conditions use only $\wedge$, $\vee$ and $\exists$ over the countable set $\mathbb{Q}$, so $\Omega$ can be the initial $\sigma$-frame, a lattice with countable joins in which binary meets distribute over countable joins. This would itself be a HIIT. The initial $\sigma$-frame cannot be $\mathbf{2}$ without excluded middle.

In all four cases $\Omega$ is a set, and $\mathbb{R}_d$ is a set.

### 3.3 Algebra and order, and why apartness matters

Addition is defined cut-wise, for example $L_{x+y}(q) :\equiv \exists r,s.\, L_x(r) \wedge L_y(s) \wedge q = r+s$. Multiplication is "a bit more cumbersome" and is interval arithmetic in disguise:

$$[a,b]\cdot[c,d] = [\min(ac,ad,bc,bd),\ \max(ac,ad,bc,bd)].$$

The lower cut of $x \cdot y$ says that $q$ lies to the left of $[a,b]\cdot[c,d]$ for some intervals containing $x$ and $y$. The book suggests thinking of an interval $[a,b]$ with $L_x(a)$ and $U_x(b)$ as an *approximation* of $x$.

Order is defined as follows:

- $x \le y :\equiv \forall q.\, L_x(q) \Rightarrow L_y(q)$
- $x < y :\equiv \exists q.\, U_x(q) \wedge L_y(q)$

Linearity $(x<y)\vee(y\le x)$ needs excluded middle. Constructively one gets only **weak linearity** (11.2.3):

$$x<y \Rightarrow (x<z)\vee(z<y).$$

Setting $x \equiv u-\epsilon$ and $y \equiv u+\epsilon$ gives "linearity up to a small numerical error". We can decide $<$ only to finite precision.

The same phenomenon explains the next definition. **Apartness** is $x \mathbin{\#} y :\equiv (x<y)\vee(y<x)$. It implies $\neg(x=y)$. The converse is not provable constructively, and Exercise 11.10 shows that assuming it yields a bit of excluded middle. Theorem 11.2.4 says a real is invertible **iff it is apart from $0$**, not iff it is $\neq 0$.

Definition 11.2.7 packages these properties as an **ordered field**: a commutative ring with unit, lattice structure, $<$ transitive, irreflexive and weakly linear, $\#$ irreflexive, symmetric and cotransitive, and the compatibility laws. It is **archimedean** when $x<y$ implies there merely exists $q$ with $x<q<y$. Theorem 11.2.8 says $\mathbb{R}_d$ is an archimedean ordered field. The book states that theorem without proof.

### 3.4 Completeness, in two senses

**Cauchy completeness.** A Cauchy sequence $x : \mathbb{N}\to\mathbb{Q}$ satisfies
$$\prod_{\epsilon:\mathbb{Q}^+}\ \sum_{n:\mathbb{N}}\ \prod_{m,k\ge n} |x_m - x_k| < \epsilon .$$
The inner $\sum$ is deliberately **not truncated**. The book wants the rate of convergence as data ("an approximation without an error estimate carries little useful information"). By Theorem 2.15.7 this yields a **modulus of convergence** $M : \mathbb{Q}^+ \to \mathbb{N}$. The book then works with **Cauchy approximations**, maps $x : \mathbb{Q}^+ \to \mathbb{R}_d$ satisfying

$$\forall \delta,\epsilon.\ |x_\delta - x_\epsilon| < \delta + \epsilon,$$

whose **limit** is an $\ell$ with $\forall \epsilon,\theta.\ |x_\epsilon - \ell| < \epsilon+\theta$. Theorem 11.2.12 says every Cauchy approximation in $\mathbb{R}_d$ has a limit, and the proof gives *existence*, not mere existence.

**Dedekind completeness.** Theorem 11.2.14 gives the stronger statement that $\mathbb{R}_d$ is **final**: every archimedean ordered field admissible for $\Omega$ embeds into it. Corollary 11.2.16 follows: cuts of $\mathbb{R}_d$ add nothing new.

## 4. The Cauchy reals as a HIIT (§11.3)

### 4.1 The motivating obstruction

The Cauchy reals should be the *free complete metric space on $\mathbb{Q}$*. Section 6.11 showed that [[Higher-Inductive-Types|higher inductive types]] build free gadgets directly, without an explicit normal form, so the book builds $\mathbb{R}_c$ that way. It does so by adding limits and quotienting by coincidence **simultaneously**. That avoids the lifting problem entirely, because there is no quotient step at the end.

There is a circularity to resolve. A "limit" constructor needs the notion of Cauchy sequence of reals, which needs a distance between reals, which would itself be a real. The fix is to define only the relation "$u$ and $v$ are within $\epsilon$":

$$\sim\ :\ \mathbb{Q}^+ \times \mathbb{R}_c \times \mathbb{R}_c \to \mathcal{U}$$

*simultaneously* with $\mathbb{R}_c$. Because $\sim_\epsilon$ is a family indexed by two copies of $\mathbb{R}_c$, this is inductive-inductive and cannot be an ordinary mutual definition.

Remark 11.3.1 explains why the book chooses inductive-inductive rather than inductive-recursive. Higher inductive-recursive definitions are harder to justify in homotopical semantics. More importantly, the inductive-inductive form yields a **more powerful induction principle**, which is needed even for the basic theory.

### 4.2 The definition (Definition 11.3.2)

$\mathbb{R}_c$ has three constructors:

- **rational points:** for $q:\mathbb{Q}$, a real $\mathsf{rat}(q)$.
- **limit points:** for a Cauchy approximation $x:\mathbb{Q}^+\to\mathbb{R}_c$ (meaning $\forall\delta,\epsilon.\ x_\delta \sim_{\delta+\epsilon} x_\epsilon$), a real $\mathsf{lim}(x)$.
- **paths:** if $\forall\epsilon.\ u\sim_\epsilon v$, then a path $\mathsf{eq}_{\mathbb{R}_c}(u,v) : u = v$.

The family $\sim$ has five constructors:

- $\mathsf{rat}(q)\sim_\epsilon\mathsf{rat}(r)$ if $-\epsilon<q-r<\epsilon$;
- $\mathsf{rat}(q)\sim_\epsilon\mathsf{lim}(y)$ if $\mathsf{rat}(q)\sim_{\epsilon-\delta}y_\delta$;
- $\mathsf{lim}(x)\sim_\epsilon\mathsf{rat}(r)$ if $x_\delta\sim_{\epsilon-\delta}\mathsf{rat}(r)$;
- $\mathsf{lim}(x)\sim_\epsilon\mathsf{lim}(y)$ if $x_\delta\sim_{\epsilon-\delta-\eta}y_\eta$;
- propositional truncation: any two witnesses of $u\sim_\epsilon v$ are equal.

The path constructor is the quotient. It says that two reals are *equal* when they are $\epsilon$-close for every $\epsilon$. Because limits and quotient are built together, a sequence of reals needs no lift to representatives.

Proof relevance: strictly $\mathsf{lim}(x,p)$ carries the proof $p$ of the Cauchy condition, and the book suppresses it in notation.

A classical Cauchy sequence $x:\mathbb{N}\to\mathbb{Q}$ with modulus $M$ gives $\mathsf{lim}(\mathsf{rat}\circ x\circ M)$. The book notes that $\sqrt2$, $\pi$ and $e$ arise this way.

### 4.3 Induction and recursion

Simultaneous induction over $(\mathbb{R}_c, \sim)$ takes two families,

$$A:\mathbb{R}_c\to\mathcal{U}, \qquad B:\prod_{x,y:\mathbb{R}_c} A(x)\to A(y)\to\prod_{\epsilon:\mathbb{Q}^+}(x\sim_\epsilon y)\to\mathcal{U},$$

and $B$ must depend on $A(x)$ and $A(y)$. The easiest way to see why is the non-dependent recursion principle, where $B : A \to A \to \mathbb{Q}^+ \to \mathcal{U}$ must mirror the shape of $\sim$. The book writes $B$ as $(x,a)\mathrel{\frown_\epsilon}(y,b)$ and notes it is "a mouthful".

Two special cases do the work in practice:

- **$\mathbb{R}_c$-induction** (take $\frown$ constant at $\mathbf{1}$). Supply $f_q : A(\mathsf{rat}(q))$, a limit case, and the path case. If $A$ is a **mere property**, the path case is automatic, so one proves it for rationals and limits of Cauchy approximations. The book observes that a direct application can only succeed for mere properties, because $u\sim_\epsilon u$ forces any two points of $A(u)$ to be equal.
- **$\sim$-induction** (take $A$ constant at $\mathbf{1}$). It gives inductive generation of the closeness family itself, used for example to prove symmetry, $(u\sim_\epsilon v)=(v\sim_\epsilon u)$ (Lemma 11.3.12).

Results shown in the book's section 11.3.2 include:

- Lemma 11.3.8: $u\sim_\epsilon u$ always.
- Theorem 11.3.9: $\mathbb{R}_c$ is a set.
- Lemma 11.3.10: $\mathsf{lim} : \mathcal{C}\to\mathbb{R}_c$ is surjective, where $\mathcal{C}$ is the type of Cauchy approximations of reals. So $\mathbb{R}_c$ *is* a quotient of Cauchy approximations of **reals**, though the book stresses this is a property, not a valid definition.
- Lemma 11.3.11: a function out of $\mathcal{C}$ into a set that respects coincidence factors uniquely through $\mathsf{lim}$.

### 4.4 Field structure and universal property

Arithmetic is obtained by extending Lipschitz functions $\mathbb{Q}\to\mathbb{R}_c$ (Definition 11.3.14) and by patching. Key results:

- Theorem 11.3.41: the archimedean principle for $\mathbb{R}_c$.
- Theorem 11.3.44: $(u\sim_\epsilon v)\simeq(|u-v|<\mathsf{rat}(\epsilon))$. After this, closeness and the metric agree.
- Theorem 11.3.47: a Cauchy real is invertible iff it is apart from zero.
- Theorem 11.3.48: $\mathbb{R}_c$ is an archimedean ordered field.
- Theorem 11.3.49: every Cauchy approximation in $\mathbb{R}_c$ has a limit.
- Theorem 11.3.50: $\mathbb{R}_c$ **embeds into every Cauchy complete archimedean ordered field**, so it is the *initial* such field.

The chapter's intro states the dual summary: the Dedekind reals are the *final* archimedean ordered field (admissible for $\Omega$), and the Cauchy reals are the *initial* Cauchy-complete archimedean ordered field.

## 5. Comparing the two (§11.4)

Since $\mathbb{R}_c$ is an archimedean ordered field admissible for $\Omega$, Theorem 11.2.14 gives an embedding $\mathbb{R}_c\to\mathbb{R}_d$ fixing $\mathbb{Q}$. In general they need not coincide.

Lemma 11.4.1 gives a sufficient condition: if for every $x:\mathbb{R}_d$ there *merely exists* an **untruncated** locatedness witness

$$c : \prod_{q,r:\mathbb{Q}}(q<r)\to(q<x)+(x<r),$$

then the two coincide. The proof is a bisection. Starting from $(a,b)$ with $a<x<b$, split at the thirds $s,t$ of the current interval and use $c(s,t)$ to pick which side to keep. The interval width shrinks by a factor $2/3$ each step, giving Cauchy sequences $q_n, r_n$ converging to $x$.

Corollary 11.4.3: excluded middle **or** countable choice suffices for $\mathbb{R}_c\simeq\mathbb{R}_d$. With excluded middle the witness is immediate. With countable choice one applies choice to the locatedness statement over $S=\{(q,r)\mid q<r\}\simeq\mathbb{N}$, using $(q<x)\vee(x<r)\ \equiv\ \exists b:\mathbf{2}.\,\dots$.

## 6. Compactness of the interval (§11.5)

Classically equivalent notions bifurcate constructively. The book considers three:

| Notion | Status for $[0,1]$ |
|---|---|
| Metric compactness (complete and totally bounded) | **Holds** (Theorem 11.5.6). |
| Bolzano–Weierstraß (every sequence has a convergent subsequence) | **Implies LPO** (Theorem 11.5.9), so it cannot be proved constructively. |
| Heine–Borel (every open cover has a finite subcover) | Holds under excluded middle for the naive "pointwise" cover (Theorem 11.5.11). Constructively it holds for **inductive covers**. |

**Metric compactness.** A metric space has $\epsilon$-nets $x_1,\dots,x_n$ with $\forall y.\,\exists k\le n.\ d(x_k,y)<\epsilon$. **Totally bounded** requires an $\epsilon$-net for every $\epsilon$ and, again, asks for a pure $\sum$, so one gets a *modulus of total boundedness*. The book states a design rule here: when porting classical metric notions to HoTT, use truncation sparingly, "typically so that we avoid asking for a non-constant map from $\mathbb{R}$ to $\mathbb{Q}$ or $\mathbb{N}$". The correct definition of uniform continuity likewise keeps $\delta$ as a function of $\epsilon$ (Definition 11.5.5). Theorem 11.5.7 then gives a supremum for a uniformly continuous map on a totally bounded space, built from the Cauchy approximation $x_\epsilon :\equiv \max(f(y_0),\dots,f(y_n))$ over an $h(\epsilon)$-net.

**Bolzano–Weierstraß.** The limited principle of omniscience is
$$\prod_{\alpha:\mathbb{N}\to\mathbf{2}}\Big(\sum_n \alpha(n)=1_{\mathbf 2}\Big)+\Big(\prod_n\alpha(n)=0_{\mathbf 2}\Big).$$
Computationally it asks you to decide whether infinitely many values of $\alpha$ are all $0$. The proof of Theorem 11.5.9 builds $x_n$ as $0$ until $\alpha$ first hits $1$, and $1$ afterwards. A convergent subsequence then decides $\alpha$.

**Heine–Borel.** The naive finite-subcover formulation does not work constructively. A *proof-relevant* alternative, the **inductive cover** $\lhd$ (Definition 11.5.13, with roots in formal topology), does. Corollary 11.5.15 says a closed interval is Heine–Borel compact for inductive covers. Theorem 11.5.16 relates the two: an inductive cover is a pointwise cover, and under excluded middle the converse holds. The book's closing remark is that the distinction between them is "not what they cover but in the proofs that they cover".

## 7. Surreal numbers (§11.6)

Conway's surreals are the common generalization of the Dedekind reals and the ordinals. Conway defines one as a pair of sets $\{L \mid R\}$ with every element of $L$ strictly below every element of $R$. The book identifies three obstacles to reading this as an ordinary inductive type:

1. $<$ must be defined simultaneously with the type of surreals ($\Rightarrow$ inductive-inductive). The book defines $<$ and $\le$ separately and mutually inductively, with *positive* definitions, because a negative definition of $<$ would be unacceptable as the hypothesis of a constructor.
2. "Sets of surreals" must be $\mathcal{U}$-small families $L\to\mathsf{No}$, $R\to\mathsf{No}$ indexed by small types, as for the cumulative hierarchy of §10.5. $\mathsf{No}$ then lives in the next universe $\mathcal{U}'$.
3. Equality via $x\le y\wedge y\le x$ would be a quotient, and without choice the same lifting problem arises as for Cauchy reals. It is solved the same way, with a path constructor.

Definition 11.6.1: $\mathsf{No}$ has a cut constructor, taking $x^L, x^R$ with $\forall L,R.\ x^L<x^R$, and a path constructor $\mathsf{eq}_{\mathsf{No}}(x,y):x=y$ for $x\le y\wedge y\le x$. The relation $\le$ has one constructor ($x^L<y$ for all $L$ and $x<y^R$ for all $R$ gives $x\le y$) plus truncation. The relation $<$ has two constructors ($\exists L.\ x\le y^L$ and $\exists R.\ x^R\le y$) plus truncation. These are the book's positive reformulation of Conway's definitions.

## 8. Grounding in code

The snippets below are my own illustrations, not from the book, and were not compiled or run.

### Rust: a Cauchy approximation with a modulus

The essential idea of §11.2.2 and §11.3 is that a real is **a function from precision to a rational approximation, together with a coherence law**. Here the law is checked on samples only. Real code would carry a proof.

```rust
use num_rational::BigRational;

/// A Cauchy approximation: for every eps > 0 yields x_eps with
/// |x_delta - x_eps| < delta + eps (checked here only on samples).
struct CReal {
    approx: Box<dyn Fn(&BigRational) -> BigRational>,
}

impl CReal {
    fn at(&self, eps: &BigRational) -> BigRational {
        (self.approx)(eps)
    }
    fn add(self, other: CReal) -> CReal {
        // x+y at precision eps: ask both for eps/2.
        CReal {
            approx: Box::new(move |eps| {
                let h = eps / BigRational::from_integer(2.into());
                self.at(&h) + other.at(&h)
            }),
        }
    }
}
```

The `eps/2` split is the pattern behind every arithmetic proof in the chapter, for example the $\epsilon/3$ in Lemma 11.3.8. Note the contrast: a Dedekind real is a *predicate* on $\mathbb{Q}$, which is not computable data in general. The Cauchy real keeps its *modulus*, which is.

### Python: the bisection of Lemma 11.4.1

```python
from fractions import Fraction as F

def approximate(located, a, b, steps):
    """located(s, t) -> True if s < x, False if x < t   (the untruncated c).
       Maintains q_n < x < r_n with width (2/3)^n * (b - a)."""
    q, r = F(a), F(b)
    for _ in range(steps):
        s, t = (2*q + r)/3, (q + 2*r)/3
        if located(s, t):      # s < x
            q = s
        else:                  # x < t
            r = t
    return q, r
```

The point of Lemma 11.4.1 is exactly that `located` must be *data*, a function returning a bit, rather than a mere existence statement. That is why countable choice or excluded middle is needed to supply it for an arbitrary Dedekind real.

### Lean

Lean 4's Mathlib defines `Real` as a quotient of Cauchy sequences and uses classical logic freely, so it sits on the "excluded middle and choice" side of the chapter's comparison, where $\mathbb{R}_c\simeq\mathbb{R}_d$. A HIIT like $\mathbb{R}_c$ has no direct counterpart in Lean's kernel, which has quotients but no higher [[Inductive-Types|inductive types]].

```lean
-- Weak linearity (11.2.3) is all one gets constructively:
theorem weak_linearity {α} [LinearOrder α] {x y z : α} (h : x < y) :
    x < z ∨ z < y := by
  rcases lt_or_ge x z with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (lt_of_le_of_lt h1 h)
```

This proof uses `lt_or_ge`, a decidable linear order, which is exactly what $\mathbb{R}_d$ does *not* have constructively. In $\mathbb{R}_d$ the weak form is proved directly from locatedness.

## 9. Synthesis

**Dependencies.** The chapter uses sets and mere propositions (§3), propositional resizing (§3.5), the quotient construction (§6.10), free algebraic structures as HITs (§6.11), the cumulative-hierarchy pattern (§10.5), and the fact that "sets" behave as expected (§10.1). It also uses inductive-inductive types (§5.7). Nothing later in the book depends on it.

```
Q (set-quotient) ──► Dedekind cuts (Ω, locatedness)   ──► final archimedean field
        │
        └──► HIIT (R_c, ~_ε) with eq path constructor ──► initial Cauchy-complete field
                         │
         excluded middle or countable choice
                         ▼
                   R_c ≃ R_d ──► compactness (metric ✓ / BW ⇒ LPO / HB via inductive covers)

          same HIIT trick ──► surreals No
```

**Bearing on the learning goals.** The topic is tagged `automated-reasoning`. The connection is real but indirect, and the book itself does not discuss solvers or proof search here. The following points are my own readings, not claims the book makes:

- **Proof-relevant, computable data.** The chapter's recurring rule is to keep $\sum$ untruncated where a modulus is wanted: modulus of convergence, of total boundedness, of uniform continuity. This is the same design question as which parts of a verification certificate must be kept as data and which may be erased as propositions. It bears on the `automated-reasoning` thread of *proof certificates* and *trusted kernels*.
- **Decidability boundaries.** Weak linearity, apartness versus $\neq$, and LPO mark where decision procedures for real constraints stop being constructive. A solver that returns a *witness* corresponds to the untruncated $c$ of Lemma 11.4.1. A solver that only returns "satisfiable" corresponds to the mere existence.
- **Interval arithmetic.** Dedekind multiplication via interval hulls is the same shape as the interval abstract domain. This is a loose analogy to *abstract interpretation*, which is outside this topic's tag. It is mentioned only because the book itself points to approximating a real by an interval (Exercise 11.4), and it is not a load-bearing prerequisite.

The topic is **not** a prerequisite for the elaborator's `isDefEq` or for the trusted kernel. The HIIT definition of $\mathbb{R}_c$ is a stress test of a type theory with higher inductive types, which a Lean-style kernel does not provide.
