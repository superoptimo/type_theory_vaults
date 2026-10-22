---
title: The Homotopical Interpretation of Types
source: "Homotopy Type Theory: Univalent Foundations of Mathematics (The Univalent Foundations Program, 2013)"
chapters: "Introduction (pp. 1–14); Chapter 2, §§2.1–2.8 (pp. 59–86)"
tags: [hott, type-theory, identity-types, higher-groupoids, transport, type-theory-focus]
---

[[book-guidelines|↩ Back to guidelines]]

# The Homotopical Interpretation of Types

**Focus Area:** `type-theory`. It touches `automated-reasoning` through unification and definitional equality. Both are explained in the closing synthesis.

## 1. The problem this solves

In ordinary mathematics, "$a = b$" is a *proposition*: it is either true or false, and a proof of it carries no information beyond the fact that it exists. Type theory with proof-relevant identity types breaks that assumption. A term $p : a =_A b$ is a *thing* that you build, and there can be many different such $p$ for the same $a$ and $b$.

The book's answer is to stop fighting this. It reads the identity type as the type of **paths** from $a$ to $b$ in a space:

| Type theory | Homotopy theory | Higher category theory |
|---|---|---|
| type $A$ | space | $\infty$-groupoid |
| term $a : A$ | point | object |
| $p : a = b$ | path from $a$ to $b$ | morphism |
| $r : p = q$ | homotopy between paths (2-path) | 2-morphism |
| $f : A \to B$ | continuous map | functor |
| family $P : A \to \mathcal{U}$ | fibration | fibration |

This is a **synthetic** description. In classical homotopy theory (an *analytic* one) a space is a set of points with a topology, and a path is a continuous function out of $[0,1]$. Here points, paths, and paths between paths are primitive notions. The book stresses that "space" is only a metaphor: there is no open set and no convergence. Only the homotopical notions are available, so "$\infty$-groupoid" is the more accurate word.

The important fact is that **all of the groupoid structure is derived from a single rule**, the induction principle for identity types. Nothing about it is added as an axiom.

## 2. The one rule: path induction

For a type family $D : \prod_{x,y:A} (x = y) \to \mathcal{U}$ and a function $d : \prod_{a:A} D(a,a,\mathsf{refl}_a)$, there is
$$\mathsf{ind}_{=_A}(D,d) : \prod_{x,y:A}\prod_{p:x=y} D(x,y,p), \qquad \mathsf{ind}_{=_A}(D,d,a,a,\mathsf{refl}_a) \equiv d(a). \tag{2.0.1}$$

Informally: to construct something that depends on a path $p : x = y$, it suffices to construct it when $y$ is judgmentally $x$ and $p$ is $\mathsf{refl}_x$. The book writes "by induction, it suffices to assume…" for this step.

A programmer's way to read it: $\mathsf{ind}_=$ is an eliminator (a dependent `match`) on an inductive family with exactly one constructor, $\mathsf{refl}$. The index $y$ is free, and that is what makes it more powerful than ordinary equality elimination. Lean's `Eq.rec` (or `match h with | rfl => …`) is the same principle. The pattern-matching compiler unifies $y$ with $x$ before it enters the `rfl` case.

```lean
-- Lemma 2.1.1: inverse of a path. One case, the reflexivity case.
def inv {A : Type u} {x y : A} : x = y → y = x
  | rfl => rfl

-- Lemma 2.1.2: concatenation. (The book does induction on BOTH paths.)
def concat {A : Type u} {x y z : A} : x = y → y = z → x = z
  | rfl, rfl => rfl
```

```rust
// Rust cannot express dependent elimination, but the *shape* of the data can be
// modelled for a checker: a path is a witness term, and `refl` is its only
// canonical form. A kernel normalises J-applications on `Refl` and gets stuck otherwise.
enum Term {
    Refl(Box<Term>),                       // refl_x
    J { motive: Box<Term>, base: Box<Term>, // ind_= (D, d, x, y, p)
        x: Box<Term>, y: Box<Term>, p: Box<Term> },
    /* ... */
}
fn reduce_j(t: &Term) -> Option<Term> {
    // ind_=(D, d, a, a, refl_a) ≡ d(a)      -- the computation rule (2.0.1)
    if let Term::J { base, p, .. } = t {
        if let Term::Refl(a) = &**p { return Some(app(base, a)); }
    }
    None
}
fn app(_f: &Term, _a: &Term) -> Term { unimplemented!() } // beta-application, omitted
```

```python
# Python analogue: J is a fold over a one-constructor family. The "motive" D
# is what makes it *dependent*; plain Python cannot check that d has the right type.
def J(D, d, x, y, p):
    assert p == ("refl", x) and x == y   # only canonical path: refl
    return d(x)                          # computation rule
```

### Why the book proves things twice

The book gives each early lemma two proofs. The "first proof" spells out the motive $D$. The "second proof" is the informal *"by induction, assume $p \equiv \mathsf{refl}$"* version. Take the first lemma.

- **Lemma 2.1.1 (inverse).** Take $D(x,y,p) :\equiv (y = x)$ and $d :\equiv \lambda x.\,\mathsf{refl}_x$. This gives $p^{-1}$ with $\mathsf{refl}_x^{-1} \equiv \mathsf{refl}_x$.
- **Lemma 2.1.2 (concatenation).** Write $p \cdot q$ for the composite of $p : x = y$ and $q : y = z$. The book writes it in diagrammatic order, the reverse of $g \circ f$.

The second lemma raises a point that matters for implementers. Concatenation could be defined by induction on $p$ only, on $q$ only, or on both. These yield three definitionally *different* functions of the same type. Only the double induction gives the symmetric rule $\mathsf{refl}_x \cdot \mathsf{refl}_x \equiv \mathsf{refl}_x$. Induction on $p$ alone would give $\mathsf{refl}_y \cdot q \equiv q$, and induction on $q$ alone would give $p \cdot \mathsf{refl}_y \equiv p$. The three are propositionally equal (Exercise 2.1) but not judgmentally equal. This is **proof relevance**: the definition you pick determines which reductions the checker performs for free. Formalizers often prefer the asymmetric versions for that reason. The book prefers the symmetric one for robust informal proofs, and says plainly that this is a stylistic choice.

## 3. Types are higher groupoids (§2.1)

The three operations $\mathsf{refl}$, $(-)^{-1}$ and $\cdot$ correspond to a constant path, an inverse and a composition. In set theory, reflexivity, symmetry and transitivity are bare *properties* of equality. Here they are *structure*, so we must ask whether the structure obeys the groupoid laws.

**Lemma 2.1.4.** For $p : x = y$, $q : y = z$, $r : z = w$:

1. $p = p \cdot \mathsf{refl}_y$ and $p = \mathsf{refl}_x \cdot p$.
2. $p^{-1} \cdot p = \mathsf{refl}_y$ and $p \cdot p^{-1} = \mathsf{refl}_x$.
3. $(p^{-1})^{-1} = p$.
4. $p \cdot (q \cdot r) = (p \cdot q) \cdot r$.

These are not judgmental equalities. They are *elements of identity types of identity types*: paths between paths, that is, homotopies. Topologically, $p \cdot p^{-1}$ is not literally the constant path. It is homotopic to it. Each proof is a single path induction that reduces to the case $p \equiv q \equiv r \equiv \mathsf{refl}$, where both sides reduce to $\mathsf{refl}$. (Here is where the choice of the symmetric concatenation pays off: with a one-sided definition some of these cases would require more work.)

**Higher structure.** The laws (i)–(iv) have their own coherence laws, which are higher paths, and so on to infinity. The book never makes the whole tower explicit. It says that the entire structure can be derived from the inductive property of identity types, "so we can make explicit as much or as little of it as we need". In practice, the working notions are:

- **$n$-paths:** $r : p =_{(x=y)} q$ is a 2-path, $s : r = r'$ a 3-path, and so on.
- **Pointed types and loop spaces:** $(A,a)$ with $a : A$. $\Omega(A,a) :\equiv ((a =_A a), \mathsf{refl}_a)$, and $\Omega^{n+1}(A,a) :\equiv \Omega^n(\Omega(A,a))$. In set theory $a = a$ is uninteresting. In homotopy theory loops carry a "higher group" structure.
- **Eckmann–Hilton (Theorem 2.1.6):** composition on $\Omega^2(A)$ is commutative, $\alpha \cdot \beta = \beta \cdot \alpha$. The proof introduces *whiskering* ($\alpha \mathbin{\triangleright_r} r$ and $q \mathbin{\triangleleft_l} \beta$) and *horizontal composition* $\alpha \star \beta :\equiv (\alpha \triangleright_r r) \cdot (q \triangleleft_l \beta)$. It then compares two ways of defining $\star$ and shows both equal $\alpha \cdot \beta$ and $\beta \cdot \alpha$ respectively. This is why higher homotopy groups are abelian (used in Chapter 8).

```lean
-- Lemma 2.1.4(iv), the associativity path, by induction on all three paths.
theorem assoc {A : Type u} {x y z w : A} (p : x = y) (q : y = z) (r : z = w) :
    (concat p (concat q r)) = concat (concat p q) r := by
  cases p; cases q; cases r; rfl
-- Note: in Lean, Eq lives in Prop (proof-irrelevant), so this is TRIVIAL there.
-- HoTT's Id is a Type, with no UIP: the same statement is a genuine path between paths.
```

That last comment is the main trap when moving between Lean 4 and the book. Lean's `Eq` is in `Prop` with definitional proof irrelevance, so the entire higher-groupoid structure collapses. HoTT's identity type is proof-relevant and does not validate uniqueness of identity proofs. The grounding examples in this article are therefore illustrative of the *shape* of the proofs, not of HoTT's behavior itself. Lean 4 without UIP (or Agda `--without-K`, or Rocq/Coq with the HoTT library) behaves like the book.

## 4. Functions are functors (§2.2)

**Lemma 2.2.1.** For $f : A \to B$ there is $\mathsf{ap}_f : (x =_A y) \to (f(x) =_B f(y))$ with $\mathsf{ap}_f(\mathsf{refl}_x) \equiv \mathsf{refl}_{f(x)}$. Every function "respects equality", or topologically, "is continuous".

**Lemma 2.2.2 (functoriality).**
$$\mathsf{ap}_f(p \cdot q) = \mathsf{ap}_f(p)\cdot\mathsf{ap}_f(q), \quad \mathsf{ap}_f(p^{-1}) = \mathsf{ap}_f(p)^{-1}, \quad \mathsf{ap}_g(\mathsf{ap}_f(p)) = \mathsf{ap}_{g\circ f}(p), \quad \mathsf{ap}_{\mathsf{id}_A}(p) = p.$$

The book often abbreviates $\mathsf{ap}_f(p)$ as $f(p)$, the same overloading category theory uses for a functor on objects and on morphisms.

```lean
def ap {A B : Type u} (f : A → B) {x y : A} : x = y → f x = f y
  | rfl => rfl   -- Lean's `congrArg`
```

## 5. Type families are fibrations (§2.3)

A dependent function $f : \prod_{x:A} B(x)$ has a problem: given $p : x = y$, the values $f(x) : B(x)$ and $f(y) : B(y)$ live in different types, so "$f(x) = f(y)$" is ill-typed. The path $p$ must itself supply a way to move between $B(x)$ and $B(y)$.

- **Transport (Lemma 2.3.1).** $p_* :\equiv \mathsf{transport}^P(p,-) : P(x) \to P(y)$, defined by $D(x,y,p) :\equiv P(x) \to P(y)$ and $d :\equiv \lambda x.\,\mathsf{id}_{P(x)}$. Therefore $(\mathsf{refl}_x)_* \equiv \mathsf{id}$. This is "indiscernibility of identicals" with a computation rule.
- **Path lifting (Lemma 2.3.2).** $\mathsf{lift}(u,p) : (x,u) = (y, p_*(u))$ in $\sum_{x:A} P(x)$, with $\mathsf{pr}_1(\mathsf{lift}(u,p)) = p$. The fibration picture: base $A$, fiber $P(x)$ over $x$, and total space $\sum_{x:A}P(x)$. Classical fibrations only *have* path liftings. A type family comes with a *specified* lifting function, which fits constructive mathematics, and since every function is automatically continuous, the liftings are automatically chosen continuously.
- **Dependent map (Lemma 2.3.4).** $\mathsf{apd}_f : \prod_{p:x=y} \bigl(p_*(f(x)) =_{P(y)} f(y)\bigr)$. The type $p_*(u) = v$ is the book's definition of "a path from $u$ to $v$ lying over $p$" (a *dependent path*). Dependent paths become central for [[Higher-Inductive-Types|higher inductive types]] in Chapter 6.
- **Relating $\mathsf{ap}$ and $\mathsf{apd}$.** For a constant family $P(x) :\equiv B$, Lemma 2.3.5 gives $\mathsf{transportconst}^B_p(b) : p_*(b) = b$, and Lemma 2.3.8 says
$$\mathsf{apd}_f(p) = \mathsf{transportconst}^B_p(f(x)) \cdot \mathsf{ap}_f(p).$$
- **Transport laws.** $q_*(p_*(u)) = (p\cdot q)_*(u)$ (2.3.9); $\mathsf{transport}^{P\circ f}(p,u) = \mathsf{transport}^P(\mathsf{ap}_f(p),u)$ (2.3.10); and naturality in $P$ (2.3.11).

```lean
def transport {A : Type u} (P : A → Sort v) {x y : A} : x = y → P x → P y
  | rfl, u => u          -- Lean's `Eq.mpr`/`▸`

-- Remark 2.7.1's caution, in code: (x, u) = (x, v) does NOT give u = v;
-- only ∃ p : x = x, transport P p u = v.
```

```rust
// A dependent pair as a Rust struct: the second component's TYPE depends on the first.
// Rust can only fake this with a type-level index; a checker represents it as Sigma.
struct Sigma<A, P: Fn(&A) -> Ty> { fst: A, snd: Val /* : P(fst) */ , _p: P }
// "transport" = coercing `snd` from P(x) to P(y) along a path p : x = y.
```

## 6. Homotopies and equivalences (§2.4)

- **Homotopy.** For $f,g : \prod_{x:A}P(x)$, define $f \sim g :\equiv \prod_{x:A} (f(x) = g(x))$. This is *not* the same as $f = g$. §2.9 introduces an axiom that makes them equivalent. Homotopy is an equivalence relation (2.4.2).
- **Naturality (Lemma 2.4.3).** For $H : f \sim g$ and $p : x = y$, $H(x) \cdot g(p) = f(p) \cdot H(y)$. By induction on $p$ the case $\mathsf{refl}$ is trivial. Homotopies are automatically natural transformations. Corollary 2.4.4: $H(f(x)) = f(H(x))$ for $H : f \sim \mathsf{id}_A$.
- **Quasi-inverse.** $\mathsf{qinv}(f) :\equiv \sum_{g:B\to A}(f\circ g \sim \mathsf{id}_B)\times(g\circ f \sim \mathsf{id}_A)$. The naive notion of "isomorphism" is *badly behaved* here: one function $f$ can have several unequal quasi-inverse triples (this is the reason higher category theory uses adjoint equivalences).
- **What replaces it.** The book reserves "equivalence" for a predicate $\mathsf{isequiv}(f)$ satisfying: (i) $\mathsf{qinv}(f) \to \mathsf{isequiv}(f)$, (ii) $\mathsf{isequiv}(f) \to \mathsf{qinv}(f)$, (iii) any two inhabitants of $\mathsf{isequiv}(f)$ are equal. One candidate shown here is the bi-invertible version
$$\mathsf{isequiv}(f) :\equiv \Bigl(\sum_{g:B\to A}(f\circ g\sim \mathsf{id}_B)\Bigr)\times\Bigl(\sum_{h:B\to A}(h\circ f\sim\mathsf{id}_A)\Bigr).$$
  Property (iii) is only proved in §4.3 (it needs the identity types of $\times$ and $\Sigma$ from §§2.6–2.7). Then $(A\simeq B) :\equiv \sum_{f:A\to B}\mathsf{isequiv}(f)$, and $\simeq$ is an equivalence relation on $\mathcal{U}$ (Lemma 2.4.12). In practice, you prove $f$ is an equivalence by exhibiting a quasi-inverse.
- Examples: concatenation $(p\cdot -)$ has quasi-inverse $(p^{-1}\cdot -)$, and $\mathsf{transport}^P(p,-)$ has quasi-inverse $\mathsf{transport}^P(p^{-1},-)$.

## 7. Paths in each type former (§§2.5–2.8)

The recipe of §2.5 is the heart of the chapter: **for most types, $x =_A y$ can be characterized, up to equivalence, by the data that built $A$.** The same applies to transport and to $\mathsf{ap}$. Because identity types are defined uniformly by induction, these characterizations are *theorems*, not definitional equalities.

**Cartesian products (§2.6).** The map $(x = y) \to (\mathsf{pr}_1 x = \mathsf{pr}_1 y)\times(\mathsf{pr}_2 x=\mathsf{pr}_2 y)$ is an equivalence (Theorem 2.6.2). Its inverse is $\mathsf{pair}^=$. The book reads this as an *introduction rule* for paths ($\mathsf{pair}^=$), with $\mathsf{ap}_{\mathsf{pr}_i}$ as *eliminators*, plus propositional computation rules and uniqueness principle:
$$\mathsf{ap}_{\mathsf{pr}_1}(\mathsf{pair}^=(p,q)) = p,\qquad r = \mathsf{pair}^=(\mathsf{ap}_{\mathsf{pr}_1}(r),\mathsf{ap}_{\mathsf{pr}_2}(r)).$$
Reflexivity, inverses and composition act componentwise. Transport in $A\times B$ is componentwise (2.6.4). Order matters in the proof: induction on the path first, then on the pairs.

**$\Sigma$-types (§2.7).** A path in the total space is a path in the base *together with a path lying over it*:
$$(w = w') \;\simeq\; \sum_{p : \mathsf{pr}_1(w)=\mathsf{pr}_1(w')} p_*(\mathsf{pr}_2(w)) = \mathsf{pr}_2(w'). \tag{Theorem 2.7.2}$$
Consequences: $z = (\mathsf{pr}_1 z,\mathsf{pr}_2 z)$; path lifting is $\mathsf{lift}(u,p) = \mathsf{pair}^=(p,\mathsf{refl}_{p_*(u)})$; and transport in $x\mapsto\sum_{u:P(x)}Q(x,u)$ is $p_*(u,z) = (p_*(u),\,\mathsf{pair}^=(p,\mathsf{refl}_{p_*(u)})_*(z))$ (2.7.4). **Remark 2.7.1:** from $(x,u)=(x,v)$ you can only conclude $\exists p : x=x$ with $p_*(u)=v$, not $u=v$. The book calls this "a well-known source of confusion for newcomers".

**Unit type (§2.8).** $(x = y) \simeq \mathbf{1}$ (Theorem 2.8.1). The proof has a trap: do not induct on $x,y : \mathbf{1}$ first, since $\star = \star$ then blocks path induction. Keep $x,y$ general and reduce to $\star$ "at the last moment". Consequently any two elements of $\mathbf{1}$ are equal.

**Where the recipe stops working.** §2.5 states that the existing rules are not sufficient for $\Pi$-types and universes, which require axioms: function extensionality (§2.9) and univalence (§2.10). Those are outside this article's scope; they are covered by the "[[Equivalences-and-Univalence|Equivalences and Univalence]]" topic. Also, most nontrivial higher [[Inductive-Types|inductive types]] cannot be characterized by induction on type construction. The identity types of $\mathbb{S}^n$ amount to computing homotopy groups of spheres.

## 8. Synthesis: where this sits in the book, and what it means for the project

**Dependencies.** The material above depends on: judgments and definitional equality (Ch. 1.1), $\Pi$ and $\Sigma$ types, and the *induction principle for identity types* (§1.12). It underlies: equivalences (Ch. 4), the encode–decode method used for $\mathbb{N}$ and coproducts (§§2.12–2.13), higher inductive types (Ch. 6, which use dependent paths and $\mathsf{apd}$), and all of Part II.

```
 path induction (§1.12)
      │
      ├── refl, ⁻¹, ·  ──► groupoid laws (2.1.4) ──► Ω^n, Eckmann–Hilton
      ├── ap_f  ─────────► functoriality (2.2.2)
      ├── transport ─────► lift, apd (2.3) ──► dependent paths ──► HITs (Ch. 6)
      ├── homotopy ~ ────► naturality, qinv / isequiv ──► Ch. 4
      └── pair⁼, Σ-paths ► characterizations of = per type former (2.6–2.8)
                                   │
                                   └──► need axioms for Π, 𝒰: funext, univalence
```

**Connections to the standing project** (tags: `type-theory`, `automated-reasoning`):

- **Definitional equality is the load-bearing prerequisite.** Every proof in this section is "reduce to $\mathsf{refl}$, then both sides *compute* to the same thing". That uses judgmental equality (e.g. $\mathsf{refl}^{-1}\equiv\mathsf{refl}$, $(\mathsf{refl}_x)_*\equiv\mathsf{id}$). In a kernel, this is `isDefEq` plus the iota rule for the eliminator $J$. Choosing the *definition* of concatenation (one-sided versus two-sided induction) changes which computation rules the kernel validates. For an implementer this is a real trusted-computing-base design decision, not just a stylistic one.
- **Unification and elaboration.** Path induction requires the motive $D$ and the endpoints to be *unified* with the goal. A Lean-style `cases`/`match` on `h : x = y` must solve $y := x$ by unification before reducing. Implicit arguments of $\mathsf{ap}$, $\mathsf{transport}$ and $\mathsf{apd}$ ($A$, $x$, $y$, $P$) are inferred in the book "from context", which in an elaborator means metavariable instantiation, with $P$ as a higher-order pattern unification problem (Miller patterns $?P\;x$). The book's own remark that the transport family $P$ must sometimes be written $\mathsf{transport}^P$ is exactly the failure mode where unification has no unique solution.
- **Substitution and context plumbing.** Transport is substitution made first-class: $p_*$ moves a term across the substitution $x\mapsto y$ in a type. Dependent paths and the $\Sigma$-path characterization $(p_*(\mathsf{pr}_2 w) = \mathsf{pr}_2 w')$ are what make well-typed equality statements in dependent contexts possible. This is the same plumbing that dependent-subtyping and refinement checking need (a refinement $\{x : A \mid \phi(x)\}$ is a $\Sigma$-type over a family $\phi$, and equality of refined values *is* the $\Sigma$-path characterization with a proof-relevant second component).
- **Proof-relevance versus refinement types.** In a refinement-type compiler, one normally wants the second component of a refined value to be *proof-irrelevant* (erased). The HoTT view explains precisely when this is justified: when the predicate is a *mere proposition* (Chapter 3). Remark 2.7.1 shows what goes wrong otherwise: equality of $(x,u)$ and $(x,v)$ does not reduce to equality of $u$ and $v$.
- **Not directly relevant.** The homotopical/topological reading (fibrations, loop spaces, Eckmann–Hilton) has no direct counterpart in the compiler or prover targets, and is best read as the semantic motivation for why the rules look as they do. No connection to `sat-smt-csp` or `static-analysis` is forced here.
