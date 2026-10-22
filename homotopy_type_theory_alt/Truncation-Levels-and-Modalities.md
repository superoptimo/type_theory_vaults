---
title: Truncation Levels and Modalities
source: Homotopy Type Theory — Univalent Foundations of Mathematics (14_homotopy_type_theory)
chapters: "Chapter 7, §§7.1–7.7 (printed pp. 221–252); background from §3.1, §3.11, §6.9"
focus-areas: [type-theory]
tags: [hott, n-types, truncation, connectedness, factorization-system, modality, type-theory]
---

[[book-guidelines|↩ Back to guidelines]]

# Truncation Levels and Modalities

## 1. Why this chapter exists

In ordinary programming a type is just a collection of values, and "are these two values equal?" is a yes/no question. In HoTT, equality $x =_A y$ is itself a type, so it can have *many* inhabitants (many distinct proofs), and those proofs can themselves be equal in many ways, and so on forever. That tower of identifications is the "homotopy" of the type.

Most types we care about don't need the whole tower. A type of booleans has trivial higher structure. A proposition has none at all. A type of groups has structure up to dimension 1. We need a way to say, *inside the theory*, "this type has no interesting structure above dimension $n$", and a way to *force* a type to have that property (a "best approximation" that forgets everything above $n$). Chapter 7 does both, then notices that the machinery is much more general than the $n$-indexed family and abstracts it into **modalities**.

Three questions drive the chapter:

1. What does it mean for a type to be an **$n$-type** (truncated), and which constructions preserve it? (§7.1–7.2)
2. How do we universally **truncate** an arbitrary type to an $n$-type, and what are its path spaces? (§7.3–7.4)
3. What is the dual notion of **connectedness**, why do connected and truncated *maps* split every function uniquely, and what is the general pattern behind all of it? (§7.5–7.7)

## 2. $n$-types: defining "no structure above dimension $n$" (§7.1)

The definition is recursive on $n \ge -2$ (the chapter starts two levels below zero on purpose):

$$
\mathsf{is\text{-}}n\mathsf{\text{-}type}(X) :\equiv
\begin{cases}
\mathsf{isContr}(X) & n = -2,\\
\prod_{x,y:X}\ \mathsf{is\text{-}}n'\mathsf{\text{-}type}(x =_X y) & n = n'+1.
\end{cases}
$$

Read it as: a $(-2)$-type is contractible (exactly one point up to identification); an $(n+1)$-type is one whose identity types are all $n$-types. So the levels are:

| $n$ | name | meaning |
|---|---|---|
| $-2$ | contractible | one point, all paths trivial |
| $-1$ | mere proposition | at most one proof |
| $0$ | set | paths exist but are unique (UIP) |
| $1$ | 1-type (groupoid) | paths may be nontrivial; paths between paths are trivial |

(Example 7.1.3: $(-1)$-types are mere propositions by Lemma 3.11.10, hence 0-types are sets.) The book notes it has not yet shown that types *fail* to be $n$-types; it later proves $\mathbb{S}^{n+1}$ is not an $n$-type (Chapter 8) and exhibits a type that is not an $n$-type for any finite $n$ (§8.8).

### Closure properties (what the type checker "gets for free")

The key engineering fact is that being an $n$-type is stable under the standard constructors. All are proved by induction on $n$ with $n=-2$ as the base case:

- **Retracts** (Thm 7.1.4): if $p : X \to Y$ is a retraction and $X$ is an $n$-type, so is $Y$. The inductive step shows $y = y'$ is a retract of $s(y) = s(y')$ via $\mathsf{ap}_s$ and $t(q) :\equiv \epsilon_y^{-1} \cdot p(q) \cdot \epsilon_{y'}$. Corollary 7.1.5: stable under equivalence $X \simeq Y$.
- **Embeddings** (Thm 7.1.6): if $f : X \to Y$ is an embedding and $Y$ is an $n$-type with $n \ge -1$, so is $X$. This *fails* at $n=-2$: $\mathbf{0} \to \mathbf{1}$ is an embedding, $\mathbf{1}$ is contractible, $\mathbf{0}$ is not.
- **Cumulativity** (Thm 7.1.7): every $n$-type is an $(n+1)$-type.
- **$\Sigma$-types** (Thm 7.1.8): $A$ an $n$-type and each $B(a)$ an $n$-type implies $\sum_{x:A} B(x)$ is. The inductive step uses the path characterization $((a_1,b_1) = (a_2,b_2)) \simeq \sum_{p:a_1=a_2} (p_*(b_1) =_{B(a_2)} b_2)$ from Thm 2.7.2. Special cases: $A \times B$, and all pullbacks, so $n$-types are closed under all limits.
- **$\Pi$-types** (Thm 7.1.9): if every $B(a)$ is an $n$-type, so is $\prod_{x:A} B(x)$; the step uses function extensionality. In particular $A \to B$ is an $n$-type when $B$ is.
- **The predicate itself is a proposition** (Thm 7.1.10): $\mathsf{is\text{-}}n\mathsf{\text{-}type}(X)$ is a mere proposition for every $n$, so it is safe to treat as a *property*, not extra data. This generalizes $\mathsf{isSet}$ and $\mathsf{isProp}$ being propositions.
- **The universe of $n$-types** $n\text{-}\mathsf{Type} :\equiv \sum_{X:\mathcal{U}} \mathsf{is\text{-}}n\mathsf{\text{-}type}(X)$ is an $(n+1)$-type (Thm 7.1.11), with $\mathsf{Prop} :\equiv (-1)\text{-}\mathsf{Type}$ and $\mathsf{Set} :\equiv 0\text{-}\mathsf{Type}$. Because the predicate is a proposition, $((X,p) = (X',p')) \simeq (X \simeq X')$ (using univalence).

**Grounding.** In a proof assistant this is the difference between data and proof: a *property* of a term is a proposition-valued predicate, so storing it cannot change the term's identity.

```lean
-- Lean 4: Prop is the (definitionally) (-1)-truncated sublanguage.
-- Subsingleton is "is a mere proposition" as a typeclass; it is itself a Prop.
#check @Subsingleton        -- Subsingleton : Sort u → Prop
-- Nonempty is the propositional truncation ‖A‖ of a type:
example (A : Type) (a : A) : Nonempty A := ⟨a⟩
```

Lean differs from HoTT here: `Prop` is proof-irrelevant *by definition* (every `Prop` is a $(-1)$-type judgmentally), whereas in HoTT $(-1)$-ness is a *theorem-level property* that has to be tracked and proved.

```python
# Python analogy (illustrative only): a "level" is a property you can check
# on a finite model, and closure under products is the reason it composes.
def is_prop(xs):            # (-1)-type: at most one element
    return len(xs) <= 1
def is_set_of_paths(paths): # the idea behind the 0-type check: no two distinct proofs
    return len(paths) <= 1  # applied to every Eq(x, y)
```

## 3. Uniqueness of identity proofs, Axiom K and Hedberg (§7.2)

"$X$ is a set" means $\prod_{x,y:X}\prod_{p,q:x=y} p = q$. In conventional type theory this is called **uniqueness of identity proofs (UIP)**. Streicher's **Axiom K** says $\prod_{x:X}\prod_{p : x = x} p = \mathsf{refl}_x$.

- **Thm 7.2.1:** $X$ is a set iff $X$ satisfies Axiom K. (K is a special case of UIP; conversely, induction on $q$ reduces UIP to K.) The book stresses that **UIP and K are not axioms here**. They are properties a particular type may or may not have, and they are equivalent to being a 0-type. Not every type is a set (Example 3.1.9).
- **Thm 7.2.2:** if $R$ is a reflexive *mere* relation implying identity, then $X$ is a set and $R(x,y) \simeq (x =_X y)$. Two proofs are given: one via $\mathsf{apd}$ and cancellation to derive K, one via showing $f$ induces an equivalence of total spaces $\sum_y R(x,y) \simeq \sum_y (x=y)$ (the latter contractible).
- **Cor 7.2.3:** if $\neg\neg(x=y) \to (x=y)$ for all $x,y$, then $X$ is a set.
- **Lemma 7.2.4:** $(A + \neg A) \to (\neg\neg A \to A)$.
- **Thm 7.2.5 (Hedberg):** *decidable equality implies set.* This is the only place decidability buys homotopical simplicity. Example: $\mathbb{N}$ has decidable equality (Thm 7.2.6), hence is a set.
- The book connects this to Corollary 3.2.7: $\mathsf{LEM}_\infty$ would give every type decidable equality, hence every type a set, which is false. The consistent $\mathsf{LEM}$ gives only *merely* decidable equality $\prod_{a,b}(\|a=b\| + \neg\|a=b\|)$.
- **Thm 7.2.7:** for $n \ge -1$, $X$ is an $(n+1)$-type iff $\Omega(X,x)$ is an $n$-type for all $x$. **Thm 7.2.9** generalizes K: for $n \ge -1$, $A$ is an $n$-type iff $\Omega^{n+1}(A,a)$ is contractible for all $a$.

```rust
// Rust: Hedberg in spirit. A type with a total decision procedure for equality
// is a "set": equality proofs carry no extra information, so we can erase them.
trait DecEq: Sized {
    fn dec_eq(a: &Self, b: &Self) -> bool; // total, computable
}
// Because dec_eq is a *function to bool*, "a == b" is witnessed by at most one thing.
// That is exactly why Hedberg collapses the path space to a proposition.
```

## 4. Truncations: the universal $n$-type approximation (§7.3)

Given any $A$, we want the "best" $n$-type under it. Theorem 7.2.9 says $A$ is an $n$-type iff $\Omega^{n+1}(A,a)$ is contractible, and $\Omega^{n+1}(A,a) \simeq \mathrm{Map}_*(\mathbb{S}^{n+1}, (A,a))$ (Lemma 6.5.4). Contractibility of such a mapping space can be *forced with path constructors*. So for $n \ge -1$, $\|A\|_n$ is the higher inductive type (using the hub-and-spoke trick of §6.7) generated by:

- $|{-}|_n : A \to \|A\|_n$,
- for each $r : \mathbb{S}^{n+1} \to \|A\|_n$, a hub point $h(r) : \|A\|_n$,
- for each such $r$ and each $x : \mathbb{S}^{n+1}$, a spoke path $s_r(x) : r(x) = h(r)$.

(For $n=-2$ the construction fails; define $\|A\|_{-2} :\equiv \mathbf{1}$.)

- **Lemma 7.3.1:** $\|A\|_n$ is an $n$-type. The center of contraction of $\mathrm{Map}_*(\mathbb{S}^{n+1},(\|A\|_n,b))$ is the constant map $c_b$; any other $r$ is joined to it through $s_r(x) \cdot s_r(\mathsf{base})^{-1} \cdot p$.
- **Thm 7.3.2 (induction):** for $P : \|A\|_n \to \mathcal{U}$ with every $P(x)$ an $n$-type and $g : \prod_{a:A} P(|a|_n)$, there is a section $f$ with $f(|a|_n) :\equiv g(a)$. The crux: **you can only eliminate into $n$-types.** The recursion principle is the constant-family special case, $\mathrm{ext}(f)(|a|_n) :\equiv f(a)$.
- **Lemma 7.3.3 (universal property):** for $B : n\text{-}\mathsf{Type}$, precomposition $(\|A\|_n \to B) \to (A \to B)$, $g \mapsto g \circ |{-}|_n$, is an equivalence. Categorically, the $n$-types form a **reflective subcategory** of types. Consequences: $\|{-}\|_n$ is functorial with naturality $\mathsf{nat}^f_n : \prod_a \|f\|_n(|a|_n) = |f(a)|_n$ (7.3.4), plus higher functoriality (Lemma 7.3.5).
- **Cor 7.3.7:** $A$ is an $n$-type iff $|{-}|_n : A \to \|A\|_n$ is an equivalence.
- **Thm 7.3.8:** $\|A\times B\|_n \simeq \|A\|_n \times \|B\|_n$ (finite products preserved).
- **Thm 7.3.9 / Cor 7.3.10:** $\big\|\sum_{x:A}\|P(x)\|_n\big\|_n \simeq \big\|\sum_{x:A} P(x)\big\|_n$; the outer truncation is redundant if $A$ is already an $n$-type.
- **Thm 7.3.12 (paths in truncations, via encode–decode):** for $n \ge -2$,
$$\|x =_A y\|_n \;\simeq\; \big(|x|_{n+1} =_{\|A\|_{n+1}} |y|_{n+1}\big).$$
  The proof generalizes the type so that general $u,v : \|A\|_{n+1}$ appear (since one cannot induct on a path between $|x|_{n+1}$ and $|y|_{n+1}$), defines $P(|x|_{n+1},|y|_{n+1}) :\equiv \|x = y\|_n$, and builds $\mathsf{decode}$ and $\mathsf{encode}$ exactly as in §§2.12–2.13. Corollaries 7.3.13 and 7.3.14 give $\|\Omega^k(A,a)\|_n = \Omega^k\|(A,a)\|_{n+k}$, which is why homotopy groups $\pi_k$ are truncated loop spaces.
- **Lemma 7.3.15 (cumulativity):** for $k \le n$, $\big\|\|A\|_n\big\|_k = \|A\|_k$.

**Grounding.** Propositional truncation $\|A\|_{-1}$ is the type-theoretic version of "squash"/"erase to a proof of existence":

```lean
-- Lean 4 core: Trunc is the quotient of A by the total relation (a Type-valued
-- "squash" with a recursor that only targets subsingletons).
#check @Trunc.rec    -- eliminates into a family of Subsingletons, like Thm 7.3.2 at n = -1
-- Nonempty A is the Prop-level analogue and eliminates only into Prop.
example (A : Type) (h : Nonempty A) (B : Prop) (f : A → B) : B :=
  h.elim f
```

The restriction "eliminate only into propositions" in Lean's `Nonempty.elim` is the same obstruction as "only into $n$-types" in Theorem 7.3.2.

```rust
// Rust: ‖A‖₋₁ as an opaque "merely inhabited" wrapper. You can construct it from
// an A, but the only way out is to produce another proof-irrelevant result.
pub struct Mere<A>(core::marker::PhantomData<A>); // no accessor for the A inside
impl<A> Mere<A> {
    pub fn intro(_a: A) -> Self { Mere(core::marker::PhantomData) }
    // elimination only into a "proposition": a unit-like result
    pub fn elim_into_prop<P: Prop>(&self, _f: impl FnOnce(A) -> P) -> P { P::the_proof() }
}
pub trait Prop { fn the_proof() -> Self; } // at-most-one-inhabitant types, by convention
```

(Snippets are illustrative; they were not compiled.)

## 5. Colimits of $n$-types (§7.4)

A homotopy colimit of $n$-types need not be an $n$-type (Exercise 7.2 gives an extreme counterexample), but truncating it gives the right universal property among $n$-types. For a span $\mathcal{D} = (A,B,C,f,g)$ with $f : C \to A$, $g : C \to B$, a **cocone** under $\mathcal{D}$ with base $D$ is $(i,j,h)$ with $h : \prod_{c:C} i(f(c)) = j(g(c))$. A pair $(D,c)$ is a **pushout of $\mathcal{D}$ in $n$-types** if for every $n$-type $E$, $(D \to E) \to \mathrm{cocone}_{\mathcal{D}}(E)$, $t \mapsto t\circ c$, is an equivalence.

**Thm 7.4.12:** if $(D,c)$ is the pushout of $\mathcal{D}$ then $(\|D\|_n, \|c\|_n)$ is the pushout of the truncated span $\|\mathcal{D}\|_n$ in $n$-types. The proof sets up maps of spans, shows the truncation maps $|{-}|_n$ assemble into one, and proves the equivalence by 2-out-of-3 on a commuting diagram using $\mathsf{happly}$ and function extensionality. Practical reading: *to compute a colimit in $n$-types, compute it in all types and truncate.*

## 6. Connectedness: the dual notion (§7.5)

**Definition 7.5.1.** $f : A \to B$ is **$n$-connected** if $\prod_{b:B}\mathsf{isContr}(\|\mathsf{fib}_f(b)\|_n)$. A type $A$ is $n$-connected if $A \to \mathbf{1}$ is, i.e. $\|A\|_n$ is contractible. Reading: an $n$-connected type has no interesting homotopy in dimensions $\le n$.

- $(-1)$-connected maps are exactly **surjections** (Lemma 7.5.2). $(-1)$-connected types are *merely inhabited*; 0-connected means "connected"; 1-connected means "simply connected".
- Indexing warning (Remark 7.5.3): the book's $n$-connected *function* is what some classical texts call $(n+1)$-connected (they focus on cofibers rather than fibers).
- **Closure (Lemmas 7.5.4–7.5.6):** retracts and homotopic maps of $n$-connected maps are $n$-connected; if $f$ is $n$-connected then $g$ is $n$-connected iff $g\circ f$ is.
- **Lemma 7.5.7 (induction-principle characterization).** For $f : A \to B$ and $n\ge -2$, the following are equivalent:
  1. $f$ is $n$-connected;
  2. for every $P : B \to n\text{-}\mathsf{Type}$, the map $\lambda s.\,s\circ f : \prod_{b:B}P(b) \to \prod_{a:A}P(f(a))$ is an equivalence;
  3. the same map has a section.

  This is the "dependent elimination against $n$-types" property. It is the tool the book later uses for the Freudenthal suspension theorem (§8.6).
- **Cor 7.5.8:** $|{-}|_n : A \to \|A\|_n$ is $n$-connected. **Cor 7.5.9:** $A$ is $n$-connected iff every map from $A$ to an $n$-type is constant ($B \to (A\to B)$, $b \mapsto \lambda a.\,b$, is an equivalence for all $n$-types $B$).
- **Lemma 7.5.10:** for $B$ an $n$-type and $f : A\to B$, the induced $\|A\|_n \to B$ is an equivalence iff $f$ is $n$-connected.
- **Lemma 7.5.11:** for $n \ge -1$, $A$ is $n$-connected iff its basepoint $a_0 : \mathbf{1}\to A$ is $(n-1)$-connected. In particular a pointed $(A,a_0)$ is 0-connected iff $\prod_{x:A}\|x = a_0\|$.
- **Lemmas 7.5.12–7.5.14:** behaviour on total spaces ($\mathrm{total}(f)$ is $n$-connected iff each $f(a)$ is), and an $n$-connected map induces $\|A\|_n \simeq \|B\|_n$. The converse fails: $0_{\mathbf{2}} : \mathbf{1}\to\mathbf{2}$ induces an equivalence on $(-1)$-truncations but is not surjective. Being $n$-connected is "a bit stronger" than inducing an equivalence on $\|{-}\|_n$.

## 7. Orthogonal factorization (§7.6)

**Definition 7.6.1.** $f$ is **$n$-truncated** if every fiber $\mathsf{fib}_f(b)$ is an $n$-type. So $f$ is $(-2)$-truncated iff it is an equivalence, and $A$ is an $n$-type iff $A \to \mathbf{1}$ is $n$-truncated. **Lemma 7.6.2:** $f$ is $(n+1)$-truncated iff each $\mathsf{ap}_f : (x=y)\to(f(x)=f(y))$ is $n$-truncated; $(-1)$-truncated is exactly "embedding" (§4.6).

So the two classes generalize the classical pair for sets:

| $n=-1$ | classical analogue |
|---|---|
| $(-1)$-connected | surjection |
| $(-1)$-truncated | injection/embedding |

**$n$-image.** $\mathrm{im}_n(f) :\equiv \sum_{b:B}\|\mathsf{fib}_f(b)\|_n$. **Lemma 7.6.4:** the canonical $\tilde f : A \to \mathrm{im}_n(f)$ is $n$-connected and $\mathrm{pr}_1 : \mathrm{im}_n(f)\to B$ is $n$-truncated, so every function factors as an $n$-connected map followed by an $n$-truncated one.

$$A \xrightarrow{\ \tilde f\ (n\text{-connected})\ } \mathrm{im}_n(f) \xrightarrow{\ \mathrm{pr}_1\ (n\text{-truncated})\ } B$$

**Uniqueness (Thm 7.6.6).** The type
$$\mathsf{fact}_n(f) :\equiv \sum_{X:\mathcal{U}}\ \sum_{g:A\to X}\ \sum_{h:X\to B} (h\circ g \sim f)\times \mathsf{conn}_n(g)\times\mathsf{trunc}_n(h)$$
is *contractible*, with center $(\mathrm{im}_n(f), \tilde f, \mathrm{pr}_1, \dots)$. The proof reduces, using Lemma 7.6.5 (a fiberwise equivalence $\mathsf{fib}_{h_1}(b)\simeq\mathsf{fib}_{h_2}(b)$ when $g_1,g_2$ are $n$-connected and $h_1,h_2$ are $n$-truncated) and univalence, to constructing an equivalence $X_1\simeq X_2$ with the required coherence homotopies. Note that "unique" here is homotopical: the *space of factorizations* is contractible, not merely "there is one up to isomorphism".

**Orthogonality (Thm 7.6.7).** If $e : A\to B$ is $n$-connected and $m : C\to D$ is $n$-truncated, then
$$(B\to C)\ \longrightarrow \sum_{h:A\to C}\ \sum_{k:B\to D}\ (m\circ h\sim k\circ e)$$
is an equivalence: every commutative square with $e$ on the left and $m$ on the right has a *unique* diagonal filler. **Thm 7.6.9:** $n$-images are stable under pullback.

**Grounding.** For $n=-1$ on finite sets, this is the familiar decomposition of a function into its surjection onto its image followed by an inclusion:

```python
def factor(f, domain):
    image = {f(x) for x in domain}          # im(f)
    g = lambda x: f(x)                       # A -> im(f)  (surjective, i.e. (-1)-connected)
    h = lambda y: y                          # im(f) -> B  (injective, i.e. (-1)-truncated)
    return image, g, h
```

The chapter's content is that *the same pattern works at every truncation level $n$ and that the factorization is unique as a space*.

## 8. Modalities: abstracting the pattern (§7.7)

The book states that this section is not used in the rest of the book. It shows that nearly everything above uses only the universal property of Lemma 7.3.3.

**Reflective subuniverse (Def 7.7.1).** A predicate $P : \mathcal{U}\to\mathsf{Prop}$ together with, for each $A$, a type $\#A$ with $P(\#A)$ and a map $\eta_A : A\to\#A$ such that for every $B$ with $P(B)$, $(\#A\to B)\to(A\to B)$, $f\mapsto f\circ\eta_A$, is an equivalence. Standard consequences: $A\in\mathcal{U}_P$ iff $\eta_A$ is an equivalence; closure under retracts and all limits (so identity types of modal types are modal); colimits in $\mathcal{U}_P$ are obtained by applying $\#$ to ordinary colimits. 

- **Thm 7.7.2:** a reflective subuniverse is closed under $\prod$-types ("exponential ideal"). **Cor 7.7.3:** $\#(A\times B)\simeq\#A\times\#B$.
- **Two properties of $n$-truncation that do *not* hold for every reflective subuniverse** are closure under $\Sigma$-types (Thm 7.1.8) and truncation induction (Thm 7.3.2). **Thm 7.7.4** shows these two are logically equivalent to each other: (i) $\Sigma$-closure is equivalent to (ii) eliminating dependent families valued in $\mathcal{U}_P$.

**Modality (Def 7.7.5).** An operation $\# : \mathcal{U}\to\mathcal{U}$ with:

1. units $\eta^\#_A : A\to\#A$;
2. for every $B : \#A\to\mathcal{U}$, an induction operator $\mathsf{ind}_\# : \prod_{a:A}\#(B(\eta^\#_A(a)))\to\prod_{z:\#A}\#(B(z))$;
3. computation paths $\mathsf{ind}_\#(f)(\eta^\#_A(a)) = f(a)$;
4. for all $z,z' : \#A$, $\eta^\#_{z=z'} : (z=z')\to\#(z=z')$ is an equivalence.

$A$ is **modal** if $\eta^\#_A$ is an equivalence, and $\mathcal{U}_\# :\equiv \{X : \mathcal{U}\mid X\text{ is }\#\text{-modal}\}$. **Thm 7.7.7** gives the universal property; **Cor 7.7.8** says modal types form a reflective subuniverse satisfying Theorem 7.7.4's conditions. So **modalities are exactly reflective subuniverses closed under $\Sigma$-types.** The name comes from modal logic ("possibly $A$", "necessarily $A$"); the book calls these idempotent, monadic modalities and suggests adverbs for informal speech: "merely" for propositional truncation, "purely" for the identity modality $\#A :\equiv A$.

For a modality, define $f$ to be **$\#$-connected** if $\#(\mathsf{fib}_f(b))$ is contractible for all $b$ and **$\#$-truncated** if each fiber is modal. Everything in §§7.5–7.6 that doesn't compare different $n$ transfers verbatim, in particular the orthogonal factorization system. The book mentions, without developing, **left exact** modalities (those preserving pullbacks), which categorify Lawvere–Tierney topologies and correspond to sub-$(\infty,1)$-toposes. Note that $n$-truncation is *not* left exact.

```lean
-- Lean 4 / Mathlib analogue (informal): a monad M with a unit and an idempotence
-- condition is the programmer's shadow of a modality.
-- class IdempotentMonad (M : Type → Type) [Monad M] where
--   idem : ∀ A, Function.Bijective (pure : M A → M (M A))  -- unit of M applied at M A
```

```rust
// Rust: the *shape* of a modality is a monad-like type constructor with an
// "already modal" test. Illustrative only: Rust cannot enforce the equivalence.
trait Modality {
    type Apply<A>;                           // #A
    fn unit<A>(a: A) -> Self::Apply<A>;      // η_A : A → #A
    // ind#: eliminate into #B(η a) pointwise and lift to all of #A
    fn ind<A, B>(f: impl Fn(A) -> Self::Apply<B>) -> impl Fn(Self::Apply<A>) -> Self::Apply<B>;
}
```

## 9. Synthesis: what depends on what

```
 isContr (§3.11)  --induction on n-->  is-n-type  (7.1)  -- closed under Σ, Π, =, retracts
        |                                   |
 Ω^{n+1}(A,a) contractible (7.2.9)          |  hub-and-spoke HIT (6.7, 6.9)
        |                                   v
        +------------------------->  ‖A‖_n  (7.3)  --> reflective subcategory of n-types
                                            |
              fibers truncated / connected  v
  n-connected (7.5) <-- dual -->  n-truncated (7.6)  ==> unique factorization, orthogonality
                                            |
                      generalize the universal property
                                            v
                         reflective subuniverse --(+Σ-closure)--> modality (7.7)
```

- **Depends on:** identity types and path induction (Ch. 1–2), contractibility and mere propositions (Ch. 3), embeddings and surjections (§4.6), function extensionality and univalence (§§2.9–2.10), HITs and the hub-and-spoke construction (Ch. 6).
- **Feeds into:** Chapter 8 (truncated loop spaces give homotopy groups, the encode-decode method, Freudenthal uses Lemma 7.5.7), Chapter 9 (the set-level case, $0$-types, underlies precategories), and Chapter 10 (the category $\mathsf{Set}$ and images).

### How this bears on the compiler and prover project (Focus Area: `type-theory`)

- **Proof irrelevance as a design axis (load-bearing).** The $(-1)$-level, "mere propositions", is the theory behind the choice of making proofs erasable or irrelevant in a dependent/refinement type language. A refinement predicate $\{x : A \mid P(x)\}$ is only a *subtype* (and `isDefEq` on it only needs to compare the underlying $A$) when $P$ is a mere proposition (§3.5). This is the mathematical justification for Lean's `Prop` and for the elaborator treating proof arguments as definitionally equal. In Lean the property is *built in* to `Prop`; in HoTT it is a proved invariant that the kernel does not know about.
- **Decidable equality $\Rightarrow$ set (Hedberg)** is the reason a type checker for a refinement language with decidable equality (integers, booleans, enums, finite automata states) need not track proof-relevant equalities at all. It bears directly on the CSP kernel's domains: a finite-domain variable has decidable equality, so its path space is a mere proposition.
- **Elimination restrictions as typing rules.** "You may only eliminate $\|A\|_n$ into $n$-types" is a *typing side condition* on a recursor; implementing the kernel's checker for a Lean-style `Quot`/`Nonempty` eliminator is the same kind of check ("target universe must be `Prop`"). This is the Rust-grounded mechanism to carry forward.
- **Modalities** are not needed for the compiler targets and are skipped as a topic of direct implementation; the idempotent-monad shape is the nearest programming analogue.
- This chapter has no bearing on unification, SAT/SMT/CSP or abstract interpretation. No connection to those is forced here.

## 10. Key questions (self-check)

1. Why does the recursion on $n$ start at $-2$ with contractible types, and what breaks in Theorem 7.1.6 when $n=-2$?
2. State Hedberg's theorem and explain which fact about $\neg\neg$ and decidability it uses (Lemma 7.2.4, Corollary 7.2.3).
3. Why can $\|A\|_n$ only be eliminated into $n$-types, and how does this restriction appear in the induction principle (Theorem 7.3.2)?
4. How are $n$-connected and $n$-truncated maps dual, and what is the statement of the unique factorization (Theorem 7.6.6)?
5. Which two properties of $n$-truncation does a general reflective subuniverse lack, and why does Theorem 7.7.4 say they are equivalent?
