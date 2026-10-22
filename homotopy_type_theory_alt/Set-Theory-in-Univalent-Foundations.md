---
title: Set Theory in Univalent Foundations
book: Homotopy Type Theory — Univalent Foundations of Mathematics
chapters: "Chapter 10 (printed pp. 341–372), with background from 3.8, 6.10, 7.6"
tags: [hott, set-theory, type-theory, automated-reasoning, well-founded-recursion, higher-inductive-types]
---

[[book-guidelines|↩ Back to guidelines]]

# Set Theory in Univalent Foundations

## 1. Why the book does this at all

In type theory, "set" is not primitive. Chapter 3 defined a **set** as a $0$-type: a type in which any two parallel paths are equal. That gives a notion of "type with no higher structure", but it does not yet show that these types support the mathematics that ordinary set theory supports. Chapter 10 checks this. It builds, inside HoTT, the following:

1. The *category* of sets, to show that the basic categorical structure of set theory is present.
2. *Cardinals* and *ordinals*, to show that the classical theory of size and order can be reconstructed.
3. A *cumulative hierarchy* $V$, to show that a model of ZF(C)-style membership-based set theory sits inside type theory.

The overall message is that univalent foundations is a conservative extension of how mathematicians already use sets, provided you are careful about where classical principles (excluded middle, choice) are needed. The chapter keeps track of this carefully, so it is a good guide to which results are constructive and which are not.

## 2. The category $\mathcal{S}et$ (§10.1)

$\mathcal{S}et$ is the category whose objects are the $0$-types of a universe $\mathcal{U}$ and whose morphisms are functions. It is a *category* (not just a precategory) by univalence (Chapter 9). The book climbs a ladder of structure.

**Limits and colimits (10.1.1).** Products come from the universal property of $\prod$:

$$\Big(X \to \prod_{a:A} B(a)\Big) \simeq \prod_{a:A}(X \to B(a)).$$

Pullbacks are $\sum_{a:A}\sum_{b:B} f(a) = g(b)$, which is a set if $A, B, C$ are. Coproducts are $+$ and $\Sigma$. Pushouts exist because $n$-types have them (§7.4). So $\mathcal{S}et$ is complete and cocomplete.

**Images and regularity (10.1.2).** The image of $f : A \to B$ is $\mathrm{im}(f) :\equiv \sum_{b:B}\|\mathrm{fib}_f(b)\|$, taken from §7.6. The book proves:

- Injective maps are exactly the monomorphisms (Lemma 10.1.2).
- For $f : A \to B$ between sets, $f$ is an epimorphism iff it is surjective iff the mapping cone $C_f$ (a pushout) is contractible (Lemma 10.1.4). The book remarks that the epi-implies-surjective direction is not trivial to prove *predicatively*; the proof here uses pushouts and univalence.
- **Theorem 10.1.5:** $\mathcal{S}et$ is a **regular** category, and surjections are the regular epimorphisms.

**Quotients and exactness (10.1.3).** A relation $R : A \to A \to \mathsf{Prop}$ is **effective** if the square formed by the quotient map $c_R : A \to A/R$ is a pullback. Equivalently, the canonical map

$$\prod_{x,y:A} R(x,y) \to (c_R(x) = c_R(y))$$

is a fiberwise equivalence. The key results:

- **Lemma 10.1.8 / Theorem 10.1.10.** Every equivalence relation is effective, and $A/R \simeq A /\!/ R$ (the coequalizer of the kernel pair).
- The proof of effectiveness uses univalence: $(R(x) = R(y)) \simeq \prod_z (R(x,z)\simeq R(y,z))$, which is equivalent to $R(x,y)$ for an equivalence relation.

**$\Pi W$-pretopos (10.1.4).** **Theorem 10.1.11:** $\mathcal{S}et$ is a $\Pi W$-pretopos, i.e. a locally cartesian closed, exact, extensive category with $W$-types (initial algebras of polynomial endofunctors, §5.3–5.4).

It is *not* automatically an elementary topos. A topos needs a subobject classifier. Univalence makes $\mathsf{Prop} :\equiv \sum_{X:\mathcal{U}}\mathsf{isProp}(X)$ classify monomorphisms, but $\mathsf{Prop}$ lives in the next universe up, so it is not an object of $\mathcal{S}et_{\mathcal{U}}$. **Theorem 10.1.12:** with propositional resizing (§3.5), $\mathcal{S}et_{\mathcal{U}}$ is an elementary topos.

**Choice implies excluded middle (10.1.5).** **Theorem 10.1.14 (Diaconescu):** the axiom of choice implies LEM. The proof is a nice use of the machinery above:

- For a mere proposition $A$, the suspension $\Sigma(A)$ is a *set* (Lemma 10.1.13), and $A \simeq (N =_{\Sigma(A)} S)$.
- The map $f : \mathbf{2} \to \Sigma(A)$ sending $0_{\mathbf 2}\mapsto N$, $1_{\mathbf 2}\mapsto S$ is surjective.
- Choice gives a section $g$. Equality on $\mathbf{2}$ is decidable, so $g(f(0)) = g(f(1))$ is decidable, hence $N = S$ is decidable, hence $A + \neg A$.

**Theorem 10.1.15:** with choice, $\mathcal{S}et$ is a well-pointed boolean elementary topos with choice (Lawvere's elementary theory of the category of sets).

## 3. Cardinal numbers (§10.2)

**First principles.** A cardinal is "a set up to bijection". In HoTT you do not need to build a quotient by hand: sets up to isomorphism *are* the $0$-truncation of the type of sets.

**Definition 10.2.1.** $\mathsf{Card} :\equiv \|\mathsf{Set}\|_0$, with $|A|_0$ the cardinality of $A$. By construction, $\mathsf{Card}$ is a set. Operations are defined by induction on truncation, e.g.

$$|A|_0 + |B|_0 :\equiv |A + B|_0,\qquad |A|_0\cdot|B|_0 :\equiv |A\times B|_0,\qquad |A|_0^{|B|_0} :\equiv |B\to A|_0.$$

- **Lemma 10.2.4:** $\mathsf{Card}$ is a commutative semiring.
- **Cardinal inequality** ($\alpha \le \beta$: there merely is an injection between representatives) is a preorder (Lemma 10.2.8).
- **Lemma 10.2.9:** with LEM, injection $A\to B$ gives surjection $B \to A$ when $A$ is inhabited. The converse direction (surjection gives injection) needs the axiom of choice.
- **Theorem 10.2.10 (Schröder–Bernstein)**, assuming LEM; **Corollary 10.2.11:** $\le$ is then a partial order.
- **Theorem 10.2.12 (Cantor):** there is no surjection $A \to (A \to \mathbf{2})$. This is constructive: diagonalize with $g(a) :\equiv \neg f(a)(a)$. **Corollary 10.2.13** (every cardinal has a strictly larger one, $2^\alpha$) assumes LEM.

## 4. Ordinal numbers (§10.3)

**First principles.** Classically, an ordinal is a well-ordered set, and "well-ordered" is stated with minimal elements of subsets, which needs LEM to be useful. The book instead uses the *constructive* notion of **well-foundedness by accessibility**, which supports induction directly.

**Accessibility (Definition 10.3.1).** For a relation $<$ on a set $A$, $\mathsf{acc}(a)$ is the inductive family with one constructor:

$$\mathsf{acc}_< : \prod_{a:A}\Big(\prod_{b:A} (b<a) \to \mathsf{acc}(b)\Big) \to \mathsf{acc}(a).$$

An element with no predecessors is vacuously accessible. $<$ is **well-founded** if every element is accessible; the induction principle of $\mathsf{acc}$ is then well-founded induction. Both properties are mere propositions (Lemmas 10.3.2, 10.3.4). Example 10.3.6 shows that the canonical order on a $W$-type is well-founded.

**Extensional** (Definition 10.3.9): $\forall a,b.\ (\forall c.\ c<a \Leftrightarrow c<b)\to a=b$. **Theorem 10.3.10:** the type of extensional well-founded relations on a set is a set.

**Simulations (Definition 10.3.11).** A simulation $f:A\to B$ preserves $<$ and is "downward closed": if $b< f(a)$ then there merely exists $a' < a$ with $f(a')=b$. Results:

- Simulations are injective (Lemma 10.3.12, by double well-founded induction).
- Between extensional well-founded relations there is at most one simulation (Lemma 10.3.16), so they form a poset (Corollary 10.3.15). **Theorem 10.3.14** shows this is a *standard notion of structure* in the sense of §9.8, so by the structure identity principle isomorphic ordinals are equal.

**Ordinals (Definition 10.3.17).** An ordinal is a set with an extensional, well-founded, **transitive** relation. Example: $(\mathbb{N}, <)$ is the ordinal $\omega$.

**The ordinal of ordinals (Theorem 10.3.20).** $A<B$ iff there is a *bounded* simulation $A \to B$, i.e. $A \cong B/b$ for an initial segment $B/b :\equiv \{c : B \mid c < b\}$. Then $(\mathsf{Ord}, <)$ is itself an ordinal. The book is careful about universes: $(\mathsf{Ord}_{\mathcal{U}_i}, <)$ is an ordinal in $\mathcal{U}_{i+1}$. Lemmas 10.3.21–22 give successors and suprema of small families.

## 5. Classical well-orderings (§10.4)

Assuming LEM, the constructive notion agrees with the classical one:

- Ordinals are trichotomous (Lemma 10.4.1); well-founded relations have no cycles (10.4.2).
- **Theorem 10.4.3:** $(A,<)$ is an ordinal iff every nonempty subset has a least element.
- **Theorem 10.4.4:** assuming LEM, "every set merely admits a choice function on nonempty subsets" iff "every set merely admits the structure of an ordinal". This is the well-ordering theorem. **Remark 10.4.5:** the proof needs propositional resizing (implied by LEM) so that the constructed $X'$ stays in the same universe as $X$. Getting the universe levels wrong makes the argument invalid.
- Under AC, $\mathsf{Ord}\to\mathsf{Set}$ is a surjection (Corollary 10.4.6). Since $\mathsf{Ord}$ is a *set* and $\mathsf{Set}$ is a $1$-type, this is not automatic for general $1$-types. **Corollary 10.4.7:** $\mathcal{S}et$ then has a weak equivalence from a strict category.
- **Theorem 10.4.8:** under AC, $\mathsf{Ord}\to\mathsf{Card}$ has a *canonical* section (least ordinal of each cardinality). The book points out the "easy and wrong" proof, which just invokes AC on two sets: it would only give a *mere* section, while the least-element construction gives a specified one. This yields the aleph function.

## 6. The cumulative hierarchy $V$ (§10.5)

**First principles.** ZF-style sets are well-founded trees of sets, compared extensionally. Two different "presentations" of the same collection (different index types, different enumerations, repeated elements) must be *equal*. The tool for this is a **higher inductive type** (Chapter 6).

**Definition 10.5.1.** $V$ (relative to a universe $\mathcal{U}$) has constructors:

1. For $A:\mathcal{U}$ and $f:A\to V$: $\mathsf{set}(A,f) : V$ (informally, the image $\{f(a)\mid a\in A\}$).
2. A **path constructor** for bi-inclusion: if
$$\forall a{:}A.\ \exists b{:}B.\ f(a) =_V g(b)\ \wedge\ \forall b{:}B.\ \exists a{:}A.\ f(a)=_V g(b),$$
then $\mathsf{set}(A,f) =_V \mathsf{set}(B,g)$.
3. The $0$-truncation constructor: $V$ is a set.

The empty set is $\mathsf{set}(\mathbf{0},\mathsf{rec}_{\mathbf 0})$, and everything else is built from it.

**Bisimulation (Definition 10.5.4, Lemma 10.5.5).** Define $\sim$ on $V$ by double induction:

$$\mathsf{set}(A,f)\sim \mathsf{set}(B,g) :\equiv \big(\forall a.\exists b.\ f(a)\sim g(b)\big)\wedge\big(\forall b.\exists a.\ f(a)\sim g(b)\big).$$

Then $(u =_V v) = (u \sim v)$. The book notes that the $0$-truncation constructor cannot be dropped and recovered afterwards from Theorem 7.2.2, because the proof of Lemma 10.5.5 already uses that $V$ is $0$-truncated.

**Membership.** $\in$ is defined from the presentation: $x\in \mathsf{set}(A,f) :\equiv \exists a.\ x = f(a)$. Lemma 10.5.6 shows every $u : V$ has a canonical monic presentation $m_u : A_u \rightarrowtail V$.

**Theorem 10.5.8.** $(V,\in)$ satisfies extensionality, empty set, pairing, infinity, union, function set, $\in$-induction, replacement, and separation (for $\mathcal{U}$-small classes).

**Theorem 10.5.11.** With AC and a universe, $V$ is a model of **ZFC**. Full separation and power sets come from LEM (power set $\mathcal{P}(a) = (a\to\mathbf{2})$), which is implied by AC via Diaconescu.

## 7. Grounding in code

These snippets are original illustrations (not from the book, and not compiled here).

**Accessibility as an inductive family (Lean).** This is exactly Definition 10.3.1; Lean's `Acc` is the same type, living in `Prop`:

```lean
inductive MyAcc {α : Type} (r : α → α → Prop) : α → Prop where
  | intro (a : α) (h : ∀ b, r b a → MyAcc r b) : MyAcc r a

def WF {α : Type} (r : α → α → Prop) : Prop := ∀ a, MyAcc r a
```

Well-founded recursion in Lean (`termination_by`, `WellFounded.fix`) is the computational face of the induction principle of $\mathsf{acc}$.

**Why the induction principle is the termination argument (Rust).** A recursive function is total when each recursive call is on an $r$-smaller argument:

```rust
// Recursion on a well-founded relation: Collatz-free example with a measure.
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) } // (b, a % b) is smaller under the measure b
}
```

The measure `b` maps into $(\mathbb{N},<)$, which is well-founded.

**Quotient with effectiveness (Python).** A quotient $A/R$ is usually implemented with canonical representatives. Effectiveness means "two elements have the same class iff they are related":

```python
def quotient(xs, related):
    classes = []
    for x in xs:
        for c in classes:
            if related(x, c[0]):
                c.append(x); break
        else:
            classes.append([x])
    return classes
# class_of(x) == class_of(y)  <=>  related(x, y)   (needs related to be an equivalence relation)
```

**The cumulative hierarchy (Rust).** The constructor $\mathsf{set}(A,f)$ is a tree node with an index set. The path constructor is the equivalence "same elements up to bisimulation":

```rust
enum V { Set(Vec<V>) }

fn bisim(u: &V, v: &V) -> bool {
    let (V::Set(xs), V::Set(ys)) = (u, v);
    xs.iter().all(|x| ys.iter().any(|y| bisim(x, y)))
        && ys.iter().all(|y| xs.iter().any(|x| bisim(x, y)))
}
```

In HoTT, `bisim` *is* equality on $V$ (Lemma 10.5.5); in Rust one has to remember to use it instead of structural `==`.

## 8. Synthesis

**Dependencies.** The chapter leans on: sets and $n$-truncation (Ch. 3, 7), univalence (Ch. 2, 4), quotients and pushouts (Ch. 6), $W$-types and inductive families (Ch. 5), and the category-theoretic setup of Ch. 9 (standard notions of structure, category $\mathcal{S}et$). It is mostly an application chapter: little new type theory, a lot of checking that the old set-theoretic notions survive.

```
Sets (0-types) ──► Set category ──► regular ──► exact ──► ΠW-pretopos
      │                                                      │ (+ resizing)
      │                                                      ▼
      ├──► Card = ‖Set‖₀ ──► semiring, ≤, Cantor        elementary topos
      ├──► acc / well-foundedness ──► simulations ──► Ord  (+ AC ⇒ LEM)
      └──► HIT V (set(A,f) + bisim path + 0-trunc) ──► ZF(C)
```

**Relevance to the project** (tagged `type-theory` and `automated-reasoning`):

- *Load-bearing, `type-theory`:* the **accessibility predicate** is the standard way an elaborator/kernel justifies well-founded recursion. A termination checker for the planned language needs exactly this: a relation, a proof that it is well-founded, and a recursor. The `acc` family is an inductive family in the sense of §5.7, so it exercises the same kernel machinery as [[Inductive-Types|inductive types]] and indexed families.
- *`type-theory` + trusted kernels:* the Diaconescu proof and Remark 10.4.5 show that universe levels matter for the *validity* of a proof, not just its presentation. A kernel that checks universe constraints is doing real logical work.
- *`automated-reasoning`:* the constructive/classical bookkeeping (what needs LEM, choice, resizing) is a map of what a prover can and cannot do by pure construction. For example, "injection gives surjection" needs *decidability of fibers*, which a solver for decidable fragments could supply. The book does not discuss proof search here, so this is a connection of mine, not the author's.
- *Don't force it:* cardinals, the cumulative hierarchy and ZFC models are foundational justifications and do not bear directly on the elaborator or the CSP kernel.
