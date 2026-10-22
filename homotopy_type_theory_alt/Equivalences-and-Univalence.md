---
title: Equivalences and Univalence
book: Homotopy Type Theory - Univalent Foundations of Mathematics
chapters: "Ch. 4 (pp. 129–148); §2.4 (pp. 76–79); §2.9 (pp. 86–87); §2.10 (pp. 89–90)"
tags: [type-theory, homotopy-type-theory, univalence, equivalences, function-extensionality]
focus-areas: [type-theory]
---

[[book-guidelines|↩ Back to guidelines]]

# Equivalences and Univalence

## 1. The problem: what should "these two things are the same" mean?

Programmers constantly treat isomorphic types as interchangeable: a `Vec<(A,B)>` and a pair of vectors of equal length, `Option<()>` and `bool`, one encoding of the naturals and another. In ordinary type theory this is an informal convention. Nothing in the *identity type* $A =_{\mathcal U} B$ says that such types are "equal", and every proof about one has to be transported to the other by hand.

Homotopy type theory (HoTT) wants to make the convention an internal rule. The identity type of types should *be* the type of ways in which two types are the same. This forces two design questions:

1. What is the right type "$f$ is an equivalence"? It has to be well behaved as *data*, because in a proof-relevant setting a proof of a property is a thing you can compare, store and transport.
2. Once that is fixed, how do we connect it to the identity type? The answer is the univalence axiom (Axiom 2.10.3).

Most of Chapter 4 answers the first question. The reason is that the naive answer is wrong, and the book shows that the wrong answer would make univalence false or inconsistent.

## 2. Homotopies and the naive notion of isomorphism (§2.4)

Two functions are traditionally "the same" if they agree pointwise. Under propositions-as-types this is a type, not a fact.

**Definition 2.4.1 (homotopy).** For $f, g : \prod_{x:A} P(x)$,

$$(f \sim g) :\equiv \prod_{x:A} \big(f(x) = g(x)\big).$$

A homotopy is not an identification $f = g$; §2.9 will add an axiom that makes the two equivalent. Lemma 2.4.2 says $\sim$ is an equivalence relation. Lemma 2.4.3 says that homotopies are automatically *natural*: for $H : f \sim g$ and $p : x = y$,

$$H(x) \cdot g(p) = f(p) \cdot H(y).$$

Here $f(p)$ abbreviates $\mathsf{ap}_f(p)$. The proof is by path induction and reduces to $\mathsf{refl}$. This naturality is the engine behind every "coherence" argument below.

**Quasi-inverses (Definition 2.4.6).** The traditional notion of isomorphism is

$$\mathsf{qinv}(f) :\equiv \sum_{g : B \to A} (f \circ g \sim \mathsf{id}_B) \times (g \circ f \sim \mathsf{id}_A).$$

The book calls this "historically accurate, but slightly derogatory-sounding". The problem is that, for a single $f$, $\mathsf{qinv}(f)$ can have several unequal inhabitants. That matters because a proof-relevant equivalence $A \simeq B$ should *carry* its witness, and if the witness is not unique then "being an equivalence" is extra structure rather than a property.

**Desiderata for $\mathsf{isequiv}(f)$** (p. 78). The book requires:

1. $\mathsf{qinv}(f) \to \mathsf{isequiv}(f)$,
2. $\mathsf{isequiv}(f) \to \mathsf{qinv}(f)$ (so the two are logically equivalent),
3. any two $e_1, e_2 : \mathsf{isequiv}(f)$ are equal, i.e. $\mathsf{isequiv}(f)$ is a *mere proposition*.

The type of equivalences is then $(A \simeq B) :\equiv \sum_{f : A \to B} \mathsf{isequiv}(f)$. Property (iii) is what lets us blur an equivalence with its underlying function: two equivalences with equal underlying functions are equal.

Lemma 2.4.12 shows that $\simeq$ is reflexive, symmetric and transitive on a universe $\mathcal U$.

## 3. Why $\mathsf{qinv}$ fails: Lemma 4.1.1 and Theorem 4.1.3 (§4.1)

**Lemma 4.1.1.** If $\mathsf{qinv}(f)$ is inhabited, then

$$\mathsf{qinv}(f) \;\simeq\; \prod_{x:A} (x = x).$$

The proof assumes univalence to reduce to the case $f \equiv \mathsf{id}_A$ (Exercise 4.3 asks for a proof without it). It then uses function extensionality and the fact that $\sum_{g : A \to A} (g = \mathsf{id}_A)$ is contractible, so that only $\mathsf{id}_A = \mathsf{id}_A \simeq \prod_x x = x$ is left.

Intuition: the data $(g, \eta)$ are "used up" by contractibility, but the second homotopy $\varepsilon$ remains as a free choice, and it contributes a *loop at every point*. The type $\prod_{x:A}(x = x)$ is the "center" of the higher groupoid $A$ (natural transformations from the identity functor to itself). If $A$ is a group seen as a one-object groupoid, it is the group's centre in the usual sense.

**Theorem 4.1.3.** There are types $A, B$ and a function $f : A \to B$ for which $\mathsf{qinv}(f)$ is *not* a mere proposition. The counterexample uses $X :\equiv \sum_{A : \mathcal U} \|\mathbf 2 = A\|$ (equivalent to $K(\mathbb Z_2, 1)$) together with Lemma 4.1.2 to build a non-trivial element of $\prod_{x:X}(x=x)$ from the swap equivalence $\mathbf 2 \simeq \mathbf 2$. The book notes that the circle $\mathbb S^1 = K(\mathbb Z, 1)$ is another easy counterexample.

Exercise 4.6 makes the point sharper: a variant "qinv-univalence", stated with $\mathsf{qinv}$ in place of a good $\mathsf{isequiv}$, is *inconsistent*. So a good definition is essential in the statement of univalence (Remark 2.10.4).

## 4. Three good definitions (§§4.2–4.5)

All three are mere propositions, and they are pairwise equivalent (Corollary 4.3.3, Theorem 4.4.5). The strategy for each is the one the book states at the start of §4.2: split the data into a contractible part plus something that combines with the remaining datum into a contractible type.

### 4.1 Half adjoint equivalences

**Definition 4.2.1.** $f$ is a half adjoint equivalence if there are $g : B \to A$, $\eta : g \circ f \sim \mathsf{id}_A$, $\varepsilon : f \circ g \sim \mathsf{id}_B$ and a coherence

$$\tau : \prod_{x:A} f(\eta x) = \varepsilon(f x).$$

So

$$\mathsf{ishae}(f) :\equiv \sum_{g} \sum_{\eta} \sum_{\varepsilon} \prod_{x:A} f(\eta x) = \varepsilon(f x).$$

- The symmetric coherence $\upsilon : \prod_{y:B} g(\varepsilon y) = \eta(g y)$ gives the same thing logically (Lemma 4.2.2). One must **not** include both, otherwise one datum remains again. The book's heuristic: "we expect to get a well-behaved type if we cut off after an odd number of coherences."
- **Theorem 4.2.3** ($\mathsf{qinv}(f) \to \mathsf{ishae}(f)$): keep $g$ and $\eta$, but *replace* $\varepsilon$ by
$$\varepsilon'(b) :\equiv \varepsilon(f(g(b)))^{-1} \cdot \big(f(\eta(g(b))) \cdot \varepsilon(b)\big),$$
and obtain $\tau$ from naturality (Lemma 2.4.3) and Corollary 2.4.4.
- **Definition 4.2.4 (fiber).** $\mathsf{fib}_f(y) :\equiv \sum_{x:A} (f(x) = y)$. **Theorem 4.2.6:** the fibers of a half adjoint equivalence are contractible, with centre $(g\,y, \varepsilon y)$.
- **Theorem 4.2.13:** $\mathsf{ishae}(f)$ is a mere proposition. The proof uses $\mathsf{linv}$, $\mathsf{rinv}$ (Definition 4.2.7), the fact that both are contractible when $f$ has a quasi-inverse (Lemma 4.2.9, via fibers of $(f\circ -)$ and $(-\circ f)$), and that $\mathsf{rcoh}_f(g,\varepsilon)$ is contractible (Lemma 4.2.12).

**The book's official choice (§4.5):** $\mathsf{isequiv}(f) :\equiv \mathsf{ishae}(f)$, because it "contains the most directly useful data", which is good for formalization.

### 4.2 Bi-invertible maps

$\mathsf{biinv}(f) :\equiv \mathsf{linv}(f) \times \mathsf{rinv}(f)$ (Definition 4.3.1), with

$$\mathsf{linv}(f) :\equiv \sum_{g} (g \circ f \sim \mathsf{id}_A), \qquad \mathsf{rinv}(f) :\equiv \sum_{g} (f \circ g \sim \mathsf{id}_B).$$

A separate left and right inverse, with no 2-dimensional data at all. This is the "easiest" definition mentioned in §2.4 (equation 2.4.10): from $(g, \alpha, h, \beta)$ one recovers a quasi-inverse via $\gamma(x) :\equiv \beta(g x)^{-1} \cdot h(\alpha x)$. Theorem 4.3.2: $\mathsf{biinv}(f)$ is a mere proposition. The trick is the alternative from the same heuristic: instead of adding a *higher* datum to combine with $\varepsilon$, add a *lower* one (a separate right inverse).

### 4.3 Contractible maps

$\mathsf{isContr}(f) :\equiv \prod_{y:B} \mathsf{isContr}(\mathsf{fib}_f(y))$ (Definition 4.4.1). This is Voevodsky's original definition. Theorem 4.4.3 builds $g(y) :\equiv \mathsf{pr}_1(\mathsf{pr}_1(P y))$ from the centres of contraction. Useful consequence (Corollary 4.4.6): when proving $f$ is an equivalence you may assume $B$ is inhabited.

Contractible maps are later called $(-2)$-truncated (from Chapter 7).

### 4.4 Which to use

| Definition | What it stores | Good for |
|---|---|---|
| $\mathsf{qinv}$ | $g, \varepsilon, \eta$ | *Proving* a map is an equivalence (most common). Not a proposition. |
| $\mathsf{ishae}$ | adds the coherence $\tau$ | Formalization; most directly useful data. |
| $\mathsf{biinv}$ | separate left and right inverse | No 2-paths; the halves are independent. |
| $\mathsf{isContr}(f)$ | every fiber contractible | Reducing to inhabited codomain; connects to truncation levels. |

## 5. More structure on equivalences (§§4.6–4.8)

**Surjections and embeddings (Definition 4.6.1).** $f$ is *surjective* if every $\|\mathsf{fib}_f(b)\|$ is inhabited, i.e. $\forall b.\ \exists a.\ f(a) = b$ with truncated $\exists$. It is an *embedding* if every $\mathsf{ap}_f : (x = y) \to (f x = f y)$ is an equivalence. For sets this gives the usual injection. **Theorem 4.6.3:** $f$ is an equivalence iff it is both surjective and an embedding. Unlike for sets, the book avoids the words "injective" and "epimorphism" for general types because those notions are ill-behaved there. Also notable: with univalence, *not every surjection is split*, which is why the axiom of choice (§3.8) is a real axiom.

**Closure (§4.7).**
- Theorem 4.7.1: 2-out-of-3.
- Theorem 4.7.4: a retract of an equivalence is an equivalence (Definition 4.7.2 defines retracts of maps, which induce retracts of fibers, Lemma 4.7.3).
- Theorem 4.7.7: a fiberwise transformation $f : \prod_{x:A} P(x) \to Q(x)$ is a fiberwise equivalence iff $\mathsf{total}(f)$ is an equivalence of total spaces, via $\mathsf{fib}_{\mathsf{total}(f)}((x,v)) \simeq \mathsf{fib}_{f(x)}(v)$ (Theorem 4.7.6).

**The object classifier (§4.8).** Lemma 4.8.1 says $\mathsf{fib}_{\mathsf{pr}_1}(a) \simeq B(a)$, and Lemma 4.8.2 says $A \simeq \sum_{b:B} \mathsf{fib}_f(b)$. Together with univalence they give

$$\chi : \Big(\sum_{A:\mathcal U} (A \to B)\Big) \simeq (B \to \mathcal U).$$

"Every map is equivalent to a fibration", and families over $B$ are the same as types over $B$. Theorem 4.8.4 states the pullback square with $\mathcal U_\bullet = \sum_{A:\mathcal U} A$.

## 6. Function extensionality (§2.9)

The base theory of Chapter 1 produces only a function

$$\mathsf{happly} : (f = g) \to \prod_{x:A} f(x) =_{B(x)} g(x)$$

by path induction, with no converse. Axiom 2.9.3 (function extensionality) asserts that $\mathsf{happly}$ is an equivalence, giving a quasi-inverse $\mathsf{funext}$. The book sets this out as the usual rule triple:

- introduction: $\mathsf{funext}$,
- elimination: $\mathsf{happly}$,
- propositional computation: $\mathsf{happly}(\mathsf{funext}(h), x) = h(x)$,
- propositional uniqueness: $p = \mathsf{funext}(x \mapsto \mathsf{happly}(p, x))$.

Pointwise operations compute identity and inverses on $\Pi$-types, e.g. $\alpha^{-1} = \mathsf{funext}(x \mapsto \mathsf{happly}(\alpha, x)^{-1})$.

## 7. The univalence axiom (§2.10)

Identity types in a universe $\mathcal U$ have a canonical map out of $A =_{\mathcal U} B$.

**Lemma 2.10.1.** $\mathsf{idtoeqv} : (A =_{\mathcal U} B) \to (A \simeq B)$, defined by transport along the identity family $X \mapsto X$ (a path $p$ induces $p_* : A \to B$, which is an equivalence because it is $\mathsf{id}_A$ on $\mathsf{refl}$).

**Axiom 2.10.3 (Univalence).** For $A, B : \mathcal U$, $\mathsf{idtoeqv}$ is an equivalence, hence

$$(A =_{\mathcal U} B) \;\simeq\; (A \simeq B).$$

A universe satisfying this is called *univalent*. The book assumes all universes are univalent unless stated otherwise. As with function extensionality, the axiom is split into an introduction rule $\mathsf{ua} : (A \simeq B) \to (A =_{\mathcal U} B)$, the elimination rule $\mathsf{idtoeqv} \equiv \mathsf{transport}^{X \mapsto X}$, and the propositional computation and uniqueness rules

$$\mathsf{transport}^{X \mapsto X}(\mathsf{ua}(f), x) = f(x), \qquad p = \mathsf{ua}(\mathsf{transport}^{X\mapsto X}(p)).$$

It identifies the operations: $\mathsf{refl}_A = \mathsf{ua}(\mathsf{id}_A)$, $\mathsf{ua}(f) \cdot \mathsf{ua}(g) = \mathsf{ua}(g \circ f)$, and $\mathsf{ua}(f)^{-1} = \mathsf{ua}(f^{-1})$. Lemma 2.10.5 is the working form: $\mathsf{transport}^B(p, u) = \mathsf{idtoeqv}(\mathsf{ap}_B(p))(u)$.

Why the definition of $\simeq$ matters: Exercise 4.6(iii) shows that the version of univalence stated with $\mathsf{qinv}$ is inconsistent. This is the payoff of §4.

## 8. Univalence implies function extensionality (§4.9)

This section works *without* assuming function extensionality. The route has two steps.

1. **Weak function extensionality** (Definition 4.9.1): $\big(\prod_{x:A} \mathsf{isContr}(P(x))\big) \to \mathsf{isContr}\big(\prod_{x:A} P(x)\big)$.
   Under univalence, post-composition with an equivalence is an equivalence $(X \to A) \simeq (X \to B)$ (Lemma 4.9.2). For a family of contractible types, $\mathsf{pr}_1$ is an equivalence, so $\alpha : (A \to \sum_{x:A} P(x)) \simeq (A \to A)$ (Corollary 4.9.3), and $\prod_x P(x)$ is a *retract* of the contractible fiber $\mathsf{fib}_\alpha(\mathsf{id}_A)$ (Theorem 4.9.4).
2. **Weak funext implies funext** (Theorem 4.9.5), with no appeal to univalence. Via Theorem 4.7.7 it suffices to show $\sum_g \prod_x f(x) = g(x)$ is contractible, and this is a retract of $\prod_x \sum_{u:P(x)} f(x) = u$, which is contractible by weak funext.

Exercise 4.9 refines this: the naive non-dependent funext already implies the full axiom.

## 9. Grounding in code

Types-as-data, with laws expressed only as tests or proofs.

### Rust: an equivalence is data you can compare only up to testing

```rust
/// Data of a quasi-inverse. The laws (g∘f ~ id, f∘g ~ id) are not expressible in the
/// Rust type system; we can only check them on samples. In HoTT they are *part of the data*.
struct QInv<A, B> {
    f: Box<dyn Fn(A) -> B>,
    g: Box<dyn Fn(B) -> A>,
}

impl<A: Clone + PartialEq, B: Clone + PartialEq> QInv<A, B> {
    fn check_on(&self, xs: &[A], ys: &[B]) -> bool {
        xs.iter().all(|x| (self.g)((self.f)(x.clone())) == *x)
            && ys.iter().all(|y| (self.f)((self.g)(y.clone())) == *y)
    }
}
```

This is exactly the situation of a proof-checker's *trusted kernel*: the host language gives you functions, and the kernel must separately certify the laws. An equivalence in a kernel is a pair of terms *plus* terms inhabiting the homotopies. For a checker, $\mathsf{isequiv}$ being a mere proposition means the certificate is canonical and the kernel need not compare two different certificates.

### Python: why $\mathsf{qinv}$ has too many witnesses

```python
# 2 ≃ 2 has two equivalences: id and swap. Both carry a (g, η, ε); for each f there is,
# up to the choice of inverse data, a "loop at every point" worth of extra choice.
swap = {False: True, True: False}
ident = {False: False, True: True}

def is_qinv(f, g, dom):
    return all(g[f[x]] == x for x in dom) and all(f[g[y]] == y for y in dom)

assert is_qinv(swap, swap, [False, True])
assert is_qinv(ident, ident, [False, True])
```

In set-like settings the inverse is determined by $f$, so $\mathsf{qinv}(f)$ is a mere proposition. The counterexample of Theorem 4.1.3 needs a type $X$ with non-trivial loops (here, $X = K(\mathbb Z_2,1)$), where $\prod_{x:X} x = x$ has a non-trivial element. Python's `dict` equality cannot see that structure, which is the point: it only exists once identity types are non-trivial.

### Lean 4: proof irrelevance collapses the whole discussion

```lean
structure QInv {A B : Type} (f : A → B) where
  g : B → A
  η : ∀ x, g (f x) = x
  ε : ∀ y, f (g y) = y

-- The half-adjoint coherence is provable by proof irrelevance, since equalities of
-- `Eq` proofs hold definitionally: no 2-dimensional data to manage.
example {A B : Type} (f : A → B) (q : QInv f) :
    ∀ x, congrArg f (q.η x) = q.ε (f x) := fun _ => rfl
```

In Lean, `Eq` lives in `Prop` and any two proofs of an equality are definitionally equal, so *every* equivalence notion above collapses to the same thing and $\mathsf{qinv}$ is not a problem. This is also why univalence is **false** in Lean for `Type`: $\mathbf 2 \simeq \mathbf 2$ has two distinct elements, but `Bool = Bool` has only one proof up to proof irrelevance, so $\mathsf{ua}$ could not be injective. Lean does have `propext` (univalence for propositions, a special case) and proves `funext` from a quotient construction, so function extensionality *is* available. Lean's `Equiv` structure (`toFun`, `invFun`, `left_inv`, `right_inv`) is precisely $\mathsf{qinv}$.

## 10. Synthesis

**What this topic depends on.** Homotopies, transport, $\mathsf{ap}$ and the path-space characterizations of $\Sigma$- and $\Pi$-types (§§2.2–2.7), contractibility and mere propositions (§3.3, §3.11), and truncation (§3.7).

**What depends on it.**
- Almost everything later. [[Higher-Inductive-Types|Higher inductive types]] (Chapter 6) and truncation levels (Chapter 7) are all stated via equivalences and contractible fibers.
- The structure identity principle and univalent categories (Chapter 9) are applications of univalence.
- Homotopy-initial algebras (Chapter 5) use the same "equivalence, not mere iso" discipline.

```
qinv(f) ⇄ biinv(f) ⇄ ishae(f) ⇄ isContr(f)         (all pairwise equivalent, all mere propositions
   │                                                except qinv)
   └── not a mere proposition (Thm 4.1.3) ── hence unsuitable inside Axiom 2.10.3
                                    univalence ⟹ funext  (§4.9)
```

**Bearing on the learning goals (Focus Area: `type-theory`).**
- *Definitional vs. propositional equality.* The $\beta$/$\eta$-style computation rules for $\mathsf{funext}$ and $\mathsf{ua}$ hold only *propositionally* in this book. This is the central obstruction to a computational (canonicity-preserving) univalence, and it is exactly what a kernel's `isDefEq` would have to be extended to handle if you wanted to implement univalence rather than just postulate it. For the refinement-type compiler the practical lesson is to *not* aim for univalence: with Lean-like proof-irrelevant `Eq` the whole theory in this note collapses, which is the more tractable design.
- *Proof-producing architecture.* "$\mathsf{isequiv}$ is a mere proposition" is the HoTT version of "a certificate has at most one canonical form". When a checker stores proof terms, the choice between $\mathsf{qinv}$ and $\mathsf{ishae}$ is a choice about whether certificate comparison is meaningful. Under proof irrelevance this question disappears.
- *Elaboration.* Corollary 4.4.6 ("you may assume the codomain is inhabited") is the sort of side-condition lemma an elaborator exploits when unfolding goals about maps. $\mathsf{total}(f)$ and the fiberwise-equivalence theorem (Theorem 4.7.7) correspond to reasoning about $\Sigma$-types fiberwise.
- *Not load-bearing for the compiler.* The object classifier, surjection/embedding characterization and §4.9 are conceptually central to HoTT but have no direct mechanism payoff for the refinement-type or CSP targets, so no project note is attached to them.

**Source notes.** All formal statements above were checked against pp. 76–79, 86–91 and 129–148 of the book. The code snippets are original illustrations; the Rust, Python and Lean snippets were not compiled or run.
