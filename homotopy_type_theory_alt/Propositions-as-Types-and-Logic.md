---
title: Propositions as Types and Logic
source: Homotopy Type Theory — Univalent Foundations of Mathematics (The Univalent Foundations Program, IAS 2013)
chapters: "Ch. 1 §1.11 (pp. 41–47); Ch. 3 §§3.2–3.11 (pp. 109–126)"
focus-areas: [automated-reasoning, type-theory]
tags: [hott, propositions-as-types, mere-propositions, truncation, lem, axiom-of-choice, contractibility]
---

[[book-guidelines|↩ Back to guidelines]]

# Propositions as Types and Logic

## 1. The problem this topic solves

A proof checker and a type checker are the same machine if you let a proposition be a type and a proof be a program of that type. Chapter 1 adopts this reading. It is simple, constructive and computational.

Chapter 3 then asks what happens when this reading meets two other things in the book: **univalence**, and the wish to still do ordinary, classical-looking mathematics. The answer is that the naive reading is too rich. An element of a type carries *data*, while a classical proposition carries only a truth value. The chapter separates the two by singling out the types that carry no extra data, the **mere propositions**. It then adds one type former, **propositional truncation** $\|A\|$, to recover a traditional "or" and "there exists".

The rest of this note follows that arc:

```
§1.11 naive reading ──► §3.2 it clashes with univalence ──► §3.3 restrict to mere propositions
                                                                   │
        §3.7 truncation recovers ∨, ∃ ◄── §3.6 which connectives survive? ◄─┘
                 │
                 ├─► §3.4 LEM, decidability     ├─► §3.8–3.9 choice, unique choice
                 └─► §3.10 which logic is the default?      §3.11 contractibility
```

## 2. The naive reading (§1.11)

The book is careful about terminology. An element of the type for a proposition is called a **witness** or evidence. "Proof" is avoided because it can mislead. A proposition is *the collection of all its witnesses*, and witnesses are mathematical objects like any other.

| Logic | Type | Rust analogue |
|---|---|---|
| True | $\mathbf{1}$ | `()` |
| False | $\mathbf{0}$ | an uninhabited enum, `std::convert::Infallible` |
| $A$ and $B$ | $A \times B$ | `(A, B)` |
| $A$ or $B$ | $A + B$ | `enum Sum<A, B> { Inl(A), Inr(B) }` |
| if $A$ then $B$ | $A \to B$ | `Box<dyn Fn(A) -> B>` |
| $A \iff B$ | $(A \to B) \times (B \to A)$ | a pair of closures |
| not $A$ | $A \to \mathbf{0}$, written $\neg A :\equiv A \to \mathbf{0}$ | `Box<dyn Fn(A) -> Infallible>` |
| for all $x : A$, $P(x)$ | $\prod_{x:A} P(x)$ | a dependent function, which Rust cannot express directly |
| exists $x : A$, $P(x)$ | $\sum_{x:A} P(x)$ | a dependent pair, which Rust cannot express directly |

The book's point is that, in each row, the rules for *constructing and using* elements of the type are the rules for *reasoning* about the proposition. To prove "$A$ and $B$" you prove both, which is a pair $(a, b)$. To use it you may use both, which is the induction principle of $A \times B$. To use an implication, "deduce $B$ if we know $A$", is function application. The book even remarks on the "convenient coincidence of the phrase 'applying a function' with that of 'applying a hypothesis'".

### 2.1 A worked translation: de Morgan

The book translates an English proof of "if not $A$ and not $B$, then not ($A$ or $B$)" step by step, building the term while reading the prose. The type is

$$(A \to \mathbf{0}) \times (B \to \mathbf{0}) \to (A + B \to \mathbf{0}).$$

Each phrase in the proof introduces or eliminates a type former:

- "Suppose not $A$ and not $B$" defines a function out of a product and introduces hypotheses $x : A \to \mathbf{0}$ and $y : B \to \mathbf{0}$ (pattern matching on the pair).
- "Also suppose $A$ or $B$" is another $\lambda$, introducing $z : A + B$.
- "There are two cases" is the recursion principle of $A + B$.
- "Contradiction from $a : A$ and $x$" is the application $x(a)$.

The result is $f((x,y))(\mathsf{inl}(a)) :\equiv x(a)$ and $f((x,y))(\mathsf{inr}(b)) :\equiv y(b)$. In Rust:

```rust
use std::convert::Infallible as Void;

enum Sum<A, B> { Inl(A), Inr(B) }

// (A → 0) × (B → 0) → (A + B → 0)
fn de_morgan<A, B>(
    (x, y): (impl Fn(A) -> Void, impl Fn(B) -> Void),
) -> impl Fn(Sum<A, B>) -> Void {
    move |z| match z {
        Sum::Inl(a) => x(a),
        Sum::Inr(b) => y(b),
    }
}
```

In Lean the same term is a one-line `fun ⟨x, y⟩ z => z.elim x y`, and in Python it is an `if isinstance` chain with no useful static check. The Rust version type-checks, so rustc has just checked a proof, though only for a propositional fragment, since Rust has no dependent types.

The converse direction, $((A+B) \to \mathbf{0}) \to (A \to \mathbf{0}) \times (B \to \mathbf{0})$, is the book's suggested exercise.

### 2.2 What is *not* provable

The type $((A \times B) \to \mathbf{0}) \to (A \to \mathbf{0}) + (B \to \mathbf{0})$ has no uniform inhabitant. That is the other de Morgan law, and it needs classical logic. Likewise $\neg\neg A \to A$ has no general construction. Two points the book makes carefully:

- **Proof of a negation by contradiction is fine.** To prove $\neg A$ you assume $x : A$ and derive $\mathbf{0}$. That is just constructing a function $A \to \mathbf{0}$. What is *not* valid is assuming $\neg A$ to prove $A$. That only yields $\neg\neg A$.
- $\neg\neg\neg A \to \neg A$ **is** provable (Exercise 1.11). Double negation elimination holds for negated statements.

Constructive logic is "constructive" in that every witness has computational meaning. This also gives **axiomatic freedom**. Since LEM is not refutable in the basic theory, it can be consistently *added*. Type theory enriches classical practice rather than constraining it.

### 2.3 Quantifiers, and $\Sigma$ as subtype

Here types play a dual role, as propositions and as the domains being quantified over. A predicate on $A$ is a family $P : A \to \mathcal{U}$. The book's examples:

- $(n \le m) :\equiv \sum_{k:\mathbb{N}} (n + k = m)$.
- $(n < m) :\equiv \sum_{k:\mathbb{N}} (n + \mathsf{succ}(k) = m)$, which is equivalent to $(n \le m) \times \neg(n = m)$ because $\mathbb{N}$ has decidable equality.
- A semigroup as $\sum_{A:\mathcal{U}} \sum_{m : A \to A \to A} \prod_{x,y,z:A} m(x, m(y,z)) = m(m(x,y),z)$, so axioms are part of the type of structures.

The same $\sum_{x:A} P(x)$ can be read as "there exists $x$ with $P(x)$" or as "the type of $x$ such that $P(x)$", a subtype. That ambiguity is the seed of the rest of the chapter.

## 3. When the naive reading breaks (§3.2)

Under the naive reading the statement that *looks like* the axiom of choice,

$$\Big(\prod_{x:X} \sum_{a:A(x)} P(x,a)\Big) \to \sum_{g : \prod_{x:X} A(x)} \prod_{x:X} P(x, g(x)),$$

is simply *provable* (Theorem 2.15.7). That differs from classical logic, where choice is a separate axiom. Conversely, the statements that look like classical principles are **refutable** once univalence is assumed.

**Theorem 3.2.2.** It is not the case that $\prod_{A:\mathcal{U}} \neg\neg A \to A$.

*Proof idea (as in the book).* Every function in type theory is "continuous", so by univalence a function $f : \prod_{A:\mathcal{U}} (\neg\neg A \to A)$ must be *natural* with respect to equivalences. Take the swap equivalence $e : \mathbf{2} \simeq \mathbf{2}$ and its path $p :\equiv \mathsf{ua}(e)$. Transport along $p$ forces $e(f(\mathbf{2})(u)) = f(\mathbf{2})(u)$. But $e$ has no fixed points, i.e. $\prod_{x:\mathbf{2}} \neg(e(x) = x)$, which gives an element of $\mathbf{0}$.

**Corollary 3.2.7.** It is not the case that $\prod_{A:\mathcal{U}} A + \neg A$. The proof reduces it to Theorem 3.2.2.

**Remark 3.2.5.** There is no Hilbert-style choice operator selecting an element of every nonempty type. No such operator could be natural with respect to equivalences, and under univalence every function on types must be.

So the unrestricted naive reading is *incompatible with leaving classical reasoning available*. The book wants to keep univalence, classical reasoning as an option, and the good properties of propositions-as-types (simplicity, constructivity, computability).

## 4. Mere propositions (§3.3)

**The diagnosis.** A witness of $\mathbf{2}$ carries one bit more than "$\mathbf{2}$ is inhabited": it tells you *which* element. A witness of $\mathbf{1}$ carries nothing beyond inhabitation. Classical logic only has the second kind.

**Definition 3.3.1.** $P$ is a *mere proposition* if any two elements are equal:

$$\mathsf{isProp}(P) :\equiv \prod_{x,y:P} (x = y).$$

This is itself a type, so "$P$ is a mere proposition" means exhibiting an inhabitant, which is a function connecting any two elements of $P$ by a path. Because that function is natural, $P$ also has no higher homotopy.

Key lemmas, with their roles:

| Result | Statement | Why it matters |
|---|---|---|
| Lemma 3.3.2 | inhabited mere proposition $\;P \simeq \mathbf{1}$ | so a mere proposition is either empty or contractible |
| Lemma 3.3.3 | mere propositions $P$, $Q$ with $P \to Q$ and $Q \to P$ satisfy $P \simeq Q$ | logical equivalence *is* equivalence (propositional extensionality, derived) |
| Lemma 3.3.4 | every mere proposition is a set | proof via $\mathsf{apd}$ and transport in path types |
| Lemma 3.3.5 | $\mathsf{isProp}(A)$ and $\mathsf{isSet}(A)$ are mere propositions | proofs by function extensionality |

Alternative names the book lists: subterminal object, subsingleton, h-proposition, and $(-1)$-type (Chapter 7). The adjective "mere" stresses that a witness carries no more than its truth.

**Grounding.** In Lean, `Prop` is the universe of exactly these types, with **definitional proof irrelevance**: any two proofs of the same `Prop` are `rfl`-equal. HoTT does not bake this in. It is a *property* ($\mathsf{isProp}$) that a type may or may not have, and it is propositional, not definitional. This is a real difference when you design a kernel. In Lean, `isDefEq` can discard proofs, whereas in HoTT's setting you would carry the path.

```lean
-- Lean: proof irrelevance is built into the kernel for Prop
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

-- HoTT-style "isProp" as an ordinary Type-level predicate (a mere proposition in Lean 4 terms)
def IsMereProp (α : Sort u) : Prop := ∀ x y : α, x = y
```

```python
# Python: a rough analogy — a type with at most one observable value
# (None-like). There is nothing to check; this is only a mental model.
class MereProp:
    def __eq__(self, other): return isinstance(other, MereProp)
```

## 5. Which connectives preserve mere propositions? (§3.6)

The traditional logic is recovered by restricting each type former to mere propositions, *when it preserves them*:

| Former | Preserves mere propositions? | Reason |
|---|---|---|
| $A \times B$ | yes | paths in products (Example 3.6.1) |
| $\prod_{x:A} B(x)$ with each $B(x)$ a mere proposition | yes | function extensionality (Example 3.6.2) |
| $A \to B$ with $B$ a mere proposition | yes, **regardless of $A$** | special case of the above |
| $\neg A$ | yes | $\mathbf{0}$ is a mere proposition |
| $A + B$ | **no** | $\mathbf{1}$ is a mere proposition, but $\mathbf{2} = \mathbf{1} + \mathbf{1}$ is not |
| $\sum_{x:A} P(x)$ | **no** in general | remembers the witness $x$ |

Thus $\wedge$, $\Rightarrow$, $\neg$ and $\forall$ are the "pure" connectives. $+$ is a "purely constructive" or: its witness says *which* disjunct holds. $\Sigma$ is a purely constructive exists: its witness *is* the witness. To get the classical ones you must forget that information.

## 6. Propositional truncation (§3.7)

For any type $A$ the **propositional truncation** (also bracket type, squash type, $(-1)$-truncation) is a type $\|A\|$ with two constructors:

1. $|a| : \|A\|$ for each $a : A$.
2. $x = y$ for all $x, y : \|A\|$. This is a *path constructor* that forces $\|A\|$ to be a mere proposition.

**Recursion principle.** If $B$ is a mere proposition and $f : A \to B$, there is $g : \|A\| \to B$ with $g(|a|) \equiv f(a)$. Informally, *anything that follows from inhabitation of $A$ and is itself a mere proposition follows from $\|A\|$*. The induction principle exists but is not especially useful (Exercise 3.17).

The book assumes it as an extra rule in this chapter, and constructs it later as a higher inductive type (§6.9).

**Traditional notation (Definition 3.7.1).** For mere propositions $P$ and $Q$:

$$\top :\equiv \mathbf{1},\quad \bot :\equiv \mathbf{0},\quad P \wedge Q :\equiv P \times Q,\quad P \Rightarrow Q :\equiv P \to Q,\quad P \Leftrightarrow Q :\equiv (P = Q),\quad \neg P :\equiv P \to \mathbf{0},$$

$$P \vee Q :\equiv \|P + Q\|,\qquad \forall (x{:}A).\,P(x) :\equiv \prod_{x:A} P(x),\qquad \exists (x{:}A).\,P(x) :\equiv \Big\|\sum_{x:A} P(x)\Big\|.$$

Note the book's definition $P \Leftrightarrow Q :\equiv (P = Q)$, which is legitimate because of Lemma 3.3.3 plus univalence. Subsets get the usual $\cap$, $\cup$, and "complement" $A \setminus \{x \mid P(x)\} :\equiv \{x \mid \neg P(x)\}$, though without LEM that complement need not satisfy $B \cup (A \setminus B) = A$.

**Using a truncated hypothesis.** If you hold $u : \|A + B\|$ and want to prove a *mere proposition* $Q$, you may case-split on $A + B$ after all, because the recursion principle reduces the goal to $A + B \to Q$. Likewise with $\big\|\sum_{x:A} P(x)\big\|$ you may introduce $x : A$ and $y : P(x)$, as long as the goal does not depend on *which* $x$. A mere-proposition codomain encodes exactly that independence.

**Grounding in Lean.** This is the same restriction Lean imposes on `Exists`: you can eliminate `∃ x, P x` only into `Prop`.

```lean
-- Lean's Exists is a Prop-valued ∃; Exists.elim only targets Prop.
example (P : Nat → Prop) (Q : Prop)
    (h : ∃ n, P n) (k : ∀ n, P n → Q) : Q :=
  h.elim k

-- And the "squash" of a *Type* is Nonempty (Prop), or Trunc in Quotient land:
example (α : Type) (a : α) : Nonempty α := ⟨a⟩
-- You cannot extract `a` back out into Type from Nonempty α:
-- the analogue of "you cannot define data out of ‖A‖".
```

In Rust there is no truncation, but you can approximate the *interface*: an opaque wrapper whose only elimination consumes a function returning a unit-like proof token.

```rust
// Analogy only: a "squash" type with no way to recover the A.
pub struct Squash<A>(std::marker::PhantomData<A>);
impl<A> Squash<A> {
    pub fn new(_a: A) -> Self { Squash(std::marker::PhantomData) }
    // Elimination is only allowed into a proposition-like target (here: ()).
    pub fn elim(self, _check: impl FnOnce(A)) {}
}
```

This analogy is imperfect. Rust cannot enforce *independence of the result from the witness*, and there is no equality type to make $\|A\|$ a mere proposition.

## 7. Excluded middle, double negation, decidability (§3.4)

With mere propositions the *correct* formulations are:

$$\mathsf{LEM} :\equiv \prod_{A:\mathcal{U}} \big(\mathsf{isProp}(A) \to (A + \neg A)\big),\qquad \mathsf{LEM}_\infty :\equiv \prod_{A:\mathcal{U}} (A + \neg A).$$

The book also gives the matching law of double negation and notes (Exercise 3.18) that they are equivalent. $\mathsf{LEM}_\infty$ is refutable under univalence (Cor. 3.2.7). $\mathsf{LEM}$ is *not* a consequence of the basic theory but can be assumed consistently, as in §10.4.

The book's practical advice:

- Replace "nonempty" by "inhabited" (or "merely inhabited"), which removes a double negation.
- Rephrase proofs by contradiction into direct proofs when possible.
- Remember that proof by contradiction for a *negative* goal never needs LEM.

**Definition 3.4.3.** $A$ is **decidable** if $A + \neg A$. A family $B : A \to \mathcal{U}$ is decidable if $\prod_{a:A}(B(a) + \neg B(a))$. $A$ has **decidable equality** if $\prod_{a,b:A}((a = b) + \neg(a = b))$. So LEM says exactly that all mere propositions are decidable. Decidable equality is very strong (Theorem 7.2.5, Hedberg).

Lean's `Decidable p` is this definition, as a `Type`-valued class, and it is what powers `if`, `decide` and `match` on propositions. `Classical.em` is the Prop-level LEM, and in HoTT terms that is $\mathsf{LEM}_{-1}$, not $\mathsf{LEM}_\infty$.

```lean
-- Decidable ≈ A + ¬A (data!). Classical.em ≈ LEM for propositions only.
#check (Decidable : Prop → Type)
#check @Classical.em   -- ∀ (p : Prop), p ∨ ¬p
```

## 8. Subsets and propositional resizing (§3.5)

If each $P(x)$ is a mere proposition, then $\sum_{x:A} P(x)$ behaves like a subset. **Lemma 3.5.1** says that two elements with equal first components are equal, so there is no hidden duplication from multiple proofs. The notation $\{x : A \mid P(x)\}$ is used for such families. Examples are $\mathsf{Set}_{\mathcal{U}} :\equiv \{A : \mathcal{U} \mid \mathsf{isSet}(A)\}$ and $\mathsf{Prop}_{\mathcal{U}} :\equiv \{A : \mathcal{U} \mid \mathsf{isProp}(A)\}$. For example, $\mathsf{isequiv}(f)$ is a mere proposition, so two equivalences with equal underlying functions are equal.

**Axiom 3.5.5 (Propositional resizing).** $\mathsf{Prop}_{\mathcal{U}_i} \to \mathsf{Prop}_{\mathcal{U}_{i+1}}$ is an equivalence. It is a form of impredicativity, implied by LEM, and *not assumed by default*. The motivation is to have $\Omega : \mathcal{U}$ classifying all mere propositions, and a universe-independent power set $\mathcal{P}(A) :\equiv (A \to \Omega)$. Without resizing, the type theory stays *predicative*.

Contrast with Lean: `Prop` is *impredicative* by design, so `∀ x : α, p x : Prop` regardless of the universe of `α`. In HoTT the book's default is the predicative setting, and resizing is an explicit hypothesis.

## 9. The axiom of choice and unique choice (§§3.8–3.9)

**Axiom of choice.** For a set $X$, families $A(x)$ that are sets and $P(x,a)$ that are mere propositions:

$$\Big(\prod_{x:X} \Big\|\sum_{a:A(x)} P(x,a)\Big\|\Big) \to \Big\|\sum_{g:\prod_{x:X}A(x)}\prod_{x:X}P(x,g(x))\Big\|.$$

The truncation appears *twice*. The domain truncation says choices exist but are not specified. The codomain truncation says the choice function exists but is not specified. **Lemma 3.8.2** shows it is equivalent to $\prod_{x:X} \|Y(x)\| \to \big\|\prod_{x:X} Y(x)\big\|$ for sets $Y(x)$, i.e. "a product of nonempty sets is nonempty". Remark 3.8.4 gives the pitfall: $\prod$ preserves mere propositions but does **not** commute with truncation.

**$X$ must be a set.** Lemma 3.8.5 builds $X :\equiv \sum_{A:\mathcal{U}} \|\mathbf{2} = A\|$, a 1-type, with each $Y(x)$ a set but the choice principle false. So choice cannot be relaxed on the domain, and over a non-set (such as a universe) there is no consistent form of choice that lets you pick elements.

**Unique choice.** Lemma 3.9.1 says that a mere proposition $P$ satisfies $P \simeq \|P\|$. Hence **Corollary 3.9.2**: if each $P(x)$ is a mere proposition and each $\|P(x)\|$ holds, then $\prod_{x:A} P(x)$.

The reusable technique is *refine existence to unique existence*. You know only $\|A\|$ and want data in $B$. Add a predicate $Q : B \to \mathcal{U}$ such that $\sum_{x:B} Q(x)$ is a mere proposition, construct from $A$ an element of it, then get $\big\|\sum_{x:B}Q(x)\big\|$ from $\|A\|$. Finally project $B$ out, which is allowed because the Σ-type equals its own truncation. Lean's `Quot`/`Quotient.lift` and "construct data from `Nonempty`" workarounds follow the same pattern.

## 10. Which logic is the default? (§3.10)

The book argues that, perhaps surprisingly, *informal mathematics is often better described by the untruncated forms*. A construction that uses "the $x$ constructed in Theorem Y" uses the witness, which is not available from $\|\sum\|$. "$A$ is isomorphic to $B$" is usually proved by giving a specific isomorphism that is used later.

On the other hand, truncated logic is essential for LEM and AC. The book introduces *adverbs* as modality names: "there **merely** exists" for $\|\sum_{x:A} P(x)\|$, "merely inhabited" for $\|A\|$, and "purely" or "actually" to emphasize no truncation.

**Default in the book: untruncated.** Reasons given: it encourages experimentation, avoids set theory's "abuse of language", mere propositions are not fundamental but the second rung of the $n$-type ladder (Ch. 7), many classical mere propositions (equality first of all) are not mere propositions here, many types are mere propositions automatically (so truncation is unnecessary), and truncations are not used much for the mathematics of the book.

## 11. Contractibility (§3.11)

**Definition 3.11.1.** $\mathsf{isContr}(A) :\equiv \sum_{a:A}\prod_{x:A}(a = x)$, with *center of contraction* $a$ and contractions $\mathsf{contr}_x : a = x$.

**Lemma 3.11.3.** These are logically equivalent: (i) $A$ is contractible, (ii) $A$ is a mere proposition and has a point, (iii) $A \simeq \mathbf{1}$.

Consequences worth keeping:

- $\mathsf{isContr}(A)$ is a mere proposition (Lemma 3.11.4), and so is contractible whenever $A$ is.
- $\prod_{x:A}P(x)$ is contractible when every $P(x)$ is (Lemma 3.11.6). This statement is equivalent to function extensionality (§4.9).
- Retracts of contractible types are contractible (Lemma 3.11.7).
- **Lemma 3.11.8:** $\sum_{x:A}(a = x)$ is contractible, which is essentially based path induction. Pronounced "the space of paths with one free end is contractible".
- **Lemma 3.11.9** (the informal principle that *contractible data can be ignored*): if each $P(x)$ is contractible then $\sum_{x:A}P(x) \simeq A$, and if $A$ is contractible with center $a$ then $\sum_{x:A}P(x) \simeq P(a)$.
- **Lemma 3.11.10:** $A$ is a mere proposition iff every $x =_A y$ is contractible, which extends the $n$-type ladder one step down.

**Remark 3.11.2 (a trap).** Read topologically, $\sum_{a}\prod_{x}(a = x)$ sounds like *connectedness*. The "there exists a path" here is a continuous one. Connectedness is expressed with truncation: $\|A\|$ together with $\prod_{x,y:A}\|x = y\|$ (§7.5).

## 12. Synthesis

**Where it sits in the book.** This topic depends on §1.1–1.10 (the basic type formers), §1.12 and §2.1–2.4 (identity types, transport, equivalences), and function extensionality and univalence (§2.9–2.10), which are *used* in the proofs of Lemma 3.3.5 and Theorem 3.2.2. It feeds directly into:

```
mere propositions ─► (−1)-types, n-truncation, modalities   (Ch. 7)
isProp(isequiv f) ─► definition of equivalence               (Ch. 4)
truncation ─► HIT construction ‖A‖                           (§6.9), quotients (§6.10)
LEM, AC  ─► classical set theory and the reals               (Ch. 10, 11)
contractibility ─► path-induction, fibers, connectedness     (Ch. 4, 5, 7, 8)
```

**Load-bearing for the project (Focus Area `automated-reasoning`, with overlap into `type-theory`).** The tags for this topic are `automated-reasoning`; I also pulled in the shared `type-theory` connections where the book makes them.

- **Judgments and typing rules as a shared ancestor of type checker and proof checker.** §1.11 is the clearest statement of this thread. The table in §2 is the exact correspondence. A verifier for a refinement language is a checker that accepts a program as evidence of its specification. §2.1 is a worked example of *proof elaboration from prose*: each English phrase maps to introduction or elimination of one type former. The hole-based derivation ($\square$ placeholders refined step by step) is the same shape as the metavariable-based tactic and elaboration state in Lean's elaborator.
- **Proof certificates and trusted kernels.** The proof-relevant/proof-irrelevant distinction decides what a certificate *contains*. In HoTT's default reading a witness is data that the kernel must keep and compare. In Lean's `Prop`, `isDefEq` is allowed to ignore the proof. For a Rust kernel, deciding which types are "mere propositions" (erasable, definitionally irrelevant) versus data-carrying is a core design choice, with real impact on the trusted computing base and on proof reconstruction.
- **Dependent types, $\Pi$ and $\Sigma$.** The quantifier rows ($\prod$ for $\forall$, $\sum$ for $\exists$) and the subtype reading of $\Sigma$ are the basis for **refinement types**. $\{x : A \mid P(x)\}$ is precisely a refinement type when $P$ is a mere proposition: Lemma 3.5.1 is the statement that *refinement proofs do not affect equality*, which is why a compiler can erase them.
- **Decidability and constraint solving.** Definition 3.4.3 is the formal home of "this predicate can be discharged by a decision procedure". `Decidable` instances in Lean, and the dichotomy between $A + \neg A$ (data, usable in guards) and a mere $A \vee \neg A$, explain why verification conditions that fall into decidable theories can *drive control flow* while classical-only facts cannot. This is the interface where an SMT or CSP backend returns proofs to the elaborator, which is the `sat-smt-csp` hand-off, mentioned here only as a pointer since the book does not discuss solvers.
- **Elaboration and unification.** Not directly. The book does not discuss unification here. The only link is the hole-filling presentation in §2.1.

**Not claimed by the book, so not claimed here:** no discussion of algorithms for proof search, decision procedures, or kernel implementation appears in these sections. The Rust and Lean material above is illustration of the same ideas, not extracted content.

## 13. Self-check

1. Why is $\neg A :\equiv A \to \mathbf{0}$ allowed to be proved "by contradiction" but $A$ is not? What exactly can you conclude from assuming $\neg A$ and deriving $\mathbf{0}$?
2. What does Theorem 3.2.2 use from univalence, and why does it fail for the version with $\mathsf{isProp}(A)$ in the hypothesis?
3. Why is $A + B$ not a mere proposition even when $A$ and $B$ are, and how does $\|A + B\|$ repair that? What do you lose?
4. Why must the target of the recursion principle of $\|A\|$ be a mere proposition? Relate this to Lean's restriction on eliminating `Exists`.
5. Why does the axiom of choice need $X$ to be a set? Sketch Lemma 3.8.5.
6. Show that $\sum_{x:A}(a = x)$ is contractible and say what that has to do with based path induction.
