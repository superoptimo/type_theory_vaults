---
title: Fixpoint Abstraction
source: "Principles of Abstract Interpretation (Patrick Cousot, MIT Press, 2021)"
chapter: "Chapter 18 — Fixpoint Abstraction"
pages: "pp. 264–292"
tags: [abstract-interpretation, fixpoint-theory, galois-connection, soundness, completeness, closure-operator, structural-induction]
---

# Fixpoint Abstraction

[[book-guidelines|↩ Back to guidelines]]

## Why fixpoints need their own abstraction theory

Every earlier chapter's abstraction recipe was pointwise: take a concrete property $P$, apply $\alpha$, get the best abstract property $\alpha(P)$. That recipe works fine for a single static fact. It does not obviously work for the *meaning of a loop*. A `while` loop's semantics, an inductive/deductive definition's extension, a reachability set — all of these are defined in chapters 15–17 as a **least fixpoint** $\mathrm{lfp}^{\sqsubseteq} f$ of some concrete transformer $f$ on a complete lattice or CPO $\langle \mathcal{C}, \sqsubseteq \rangle$. You cannot compute $\mathrm{lfp}^{\sqsubseteq} f$ directly in a static analyzer — $\mathcal{C}$ is typically the powerset of program states, astronomically large or infinite. What you *can* compute is a fixpoint of some abstract transformer $\bar f$ on a small abstract domain $\langle \mathcal{A}, \preccurlyeq \rangle$. The question this chapter answers, precisely, is: **under what conditions does $\mathrm{lfp}^{\preccurlyeq} \bar f$ actually tell you something true about $\mathrm{lfp}^{\sqsubseteq} f$?**

**What breaks without this chapter:** without a theorem connecting the two fixpoints, computing an abstract fixpoint is just running an algorithm that terminates with *some* answer — you have no license to call that answer sound, let alone precise. This is not a hypothetical risk: it is entirely possible to write a plausible-looking abstract transformer whose fixpoint iteration converges to a value with no relationship at all to the concrete semantics, simply because the abstract operations were coded by informal analogy with the concrete ones rather than derived from them. Chapter 18 is the machinery that turns "I abstracted each operation" into "the abstract loop invariant I computed is provably a true fact about every concrete execution."

The chapter's own opening figure captures the whole chapter in one picture: given a concrete transformer $f$ and its concrete iterates $f^0 = \bot, f^1, f^2, \dots, f^\omega = \mathrm{lfp}^{\sqsubseteq} f$ on the left, and an abstract transformer $\bar f$ with abstract iterates $\bar f^0 = \alpha(\bot), \bar f^1, \dots$ on the right, there are exactly two possible outcomes: the picture *commutes* — $\alpha$ maps each concrete iterate exactly onto the corresponding abstract iterate, so $\alpha(\mathrm{lfp}^{\sqsubseteq} f) = \mathrm{lfp}^{\preccurlyeq} \bar f$ (**exact/complete abstraction**) — or it only *soundly bounds* — $\alpha(\mathrm{lfp}^{\sqsubseteq} f) \preccurlyeq \mathrm{lfp}^{\preccurlyeq} \bar f$, with the abstract fixpoint sitting strictly above what's needed (**sound overapproximation**).

<svg viewBox="0 0 900 380" xmlns="http://www.w3.org/2000/svg" font-family="Georgia, 'Times New Roman', serif" font-size="15">
  <rect x="0" y="0" width="900" height="380" fill="none"/>
  <!-- concrete column -->
  <text x="140" y="30" text-anchor="middle" font-weight="bold" fill="#4a6fa5">concrete: C</text>
  <circle cx="140" cy="70" r="5" fill="#4a6fa5"/>
  <text x="160" y="75" fill="#555">f&#8304; = &#8869;</text>
  <circle cx="140" cy="130" r="5" fill="#4a6fa5"/>
  <text x="160" y="135" fill="#555">f&#185;</text>
  <circle cx="140" cy="190" r="5" fill="#4a6fa5"/>
  <text x="160" y="195" fill="#555">f&#178;</text>
  <text x="140" y="230" fill="#888">&#8942;</text>
  <circle cx="140" cy="270" r="6" fill="#4a6fa5"/>
  <text x="160" y="275" fill="#333" font-weight="bold">f&#969; = lfp&#8849; f</text>
  <path d="M140,75 L140,125" stroke="#4a6fa5" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>
  <path d="M140,135 L140,185" stroke="#4a6fa5" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>
  <path d="M140,195 L140,264" stroke="#4a6fa5" stroke-width="1.5" fill="none" marker-end="url(#arrow)" stroke-dasharray="2,3"/>

  <!-- abstract column A -->
  <text x="420" y="30" text-anchor="middle" font-weight="bold" fill="#b5654a">abstract (exact): A</text>
  <circle cx="420" cy="70" r="5" fill="#b5654a"/>
  <text x="440" y="75" fill="#555">&#945;(&#8869;)</text>
  <circle cx="420" cy="130" r="5" fill="#b5654a"/>
  <text x="440" y="135" fill="#555">f&#772;&#185;</text>
  <circle cx="420" cy="190" r="5" fill="#b5654a"/>
  <text x="440" y="195" fill="#555">f&#772;&#178;</text>
  <text x="420" y="230" fill="#888">&#8942;</text>
  <circle cx="420" cy="270" r="6" fill="#b5654a"/>
  <text x="440" y="275" fill="#333" font-weight="bold">lfp&#8829; f&#772; = &#945;(lfp&#8849; f)</text>
  <path d="M420,75 L420,125" stroke="#b5654a" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>
  <path d="M420,135 L420,185" stroke="#b5654a" stroke-width="1.5" fill="none" marker-end="url(#arrow)"/>
  <path d="M420,195 L420,264" stroke="#b5654a" stroke-width="1.5" fill="none" marker-end="url(#arrow)" stroke-dasharray="2,3"/>
  <path d="M155,70 L400,70" stroke="#777" stroke-width="1.2" fill="none" marker-end="url(#arrow)"/>
  <text x="280" y="63" text-anchor="middle" fill="#777" font-size="13">&#945;</text>
  <path d="M155,130 L400,130" stroke="#777" stroke-width="1.2" fill="none" marker-end="url(#arrow)"/>
  <text x="280" y="123" text-anchor="middle" fill="#777" font-size="13">&#945;</text>
  <path d="M155,270 L400,270" stroke="#777" stroke-width="1.2" fill="none" marker-end="url(#arrow)"/>
  <text x="280" y="263" text-anchor="middle" fill="#777" font-size="13">&#945;   (commutes)</text>

  <!-- abstract column A' overapprox -->
  <text x="720" y="30" text-anchor="middle" font-weight="bold" fill="#7a8a53">abstract (sound only): A</text>
  <circle cx="720" cy="270" r="6" fill="#7a8a53"/>
  <text x="740" y="275" fill="#333" font-weight="bold">lfp&#8829; f&#772;</text>
  <path d="M155,270 L706,264" stroke="#999" stroke-width="1.2" fill="none" marker-end="url(#arrow2)"/>
  <text x="480" y="245" text-anchor="middle" fill="#999" font-size="13">&#945;(lfp&#8849; f) &#8829; lfp&#8829; f&#772;  (overapproximation, not equality)</text>

  <defs>
    <marker id="arrow" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#777"/>
    </marker>
    <marker id="arrow2" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto">
      <path d="M0,0 L6,3 L0,6 Z" fill="#999"/>
    </marker>
  </defs>
</svg>

Throughout, follow the book's own notation: $\bar f \in \mathcal{A} \to \mathcal{A}$ denotes an *arbitrary* candidate abstract transformer (whatever an analyzer actually implements), while $\vec\alpha(f) \triangleq \alpha \circ f \circ \gamma$ denotes the *canonical, calculated* abstraction of $f$ — the transformer you'd get by concretizing, applying $f$, then re-abstracting. The whole chapter is about the relationship between an implemented $\bar f$ and this canonical $\vec\alpha(f)$.

## 1. Sound overapproximation of a concrete fixpoint

The soundness story has three layers, and it's worth keeping them separate because each one is a genuinely different failure mode to guard against.

### Layer 1 — is the transformer itself sound?

**Theorem 18.3 (sound transformer abstraction).** For $f \in \mathcal{C} \to \mathcal{C}$ and $\bar f \in \mathcal{A} \to \mathcal{A}$ increasing,
$$\vec\alpha(f) \mathrel{\dot\preccurlyeq} \bar f \iff f \mathrel{\dot\sqsubseteq} \vec\gamma(\bar f),$$
where $\vec\gamma(\bar f) \triangleq \gamma \circ \bar f \circ \alpha$ and $\dot\preccurlyeq$/$\dot\sqsubseteq$ are the pointwise orders on functions ($f \mathrel{\dot\sqsubseteq} g \iff \forall x.\, f(x) \sqsubseteq g(x)$). This says: $\bar f$ is a sound abstraction of $f$ exactly when it never returns *less* than what concretizing-then-applying-$f$-then-abstracting would give you. It's the pointwise analogue, at the level of transformers, of "$\alpha(P) \preccurlyeq a$ is sound" at the level of single properties — proved the same way, by unfolding the Galois-connection biconditional under a universal quantifier.

### Layer 2 — does a bigger transformer give a bigger fixpoint?

Before touching abstraction at all, section 18.2 asks a purely order-theoretic question in one lattice: if $f \mathrel{\dot\sqsubseteq} g$ (both increasing, on a complete lattice), does $\mathrm{lfp}^{\sqsubseteq} f \sqsubseteq \mathrm{lfp}^{\sqsubseteq} g$?

**Theorem 18.7.** Yes — and the proof is one line once you have [[Fixpoint-Theory#Tarski's fixpoint theorem|Tarski's fixpoint theorem]] (chapter 15) in hand: $\mathrm{lfp}^{\sqsubseteq} f = \bigsqcap\{x \mid f(x) \sqsubseteq x\}$, and $f \mathrel{\dot\sqsubseteq} g$ makes every postfixpoint of $g$ a postfixpoint of $f$ (if $g(x) \sqsubseteq x$ then $f(x) \sqsubseteq g(x) \sqsubseteq x$), so $f$'s postfixpoint set is a *superset* of $g$'s, and a meet over a larger set is smaller-or-equal. **Corollary 18.8** weakens the hypothesis from "$f \mathrel{\dot\sqsubseteq} g$ everywhere" to "$f(x) \sqsubseteq x$ whenever $g(x) \sqsubseteq x$" — you only need the inequality to hold at postfixpoints of $g$, since that's all the proof actually uses. **Theorem 18.9** gives the Scott–Kleene iterate version for upper-continuous $f$: it suffices that $f(x) \sqsubseteq g(x)$ for $x$ below the fixpoint, i.e. only along the actual iteration path, proved by induction over the iterates $f^n(\bot)$ rather than over all of $\mathcal{C}$. This restriction-to-iterates move — "you don't need the property everywhere, only where the iteration actually visits" — recurs throughout the chapter and is the single biggest lever for turning an intractable-looking proof obligation into a tractable one.

### Layer 3 — composing layers 1 and 2 across the Galois connection

Plugging a sound transformer abstraction (layer 1) into the lfp-monotonicity result (layer 2) gives the chapter's central soundness theorem.

**Theorem 18.10.** For complete lattices $\mathcal{C}, \mathcal{A}$ and a Galois connection $\langle \mathcal{C}, \sqsubseteq \rangle \xrightleftharpoons[\gamma]{\alpha} \langle \mathcal{A}, \preccurlyeq \rangle$ with $f$ increasing:
$$\mathrm{lfp}^{\sqsubseteq} f \;\sqsubseteq\; \gamma\big(\mathrm{lfp}^{\preccurlyeq} \vec\alpha(f)\big).$$
Equivalently (**Corollary 18.14**, replacing $\vec\alpha(f)$ with any sound $\bar f \succcurlyeq \vec\alpha(f)$): $\mathrm{lfp}^{\sqsubseteq} f \sqsubseteq \gamma(\mathrm{lfp}^{\preccurlyeq} \bar f)$. The practically important reformulation is **Corollary 18.16 (semicommutation)**: it's *sufficient* — and easier to check locally, one operation at a time — that
$$\alpha \circ f \mathrel{\dot\preccurlyeq} \bar f \circ \alpha$$
i.e. abstracting-then-applying-$f$ never exceeds applying-$\bar f$-then-abstracting. This is the condition an implementer actually checks, primitive operation by primitive operation, rather than reasoning about the whole fixpoint at once — precisely the "local soundness of domain primitives implies global soundness" idea that chapter 19's generic abstract interpreter is built on. **Theorem 18.18** restates all of this for CPOs (needed because plenty of the book's concrete domains, like sets of finite/infinite traces, are CPOs rather than complete lattices), and **Theorem 18.21** further generalizes to the case where the *approximation ordering* used for soundness and the *calculational ordering* used to define the fixpoint are allowed to differ — a subtlety that matters once narrowing (chapter 23) enters the picture.

**What breaks without semicommutation:** if you implement each abstract primitive by hand-waving ("this feels like what interval addition should do") without checking $\alpha \circ f \mathrel{\dot\preccurlyeq} \bar f \circ \alpha$ at each one, unsoundness doesn't announce itself — the analyzer still terminates, still produces plausible-looking output, and the bug surfaces only when a real program is silently mis-analyzed as safe. Every one of the concrete domain chapters later in the book (signs, intervals, congruences, octagons, ...) discharges exactly this one inequality for each primitive operation, then invokes Corollary 18.16 once to get global soundness for free.

### Worked example: sign abstraction of an affine recurrence

Exercise 18.29 asks you to abstract $F(X) \triangleq \{1\} \cup \{z + 2 \mid z \in X\}$ on $\wp(\mathbb{Z})$ into the sign domain $\mathbb{P}_\pm$ from chapter 3. Concretely, $\mathrm{lfp}^{\subseteq} F = \{1, 3, 5, 7, \dots\}$ — the positive odd integers, since $F$ never produces anything else. The abstract transformer, calculated as $\bar F \triangleq \vec\alpha_\pm(F) = \alpha_\pm \circ F \circ \gamma_\pm$, works out to $\bar F({>}0) = {>}0$ (adding 2 to a positive number stays positive) and its fixpoint from $\bot_\pm$ converges to ${>}0$ in two iterations: $\bar F(\bot_\pm) = {=}0$ (from the singleton $\{1\}$), $\bar F({=}0) = {>}0$, $\bar F({>}0) = {>}0$. So $\alpha_\pm(\mathrm{lfp}^{\subseteq} F) = {>}0 = \mathrm{lfp}^{\sqsubseteq_\pm} \bar F$ — this particular example is exact, not merely sound, which is a nice segue into the next section: exactness is possible, just not guaranteed by soundness alone.

### Grounding: soundness as a trait obligation in Rust

A worklist-based fixpoint solver over an abstract lattice makes Theorem 18.10 and Corollary 18.16 into a literal API contract:

```rust
trait AbstractDomain: PartialOrd + Clone {
    fn bottom() -> Self;
    fn join(&self, other: &Self) -> Self;
}

/// f̄ is sound for f iff, for every concrete x this transformer will
/// ever be applied to along the iteration, α(f(x)) ≼ f̄(α(x)).
/// The trait cannot enforce this mathematically — it is a proof
/// obligation the implementer discharges once per primitive, per
/// Corollary 18.16 (semicommutation), not something checked at runtime.
trait AbstractTransformer<A: AbstractDomain> {
    fn apply(&self, x: &A) -> A;
}

/// Kleene iteration lfp^≼ f̄ = ⋁ { f̄ⁿ(⊥) | n ∈ ℕ }, terminating once
/// the chain stabilizes (guaranteed on a finitary domain, chapter 15).
fn least_fixpoint<A, F>(transformer: &F) -> A
where
    A: AbstractDomain,
    F: AbstractTransformer<A>,
{
    let mut current = A::bottom();
    loop {
        let next = current.join(&transformer.apply(&current));
        if next <= current {
            return current; // reached lfp^≼ f̄ ⊒ α(lfp^⊑ f) by Theorem 18.10
        }
        current = next;
    }
}
```

The `join` in the loop body is doing real work: it is what makes the iterates $\bar f^n(\bot)$ increasing even when the hand-written `apply` isn't perfectly calculated, which is exactly the slack Theorem 18.7/18.9 needs — you don't require $\bar f = \vec\alpha(f)$ exactly, only $\bar f \succcurlyeq \vec\alpha(f)$ pointwise.

## 2. Exact and complete fixpoint abstraction by commutation

Soundness alone is a weak guarantee — $\top$ (the abstract domain's most imprecise element) trivially satisfies every soundness theorem above, and is useless. **Exactness** (the book also calls it *completeness*) is the much stronger, much harder-to-achieve property that the abstract fixpoint tells you *exactly* what the concrete fixpoint says, no more and no less.

**Definition (18.4, restated).** A sound fixpoint abstraction $\alpha(\mathrm{lfp}^{\sqsubseteq} f) \preccurlyeq \mathrm{lfp}^{\preccurlyeq} \bar f$ is **exact** when equality holds: $\alpha(\mathrm{lfp}^{\sqsubseteq} f) = \mathrm{lfp}^{\preccurlyeq} \bar f$.

**Theorem 18.23 (exact least fixpoint abstraction).** If $\alpha \circ f = \bar f \circ \alpha$ — the **commutation property**, also called **pointwise completeness** — then $\alpha(\mathrm{lfp}^{\sqsubseteq} f) = \mathrm{lfp}^{\preccurlyeq} \bar f$. Read the diagram: instead of a one-directional inequality (apply-then-abstract is *at most* abstract-then-apply), commutation demands the two paths around the square be *equal*, at every concrete $x$, not just at the fixpoint. That's why it's so much harder than soundness: soundness is a local ($\preccurlyeq$) constraint you can slacken by rounding outward; commutation is a local *equality* you cannot slacken at all.

The proof is short and instructive: from $\alpha \circ f \mathrel{\dot\sqsubseteq} \bar f \circ \alpha$ (the "$\sqsubseteq$" half of the equality) you already get $\mathrm{lfp}^{\preccurlyeq} \bar f \preccurlyeq \alpha(\mathrm{lfp}^{\sqsubseteq} f)$ by Corollary 18.16 run in the *other* direction — this is the surprising part, and it's exactly why commutation gives you both inequalities where semicommutation only gave you one. Antisymmetry closes the gap.

The chapter immediately weakens the hypothesis twice, in the direction of practicality:

- **Corollaries 18.34/18.35 (exact iterates abstraction).** You don't need $\alpha \circ f = \bar f \circ \alpha$ to hold on all of $\mathcal{C}$ — only along the actual iterates ($x \sqsubseteq \mathrm{lfp}^{\sqsubseteq} f$), the same "restrict to the iteration path" move from Layer 2 above. This matters because commutation is often false in general but true along the specific trajectory a given loop actually traces.
- **Theorem 18.27.** When $\langle \alpha, \gamma \rangle$ is a **Galois retraction** (i.e. $\alpha$ is surjective, so $\alpha \circ \gamma = 1_\mathcal{A}$ — no information is lost round-tripping through the abstract domain) and commutation holds along the iterates, then $\bar f = \vec\alpha(f)$ is *automatically* increasing and exact — you get monotonicity of the calculated transformer for free, rather than as a separate proof obligation.

### Reformulated via closure operators

Section 18.7 recasts everything using an **upper closure operator** $\rho = \gamma \circ \alpha$ (chapter 11's alternative, concretization-free formalization of an abstract domain as a set of concrete "representable" properties closed under meets). Commutation becomes two named, independently useful properties:

- **backward completeness**: $\rho \circ f = \rho \circ f \circ \rho$,
- **forward completeness**: $f \circ \rho = \rho \circ f \circ \rho$.

These names are worth remembering because they reappear, unmodified, in chapter 21's discussion of reduced products and domain refinement: a domain combinator is "backward complete" or "forward complete" with respect to a given transformer in *exactly* this fixpoint-commutation sense, not as a separate ad hoc notion.

### Worked example: transitive closure as an exact fixpoint abstraction

Exercise 18.30 is the cleanest illustration of why this section matters for the book's larger arc toward reachability analysis (chapter 19). Define the reflexive-transitive closure of a relation $r \subseteq S \times S$ as $r^* \triangleq \mathrm{lfp}^{\subseteq} F_r$ where $F_r(X) \triangleq \mathbb{1}_S \cup (X \circ r)$. Now abstract *relations* into *reachable-sets-from-$P$* via $\alpha_P(r) \triangleq \mathrm{post}[r]P = \{y \mid \exists x \in P.\, \langle x, y\rangle \in r\}$. Working through the algebra (the book does this in the chapter's solved exercises) shows
$$\alpha_P(F_r(X)) = P \cup \mathrm{post}[r](\alpha_P(X)),$$
which is exactly the commutation property $\alpha_P \circ F_r = \bar F \circ \alpha_P$ for $\bar F(Y) \triangleq P \cup \mathrm{post}[r]Y$. By Theorem 18.23, $\alpha_P(r^*) = \mathrm{lfp}^{\subseteq} \bar F$ — the set of nodes reachable from $P$ following $r$ is *exactly* (not just soundly) the least fixpoint of "start at $P$, repeatedly follow one more edge." This is precisely the fixpoint characterization that chapter 19's reachability semantics and chapter 25's graph path problems both instantiate: reachability analysis is, structurally, this exercise.

### Grounding: exactness as `isDefEq`, not just type-checking

This is the sharpest place in the chapter to connect to elaboration. A type checker that merely *checks* a candidate type against an expected one is doing something soundness-shaped: it accepts only when it can positively verify agreement, and rejects (conservatively) otherwise — a one-directional guarantee, like semicommutation. Lean's **definitional equality** decision procedure (`isDefEq`, and the kernel's `whnf`-driven equality check) is trying to do something commutation-shaped instead: decide, *exactly*, whether two terms reduce to the same normal form, with no slack in either direction. The reason `isDefEq` is hard to get both sound *and* complete — and why Lean's elaborator sometimes has to fall back to weaker heuristics (unfolding reducibility settings, `whnf` with different transparency levels) — is structurally the same reason Theorem 18.23's hypothesis is so much stronger than Theorem 18.10's: an equality-shaped guarantee needs the *whole square* to commute, not just one triangle of it.

```lean
-- A commuting-square statement is exactly what `rfl` certifies:
-- `rfl : f (g a) = g (f a)` succeeds only when both sides reduce
-- to a syntactically identical normal form — the definitional-equality
-- analogue of Theorem 18.23's α ∘ f = f̄ ∘ α, checked at one point `a`
-- rather than proved for the whole domain.
example (f g : Nat → Nat) (h : ∀ n, f (g n) = g (f n)) (a : Nat) :
    f (g a) = g (f a) := h a
```

**What breaks without exactness:** a sound-but-inexact abstract fixpoint accumulates precision loss with every iteration of the loop it's analyzing — the classic failure mode where a widened or merely-sound interval analysis of a tight loop converges to $[-\infty, +\infty]$ after a handful of iterations even though the true invariant is a small, provable range. Exactness (or the weaker, iterate-restricted forms in Corollaries 18.34/18.35) is the only thing standing between "technically sound" and "actually useful."

## 3. Iterates multiabstraction with a varying abstract transformer

Every result so far assumed *one fixed* abstract transformer $\bar f$ approximating *one fixed* concrete transformer $f$, at every step of the iteration. Section 18.5 drops that assumption: what if the transformer used to compute the $(i{+}1)$-th abstract iterate is allowed to be a *different* function $\bar f_i$ at each step $i$?

This isn't a technicality — it's exactly the situation that arises the moment you introduce **widening** (chapter 23, foreshadowed here) to force convergence on an infinite-height abstract domain: a widening-based analysis applies the ordinary abstract transformer for the first few iterations, then switches to a widening operator $\nabla$ for later iterates to guarantee termination, and later still may switch to a *narrowing* operator to recover precision. That's three different "transformers" applied across one iteration sequence, and none of the single-$\bar f$ theorems above say anything about whether the *final* result relates soundly or exactly to the concrete fixpoint.

**Theorem 18.36 (exact abstraction of iterates).** Given concrete transformers $\langle f_i \mid i \in \mathbb{N} \rangle$ generating concrete iterates $x_0 = \bot,\, x_{i+1} = f_i(x_i),\, x_\omega = \bigsqcup_i x_i$, and abstract transformers $\langle \bar f_i \mid i \in \mathbb{N} \rangle$ generating abstract iterates $\bar x_0 = 0,\, \bar x_{i+1} = \bar f_i(\bar x_i),\, \bar x_\omega = \bigvee_i \bar x_i$, related by a *different abstraction at each stage* $\langle \alpha_i \mid i \in \mathbb{N} \cup \{\omega\} \rangle$ satisfying
$$\alpha_0(x_0) = \bar x_0 \qquad \alpha_{i+1}(f_i(x_i)) = \bar f_i(\alpha_i(x_i)) \qquad \text{and a limit-preservation condition at } \omega,$$
then $\alpha_\omega(x_\omega) = \bar x_\omega$, and — when the $f_i$ and $\bar f_i$ are additionally upper continuous — $x_\omega = \mathrm{lfp}^{\sqsubseteq} f$ and $\bar x_\omega = \mathrm{lfp}^{\preccurlyeq} \bar f$ for the appropriate limits $f, \bar f$, so that $\alpha_\omega(\mathrm{lfp}^{\sqsubseteq} f) = \mathrm{lfp}^{\preccurlyeq} \bar f$.

This is a genuine generalization, not a relabeling: single-transformer commutation (Theorem 18.23) required $\alpha \circ f_i = \bar f_i \circ \alpha$ with the *same* $\alpha$ before and after every step; here, the abstraction itself is allowed to change stage by stage ($\alpha_{i+1}$ on the output side, $\alpha_i$ on the input side), and commutation only has to hold "diagonally," stage by stage, not with one fixed square repeated forever.

**Corollary 18.37 (iterates multiabstraction)** specializes this to the practically common case — one fixed concrete transformer $f$, but a *stage-varying* abstract transformer $\bar f_i$ — which is precisely the widening/narrowing shape: the concrete semantics of the loop body never changes, only the abstract operator applied to it does, iteration by iteration. **Corollary 18.39** further specializes to a single fixed $\alpha_i = \alpha$ across all stages, recovering ordinary commutation (Theorem 18.23) as the degenerate case where nothing varies — a useful sanity check that the general theorem doesn't silently lose the simple case.

**What breaks without multiabstraction:** without this theorem, switching operators mid-iteration (which every practical widening-based analyzer does) would be an unjustified move — you'd be invoking Theorem 18.23's single-transformer commutation on a sequence that doesn't actually use a single transformer, and the "proof" of soundness for the widened analysis would be a category error, not merely an approximation. Section 18.5 is what makes chapter 23's widening theorems (and chapter 39's more elaborate iteration strategies) legitimate applications of fixpoint abstraction rather than an ad hoc extension bolted onto it.

### Grounding: a per-stage transformer in Python

Because the point here is the *shape* of the iteration protocol, not a load-bearing implementation, a short Python sketch communicates it faster than the Rust ceremony would:

```python
def multi_transformer_iterate(transformers, bottom, join, leq, max_widen_steps):
    """
    transformers: a function i -> (abstract element -> abstract element),
    i.e. f̄_i varies with the iteration count i, per Theorem 18.36 /
    Corollary 18.37 — e.g. the ordinary abstract step for i < max_widen_steps,
    then a widening operator ∇ applied against the previous value for
    i >= max_widen_steps, to force termination.
    """
    current = bottom
    i = 0
    while True:
        step = transformers(i)
        candidate = step(current)
        nxt = join(current, candidate) if i < max_widen_steps else candidate
        if leq(nxt, current):
            return current
        current = nxt
        i += 1
```

## 4. Abstraction of deductive, inductive, and structural definitions

Chapter 16 established that a deductive (rule-based) definition of a set $D \in \wp(\mathcal{C})$ by inference rules $R$ is equivalent to a least fixpoint: $D = \mathrm{lfp}^{\subseteq} F_R$, where $F_R$ is the **consequence operator** — apply every rule once to the current set, union in the results. Since Sections 18.2–18.4 already characterize when a least fixpoint abstracts soundly or exactly, they transfer to deductive definitions *for free*, by substitution.

**Theorem 18.44 (deductive definition abstraction).** For a deductive definition $D$ via rules $R$, an abstract "rule set" $\bar R \in \wp(\mathcal{A})$ defined analogously on the abstract side, and a Galois connection $\langle \wp(\mathcal{C}), \subseteq \rangle \xrightleftharpoons[\gamma]{\alpha} \langle \wp(\mathcal{A}), \preccurlyeq \rangle$:

- $\alpha(D) \sqsubseteq \bar D$ always (**soundness**, inherited directly from Corollary 18.16), and
- if $\forall X \subseteq D.\, \gamma(\alpha(X)) \subseteq X$ (a completeness side-condition needed only along the actual iterates of the consequence operator) then $\alpha(D) = \bar D$ (**exactness**, inherited from Corollaries 18.34/18.16 together).

Why bother restating theorems you already have? Because a huge amount of the book's later material — typing rules (chapter 34), Hoare logic's inference rules (chapter 24), model checking (chapter 29) — is presented as *deductive systems*, not directly as fixpoints. Theorem 18.44 is the bridge that lets "is this typing-rule abstraction sound?" be answered by the same machinery as "is this loop-invariant abstraction sound?", without re-deriving [[Fixpoint-Theory|fixpoint theory]] from scratch for every deductive presentation in the book.

**Section 18.9 (inductive and structural abstraction)** takes the last step: for an *inductive* (or, when the well-founded order is syntactic structure, *structural*) definition $D \in S \to \wp(\mathbb{U})$ over a well-founded poset $\langle S, \prec \rangle$ — where $D(s)$ is defined from $\langle D(s') \mid s' \prec s \rangle$ — the abstraction $\bar D \in S \to \mathcal{A}$ with $\bar D(s) \triangleq \alpha(D(s))$ is obtained *by induction on $\prec$*: at each $s$, $D(s)$ is itself given by a fixpoint or deductive definition over the already-abstracted $\bar D(s')$ for smaller $s'$, so the fixpoint/deductive abstraction theorems from earlier in this chapter apply one well-founded step at a time. This is precisely Burstall's structural-induction principle from chapter 2, now doing double duty: it both defines the semantics *and* carries the soundness/exactness proof of its abstraction through every syntactic case.

**Why this matters for typing rules and elaboration specifically:** a monomorphic typing judgment $\Gamma \vdash e : \tau$, presented structurally (chapter 34 does this explicitly), is a structural definition over the syntax of $e$ in exactly this sense. Reading it through this section: the *type* assigned to an expression is an *abstraction* of its full semantic behavior (which values it can produce), computed compositionally by structural recursion, and the question "is this typing rule sound" is literally an instance of Theorem 18.44/Section 18.9 — check the local deductive-rule soundness condition at each syntax case, and structural induction propagates it to the whole judgment. This is the same shape a bidirectional type checker's inference/checking modes use: inference mode computes $\bar D(s)$ structurally bottom-up (an abstraction, synthesized), checking mode verifies a *given* abstract value against what structural abstraction would produce — the checking-mode question is exactly "does $\bar D(s) \preccurlyeq$ (the expected type)," a one-sided soundness query, not the exact-equality query inference mode answers.

### Grounding: structural abstraction as a Rust compiler pass

```rust
// A structural definition D(s) for s ranging over an AST, abstracted
// via structural recursion — Section 18.9's inductive-abstraction
// recipe applied to type inference.
enum Expr {
    Lit(i64),
    Add(Box<Expr>, Box<Expr>),
    Var(String),
}

#[derive(Clone, PartialEq, Debug)]
enum SignType { Bottom, Neg, Zero, Pos, Top } // the abstract domain 𝒜

// D(s) ≜ the (huge, semantic) set of values `s` can evaluate to.
// D̄(s) ≜ α(D(s)), computed structurally — never touching D(s) itself.
// Each match arm is one local soundness/completeness obligation from
// Theorem 18.44 / Section 18.9, discharged once per syntax case.
fn abstract_type(e: &Expr, env: &std::collections::HashMap<String, SignType>) -> SignType {
    match e {
        Expr::Lit(n) => classify_literal(*n),           // base case: α of a singleton
        Expr::Var(x) => env.get(x).cloned().unwrap_or(SignType::Top),
        Expr::Add(l, r) => {
            // sound abstraction of the concrete `+` primitive: this line
            // IS the local check "α ∘ f ≼ f̄ ∘ α" for the Add rule.
            sign_add(&abstract_type(l, env), &abstract_type(r, env))
        }
    }
}
```

## Where this leads

Fixpoint abstraction is the load-bearing theorem this entire book calculates *toward*, from chapter 19 onward. Chapter 19's reachability semantics, chapter 24–26's fixpoint-based proof methods and Hoare logic, chapter 29's model checking, and every concrete domain in Part III (signs, intervals, congruences, zones/octagons, points-to, dependency, types) all ultimately reduce their soundness argument to one instance of Theorem 18.10 or Corollary 18.16, and their precision claims (where made) to one instance of Theorem 18.23 or its iterate-restricted corollaries. Chapter 23's widening/narrowing machinery is a direct descendant of Section 18.5's iterates multiabstraction — that section is the reason widening-based non-termination fixes are provably sound rather than merely plausible. Section 18.7's closure-operator reformulation (backward/forward completeness) resurfaces by name in chapter 21's treatment of reduced products.

For the standing elaborator/verifier project: this chapter is the general mechanism underneath "is my type-checking rule sound" and "does my invariant-inference pass compute the right loop invariant" — the same question, instantiated twice. The distinction between **soundness** (semicommutation, Corollary 18.16 — a checker never wrongly accepts) and **exactness** (commutation, Theorem 18.23 — a checker/inferencer that is *also* complete) is the same distinction that separates "my unifier rejects some definitionally-equal terms it should accept" from "my unifier decides definitional equality exactly." Every time you're tempted to hand-wave that an abstract operation "looks about right," this chapter is the checklist for turning that hand-wave into either a soundness proof (check semicommutation once, locally) or a genuine completeness proof (check commutation, which is much harder, and usually only along the iterates you actually visit).
