---
title: "Transfinite Ordinals"
source: "An Introduction to Proof Theory: Normalization, Cut-Elimination, and Consistency Proofs (Mancosu, Galvan, Zach, 2021)"
chapter: "Chapter 8, §§8.6–8.8 (pp. 332–339)"
tags: [proof-theory, ordinals, von-neumann-ordinals, set-theory, burali-forti, cantor-normal-form, epsilon-0, well-orderings]
---

# Transfinite Ordinals

[[book-guidelines|↩ Back to guidelines]]

## Why go back to set theory at all?

The [[Ordinal-Notations-up-to-Epsilon-0|previous topic]] built something deliberately austere: finite strings of symbols — $0$, $\boldsymbol{\omega}$, sums, exponents — ordered by a purely combinatorial rule ($\prec$), justified purely by facts about lexicographic orderings of sequences. Nothing about "sets," nothing about "the transfinite," nothing that could smuggle in a foundational commitment stronger than arithmetic itself. That's not an accident — it's the whole point. Hilbert's program (and Gentzen's rescue of it) needs the consistency proof of arithmetic to be *finitary*, and finitary metamathematics doesn't get to assume the [[The-Sequent-Calculus#Axioms|axioms]] of set theory, including the Axiom of Choice, which turns out to be exactly what's needed to prove "every well-ordered set is isomorphic to an ordinal" in general.

So why does the book turn around, in §8.6, and define ordinals as actual sets — objects built from $\varnothing$ by taking unions and singleton-adjunctions, governed by the Axiom of Choice? Two reasons, and they matter for different audiences:

1. **Naming, not proving.** The word "ordinal notation" is a promise: that these strings are order-isomorphic to an initial segment of the real ordinals, specifically the segment below $\varepsilon_0$. Section 8.6–8.8 cashes that promise out. It's exposition and motivation, not machinery the consistency proof itself depends on — you could delete this section and Chapter 9's argument would go through unchanged, because Chapter 9 only ever touches the syntactic notations.
2. **It tells you exactly where the danger is.** Ordinals-as-sets is where a subtlety lives that the purely combinatorial notations sidestep for free: there is no set of all ordinals (Burali-Forti's paradox, below). If your termination measure were literally "the ordinal," you'd need to be careful about what totality you're quantifying over. If your termination measure is a *string* built by an explicit grammar, that worry evaporates — you're just doing induction on finite syntax, the same kind of induction you already trust for induction on formula height.

*What breaks without this section*: nothing in the formal machinery — but you'd be left not knowing *why* the notations of the previous topic are called "ordinal notations" rather than just "some well-founded gadget the author invented," and you'd have no way to answer the question "how far do these go, and how do I know that's the right amount?" The answer, worked out below, is: exactly as far as $\varepsilon_0$, and Cantor normal form is the theorem that proves it.

## The von Neumann ordinal: a set that *is* its own history

Start from the finite case, where the definition should feel almost too simple. In set theory you can represent the number $n$ by *any* $n$-element set — but von Neumann's trick is to pick a canonical one: represent $n$ by the set of all ordinals smaller than $n$.

$$
0 = \varnothing, \quad 1 = \{0\}, \quad 2 = \{0,1\}, \quad 3 = \{0,1,2\}, \quad \ldots
$$

Each number literally *contains* every number below it as an element. This is what Definition 8.48 generalizes:

> **Definition 8.48.** A set $\alpha$ is an **ordinal** if and only if it is
> 1. transitive, i.e. for all $\beta \in \alpha$, $\beta \subseteq \alpha$, and
> 2. $\langle \alpha, \in \rangle$ is a well-ordering.

"Transitive" here is a property of the set, not of a relation on it — don't confuse it with the transitivity of $<$: a set $\alpha$ is transitive when every element of an element of $\alpha$ is again an element of $\alpha$. Combine that with $\in$ being a well-ordering of $\alpha$, and you get a set that is, in a precise sense, *its own complete downward history*: $\alpha$ doesn't just contain smaller ordinals, it contains *all* of them, and orders them correctly. This is made exact by Proposition 8.50:

> **Proposition 8.50.** If $\alpha$ is an ordinal then $\alpha = \{\beta : \beta \text{ is an ordinal and } \beta < \alpha\}$.

where, once you're inside ordinal theory, $\alpha < \beta$ is *defined* to mean $\alpha \in \beta$. So "less than" and "member of" collapse into the same relation for ordinals — there's no separate order to check for consistency with membership, because there's only one relation doing both jobs.

An important, easy-to-miss consequence: **every element of an ordinal is itself an ordinal** (the book proves this by unwinding the transitivity clause twice — if $\beta \in \alpha$, you show $\beta$ is transitive and that $\in$ well-orders $\beta$ as a sub-ordering of $\langle \alpha, \in\rangle$). This is the fact the Burali-Forti argument below leans on.

**Grounding — finite von Neumann ordinals as nested containers.** This construction is concrete enough to just build in Python (illustrative only — not something you'd actually want in a real codebase):

```python
def von_neumann(n: int) -> frozenset:
    """Represent n as the set of all smaller von Neumann ordinals."""
    if n == 0:
        return frozenset()
    return frozenset(von_neumann(k) for k in range(n)) | {von_neumann(n - 1)}

# von_neumann(3) == frozenset({frozenset(), frozenset({frozenset()}),
#                               frozenset({frozenset(), frozenset({frozenset()})})})
# i.e. {0, 1, 2} — exactly Definition 8.48's picture.
```

Every element really is a smaller ordinal, membership really is the order, and `len(von_neumann(n)) == n` for free — cardinality falls out of the order-theoretic definition without being separately stipulated.

**Why Lean doesn't do it this way.** If you've looked at `Mathlib.SetTheory.Ordinal.Basic`, you'll notice Lean's `Ordinal` is *not* defined as "a hereditarily transitive set well-ordered by $\in$." It can't be — Lean's type theory has no primitive membership relation between arbitrary terms the way ZFC does, and building a raw cumulative-hierarchy-of-sets encoding inside a proof assistant is exactly the kind of foundational commitment a trusted kernel wants to avoid taking on lightly. Instead, mathlib takes Theorem 8.58 below — "every well-ordered set is order-isomorphic to an ordinal" — and turns it into the *definition*: an `Ordinal` is a well-order up to order-isomorphism (a quotient type over well-ordered types). This is a good habit to notice and generalize: **when a theorem says "every X is representable as a canonical Y," a proof assistant will often prefer to define the object as the quotient/equivalence class directly, rather than reproduce the set-theoretic construction that motivated it.** You'll hit this same move again when your own elaborator needs canonical representatives for metavariable equivalence classes under unification.

## Successor and limit ordinals — the two ways an ordinal can arise

Definition 8.55 gives you the successor operation directly from set operations:

> **Definition 8.55 (Successor ordinal).** If $\alpha$ is an ordinal, then $S(\alpha) = \alpha \cup \{\alpha\}$.

Read set-theoretically this says: "the ordinal right after $\alpha$ is $\alpha$'s complete history, plus $\alpha$ itself as a new final element." Proposition 8.56 confirms this is a genuine immediate successor — there is no ordinal strictly between $\alpha$ and $S(\alpha)$. Once ordinal addition is defined (§8.8, below), $S(\alpha)$ and $\alpha + 1$ turn out to be the same ordinal, so the book freely uses both notations afterward.

Iterating $S$ from $0$ gives you all the finite ordinals — but not more. To get past all of them at once, you need a genuinely different construction: **taking the union of an increasing sequence**.

> **Proposition 8.57.** If $\langle \alpha_i : i = 1, 2, \ldots\rangle$ is an increasing sequence of ordinals, then $\bigcup_i \alpha_i$ is an ordinal, and is the *least* ordinal $\beta$ with $\beta > \alpha_i$ for every $i$.

Applied to $\langle 0, 1, 2, 3, \ldots \rangle$, this union is $\omega = \{0, 1, 2, 3, \ldots\}$ — literally the set of all finite ordinals, and (unsurprisingly, since ordinals are their own downward history) also the *least upper bound* of the finite ordinals. This gives the book's terminology:

- An ordinal is a **successor ordinal** if it equals $S(\beta)$ for some $\beta$.
- An ordinal other than $0$ that is *not* a successor is a **limit ordinal** — it is only reachable as the union/supremum of an infinite increasing sequence beneath it, never by taking one predecessor's immediate next step.

This trichotomy ($0$ / successor / limit) is the shape every transfinite induction and every transfinite recursion you'll ever write is built around — you prove or define the successor case and the limit case separately, because they're genuinely different operations (one predecessor to advance past, vs. an entire infinite approximating sequence to take the supremum of).

**What breaks without the limit case, and why this is load-bearing for your abstract-interpretation work.** Successor-only reasoning is exactly ordinary mathematical induction — it can only ever certify facts about ordinals reachable by finitely many "+1" steps, i.e. about $\mathbb{N}$ itself. The moment your recursion or your induction needs to talk about a fixed point reached only "in the limit" — after infinitely many approximation steps — you need the limit case, and concretely you need *some* way to compute or bound $\bigcup_i \alpha_i$. This is not a curiosity: it is *precisely* the shape of the widening problem in abstract interpretation. When an abstract domain has infinite ascending chains (interval bounds, polyhedra, whatever), a naive Kleene-iteration fixpoint computation $\bot, F(\bot), F(F(\bot)), \ldots$ may never stabilize after finitely many steps — you need a "limit ordinal" move (a widening operator $\nabla$) that jumps to an over-approximation of the supremum in one step, then resumes ordinary iteration from there, exactly the way Proposition 8.57's union gets you to $\omega$ in one conceptual step and then $S$ resumes from there to give $\omega+1, \omega+2, \ldots$. Reading transfinite iteration schemes for abstract interpretation (Cousot–Cousot) is, structurally, reading successor/limit induction wearing a different hat.

## The Burali-Forti paradox: why there is no "set of all ordinals"

This is stated as a footnote in the book (footnote 6 to §8.6), but it is one of the most important facts in the chapter, precisely because of what it rules out:

> Suppose there is a set $\Omega$ of all ordinals. Every element of an ordinal is an ordinal, so every element of an element of $\Omega$ is an element of $\Omega$ — i.e. $\Omega$ is transitive. Every set of ordinals is well-ordered by $\in$. So $\Omega$ satisfies both clauses of Definition 8.48: it is itself an ordinal. But then $\Omega \in \Omega$ — a set that is a member of itself — which contradicts a basic axiom of set theory (Foundation/Regularity).

The structure of the argument is worth isolating, because it's the same move as Russell's paradox and the same move that makes "the type of all types" inconsistent as a naive foundation: you have a predicate ("is an ordinal") that is well-behaved on any *particular* set of ordinals you hand it, but collecting *all* the objects satisfying the predicate into a single object and then checking whether the predicate applies to *that* collection breaks. "Ordinal" is not a set-sized notion; the ordinals form what set theorists call a **proper class**, not a set.

Trace the dependency back to the previous topic and you can see exactly why the book was so careful there. If the consistency proof's termination measure were "an ordinal" in this literal, unrestricted, set-theoretic sense, you'd eventually need to reason about *the collection of all ordinals a proof's reduction sequence could produce* — and that's not a legitimate mathematical object to quantify over without care. The combinatorial ordinal notations sidestep this completely: they are a specific, syntactically-defined, recursively enumerable set of finite strings, no different in kind from "the set of well-formed formulas." There is no Burali-Forti worry about "the set of all ordinal notations" because it manifestly *is* a perfectly good set — it's just strings satisfying a grammar, the same status as $O_{\leq 1}$ or $O_{\leq 2}$ from the previous topic. This is the finitary payoff of doing the hard combinatorial work first: you get all the *order*-theoretic power of the ordinals below $\varepsilon_0$ without ever having to reason about the class of all ordinals.

## Ordinal arithmetic: addition, multiplication, exponentiation

With Theorem 8.58 in hand ("every well-ordered set is order-isomorphic to an ordinal" — unprovable finitarily, stated without proof here, and the fact that genuinely needs Choice), the book defines the three ordinal operations by first building an explicit well-order out of two ordinals, then invoking 8.58 to say "the ordinal isomorphic to *that*."

**Addition.** $\alpha + \beta$ is the ordinal isomorphic to "$\alpha$-many points, followed by $\beta$-many points":

> **Definition 8.59.** $\alpha + \beta$ is the ordinal isomorphic to $\{\langle 0,\alpha'\rangle : \alpha' < \alpha\} \cup \{\langle 1,\beta'\rangle : \beta' < \beta\}$, ordered by $\langle i,\gamma\rangle < \langle j,\gamma'\rangle$ iff $i<j$, or $i=j$ and $\gamma<\gamma'$.

Because "followed by" is not symmetric, **ordinal addition is not commutative** — and the book's two worked examples are worth internalizing as a pair:

- $2 + \omega$: a finite bit ($\bullet\bullet$) followed by $\omega$-many points. But "two points, then infinitely many more" is order-isomorphic to just $\omega$ — the two initial points get absorbed, relabeled as points $0,1$ of the same $\omega$-shaped sequence. So $2+\omega = \omega$.
- $\omega + 2$: $\omega$-many points, *then* two more *after all of them*. There's no way to absorb a point that comes after infinitely many others into the $\omega$-shape — this genuinely has two new "largest" elements. So $\omega + 2 \neq \omega$; it's $(\omega+1)+1$.

**Multiplication.** $\alpha \cdot \beta$ is $\beta$-many back-to-back copies of $\alpha$ (Definition 8.61, ordered so the $\beta$-coordinate is primary). Symmetric asymmetry again: $2 \cdot \omega$ is $\omega$-many copies of a 2-element block, one after another — which telescopes into just $\omega$. But $\omega \cdot 2$ is two copies of $\omega$ placed end to end, which is strictly bigger than $\omega$ (it's $\omega + \omega$).

**Exponentiation.** Definition 8.62 defines $\alpha^\beta$ as (isomorphic to) the set of finitely-supported functions $f : \beta \to \alpha$ (functions that are $0$ almost everywhere), ordered by comparing the highest-indexed point of difference. For $\alpha=\beta=\omega$ this is exactly finite sequences of naturals under an anti-lexicographic order — the same style of order the previous topic used for ordinal notations themselves.

**A crucial subtlety — two different "sums."** If you read the previous topic, you already met a binary operation on ordinal notations called the *natural sum*, $\alpha \,\#\, \beta$, which is commutative. **Ordinal addition $\alpha+\beta$, defined here, is not the same operation** — it's non-commutative, as just shown. The book uses $\#$ (not $+$) throughout the purely combinatorial development precisely because commutativity is what makes $\#$ well-behaved as a componentwise merge of two Cantor-normal-form-shaped strings; it's only once you've fixed a specific left-to-right positional convention (Definition 8.59's $\langle i,\gamma\rangle$ pairing) that you get the order-sensitive $+$. If you ever implement both, keep them as genuinely distinct operations in your type — collapsing them is a real bug, not a naming nitpick, because it changes which of two proof states counts as smaller.

**Grounding — Rust: ordinals as Cantor-normal-form data, addition as data manipulation.** The theorem that closes this loop (next section) says every ordinal below $\varepsilon_0$ *is* a finite tree of natural-number exponents and coefficients — which means you can represent it as an ordinary recursive Rust enum, and the "abstract" arithmetic above becomes concrete structural recursion:

```rust
/// An ordinal < ε0 in Cantor normal form: ω^β1·a1 + ω^β2·a2 + ... + ω^βn·an
/// with β1 > β2 > ... > βn and each ai a positive natural number.
#[derive(Clone, PartialEq, Eq)]
enum Ordinal {
    Zero,
    Term { terms: Vec<(Ordinal, u64)> }, // (exponent, coefficient) pairs, strictly decreasing exponents
}

impl Ordinal {
    fn is_limit(&self) -> bool {
        // A CNF ordinal is a successor iff its lowest-order term has exponent 0
        // (i.e. it ends in "+ n" for some finite n > 0); otherwise it's 0 or a limit.
        match self {
            Ordinal::Zero => false,
            Ordinal::Term { terms } => {
                !matches!(terms.last(), Some((Ordinal::Zero, _)))
            }
        }
    }

    /// Non-commutative ordinal successor: S(α) = α + 1.
    fn successor(&self) -> Ordinal {
        match self {
            Ordinal::Zero => Ordinal::Term { terms: vec![(Ordinal::Zero, 1)] },
            Ordinal::Term { terms } => {
                let mut terms = terms.clone();
                match terms.last_mut() {
                    Some((Ordinal::Zero, c)) => *c += 1,      // absorb into the finite tail
                    _ => terms.push((Ordinal::Zero, 1)),      // append a new finite tail
                }
                Ordinal::Term { terms }
            }
        }
    }
}
```

Notice `is_limit` is exactly Definition 8.55/the successor-vs-limit trichotomy made computable: an ordinal is a limit precisely when its CNF has no finite tail to increment — there's nothing there to add $1$ to without changing the exponent structure, which is exactly why reaching it requires a supremum instead of a `+1`. This is the same case-split your termination-measure code will need anywhere you're decreasing an $\varepsilon_0$-valued (or smaller) measure across a proof-search or fixpoint-iteration step.

## Cantor normal form: the theorem that justifies the whole notation system

This is the payoff. Theorem 8.63 is stated without proof, but it's the single fact that turns "ordinal notations" from a suggestive name into a proven correspondence:

> **Theorem 8.63 (Cantor normal form).** For every ordinal $\alpha$ there is a *unique* sequence of ordinals $\beta_1 \geq \beta_2 \geq \cdots \geq \beta_n$ such that
> $$\alpha = \omega^{\beta_1} + \omega^{\beta_2} + \cdots + \omega^{\beta_n}.$$

For $\alpha < \varepsilon_0$, every exponent $\beta_i$ is itself $< \alpha$, so you can recursively expand each $\beta_i$ into its own Cantor normal form, and keep going — the recursion is guaranteed to bottom out (each recursive call strictly decreases the ordinal being expanded) at exponents that are finite sums of $\omega^0 = 1$'s, i.e. natural numbers, or at $0$ itself. Definition 8.64 packages exactly this recursive unfolding as a translation function:

> **Definition 8.64.** $o(\alpha) = 0$ if $\alpha = 0$; otherwise, if $\alpha$'s Cantor normal form is $\omega^{\beta_1}+\cdots+\omega^{\beta_n}$, then $o(\alpha) = \boldsymbol{\omega}^{o(\beta_1)} + \cdots + \boldsymbol{\omega}^{o(\beta_n)}$.

Read the bold $\boldsymbol{\omega}$ versus the plain $\omega$ carefully — this is the bridge between the two worlds of this pair of articles. Plain $\omega$ (and $+$, and the whole right-hand side) lives in real set-theoretic ordinal arithmetic; bold $\boldsymbol{\omega}$ (and the ordinal-notation sum from the previous topic) lives in the purely syntactic world of finite strings. $o$ is the map that takes you from one to the other, and Theorem 8.63's uniqueness is exactly what makes $o$ well-defined and injective: **the finite strings of the previous topic are not an arbitrary notation system that happens to resemble ordinal arithmetic — they are, definitionally, Cantor normal form written down as syntax.** The book closes the loop with one line: "the ordering defined on ordinal notations is the same as the ordering of the corresponding ordinals, i.e. $\alpha < \alpha'$ iff $o(\alpha) \prec o(\alpha')$" — so the well-ordering proof the previous topic did entirely by combinatorics (§8.5, induction on height and lexicographic comparison of sequences) really was, all along, a proof about actual ordinal order, just conducted without needing to say so.

**Grounding — this is why `Ordinal` libraries store CNF, not raw set data.** If you look at how mathlib or any computational ordinal-arithmetic library actually *represents* ordinals below $\varepsilon_0$ for computation (as opposed to how it *defines* `Ordinal` abstractly via Theorem 8.58's quotient construction), you'll find exactly the Rust-style tree from the previous section — Cantor normal form, recursively. This isn't a coincidence or an implementation convenience: Theorem 8.63 is the theorem that *guarantees* CNF is a faithful, terminating, unique data representation for every ordinal below $\varepsilon_0$ in the first place. Any well-founded termination measure you build later for a proof-search or constraint-solving loop that needs "more than $\mathbb{N}$ but still finitely presentable" should reach for exactly this representation.

## Constructing $\varepsilon_0$ as a limit

Section 8.7 builds $\varepsilon_0$ concretely, bottom-up, alternating the two moves this article has now fully justified: **successor** ($S(\alpha) = \alpha \cup \{\alpha\}$, one step at a time) and **limit** (union of an increasing sequence, a genuine leap). Read it as a tower of fixpoint-approximation rounds, each round using the previous round's limit as its new starting point:

```mermaid
flowchart TD
    A["0, 1, 2, 3, ... (successor steps)"] -->|union, Prop 8.57| B["ω"]
    B -->|successor steps: ω, ω+1, ω+2, ...| C["ω·2"]
    C -->|repeat, then union over ω·1, ω·2, ω·3, ...| D["ω·ω = ω²"]
    D -->|repeat the whole process| E["ω³, ω⁴, ... → ω^ω"]
    E -->|iterate the exponential successor α ↦ ω^(α+1)| F["ω^ω, ω^(ω+1), ... → ω^(ω·2)"]
    F -->|keep iterating| G["ω^ω², ω^ω³, ... → ω^(ω^ω)"]
    G -->|iterate the tower itself| H["ω^ω, ω^ω^ω, ω^ω^ω^ω, ... "]
    H -->|union of the whole increasing tower sequence| I["ε₀"]
```

Each arrow into a boxed node is one application of Proposition 8.57 — the *limit* move, jumping over an infinite successor-chain in a single step. The characterizing equation the book gives is $\varepsilon_0 = \omega^{\varepsilon_0}$ — $\varepsilon_0$ is a **fixed point** of the exponential map $\alpha \mapsto \omega^\alpha$, and moreover the *least* such fixed point (anything smaller still has room to grow when you feed it back into $\omega^{(\cdot)}$). This is worth sitting with, because it is precisely the Knaster–Tarski shape: $\varepsilon_0$ is $\mathrm{lfp}(\alpha \mapsto \omega^\alpha)$, obtained by transfinitely iterating the map from $0$ and taking limits at every limit stage — the exact recipe an abstract interpreter runs (with a widening operator standing in for "take the limit" when the concrete supremum isn't computable) to find the least fixed point of a monotone transfer function over an infinite-height lattice.

## Where this leads

**Depends on:** the well-ordering and induction machinery from §§8.1–8.2 (this is where Theorem 8.58 — every well-order is isomorphic to an ordinal — gets its force), and implicitly on full ZFC, including Choice, which is exactly the commitment the previous topic's combinatorial notations were built to avoid needing.

**Feeds into:** nothing in Chapter 9's actual consistency proof directly touches this article's set-theoretic apparatus — Gentzen's ordinal-notation assignment to proofs (§9.1) uses only the syntactic notations from the previous topic. This article's real job is retroactive justification: it's the reason you're allowed to trust that "the notations well-order exactly the ordinals below $\varepsilon_0$" means something, and it's the reason the previous topic had to be built the careful, syntactic, string-grammar way it was — because the alternative, reasoning directly about "the ordinals" as a completed totality, runs straight into Burali-Forti.

**For the compiler/elaborator project:** three things here are directly load-bearing, not just background color. First, the successor/limit trichotomy is the general shape of well-founded recursion once your termination measures outgrow $\mathbb{N}$ — any proof-search, constraint-propagation, or CHC-solving loop whose termination argument needs an ordinal-valued measure will need to handle "the limit case" as a genuinely distinct branch, not a degenerate successor. Second, Cantor normal form is the concrete, finitely-presentable data structure you'd actually implement such a measure as — a small Rust enum, exactly as sketched above, with well-founded recursion on it justified by Theorem 8.63's uniqueness and the strict decrease of exponents. Third, and most concretely for the abstract-interpretation side of the project: $\varepsilon_0$ as the least fixed point of $\alpha \mapsto \omega^\alpha$, built by iterating-then-taking-limits, is the textbook shape of the transfinite fixpoint iteration that underlies widening/narrowing over infinite-height abstract domains — the same "successor step, successor step, ..., now take a limit and continue" rhythm you'll be implementing, just with a widening operator playing the role Proposition 8.57's union plays here.
