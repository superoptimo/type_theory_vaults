---
title: "Semantics of Assertions"
book: "An Introduction to Separation Logic (Reynolds, 2008)"
chapter: "Chapter 2, §2.1–2.2 (pp. 33–41)"
tags: [separation-logic, semantics, satisfaction-relation, substitution, formal-proof]
---

[[book-guidelines|↩ Back to guidelines]]

## Why the syntax alone isn't enough

[[The-Separation-Logic-Assertion-Language|The previous article]] introduced $\mathrm{emp}$, $\mapsto$, $*$, and $\mathbin{-\!*}$ purely by gloss — "the heap splits into two disjoint parts," "if you extend the heap with a disjoint part…" These glosses are precise enough to use informally, but a logic needs something sharper before you can *prove* anything about it: a mathematical definition of when a state actually satisfies a formula, stated independently of any proof system. Without that, "sound inference rule" has no meaning — soundness *is* a claim that a syntactic derivation tracks this underlying semantic fact. Chapter 2 supplies exactly this: the **satisfaction relation** $s, h \models p$, defined once and for all by structural induction on $p$, plus the substitution machinery needed to state and prove properties of that relation.

This is precisely the type-checker/proof-checker split that recurs throughout formal verification: the syntax is the *language* your checker parses, the semantics is the *ground truth* your checker is supposed to be deciding membership in. Get this wrong and every inference rule you build on top is unsound by construction, no matter how convincing the rule looks on paper.

## The satisfaction relation, by structural induction

A state is a pair $(s, h)$ — a store $s$ (finite map, variables to values) and a heap $h$ (finite partial map, addresses to values). Reynolds defines $s, h \models p$ by cases on the outermost connective of $p$:

$$
\begin{aligned}
s, h &\models b &&\text{iff } [\![b]\!]_{\mathrm{bexp}}\, s = \mathrm{true} \\
s, h &\models \neg p &&\text{iff } s, h \models p \text{ is false} \\
s, h &\models p_0 \wedge p_1 &&\text{iff } s, h \models p_0 \text{ and } s, h \models p_1 \\
s, h &\models \forall v.\ p &&\text{iff } \forall x \in \mathbb{Z}.\ [s \mid v : x],\, h \models p \\
s, h &\models \exists v.\ p &&\text{iff } \exists x \in \mathbb{Z}.\ [s \mid v : x],\, h \models p \\[4pt]
s, h &\models \mathrm{emp} &&\text{iff } \mathrm{dom}\, h = \{\} \\
s, h &\models e \mapsto e' &&\text{iff } \mathrm{dom}\, h = \{[\![e]\!]_{\mathrm{exp}}\, s\} \text{ and } h([\![e]\!]_{\mathrm{exp}}\, s) = [\![e']\!]_{\mathrm{exp}}\, s \\
s, h &\models p_0 * p_1 &&\text{iff } \exists h_0, h_1.\ h_0 \perp h_1 \text{ and } h_0 \cdot h_1 = h \text{ and } s, h_0 \models p_0 \text{ and } s, h_1 \models p_1 \\
s, h &\models p_0 \mathbin{-\!*} p_1 &&\text{iff } \forall h_0.\ (h_0 \perp h \text{ and } s, h_0 \models p_0) \text{ implies } s, h \cdot h_0 \models p_1
\end{aligned}
$$

(Here $h_0 \perp h_1$ means the two heaps have disjoint domains, and $h_0 \cdot h_1$ is their union.) The first block — booleans, negation, conjunction, quantifiers — is *identical* to ordinary predicate logic's Tarskian semantics: the heap is carried along completely unchanged. All of the heap-specific content of separation logic is concentrated in the last four clauses, and notice how literally they encode the informal glosses from the previous article: $*$'s clause is an existential over *all* ways to [[Case-Studies-in-Program-Verification#Partition|partition]] $h$ into disjoint pieces; $\mathbin{-\!*}$'s clause is a universal over *all* disjoint extensions.

**What breaks without this definition:** if you only had the informal English gloss, you could not settle a question like "does $x \mapsto 0 * x \mapsto 0$ hold of any heap?" by argument alone — you'd be arguing about what the English *means*. With the formal clause, it's a two-line derivation: it would require $h_0 \perp h_1$ with both $s, h_0 \models x \mapsto 0$ and $s, h_1 \models x \mapsto 0$, i.e. both $\mathrm{dom}\,h_0 = \{sx\}$ and $\mathrm{dom}\,h_1 = \{sx\}$ — but disjoint domains can't both equal $\{sx\}$ unless one is empty, which it isn't. No heap satisfies it. This is exactly the failure of contraction from the previous article, now derived from the semantics rather than asserted by example.

### Grounding: the satisfaction relation as an actual decision procedure

This definition translates almost verbatim into an evaluator — which is the right way to think about it if you're building a verifier: the satisfaction relation *is* the specification your checker's `eval` function must be correct against.

```rust
use std::collections::HashMap;

type Addr = i64;
type Store = HashMap<String, i64>;
type Heap = HashMap<Addr, i64>;

enum Assertion {
    Emp,
    PointsTo(Expr, Expr),
    And(Box<Assertion>, Box<Assertion>),
    Sep(Box<Assertion>, Box<Assertion>),   // p0 * p1
    Wand(Box<Assertion>, Box<Assertion>),  // p0 -* p1
    // ... Not, Or, Forall, Exists, boolean expr
}

fn satisfies(s: &Store, h: &Heap, p: &Assertion) -> bool {
    match p {
        Assertion::Emp => h.is_empty(),
        Assertion::PointsTo(e, e2) => {
            let addr = eval_exp(s, e);
            h.len() == 1 && h.get(&addr) == Some(&eval_exp(s, e2))
        }
        Assertion::And(p0, p1) => satisfies(s, h, p0) && satisfies(s, h, p1),
        Assertion::Sep(p0, p1) => {
            // exists a partition of h into disjoint h0, h1 ...
            all_disjoint_splits(h).any(|(h0, h1)| {
                satisfies(s, &h0, p0) && satisfies(s, &h1, p1)
            })
        }
        Assertion::Wand(p0, p1) => {
            // forall disjoint extensions h0 of h, if h0 |= p0 then h ∪ h0 |= p1
            all_disjoint_heaps_not_in(h).all(|h0| {
                !satisfies(s, &h0, p0) || satisfies(s, &(union(h, &h0)), p1)
            })
        }
        // ...
    }
}
```

The two existential/universal clauses over "all disjoint splits" or "all disjoint extensions" are why $*$ and $\mathbin{-\!*}$ are, in general, *not* decidable by naive enumeration over an unbounded heap — this is exactly why separation-logic-based verifiers (like Viper, Iris, or Verus's underlying model) don't literally run this quantifier; instead they use *symbolic heaps* and syntactic entailment procedures whose soundness is justified against this semantic definition, not by running it. [[Doubly-Linked-and-Xor-Linked-List-Segments#The definition|The definition]] above is your ground truth, and your real checker is an algorithm you separately prove sound against it — the same relationship a type checker's algorithmic typing rules have to declarative typing judgments.

## Substitution: the bridge between syntax and semantics

Before giving the satisfaction relation, the notes establish substitution laws for *expressions*, because assertions' meaning under substitution reduces to expressions' meaning under substitution. The **Partial Substitution Law for Expressions** says: substituting $e_i$ for $v_i$ in an expression $e$ and evaluating in store $s$ gives the same result as evaluating $e$ (unsubstituted) in a *modified* store $\hat s$ that already maps each $v_i$ to $[\![e_i]\!]_{\mathrm{exp}}\, s$:

$$[\![e / v_1{\to}e_1, \ldots, v_n{\to}e_n]\!]_{\mathrm{exp}}\, s = [\![e]\!]_{\mathrm{exp}}\, \hat s \qquad \hat s = [\, s \mid v_1 : [\![e_1]\!]_{\mathrm{exp}}\, s \mid \cdots \mid v_n : [\![e_n]\!]_{\mathrm{exp}}\, s\, ]$$

This looks like a triviality, but it's the load-bearing lemma that lets you reason about "substitute-then-evaluate" purely in terms of "evaluate-in-a-modified-environment" — which is exactly the operation you need to state the assignment rule of Hoare logic ($\{q/v{\to}e\}\ v := e\ \{q\}$) soundly, and it generalizes unchanged to assertions:

**Proposition 3 (Partial Substitution Law for Assertions):** $s, h \models (p/\delta) \text{ iff } \hat s, h \models p$, where $\delta$ is $v_1{\to}e_1, \ldots, v_n{\to}e_n$ and $\hat s$ is the correspondingly updated store.

Notice what *doesn't* change here: the heap $h$ is completely untouched by substitution into an assertion. This is a direct consequence of expressions being heap-independent (§1.3) — since `[e]` and `cons` are commands, not expressions, no expression (and hence no substituted term) can read or depend on the heap. That property is what makes this substitution law simple; substitution *into commands* (Chapter 3) is a genuinely harder problem, precisely because commands can mutate the heap and the store simultaneously.

### Grounding: this is capture-avoiding substitution, the thing every elaborator does constantly

If you've implemented a substitution function for a lambda calculus or a dependent type checker, this is the exact same operation, minus the complexity of variable capture in *binders* (the notes handle that separately — "bound variables in $p$ will be renamed to avoid capture," the standard $\alpha$-renaming discipline). In Lean-style pseudocode:

```lean
-- Simultaneous substitution of expressions for variables, capture-avoiding.
def subst (p : Assertion) (δ : List (Var × Expr)) : Assertion :=
  match p with
  | .forall v body =>
      -- rename v if it clashes with any free variable in δ's expressions,
      -- then recurse under the (possibly renamed) binder
      let v' := freshIfNeeded v δ
      .forall v' (subst (rename body v v') (δ.filter (·.1 ≠ v)))
  | .and p0 p1 => .and (subst p0 δ) (subst p1 δ)
  | .pointsTo e e' => .pointsTo (substExpr e δ) (substExpr e' δ)
  -- ...
```

This is precisely the machinery a bidirectional type checker's `substitute` function needs when it beta-reduces an application, or when an elaborator instantiates a metavariable — "substitute, avoiding capture, then re-establish the invariant that free variables mean what they used to." Reynolds's Partial Substitution Law is the semantic correctness statement your `subst` function would need to satisfy: substitution and evaluation must commute. That's a soundness obligation, not an implementation detail — get it wrong and your Hoare-logic assignment rule (or your elaborator's beta-reduction) silently produces false specifications.

## Validity, satisfiability, and worked examples

An assertion $p$ is **valid** iff $s, h \models p$ for *every* state $(s, h)$ (with $\mathrm{dom}\,s \supseteq \mathrm{FV}(p)$); it is **satisfiable** iff $s, h \models p$ for *some* state. These are the standard model-theoretic notions, but worth pinning down because the rest of the notes constantly distinguishes them: an *inference rule* $p / q$ is sound when validity of $p$ transfers to validity of $q$ — a much weaker requirement than the *implication* $p \Rightarrow q$ being valid (which demands the transfer hold state-by-state). The notes flag this distinction explicitly with a subtle example: the rule of generalization $p / \forall v.\, p$ is sound (if $p$ is valid for all states, so is $\forall v.\, p$), but the corresponding implication $p \Rightarrow \forall v.\, p$ is *not* valid (take $p$ to be $x = 0$: true in *some* states, but $\forall x.\, x = 0$ is false).

The book works through the satisfaction clause for $x \mapsto 0 * y \mapsto 1$ step by step, unwinding to:

$$s, h \models x \mapsto 0 * y \mapsto 1 \quad\text{iff}\quad sx \neq sy \text{ and } h = [\, sx : 0 \mid sy : 1\, ]$$

— note the *derived* fact that $sx \neq sy$: nothing in the syntax says $x$ and $y$ denote different addresses, but the semantics of $*$ forces it, because a single-cell heap can't simultaneously be split into two nonempty disjoint single-cell pieces at the *same* address. A comparison table in the text nails down several edge cases worth internalizing directly (writing $h_0 = [sx{:}0]$, $h_1 = [sy{:}1]$, $sx \neq sy$):

| $p$ | $s, h \models p$ iff |
|---|---|
| $x \mapsto 0 * x \mapsto 0$ | false (same argument as the contraction counterexample) |
| $(x \mapsto 0 \vee y \mapsto 1) * (x \mapsto 0 \vee y \mapsto 1)$ | $h = h_0 \cdot h_1$ |
| $x \mapsto 0 * y \mapsto 1 * (x \mapsto 0 \vee y \mapsto 1)$ | false (nothing left to satisfy the third conjunct) |
| $x \mapsto 0 * \mathrm{true}$ | $h_0 \subseteq h$ |
| $x \mapsto 0 * \neg\, x \mapsto 0$ | $h_0 \subseteq h$ (same as above!) |

That last line is worth pausing on: $x \mapsto 0 * \mathrm{true}$ and $x \mapsto 0 * \neg\,x \mapsto 0$ are *equivalent*, even though $\mathrm{true}$ and $\neg\,x \mapsto 0$ are wildly different assertions — because once you've carved out the sub-heap satisfying $x \mapsto 0$, *anything at all* can happen on the disjoint remainder, so the remainder's assertion is irrelevant as long as it's satisfiable by *some* heap disjoint from $h_0$. This is the semantic content behind $\hookrightarrow$ from the previous article ($e \hookrightarrow e' \stackrel{\text{def}}{=} e \mapsto e' * \mathrm{true}$): "somewhere in the heap" really does mean "padded by an arbitrary, don't-care remainder."

## Inference, formal proofs, and meta-proofs

§2.2 turns from *meaning* to *reasoning about meaning*. An inference rule is a schema $P_1 \cdots P_n / C$ with metavariables (Reynolds is careful to distinguish these — italic/Greek, ranging over *phrases* — from the logic's own object-level variables, which stay sans-serif; substitution never renames metavariable instances, only object variables). A rule is **sound** iff every instance with valid premisses has a valid conclusion. A **formal proof** is a sequence of assertions, each the conclusion of a sound rule instance whose premisses appear earlier — crucially, *because the rules are sound*, every assertion appearing in a formal proof is automatically valid.

This is contrasted sharply with a **meta-proof**: an ordinary mathematical argument, conducted in the surrounding metalanguage using the *semantics* (the satisfaction relation itself), used to establish that a *rule* is sound in the first place. Propositions 4–10 in the special-classes material (see [[Special-Classes-Of-Assertions|the next article]]) are meta-proofs; the day-to-day derivations that *use* those propositions inside program-verification proofs are formal proofs. Confusing the two levels is a classic beginner error in any Hoare-logic or type-theory course: a formal proof lives *inside* the object logic and only chains together rule instances; a meta-proof lives in the ambient mathematics and is what justifies that the rules were safe to add in the first place.

An inference rule with zero premisses is an **axiom schema** (an *axiom*, if it additionally contains no metavariables — it's already its own instance). All of the familiar propositional and quantifier axiom schemata (modus ponens, $\forall$/$\exists$-introduction under a non-freeness side condition, the usual $\Rightarrow$/$\wedge$/$\vee$/$\neg$/$\Leftrightarrow$ schemata drawn from Kleene) remain sound unchanged in separation logic — they never mention $\mathrm{emp}$, $\mapsto$, $*$, or $\mathbin{-\!*}$, and the semantic clauses for $\wedge, \vee, \Rightarrow, \forall, \exists$ carry the heap along unchanged, so nothing about heaps could possibly invalidate them. On top of these, the notes restate $*$'s algebraic laws (commutativity, associativity, $\mathrm{emp}$ as identity, distributive/semidistributive laws, monotonicity, currying/decurrying) as formal inference rules — now derivable, in principle, from the semantic clauses above rather than merely asserted — plus specific rules for $\mapsto$ and $\hookrightarrow$, e.g.

$$e \hookrightarrow e' \wedge p \;\Rightarrow\; (e \mapsto e') * ((e \mapsto e') \mathbin{-\!*} p)$$

which is exactly the "carve out the known cell, keep the rest abstract via $\mathbin{-\!*}$" move that powers backward-reasoning rules throughout Chapter 3.

### Grounding: trusted kernels and proof-checking architecture

The formal-proof/meta-proof distinction is the same one that separates a proof assistant's **trusted kernel** from everything built on top of it. In Lean, the kernel only ever checks that a term has a type by re-deriving it through a small, fixed set of typing rules (the analogue of Reynolds's sound inference rules) — every tactic, every elaboration step, every `simp` call is a *meta-proof* in the sense used here: convincing machinery, running in the metalanguage, whose entire job is to eventually hand the kernel an object-level proof term built only out of trusted rule instances. If your compiler project embeds a theorem prover for verification conditions, this split is exactly the one you want to preserve: your constraint solver, your abstract interpreter, your CEGAR loop can all be arbitrarily untrusted and complex (meta-proofs, in this sense), *as long as* what they ultimately hand the checker is a certificate built from the small set of axioms and inference rules whose soundness you proved once, by hand, against the semantics — never re-derived per call.

## Where this leads

Everything from here is downstream of two things fixed in this section: the satisfaction relation (the ground truth every later soundness argument is checked against) and the sound/valid distinction (which prevents you from smuggling an unsound-but-plausible-looking rule into a proof system). [[Special-Classes-Of-Assertions|The next article]] uses exactly this apparatus — meta-proofs conducted directly against $s, h \models p$ — to classify assertions (pure, precise, intuitionistic, supported) whose special semantic properties license *extra* sound inference rules beyond the general-purpose ones given here; and [[Hoare-Triples-And-Specifications|the Hoare-triple specifications]] of Chapter 3 reuse this section's substitution laws verbatim when stating the substitution rule for commands. If you're building a verifier, this chapter is the layer that has to be *unconditionally* correct — everything downstream (the frame rule, the mutation/lookup/allocation rules, any decision procedure you build for entailment checking) is only as trustworthy as its soundness proof against this satisfaction relation.
