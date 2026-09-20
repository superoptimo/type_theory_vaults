---
title: "Intuitionism and Heyting Semantics"
book: "Topoi: The Categorical Analysis of Logic (Robert Goldblatt)"
chapter: "8 — Intuitionism and its Logic"
pages: "173–193"
tags: [intuitionistic-logic, heyting-algebra, kripke-semantics, constructivism, type-theory, proof-theory]
---

[[book-guidelines|↩ Back to guidelines]]

# Intuitionism and Heyting Semantics

## 0. Why the book stops to do philosophy before more category theory

Chapter 7 proved that $\mathrm{Sub}(d)$, the subobjects of any object in a topos, forms a lattice with a pseudo-complement operation that is *not* Boolean complementation in general. That was left as a slightly strange algebraic fact. Chapter 8 explains why it isn't strange at all — it's the algebra of a full, independently-motivated logic that mathematicians were already using before category theory existed. Once that identification is made, everything the book does from Chapter 9 onward (presheaf topoi, forcing, first-order truth in a topos) is really just: *take this logic and run it internally to more and more categories.* This chapter is the payoff-in-waiting for the entire book — it's where you learn what kind of logic topos logic actually is.

**What breaks without this chapter.** Without it, "$\mathrm{Sub}(d)$ is a Heyting algebra, not a Boolean algebra" reads as a curiosity about a fact you now have to take on faith. With it, you know exactly what that curiosity means: reasoning inside a topos is *constructive* reasoning, in the precise sense a working mathematician (Brouwer, Heyting) already gave that word decades before topos theory existed.

---

## 1. Constructivist philosophy: truth as something you build

### 1.1 The problem classical logic quietly assumes away

Classical logic treats every proposition $a$ as having a truth value — true or false — independent of whether anyone has, or ever will, determine which. This licenses **proof by contradiction as an existence proof**: to show something exists, assume it doesn't, derive a contradiction, conclude it does. Goldblatt's example: Cantor's set theory treats an infinite collection as a "thing-in-itself" you can reason about this way, whether or not you can produce any of its members.

L. E. J. Brouwer, following Kronecker's insistence that mathematical objects be "intuitively founded," rejected this. For an intuitionist, **a proposition $a$ is not "true" or "false" as a static fact — asserting $a$ *means* "I have carried out a mental construction demonstrating $a$."** Truth is epistemic, not metaphysical; it's indexed to what has actually been constructed, not to some Platonic fact of the matter.

**What breaks without this reading.** Under it, the classical tautology $a \lor \lnot a$ (law of excluded middle) stops being automatically true. Read constructively it says: *"I have constructed a proof of $a$, or I have constructed a proof that $a$ is impossible."* For an open problem — Goldblatt's example is Fermat's Last Theorem, undecided at the time of writing — neither disjunct has been constructed, so the disjunction itself has no construction. It is *not* true in the constructive sense, even though classically "of course it's true or false, we just don't know which" feels unassailable. That gap — between "no construction exists yet" and "the negation has been proved" — is the entire content of intuitionism, and it's what forces excluded middle, and everything downstream of it (like double-negation elimination $\lnot\lnot a \Rightarrow a$), out of the logic.

**[[Logical-Geometry#Grounding|Grounding]] — this is exactly `Option`/`Prop`, not `bool`.** In Rust, `bool` is a two-valued classical proposition: every value is `true` or `false`, decidable by inspection. A constructive proposition behaves more like

```rust
enum Evidence<E> {
    Proved(E),      // a construction/witness exists
    Unresolved,     // neither proved nor refuted (yet)
}
```

You cannot pattern-match `Unresolved` into "true" or "false" — that's the whole point. In Lean this is *not* an analogy but the literal mechanism: a proposition `P : Prop` is inhabited exactly when you can construct a term `p : P`. Lean's core kernel is intuitionistic — `Classical.em : ∀ (p : Prop), p ∨ ¬p` exists in the standard library, but it is an *axiom* you opt into (`open Classical` / `Classical.byCases`), not a theorem derivable from the kernel's rules. This is the load-bearing fact for your dependent-type-checker project: **a trusted kernel that stays constructive by default, and treats classical reasoning as an explicit, auditable axiom, is a smaller and more inspectable trusted computing base** than one that bakes excluded middle into every proposition. Curry–Howard makes the correspondence exact: intuitionistic propositional logic *is* the type theory of the simply-typed lambda calculus's `Prop`-like fragment, term-for-term.

---

## 2. Heyting's calculus (IL): the formal system

In 1930 Arend Heyting gave the axiomatic system that generates exactly the intuitionistically valid sentences. It uses the *same language* $PL$ as the classical calculus of Chapter 6:

- **Axioms:** all the classical axiom schemas I–XI *except* $a \lor \lnot a$.
- **Sole rule of inference:** Detachment (modus ponens).

Call this system **IL**. So IL is a strict subsystem of CL — every IL-theorem is a CL-theorem, but not conversely.

Some things that hold classically but are **not** IL-theorems:
$$a \lor \lnot a, \qquad \lnot\lnot a \Rightarrow a, \qquad \lnot a \lor \lnot\lnot a$$

Some things that *do* hold in IL, even though they look like fragments of the above:
$$a \Rightarrow \lnot\lnot a, \qquad \lnot\lnot\lnot a \Rightarrow \lnot a, \qquad \lnot\lnot(a \lor \lnot a)$$

That last one is worth sitting with: you can't *construct* $a \lor \lnot a$, but you *can* construct a proof that its double-negation-refutation is impossible — "it is not the case that ($a \lor \lnot a$) is refutable" is provable even though $a \lor \lnot a$ itself is not. This asymmetry — provability of $\lnot\lnot\varphi$ without provability of $\varphi$ — is precisely what a solver built on classical SAT/SMT engines will never surface, because those engines are built on Boolean algebras where $\lnot\lnot\varphi \equiv \varphi$ definitionally. If your verifier's proof certificates need to distinguish "provably decidable" from "provably not-refutable-in-principle," you need an IL-shaped proof system, not a Boolean one.

One more structural fact Goldblatt flags: in IL, **none of $\lnot, \land, \lor, \Rightarrow$ is definable from the others** (unlike CL, where e.g. $a \lor b \equiv \lnot a \Rightarrow b$). Each connective carries independent semantic content — a fact that becomes visible once you have algebraic semantics for IL, which is where Heyting algebras come in.

---

## 3. Heyting algebras: implication as an operation, not a derived formula

### 3.1 Building up to the definition

Start from an ordinary lattice $L = (L, \sqsubseteq)$ with meets $\sqcap$ and joins $\sqcup$. In a Boolean algebra, every element $a$ has a genuine complement $a'$ satisfying $a \sqcap a' = 0$ and $a \sqcup a' = 1$. Goldblatt generalizes this in two steps.

**Step 1 — pseudo-complement.** In a lattice with zero $0$, the **pseudo-complement** of $a$ (if it exists) is the *greatest* element disjoint from $a$ — i.e., the greatest $x$ with $a \sqcap x = 0$. Every Boolean complement is a pseudo-complement, but a pseudo-complement need not be a genuine complement (it need not satisfy $a \sqcup \lnot a = 1$).

**Step 2 — relative pseudo-complement, i.e. implication.** Generalize $0$ to an arbitrary element $b$: the pseudo-complement of $a$ *relative to* $b$, written $a \Rightarrow b$, is the greatest element $c$ such that $a \sqcap c \sqsubseteq b$:
$$a \Rightarrow b \;=\; \bigsqcup\{x \in L : a \sqcap x \sqsubseteq b\}$$

Equivalently, and this is the characterizing property (Goldblatt's Exercise 6): for all $x$,
$$x \sqsubseteq (a \Rightarrow b) \iff a \sqcap x \sqsubseteq b$$

**What breaks without the "relative to $b$" generalization.** If you only had absolute pseudo-complements ($b = 0$), you'd have negation but no implication — you couldn't ask "the weakest extra fact I need, on top of $a$, to guarantee $b$." That's exactly what $a \Rightarrow b$ answers, and it is the single most important sentence in this section for your project (see §5 below): **$a \Rightarrow b$ is, verbatim, "the weakest $x$ such that $a$ together with $x$ implies $b$."**

A lattice where $a \Rightarrow b$ exists for *every* pair is **relatively pseudo-complemented (r.p.c.)**.

### 3.2 The definition

> **Definition (Heyting algebra).** A **Heyting algebra** is an r.p.c. lattice with a zero $0$. Given such $H = (H, \sqsubseteq)$, define $\lnot a := a \Rightarrow 0$ — the pseudo-complement of $a$.

Every Boolean algebra is a Heyting algebra (its genuine complement satisfies the r.p.c. property), but the converse fails. This is the algebraic fact Chapter 7 was building toward: $\mathrm{Sub}(d)$ in any topos is a Heyting algebra, and it's Boolean *only in special topoi* (like $\mathbf{Set}$).

**Key facts (from Goldblatt's exercise list — the ones that matter downstream):**
- $a \Rightarrow a = 1$ (Exercise 7)
- $a \sqcap (a \Rightarrow b) \sqsubseteq b$ (Exercise 10) — this is **modus ponens read as a lattice inequality**
- $a \sqsubseteq \lnot\lnot a$ always holds (Exercise 20), but $\lnot\lnot a \sqsubseteq a$ **need not** — this failure is the algebraic shadow of $\lnot\lnot a \Rightarrow a$ not being an IL-theorem
- **Exercise 30**, the sharp dividing line: if a Heyting algebra satisfies $\lnot\lnot x \sqsubseteq x$ for *every* $x$, it is forced to be a Boolean algebra. So "how far is $\lnot\lnot a$ from $a$" is exactly the measure of how far a Heyting algebra is from being Boolean.

### 3.3 Concrete examples

Goldblatt runs six worked examples; the two most useful for building intuition:

- **Powerset lattice $(\wp(D), \subseteq)$**: $-A$ (ordinary set complement) is the pseudo-complement; $A \Rightarrow B := -A \cup B$ is the relative one. This *is* a Boolean algebra — no surprises.
- **Open sets of a topological space $(\mathcal{O}, \subseteq)$**: this is the example that actually fails to be Boolean, and is the intuition-carrying one. The pseudo-complement of open $U$ is $(-U)^\circ$ — the **interior** of the set-complement, not the set-complement itself (which need not be open). Relative pseudo-complement: $U \Rightarrow V = (-U \cup V)^\circ$. Since taking-interior can genuinely lose points (a boundary point of $U$ is in $-U \cup U = D$ but might not survive `interior`), $\lnot\lnot U \neq U$ in general — you can have $U$ dense but not equal to all of $D$, so $\lnot\lnot U = D \neq U$. This is a clean, checkable counterexample to excluded middle living entirely in ordinary topology, no philosophy required.
- **$\mathrm{Sub}(\mathscr{E})$, subobjects in a topos**: Goldblatt proves (via a pullback/exercise chain using the topos $\Omega$-axiom) that $\lnot f : \lnot a \rightarrowtail d$, defined by composing $f$'s classifying arrow with $\Omega$'s negation arrow, *is* the pseudo-complement of $f$ in the subobject lattice. This is the fact that finally cashes out Chapter 7's loose end: subobject lattices are Heyting algebras because Heyting-algebra structure is exactly what "pseudo-complement via a pullback square" gives you, in any topos, for free.

### 3.4 The categorical reading: Heyting algebra = CCC on a poset

Goldblatt makes the connection to Chapter 3's cartesian closed categories explicit. Viewing an r.p.c. lattice as a poset-category, the defining property
$$x \sqsubseteq (a \Rightarrow b) \iff a \sqcap x \sqsubseteq b$$
is *literally* the exponential adjunction $\mathscr{C}(x, b^a) \cong \mathscr{C}(x \times a, b)$ specialized to a poset (where a hom-set has at most one arrow). So:

> Categorially, a Heyting algebra is nothing more nor less than a Cartesian closed, finitely co-complete poset.

$a \sqcap b$ is the categorical product, $a \Rightarrow b$ is the exponential $b^a$, and the evaluation arrow $\mathrm{ev} : b^a \times a \to b$ is exactly the inequality $(a \Rightarrow b) \sqcap a \sqsubseteq b$ from Exercise 10. This is genuinely the same "implication is an internal hom" idea you already know from functional programming — `Fn(A) -> B` — just specialized to a category with at most one morphism between any two objects.

**Grounding — Rust.** A finite Heyting algebra (say the powerset-of-open-sets one, on a small finite poset frame) is directly implementable and directly testable:

```rust
use std::collections::BTreeSet;

/// A finite poset given by its covering/order relation.
struct Poset { leq: Vec<Vec<bool>> } // leq[p][q] == true iff p ⊑ q

/// Elements of P+ : upward-closed ("hereditary") subsets of the poset.
type Hereditary = BTreeSet<usize>;

fn is_hereditary(s: &Hereditary, p: &Poset) -> bool {
    s.iter().all(|&x| (0..p.leq.len()).all(|y| !p.leq[x][y] || s.contains(&y)))
}

/// Relative pseudo-complement a ⇒ b in the Heyting algebra of hereditary sets:
/// the largest hereditary c with a ∩ c ⊆ b.
fn implies(a: &Hereditary, b: &Hereditary, p: &Poset) -> Hereditary {
    (0..p.leq.len())
        .filter(|&x| {
            // x is in (a ⇒ b) iff every y ⊒ x that's in a is also in b
            (0..p.leq.len()).all(|y| !p.leq[x][y] || !a.contains(&y) || b.contains(&y))
        })
        .collect()
}
```

This is not a toy — it *is* the operation your refinement-type checker will need whenever a lattice of abstract facts (not just booleans) needs a "weakest condition that closes the gap" operator. See §5.

**Grounding — Lean.** The kernel-level statement is that `Prop` under `∧`, `∨`, `¬`, `→` forms exactly this structure (constructively). `Heyting algebra` and `Frame` are literal typeclasses in mathlib (`Mathlib.Order.Heyting.Basic`), with `⇨` for relative pseudo-complement and `himp_le_iff : a ⇨ b ≤ c ↔ ...`-shaped lemmas reproducing Goldblatt's exercises verbatim as theorems. If your dependent-type kernel's `Prop` universe is going to be intuitionistic (recommended, per §1), its internal propositional-connective algebra literally *is* a Heyting algebra by construction — this section is describing your own type theory's logic from the outside.

---

## 4. Kripke semantics: possible worlds as "stages of knowledge"

### 4.1 Motivation: why algebra alone isn't the intuitive picture

Heyting algebras give you a *sound and complete* semantics for IL, but they don't obviously *feel* like the epistemic story of §1 — "truth is what's been constructed so far." In 1965 Saul Kripke gave a semantics that does, adapted from his possible-worlds semantics for the modal logic S4 (McKinsey and Tarski had already shown S4's algebraic models, closure algebras, correspond to IL's algebraic models, Brouwerian algebras — Heyting algebras' order-duals).

The picture: a **poset of stages of knowledge** $P = (P, \sqsubseteq)$ ("frames," in this context), ordered by *time* — $p \sqsubseteq q$ means "$q$ is a later, more-informed stage than $p$." A proposition true at stage $p$ **must remain true at every later stage** — this is "persistence of constructive truth": once you've built a proof, it doesn't un-build itself. Formally: a set $A \subseteq P$ is **hereditary** if $p \in A$ and $p \sqsubseteq q$ implies $q \in A$. The collection of hereditary sets is $P^+$.

**What breaks without monotonicity.** If truth-sets weren't required to be hereditary, you could have a proposition true at $p$ and false at some later, strictly more-informed $q$ — i.e. knowledge could be *retracted*. That's not a model of anything Brouwer described; constructive knowledge is cumulative by definition. Monotonicity is the formal encoding of "you don't un-prove things."

### 4.2 The forcing relation

A **valuation** $V : \Phi_0 \to P^+$ assigns each sentence letter a hereditary set (the stages where it's known true). $M = (P, V)$ is a **model**. The forcing relation $M \Vdash_p a$ ("$a$ is true in $M$ at $p$") is defined by induction:

$$
\begin{aligned}
M \Vdash_p \pi_i &\iff p \in V(\pi_i) \\
M \Vdash_p (a \land \beta) &\iff M \Vdash_p a \text{ and } M \Vdash_p \beta \\
M \Vdash_p (a \lor \beta) &\iff M \Vdash_p a \text{ or } M \Vdash_p \beta \\
M \Vdash_p \lnot a &\iff \text{for all } q \sqsupseteq p,\ M \not\Vdash_q a \\
M \Vdash_p (a \Rightarrow \beta) &\iff \text{for all } q \sqsupseteq p,\ M \Vdash_q a \text{ implies } M \Vdash_q \beta
\end{aligned}
$$

Notice $\lnot$ and $\Rightarrow$ **quantify over the entire future** of $p$, not just $p$ itself — that's exactly why they aren't reducible to a local truth-value check, and why $a \lor \lnot a$ can fail: $\lnot a$ at $p$ requires *no future stage ever* establishes $a$, which is a much stronger, non-local demand than "$a$ is not currently established."

Setting $M(a) = \{p : M \Vdash_p a\}$, the clauses restate as lattice operations exactly matching §3:
$$M(a \land \beta) = M(a) \sqcap M(\beta), \quad M(a \lor \beta) = M(a) \sqcup M(\beta), \quad M(\lnot a) = \lnot M(a), \quad M(a \Rightarrow \beta) = M(a) \Rightarrow M(\beta)$$

where $\sqcap, \sqcup, \lnot, \Rightarrow$ on the right are the Heyting-algebra operations on $P^+$ (with $S \Rightarrow T$ *defined* as $\{p : \forall q \sqsupseteq p,\ q \in S \Rightarrow q \in T\}$). This is the theorem that unifies §3 and §4:

> **$M(a) = V(a)$**, and consequently **Kripke-validity on frame $P$ is the same as Heyting-algebra-validity on $P^+$.**

So Kripke frames and Heyting algebras aren't two competing semantics — every Kripke frame *generates* a Heyting algebra ($P^+$), and Kripke semantics is just Heyting-algebra semantics unfolded stage-by-stage, in a form that's usually far more tractable to compute with.

### 4.3 Completeness via the canonical model

Goldblatt sketches the Henkin-style route (as opposed to Kripke's original semantic-tableaux proof): build the **canonical frame** $P_{IL}$ whose elements are the **full sets** — sets $\Gamma$ of sentences that are (i) sound (contain only IL-consequences of $\vdash_{IL}$-derivable premises... more precisely closed under IL-derivability), (ii) closed under detachment, (iii) consistent (some sentence is excluded), (iv) *prime* ($a \lor \beta \in \Gamma \implies a \in \Gamma$ or $\beta \in \Gamma$). Ordered by $\subseteq$, with $V_{IL}(\pi_i) = \{\Gamma : \pi_i \in \Gamma\}$, the **Truth Lemma** holds:
$$M_{IL} \Vdash_\Gamma a \iff a \in \Gamma$$
Combined with Lindenbaum's Lemma ($\vdash_{IL} a$ iff $a$ is in every full set), this yields: $\vdash_{IL} a \iff P_{IL} \Vdash a \iff a$ is valid on every frame.

This "full set = maximal-consistent-and-prime" construction is the same shape as a Lindenbaum-algebra completeness proof for classical propositional logic, and structurally the same shape as the model-existence lemmas behind SAT-completeness arguments — a consistent, sufficiently-complete set of formulas *is* a model.

### 4.4 Frame conditions ↔ logical strength

A striking payoff of Kripke semantics over pure Heyting-algebra semantics: extra axioms correspond to simple **order-theoretic conditions on the frame**, computable and checkable directly:

- **Discrete frames** ($p \sqsubseteq q \iff p = q$, i.e. no nontrivial future) validate $a \lor \lnot a$ — with no distinct future stages, "not $a$" collapses to classical negation, and Kripke-validity on the discrete 2-point frame is *exactly* the classical BA-validity of Chapter 6.
- **Weakly linear frames** ($p \sqsubseteq q$ and $p \sqsubseteq r$ implies $q \sqsubseteq r$ or $r \sqsubseteq q$) validate $(a \Rightarrow \beta) \lor (\beta \Rightarrow a)$ — adjoining this axiom to IL gives Dummett's system **LC**, and the canonical-frame method shows LC-theorems are exactly the sentences valid on all weakly linear frames.
- A frame with a genuine branch (two incomparable futures, Goldblatt's two-point antichain example) is enough to falsify $(\pi_1 \Rightarrow \pi_2) \lor (\pi_2 \Rightarrow \pi_1)$ — incomparable futures are exactly what breaks total comparability of implications.

This "logic ↔ frame-shape" correspondence is a template you'll meet again constantly: **axiomatic strength trades off against structural constraints on the model class**, the same pattern that shows up in modal-logic correspondence theory and in choosing abstract domains for program analysis (a coarser/more constrained domain validates more approximations, at the cost of precision).

### 4.5 Grounding: evaluating forcing is a straightforward fixpoint-free traversal

**Python** (fast to read, illustrative only):
```python
def forces(model, p, formula):
    match formula:
        case ('atom', name):
            return p in model.valuation[name]
        case ('and', a, b):
            return forces(model, p, a) and forces(model, p, b)
        case ('or', a, b):
            return forces(model, p, a) or forces(model, p, b)
        case ('not', a):
            return all(not forces(model, q, a) for q in model.frame.future(p))
        case ('implies', a, b):
            return all(forces(model, q, b) for q in model.frame.future(p)
                       if forces(model, q, a))
```
Note `not` and `implies` are the only cases that recurse over `future(p)` rather than just `p` — this directly mirrors the forcing clauses above, and it's the computational reason those two connectives are the ones IL treats specially.

**Rust**, as a typestate/trait pattern — worth building because it's the shape of a real refinement-type or Hoare-logic evaluator:
```rust
trait Frame {
    fn future(&self, p: usize) -> Vec<usize>; // all q with p ⊑ q, including p
}

fn forces(m: &Model, f: &impl Frame, p: usize, phi: &Formula) -> bool {
    match phi {
        Formula::Atom(i) => m.valuation[*i].contains(&p),
        Formula::And(a, b) => forces(m, f, p, a) && forces(m, f, p, b),
        Formula::Or(a, b)  => forces(m, f, p, a) || forces(m, f, p, b),
        Formula::Not(a)    => f.future(p).iter().all(|&q| !forces(m, f, q, a)),
        Formula::Implies(a, b) =>
            f.future(p).iter().all(|&q| !forces(m, f, q, a) || forces(m, f, q, b)),
    }
}
```

---

## 5. Where this leads — and why it's load-bearing for the compiler/elaborator project

**1. Weakening/persistence is literally hereditary-truth-sets.** The requirement that forcing be monotone under $\sqsubseteq$ — "once true at $p$, true at every $q \sqsupseteq p$" — is *the same lemma* as **context weakening** in a type theory: a judgment $\Gamma \vdash e : \tau$ derivable in context $\Gamma$ remains derivable in any extension $\Gamma, \Delta$. Kripke's "stage of knowledge" ordered by information-gain is exactly a **typing context ordered by extension**, and hereditary truth is exactly what makes weakening a theorem instead of an assumption you bolt on. If your elaborator's metavariable-context grows monotonically as unification proceeds, you are literally building a Kripke frame, and its soundness proof will look like §4.2.

**2. $a \Rightarrow b$ as "weakest $x$ closing the gap" is the shape of a weakest-liberal-precondition operator.** Relative pseudo-complement ($x \sqsubseteq (a \Rightarrow b) \iff a \sqcap x \sqsubseteq b$) is not an analogy to `wlp` in Hoare logic — it *is* the same universal property: the weakest additional assumption that, combined with $a$, guarantees $b$. If your abstract-interpretation domain for invariant generation is itself only a lattice (not necessarily Boolean — e.g. intervals, octagons, or a Horn-clause solution space), the "weakest condition" operator you need for backward analysis is exactly this relative pseudo-complement, and Goldblatt's Exercises 10–17 are, read that way, a small catalogue of Hoare-triple-composition lemmas already proved for you.

**3. The Boolean/Heyting split is the classical/constructive split in your trusted kernel, decided once, felt everywhere.** Whether your kernel's `Prop` connectives form a Heyting algebra (constructive) or collapse to a Boolean one (classical, `Classical.em` always available) determines whether $\lnot\lnot P \to P$ is free or an axiom you must invoke and record in a proof certificate. For a proof-producing architecture with a small trusted computing base, staying Heyting (constructive) by default and making classical reasoning an explicit, logged axiom application is the more auditable design — this is literally how Lean's kernel is built.

**4. This chapter is the direct prerequisite for Chapters 9–11.** Functor categories $\mathbf{Set}^P$ (Ch. 9) turn Kripke frames $P$ into topoi; their subobject classifier (Ch. 10) turns out to *be* the Heyting algebra $P^+$ of hereditary sets constructed here; and the completeness/soundness argument of §4.3 reappears verbatim as the completeness theorem for topos-valid sentences (Ch. 11). Everything algebraic in this chapter (§3) and everything relational (§4) are about to be re-derived as two views of a single categorical structure — you now have both views in hand before that happens.
