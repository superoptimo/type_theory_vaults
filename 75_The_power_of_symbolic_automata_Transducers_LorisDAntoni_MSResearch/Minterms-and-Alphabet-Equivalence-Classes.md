---
title: Minterms and Alphabet Equivalence Classes
source: "The Power of Symbolic Automata and Transducers (D'Antoni & Veanes, 2017)"
chapter: "Chapter 2, Section 2.1 — Alphabet Equivalence Classes"
pages: "pp. 4-6"
tags: [symbolic-automata, minterms, sat-smt-csp, boolean-algebra, automata-theory]
---

[[book-guidelines|↩ Back to guidelines]]

## The problem: an s-FA doesn't run on a classic automata algorithm

A symbolic finite automaton (s-FA) labels its transitions with *predicates* — formulas like $\varphi_{>0}(x) \equiv x > 0$ or $\varphi_{odd}(x) \equiv x \% 2 = 1$ — rather than concrete symbols. That's the entire point of the model: it lets you reason about automata over infinite domains (all integers, all Unicode code points, all IEEE floats) without ever enumerating the domain.

But here's what breaks the moment you want to *reuse* fifty years of classic automata theory: Hopcroft's minimization, the standard product construction, Myhill-Nerode-style equivalence-class reasoning — all of it is written assuming transitions are labeled by elements of a small, enumerable alphabet $\Sigma$. An s-FA transition guarded by $x > 0$ isn't labeled by a symbol at all; it's labeled by a *set* of symbols, potentially infinite, described intensionally. You cannot loop "for each $a \in \Sigma$" over the integers. If you want to intersect two s-FAs, or minimize one, or just compare two of them state-by-state the way a textbook DFA product construction does, you need some way to talk about "which characters this transition cares about" using a finite vocabulary.

The paper's answer is **alphabet equivalence classes**, built from an object called a **minterm**. The core idea, stated plainly before any notation: even though the underlying domain $D$ is infinite, the *finitely many* predicates actually appearing in your automaton (or automata) can only carve $D$ into finitely many distinguishable regions. Two elements of $D$ that fall in the same region are, as far as this automaton is concerned, interchangeable — no sequence of transitions can tell them apart. Minterms are exactly those regions, made syntactically explicit as Boolean formulas.

## Minterms: the maximal satisfiable combinations

Let $S$ be a finite set of predicates — say, all the guards appearing across one or several s-FAs sharing an alphabet algebra. A **minterm** of $S$ is a maximal satisfiable Boolean combination of the predicates in $S$: for every predicate $\varphi \in S$, you either conjoin $\varphi$ or its negation $\neg\varphi$, taking one such literal per predicate, and the resulting conjunction must be satisfiable (denote it possible to find some domain element it accepts).

$$
\mathrm{Minterms}(S) = \Big\{\, \bigwedge_{\varphi \in S} \ell_\varphi \;\Big|\; \ell_\varphi \in \{\varphi, \neg\varphi\},\ \mathrm{SAT}\Big(\bigwedge_{\varphi \in S} \ell_\varphi\Big) \Big\}
$$

Concretely, take the two predicates from the running example in the paper (an SMT algebra over the integers, $\text{SMT}_\mathbb{Z}$):

$$
S = \{\varphi_{>0},\ \varphi_{odd}\}
$$

There are $2^{|S|} = 4$ ways to pick a literal per predicate, and here all four turn out satisfiable, giving

$$
\Sigma = \mathrm{Minterms}(S) = \{\underbrace{\varphi_{odd}\wedge\varphi_{>0}}_{a},\ \underbrace{\neg\varphi_{odd}\wedge\varphi_{>0}}_{b},\ \underbrace{\varphi_{odd}\wedge\neg\varphi_{>0}}_{c},\ \underbrace{\neg\varphi_{odd}\wedge\neg\varphi_{>0}}_{d}\}
$$

These four minterms partition all of $\mathbb{Z}$ into four disjoint classes: positive odd numbers ($a$), positive even numbers ($b$), non-positive odd numbers ($c$), non-positive even numbers ($d$). Not every combination need be satisfiable in general — if $S$ contained mutually contradictory predicates, some of the $2^{|S|}$ candidate conjunctions would simply be dropped for failing the SAT check, which is exactly why $|\mathrm{Minterms}(S)| \le 2^{|S|}$ rather than equal to it.

The crucial property, stated informally right after the definition: **using only the predicates in $S$, there is no way to distinguish two elements inside the same minterm.** Given any accepted string, swapping the number $1$ for the number $3$ anywhere in it changes nothing about acceptance, because both live inside minterm $a$. This is the symbolic analogue of the classic Myhill-Nerode indistinguishability relation — except the equivalence classes are being defined *syntactically*, from the automaton's own guards, not semantically from language behavior.

## Predicate abstraction: compiling the s-FA into a classic automaton

Once you have $\Sigma = \mathrm{Minterms}(S)$ as a genuinely finite alphabet, the compilation step is mechanical. Replace each symbolic transition $p \xrightarrow{\varphi} q$ with one concrete transition per minterm that overlaps $\varphi$:

$$
p \xrightarrow{\varphi} q \quad\rightsquigarrow\quad \Big\{\, p \xrightarrow{c} q \;\Big|\; c \in \Sigma,\ \mathrm{SAT}(c \wedge \varphi) \,\Big\}
$$

Every minterm $c$ either entails $\varphi$ or entails $\neg\varphi$ (it's built from a literal choice over every predicate in $S \supseteq \{\varphi\}$), so this test is really just "is $c$ one of the minterms consistent with $\varphi$" — there's no partial overlap to worry about. The resulting object is now, by construction, an ordinary finite automaton over the finite alphabet $\Sigma$, and every classic algorithm applies directly.

Running this on the paper's example: $M_{pos}$ (accepts strings of only positive numbers, guard $\varphi_{>0}$) becomes a one-state DFA over $\Sigma$ with transitions on $a$ and $b$ (the two minterms entailing $\varphi_{>0}$) looping back to itself. $M_{ev/odd}$ (accepts even-length strings of only odd numbers) becomes a two-state DFA alternating states on $a$ and $c$ (the minterms entailing $\varphi_{odd}$). Taking the classic product construction of these two DFAs over $\Sigma$ — no symbolic machinery needed anymore — only the $a$-transitions survive, exactly matching the symbolic product $M_{pos}\times M_{ev/odd}$ computed directly on the s-FAs.

This technique is called **predicate abstraction**: replacing an infinite-domain object with a finite quotient built from the finitely many predicates that actually appear, so that off-the-shelf finite-state reasoning becomes applicable. (The paper notes this same name and idea is a workhorse of program verification more broadly — abstracting an infinite program state space down to the finitely many predicates a verifier actually tracks is the identical move.) The move is general: given any s-FA $M$, and any finite predicate set $S \supseteq \mathrm{Predicates}(M)$, $M$ compiles into a *symbolically equivalent* classic automaton over $\mathrm{Minterms}(S)$ — "symbolically equivalent" meaning it accepts the same strings, just routed through the abstracted alphabet instead of the raw guards.

## What breaks without minterms

Without this construction, every one of the "closure and decidability" results from earlier in Chapter 2 — Boolean closure, emptiness, equivalence, determinization — would each need its own bespoke symbolic reformulation of a classic algorithm, reproving from scratch that the finite-alphabet argument still goes through when the alphabet is a predicate space. Minterms instead give a uniform reduction: prove the correctness of the reduction once, and every classic finite-automata algorithm becomes available for free on the compiled automaton. The price paid for that convenience is what the next section (parametric complexity) is about — the abstraction step itself can be expensive, because $|\Sigma|$ is not fixed the way a real programming language's character set is; it depends on how many predicates the automaton happens to use and how they interact.

## How many minterms can there be? — Theorem 4

Since $\Sigma = \mathrm{Minterms}(M) \overset{\mathrm{def}}{=} \mathrm{Minterms}(\mathrm{Predicates}(M))$ is computed by literally enumerating up to $2^{|S|}$ candidate Boolean combinations and SAT-checking each one, this compilation is exponential in the number of *distinct predicates*, not the number of states. The paper's Theorem 4 nails down exactly how bad this gets as a function of the state count alone, for a **complete and normalized** s-FA (recall: normalized means at most one transition between any ordered pair of states, so $|\Delta| \le n^2$; complete means every state has an outgoing transition for every character).

> **Theorem 4 (Number of minterms).** Let $M$ be a complete and normalized s-FA with $n$ states. Then $|\mathrm{Minterms}(M)| \le 2^{(n^2)}$. If $M$ is deterministic, then $|\mathrm{Minterms}(M)| \le 2^{n\log_2 n}$.

**General bound — $2^{(n^2)}$.** Normalization caps the number of *distinct* transition guards at $|\Delta| \le n^2$ (one composite guard per ordered pair of states, and $\bot$ where there's no transition — but $\bot$ contributes nothing new to $S$). So $S = \mathrm{Predicates}(M)$ has $|S| \le n^2$, and since $|\mathrm{Minterms}(S)| \le 2^{|S|}$ by definition (you're choosing one literal per predicate), the bound $|\mathrm{Minterms}(M)| \le 2^{n^2}$ falls straight out. Nothing about determinism was used yet — this is the crude combinatorial ceiling for *any* s-FA.

**Deterministic bound — $2^{n \log_2 n}$, exponentially tighter.** This is the interesting half of the theorem, and it's a genuine structural argument, not a restatement of the generic bound. Determinism means each state $p_i$'s outgoing guards are pairwise disjoint (that's the definition: distinct targets never share a satisfying character), so the set of guards leaving $p_i$ defines an actual **partition** $P_i$ of the domain $D$ — every element of $D$ falls into exactly one outgoing transition's guard from $p_i$. Because $M$ is normalized, $|P_i| \le n$ (at most one transition to each of the $n$ possible target states).

Now here's the key move: a minterm is precisely an element of the **common refinement** of all $n$ of these per-state partitions — $\{[\![\mu]\!] \mid \mu \in \mathrm{Minterms}(S)\} = \bigsqcap_{i<n} P_i$, where $\sqcap$ denotes the coarsest partition refining every $P_i$ simultaneously (i.e., $x, y$ land in the same refined block iff every single $P_i$ puts them in the same block as each other). Intuitively: a minterm groups together exactly the domain elements that are indistinguishable *from every state's perspective at once* — since determinism means "state + character" always picks out one target, two elements are in the same minterm iff, from **every** state $p_i$, they'd be routed to the same successor.

Refining $n$ partitions, each of size at most $n$, together: the number of blocks in the common refinement is bounded by the product of the individual partition sizes, $\prod_{i<n}|P_i| \le n^n$. So $|\mathrm{Minterms}(S)| \le n^n = 2^{n \log_2 n}$ — exponentially smaller than the general $2^{n^2}$ bound (compare $n \log_2 n$ against $n^2$ in the exponent: for $n = 100$, that's roughly $2^{664}$ against $2^{10000}$). **Determinism is what buys you the improvement**, because it's the only thing guaranteeing each state's own view of the domain is already a genuine partition of bounded size $n$, rather than an unstructured set of possibly-overlapping guards.

## Worked grounding

**Rust.** The predicate-abstraction step is exactly a fold that discovers equivalence classes by testing conjunctions for satisfiability, then dispatches on which class a value belongs to — a good fit for an enum-of-predicates plus a "classify" function:

```rust
/// A guard from the alphabet theory, e.g. x > 0 or x % 2 == 1.
trait Predicate<D>: Clone + Eq + std::hash::Hash {
    fn eval(&self, d: &D) -> bool;
    fn and(&self, other: &Self) -> Self;
    fn not(&self) -> Self;
    fn is_sat(&self) -> bool; // delegates to an SMT call in practice
}

/// A minterm is a conjunction of literals over S, materialized as an id
/// plus the composite predicate it denotes, so it can be re-tested for SAT
/// against any other guard in the automaton.
struct Minterm<P> {
    id: usize,
    formula: P,
}

fn compute_minterms<P: Predicate<D>, D>(predicates: &[P]) -> Vec<Minterm<P>> {
    let mut minterms = Vec::new();
    // 2^|S| candidate literal-choices; SAT-check each, keep the satisfiable ones.
    for mask in 0..(1u64 << predicates.len()) {
        let mut formula = predicates[0].clone(); // placeholder init
        let mut first = true;
        for (i, p) in predicates.iter().enumerate() {
            let literal = if mask & (1 << i) != 0 { p.clone() } else { p.not() };
            formula = if first { literal } else { formula.and(&literal) };
            first = false;
        }
        if formula.is_sat() {
            let id = minterms.len();
            minterms.push(Minterm { id, formula });
        }
    }
    minterms
}

/// Predicate abstraction: replace a symbolic guard with the set of minterm
/// ids it's consistent with — this IS the compiled classic-automaton alphabet.
fn expand_transition<P: Predicate<D>, D>(guard: &P, minterms: &[Minterm<P>]) -> Vec<usize> {
    minterms
        .iter()
        .filter(|m| m.formula.and(guard).is_sat())
        .map(|m| m.id)
        .collect()
}
```

The `is_sat` calls are where the real cost lives — in the SMT-algebra case each one is a solver query — which is precisely the "predicate space explosion" the paper flags as the s-FA-specific complexity axis that has no classic-automata analogue (developed further in the Parametric Complexity topic).

**Lean.** The mathematical content of Theorem 4's deterministic case — a common refinement of $n$ partitions, each bounded, itself bounded by the product of sizes — is a statement `Mathlib` already has infrastructure for (`Setoid` and `Finpartition` machinery), because it's the exact same shape of reasoning used for a product of quotients:

```lean
-- Each state pᵢ induces a finite partition of the domain D via its
-- outgoing transitions (determinism ⇒ disjoint guards ⇒ genuine partition).
-- Refining n partitions together (⊓ over Setoid) has cardinality bounded
-- by the product of the individual partition sizes — the same combinatorial
-- fact underlying Theorem 4's n^n bound.
example (n : ℕ) (P : Fin n → Setoid D) (h : ∀ i, Nat.card (Quotient (P i)) ≤ n) :
    Nat.card (Quotient (⨅ i, P i)) ≤ n ^ n := by
  sorry -- the informal proof: refine one partition at a time, size multiplies each step
```

This is worth citing by name because it's a recurring shape: any time your compiler's abstract-interpretation lattice is built as a **product of finitely many finite abstractions** (e.g., combining a sign-analysis domain with a parity domain — literally this example's $\varphi_{>0}$ and $\varphi_{odd}$), the number of reachable abstract states is bounded the same way minterms are here.

**Python**, as a quick illustrative sketch of brute-force minterm enumeration (fine for small $|S|$, not what you'd ship):

```python
from itertools import product

def minterms(predicates, is_sat):
    """predicates: list of (name, predicate_fn); is_sat: satisfiability oracle
    over a conjunction of literals, each literal a (predicate, polarity) pair."""
    result = []
    for bits in product([True, False], repeat=len(predicates)):
        literals = list(zip(predicates, bits))
        if is_sat(literals):
            result.append(literals)
    return result  # |result| <= 2**len(predicates), per Theorem 4's general bound
```

## Synthesis: where this fits, and why it matters for the CSP kernel

Structurally, minterms sit directly downstream of Section 2's Boolean-algebra and s-FA definitions and directly upstream of everything else in Chapter 2: Boolean closure, emptiness/equivalence decidability, and minimization are all either *implemented via* or *justified by* the fact that an s-FA can always be viewed, after abstraction, as a classic automaton over $\mathrm{Minterms}(M)$. The very next subsection (Parametric Complexity) exists because this abstraction is not free — $f(\ell)$, the cost of a single satisfiability check, and the sheer count of minterms, become new complexity parameters that a purely state-counting analysis (as in classic automata theory) can't see.

For the `sat-smt-csp` focus area this topic is tagged under: this is a clean, self-contained illustration of **predicate abstraction** as a general technique for taming an infinite domain with finitely many SAT queries — exactly the move your abstract-interpretation / CSP kernel will need when it represents a program variable's possible values as a finite lattice built from a handful of tracked predicates (sign, parity, range bounds, and so on) rather than enumerating concrete values. Theorem 4's determinism-dependent bound is also a direct preview of a recurring cost concern in that kernel: whenever you combine several finite abstract domains via a product construction (the common-refinement argument here), the number of resulting abstract states is bounded by the *product* of each domain's size, not their sum — the same $n^n$-shaped blowup that shows up whenever finite abstractions are composed rather than kept separate. Concretely, if your CSP kernel tracks both a sign domain and a parity domain over an integer variable, the reachable combined-state count follows exactly this partition-refinement bound — worth remembering before combining more than a couple of finite domains naively.

## Where this leads

The very next subsection, Parametric Complexity, makes explicit what minterm-based compilation costs in practice — it introduces $f(\ell)$, the satisfiability-checking cost for predicates of size $\ell$, as a second complexity axis alongside the classic state-count $n$, and shows how Moore's and Hopcroft's minimization algorithms trade off state-complexity savings against alphabet-complexity cost in ways that have no analogue when the alphabet is finite from the start.
