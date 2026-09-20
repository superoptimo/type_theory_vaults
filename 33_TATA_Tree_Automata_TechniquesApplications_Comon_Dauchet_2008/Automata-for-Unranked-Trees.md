---
title: Automata for Unranked Trees
source: "Tree Automata Techniques and Applications (TATA)"
chapter: "Chapter 8, §8.2–8.6"
pages: "199–228"
tags: [tree-automata, hedge-automata, unranked-trees, xml, minimization, wmso]
---

[[book-guidelines|↩ Back to guidelines]]

## Why ranked trees aren't enough

Every automaton model up to this point in the book has quietly leaned on one assumption: a node's label tells you exactly how many children it has. That's what "ranked alphabet" means — $f\in F_n$ comes with its arity $n$ baked in, and a transition rule $f(q_1,\dots,q_n)\to q$ can simply pattern-match on a fixed-length tuple of child states.

That assumption is false for the trees you actually meet in semi-structured data. An HTML `<table>` can have any number of `<tr>` rows; a `<tr>` can have any number of `<td>` cells. The *label* `table` doesn't determine the arity — the document does. If you tried to force this into the ranked-tree mold, you'd need a separate symbol `table_2`, `table_3`, `table_4`, ... for every possible row count, and a real automaton would need infinitely many transition rules to cover them all. That's not a finite object anymore.

**[[Automata-with-Constraints#What breaks|What breaks]] without a new model:** you could, in principle, statically bound the maximum arity you'll ever see and pad everything out to that width — but real documents have no such bound, and even if they did, you'd be manufacturing an enormous, mostly-unused alphabet just to preserve a modeling convenience (fixed arity) that the data itself doesn't respect. The honest move is to build an automaton model where a node's number of children is *unbounded and label-independent* — a **hedge automaton** — and that's this chapter's subject.

If you're used to writing a Rust AST, this is a familiar tension: you already know the difference between an enum variant like `BinOp { left: Box<Expr>, right: Box<Expr> }` (fixed arity, ranked) and one like `Call { callee: Box<Expr>, args: Vec<Expr> }` (variable arity, unranked). Hedge automata are the formal theory of recognizing sets of the second kind of tree.

## Unranked trees and hedges

Formally, drop the arity restriction: an unranked tree over a label set $\Sigma$ is a partial function $t:\mathbb{N}^*\to\Sigma$ with prefix-closed, finite domain $\mathrm{Pos}(t)$ — same shape as the Preliminaries' definition, just without the "the label determines which child-positions must exist" clause. A node labeled $a$ can have $0, 1, 2, \dots$ children, however many the tree actually has.

Write $a(t_1\cdots t_n)$ for the tree with root $a$ and children $t_1,\dots,t_n$ in that left-to-right order. The sequence $t_1\cdots t_n$ itself — zero or more unranked trees side by side — is called a **hedge** (yes, literally "a row of trees," like a hedge is a row of bushes). This gives a clean inductive definition:

- A sequence of unranked trees (including the empty sequence $\epsilon$) is a hedge.
- If $h$ is a hedge and $a\in\Sigma$, then $a(h)$ is an unranked tree.

This is exactly the recursive shape of a `Vec<Node>` in a Rust AST: a node's children are a *list*, not a fixed tuple, and the empty list is allowed.

## Hedge automata: symbolically compressing infinitely many rules

Here's the actual technical problem a hedge automaton has to solve. A bottom-up ranked-tree automaton's rule $f(q_1,\dots,q_n)\to q$ works because $n$ is fixed by $f$'s arity — you write down finitely many rules, one shape per symbol. For an unranked symbol $a$, there's no such bound: you'd need a rule for every possible *length* of child-state-sequence, which is again infinitely many rules.

The fix is the same idea WSkS used to code infinite sets finitely (see the companion article on WSkS): don't enumerate, describe with a finite specification. Specifically, replace "list all applicable sequences of child states" with **a regular language over states describing which sequences are allowed**:

$$a(R) \to q, \qquad R \subseteq Q^*\text{ regular.}$$

A **nondeterministic finite hedge automaton (NFHA)** is $A=(Q,\Sigma,Q_f,\Delta)$ with $\Delta$ a finite set of such rules. $R$ is called the rule's **horizontal language** — "horizontal" because it constrains a sequence of siblings, as opposed to the "vertical" structure of parent/child.

**What breaks without regularity specifically:** you could let $R$ range over a richer class (context-free languages, say), but then the horizontal check itself would need unbounded memory to decide — defeating the purpose of a *finite*-state automaton. Regular languages are exactly the class checkable with bounded memory (a DFA), so they're the natural fit for "finite automaton with symbolic sibling-sequence constraints."

A run of $A$ on $t$ is a state-labeled copy $r$ of $t$'s shape such that at every node $p$ labeled $a$ with $n$ children, the sequence of the children's states in $r$ lies in some rule's horizontal language for $a$, and $r(p)$ is that rule's target state. $t$ is accepted if some run labels the root with a final state.

A worked example makes the compression concrete: to accept all trees of height 1 with root $a$, an even (possibly zero) number of $b$-leaves, you don't write $a\to q$, $a(q_bq_b)\to q$, $a(q_bq_bq_bq_b)\to q,\dots$ forever — you write one rule, $a((q_bq_b)^*)\to q$, with $(q_bq_b)^*$ a regular expression over the state alphabet $\{q_b\}$.

## Determinism, completeness, and the subset construction

An NFHA is **deterministic (DFHA)** if for any two rules $a(R_1)\to q_1$ and $a(R_2)\to q_2$, either $R_1\cap R_2=\emptyset$ or $q_1=q_2$ — i.e., no sibling-sequence is simultaneously covered by two rules disagreeing on the resulting state. It's **complete** if every tree has at least one accepting-or-rejecting run (every label/sibling-sequence combination is covered by some rule); as with NFTAs, you can always complete an automaton for free by adding one sink state.

**Theorem 8.2.8** (subset construction): every NFHA has an equivalent DFHA, at the cost of an exponential blow-up in the number of states — structurally identical to the ranked case (Theorem 1.1.9), except now the construction has to additionally verify that the induced horizontal languages over *sets of states* are still regular (they are, via closure of regular languages under substitution).

```rust
// A hedge-automaton rule set, mirroring a(R) -> q.
// Each rule's horizontal language is itself represented by
// something that recognizes sequences of states (e.g. an NFA over Q).
struct HedgeRule<Q> {
    label: char,
    horizontal: RegularLangOverStates<Q>, // R subset of Q*
    target: Q,
}

// Bottom-up evaluation: for a node with children c1..cn already
// labeled with states q1..qn, find a rule whose horizontal
// language contains q1...qn and whose label matches.
fn step<Q: Clone + PartialEq>(
    rules: &[HedgeRule<Q>],
    label: char,
    child_states: &[Q],
) -> Vec<Q> {
    rules.iter()
        .filter(|r| r.label == label && r.horizontal.contains(child_states))
        .map(|r| r.target.clone())
        .collect()
}
```

## Encoding unranked trees as ranked ones

Rather than redo every closure-property proof from Chapter 1 in the unranked setting, the book takes a shortcut: encode unranked trees *as* ranked trees, transfer results across the encoding, and get closure (union, intersection, complement, projection) essentially for free. Two encodings are given, each useful for a different reason.

### First-child-next-sibling (FCNS)

This is the encoding you'd write in Rust without thinking twice: represent each node by two pointers, one to its first child and one to its next sibling to the right. Concretely, every unranked symbol $a$ becomes a *binary* ranked symbol $a(\cdot,\cdot)$, plus one new constant $\#$ standing for "no such pointer." Inductively:

- $\mathrm{fcns}(a) = a(\#,\#)$ for a leaf,
- $\mathrm{fcns}(a(t_1\cdots t_n)) = a(\mathrm{fcns}(t_1\cdots t_n), \#)$,
- $\mathrm{fcns}(t_1\cdots t_n) = \mathrm{fcns}(t_1)[\mathrm{fcns}(t_2\cdots t_n)]_2$ for $n\ge 2$ (graft the encoding of "the rest of the hedge" onto the first tree's right-pointer slot).

```rust
enum RankedFCNS<L> {
    Node(L, Box<RankedFCNS<L>>, Box<RankedFCNS<L>>), // (first-child, next-sibling)
    Hash, // '#': no such pointer
}
```

This is literally the "linked list of children" representation: `first_child: Option<Box<Node>>`, `next_sibling: Option<Box<Node>>`. $\mathrm{fcns}$ is a bijection between hedges and this binary-tree shape, so it's invertible, and **Proposition 8.3.2 / 8.3.3**: hedge-recognizability transfers in both directions across $\mathrm{fcns}$ — an NFHA can be compiled into an NFTA on the FCNS encoding (each rule's horizontal-language NFA gets "unrolled" along the right-pointer spine) and vice versa.

### The extension encoding ($@$)

The second encoding is more algebraic, and it's the one that does real technical work later (minimization, §8.6). The idea: pick one binary **operation** that builds up any unranked tree from atoms, and represent the tree by the *term* that constructs it.

The operation is $@$ ("extend"): given $t=a(t_1\cdots t_n)$ and any tree $t'$, $t@t' = a(t_1\cdots t_n t')$ — append $t'$ as the new rightmost child. Every unranked tree can be built uniquely this way starting from height-0 trees (bare labels): $a(bc) = (a@b)@c$. So define $\mathrm{ext}(a)=a$ for leaves and $\mathrm{ext}(a(t_1\cdots t_n)) = @(\mathrm{ext}(a(t_1\cdots t_{n-1})),\mathrm{ext}(t_n))$ — recursively peel off the rightmost child.

This is precisely how you'd represent a variable-arity constructor using only binary application in a term language — the same trick a curried function application tree uses to represent an $n$-ary call with only binary `App` nodes. $\mathrm{ext}$ is a bijection $T(\Sigma)\to T(F_{ext}^\Sigma)$ ($F_{ext}^\Sigma=\{@(\cdot,\cdot)\}\cup\Sigma$, treating $\Sigma$ now as constants), and **Theorem 8.3.7**: hedge-recognizability transfers across $\mathrm{ext}$ in both directions too.

With both encodings established, **Theorem 8.3.8 / 8.3.9**: recognizable unranked-tree languages are closed under union, intersection, complementation, projection, and inverse projection — for free, by pushing the operation through to whichever encoding's ranked-tree theory (Chapter 1, §1.3–1.4) already proved it.

## WMSO: the logic side, briefly

Chapter 3's WSkS logic talked about a node's $i$-th successor via the term $xi$ — but for unranked trees, a node can have unboundedly many successors, so there's no finite vocabulary of successor symbols to write formulas with. The fix: replace "access the $i$-th child directly" with two binary relations, $\mathrm{child}(x,y)$ ("$y$ is a child of $x$") and $\mathrm{next\text{-}sibling}(x,y)$ ("$y$ is immediately to the right of $x$"). **Weak monadic second-order logic (WMSO)** over this signature plays exactly WSkS's role: **Theorem 8.4.2**, WMSO-definable = recognizable, proved by translating into WS2S over the FCNS encoding (the two binary relations map naturally onto FCNS's two pointer directions) and invoking Chapter 3's Thatcher–Wright result. This is the same "logic ↔ automaton" correspondence pattern from Chapter 3, transplanted onto unranked trees via the encoding machinery just built.

## Decision problems: it's all about how you represent the horizontal languages

Here's where hedge automata theory gets genuinely interesting from an engineering standpoint, and where the "just transfer everything through an encoding" strategy starts to show cracks.

**The naive plan:** encode via $\mathrm{ext}$, reuse Chapter 1's ranked-tree decision procedures. This works fine for some problems (membership, some emptiness cases) — but it silently assumes the horizontal languages are represented simply (say, by NFAs), and it throws away information about *how expensive it is to specify the horizontal constraint itself*.

The book instead studies decision complexity **as a function of the horizontal-language representation**, using notation like $\mathrm{NFHA(NFA)}$ (nondeterministic hedge automaton, horizontal languages given by NFAs) vs. $\mathrm{NFHA(AFA)}$ (given by *alternating* finite automata — Boolean combinations of regular expressions, useful for compactly saying "all of these substrings must occur" without blowing up into a permutation-listing regular expression) vs. $\mathrm{NFHA}(RE_\|)$ (regular expressions extended with a shuffle/interleave operator $\|$, used later by Relax NG).

**Theorem 8.5.6 (uniform membership):**

| Representation | Complexity |
|---|---|
| $\mathrm{NFHA(NFA)}$ | PTIME |
| $\mathrm{DFHA(DFA)}$ | linear time |
| $\mathrm{NFHA(AFA)}$ | **NP-complete** |
| $\mathrm{DFHA(AFA)}$ | PTIME |
| $\mathrm{NFHA}(RE_\|)$ | NP-complete |

**Theorem 8.5.8 (emptiness):** PTIME for $\mathrm{NFHA(NFA)}$, but **PSPACE-complete** for $\mathrm{NFHA(AFA)}$ (matching AFA-emptiness itself, Proposition 8.5.1) — even though for $RE_\|$ it drops back to PTIME, because replacing $\|$ by ordinary concatenation preserves non-emptiness (shuffling doesn't change whether *some* interleaving exists, just which one).

**This is where Key Question 3 lives, and it's worth sitting with.** Corollary 8.5.7: there is **no polynomial-time translation** from $\mathrm{NFHA(AFA)}$ to [[Alternating-Tree-Automata|alternating tree automata]] on the FCNS or extension encoding, unless P = NP. Why does the general "transfer via encoding" strategy break down exactly here? Because alternating tree automata (Chapter 7) have a *polynomial-time* uniform membership problem, but $\mathrm{NFHA(AFA)}$'s uniform membership is NP-complete (Theorem 8.5.6(3)) — if there *were* a polynomial encoding-translation, you could decide an NP-complete problem in polynomial time via the poly-time-checkable encoded automaton, collapsing P and NP. The encoding machinery (FCNS, $\mathrm{ext}$) transfers *recognizability* faithfully, but it does **not**, in general, transfer *complexity of representation* faithfully — going through an encoding first requires removing alternation from the horizontal languages (converting AFAs to NFAs), and that conversion itself costs an exponential blow-up. The moral: an encoding-based reduction proves a decidability/closure result correctly, but if you then read off a complexity bound from "the ranked-tree version is polynomial," you've silently assumed the *translation into the encoding* was free. It never is when the source representation (here, AFAs) is already more succinct than the target formalism's naïve rule-per-transition style.

This is a sharper, more concrete version of the general lesson Chapters 4 and 5 kept surfacing: a formalism's expressive/succinctness choices are never complexity-neutral, and "can I get this result via a generic transfer" is a different question from "should I, if I actually care about the complexity number."

## Minimization: where the story gets genuinely surprising

In the ranked-tree setting (§1.5), the Myhill-Nerode congruence $\equiv_L$ gave you *everything*: finite index iff recognizable, and the quotient automaton was the unique minimal one. You'd hope the direct unranked analogue — define $t\equiv_L t'$ using contexts $C\in C(\Sigma)$ exactly as before — would give the same clean story. **It doesn't, and the reason why is the real content of this section.**

**Theorem 8.6.1** does hold: for each recognizable $L$, there's a unique (up to renaming) normalized DFHA with minimal *state count*, built from $\equiv_L$'s equivalence classes exactly as in the ranked case.

But here's **Example 8.6.2**, the counterexample that should give you pause: $L=\{a(b^nc^n)\mid n\in\mathbb{N}\}$ is **not** recognizable (its horizontal language $b^nc^n$ isn't regular — this is the exact non-regularity witnessed by the classic pumping argument on strings). And yet $\equiv_L$ has only **4** equivalence classes: $L$ itself, $\{b\}$, $\{c\}$, and everything else. **Finite index does not imply recognizable here.** The vertical congruence $\equiv_L$ simply isn't fine-grained enough to see that the *horizontal* structure below each $a$-node needs to be regular — it only tracks "can this subtree be swapped for that one in any context," which is blind to the internal state-sequence structure a hedge automaton actually needs to track.

**What this reveals** (Key Question 1): a hedge automaton's real state information doesn't live purely "at a node" the way a ranked-tree automaton's does — it's smeared across *how a node's children were counted and classified as a sequence*, and no amount of node-local congruence-checking can recover that. You need a congruence that looks at horizontal composition directly.

Even setting that aside, if you try to minimize the *whole representation* (states plus however you encode each horizontal language), **Example 8.6.3** shows there's no unique minimal DFHA at all under any reasonable size measure: a language "$n$ divisible by 2 or 3" can be represented either as one horizontal-language automaton counting mod 6 (6 states, one transition) or as two automata splitting the disjunction (2+3 states, two transitions) — both minimal by a states-plus-transitions measure, genuinely non-isomorphic. The model has an inherent ambiguity: which horizontal automaton to apply isn't determined step-by-step, it requires committing to the whole successor sequence up front.

### The fix: stepwise hedge automata and the @-congruence

The repair (Key Question 2) is to stop treating "read the whole horizontal sequence, then decide the state" as one atomic step, and instead make horizontal reading itself **truly step-by-step, one child at a time** — merging the hedge automaton's states with the horizontal automata's states into a single state set. A **deterministic stepwise hedge automaton (DSHA)** $A=(Q,\Sigma,\delta_0,Q_f,\delta)$ has $\delta_0:\Sigma\to Q$ (initial state per label) and $\delta:Q\times Q\to Q$ (fold one more child's state into the running state), so that reading a sequence of $n$ children is literally a left-fold: $\delta_a(q_1\cdots q_n) = \delta(\delta(\cdots\delta(\delta_0(a),q_1)\cdots),q_n)$.

```rust
// A DSHA: one state set shared between "vertical" and "horizontal" roles.
struct DSHA<Q> {
    initial: HashMap<char, Q>,     // delta_0 : Sigma -> Q
    step: HashMap<(Q, Q), Q>,      // delta   : Q x Q -> Q  (fold one child in)
    final_states: HashSet<Q>,
}

fn run<Q: Eq + Hash + Clone>(a: &DSHA<Q>, t: &Tree) -> Q {
    let mut acc = a.initial[&t.label].clone();
    for child in &t.children {
        let child_state = run(a, child);
        acc = a.step[&(acc, child_state)].clone();
    }
    acc
}
```

This is exactly a **left fold over `Vec<Child>`** — `children.iter().fold(initial_state, |acc, c| step(acc, run(c)))` — which should feel like the single most natural way a Rust programmer would already process a variable-arity node.

The technical payoff (Lemma 8.6.5, Theorem 8.6.6) is that a DSHA corresponds *exactly* to a DFTA on the **extension encoding**: $\delta_0(a)=q$ plays the role of the ranked rule $a\to q$, and $\delta(q_1,q_2)=q$ plays the role of $@(q_1,q_2)\to q$. Because this correspondence is exact (not just language-preserving up to some blow-up), all of Chapter 1's minimization theory (§1.5) transfers cleanly: **Theorem 8.6.8**, every recognizable language has a **unique minimal DSHA**. The book closes the loop with a genuine Myhill–Nerode-style **@-congruence** (Theorem 8.6.9) defined directly in terms of the $@$ operation rather than node-local contexts — precisely the "look at horizontal composition directly" fix that Key Question 1 was gesturing at.

## Where this leads

Within the chapter: §8.2–8.6 lay the whole theoretical foundation — the hedge-automaton model, its two encodings into ranked trees, its logic, its decision complexity, and (after some real surprises) its minimization theory. §8.7, covered in the companion article on [[XML-Schema-Formalisms|XML Schema Formalisms]], is the payoff application: DTDs, XML Schema, and Relax NG are all shown to be specific, more-or-less-restricted instances of exactly this hedge-automaton machinery, with their real-world design trade-offs (deterministic content models, single-typing, the interleave operator) explained precisely in terms of which corner of this chapter's complexity landscape they occupy.

For your standing project: variable-arity constructors are everywhere in a real compiler's AST and in inductive type definitions with variable numbers of fields or constructor arguments — hedge automata are the natural "automaton-shaped abstract domain" for such structures, directly relevant to the abstract-interpretation/CSP-kernel goal of representing complex recursive data as automaton-like domains. The minimization story is the sharper lesson to internalize, though: it's a fully worked example of *structural tractability* failing in a subtle way — a naive, node-local congruence (the direct transplant of Myhill-Nerode) looks like it should work, has finite index on a genuine counterexample, and yet completely misses recognizability; only a congruence built around the right compositional operation (here, $@$) restores the clean theory. That's a pattern worth watching for anywhere you're tempted to reuse a ranked/fixed-arity proof technique unchanged on a variable-arity or open-ended domain — the fix is rarely "add more machinery to the naive approach," it's "find the operation the naive approach was blind to."
