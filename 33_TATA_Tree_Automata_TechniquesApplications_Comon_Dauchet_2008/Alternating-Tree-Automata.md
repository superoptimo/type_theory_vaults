---
title: Alternating Tree Automata
source: "Tree Automata Techniques and Applications (TATA)"
chapter: "Chapter 7 — Alternating Tree Automata"
pages: "183–196"
tags: [tree-automata, alternating-automata, horn-clauses, set-constraints, two-way-automata, complexity]
---

[[book-guidelines|↩ Back to guidelines]]

## The asymmetry that alternation fixes

Go back to a plain nondeterministic bottom-up tree automaton. Two rules with the same left-hand side, $f(q_1,\dots,q_n)\to q$ and $f(q_1',\dots,q_n')\to q$, are really one rule with a *disjunctive* choice of right-hand configuration: "accept in state $q$ if the children satisfy this combination *or* that combination." A run has to commit to one disjunct. That commitment is exactly what determinization has to undo — subset construction gathers every disjunct the run could have picked into a single state, so that "was there some accepting choice" becomes "does the (unique) deterministic run land in an accepting state." It works, but it costs an exponential blowup, and it's needed only because the formalism gave you disjunction and nothing else.

**[[Automata-with-Constraints#What breaks|What breaks]] without alternation:** you can't directly say "accept iff *all* of these several sub-conditions hold," only "iff *some* rule's children-pattern matches." If you want genuine conjunction — verify property $A$ of the first child *and* property $B$ of the second, checked by two independent, possibly-overlapping runs — nondeterministic automata make you fold that conjunction into the state space by hand (a Cartesian-product construction), which is exactly the kind of blow-up you'd like the formalism to absorb once and for all.

**Alternating tree automata** restore the missing symmetry: transitions map to *positive Boolean formulas* over (state, child-position) pairs, so both $\land$ and $\lor$ are first-class. The immediate payoff, worked out below, is that complementation stops needing determinization at all — you just swap $\land\leftrightarrow\lor$ and $\mathrm{true}\leftrightarrow\mathrm{false}$. The price, also worked out below, is that the automaton is now a much more concise representation of the same class of languages, and conciseness has to be paid for somewhere: in harder decision problems.

## Definitions: positive Boolean transition formulas

Fix a finite set of states $Q$. Write $\mathcal{B}^+(Q)$ for the set of positive propositional formulas over $Q$ — built from atoms in $Q$, $\mathrm{true}$, $\mathrm{false}$, using only $\land$ and $\lor$ (no negation; that's what "positive" means, and it's what makes the later complementation trick work). For example $q_1 \land (q_2\lor q_3)\land(q_2\lor q_4)$ is a formula in $\mathcal{B}^+(\{q_1,q_2,q_3,q_4\})$.

**Definition 7.2.3.** An alternating tree automaton over a ranked alphabet $F$ is $A=(Q,F,I,\Delta)$, where $I\subseteq Q$ is a set of *initial* states and $\Delta$ maps $Q\times F$ to $\mathcal{B}^+(Q\times\mathbb{N})$, with $\Delta(q,f)\in\mathcal{B}^+(Q\times\{1,\dots,\mathrm{Arity}(f)\})$. The book presents this as a **top-down** automaton — the formula at $(q,f)$ talks about which states the automaton demands of each numbered child, which is the natural direction for a top-down reading (it's more convenient here than forcing a bottom-up phrasing).

A run isn't a sequence of moves anymore; it's a tree $\rho$ over positions labeled by $Q\times\mathbb{N}^*$ (state paired with tree-position), such that if $\rho(\pi)=(q,p)$, $t(p)=f$, and $\Delta(q,f)=\varphi$, then there is *some* set $S=\{(q_1,i_1),\dots,(q_n,i_n)\}\subseteq Q\times\{1,\dots,\mathrm{Arity}(f)\}$ satisfying $\varphi$ (in the ordinary propositional sense — members of $S$ are true, everything else false) such that $\rho$ branches at $\pi$ into children labeled $(q_j, p\cdot i_j)$. A run is successful if its root is labeled $(q,\epsilon)$ for some $q\in I$.

Read that satisfaction condition concretely: at a node demanding $(q_1,1)\land(q_2,2)$, the run *must* branch into both a $q_1$-labeled subrun at child 1 and a $q_2$-labeled subrun at child 2 — conjunction forces multiple obligations at once. At a node demanding $(q_1,1)\lor(q_1,2)$, the run only needs *one* of the two — disjunction is the familiar nondeterministic choice. Ordinary (completely specified) nondeterministic top-down automata are recovered exactly as the disjunction-only fragment:
$$
\Delta(q,f) = \bigvee_{(q_1,\dots,q_n)\in S}\ \bigwedge_{i=1}^{\mathrm{Arity}(f)} (q_i,i)
$$
— i.e., a nondeterministic automaton is "alternating with conjunction used only to bundle a rule's own children together, never to branch across separate obligations."

```rust
// A minimal Rust shape for the transition-formula side of an
// alternating tree automaton. `Formula` is the B+(Q x N) piece;
// evaluating it against a candidate assignment S is a direct recursive
// walk, exactly mirroring the "S |= phi" satisfaction relation above.
#[derive(Clone)]
enum Formula<Q> {
    True,
    False,
    Atom(Q, usize),           // (state, child position)
    And(Box<Formula<Q>>, Box<Formula<Q>>),
    Or(Box<Formula<Q>>, Box<Formula<Q>>),
}

impl<Q: PartialEq> Formula<Q> {
    // S: the set of (state, position) pairs a candidate run assigns "true"
    fn satisfied_by(&self, s: &[(Q, usize)]) -> bool
    where
        Q: Clone,
    {
        match self {
            Formula::True => true,
            Formula::False => false,
            Formula::Atom(q, i) => s.iter().any(|(qq, ii)| qq == q && ii == i),
            Formula::And(l, r) => l.satisfied_by(s) && r.satisfied_by(s),
            Formula::Or(l, r) => l.satisfied_by(s) || r.satisfied_by(s),
        }
    }
}
```

A run-search procedure then just needs to, at each node, enumerate subsets $S$ (or better, use a SAT-style search for a *minimal* satisfying set — the book notes you can always restrict to a minimal $S$ without loss of generality) and recurse into the children it names.

## Closure properties: complementation for free

**Proposition 7.3.2.** Union, intersection, and complement of alternating tree automata are all computable in **linear time**.

Union and intersection are unsurprising: normalize both automata to a single initial state (Lemma 7.3.1 — add a fresh state $q^0$ with $\Delta(q^0,f) = \bigvee_{q\in I}\Delta(q,f)$), take the disjoint union of state sets, and combine the two normalized root formulas with $\lor$ (union) or $\land$ (intersection).

Complement is the interesting one, and it's where positivity earns its keep: build the **dual automaton** $\tilde A$ by taking every transition formula $\varphi$ and swapping $\land\leftrightarrow\lor$, $\mathrm{true}\leftrightarrow\mathrm{false}$, everywhere. That's it — no determinization, no state-set blow-up, just a syntactic transformation on the formulas, done once per transition. The correctness argument is a clean induction on the term's size: for a leaf $a$, $\Delta(q,a)$ is either $\mathrm{true}$ or $\mathrm{false}$ outright, so $a$ is accepted by exactly one of $A,\tilde A$ in state $q$. For $t=f(t_1,\dots,t_n)$, let $S$ be the set of $(q_j,i_j)$ pairs where $t_{i_j}$ is actually accepted (by $A$) in state $q_j$; $t$ is accepted by $A$ in state $q$ iff $S\models\varphi$. The complementary set $\tilde S$ (everywhere $S$ says "no") is, by induction, exactly the pairs accepted by $\tilde A$ — and a short induction on formula structure shows $\tilde S \models \tilde\varphi \iff S\not\models\varphi$. So acceptance by $A$ and by $\tilde A$ are exact complements at every node, all the way up.

**What breaks without positivity:** if $\Delta$ could itself contain negation, $\varphi$ and $\tilde\varphi$ built by naive symbol-swapping would no longer be guaranteed logical duals in the clean sense the induction needs — you'd be back to needing an actual semantic complementation step. Restricting transitions to positive formulas is precisely what makes "complement = swap connective symbols" a *syntactic*, linear-time operation rather than a semantic one.

## Same expressive power, still exponentially harder to determinize

Here's the part worth sitting with, because it resolves an apparent tension.

**Theorem 7.4.1.** Every alternating tree automaton $A$ has an equivalent finite deterministic bottom-up tree automaton $A'$ — computable from $A$, but only in **deterministic exponential time**.

The construction is the expected "states of $A'$ are subsets of states of $A$" move: $A' = (2^Q, F, Q_f, \delta)$ with $Q_f=\{S\in 2^Q \mid S\cap I\neq\emptyset\}$ and
$$
\delta(f, S_1,\dots,S_n) = \{q\in Q \mid (S_1\times\{1\})\cup\cdots\cup(S_n\times\{n\}) \models \Delta(q,f)\}.
$$
A term is accepted by $A'$ in state $S$ exactly when it's accepted by $A$ *in every state $q\in S$ simultaneously* — the subset-of-states bookkeeping is doing exactly the same job subset construction always does, tracking "which states are still consistent," except here "consistent" already has to account for conjunctive obligations baked into $\Delta$.

**And this blow-up is provably unavoidable** — not an artifact of this particular construction, but a consequence of Proposition 7.3.2 together with Chapter 1's complexity results (Theorems 1.7.4, 1.7.7): if alternating automata could always be determinized in less than exponential time, you could decide their universality/inclusion problems too cheaply, contradicting known lower bounds.

**This is the resolution of Key Question 1.** There is no contradiction between "alternating and nondeterministic (equivalently: deterministic) automata recognize exactly the same class of languages" and "complementation is free for alternating automata but costs a determinization for nondeterministic ones." *Expressive power* is a statement about which languages are recognizable at all — and that class is identical (Theorem 7.4.1 says so directly: alternating automata recognize nothing nondeterministic bottom-up automata can't). *Cost of an operation on a given representation* is a completely separate axis — it's about how expensive it is to compute the automaton *for the complement*, starting from *this specific automaton*, without changing the underlying formalism. Alternation is a representation that happens to make complementation cheap precisely because it defers the states-tracking cost: an alternating automaton can be exponentially more *succinct* than an equivalent deterministic one for the same language, and that succinctness is exactly what you're paying for later, in Theorem 7.4.1's exponential conversion, or in the harder decision problems below. Free complementation and expensive determinization aren't in tension; they're the same trade viewed from two ends of a single automaton, sized differently at each end.

## Decision problems: DEXPTIME climbs in

**Theorem 7.5.1.** Emptiness and universality for alternating tree automata are **DEXPTIME-complete**. Membership (is a *given* term $t$ accepted?) stays in **PTIME** — you're just evaluating $\Delta$ bottom-up against a fixed term, no search over the automaton's structure required.

DEXPTIME membership for emptiness/universality falls straight out of Theorem 7.4.1 (convert, then use Chapter 1's polynomial-in-automaton-size emptiness/universality algorithms — polynomial in the *converted*, exponentially larger automaton). DEXPTIME-hardness comes from Proposition 7.3.2's free complementation plus Chapter 1's EXPTIME-completeness results for nondeterministic automata (Theorem 1.7.7) — you can encode a hard nondeterministic-automaton problem as an alternating one cheaply, so alternating automata inherit at least that hardness, and the free complement lets you push it up a level. So the concision alternation buys you at the representation level is exactly what these decision problems now have to spend, undoing on the complexity side what was saved on the representation side.

## Horn clauses: automata as least-fixed-point logic programs

Section 7.6 recasts everything above in a genuinely different vocabulary, and this recasting is worth real attention — it's the book's most direct bridge to constraint-logic-programming-style reasoning.

**View each state $q$ as a unary predicate symbol $P_q$.** A plain nondeterministic bottom-up rule $f(q_1,\dots,q_n)\to q$ becomes the **Horn clause**
$$
P_q(f(x_1,\dots,x_n)) \leftarrow P_{q_1}(x_1), \dots, P_{q_n}(x_n).
$$
The language accepted in state $q$ is exactly the interpretation of $P_q$ in the **least Herbrand model** of the resulting clause set — i.e., tree-automaton acceptance *is* least-fixed-point Horn-clause semantics, with no separate "run" concept needed at all: a term is accepted iff it's derivable from the facts and rules by ordinary forward chaining. This is worth pausing on if your mental model of Horn clauses comes from program verification: a bottom-up tree automaton is nothing but a monadic (unary-predicate) Datalog program over a term algebra, and its accepted language is that program's model.

**Alternation is exactly variable sharing in a clause body.** Given a DNF transition $\Delta(q,f) = \bigvee_{i=1}^m \bigwedge_{j=1}^{k_i} (q_j, i_j)$, each disjunct $i$ becomes its own clause
$$
P_q(f(x_1,\dots,x_n)) \leftarrow \bigwedge_{j=1}^{k_i} P_{q_j}(x_{i_j}),
$$
and conjunction inside a disjunct is realized by *repeating the same variable $x_{i_j}$* across multiple body atoms — i.e., by requiring several predicates to hold of the *same* subterm simultaneously. That single mechanism (shared variables in a clause body) is *all* that alternation adds to ordinary tree-automaton-as-Datalog: nondeterministic automata are exactly the fragment where each body variable appears at most once.

This connects directly to a `Constrained Horn Clauses` mental model if you're building a CHC-based verification backend: a CHC solver's whole job is finding predicate interpretations satisfying a clause set with shared variables and arbitrary constraints in the bodies — which is *precisely* what's happening here, specialized to the case where the "constraints" are just "these two positions must satisfy predicates simultaneously." Automata-with-constraints-between-brothers (Chapter 4, §4.3) fits into this picture as *literally* allowing repeated variables in the **head** of the clause too (not just the body) — a strictly larger class, and one where the book flags that emptiness is still decidable, but the clean automaton-theoretic complexity bounds from Chapter 4 don't transfer over cleanly to this logical framework (the book is candid that deriving those bounds logically is genuinely harder — automata techniques bought results that the Horn-clause view doesn't reproduce for free).

```lean
-- The clause-per-disjunct translation, stated as a Lean-style
-- inductive characterization of acceptance-as-least-fixed-point.
-- `accepts A q t` mirrors "t is in the least Herbrand model's
-- interpretation of P_q" directly: it's exactly the smallest
-- relation closed under the automaton's clauses.
inductive Accepts (Δ : State → Symbol → Formula) : State → Term → Prop
  | step {q f args} :
      (∃ S, Satisfies S (Δ q f) ∧
            ∀ (qi : State) (i : Nat), (qi, i) ∈ S →
              Accepts Δ qi (args.get i)) →
      Accepts Δ q (Term.mk f args)
```

**Definite set constraints** (Chapter 5's formalism, revisited here) give a third equivalent presentation: inclusions $e\subseteq t$ where $e$ is built from function application, intersection, and variables, and $t$ from function application and variables only. Restricting the *left* side of every inclusion to a bare variable recovers exactly alternating tree automata again (each $(q,f,\text{disjunct }d)$ triple becomes an inclusion $f(X_{1,f,q,d},\dots) \subseteq X_q$ paired with $\bigcap_{(q',j)\in d} X_{q'} \subseteq X_{j,f,q,d}$) — the least solution of the constraint system is exactly the language recognized. Three formalisms — alternating automata, monadic Horn clauses, definite set constraints with variable-only right sides — turn out to be the *same object* wearing different notation, each making a different closure property or proof technique easiest to see.

## Two-way automata: pop clauses break the symmetry, on purpose

Plain definite set constraints look strictly more expressive than one-way alternating automata, because an inclusion like $X\subseteq f(Y,Z)$ — "everything in $X$ *decomposes as* $f$ of something in $Y$ and something in $Z$" — has no direct automaton-rule translation: ordinary transitions only ever build *up* from children to parent, never reason *down* from a parent's shape back to constraints on children.

**Two-way alternating tree automata** are defined purely clausally to capture exactly this. Three clause shapes:
- a **push clause** $P(u) \leftarrow P_1(x_1),\dots,P_n(x_n)$ ($u$ linear, non-variable — this is an ordinary bottom-up move, "build $u$ if the pieces are already verified"),
- a **pop clause** $P(x) \leftarrow Q(t)$ ($t$ linear — this is the new move: "verify $P$ of a *subterm* $x$ by looking at a larger term $t$ containing it," reasoning from parent-shape down into a piece),
- an **alternating (intersection) clause** $P(x)\leftarrow P_1(x),\dots,P_n(x)$ (the same-subterm conjunction from before).

Despite genuinely adding expressive convenience — the book notes these are handy for encoding problems that don't have a natural one-way phrasing — **Theorem 7.6.3** shows two-way automata **do not increase expressive power**: every two-way alternating tree automaton has an equivalent ordinary (one-way) tree automaton, computable in deterministic exponential time. The construction *flattens* the clauses (introducing fresh predicates so every clause has a single functional symbol at top), then **saturates** by ordered resolution (with respect to a subterm ordering) discarding subsumed clauses, and finally reads off the resulting push clauses as the equivalent automaton — the pop clauses have been resolved away entirely. The book works this through concretely for a small cryptographic-style example, tracking a Herbrand-model computation step by step and then rerunning the same example through the saturation procedure to recover an 8-rule ordinary automaton.

**This answers Key Question 2 precisely.** Pushdown automata *also* look like they're doing a two-way-ish thing — push/pop on a stack — and two-way tree automata really can *simulate* a pushdown automaton's reachable-stack-contents language (Exercise 7.5 walks through the construction directly). But that simulation only shows two-way tree automata are at least as powerful as *stack-content tracking*, and Theorem 7.6.3 caps their power at *regular tree languages* overall — no more than ordinary tree automata recognize. Pushdown automata, in contrast, recognize **context-free** languages, a strictly larger class than regular. The superficial resemblance (both have a "push" and a "pop" move) is misleading: a two-way tree automaton's pop clause reasons *down into an already-fixed, already-verified term* — it never gets to build up an unbounded, order-sensitive stack of its own choices the way a pushdown automaton's stack does. The push/pop vocabulary is shared; the actual computational device underneath is not. As a genuinely nice corollary of Theorem 7.6.3: the language of *reachable stack contents* of a pushdown automaton is itself regular — a fact you get for free once you see stack-content tracking as an instance of the (regularity-preserving) two-way tree automaton construction.

## Where this leads

Within the book, this chapter is the last stop before Chapter 8 moves to a completely different generalization axis — not "richer transitions" (alternation, constraints) but "richer tree shape" (unranked trees / hedges, motivated by XML). The two axes are largely orthogonal: nothing here assumed a fixed arity was essential, but nothing in Chapter 8 revisits alternation either, so the two extensions of "plain" tree automata developed in this book don't compose into a single super-formalism — each is its own self-contained trade-off.

For your compiler/elaborator project, the highest-value takeaway is §7.6's three-way equivalence (alternating automata = monadic Horn clauses with shared body variables = definite set constraints). If your CSP/abstract-interpretation kernel is going to represent invariants or refinement obligations as Constrained Horn Clauses, this chapter is a fully worked-out instance of exactly that connection at its simplest: states-as-predicates, transitions-as-clauses, and *acceptance is literally least-fixed-point semantics* — the same semantics a CHC solver computes when it looks for the least model satisfying your generated verification-condition clauses. The free-complementation-vs-exponential-determinization split is also a genuinely transferable design lesson for structural tractability: a representation that's cheap for one operation (union/intersection/complement here) can be expensive for another (determinization, decision problems) precisely because of the succinctness that made the first operation cheap — worth remembering when choosing how to represent abstract domains in the kernel, since "easy to combine" and "easy to query" are not the same property and a formalism rarely gives you both for free.
